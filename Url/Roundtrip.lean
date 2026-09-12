import Url.ApiValid

/-!
# parse ∘ serialize

**目標は `basicUrlParse (urlSerializer u) = some u`** である。この file はその一部を閉じる。

## `ValidUrl` では足りない

`ValidUrl`（と `checkStrictUrl`）を満たすだけの record では成り立たない。
どれも §4.1 は禁じていないが、parser が作らない形である。

| record | serialize | parse し直すと |
| --- | --- | --- |
| `{ scheme := "sc", query := some " " }` | `sc:? ` | query が `""` になる（前処理が末尾の space を落とす） |
| `{ scheme := "http", host := "a", port := some 80, path := .list [""] }` | `http://a:80/` | port が `none` になる（既定 port） |
| `{ scheme := "sc", path := .list [".."] }` | `sc:/..` | path が `[""]` になる（double-dot segment） |

つまり **record が parser の出力の形（canonical form）である**ことが要る。
それを `canonicalUrl` として書いた。`checkValidUrl` と同じく、まず boolean として置いて
WPT の 820 件と setter の 705 件で実行時に確かめている（違反 0）。

実行時の検査で分かるのは「強すぎないこと」だけである。**弱すぎるかどうかは証明でしか
分からない。** 実際、opaque path の `?` `#` と先頭の `/`、special な URL の segment の
`\\` は、証明を書いていて足りないことに気づいた条件である。

## この file が閉じた分

* `roundtrip_opaque`：scheme start → scheme → opaque path → query → fragment
* `roundtrip_path`：scheme start → scheme → path or authority → path

どちらも `canonicalUrl` のうち通る成分に当たる条件を仮定して `parse ∘ serialize = id` を言う。

作り方は state ごとの等式を積む形で、`Url/ApiValid.lean` の setter の肯定側と同じである。
一つの state について三種類を用意する。

* **chunk**：区切りでない文字を読み切って同じ state に留まる（`run_opaquePath_chunk` ほか）
* **区切り**：1 文字で次の state へ渡す（`run_opaquePath_question` ほか）
* **終端**：EOF で `.ok` を返す（`run_opaquePath_eof` ほか）

path を通る経路（host を持たない非 special な URL）も同じ形で閉じた（`roundtrip_path`）。
残りは authority / host / port を通る経路、つまり `//` で始まる URL である。
-/

namespace Url

open Infra

set_option maxHeartbeats 1000000

/-! ## canonical form

parser が返す record の形。これを満たさない record には `parse ∘ serialize` は成り立たない
（上の表の三つがその例である）。`checkValidUrl` と同じく、まず boolean として書いて
WPT の全 case で実行時に確かめる。証明はこれを仮定として進める。
-/

/-- scheme が parser の書く形か。先頭は ASCII 小文字 alpha、残りは alphanumeric か `+` `-` `.`。 -/
def canonicalScheme (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: rest =>
    isAsciiLowerAlpha c &&
      rest.all fun x =>
        (isAsciiDigit x || isAsciiLowerAlpha x) || x == '+' || x == '-' || x == '.'

/--
その set の文字を含まないこと。

percent-encode の出力がこれを満たす。`%` も 16 進の数字もどの set にも入らないので、
encode した結果をもう一度 encode しても変わらない（`utf8PercentEncode_id`）。
-/
def encodedWith (set : Char → Bool) (s : String) : Bool :=
  s.toList.all fun c => !set c

/--
**parser が返す record の形。**

`ValidUrl` は §4.1 の条件で、こちらは「parse し直しても同じ record になる」ための条件である。
重なりは無く、どちらも他方を含まない。
-/
def canonicalUrl (u : Url) (toAscii : List Char → Option String := asciiDomainToASCII) : Bool :=
  canonicalScheme u.scheme &&
  -- 既定 port は書かない（`portOf` が null にする）
  (match u.port with | none => true | some p => defaultPort u.scheme != some p) &&
  encodedWith userinfoSet u.username &&
  encodedWith userinfoSet u.password &&
  (match u.query with
   | none => true
   | some q => encodedWith (if u.isSpecial then specialQuerySet else querySet) q) &&
  (match u.fragment with | none => true | some f => encodedWith fragmentSet f) &&
  (match u.path with
   | .opaque o =>
     -- `?` と `#` は opaque path state の出口なので、中には入らない。
     -- 末尾の space は前処理が落とすので、parser は `%20` にしている。
     encodedWith c0ControlSet o && !(o.toList.getLast? == some ' ') &&
       o.toList.all (fun c => c != '?' && c != '#') &&
       -- 先頭の `/` は path or authority state へ行ってしまう。
       !(o.toList.head? == some '/')
   | .list segs =>
     segs.all fun seg =>
       encodedWith pathSet seg && !isSingleDot seg.toList && !isDoubleDot seg.toList &&
         -- special な URL では `\\` も区切りである（`pathSet` は encode しない）。
         (!u.isSpecial || seg.toList.all (fun c => c != '\\'))) &&
  -- host が null で path が空だと、serialize しても path の跡が残らない。
  -- parser は host が null の URL には必ず segment を一つ以上書く。
  (match u.host, u.path with | none, .list [] => false | _, _ => true) &&
  -- host は serialize してから読み直すと同じもの
  (match u.host with
   | none => true
   -- empty host は host parser の出力ではない（parser が直に書く）。
   | some .empty => true
   | some h => hostParser toAscii (hostSerializer h).toList (!u.isSpecial) == some h)

/-- 先頭が落ちない文字なら `dropWhile` は何もしない。 -/
theorem dropWhile_of_head : ∀ (l : List Char) (p : Char → Bool), (∀ c ∈ l.head?, p c = false) →
    List.dropWhile p l = l
  | [], _, _ => rfl
  | c :: rest, p, h => by
    rw [List.dropWhile_cons, if_neg (by rw [h c rfl]; simp)]

/--
前後が C0 control でも space でもなく、tab も newline も無ければ、前処理は何もしない。

前後だけで済むのは `dropWhile` が最初の一つで止まるからである。
-/
theorem preprocess_eq_self {str : String}
    (hh : ∀ c ∈ str.toList.head?, isC0ControlOrSpace c = false)
    (hl : ∀ c ∈ str.toList.reverse.head?, isC0ControlOrSpace c = false)
    (hnt : ∀ c ∈ str.toList, c.toNat ≠ 0x09 ∧ c.toNat ≠ 0x0A ∧ c.toNat ≠ 0x0D) :
    preprocess str = str.toList := by
  unfold preprocess
  simp only [dropWhile_of_head str.toList isC0ControlOrSpace hh]
  rw [dropWhile_of_head str.toList.reverse isC0ControlOrSpace hl, List.reverse_reverse]
  exact stripTabNewline_eq_self hnt

/-- scheme に使える文字。§4.4 scheme state の step 1 である。 -/
def schemeChar (c : Char) : Bool :=
  isAsciiAlphanumeric c || c == '+' || c == '-' || c == '.'

/-- scheme state は scheme の文字を小文字にして buffer に積む。 -/
theorem run_scheme_prefix (base : Option Url) : ∀ (pre rest : List Char) (ctx : PCtx),
    (∀ c ∈ pre, schemeChar c = true) →
    run base .scheme (pre ++ rest) ctx
      = run base .scheme rest { ctx with buffer := ctx.buffer ++ pre.map asciiLowerChar } := by
  intro pre
  induction pre with
  | nil => intro rest ctx _; simp
  | cons c tail ih =>
    intro rest ctx hd
    simp only [List.cons_append]
    rw [run, step, if_pos (by have := hd c (by simp); simpa [schemeChar] using this)]
    rw [ih rest { ctx with buffer := ctx.buffer ++ (asciiLowercase (String.ofList [c])).toList }
        (fun x hx => hd x (by simp [hx]))]
    simp [asciiLowercase]

/--
scheme state の `:`：special でない scheme で、続きが `/` で始まらなければ opaque path へ。

仕様 §4.4 scheme state の step 2.6 である。
-/
theorem run_scheme_opaque (base : Option Url) (rest : List Char) (ctx : PCtx)
    (hov : ctx.over = none)
    (hf : ¬(String.ofList ctx.buffer = "file"))
    (hsp : isSpecialScheme (String.ofList ctx.buffer) = false)
    (hr : ∀ r ∈ rest.head?, ¬r = '/') :
    run base .scheme (':' :: rest) ctx
      = run base .opaquePath rest
          { ctx with
            url := { ctx.url with scheme := String.ofList ctx.buffer, path := .opaque "" }
            buffer := [] } := by
  rw [run, step]
  rw [if_neg (by decide), if_pos (by decide)]
  simp only [hov, Option.isSome_none, Bool.false_eq_true, if_false]
  rw [if_neg (by simpa using hf), if_neg (by simp [Url.isSpecial, hsp]),
    if_neg (by simp [Url.isSpecial, hsp])]
  cases rest with
  | nil => rfl
  | cons r t =>
    have hne : ¬r = '/' := hr r (by simp)
    split
    · next rest2 he => simp only [List.cons.injEq] at he; exact absurd he.1 hne
    · rfl

/-- scheme に使える文字は tab でも newline でもない。 -/
theorem schemeChar_ne_tab {c : Char} (h : schemeChar c = true) :
    c.toNat ≠ 0x09 ∧ c.toNat ≠ 0x0A ∧ c.toNat ≠ 0x0D := by
  simp only [schemeChar, isAsciiAlphanumeric, isAsciiDigit, isAsciiAlpha, isAsciiUpperAlpha,
    isAsciiLowerAlpha, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rcases h with (((h | h | h) | h) | h) | h <;> first | omega | (subst h; decide)

/-- 末尾の一文字。`preprocess` が見るのは後ろの `dropWhile` の最初の一つだけである。 -/
theorem reverse_head_mid (l1 : List Char) (c : Char) (l2 : List Char) :
    (l1 ++ c :: l2).reverse.head? = if l2.isEmpty then some c else l2.reverse.head? := by
  cases hx : l2 with
  | nil => simp
  | cons d t => simp [List.reverse_append]

/-! ## query と fragment

どちらも終端の state で、opaque path state からも path state からも来る。
-/

/-- set に入らない文字だけなら、1 文字ずつの percent-encode は何もしない。 -/
theorem encFold_id {set : Char → Bool} : ∀ (l : List Char), (∀ c ∈ l, set c = false) →
    l.flatMap (fun c => (encChar set c).toList) = l
  | [], _ => rfl
  | d :: rest, h => by
    have hc : encChar set d = String.ofList [d] := by
      unfold encChar
      rw [utf8PercentEncode_id (by intro x hx; simp at hx; subst hx; exact h _ (by simp))]
    simp only [List.flatMap_cons, hc, String.toList_ofList, List.singleton_append]
    rw [encFold_id rest (fun x hx => h x (by simp [hx]))]

/-- fragment state は、素通しの文字をそのまま fragment の末尾に足す。 -/
theorem run_fragment_plain (base : Option Url) (l : List Char) (ctx : PCtx) (f : String)
    (hf : ctx.url.fragment = some f) (h : ∀ c ∈ l, fragmentSet c = false) :
    run base .fragment l ctx = .ok { ctx.url with fragment := some (f ++ String.ofList l) } := by
  obtain ⟨u, hu⟩ := run_fragment_ok base l ctx
  rw [hu]
  rw [run_fragment_spec base l ctx u (by rw [hf]; rfl) hu]
  rw [encFold_id l h, hf]
  rfl

/-- override が無い query state は、`#` までの文字を buffer に積んで `queryOf` を書く。 -/
theorem run_query_plain (base : Option Url) : ∀ (l : List Char) (ctx : PCtx),
    ctx.over = none → (∀ c ∈ l, ¬c = '#') →
    run base .query l ctx = .ok { ctx.url with query := some (queryOf { ctx with buffer := ctx.buffer ++ l }) } := by
  intro l
  induction l with
  | nil => intro ctx _ _; rw [run, step]; simp
  | cons c tail ih =>
    intro ctx hov h
    have hc : ¬c = '#' := h c (by simp)
    rw [run, step]
    simp +zetaDelta only []
    rw [ih { ctx with buffer := ctx.buffer ++ [c] } hov (fun x hx => h x (by simp [hx]))]
    all_goals first
      | exact hc
      | (simp; done)

/-- query state は `#` でない文字を buffer に積む。 -/
theorem run_query_chunk (base : Option Url) : ∀ (l tail : List Char) (ctx : PCtx),
    (∀ c ∈ l, ¬c = '#') →
    run base .query (l ++ tail) ctx
      = run base .query tail { ctx with buffer := ctx.buffer ++ l } := by
  intro l
  induction l with
  | nil => intro tail ctx _; simp
  | cons c rest ih =>
    intro tail ctx h
    have hc : ¬c = '#' := h c (by simp)
    simp only [List.cons_append]
    rw [run, step]
    rw [ih tail { ctx with buffer := ctx.buffer ++ [c] } (fun x hx => h x (by simp [hx]))]
    all_goals first
      | exact hc
      | (simp; done)

/-- query state の終わり。buffer を percent-encode して query に書く。 -/
theorem run_query_eof (base : Option Url) (ctx : PCtx) :
    run base .query [] ctx = .ok { ctx.url with query := some (queryOf ctx) } := by
  rw [run, step]

/-- query state の `#`。query を確定させて fragment state へ渡す。 -/
theorem run_query_hash (base : Option Url) (rest : List Char) (ctx : PCtx) (hov : ctx.over = none) :
    run base .query ('#' :: rest) ctx
      = run base .fragment rest
          { ctx with
            url := { ctx.url with query := some (queryOf ctx), fragment := some "" }
            buffer := [] } := by
  rw [run, step]
  simp only [hov, Option.isSome_none, Bool.false_eq_true, if_false]

/-- opaque path state の `?`。query state へ渡す。 -/
theorem run_opaquePath_question (base : Option Url) (rest : List Char) (ctx : PCtx) :
    run base .opaquePath ('?' :: rest) ctx
      = run base .query rest { ctx with url := { ctx.url with query := some "" } } := by
  rw [run, step]

/-- opaque path state の `#`。fragment state へ渡す。 -/
theorem run_opaquePath_hash (base : Option Url) (rest : List Char) (ctx : PCtx) :
    run base .opaquePath ('#' :: rest) ctx
      = run base .fragment rest { ctx with url := { ctx.url with fragment := some "" } } := by
  rw [run, step]

/-- opaque path state の終わり。 -/
theorem run_opaquePath_eof (base : Option Url) (ctx : PCtx) :
    run base .opaquePath [] ctx = .ok ctx.url := by
  rw [run, step]

/-- serializer が query と fragment を並べる分。 -/
def qfList (q f : Option String) : List Char :=
  (match q with | none => [] | some s => '?' :: s.toList) ++
    (match f with | none => [] | some s => '#' :: s.toList)

/-- buffer をそのまま query にできるとき、`queryOf` はその文字列を返す。 -/
theorem queryOf_encoded {ctx : PCtx} {qs : String} (hq : ctx.url.query = some "")
    (hb : ctx.buffer = qs.toList)
    (h : ∀ c ∈ qs.toList, (if ctx.url.isSpecial then specialQuerySet else querySet) c = false) :
    queryOf ctx = qs := by
  unfold queryOf
  rw [hq, hb, utf8PercentEncode_id h, String.ofList_toList]
  simp

/--
opaque path state から先、query と fragment を読み切る。

query と fragment の有無の四通りをまとめて扱う。
-/
theorem run_opaquePath_qf (base : Option Url) (ctx : PCtx) (q f : Option String)
    (hov : ctx.over = none) (hbuf : ctx.buffer = [])
    (hq : ctx.url.query = none) (hf : ctx.url.fragment = none)
    (hqc : ∀ s, q = some s → ∀ c ∈ s.toList,
      (if ctx.url.isSpecial then specialQuerySet else querySet) c = false)
    (hfc : ∀ s, f = some s → ∀ c ∈ s.toList, fragmentSet c = false) :
    run base .opaquePath (qfList q f) ctx = .ok { ctx.url with query := q, fragment := f } := by
  unfold qfList
  cases q with
  | none =>
    cases f with
    | none =>
      simp only [List.append_nil]
      have h1 : ({ ctx.url with query := none, fragment := none } : Url)
          = { ctx.url with query := ctx.url.query, fragment := ctx.url.fragment } := by
        rw [hq, hf]
      rw [run_opaquePath_eof, h1]
    | some fs =>
      simp only [List.nil_append]
      rw [run_opaquePath_hash]
      rw [run_fragment_plain base fs.toList _ "" rfl (hfc fs rfl), ← hq]
      simp
  | some qs =>
    have hqs := hqc qs rfl
    have hqe : utf8PercentEncode (if ctx.url.isSpecial then specialQuerySet else querySet)
        qs.toList = qs.toList := utf8PercentEncode_id hqs
    cases f with
    | none =>
      simp only [List.append_nil]
      rw [run_opaquePath_question]
      rw [run_query_plain base qs.toList { ctx with url := { ctx.url with query := some "" } }
        hov (fun c hc => by
          intro he
          have h2 := hqs c hc
          rw [he] at h2
          revert h2
          cases ctx.url.isSpecial <;> decide)]
      rw [← hf]
      simp
      exact queryOf_encoded rfl (by simp [hbuf]) hqs
    | some fs =>
      simp only [List.cons_append]
      rw [run_opaquePath_question]
      rw [run_query_chunk base qs.toList ('#' :: fs.toList)
        { ctx with url := { ctx.url with query := some "" } } (fun c hc => by
          intro he
          have h2 := hqs c hc
          rw [he] at h2
          revert h2
          cases ctx.url.isSpecial <;> decide)]
      rw [run_query_hash base fs.toList
        { ctx with
          url := { ctx.url with query := some "" }
          buffer := ctx.buffer ++ qs.toList } hov]
      rw [run_fragment_plain base fs.toList _ "" rfl (hfc fs rfl)]
      simp
      exact queryOf_encoded rfl (by simp [hbuf]) hqs

/-! ## 文字の性質

前処理が落とす文字（前後の C0 control or space、tab と newline）が
serialize した文字列に現れないことを、成分ごとの percent-encode set から出す。
-/

/-- C0 control percent-encode set に入らない文字は tab でも newline でもない。 -/
theorem ne_tab_of_c0Set {c : Char} (h : c0ControlSet c = false) :
    c.toNat ≠ 0x09 ∧ c.toNat ≠ 0x0A ∧ c.toNat ≠ 0x0D := by
  simp only [c0ControlSet, isC0Control, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    Nat.not_le, Nat.not_lt] at h
  omega

/-- C0 control percent-encode set に入らない文字は C0 control でもない。space は別に見る。 -/
theorem ne_c0_of_c0Set {c : Char} (h : c0ControlSet c = false) (hs : ¬c = ' ') :
    isC0ControlOrSpace c = false := by
  simp only [c0ControlSet, isC0Control, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    Nat.not_le, Nat.not_lt] at h
  simp only [isC0ControlOrSpace, decide_eq_false_iff_not, Nat.not_le]
  have h20 : c.toNat ≠ 0x20 := by
    intro he
    exact hs (by rw [← Char.ofNat_toNat c, he])
  omega

/-- query set に入らなければ C0 control percent-encode set にも入らない。 -/
theorem c0Set_of_querySet {c : Char} (h : querySet c = false) : c0ControlSet c = false := by
  simp only [querySet, Bool.or_eq_false_iff] at h
  exact h.1.1.1.1.1

/-- fragment set についても同じ。 -/
theorem c0Set_of_fragmentSet {c : Char} (h : fragmentSet c = false) : c0ControlSet c = false := by
  simp only [fragmentSet, Bool.or_eq_false_iff] at h
  exact h.1.1.1.1.1

/-- query set に入らない文字は space でもない。 -/
theorem ne_space_of_querySet {c : Char} (h : querySet c = false) : ¬c = ' ' := by
  intro he; rw [he] at h; revert h; decide

/-- fragment set についても同じ。 -/
theorem ne_space_of_fragmentSet {c : Char} (h : fragmentSet c = false) : ¬c = ' ' := by
  intro he; rw [he] at h; revert h; decide

/-! ## path

host を持たない非 special な URL の経路。scheme state から path or authority state へ入る。
-/

/-- path state が区切りでない文字を読み切る。special でない URL の場合。 -/
theorem run_path_chunk (base : Option Url) : ∀ (l tail : List Char) (ctx : PCtx),
    ctx.url.isSpecial = false → ctx.over = none →
    (∀ c ∈ l, pathSet c = false ∧ ¬c = '/' ∧ ¬c = '?' ∧ ¬c = '#') →
    run base .path (l ++ tail) ctx
      = run base .path tail { ctx with buffer := ctx.buffer ++ l } := by
  intro l
  induction l with
  | nil => intro tail ctx _ _ _; simp
  | cons c rest ih =>
    intro tail ctx hsp hov h
    have hc := h c (by simp)
    have henc : encChar pathSet c = String.ofList [c] := by
      unfold encChar
      rw [utf8PercentEncode_id (by intro x hx; simp at hx; subst hx; exact hc.1)]
    simp only [List.cons_append]
    rw [run, step]
    rw [if_neg (by simp [hsp, hc.2.1, hc.2.2.1, hc.2.2.2, hov])]
    rw [ih tail { ctx with buffer := ctx.buffer ++ (encChar pathSet c).toList } hsp hov
      (fun x hx => h x (by simp [hx]))]
    simp [henc]

/-- path state の `/`。segment を確定させて次へ進む。 -/
theorem run_path_slash (base : Option Url) (rest : List Char) (ctx : PCtx) :
    run base .path ('/' :: rest) ctx
      = run base .path rest
          { ctx with url := pathStepUrl ctx.url true ctx.buffer, buffer := [] } := by
  rw [run, step]
  simp

/-- path state の終わり。buffer を最後の segment にする。 -/
theorem run_path_eof (base : Option Url) (ctx : PCtx) :
    run base .path [] ctx = .ok (pathStepUrl ctx.url false ctx.buffer) := by
  rw [run, step]
  simp

/-- `.` でも `..` でもない segment を、`file` でない URL の path の末尾に足す。 -/
theorem pathStepUrl_append {u : Url} {pre : List String} {s : String}
    (hp : u.path = .list pre) (hnf : ¬u.scheme = "file")
    (h1 : isSingleDot s.toList = false) (h2 : isDoubleDot s.toList = false) (slash : Bool) :
    pathStepUrl u slash s.toList = { u with path := .list (pre ++ [s]) } := by
  unfold pathStepUrl
  rw [if_neg (by simp [h2]), if_neg (by simp [h1])]
  unfold pathStepUrl.windowsDriveBuffer
  rw [if_neg (by simp [hnf])]
  unfold appendSegment
  rw [hp]
  simp

/-- serializer が segment を並べる分（先頭の `/` を除く）。 -/
def intercal : List String → List Char
  | [] => []
  | [s] => s.toList
  | s :: rest => s.toList ++ '/' :: intercal rest

/-- path state が segment の列を読み切る。最後の segment は buffer に残る。 -/
theorem run_path_segs (base : Option Url) : ∀ (segs : List String) (tail : List Char) (ctx : PCtx)
    (pre : List String),
    ctx.url.path = .list pre → ctx.buffer = [] →
    ctx.url.isSpecial = false → ctx.over = none → ¬ctx.url.scheme = "file" →
    (∀ s ∈ segs, (∀ c ∈ s.toList, pathSet c = false ∧ ¬c = '/' ∧ ¬c = '?' ∧ ¬c = '#') ∧
      isSingleDot s.toList = false ∧ isDoubleDot s.toList = false) →
    run base .path (intercal segs ++ tail) ctx
      = run base .path tail
          { ctx with
            url := { ctx.url with path := .list (pre ++ segs.dropLast) }
            buffer := (segs.getLast?.getD "").toList } := by
  intro segs
  induction segs with
  | nil =>
    intro tail ctx pre hp hb _ _ _ _
    simp only [intercal, List.nil_append, List.dropLast_nil, List.append_nil,
      List.getLast?_nil, Option.getD_none]
    have h1 : ({ ctx.url with path := Path.list pre } : Url) = ctx.url := by rw [← hp]
    have h2 : ("" : String).toList = ctx.buffer := by rw [hb]; simp
    rw [h1, h2]
  | cons s rest ih =>
    intro tail ctx pre hp hb hsp hov hnf hall
    have hs := hall s (by simp)
    cases rest with
    | nil =>
      show run base .path (s.toList ++ tail) ctx = _
      rw [run_path_chunk base s.toList tail ctx hsp hov hs.1]
      have h1 : ({ ctx.url with path := Path.list (pre ++ ([s] : List String).dropLast) } : Url)
          = ctx.url := by
        show ({ ctx.url with path := Path.list (pre ++ ([] : List String)) } : Url) = ctx.url
        rw [List.append_nil, ← hp]
      rw [h1, hb, List.nil_append]
      simp
    | cons t u =>
      show run base .path ((s.toList ++ '/' :: intercal (t :: u)) ++ tail) ctx = _
      rw [List.append_assoc]
      rw [run_path_chunk base s.toList ('/' :: intercal (t :: u) ++ tail) ctx hsp hov hs.1]
      rw [List.cons_append, run_path_slash]
      rw [ih tail
        { ctx with
          url := pathStepUrl ctx.url true (ctx.buffer ++ s.toList)
          buffer := [] } (pre ++ [s])
        (by rw [hb, List.nil_append, pathStepUrl_append hp hnf hs.2.1 hs.2.2]) rfl
        (by rw [hb, List.nil_append, pathStepUrl_append hp hnf hs.2.1 hs.2.2]; exact hsp)
        hov
        (by rw [hb, List.nil_append, pathStepUrl_append hp hnf hs.2.1 hs.2.2]; exact hnf)
        (fun x hx => hall x (by simp [hx]))]
      rw [hb, List.nil_append, pathStepUrl_append hp hnf hs.2.1 hs.2.2]
      simp [List.append_assoc]

/-- path の serialize は `/` と segment を交互に並べたものである。 -/
theorem pathSerializer_intercal : ∀ (segs : List String), segs ≠ [] →
    (pathSerializer (.list segs)).toList = '/' :: intercal segs
  | [], h => absurd rfl h
  | [s], _ => by
    rw [pathSerializer_cons]
    simp [intercal]
  | s :: t :: u, _ => by
    rw [pathSerializer_cons]
    have hrec : (t :: u).foldl (fun a x => a ++ "/" ++ x) "" = pathSerializer (.list (t :: u)) := rfl
    rw [hrec]
    rw [show ("/" ++ s ++ pathSerializer (.list (t :: u))).toList
        = ("/" ++ s).toList ++ (pathSerializer (.list (t :: u))).toList from by simp]
    rw [pathSerializer_intercal (t :: u) (by simp)]
    simp [intercal]

/-- `intercal` に現れる文字は `/` か segment の文字である。 -/
theorem intercal_mem : ∀ (segs : List String) (c : Char), c ∈ intercal segs →
    c = '/' ∨ ∃ s ∈ segs, c ∈ s.toList
  | [], c, h => by simp [intercal] at h
  | [s], c, h => Or.inr ⟨s, by simp, by simpa [intercal] using h⟩
  | s :: t :: u, c, h => by
    simp only [intercal, List.mem_append, List.mem_cons] at h
    rcases h with h | h | h
    · exact Or.inr ⟨s, by simp, h⟩
    · exact Or.inl h
    · rcases intercal_mem (t :: u) c h with h2 | ⟨x, hx, hc⟩
      · exact Or.inl h2
      · exact Or.inr ⟨x, by simp [hx], hc⟩

/-- path set に入らない文字は C0 control percent-encode set にも入らない。 -/
theorem c0Set_of_pathSet {c : Char} (h : pathSet c = false) : c0ControlSet c = false := by
  simp only [pathSet, querySet, Bool.or_eq_false_iff] at h
  exact h.1.1.1.1.1.1.1.1.1.1

/-- path set に入らない文字は space でもない。 -/
theorem ne_space_of_pathSet {c : Char} (h : pathSet c = false) : ¬c = ' ' := by
  intro he; rw [he] at h; revert h; decide

/-- scheme state の `:`：続きが `/` なら path or authority state へ。 -/
theorem run_scheme_pathOrAuthority (base : Option Url) (rest2 : List Char) (ctx : PCtx)
    (hov : ctx.over = none)
    (hf : ¬(String.ofList ctx.buffer = "file"))
    (hsp : isSpecialScheme (String.ofList ctx.buffer) = false) :
    run base .scheme (':' :: '/' :: rest2) ctx
      = run base .pathOrAuthority rest2
          { ctx with
            url := { ctx.url with scheme := String.ofList ctx.buffer }
            buffer := [] } := by
  rw [run, step]
  rw [if_neg (by decide), if_pos (by decide)]
  simp only [hov, Option.isSome_none, Bool.false_eq_true, if_false]
  rw [if_neg (by simpa using hf), if_neg (by simp [Url.isSpecial, hsp]),
    if_neg (by simp [Url.isSpecial, hsp])]

/-- path or authority state：`/` でなければ path state へ、読んだ文字ごと渡す。 -/
theorem run_pathOrAuthority_path (base : Option Url) (l : List Char) (ctx : PCtx)
    (h : ∀ c ∈ l.head?, ¬c = '/') :
    run base .pathOrAuthority l ctx = run base .path l ctx := by
  cases l with
  | nil => rw [run, step]; simp
  | cons c t =>
    rw [run, step]
    rw [if_neg (by simpa using h c rfl)]

/-- segment の列の先頭の文字は、先頭 segment の文字である（先頭が空でなければ）。 -/
theorem intercal_head_ne_slash : ∀ (segs : List String) (c : Char),
    (∀ x t, segs = x :: t → t ≠ [] → ¬x = "") →
    (∀ x ∈ segs, ∀ d ∈ x.toList, ¬d = '/') →
    c ∈ (intercal segs).head? → ¬c = '/'
  | [], c, _, _, h => by simp [intercal] at h
  | [x], c, _, hall, h => by
    refine hall x (by simp) c ?_
    simpa [intercal] using List.mem_of_mem_head? h
  | x :: y :: u, c, hfirst, hall, h => by
    have hx : ¬x = "" := hfirst x (y :: u) rfl (by simp)
    have hxl : x.toList ≠ [] := by simp_all
    cases hxx : x.toList with
    | nil => exact absurd hxx hxl
    | cons d t =>
      refine hall x (by simp) c ?_
      simp only [intercal, hxx, List.cons_append, List.head?_cons, Option.mem_def,
        Option.some.injEq] at h
      rw [hxx, ← h]
      simp

/-- 最後の segment を戻すと元の列になる。 -/
theorem dropLast_getLast? : ∀ (l : List String), l ≠ [] →
    l.dropLast ++ [l.getLast?.getD ""] = l
  | [], h => absurd rfl h
  | [s], _ => by simp
  | s :: t :: u, _ => by
    rw [List.dropLast_cons_cons, List.getLast?_cons_cons, List.cons_append,
      dropLast_getLast? (t :: u) (by simp)]

/-- scheme に使える文字は C0 control でも space でもない。 -/
theorem ne_c0_of_schemeChar {c : Char} (h : schemeChar c = true) :
    isC0ControlOrSpace c = false := by
  simp only [schemeChar, isAsciiAlphanumeric, isAsciiDigit, isAsciiAlpha, isAsciiUpperAlpha,
    isAsciiLowerAlpha, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  simp only [isC0ControlOrSpace, decide_eq_false_iff_not, Nat.not_le]
  rcases h with (((h | h | h) | h) | h) | h <;> first | omega | (subst h; decide)

/--
**`/` で始まる path を持つ URL は、serialize して parse し直すと元に戻る。**

`parse ∘ serialize = id` のうち、host を持たない非 special な URL の経路
（scheme start → scheme → path or authority → path）である。
先頭 segment が空で segment が二つ以上のときは serializer が `/.` を前置するので、
その場合は除いてある。
-/
theorem roundtrip_path {s : String} {segs : List String} {a : Char} {rest : List Char}
    (hs : s.toList = a :: rest) (ha : isAsciiLowerAlpha a = true)
    (hr : ∀ c ∈ rest, schemeChar c = true)
    (hlow : s.toList.map asciiLowerChar = s.toList)
    (hsp : isSpecialScheme s = false)
    (hne : segs ≠ [])
    (hfirst : ∀ x t, segs = x :: t → t ≠ [] → ¬x = "")
    (hall : ∀ x ∈ segs, (∀ c ∈ x.toList, pathSet c = false ∧ ¬c = '/' ∧ ¬c = '?' ∧ ¬c = '#') ∧
      isSingleDot x.toList = false ∧ isDoubleDot x.toList = false) :
    basicUrlParse (urlSerializer { scheme := s, path := .list segs }) none
      = some { scheme := s, path := .list segs } := by
  have haa : isAsciiAlpha a = true := by
    simp only [isAsciiAlpha, Bool.or_eq_true]; exact Or.inr ha
  have hstr : (urlSerializer { scheme := s, path := .list segs }).toList
      = s.toList ++ ':' :: '/' :: intercal segs := by
    have hout : serializerTail { scheme := s, path := .list segs } false
        = pathSerializer (.list segs) := by
      simp only [serializerTail]
      cases segs with
      | nil => exact absurd rfl hne
      | cons x t =>
        cases t with
        | nil => simp
        | cons y u =>
          simp only []
          rw [if_neg (by simpa using hfirst x (y :: u) rfl (by simp))]
          simp
    simp only [urlSerializer, hout]
    rw [show (s ++ ":" ++ pathSerializer (.list segs)).toList
        = (s ++ ":").toList ++ (pathSerializer (.list segs)).toList from by simp]
    rw [pathSerializer_intercal segs hne]
    simp
  have hbuf : ([] : List Char) ++ [asciiLowerChar a] ++ rest.map asciiLowerChar = s.toList := by
    rw [List.nil_append, List.singleton_append, ← List.map_cons, ← hs, hlow]
  have hfile : ¬s = "file" := by
    intro he; rw [he] at hsp; exact absurd hsp (by decide)
  have hallc : ∀ c ∈ s.toList ++ ':' :: '/' :: intercal segs, isC0ControlOrSpace c = false := by
    intro c hcm
    rcases List.mem_append.mp hcm with hcm | hcm
    · rw [hs] at hcm
      rcases List.mem_cons.mp hcm with rfl | hcm
      · simp only [isAsciiLowerAlpha, Bool.and_eq_true, decide_eq_true_eq] at ha
        simp only [isC0ControlOrSpace, decide_eq_false_iff_not, Nat.not_le]
        omega
      · exact ne_c0_of_schemeChar (hr c hcm)
    · rcases List.mem_cons.mp hcm with rfl | hcm
      · decide
      · rcases List.mem_cons.mp hcm with rfl | hcm
        · decide
        · rcases intercal_mem segs c hcm with rfl | ⟨x, hx, hc⟩
          · decide
          · exact ne_c0_of_c0Set (c0Set_of_pathSet ((hall x hx).1 c hc).1)
              (ne_space_of_pathSet ((hall x hx).1 c hc).1)
  have hpre : preprocess (urlSerializer { scheme := s, path := .list segs })
      = s.toList ++ ':' :: '/' :: intercal segs := by
    rw [preprocess_eq_self ?head ?last ?tab, hstr]
    case head =>
      intro c hcm
      rw [hstr] at hcm
      exact hallc c (List.mem_of_mem_head? hcm)
    case last =>
      intro c hcm
      rw [hstr, List.head?_reverse] at hcm
      exact hallc c (List.mem_of_mem_getLast? hcm)
    case tab =>
      intro c hcm
      rw [hstr] at hcm
      have := hallc c hcm
      simp only [isC0ControlOrSpace, decide_eq_false_iff_not, Nat.not_le] at this
      omega
  -- 最後の segment を取り出す。
  cases hlast : segs.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp hlast) hne
  | some last =>
    have hlmem : last ∈ segs := List.mem_of_mem_getLast? hlast
    unfold basicUrlParse
    rw [hpre, hs, List.cons_append]
    rw [run_schemeStart_step none _ a (rest ++ ':' :: '/' :: intercal segs) haa]
    rw [run_scheme_prefix none rest (':' :: '/' :: intercal segs) _ hr]
    rw [run_scheme_pathOrAuthority none (intercal segs) _ rfl
      (by rw [hbuf, String.ofList_toList]; exact hfile)
      (by rw [hbuf, String.ofList_toList]; exact hsp)]
    rw [hbuf, String.ofList_toList]
    rw [run_pathOrAuthority_path none (intercal segs) _
      (fun c hc => intercal_head_ne_slash segs c hfirst
        (fun x hx d hd => ((hall x hx).1 d hd).2.1) hc)]
    rw [show intercal segs = intercal segs ++ ([] : List Char) from by simp]
    rw [run_path_segs none segs [] _ [] rfl rfl (by simp [Url.isSpecial, hsp]) rfl hfile hall]
    rw [run_path_eof]
    rw [hlast]
    simp only [Option.getD_some]
    rw [pathStepUrl_append (pre := ([] : List String) ++ segs.dropLast) rfl hfile
      (hall last hlmem).2.1 (hall last hlmem).2.2]
    simp only [List.nil_append]
    rw [show segs.dropLast ++ [last] = segs from by
      have := dropLast_getLast? segs hne
      rw [hlast] at this
      simpa using this]

/-- 仮定が空でないことの確認。`sc:/a/b` は実際にこの形である。 -/
example : basicUrlParse (urlSerializer { scheme := "sc", path := .list ["a", "b"] }) none
    = some { scheme := "sc", path := .list ["a", "b"] } :=
  roundtrip_path (a := 's') (rest := ['c']) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
    (by intro x t h _; simp only [List.cons.injEq] at h; rw [← h.1]; simp)
    (by decide)

/-! ## 組み立て -/

/--
opaque path state が区切りまでの文字を読み切る。

`?` と `#` は出口なので入力に無いこととした。space はそのまま積まれるが、
**末尾の space だけは別**である（次が `?` か `#` なら `%20` になる）。
parser はそういう opaque path を作らないので、無いことを仮定する。
-/
theorem run_opaquePath_chunk (base : Option Url) : ∀ (l tail : List Char) (ctx : PCtx) (p : String),
    ctx.url.path = .opaque p →
    (∀ c ∈ l, c0ControlSet c = false ∧ ¬c = '?' ∧ ¬c = '#') →
    (∀ c ∈ l.getLast?, ¬c = ' ') →
    run base .opaquePath (l ++ tail) ctx
      = run base .opaquePath tail
          { ctx with url := { ctx.url with path := .opaque (p ++ String.ofList l) } } := by
  intro l
  induction l with
  | nil =>
    intro tail ctx p hp _ _
    simp only [List.nil_append, String.ofList_nil]
    have h1 : ({ ctx.url with path := Path.opaque (p ++ "") } : Url)
        = { ctx.url with path := ctx.url.path } := by rw [hp]; simp
    rw [h1]
  | cons c l' ih =>
    intro tail ctx p hp hd hend
    have hc := hd c (by simp)
    have henc : encChar c0ControlSet c = String.ofList [c] := by
      unfold encChar
      rw [utf8PercentEncode_id (by intro x hx; simp at hx; subst hx; exact hc.1)]
    have hend' : ∀ x ∈ l'.getLast?, ¬x = ' ' := by
      intro x hx
      refine hend x ?_
      cases l' with
      | nil => simp at hx
      | cons d t => rw [List.getLast?_cons_cons]; exact hx
    have hstep : run base .opaquePath ((c :: l') ++ tail) ctx
        = run base .opaquePath (l' ++ tail)
            { ctx with url := appendOpaque ctx.url (encChar c0ControlSet c) } := by
      by_cases hsp : c = ' '
      · subst hsp
        rw [List.cons_append, run, step]
        cases hl : l' with
        | nil =>
          exact absurd (hend ' ' (by rw [hl]; rfl)) (by simp)
        | cons d t =>
          have h1 : ¬d = '?' := (hd d (by rw [hl]; simp)).2.1
          have h2 : ¬d = '#' := (hd d (by rw [hl]; simp)).2.2
          simp only [List.cons_append, List.head?_cons]
          split
          · next hq => exact absurd (Option.some.inj hq) h1
          · next hq => exact absurd (Option.some.inj hq) h2
          · simp [henc]
      · rw [List.cons_append, run, step]
        all_goals first
          | rfl
          | (intro he; exact absurd he hc.2.1)
          | (intro he; exact absurd he hc.2.2)
          | (intro he; exact absurd he hsp)
    rw [hstep]
    rw [ih tail { ctx with url := appendOpaque ctx.url (encChar c0ControlSet c) }
      (p ++ encChar c0ControlSet c) (by simp [appendOpaque, hp])
      (fun x hx => hd x (by simp [hx])) hend']
    simp only [appendOpaque, hp, henc]
    simp
    rw [String.push_eq_append, String.append_assoc]

/-- 末尾の一文字。区切りの後ろが空なら区切り自身が最後になる。 -/
theorem getLast?_mid (l1 : List Char) (c : Char) (l2 : List Char) :
    (l1 ++ c :: l2).getLast? = if l2.isEmpty then some c else l2.getLast? := by
  rw [← List.head?_reverse, reverse_head_mid]
  cases l2 with
  | nil => simp
  | cons d t => exact List.head?_reverse

/--
**opaque path を持つ URL は、serialize して parse し直すと元に戻る。**

`parse ∘ serialize = id` のうち、いちばん短い経路
（scheme start → scheme → opaque path → query → fragment）を閉じたものである。
仮定はその経路を通る形であること、つまり `canonicalUrl` のうち
scheme・opaque path・query・fragment に当たる分である。
-/
theorem roundtrip_opaque {s o : String} {q f : Option String} {a : Char} {rest : List Char}
    (hs : s.toList = a :: rest) (ha : isAsciiLowerAlpha a = true)
    (hr : ∀ c ∈ rest, schemeChar c = true)
    (hlow : s.toList.map asciiLowerChar = s.toList)
    (hsp : isSpecialScheme s = false)
    (ho : ∀ c ∈ o.toList, c0ControlSet c = false ∧ ¬c = '?' ∧ ¬c = '#')
    (hlast : ∀ c ∈ o.toList.getLast?, ¬c = ' ')
    (hhead : ∀ c ∈ o.toList.head?, ¬c = '/')
    (hqc : ∀ x, q = some x → ∀ c ∈ x.toList, querySet c = false)
    (hfc : ∀ x, f = some x → ∀ c ∈ x.toList, fragmentSet c = false) :
    basicUrlParse
        (urlSerializer { scheme := s, path := .opaque o, query := q, fragment := f }) none
      = some { scheme := s, path := .opaque o, query := q, fragment := f } := by
  have haa : isAsciiAlpha a = true := by
    simp only [isAsciiAlpha, Bool.or_eq_true]; exact Or.inr ha
  have hstr : (urlSerializer { scheme := s, path := .opaque o, query := q, fragment := f }).toList
      = s.toList ++ ':' :: (o.toList ++ qfList q f) := by
    cases q <;> cases f <;>
      simp [urlSerializer, serializerTail, pathSerializer, qfList]
  have hbuf : ([] : List Char) ++ [asciiLowerChar a] ++ rest.map asciiLowerChar = s.toList := by
    rw [List.nil_append, List.singleton_append, ← List.map_cons, ← hs, hlow]
  have hfile : ¬s = "file" := by
    intro he; rw [he] at hsp; exact absurd hsp (by decide)
  -- 前処理が何もしないこと。前後の一文字と、tab / newline が無いことを見る。
  have hpre : preprocess (urlSerializer { scheme := s, path := .opaque o, query := q, fragment := f })
      = s.toList ++ ':' :: (o.toList ++ qfList q f) := by
    rw [preprocess_eq_self ?head ?last ?tab, hstr]
    case head =>
      intro c hcm
      rw [hstr, hs] at hcm
      simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hcm
      subst hcm
      simp only [isAsciiLowerAlpha, Bool.and_eq_true, decide_eq_true_eq] at ha
      simp only [isC0ControlOrSpace, decide_eq_false_iff_not, Nat.not_le]
      omega
    case last =>
      intro c hcm
      rw [hstr, List.head?_reverse, getLast?_mid] at hcm
      cases hB : (o.toList ++ qfList q f).isEmpty with
      | true =>
        rw [hB] at hcm
        simp at hcm
        subst hcm; decide
      | false =>
        rw [hB] at hcm
        -- 最後の成分で場合分けする。
        cases f with
        | some fs =>
          rw [show o.toList ++ qfList q (some fs) = (o.toList ++ (match q with
                | none => [] | some x => '?' :: x.toList)) ++ '#' :: fs.toList from by
              unfold qfList; cases q <;> simp, getLast?_mid] at hcm
          cases hfs : fs.toList.isEmpty with
          | true =>
            rw [hfs] at hcm
            simp at hcm
            subst hcm; decide
          | false =>
            rw [hfs] at hcm
            exact ne_c0_of_c0Set
              (c0Set_of_fragmentSet (hfc fs rfl c (List.mem_of_mem_getLast? hcm)))
              (ne_space_of_fragmentSet (hfc fs rfl c (List.mem_of_mem_getLast? hcm)))
        | none =>
          cases q with
          | some qs =>
            rw [show o.toList ++ qfList (some qs) none = o.toList ++ '?' :: qs.toList from by
                simp [qfList], getLast?_mid] at hcm
            cases hqs : qs.toList.isEmpty with
            | true =>
              rw [hqs] at hcm
              simp at hcm
              subst hcm; decide
            | false =>
              rw [hqs] at hcm
              exact ne_c0_of_c0Set
                (c0Set_of_querySet (hqc qs rfl c (List.mem_of_mem_getLast? hcm)))
                (ne_space_of_querySet (hqc qs rfl c (List.mem_of_mem_getLast? hcm)))
          | none =>
            rw [show o.toList ++ qfList (none : Option String) (none : Option String)
                = o.toList from by unfold qfList; simp] at hcm
            exact ne_c0_of_c0Set (ho c (List.mem_of_mem_getLast? hcm)).1 (hlast c hcm)
    case tab =>
      intro c hcm
      rw [hstr] at hcm
      rcases List.mem_append.mp hcm with hcm | hcm
      · rw [hs] at hcm
        rcases List.mem_cons.mp hcm with rfl | hcm
        · simp only [isAsciiLowerAlpha, Bool.and_eq_true, decide_eq_true_eq] at ha
          omega
        · exact schemeChar_ne_tab (hr c hcm)
      · rcases List.mem_cons.mp hcm with rfl | hcm
        · decide
        · rcases List.mem_append.mp hcm with hcm | hcm
          · exact ne_tab_of_c0Set (ho c hcm).1
          · unfold qfList at hcm
            rcases List.mem_append.mp hcm with hcm | hcm
            · cases q with
              | none => simp at hcm
              | some qs =>
                rcases List.mem_cons.mp hcm with rfl | hcm
                · decide
                · exact ne_tab_of_c0Set (c0Set_of_querySet (hqc qs rfl c hcm))
            · cases f with
              | none => simp at hcm
              | some fs =>
                rcases List.mem_cons.mp hcm with rfl | hcm
                · decide
                · exact ne_tab_of_c0Set (c0Set_of_fragmentSet (hfc fs rfl c hcm))
  unfold basicUrlParse
  rw [hpre, hs, List.cons_append]
  rw [run_schemeStart_step none _ a (rest ++ ':' :: (o.toList ++ qfList q f)) haa]
  rw [run_scheme_prefix none rest (':' :: (o.toList ++ qfList q f)) _ hr]
  rw [run_scheme_opaque none (o.toList ++ qfList q f) _ rfl
    (by rw [hbuf, String.ofList_toList]; exact hfile)
    (by rw [hbuf, String.ofList_toList]; exact hsp)
    (by intro r hrr
        cases hoo : o.toList with
        | nil =>
          rw [hoo] at hrr
          simp only [List.nil_append] at hrr
          unfold qfList at hrr
          cases q with
          | some qs => simp at hrr; rw [← hrr]; decide
          | none =>
            cases f with
            | some fs => simp at hrr; rw [← hrr]; decide
            | none => simp at hrr
        | cons d t =>
          rw [hoo] at hrr
          simp only [List.cons_append, List.head?_cons, Option.mem_def,
            Option.some.injEq] at hrr
          subst hrr
          exact hhead d (by rw [hoo]; rfl))]
  rw [hbuf, String.ofList_toList]
  rw [run_opaquePath_chunk none o.toList (qfList q f) _ "" rfl ho hlast]
  rw [run_opaquePath_qf none _ q f rfl rfl rfl rfl
    (fun x hx c hc => by simpa [Url.isSpecial, hsp] using hqc x hx c hc)
    (fun x hx c hc => hfc x hx c hc)]
  simp

/-- 仮定が空でないことの確認。`sc:x?a#b` は実際にこの形である。 -/
example : basicUrlParse (urlSerializer
      { scheme := "sc", path := .opaque "x", query := some "a", fragment := some "b" }) none
    = some { scheme := "sc", path := .opaque "x", query := some "a", fragment := some "b" } :=
  roundtrip_opaque (a := 's') (rest := ['c']) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end Url
