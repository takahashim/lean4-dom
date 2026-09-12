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
* `roundtrip_host`：host を持つ URL。`sc://h/a` も `http://h/a/b` も、credentials 付きも
  port 付きも IPv6 host も。special かどうかは `sp : Bool` で持つ

どれも `canonicalUrl` のうち通る成分に当たる条件を仮定して `parse ∘ serialize = id` を言う。

作り方は state ごとの等式を積む形で、`Url/ApiValid.lean` の setter の肯定側と同じである。
一つの state について三種類を用意する。

* **chunk**：区切りでない文字を読み切って同じ state に留まる（`run_opaquePath_chunk` ほか）
* **区切り**：1 文字で次の state へ渡す（`run_opaquePath_question` ほか）
* **終端**：EOF で `.ok` を返す（`run_opaquePath_eof` ほか）

残っているのは `file:`（file state）である。

port には 10 進の往復（`portValue_toString`）が要った。`Nat.toDigitsCore` についての
帰納法で、桁を積む向きと読む向きが逆になるので `portValue (l1 ++ l2)` の形を経由する。
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
  -- path が空だと serialize しても跡が残らない（host が null のとき）。
  -- special な URL も同じで、`http://h` を読み直すと segment が一つ（空）できる。
  -- parser はこの二つの場合に必ず segment を一つ以上書く。
  (match u.host, u.path with | none, .list [] => false | _, _ => true) &&
  (!u.isSpecial || (match u.path with | .list [] => false | _ => true)) &&
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

/-- query も fragment も無い URL は、その二つを `none` と書き直しても同じものである。 -/
theorem url_qf_eta {u : Url} (hq : u.query = none) (hf : u.fragment = none) :
    ({ u with query := none, fragment := none } : Url) = u := by
  cases u
  simp_all

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

/-- fragment state は fragment を読み切って返す。 -/
theorem run_fragment_full (base : Option Url) (fs : String) (ctx : PCtx)
    (hf : ctx.url.fragment = some "") (h : ∀ c ∈ fs.toList, fragmentSet c = false) :
    run base .fragment fs.toList ctx = .ok { ctx.url with fragment := some fs } := by
  rw [run_fragment_plain base fs.toList ctx "" hf h]
  simp

/--
query state は query を読み切り、`#` があれば fragment へ渡す。

`tail` を仮引数にしてあるのは、`match f with` の作る matcher が
仮定 `hfc` を巻き込んでしまい、そのままでは `rw` の対象に合わないためである。
-/
theorem run_query_full (base : Option Url) (qs : String) (f : Option String)
    (tail : List Char) (ctx : PCtx)
    (htail : tail = match f with | none => [] | some fs => '#' :: fs.toList)
    (hov : ctx.over = none) (hb : ctx.buffer = []) (hq : ctx.url.query = some "")
    (hf0 : ctx.url.fragment = none)
    (hqc : ∀ c ∈ qs.toList,
      (if ctx.url.isSpecial then specialQuerySet else querySet) c = false)
    (hfc : ∀ x, f = some x → ∀ c ∈ x.toList, fragmentSet c = false) :
    run base .query (qs.toList ++ tail) ctx
      = .ok { ctx.url with query := some qs, fragment := f } := by
  subst htail
  have hnh : ∀ c ∈ qs.toList, ¬c = '#' := by
    intro c hc
    have := hqc c hc
    intro he
    rw [he] at this
    cases hsx : ctx.url.isSpecial <;> rw [hsx] at this <;> revert this <;> decide
  have hqe : utf8PercentEncode (if ctx.url.isSpecial then specialQuerySet else querySet)
      qs.toList = qs.toList := utf8PercentEncode_id hqc
  cases f with
  | none =>
    simp only [List.append_nil]
    rw [run_query_plain base qs.toList ctx hov hnh]
    simp only [queryOf, hb, List.nil_append, hq, hqe, String.ofList_toList]
    rw [← hf0]
    simp
  | some fs =>
    rw [run_query_chunk base qs.toList ('#' :: fs.toList) ctx hnh]
    rw [run_query_hash base fs.toList { ctx with buffer := ctx.buffer ++ qs.toList } hov]
    rw [run_fragment_full base fs _ rfl (hfc fs rfl)]
    simp only [queryOf, hb, List.nil_append, hq, hqe, String.ofList_toList]
    simp

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

/-- special-query set に入らない文字は query set にも入らない。 -/
theorem querySet_of_specialQuerySet {c : Char} (h : specialQuerySet c = false) :
    querySet c = false := by
  simp only [specialQuerySet, Bool.or_eq_false_iff] at h
  exact h.1

/-- special かどうかで選ぶ query set のどちらでも、入らなければ query set に入らない。 -/
theorem querySet_of_ite {b : Bool} {c : Char}
    (h : (if b then specialQuerySet else querySet) c = false) : querySet c = false := by
  cases b with
  | true => exact querySet_of_specialQuerySet (by simpa using h)
  | false => simpa using h

/-- query と fragment に現れる文字は、C0 control でも space でもない。 -/
theorem qfList_c0 {q f : Option String}
    (hqc : ∀ s, q = some s → ∀ c ∈ s.toList, querySet c = false)
    (hfc : ∀ s, f = some s → ∀ c ∈ s.toList, fragmentSet c = false) :
    ∀ c ∈ qfList q f, isC0ControlOrSpace c = false := by
  intro c hcm
  unfold qfList at hcm
  rcases List.mem_append.mp hcm with hcm | hcm
  · cases q with
    | none => simp at hcm
    | some qs =>
      rcases List.mem_cons.mp hcm with rfl | hcm
      · decide
      · exact ne_c0_of_c0Set (c0Set_of_querySet (hqc qs rfl c hcm))
          (ne_space_of_querySet (hqc qs rfl c hcm))
  · cases f with
    | none => simp at hcm
    | some fs =>
      rcases List.mem_cons.mp hcm with rfl | hcm
      · decide
      · exact ne_c0_of_c0Set (c0Set_of_fragmentSet (hfc fs rfl c hcm))
          (ne_space_of_fragmentSet (hfc fs rfl c hcm))

/-! ## path

host を持たない非 special な URL の経路。scheme state から path or authority state へ入る。
-/

/-- 区切りでないことを、文字ごとの条件から言う。 -/
theorem isTerminator_false {sp : Bool} {c : Char} (h1 : ¬c = '/') (h2 : ¬c = '?') (h3 : ¬c = '#')
    (h4 : sp = true → ¬c = '\\') : isTerminator sp (some c) = false := by
  simp only [isTerminator, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  refine ⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩
  cases sp with
  | false => simp
  | true => simp [h4 rfl]

/-- path state が区切りでない文字を読み切る。 -/
theorem run_path_chunk (base : Option Url) (sp : Bool) :
    ∀ (l tail : List Char) (ctx : PCtx),
    ctx.url.isSpecial = sp → ctx.over = none →
    (∀ c ∈ l, pathSet c = false ∧ isTerminator sp (some c) = false) →
    run base .path (l ++ tail) ctx
      = run base .path tail { ctx with buffer := ctx.buffer ++ l } := by
  intro l
  induction l with
  | nil => intro tail ctx _ _ _; simp
  | cons c rest ih =>
    intro tail ctx hsp hov h
    have hc := h c (by simp)
    have ht := hc.2
    simp only [isTerminator, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at ht
    have henc : encChar pathSet c = String.ofList [c] := by
      unfold encChar
      rw [utf8PercentEncode_id (by intro x hx; simp at hx; subst hx; exact hc.1)]
    simp only [List.cons_append]
    rw [run, step]
    rw [if_neg (by simp [hsp, ht.1.1.1, ht.1.1.2, ht.1.2, ht.2, hov])]
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
theorem run_path_segs (base : Option Url) (sp : Bool) :
    ∀ (segs : List String) (tail : List Char) (ctx : PCtx) (pre : List String),
    ctx.url.path = .list pre → ctx.buffer = [] →
    ctx.url.isSpecial = sp → ctx.over = none → ¬ctx.url.scheme = "file" →
    (∀ s ∈ segs, (∀ c ∈ s.toList, pathSet c = false ∧ isTerminator sp (some c) = false) ∧
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
      rw [run_path_chunk base sp s.toList tail ctx hsp hov hs.1]
      have h1 : ({ ctx.url with path := Path.list (pre ++ ([s] : List String).dropLast) } : Url)
          = ctx.url := by
        show ({ ctx.url with path := Path.list (pre ++ ([] : List String)) } : Url) = ctx.url
        rw [List.append_nil, ← hp]
      rw [h1, hb, List.nil_append]
      simp
    | cons t u =>
      show run base .path ((s.toList ++ '/' :: intercal (t :: u)) ++ tail) ctx = _
      rw [List.append_assoc]
      rw [run_path_chunk base sp s.toList ('/' :: intercal (t :: u) ++ tail) ctx hsp hov hs.1]
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

/-- serializer が path を並べる分（host の後ろ）。 -/
def pathChars : List String → List Char
  | [] => []
  | s :: rest => '/' :: intercal (s :: rest)

/-- path の serialize は `pathChars` である。 -/
theorem pathSerializer_pathChars : ∀ (segs : List String),
    (pathSerializer (.list segs)).toList = pathChars segs
  | [] => rfl
  | s :: rest => by rw [pathSerializer_intercal (s :: rest) (by simp)]; rfl

/-! ## special

`http:` などの経路。scheme state から special authority slashes state へ入り、
`//` を読み飛ばして authority state に着く。path state では `\\` も区切りになる。
-/

/-- scheme state の `:`：special な scheme で base が無ければ special authority slashes へ。 -/
theorem run_scheme_specialAuthoritySlashes (rest : List Char) (ctx : PCtx)
    (hov : ctx.over = none) (hf : ¬(String.ofList ctx.buffer = "file"))
    (hsp : isSpecialScheme (String.ofList ctx.buffer) = true) :
    run none .scheme (':' :: rest) ctx
      = run none .specialAuthoritySlashes rest
          { ctx with
            url := { ctx.url with scheme := String.ofList ctx.buffer }
            buffer := [] } := by
  rw [run, step]
  rw [if_neg (by decide), if_pos (by decide)]
  simp only [hov, Option.isSome_none, Bool.false_eq_true, if_false]
  rw [if_neg (by simpa using hf), if_neg (by simp [Url.isSpecial, hsp]),
    if_pos (by simp [Url.isSpecial, hsp])]

/-- special authority slashes state：`//` を読み飛ばす。 -/
theorem run_specialAuthoritySlashes (base : Option Url) (rest2 : List Char) (ctx : PCtx) :
    run base .specialAuthoritySlashes ('/' :: '/' :: rest2) ctx
      = run base .specialAuthorityIgnoreSlashes rest2 ctx := by
  rw [run, step]

/-- special authority ignore slashes state：`/` でも `\` でもなければ authority へ。 -/
theorem run_specialAuthorityIgnoreSlashes (base : Option Url) (l : List Char) (ctx : PCtx)
    (h : ∀ c ∈ l.head?, ¬c = '/' ∧ ¬c = '\\') :
    run base .specialAuthorityIgnoreSlashes l ctx = run base .authority l ctx := by
  cases l with
  | nil => rw [run, step]
  | cons c t =>
    have hc := h c rfl
    rw [run, step]
    rw [if_neg (by simp [hc.1, hc.2])]

/-- path start state：special なら `/` を一つ落として path state へ。 -/
theorem run_pathStart_slash_special (base : Option Url) (rest : List Char) (ctx : PCtx)
    (hsp : ctx.url.isSpecial = true) :
    run base .pathStart ('/' :: rest) ctx = run base .path rest ctx := by
  rw [run, step]
  rw [if_pos (by simp [hsp])]
  simp

/-- path state の `?`。最後の segment を確定させて query state へ渡す。 -/
theorem run_path_question (base : Option Url) (rest : List Char) (ctx : PCtx)
    (hov : ctx.over = none) :
    run base .path ('?' :: rest) ctx
      = run base .query rest
          { ctx with
            url := { pathStepUrl ctx.url false ctx.buffer with query := some "" }
            buffer := [] } := by
  rw [run, step]
  rw [if_pos (by simp [hov])]
  simp

/-- path state の `#`。最後の segment を確定させて fragment state へ渡す。 -/
theorem run_path_hash (base : Option Url) (rest : List Char) (ctx : PCtx)
    (hov : ctx.over = none) :
    run base .path ('#' :: rest) ctx
      = run base .fragment rest
          { ctx with
            url := { pathStepUrl ctx.url false ctx.buffer with fragment := some "" }
            buffer := [] } := by
  rw [run, step]
  rw [if_pos (by simp [hov])]
  simp

/-- path state が path と query と fragment を読み切る。 -/
theorem run_path_full (base : Option Url) (sp : Bool) (segs : List String) (q f : Option String)
    (ctx : PCtx)
    (hsp : ctx.url.isSpecial = sp) (hov : ctx.over = none)
    (hpath : ctx.url.path = .list []) (hb : ctx.buffer = []) (hnf : ¬ctx.url.scheme = "file")
    (hq0 : ctx.url.query = none) (hf0 : ctx.url.fragment = none)
    (hne : segs ≠ [])
    (hall : ∀ x ∈ segs, (∀ c ∈ x.toList, pathSet c = false ∧ isTerminator sp (some c) = false) ∧
      isSingleDot x.toList = false ∧ isDoubleDot x.toList = false)
    (hqc : ∀ x, q = some x → ∀ c ∈ x.toList,
      (if ctx.url.isSpecial then specialQuerySet else querySet) c = false)
    (hfc : ∀ x, f = some x → ∀ c ∈ x.toList, fragmentSet c = false) :
    run base .path (intercal segs ++ qfList q f) ctx
      = .ok { ctx.url with path := .list segs, query := q, fragment := f } := by
  cases hseg : segs with
  | nil => exact absurd hseg hne
  | cons x t =>
    rw [run_path_segs base sp (x :: t) (qfList q f) ctx [] ?p1 ?p2 ?p3 ?p4 ?p5 ?p6]
    case p1 => exact hpath
    case p2 => exact hb
    case p3 => exact hsp
    case p4 => exact hov
    case p5 => exact hnf
    case p6 => rw [← hseg]; exact hall
    cases hlast : (x :: t).getLast? with
    | none => simp at hlast
    | some last =>
      have hlmem : last ∈ (x :: t) := List.mem_of_mem_getLast? hlast
      have hlall := hall last (by rw [hseg]; exact hlmem)
      have hdl : (x :: t).dropLast ++ [last] = x :: t := by
        have := dropLast_getLast? (x :: t) (by simp)
        rw [hlast] at this
        simpa using this
      -- 最後の segment を確定させる。ここから先は query と fragment の有無で分かれる。
      have hcommit : pathStepUrl
          { ctx.url with path := Path.list (x :: t).dropLast } false last.toList
          = { ctx.url with path := Path.list (x :: t) } := by
        rw [pathStepUrl_append (pre := (x :: t).dropLast) rfl (by simpa using hnf)
          hlall.2.1 hlall.2.2]
        rw [hdl]
      simp only [Option.getD_some]
      cases q with
      | none =>
        cases f with
        | none =>
          simp only [qfList, List.append_nil, List.nil_append]
          rw [run_path_eof]
          dsimp only
          rw [hcommit]
          simp [hq0, hf0]
        | some fs =>
          simp only [qfList, List.nil_append]
          rw [run_path_hash base fs.toList _ ?h1]
          case h1 => exact hov
          dsimp only
          rw [hcommit]
          rw [run_fragment_full base fs _ rfl (hfc fs rfl)]
          simp [hq0]
      | some qs =>
        simp only [qfList, List.cons_append, List.nil_append]
        rw [run_path_question base _ _ ?h3]
        case h3 => exact hov
        dsimp only
        rw [hcommit]
        dsimp only
        rw [run_query_full base qs f _ _ ?g0 ?g1 ?g2 ?g3 ?g4 ?g5 ?g6]
        case g0 => rfl
        case g1 => simp [hov]
        case g2 => rfl
        case g3 => rfl
        case g4 => simpa using hf0
        case g5 => exact hqc qs rfl
        case g6 => exact hfc

/--
path state の `./`。single-dot segment は何も足さずに消える。

serializer が host の無い URL の先頭に付ける `/.` を読み直すところである。
-/
theorem run_path_dot (base : Option Url) (rest : List Char) (ctx : PCtx) (hb : ctx.buffer = []) :
    run base .path ('.' :: '/' :: rest) ctx = run base .path rest ctx := by
  rw [run, step]
  rw [if_neg (by simp)]
  rw [run, step]
  rw [if_pos (by simp)]
  have henc : (encChar pathSet '.').toList = ['.'] := by decide
  have hstep : pathStepUrl ctx.url true ['.'] = ctx.url := by
    unfold pathStepUrl
    rw [if_neg (by decide), if_pos (by decide)]
    simp
  simp only [hb, List.nil_append, henc]
  split
  · next he => simp at he
  · next he => simp at he
  · next he => simp at he
  · simp only [beq_self_eq_true, Bool.true_or, hstep]
    rw [← hb]

/-- host の無い URL で、先頭 segment が空のときに serializer が足す `/.`。 -/
def dotPrefix (segs : List String) : List Char :=
  match segs with
  | seg :: _ :: _ => if seg.isEmpty then ['/', '.'] else []
  | _ => []

/--
**`/` で始まる path を持つ URL は、serialize して parse し直すと元に戻る。**

`parse ∘ serialize = id` のうち、host を持たない非 special な URL の経路
（scheme start → scheme → path or authority → path）である。
先頭 segment が空で segment が二つ以上のときは serializer が `/.` を前置するが、
parse がそれを single-dot segment として落とすので、そこも入っている。
-/
theorem roundtrip_path {s : String} {segs : List String} {q f : Option String}
    {a : Char} {rest : List Char}
    (hs : s.toList = a :: rest) (ha : isAsciiLowerAlpha a = true)
    (hr : ∀ c ∈ rest, schemeChar c = true)
    (hlow : s.toList.map asciiLowerChar = s.toList)
    (hsp : isSpecialScheme s = false)
    (hne : segs ≠ [])
    (hqc : ∀ x, q = some x → ∀ c ∈ x.toList, querySet c = false)
    (hfc : ∀ x, f = some x → ∀ c ∈ x.toList, fragmentSet c = false)
    (hall : ∀ x ∈ segs, (∀ c ∈ x.toList, pathSet c = false ∧ ¬c = '/' ∧ ¬c = '?' ∧ ¬c = '#') ∧
      isSingleDot x.toList = false ∧ isDoubleDot x.toList = false) :
    basicUrlParse (urlSerializer
        { scheme := s, path := .list segs, query := q, fragment := f }) none
      = some { scheme := s, path := .list segs, query := q, fragment := f } := by
  have haa : isAsciiAlpha a = true := by
    simp only [isAsciiAlpha, Bool.or_eq_true]; exact Or.inr ha
  have hterm : ∀ x ∈ segs, ∀ c ∈ x.toList, isTerminator false (some c) = false := by
    intro x hx c hc
    have := (hall x hx).1 c hc
    exact isTerminator_false this.2.1 this.2.2.1 this.2.2.2 (by simp)
  have hall' : ∀ x ∈ segs,
      (∀ c ∈ x.toList, pathSet c = false ∧ isTerminator false (some c) = false) ∧
      isSingleDot x.toList = false ∧ isDoubleDot x.toList = false :=
    fun x hx => ⟨fun c hc => ⟨((hall x hx).1 c hc).1, hterm x hx c hc⟩,
      (hall x hx).2.1, (hall x hx).2.2⟩
  have hstr : (urlSerializer
      { scheme := s, path := .list segs, query := q, fragment := f }).toList
      = s.toList ++ ':' :: (dotPrefix segs ++ (pathChars segs ++ qfList q f)) := by
    have hout : (serializerTail
        { scheme := s, path := .list segs, query := q, fragment := f } false).toList
        = dotPrefix segs ++ (pathChars segs ++ qfList q f) := by
      simp only [serializerTail, dotPrefix, qfList]
      cases segs with
      | nil => exact absurd rfl hne
      | cons x t =>
        cases t with
        | nil => cases q <;> cases f <;> simp [pathSerializer_pathChars]
        | cons y u =>
          cases hx : x.isEmpty with
          | true =>
            cases q <;> cases f <;>
              simp [hx, String.toList_append, pathSerializer_pathChars]
          | false => cases q <;> cases f <;> simp [hx, pathSerializer_pathChars]
    simp only [urlSerializer, String.toList_append, hout]
    simp
  have hbuf : ([] : List Char) ++ [asciiLowerChar a] ++ rest.map asciiLowerChar = s.toList := by
    rw [List.nil_append, List.singleton_append, ← List.map_cons, ← hs, hlow]
  have hfile : ¬s = "file" := by
    intro he; rw [he] at hsp; exact absurd hsp (by decide)
  have hallc : ∀ c ∈ s.toList ++ ':' :: (dotPrefix segs ++ (pathChars segs ++ qfList q f)),
      isC0ControlOrSpace c = false := by
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
      · rcases List.mem_append.mp hcm with hcm | hcm
        · unfold dotPrefix at hcm
          split at hcm
          · split at hcm
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hcm
              rcases hcm with rfl | rfl <;> decide
            · simp at hcm
          · simp at hcm
        · rcases List.mem_append.mp hcm with hcm | hcm
          · cases segs with
            | nil => exact absurd rfl hne
            | cons x t =>
              rcases List.mem_cons.mp hcm with rfl | hcm
              · decide
              · rcases intercal_mem (x :: t) c hcm with rfl | ⟨y, hy, hc⟩
                · decide
                · exact ne_c0_of_c0Set (c0Set_of_pathSet ((hall y hy).1 c hc).1)
                    (ne_space_of_pathSet ((hall y hy).1 c hc).1)
          · exact qfList_c0 hqc hfc c hcm
  have hpre : preprocess (urlSerializer
      { scheme := s, path := .list segs, query := q, fragment := f })
      = s.toList ++ ':' :: (dotPrefix segs ++ (pathChars segs ++ qfList q f)) := by
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
  unfold basicUrlParse
  rw [hpre, hs, List.cons_append]
  rw [run_schemeStart_step none _ a
    (rest ++ ':' :: (dotPrefix segs ++ (pathChars segs ++ qfList q f))) haa]
  rw [run_scheme_prefix none rest (':' :: (dotPrefix segs ++ (pathChars segs ++ qfList q f))) _ hr]
  -- 先頭 segment が空で二つ以上あるときは serializer が `/.` を足す。
  have hdot : ∀ (c2 : PCtx), c2.url.isSpecial = false → c2.over = none →
      c2.url.path = .list [] → c2.buffer = [] → ¬c2.url.scheme = "file" →
      c2.url.query = none → c2.url.fragment = none →
      run none .path (intercal segs ++ qfList q f) c2
        = .ok { c2.url with path := .list segs, query := q, fragment := f } :=
    fun c2 h1 h2 h3 h4 h5 h6 h7 =>
      run_path_full none false segs q f c2 h1 h2 h3 h4 h5 h6 h7 hne hall'
        (fun x hx c hc => by rw [if_neg (by simp [h1])]; exact hqc x hx c hc) hfc
  cases hseg : segs with
  | nil => exact absurd hseg hne
  | cons x t =>
    have hpc : pathChars (x :: t) = '/' :: intercal (x :: t) := rfl
    by_cases hdp : dotPrefix (x :: t) = []
    · -- `/.` は付かない。先頭 segment は空でないか、segment が一つしかない。
      have hheadx : ∀ c ∈ (intercal (x :: t) ++ qfList q f).head?, ¬c = '/' := by
        intro c hc
        cases hi : intercal (x :: t) with
        | nil =>
          rw [hi, List.nil_append] at hc
          unfold qfList at hc
          cases q with
          | some qs =>
            simp only [List.cons_append, List.head?_cons, Option.mem_def,
              Option.some.injEq] at hc
            rw [← hc]; decide
          | none =>
            cases f with
            | some fs =>
              simp only [List.nil_append, List.head?_cons, Option.mem_def,
                Option.some.injEq] at hc
              rw [← hc]; decide
            | none => simp at hc
        | cons d u =>
        rw [hi, List.cons_append, List.head?_cons] at hc
        refine intercal_head_ne_slash (x :: t) c ?_ ?_ (by rw [hi]; exact hc)
        · intro y u hu hune
          simp only [List.cons.injEq] at hu
          rw [← hu.1]
          cases hxe : x.isEmpty with
          | true =>
            exfalso
            have hd2 : dotPrefix (x :: t) = ['/', '.'] := by
              unfold dotPrefix
              cases t with
              | nil => exact absurd hu.2.symm hune
              | cons z w => simp [hxe]
            rw [hd2] at hdp
            simp at hdp
          | false => simpa using hxe
        · exact fun y hy d hd => ((hall y (by rw [hseg]; exact hy)).1 d hd).2.1
      rw [hdp, List.nil_append, hpc, List.cons_append]
      rw [run_scheme_pathOrAuthority none (intercal (x :: t) ++ qfList q f) _ rfl
        (by rw [hbuf, String.ofList_toList]; exact hfile)
        (by rw [hbuf, String.ofList_toList]; exact hsp)]
      rw [hbuf, String.ofList_toList]
      rw [run_pathOrAuthority_path none (intercal (x :: t) ++ qfList q f) _ hheadx]
      rw [show intercal (x :: t) = intercal segs from by rw [hseg]]
      rw [hdot _ (by simp [Url.isSpecial, hsp]) rfl rfl rfl (by simpa using hfile) rfl rfl]
      simp [hseg]
    · -- `/.` が付く。`.` は single-dot segment なので消える。
      have hdp2 : dotPrefix (x :: t) = ['/', '.'] := by
        unfold dotPrefix at hdp ⊢
        cases t with
        | nil => exact absurd rfl hdp
        | cons z w =>
          cases hxe : x.isEmpty with
          | true => simp [hxe]
          | false => exact absurd (by simp [hxe]) hdp
      rw [hdp2]
      rw [show (['/', '.'] ++ (pathChars (x :: t) ++ qfList q f))
          = '/' :: '.' :: (pathChars (x :: t) ++ qfList q f) from rfl]
      rw [run_scheme_pathOrAuthority none ('.' :: (pathChars (x :: t) ++ qfList q f)) _ rfl
        (by rw [hbuf, String.ofList_toList]; exact hfile)
        (by rw [hbuf, String.ofList_toList]; exact hsp)]
      rw [hbuf, String.ofList_toList]
      rw [run_pathOrAuthority_path none ('.' :: (pathChars (x :: t) ++ qfList q f)) _ (by simp)]
      rw [hpc, List.cons_append]
      rw [run_path_dot none (intercal (x :: t) ++ qfList q f) _ rfl]
      rw [show intercal (x :: t) = intercal segs from by rw [hseg]]
      rw [hdot _ (by simp [Url.isSpecial, hsp]) rfl rfl rfl (by simpa using hfile) rfl rfl]
      simp [hseg]

/-- 先頭 segment が空でも往復する。serializer が `/.` を足し、parse が single dot で落とす。 -/
example : basicUrlParse (urlSerializer { scheme := "sc", path := .list ["", "x"] }) none
    = some { scheme := "sc", path := .list ["", "x"] } :=
  roundtrip_path (a := 's') (rest := ['c']) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by simp) (by simp) (by decide)

/-- 仮定が空でないことの確認。`sc:/a/b` は実際にこの形である。 -/
example : basicUrlParse (urlSerializer { scheme := "sc", path := .list ["a", "b"] }) none
    = some { scheme := "sc", path := .list ["a", "b"] } :=
  roundtrip_path (a := 's') (rest := ['c']) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by simp) (by simp) (by decide)

/-- path の側でも query と fragment が往復する。`sc:/a?q#f` の形である。 -/
example : basicUrlParse (urlSerializer
      { scheme := "sc", path := .list ["a"], query := some "q", fragment := some "f" }) none
    = some { scheme := "sc", path := .list ["a"], query := some "q", fragment := some "f" } :=
  roundtrip_path (a := 's') (rest := ['c']) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by simp; decide) (by simp; decide) (by decide)

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

/-! ## port

10 進で書いた port を読み直すところ。`portValue_toString` が数の往復を言う。
-/

/-- 10 進の畳み込みは、初期値を桁数ぶん持ち上げる。 -/
theorem portFold_acc : ∀ (l : List Char) (a : Nat),
    l.foldl (fun acc c => acc * 10 + (digitValue c).getD 0) a
      = a * 10 ^ l.length + l.foldl (fun acc c => acc * 10 + (digitValue c).getD 0) 0
  | [], a => by simp
  | c :: rest, a => by
    show rest.foldl _ (a * 10 + (digitValue c).getD 0) = _
    rw [portFold_acc rest (a * 10 + (digitValue c).getD 0)]
    show _ = a * 10 ^ (rest.length + 1) + rest.foldl _ (0 * 10 + (digitValue c).getD 0)
    rw [portFold_acc rest (0 * 10 + (digitValue c).getD 0)]
    rw [Nat.pow_succ]
    simp only [Nat.zero_mul, Nat.zero_add]
    rw [Nat.add_mul, Nat.mul_assoc]
    rw [Nat.mul_comm 10 (10 ^ rest.length), ← Nat.mul_assoc]
    omega

/-- 連結した 10 進の値。 -/
theorem portValue_append (l1 l2 : List Char) :
    portValue (l1 ++ l2) = portValue l1 * 10 ^ l2.length + portValue l2 := by
  unfold portValue
  rw [List.foldl_append, portFold_acc l2 (l1.foldl _ 0)]

/-- `digitChar` の逆。 -/
theorem digitValue_digitChar : ∀ (d : Nat), d < 10 → digitValue (Nat.digitChar d) = some d
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => by decide
  | _ + 10, h => absurd h (by omega)

/-- `Nat.toDigitsCore` が積む桁の値。 -/
theorem portValue_toDigitsCore : ∀ (fuel n : Nat) (ds : List Char), n < fuel →
    portValue (Nat.toDigitsCore 10 fuel n ds) = n * 10 ^ ds.length + portValue ds := by
  intro fuel
  induction fuel with
  | zero => intro n ds h; exact absurd h (by omega)
  | succ f ih =>
    intro n ds h
    rw [Nat.toDigitsCore]
    have hd : digitValue (Nat.digitChar (n % 10)) = some (n % 10) :=
      digitValue_digitChar _ (by omega)
    have hcons : portValue (Nat.digitChar (n % 10) :: ds)
        = (n % 10) * 10 ^ ds.length + portValue ds := by
      rw [show (Nat.digitChar (n % 10) :: ds) = [Nat.digitChar (n % 10)] ++ ds from rfl,
        portValue_append]
      simp [portValue, hd]
    split
    · next hz =>
      have h10 : n % 10 = n := by omega
      rw [hcons, h10]
    · next hz =>
      rw [ih (n / 10) (Nat.digitChar (n % 10) :: ds) (by omega)]
      rw [hcons]
      simp only [List.length_cons, Nat.pow_succ]
      have hn : n / 10 * (10 ^ ds.length * 10) = (n / 10 * 10) * 10 ^ ds.length := by
        rw [Nat.mul_comm (10 ^ ds.length) 10, ← Nat.mul_assoc]
      rw [hn, ← Nat.add_assoc, ← Nat.add_mul]
      have : n / 10 * 10 + n % 10 = n := by omega
      rw [this]

/-- **10 進で書いた数は、読み直すと元に戻る。** -/
theorem portValue_toString (n : Nat) : portValue (toString n).toList = n := by
  show portValue (Nat.repr n).toList = n
  unfold Nat.repr Nat.toDigits
  rw [String.toList_ofList, portValue_toDigitsCore (n + 1) n [] (by omega)]
  simp [portValue]

/-- `digitChar` が返すのは ASCII digit である。 -/
theorem isAsciiDigit_digitChar : ∀ (d : Nat), d < 10 → isAsciiDigit (Nat.digitChar d) = true
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => by decide
  | _ + 10, h => absurd h (by omega)

/-- `Nat.toDigitsCore` が積むのは digit だけである。 -/
theorem toDigitsCore_digits : ∀ (fuel n : Nat) (ds : List Char),
    (∀ c ∈ ds, isAsciiDigit c = true) →
    ∀ c ∈ Nat.toDigitsCore 10 fuel n ds, isAsciiDigit c = true := by
  intro fuel
  induction fuel with
  | zero => intro n ds h; simpa [Nat.toDigitsCore] using h
  | succ f ih =>
    intro n ds h
    rw [Nat.toDigitsCore]
    have hd : isAsciiDigit (Nat.digitChar (n % 10)) = true :=
      isAsciiDigit_digitChar _ (by omega)
    split
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hd
      · exact h c hc
    · refine ih (n / 10) (Nat.digitChar (n % 10) :: ds) ?_
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hd
      · exact h c hc

/-- `Nat.toDigitsCore` は積むだけなので、空にはならない。 -/
theorem toDigitsCore_ne_nil : ∀ (fuel n : Nat) (ds : List Char), ds ≠ [] →
    Nat.toDigitsCore 10 fuel n ds ≠ [] := by
  intro fuel
  induction fuel with
  | zero => intro n ds h; simpa [Nat.toDigitsCore] using h
  | succ f ih =>
    intro n ds h
    rw [Nat.toDigitsCore]
    split
    · simp
    · exact ih (n / 10) _ (by simp)

/-- 10 進で書いた数は空でない。 -/
theorem toString_ne_nil (n : Nat) : (toString n).toList ≠ [] := by
  show (Nat.repr n).toList ≠ []
  unfold Nat.repr Nat.toDigits
  rw [String.toList_ofList, Nat.toDigitsCore]
  split
  · simp
  · exact toDigitsCore_ne_nil _ _ _ (by simp)

/-- **10 進で書いた数は digit だけからなる。** -/
theorem toString_digits (n : Nat) : ∀ c ∈ (toString n).toList, isAsciiDigit c = true := by
  show ∀ c ∈ (Nat.repr n).toList, isAsciiDigit c = true
  unfold Nat.repr Nat.toDigits
  rw [String.toList_ofList]
  exact toDigitsCore_digits (n + 1) n [] (by simp)

/-- host state の `:`。host を確定させて port state へ移る。 -/
theorem run_host_port (base : Option Url) (sp : Bool) (rest : List Char) (ctx : PCtx) (hst : Host)
    (hov : ctx.over = none) (hsp : ctx.url.isSpecial = sp) (hib : ctx.insideBrackets = false)
    (hne : ctx.buffer ≠ [])
    (hp : hostParser ctx.toAscii ctx.buffer (!sp) = some hst) :
    run base .host (':' :: rest) ctx
      = run base .port rest
          { ctx with url := { ctx.url with host := some hst }, buffer := [] } := by
  rw [run, step]
  rw [if_neg (by simp [hov])]
  rw [if_pos (by simp [hib])]
  rw [if_neg (by simpa using hne)]
  rw [if_neg (by simp [hov])]
  simp only [hsp, hp]

/-- port state が digit を読み切る。 -/
theorem run_port_chunk (base : Option Url) (sp : Bool) : ∀ (l tail : List Char) (ctx : PCtx),
    ctx.url.isSpecial = sp → (∀ c ∈ l, isAsciiDigit c = true) →
    run base .port (l ++ tail) ctx
      = run base .port tail { ctx with buffer := ctx.buffer ++ l } := by
  intro l
  induction l with
  | nil => intro tail ctx _ _; simp
  | cons c l' ih =>
    intro tail ctx hsp h
    simp only [List.cons_append]
    rw [run, step, if_pos (h c (by simp))]
    rw [ih tail { ctx with buffer := ctx.buffer ++ [c] } hsp (fun x hx => h x (by simp [hx]))]
    simp

/-- port state の区切り。buffer を 10 進として読んで path start state へ移る。 -/
theorem run_port_pathStart (base : Option Url) (sp : Bool) (tail : List Char) (ctx : PCtx)
    (hov : ctx.over = none) (hsp : ctx.url.isSpecial = sp)
    (hne : ctx.buffer ≠ []) (hle : portValue ctx.buffer ≤ 65535)
    (ht : ∀ c ∈ tail.head?, isTerminator sp (some c) = true) :
    run base .port tail ctx
      = run base .pathStart tail
          (portSet ctx (portOf ctx.url.scheme (portValue ctx.buffer))) := by
  cases tail with
  | nil =>
    rw [run, step]
    rw [portDone_digits hne hle]
    simp only [hov, Option.isSome_none, Bool.false_eq_true, if_false]
  | cons t ts =>
    have htt := ht t rfl
    rw [run, step]
    rw [if_neg (by
      intro hd
      have ht2 : isTerminator sp (some t) = true := htt
      simp only [isTerminator, Bool.or_eq_true, beq_iff_eq] at ht2
      rcases ht2 with ((h | h) | h) | h
      · rw [h] at hd; revert hd; decide
      · rw [h] at hd; revert hd; decide
      · rw [h] at hd; revert hd; decide
      · simp only [Bool.and_eq_true, beq_iff_eq] at h
        rw [h.2] at hd; revert hd; decide)]
    rw [if_pos (by simp [hsp, htt])]
    rw [portDone_digits hne hle]
    simp only [hov, Option.isSome_none, Bool.false_eq_true, if_false]

/-! ## authority

`//` で始まる URL の経路。authority state が buffer を host state へ戻し、
host state が host parser を呼ぶ。credentials と port はまだ扱っていない。
-/

/-- path or authority state：`/` なら authority state へ。 -/
theorem run_pathOrAuthority_authority (base : Option Url) (rest : List Char) (ctx : PCtx) :
    run base .pathOrAuthority ('/' :: rest) ctx = run base .authority rest ctx := by
  rw [run, step]
  simp

set_option linter.unnecessarySimpa false in
/--
authority state が `@` も区切りも無い文字列を読み切って host state へ渡す。

buffer は host state の入力の先頭に戻る。
-/
theorem run_authority_host (base : Option Url) (sp : Bool) : ∀ (l tail : List Char) (ctx : PCtx),
    ctx.url.isSpecial = sp → (ctx.atSignSeen = true → ctx.buffer ++ l ≠ []) →
    (∀ c ∈ l, ¬c = '@' ∧ isTerminator sp (some c) = false) →
    (∀ c ∈ tail.head?, isTerminator sp (some c) = true) →
    run base .authority (l ++ tail) ctx
      = run base .host (ctx.buffer ++ l ++ tail) { ctx with buffer := [] } := by
  intro l
  induction l with
  | nil =>
    intro tail ctx hsp has _ ht
    simp only [List.nil_append, List.append_nil]
    cases tail with
    | nil =>
      rw [run, step]
      rw [if_neg (by simpa using has)]
    | cons t ts =>
      have htt := ht t rfl
      have hat : ¬t = '@' := by
        intro he; rw [he] at htt; simp [isTerminator] at htt
      rw [run, step]
      simp only [hsp]
      rw [if_neg (by simpa using hat), if_pos (by simpa using htt),
        if_neg (by simpa using has)]
  | cons c l' ih =>
    intro tail ctx hsp has h ht
    have hc := h c (by simp)
    simp only [List.cons_append]
    rw [run, step]
    simp only [hsp]
    rw [if_neg (by simpa using hc.1), if_neg (by simpa using hc.2)]
    rw [ih tail { ctx with buffer := ctx.buffer ++ [c] } hsp (by simpa using has)
      (fun x hx => h x (by simp [hx])) ht]
    simp

/-- host state が区切りでも `:` でも bracket でもない文字を読み切る。override が無い側。 -/
theorem run_host_chunk (base : Option Url) (sp : Bool) : ∀ (l tail : List Char) (ctx : PCtx),
    ctx.over = none → ctx.url.isSpecial = sp → ctx.insideBrackets = false →
    (∀ c ∈ l, ¬c = ':' ∧ isTerminator sp (some c) = false ∧ ¬c = '[' ∧ ¬c = ']') →
    run base .host (l ++ tail) ctx = run base .host tail { ctx with buffer := ctx.buffer ++ l } := by
  intro l
  induction l with
  | nil => intro tail ctx _ _ _ _; simp
  | cons c l' ih =>
    intro tail ctx hov hsp hib h
    have hc := h c (by simp)
    simp only [List.cons_append]
    rw [run, step]
    rw [if_neg (by simp [hov])]
    rw [if_neg (by simp [hc.1])]
    rw [if_neg (by simpa [hsp] using hc.2.1)]
    have hib2 : (if (c == '[') = true then true else if (c == ']') = true then false
        else ctx.insideBrackets) = false := by simp [hc.2.2.1, hc.2.2.2, hib]
    simp +zetaDelta only [hib2]
    rw [ih tail { ctx with buffer := ctx.buffer ++ [c], insideBrackets := false } hov hsp rfl
      (fun x hx => h x (by simp [hx]))]
    simp [← hib]

/-- host state の区切り。buffer を host parser に渡して path start state へ移る。 -/
theorem run_host_pathStart (base : Option Url) (sp : Bool) (tail : List Char) (ctx : PCtx)
    (hst : Host) (hov : ctx.over = none) (hsp : ctx.url.isSpecial = sp)
    (hne : sp = true → ctx.buffer ≠ [])
    (ht : ∀ c ∈ tail.head?, isTerminator sp (some c) = true ∧ ¬c = ':')
    (hp : hostParser ctx.toAscii ctx.buffer (!sp) = some hst) :
    run base .host tail ctx
      = run base .pathStart tail
          { ctx with url := { ctx.url with host := some hst }, buffer := [] } := by
  cases tail with
  | nil =>
    rw [run, step]
    rw [if_neg (by simp [hov])]
    rw [if_neg (by simp)]
    rw [if_pos (by simp [isTerminator])]
    rw [if_neg (by simp [hsp]; intro h; exact hne h)]
    rw [if_neg (by simp [hov])]
    simp only [hsp, hp]
    rw [if_neg (by simp [hov])]
  | cons t ts =>
    have htt := ht t rfl
    rw [run, step]
    rw [if_neg (by simp [hov])]
    rw [if_neg (by simp [htt.2])]
    rw [if_pos (by simpa [hsp] using htt.1)]
    rw [if_neg (by simp [hsp]; intro h; exact hne h)]
    rw [if_neg (by simp [hov])]
    simp only [hsp, hp]
    rw [if_neg (by simp [hov])]

/-- path start state：非 special で override が無いとき、`/` を一つ落として path state へ。 -/
theorem run_pathStart_slash (base : Option Url) (rest : List Char) (ctx : PCtx)
    (hsp : ctx.url.isSpecial = false) (hov : ctx.over = none) :
    run base .pathStart ('/' :: rest) ctx = run base .path rest ctx := by
  rw [run, step]
  rw [if_neg (by simp [hsp])]
  rw [if_neg (by simp [hov])]
  rw [if_neg (by simp [hov])]
  simp

/-- path start state の終わり。override が無ければ path は空のまま。 -/
theorem run_pathStart_eof (base : Option Url) (ctx : PCtx)
    (hsp : ctx.url.isSpecial = false) (hov : ctx.over = none) :
    run base .pathStart [] ctx = .ok ctx.url := by
  rw [run, step]
  rw [if_neg (by simp [hsp])]
  rw [if_neg (by simp [hov])]
  rw [if_neg (by simp [hov])]
  simp [hov]

/-- opaque host parser を通ったなら、入力に forbidden host code point は無い。 -/
theorem hostParser_opaque_no_forbidden {f : List Char → Option String} {input : List Char}
    {h : Host} (hb : ∀ c ∈ input.head?, ¬c = '[') (hp : hostParser f input true = some h) :
    input.any isForbiddenHost = false := by
  unfold hostParser at hp
  split at hp
  · exact absurd (hb '[' rfl) (by simp)
  · rw [if_pos rfl] at hp
    exact opaqueHostParser_no_forbidden hp

/-- forbidden host code point でなければ、host state も authority state も読み進む。 -/
theorem not_forbidden_host {c : Char} (h : isForbiddenHost c = false) :
    ¬c = '@' ∧ ¬c = ':' ∧ ¬c = '[' ∧ ¬c = ']' ∧ ∀ sp, isTerminator sp (some c) = false := by
  refine ⟨?_, ?_, ?_, ?_, fun sp => isTerminator_false ?_ ?_ ?_ (fun _ => ?_)⟩ <;>
    (intro he; rw [he] at h; revert h; decide)

/-- `/` を一つ落として path state へ。special かどうかに依らない。 -/
theorem run_pathStart_slash_any (base : Option Url) (sp : Bool) (rest : List Char) (ctx : PCtx)
    (hsp : ctx.url.isSpecial = sp) (hov : ctx.over = none) :
    run base .pathStart ('/' :: rest) ctx = run base .path rest ctx := by
  cases sp with
  | true => exact run_pathStart_slash_special base rest ctx (by simpa using hsp)
  | false => exact run_pathStart_slash base rest ctx (by simpa using hsp) hov

/-- path start state の `?`：special でなければ query state へ移る。 -/
theorem run_pathStart_question (base : Option Url) (rest : List Char) (ctx : PCtx)
    (hsp : ctx.url.isSpecial = false) (hov : ctx.over = none) :
    run base .pathStart ('?' :: rest) ctx
      = run base .query rest { ctx with url := { ctx.url with query := some "" } } := by
  rw [run, step]
  rw [if_neg (by simp [hsp])]
  rw [if_pos (by simp [hov])]

/-- path start state の `#`：special でなければ fragment state へ移る。 -/
theorem run_pathStart_hash (base : Option Url) (rest : List Char) (ctx : PCtx)
    (hsp : ctx.url.isSpecial = false) (hov : ctx.over = none) :
    run base .pathStart ('#' :: rest) ctx
      = run base .fragment rest { ctx with url := { ctx.url with fragment := some "" } } := by
  rw [run, step]
  rw [if_neg (by simp [hsp])]
  rw [if_neg (by simp [hov])]
  rw [if_pos (by simp [hov])]

/-- path start state から、path が空のまま query と fragment を読み切る。 -/
theorem run_pathStart_qf (base : Option Url) (q f : Option String) (ctx : PCtx)
    (hsp : ctx.url.isSpecial = false) (hov : ctx.over = none) (hb : ctx.buffer = [])
    (hq0 : ctx.url.query = none) (hf0 : ctx.url.fragment = none)
    (hqc : ∀ x, q = some x → ∀ c ∈ x.toList,
      (if ctx.url.isSpecial then specialQuerySet else querySet) c = false)
    (hfc : ∀ x, f = some x → ∀ c ∈ x.toList, fragmentSet c = false) :
    run base .pathStart (qfList q f) ctx
      = .ok { ctx.url with query := q, fragment := f } := by
  cases q with
  | none =>
    cases f with
    | none =>
      simp only [qfList, List.append_nil]
      rw [run_pathStart_eof base ctx hsp hov, url_qf_eta hq0 hf0]
    | some fs =>
      simp only [qfList, List.nil_append]
      rw [run_pathStart_hash base fs.toList ctx hsp hov]
      rw [run_fragment_full base fs _ rfl (hfc fs rfl)]
      rw [← hq0]
  | some qs =>
    simp only [qfList, List.cons_append]
    rw [run_pathStart_question base _ ctx hsp hov]
    rw [run_query_full base qs f _ _ ?g0 ?g1 ?g2 ?g3 ?g4 ?g5 ?g6]
    case g0 => rfl
    case g1 => simp [hov]
    case g2 => simp [hb]
    case g3 => rfl
    case g4 => simpa using hf0
    case g5 => exact hqc qs rfl
    case g6 => exact hfc

/-- path start state の終わり：special なら空の segment が一つ残る。 -/
theorem run_pathStart_eof_special (base : Option Url) (ctx : PCtx)
    (hsp : ctx.url.isSpecial = true) :
    run base .pathStart [] ctx = run base .path [] ctx := by
  rw [run, step]
  rw [if_pos (by simp [hsp])]
  simp

/-- userinfo set に入らない文字は `@` でも `:` でも区切りでもない。 -/
theorem not_userinfoSet {c : Char} (h : userinfoSet c = false) :
    ¬c = '@' ∧ ¬c = ':' ∧ ∀ sp, isTerminator sp (some c) = false := by
  refine ⟨?_, ?_, fun sp => isTerminator_false ?_ ?_ ?_ (fun _ => ?_)⟩ <;>
    (intro he; rw [he] at h; revert h; decide)

/-- userinfo の畳み込みは、`:` の前を username に積む。 -/
theorem userinfoFold_user : ∀ (l : List Char) (u : Url),
    (∀ c ∈ l, userinfoSet c = false) →
    l.foldl userinfoStep (u, false)
      = ({ u with username := u.username ++ String.ofList l }, false)
  | [], u, _ => by simp
  | c :: rest, u, h => by
    have hc := h c (by simp)
    have henc : encChar userinfoSet c = String.ofList [c] := by
      unfold encChar
      rw [utf8PercentEncode_id (by intro x hx; simp at hx; subst hx; exact hc)]
    show (rest.foldl userinfoStep (userinfoStep (u, false) c)) = _
    have hstep : userinfoStep (u, false) c
        = ({ u with username := u.username ++ String.ofList [c] }, false) := by
      unfold userinfoStep
      rw [if_neg (by simp [(not_userinfoSet hc).2.1])]
      simp [henc]
    rw [hstep, userinfoFold_user rest _ (fun x hx => h x (by simp [hx]))]
    simp
    rw [String.push_eq_append, String.append_assoc]

/-- `:` の後ろは password に積む。 -/
theorem userinfoFold_pass : ∀ (l : List Char) (u : Url),
    (∀ c ∈ l, userinfoSet c = false) →
    l.foldl userinfoStep (u, true)
      = ({ u with password := u.password ++ String.ofList l }, true)
  | [], u, _ => by simp
  | c :: rest, u, h => by
    have hc := h c (by simp)
    have henc : encChar userinfoSet c = String.ofList [c] := by
      unfold encChar
      rw [utf8PercentEncode_id (by intro x hx; simp at hx; subst hx; exact hc)]
    show (rest.foldl userinfoStep (userinfoStep (u, true) c)) = _
    have hstep : userinfoStep (u, true) c
        = ({ u with password := u.password ++ String.ofList [c] }, true) := by
      unfold userinfoStep
      split
      · next he => simp at he
      · simp [henc]
    rw [hstep, userinfoFold_pass rest _ (fun x hx => h x (by simp [hx]))]
    simp
    rw [String.push_eq_append, String.append_assoc]

/-- `user:pass` の形の buffer は username と password に分かれる。 -/
theorem userinfoFold_split (u : Url) (user pass : List Char)
    (hu : ∀ c ∈ user, userinfoSet c = false) (hp : ∀ c ∈ pass, userinfoSet c = false) :
    (user ++ ':' :: pass).foldl userinfoStep (u, false)
      = ({ u with
            username := u.username ++ String.ofList user
            password := u.password ++ String.ofList pass }, true) := by
  rw [List.foldl_append, userinfoFold_user user u hu]
  show pass.foldl userinfoStep (userinfoStep _ ':') = _
  have hstep : userinfoStep
      ({ u with username := u.username ++ String.ofList user }, false) ':'
      = ({ u with username := u.username ++ String.ofList user }, true) := by
    unfold userinfoStep
    rw [if_pos (by simp)]
  rw [hstep, userinfoFold_pass pass _ hp]

/-- authority state が `@` でも区切りでもない文字を buffer に積む。 -/
theorem run_authority_chunk (base : Option Url) (sp : Bool) : ∀ (l tail : List Char) (ctx : PCtx),
    ctx.url.isSpecial = sp →
    (∀ c ∈ l, ¬c = '@' ∧ isTerminator sp (some c) = false) →
    run base .authority (l ++ tail) ctx
      = run base .authority tail { ctx with buffer := ctx.buffer ++ l } := by
  intro l
  induction l with
  | nil => intro tail ctx _ _; simp
  | cons c l' ih =>
    intro tail ctx hsp h
    have hc := h c (by simp)
    simp only [List.cons_append]
    rw [run, step]
    simp only [hsp]
    rw [if_neg (by simpa using hc.1), if_neg (by simpa using hc.2)]
    rw [ih tail { ctx with buffer := ctx.buffer ++ [c] } hsp (fun x hx => h x (by simp [hx]))]
    simp

/-- authority state の `@`。buffer を credentials に振り分ける。 -/
theorem run_authority_at (base : Option Url) (rest : List Char) (ctx : PCtx)
    (has : ctx.atSignSeen = false) :
    run base .authority ('@' :: rest) ctx
      = run base .authority rest
          { ctx with
            url := (ctx.buffer.foldl userinfoStep (ctx.url, ctx.passwordTokenSeen)).1
            buffer := []
            atSignSeen := true
            passwordTokenSeen :=
              (ctx.buffer.foldl userinfoStep (ctx.url, ctx.passwordTokenSeen)).2 } := by
  rw [run, step]
  rw [if_pos (by simp)]
  simp only [has, Bool.false_eq_true, if_false]

/-- serializer が credentials を並べる分。 -/
def credChars (user pass : String) : List Char :=
  if user.isEmpty && pass.isEmpty then []
  else user.toList ++ (if pass.isEmpty then [] else ':' :: pass.toList) ++ ['@']

/-- path start state から先の path と query と fragment を読み切る。 -/
theorem run_pathStart_path (base : Option Url) (sp : Bool) (segs : List String)
    (q f : Option String) (ctx : PCtx)
    (hsp : ctx.url.isSpecial = sp) (hov : ctx.over = none)
    (hpath : ctx.url.path = .list []) (hb : ctx.buffer = []) (hnf : ¬ctx.url.scheme = "file")
    (hq0 : ctx.url.query = none) (hf0 : ctx.url.fragment = none)
    (hsegs : sp = true → segs ≠ [])
    (hall : ∀ x ∈ segs, (∀ c ∈ x.toList, pathSet c = false ∧ isTerminator sp (some c) = false) ∧
      isSingleDot x.toList = false ∧ isDoubleDot x.toList = false)
    (hqc : ∀ x, q = some x → ∀ c ∈ x.toList,
      (if ctx.url.isSpecial then specialQuerySet else querySet) c = false)
    (hfc : ∀ x, f = some x → ∀ c ∈ x.toList, fragmentSet c = false) :
    run base .pathStart (pathChars segs ++ qfList q f) ctx
      = .ok { ctx.url with path := .list segs, query := q, fragment := f } := by
  cases hseg : segs with
  | nil =>
    cases hspv : sp with
    | true => exact absurd hseg (hsegs hspv)
    | false =>
      rw [show pathChars [] = [] from rfl, List.nil_append]
      rw [run_pathStart_qf base q f ctx ?e1 hov hb hq0 hf0 hqc hfc]
      · rw [← hpath]
      case e1 => rw [hspv] at hsp; exact hsp
  | cons x t =>
    rw [show pathChars (x :: t) = '/' :: intercal (x :: t) from rfl, List.cons_append]
    rw [run_pathStart_slash_any base sp (intercal (x :: t) ++ qfList q f) _ ?s1 ?s2]
    case s1 => exact hsp
    case s2 => exact hov
    exact run_path_full base sp (x :: t) q f _ hsp hov hpath hb hnf hq0 hf0 (by simp)
      (by rw [← hseg]; exact hall) hqc hfc

/-- serializer が port を並べる分。 -/
def portChars : Option Nat → List Char
  | none => []
  | some p => ':' :: (toString p).toList

/-! ## IPv6 host

`[` と `]` で囲まれた host。中では `:` が port の区切りにならないので、
host state は bracket を数えながら読む。
-/

/-- 小文字 16 進の数字か、IPv6 の区切りの `:` である。 -/
def isHexOrColon (c : Char) : Bool :=
  (0x30 ≤ c.toNat && c.toNat ≤ 0x39) || (0x61 ≤ c.toNat && c.toNat ≤ 0x66) || c == ':'

theorem toHexString_go_chars : ∀ (fuel n : Nat) (acc : List Char), n ≤ fuel →
    (∀ c ∈ acc, isHexOrColon c = true) →
    ∀ c ∈ toHexString.go n acc, isHexOrColon c = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro n acc hle hacc
    have hn : n = 0 := Nat.le_zero.mp hle
    subst hn
    simpa [toHexString.go] using hacc
  | succ f ih =>
    intro n acc hle hacc
    cases n with
    | zero => simpa [toHexString.go] using hacc
    | succ m =>
      rw [toHexString.go]
      refine ih ((m + 1) / 16) _ (by omega) ?_
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · have hd : (m + 1) % 16 < 16 := Nat.mod_lt _ (by omega)
        simp only [isHexOrColon, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        rw [toNat_ofNat_ascii (by split <;> omega)]
        split <;> omega
      · exact hacc c hc

theorem toHexString_chars (n : Nat) :
    ∀ c ∈ (toHexString n).toList, isHexOrColon c = true := by
  unfold toHexString
  split
  · intro c hc; simp at hc; subst hc; decide
  · rw [String.toList_ofList]
    exact toHexString_go_chars n n [] (by omega) (by simp)


theorem ipv6Serializer_go_chars (cmp : Option Nat) : ∀ (l : List (Nat × Nat)) (ig : Bool),
    ∀ c ∈ (ipv6Serializer.go cmp l ig).toList, isHexOrColon c = true := by
  intro l
  induction l with
  | nil => intro ig c hc; simp [ipv6Serializer.go] at hc
  | cons p rest ih =>
    intro ig c hc
    obtain ⟨pv, i⟩ := p
    rw [ipv6Serializer.go] at hc
    split at hc
    · exact ih true c hc
    · split at hc
      · rw [String.toList_append] at hc
        rcases List.mem_append.mp hc with hc | hc
        · split at hc <;> (simp at hc; subst hc; decide)
        · exact ih true c hc
      · rw [String.toList_append, String.toList_append] at hc
        rcases List.mem_append.mp hc with hc | hc
        · rcases List.mem_append.mp hc with hc | hc
          · exact toHexString_chars pv c hc
          · split at hc
            · simp at hc
            · simp at hc; subst hc; decide
        · exact ih false c hc

/-- IPv6 を serialize した文字は 16 進の数字か `:` である。 -/
theorem ipv6Serializer_chars (a : Ipv6) :
    ∀ c ∈ (ipv6Serializer a).toList, isHexOrColon c = true :=
  ipv6Serializer_go_chars _ _ _


/-- bracket の中では `:` は port の区切りにならない。 -/
theorem run_host_inside (base : Option Url) (sp : Bool) : ∀ (l tail : List Char) (ctx : PCtx),
    ctx.over = none → ctx.url.isSpecial = sp → ctx.insideBrackets = true →
    (∀ c ∈ l, isTerminator sp (some c) = false ∧ ¬c = '[' ∧ ¬c = ']') →
    run base .host (l ++ tail) ctx = run base .host tail { ctx with buffer := ctx.buffer ++ l } := by
  intro l
  induction l with
  | nil => intro tail ctx _ _ _ _; simp
  | cons c l' ih =>
    intro tail ctx hov hsp hib h
    have hc := h c (by simp)
    simp only [List.cons_append]
    rw [run, step]
    rw [if_neg (by simp [hov])]
    rw [if_neg (by simp [hib])]
    rw [if_neg (by simpa [hsp] using hc.1)]
    have hib2 : (if (c == '[') = true then true else if (c == ']') = true then false
        else ctx.insideBrackets) = true := by simp [hc.2.1, hc.2.2, hib]
    simp +zetaDelta only [hib2]
    rw [ih tail { ctx with buffer := ctx.buffer ++ [c], insideBrackets := true } hov hsp rfl
      (fun x hx => h x (by simp [hx]))]
    simp [← hib]

/-- `[` から `]` までを buffer に積む。IPv6 host はこの形である。 -/
theorem run_host_bracket (base : Option Url) (sp : Bool) (inner tail : List Char) (ctx : PCtx)
    (hov : ctx.over = none) (hsp : ctx.url.isSpecial = sp) (hib : ctx.insideBrackets = false)
    (h : ∀ c ∈ inner, isTerminator sp (some c) = false ∧ ¬c = '[' ∧ ¬c = ']') :
    run base .host ('[' :: (inner ++ ']' :: tail)) ctx
      = run base .host tail { ctx with buffer := ctx.buffer ++ ('[' :: (inner ++ [']'])) } := by
  rw [run, step]
  rw [if_neg (by simp [hov])]
  rw [if_neg (by simp)]
  rw [if_neg (by cases sp <;> simp [hsp, isTerminator])]
  simp +zetaDelta only [show ((if ('[' == '[') = true then true
      else if ('[' == ']') = true then false else ctx.insideBrackets)) = true from by simp]
  rw [run_host_inside base sp inner (']' :: tail)
    { ctx with buffer := ctx.buffer ++ ['['], insideBrackets := true } hov hsp rfl h]
  rw [run, step]
  rw [if_neg (by simp [hov])]
  rw [if_neg (by simp)]
  rw [if_neg (by cases sp <;> simp [hsp, isTerminator])]
  simp +zetaDelta only [show ((if (']' == '[') = true then true
      else if (']' == ']') = true then false else true)) = false from by simp]
  simp [← hib]


/--
host を serialize した文字列が authority state と host state を素通りできること。

domain も opaque host も forbidden host code point を含まない。IPv6 host はそれを含むが、
`[` と `]` に囲まれていて、その中では `:` が port の区切りにならない。
-/
def hostReadable (sp : Bool) (hst : Host) : Prop :=
  (∀ c ∈ (hostSerializer hst).toList, isForbiddenHost c = false) ∨
    (∃ inner, (hostSerializer hst).toList = '[' :: (inner ++ [']']) ∧
      ∀ c ∈ inner, isTerminator sp (some c) = false ∧ ¬c = '[' ∧ ¬c = ']' ∧ ¬c = '@')

/-- host を serialize した文字は `@` でも区切りでもない。authority state を素通りする。 -/
theorem hostReadable_auth {sp : Bool} {hst : Host} (h : hostReadable sp hst) :
    ∀ c ∈ (hostSerializer hst).toList, ¬c = '@' ∧ isTerminator sp (some c) = false := by
  rcases h with h | ⟨inner, he, h⟩
  · exact fun c hc => ⟨(not_forbidden_host (h c hc)).1, (not_forbidden_host (h c hc)).2.2.2.2 sp⟩
  · intro c hc
    rw [he] at hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨by decide, by cases sp <;> decide⟩
    · rcases List.mem_append.mp hc with hc | hc
      · exact ⟨(h c hc).2.2.2, (h c hc).1⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        subst hc
        exact ⟨by decide, by cases sp <;> decide⟩

/-- host state は host を serialize した文字列をそのまま buffer に積む。 -/
theorem run_host_serialized (base : Option Url) (sp : Bool) (hst : Host) (tail : List Char)
    (ctx : PCtx) (hov : ctx.over = none) (hsp : ctx.url.isSpecial = sp)
    (hib : ctx.insideBrackets = false) (hok : hostReadable sp hst) :
    run base .host ((hostSerializer hst).toList ++ tail) ctx
      = run base .host tail
          { ctx with buffer := ctx.buffer ++ (hostSerializer hst).toList } := by
  rcases hok with h | ⟨inner, he, h⟩
  · exact run_host_chunk base sp _ tail ctx hov hsp hib
      (fun c hc => ⟨(not_forbidden_host (h c hc)).2.1,
        (not_forbidden_host (h c hc)).2.2.2.2 sp,
        (not_forbidden_host (h c hc)).2.2.1,
        (not_forbidden_host (h c hc)).2.2.2.1⟩)
  · rw [he]
    rw [show ('[' :: (inner ++ [']'])) ++ tail = '[' :: (inner ++ ']' :: tail) from by simp]
    exact run_host_bracket base sp inner tail ctx hov hsp hib
      (fun c hc => ⟨(h c hc).1, (h c hc).2.1, (h c hc).2.2.1⟩)

/-- IPv6 host を serialize した文字列は、`[` と `]` に囲まれた 16 進と `:` だけである。 -/
theorem hostReadable_ipv6 (sp : Bool) (a : Ipv6) : hostReadable sp (.ipv6 a) := by
  refine Or.inr ⟨(ipv6Serializer a).toList, ?_, ?_⟩
  · simp [hostSerializer, String.toList_append]
  · intro c hc
    have h := ipv6Serializer_chars a c hc
    refine ⟨isTerminator_false ?_ ?_ ?_ (fun _ => ?_), ?_, ?_, ?_⟩ <;>
      (intro he; rw [he] at h; revert h; decide)

/-- IPv6 host を serialize した文字に C0 control も space も無い。 -/
theorem ipv6_no_c0 (a : Ipv6) :
    ∀ c ∈ (hostSerializer (.ipv6 a)).toList, isC0ControlOrSpace c = false := by
  intro c hc
  simp only [hostSerializer, String.toList_append] at hc
  rcases List.mem_append.mp hc with hc | hc
  · rcases List.mem_append.mp hc with hc | hc
    · rw [show ("[" : String).toList = ['['] from rfl] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc; decide
    · have h := ipv6Serializer_chars a c hc
      simp only [isHexOrColon, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        beq_iff_eq] at h
      simp only [isC0ControlOrSpace, decide_eq_false_iff_not, Nat.not_le]
      rcases h with (h | h) | rfl
      · omega
      · omega
      · decide
  · rw [show ("]" : String).toList = [']'] from rfl] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc; decide

/--
authority state から先（host と port と path）を読み切る。

credentials の有無で入口の `ctx` が変わるので、そこから先をこの補題にまとめてある。
-/
theorem run_authority_hostpath (base : Option Url) (sp : Bool) (hst : Host) (port : Option Nat)
    (segs : List String) (q f : Option String) (ctx : PCtx)
    (hsp : ctx.url.isSpecial = sp) (hov : ctx.over = none) (hb : ctx.buffer = [])
    (hib : ctx.insideBrackets = false) (hpath : ctx.url.path = .list [])
    (hport0 : ctx.url.port = none) (hnf : ¬ctx.url.scheme = "file")
    (hq0 : ctx.url.query = none) (hf0 : ctx.url.fragment = none)
    (hok : hostReadable sp hst)
    (hhne : sp = true ∨ ctx.atSignSeen = true ∨ port ≠ none →
      (hostSerializer hst).toList ≠ [])
    (hcan : hostParser ctx.toAscii (hostSerializer hst).toList (!sp) = some hst)
    (hport : ∀ p, port = some p → p ≤ 65535 ∧ portOf ctx.url.scheme p = some p)
    (hsegs : sp = true → segs ≠ [])
    (hall : ∀ x ∈ segs, (∀ c ∈ x.toList, pathSet c = false ∧ isTerminator sp (some c) = false) ∧
      isSingleDot x.toList = false ∧ isDoubleDot x.toList = false)
    (hqc : ∀ x, q = some x → ∀ c ∈ x.toList,
      (if ctx.url.isSpecial then specialQuerySet else querySet) c = false)
    (hfc : ∀ x, f = some x → ∀ c ∈ x.toList, fragmentSet c = false) :
    run base .authority
        ((hostSerializer hst).toList ++ (portChars port ++ (pathChars segs ++ qfList q f))) ctx
      = .ok { ctx.url with
              host := some hst
              port := port
              path := .list segs
              query := q
              fragment := f } := by
  have htail : ∀ c ∈ (pathChars segs ++ qfList q f).head?,
      isTerminator sp (some c) = true := by
    intro c hc
    cases segs with
    | nil =>
      simp only [pathChars, List.nil_append] at hc
      unfold qfList at hc
      cases q with
      | some qs =>
        simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hc
        rw [← hc]
        cases sp <;> decide
      | none =>
        cases f with
        | some fs =>
          simp only [List.nil_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hc
          rw [← hc]
          cases sp <;> decide
        | none => simp at hc
    | cons x t =>
      simp only [pathChars, List.cons_append, List.head?_cons, Option.mem_def,
        Option.some.injEq] at hc
      rw [← hc]
      cases sp <;> decide
  have hportc : ∀ c ∈ portChars port, ¬c = '@' ∧ isTerminator sp (some c) = false := by
    intro c hc
    cases hp : port with
    | none => rw [hp] at hc; simp [portChars] at hc
    | some p =>
      rw [hp] at hc
      simp only [portChars, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact ⟨by decide, by cases sp <;> decide⟩
      · have := toString_digits p c hc
        simp only [isAsciiDigit, Bool.and_eq_true, decide_eq_true_eq] at this
        refine ⟨?_, isTerminator_false ?_ ?_ ?_ (fun _ => ?_)⟩ <;>
          (intro he; rw [he] at this; revert this; decide)
  -- authority state は区切りまで（host と port）を buffer に積んで host state へ返す
  rw [← List.append_assoc]
  rw [run_authority_host base sp ((hostSerializer hst).toList ++ portChars port)
    (pathChars segs ++ qfList q f) ctx hsp
    (fun h => by
      rw [hb, List.nil_append]
      intro he
      exact hhne (Or.inr (Or.inl h)) (List.append_eq_nil_iff.mp he).1)
    (fun c hc => by
      rcases List.mem_append.mp hc with hc | hc
      · exact hostReadable_auth hok c hc
      · exact hportc c hc) htail]
  rw [hb, List.nil_append, List.append_assoc]
  rw [run_host_serialized base sp hst (portChars port ++ (pathChars segs ++ qfList q f))
    { ctx with buffer := [] } hov hsp hib hok]
  cases hp : port with
  | none =>
    rw [show portChars none = [] from rfl, List.nil_append]
    rw [run_host_pathStart base sp (pathChars segs ++ qfList q f)
      { ctx with buffer := [] ++ (hostSerializer hst).toList } hst hov hsp
      (fun h => by simpa using hhne (Or.inl h))
      (fun c hc => ⟨htail c hc, by
        have := htail c hc
        intro he
        rw [he] at this
        cases sp <;> simp [isTerminator] at this⟩)
      (by simpa using hcan)]
    rw [run_pathStart_path base sp segs q f _ ?n1 ?n2 ?n3 rfl ?n4 ?n5 ?n6 hsegs hall ?n7 hfc]
    · rw [← hport0]
    case n1 => exact hsp
    case n2 => exact hov
    case n3 => exact hpath
    case n4 => exact hnf
    case n5 => exact hq0
    case n6 => exact hf0
    case n7 => exact hqc
  | some p =>
    obtain ⟨hle, hpo⟩ := hport p hp
    rw [show portChars (some p) = ':' :: (toString p).toList from rfl, List.cons_append]
    rw [run_host_port base sp ((toString p).toList ++ (pathChars segs ++ qfList q f))
      { ctx with buffer := [] ++ (hostSerializer hst).toList } hst hov hsp hib
      (by simpa using hhne (Or.inr (Or.inr (by rw [hp]; simp))))
      (by simpa using hcan)]
    rw [run_port_chunk base sp (toString p).toList (pathChars segs ++ qfList q f) _ ?d1 (toString_digits p)]
    case d1 => exact hsp
    rw [run_port_pathStart base sp (pathChars segs ++ qfList q f) _ ?d2 ?d3 ?d4 ?d5 htail]
    case d2 => exact hov
    case d3 => exact hsp
    case d4 => simp
    case d5 => simp only [List.nil_append, portValue_toString]; exact hle
    simp only [portSet, List.nil_append, portValue_toString, hpo]
    rw [run_pathStart_path base sp segs q f _ ?m1 ?m2 ?m3 rfl ?m4 ?m5 ?m6 hsegs hall ?m7 hfc]
    case m1 => exact hsp
    case m2 => exact hov
    case m3 => exact hpath
    case m4 => exact hnf
    case m5 => exact hq0
    case m6 => exact hf0
    case m7 => exact hqc

/--
authority state から先を、credentials も込めて読み切る。

credentials が無ければそのまま host へ、あれば `@` までを username と password に振り分ける。
-/
theorem run_authority_full (base : Option Url) (sp : Bool) (user pass : String) (hst : Host)
    (port : Option Nat) (segs : List String) (q f : Option String) (ctx : PCtx)
    (hsp : ctx.url.isSpecial = sp) (hov : ctx.over = none) (has : ctx.atSignSeen = false)
    (hb : ctx.buffer = []) (hib : ctx.insideBrackets = false) (hpt : ctx.passwordTokenSeen = false)
    (hpath : ctx.url.path = .list []) (hport0 : ctx.url.port = none)
    (hnf : ¬ctx.url.scheme = "file")
    (hq0 : ctx.url.query = none) (hf0 : ctx.url.fragment = none)
    (hu0 : ctx.url.username = "") (hp0 : ctx.url.password = "")
    (hu : ∀ c ∈ user.toList, userinfoSet c = false)
    (hp : ∀ c ∈ pass.toList, userinfoSet c = false)
    (hok : hostReadable sp hst)
    (hhne : sp = true ∨ (user.isEmpty && pass.isEmpty) = false ∨ port ≠ none →
      (hostSerializer hst).toList ≠ [])
    (hcan : hostParser ctx.toAscii (hostSerializer hst).toList (!sp) = some hst)
    (hport : ∀ p, port = some p → p ≤ 65535 ∧ portOf ctx.url.scheme p = some p)
    (hsegs : sp = true → segs ≠ [])
    (hall : ∀ x ∈ segs, (∀ c ∈ x.toList, pathSet c = false ∧ isTerminator sp (some c) = false) ∧
      isSingleDot x.toList = false ∧ isDoubleDot x.toList = false)
    (hqc : ∀ x, q = some x → ∀ c ∈ x.toList,
      (if ctx.url.isSpecial then specialQuerySet else querySet) c = false)
    (hfc : ∀ x, f = some x → ∀ c ∈ x.toList, fragmentSet c = false) :
    run base .authority
        (credChars user pass ++ ((hostSerializer hst).toList
          ++ (portChars port ++ (pathChars segs ++ qfList q f)))) ctx
      = .ok { ctx.url with
              username := user
              password := pass
              host := some hst
              port := port
              path := .list segs
              query := q
              fragment := f } := by
  unfold credChars
  cases hc : (user.isEmpty && pass.isEmpty) with
  | true =>
    have hue : user = "" := by simp_all
    have hpe : pass = "" := by simp_all
    simp only [if_true, List.nil_append]
    rw [run_authority_hostpath base sp hst port segs q f ctx hsp hov hb hib hpath hport0 hnf
      hq0 hf0 hok
      (fun h => hhne (by
        rcases h with h | h | h
        · exact Or.inl h
        · rw [has] at h
          exact absurd h (by simp)
        · exact Or.inr (Or.inr h)))
      hcan hport hsegs hall hqc hfc]
    simp [hue, hpe, hu0, hp0]
  | false =>
    -- credentials がある。`@` までを buffer に積んでから振り分ける。
    have hchunk : ∀ c ∈ user.toList ++ (if pass.isEmpty then [] else ':' :: pass.toList),
        ¬c = '@' ∧ isTerminator sp (some c) = false := by
      intro c hcm
      rcases List.mem_append.mp hcm with hcm | hcm
      · exact ⟨(not_userinfoSet (hu c hcm)).1, (not_userinfoSet (hu c hcm)).2.2 sp⟩
      · cases hpc : pass.isEmpty with
        | true => rw [hpc] at hcm; simp at hcm
        | false =>
          rw [hpc] at hcm
          simp only [Bool.false_eq_true, if_false, List.mem_cons] at hcm
          rcases hcm with rfl | hcm
          · exact ⟨by decide, by cases sp <;> decide⟩
          · exact ⟨(not_userinfoSet (hp c hcm)).1, (not_userinfoSet (hp c hcm)).2.2 sp⟩
    simp only [Bool.false_eq_true, if_false]
    rw [List.append_assoc (user.toList ++ (if pass.isEmpty then [] else ':' :: pass.toList))
      ['@'] ((hostSerializer hst).toList ++ (portChars port ++ (pathChars segs ++ qfList q f))),
      List.singleton_append]
    rw [run_authority_chunk base sp
      (user.toList ++ (if pass.isEmpty then [] else ':' :: pass.toList))
      ('@' :: ((hostSerializer hst).toList ++ (portChars port ++ (pathChars segs ++ qfList q f)))) ctx hsp hchunk]
    rw [run_authority_at base _ _ ?a1]
    case a1 => exact has
    rw [hb, List.nil_append, hpt]
    cases hpe : pass.isEmpty with
    | true =>
      have hpe' : pass = "" := by simp_all
      simp only [if_true, List.append_nil]
      rw [userinfoFold_user user.toList ctx.url hu]
      rw [run_authority_hostpath base sp hst port segs q f _ ?b1 ?b2 ?b3 ?b4 ?b5 ?b6 ?b7
        ?b11 ?b12 hok ?b8 ?b9 ?b10 hsegs hall ?b13 hfc]
      case b1 => exact hsp
      case b2 => exact hov
      case b3 => rfl
      case b4 => exact hib
      case b5 => exact hpath
      case b6 => exact hport0
      case b7 => exact hnf
      case b8 => intro _; exact hhne (Or.inr (Or.inl hc))
      case b9 => exact hcan
      case b10 => exact hport
      case b11 => exact hq0
      case b12 => exact hf0
      case b13 => exact hqc
      simp [hu0, hpe', String.ofList_toList, hp0]
    | false =>
      simp only [Bool.false_eq_true, if_false]
      rw [userinfoFold_split ctx.url user.toList pass.toList hu hp]
      rw [run_authority_hostpath base sp hst port segs q f _ ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7
        ?c11 ?c12 hok ?c8 ?c9 ?c10 hsegs hall ?c13 hfc]
      case c1 => exact hsp
      case c2 => exact hov
      case c3 => rfl
      case c4 => exact hib
      case c5 => exact hpath
      case c6 => exact hport0
      case c7 => exact hnf
      case c8 => intro _; exact hhne (Or.inr (Or.inl hc))
      case c9 => exact hcan
      case c10 => exact hport
      case c11 => exact hq0
      case c12 => exact hf0
      case c13 => exact hqc
      simp [hu0, hp0, String.ofList_toList]

/--
host を持つ URL の serialize は、`//` と credentials と host と port と path、
それに query と fragment を並べたもの。
-/
theorem serializerTail_authority (s user pass : String) (hst : Host) (port : Option Nat)
    (segs : List String) (q f : Option String) :
    (serializerTail
        { scheme := s
          username := user
          password := pass
          host := some hst
          port := port
          path := .list segs
          query := q
          fragment := f } false).toList
      = '/' :: '/' :: (credChars user pass
          ++ ((hostSerializer hst).toList
            ++ (portChars port ++ (pathChars segs ++ qfList q f)))) := by
  have hcred :
      ({ scheme := s
         username := user
         password := pass
         host := some hst
         port := port
         path := .list segs
         query := q
         fragment := f } : Url).includesCredentials
        = !(user.isEmpty && pass.isEmpty) := by
    simp [Url.includesCredentials, String.isEmpty]
  simp only [serializerTail, hcred, credChars, portChars, qfList]
  cases hc : (user.isEmpty && pass.isEmpty) <;> cases hp : pass.isEmpty <;> cases hpo : port <;>
    cases hq : q <;> cases hf : f <;>
    simp [String.toList_append, pathSerializer_pathChars]

/-- userinfo set に入らない文字は C0 control でも space でもない。 -/
theorem ne_c0_of_userinfoSet {c : Char} (h : userinfoSet c = false) :
    isC0ControlOrSpace c = false := by
  refine ne_c0_of_c0Set ?_ ?_
  · simp only [userinfoSet, pathSet, querySet, Bool.or_eq_false_iff] at h
    exact h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1
  · intro he; rw [he] at h; revert h; decide

/-- credentials の先頭の文字は `/` でも `\\` でもない。 -/
theorem credChars_head {user pass : String} {c : Char}
    (hu : ∀ x ∈ user.toList, userinfoSet x = false)
    (h : c ∈ (credChars user pass).head?) : ¬c = '/' ∧ ¬c = '\\' := by
  unfold credChars at h
  split at h
  · simp at h
  · cases hux : user.toList with
    | nil =>
      rw [hux] at h
      cases hpx : pass.isEmpty with
      | true =>
        rw [hpx] at h
        simp only [List.nil_append, if_true, List.head?_cons, Option.mem_def,
          Option.some.injEq] at h
        rw [← h]
        exact ⟨by decide, by decide⟩
      | false =>
        rw [hpx] at h
        simp only [List.nil_append, Bool.false_eq_true, if_false, List.cons_append,
          List.head?_cons, Option.mem_def, Option.some.injEq] at h
        rw [← h]
        exact ⟨by decide, by decide⟩
    | cons d t =>
      rw [hux] at h
      simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at h
      have := not_userinfoSet (hu d (by rw [hux]; simp))
      rw [← h]
      exact ⟨by
          have h2 := this.2.2 false
          intro he; rw [he] at h2; revert h2; decide,
        by
          have h2 := hu d (by rw [hux]; simp)
          intro he; rw [he] at h2; revert h2; decide⟩

/-- credentials に現れる文字は、username か password の文字か `:` か `@` である。 -/
theorem credChars_mem {user pass : String} {c : Char} (h : c ∈ credChars user pass) :
    c ∈ user.toList ∨ c ∈ pass.toList ∨ c = ':' ∨ c = '@' := by
  unfold credChars at h
  split at h
  · simp at h
  · rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · exact Or.inl h
      · split at h
        · simp at h
        · rcases List.mem_cons.mp h with rfl | h
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inl h)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      exact Or.inr (Or.inr (Or.inr h))

/-- scheme state の `:` から authority state まで。special かどうかで経路が違うが行き先は同じ。 -/
theorem run_scheme_authority (sp : Bool) (rest : List Char) (ctx : PCtx)
    (hov : ctx.over = none) (hf : ¬(String.ofList ctx.buffer = "file"))
    (hsp : isSpecialScheme (String.ofList ctx.buffer) = sp)
    (hhead : sp = true → ∀ c ∈ rest.head?, ¬c = '/' ∧ ¬c = '\\') :
    run none .scheme (':' :: '/' :: '/' :: rest) ctx
      = run none .authority rest
          { ctx with
            url := { ctx.url with scheme := String.ofList ctx.buffer }
            buffer := [] } := by
  cases sp with
  | false =>
    rw [run_scheme_pathOrAuthority none ('/' :: rest) ctx hov hf (by simpa using hsp)]
    rw [run_pathOrAuthority_authority]
  | true =>
    rw [run_scheme_specialAuthoritySlashes ('/' :: '/' :: rest) ctx hov hf (by simpa using hsp)]
    rw [run_specialAuthoritySlashes]
    rw [run_specialAuthorityIgnoreSlashes none rest _ (hhead rfl)]

/--
**host を持つ URL は、serialize して parse し直すと元に戻る。**

special かどうかを `sp` で持つので、`sc://h/a` も `http://h/a/b` もこれ一つで済む。
credentials も扱う。除いてあるのは `file:`、port、IPv6 host、
それと host が空で path が空でない場合（serialize すると `//` が続いてしまう）である。
-/
theorem roundtrip_host {s user pass : String} {sp : Bool} {hst : Host} {port : Option Nat}
    {segs : List String} {q f : Option String} {a : Char} {rest : List Char}
    (hs : s.toList = a :: rest) (ha : isAsciiLowerAlpha a = true)
    (hr : ∀ c ∈ rest, schemeChar c = true)
    (hlow : s.toList.map asciiLowerChar = s.toList)
    (hsp : isSpecialScheme s = sp) (hfile : ¬s = "file")
    (hu : ∀ c ∈ user.toList, userinfoSet c = false)
    (hp : ∀ c ∈ pass.toList, userinfoSet c = false)
    (hcan : hostParser asciiDomainToASCII (hostSerializer hst).toList (!sp) = some hst)
    (hok : hostReadable sp hst)
    (hnc : ∀ c ∈ (hostSerializer hst).toList, isC0ControlOrSpace c = false)
    (hhead : sp = true →
      ∀ c ∈ ((hostSerializer hst).toList ++ (portChars port ++ (pathChars segs ++ qfList q f))).head?,
      ¬c = '/' ∧ ¬c = '\\')
    (hhne : sp = true ∨ (user.isEmpty && pass.isEmpty) = false ∨ port ≠ none →
      (hostSerializer hst).toList ≠ [])
    (hport : ∀ p, port = some p → p ≤ 65535 ∧ portOf s p = some p)
    (hqc : ∀ x, q = some x → ∀ c ∈ x.toList,
      (if isSpecialScheme s then specialQuerySet else querySet) c = false)
    (hfc : ∀ x, f = some x → ∀ c ∈ x.toList, fragmentSet c = false)
    (hsegs : sp = true → segs ≠ [])
    (hall : ∀ x ∈ segs, (∀ c ∈ x.toList, pathSet c = false ∧ isTerminator sp (some c) = false) ∧
      isSingleDot x.toList = false ∧ isDoubleDot x.toList = false) :
    basicUrlParse (urlSerializer
        { scheme := s
          username := user
          password := pass
          host := some hst
          port := port
          path := .list segs
          query := q
          fragment := f }) none
      = some
        { scheme := s
          username := user
          password := pass
          host := some hst
          port := port
          path := .list segs
          query := q
          fragment := f } := by
  have haa : isAsciiAlpha a = true := by
    simp only [isAsciiAlpha, Bool.or_eq_true]; exact Or.inr ha
  have hbuf : ([] : List Char) ++ [asciiLowerChar a] ++ rest.map asciiLowerChar = s.toList := by
    rw [List.nil_append, List.singleton_append, ← List.map_cons, ← hs, hlow]
  have hstr : (urlSerializer
      { scheme := s
        username := user
        password := pass
        host := some hst
        port := port
        path := .list segs
        query := q
        fragment := f }).toList
      = s.toList ++ ':' :: '/' :: '/'
        :: (credChars user pass
          ++ ((hostSerializer hst).toList ++ (portChars port ++ (pathChars segs ++ qfList q f)))) := by
    simp only [urlSerializer, String.toList_append, serializerTail_authority]
    simp
  have hallc : ∀ c ∈ s.toList ++ ':' :: '/' :: '/'
      :: (credChars user pass
        ++ ((hostSerializer hst).toList ++ (portChars port ++ (pathChars segs ++ qfList q f)))),
      isC0ControlOrSpace c = false := by
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
        · rcases List.mem_cons.mp hcm with rfl | hcm
          · decide
          · rcases List.mem_append.mp hcm with hcm | hcm
            · rcases credChars_mem hcm with h | h | rfl | rfl
              · exact ne_c0_of_userinfoSet (hu c h)
              · exact ne_c0_of_userinfoSet (hp c h)
              · decide
              · decide
            · rcases List.mem_append.mp hcm with hcm | hcm
              · exact hnc c hcm
              · rcases List.mem_append.mp hcm with hcm | hcm
                · cases hpo : port with
                  | none => rw [hpo] at hcm; simp [portChars] at hcm
                  | some p =>
                    rw [hpo] at hcm
                    simp only [portChars, List.mem_cons] at hcm
                    rcases hcm with rfl | hcm
                    · decide
                    · have := toString_digits p c hcm
                      simp only [isAsciiDigit, Bool.and_eq_true, decide_eq_true_eq] at this
                      simp only [isC0ControlOrSpace, decide_eq_false_iff_not, Nat.not_le]
                      omega
                · rcases List.mem_append.mp hcm with hcm | hcm
                  · cases segs with
                    | nil => simp [pathChars] at hcm
                    | cons x t =>
                      rcases List.mem_cons.mp hcm with rfl | hcm
                      · decide
                      · rcases intercal_mem (x :: t) c hcm with rfl | ⟨y, hy, hcy⟩
                        · decide
                        · exact ne_c0_of_c0Set (c0Set_of_pathSet ((hall y hy).1 c hcy).1)
                            (ne_space_of_pathSet ((hall y hy).1 c hcy).1)
                  · exact qfList_c0 (fun x hx c hc => querySet_of_ite (hqc x hx c hc)) hfc c hcm
  have hpre : preprocess (urlSerializer
      { scheme := s
        username := user
        password := pass
        host := some hst
        port := port
        path := .list segs
        query := q
        fragment := f })
      = s.toList ++ ':' :: '/' :: '/'
        :: (credChars user pass
          ++ ((hostSerializer hst).toList ++ (portChars port ++ (pathChars segs ++ qfList q f)))) := by
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
  have hhead2 : sp = true → ∀ c ∈ (credChars user pass
      ++ ((hostSerializer hst).toList ++ (portChars port ++ (pathChars segs ++ qfList q f)))).head?,
      ¬c = '/' ∧ ¬c = '\\' := by
    intro hspv c hc
    cases hcc : credChars user pass with
    | nil =>
      rw [hcc, List.nil_append] at hc
      exact hhead hspv c hc
    | cons d t =>
      rw [hcc] at hc
      simp only [List.cons_append, List.head?_cons] at hc
      exact credChars_head hu (by rw [hcc]; simpa using hc)
  unfold basicUrlParse
  rw [hpre, hs, List.cons_append]
  rw [run_schemeStart_step none _ a
    (rest ++ ':' :: '/' :: '/'
      :: (credChars user pass
        ++ ((hostSerializer hst).toList ++ (portChars port ++ (pathChars segs ++ qfList q f))))) haa]
  rw [run_scheme_prefix none rest
    (':' :: '/' :: '/'
      :: (credChars user pass
        ++ ((hostSerializer hst).toList ++ (portChars port ++ (pathChars segs ++ qfList q f))))) _ hr]
  rw [run_scheme_authority sp
    (credChars user pass
      ++ ((hostSerializer hst).toList ++ (portChars port ++ (pathChars segs ++ qfList q f)))) _ rfl
    (by rw [hbuf, String.ofList_toList]; exact hfile)
    (by rw [hbuf, String.ofList_toList]; exact hsp) hhead2]
  rw [hbuf, String.ofList_toList]
  rw [run_authority_full none sp user pass hst port segs q f _ ?j1 rfl rfl rfl rfl rfl rfl rfl ?j2
    rfl rfl rfl rfl hu hp hok ?j3 ?j4 ?j5 hsegs hall ?j6 hfc]
  case j1 => simp [Url.isSpecial, hsp]
  case j2 => simpa using hfile
  case j3 => exact hhne
  case j4 => simpa using hcan
  case j5 => exact hport
  case j6 => exact hqc

/-- 仮定が空でないことの確認。`sc://h/a` は実際にこの形である。 -/
example : basicUrlParse
      (urlSerializer { scheme := "sc", host := some (.opaque "h"), path := .list ["a"] }) none
    = some { scheme := "sc", host := some (.opaque "h"), path := .list ["a"] } :=
  roundtrip_host (a := 's') (rest := ['c']) (user := "") (pass := "") (sp := false)
    (port := none) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (Or.inl (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by simp) (by simp) (by decide) (by decide)

/-- host が空でも往復する。`sc:///a` の形である。 -/
example : basicUrlParse
      (urlSerializer { scheme := "sc", host := some .empty, path := .list ["a"] }) none
    = some { scheme := "sc", host := some .empty, path := .list ["a"] } :=
  roundtrip_host (a := 's') (rest := ['c']) (user := "") (pass := "") (sp := false)
    (port := none) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (Or.inl (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by simp) (by simp) (by decide) (by decide)

/-- port が付いていても往復する。`sc://h:8080/a` の形である。 -/
example : basicUrlParse (urlSerializer
      { scheme := "sc", host := some (.opaque "h"), port := some 8080,
        path := .list ["a"] }) none
    = some { scheme := "sc", host := some (.opaque "h"), port := some 8080,
             path := .list ["a"] } :=
  roundtrip_host (a := 's') (rest := ['c']) (user := "") (pass := "") (sp := false)
    (port := some 8080) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (Or.inl (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by simp) (by simp) (by decide) (by decide)

/-- query と fragment が付いていても往復する。`sc://h/a?q#f` の形である。 -/
example : basicUrlParse (urlSerializer
      { scheme := "sc", host := some (.opaque "h"), path := .list ["a"],
        query := some "q", fragment := some "f" }) none
    = some { scheme := "sc", host := some (.opaque "h"), path := .list ["a"],
             query := some "q", fragment := some "f" } :=
  roundtrip_host (a := 's') (rest := ['c']) (user := "") (pass := "") (sp := false)
    (port := none) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (Or.inl (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by simp; decide) (by simp; decide) (by decide) (by decide)

/-- IPv6 host も往復する。`sc://[::]/a` の形である。 -/
example : basicUrlParse (urlSerializer
      { scheme := "sc", host := some (.ipv6 [0, 0, 0, 0, 0, 0, 0, 0]),
        path := .list ["a"] }) none
    = some { scheme := "sc", host := some (.ipv6 [0, 0, 0, 0, 0, 0, 0, 0]),
             path := .list ["a"] } :=
  roundtrip_host (a := 's') (rest := ['c']) (user := "") (pass := "") (sp := false)
    (port := none) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (hostReadable_ipv6 _ _) (ipv6_no_c0 _)
    (by decide) (by decide)
    (by decide) (by simp) (by simp) (by decide) (by decide)

/-- special な URL の IPv6 host も往復する。`http://[::]/a` の形である。 -/
example : basicUrlParse (urlSerializer
      { scheme := "http", host := some (.ipv6 [0, 0, 0, 0, 0, 0, 0, 0]),
        path := .list ["a"] }) none
    = some { scheme := "http", host := some (.ipv6 [0, 0, 0, 0, 0, 0, 0, 0]),
             path := .list ["a"] } :=
  roundtrip_host (a := 'h') (rest := ['t', 't', 'p']) (user := "") (pass := "") (sp := true)
    (port := none) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (hostReadable_ipv6 _ _) (ipv6_no_c0 _)
    (by decide) (by decide)
    (by decide) (by simp) (by simp) (by decide) (by decide)

/-!
`http://h/a` がこの形であることは `decide` では確かめられない。
host parser が domain parser を通り、そこが UTF-8 の encode / decode（well-founded 再帰）を
呼ぶので、`Decidable` 実体が簡約しないためである（`#audit_axioms` の制約でもある）。
`#eval` では `hostParser asciiDomainToASCII "h".toList false = some (.domain "h")` になり、
`UrlMain.lean` の ROUNDTRIP と CANONICAL が WPT の 820 件で同じことを見ている。

IPv6 host は host parser が `[` の分岐へ行き domain parser を通らないので、
`http://[::]/a` の方は `decide` で確かめられる。ただし `toHexString` は well-founded 再帰で
簡約しないので、0 以外の piece を持つ address（`[::1]` など）は例に書けない。
-/

end Url
