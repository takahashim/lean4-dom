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

いちばん短い経路（scheme start → scheme → opaque path）だけである。
`roundtrip_opaque` が、scheme と opaque path について `canonicalUrl` に当たる条件を仮定して
`parse ∘ serialize = id` を言う。経路ごとに state の等式を積む形で、
`Url/ApiValid.lean` の setter の肯定側と同じやり方である。

残りは query / fragment が付く場合と、authority / host / port / path を通る経路で、
こちらは state も条件も多い。
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

/--
opaque path state は、素通しの文字をそのまま path の末尾に足す。

`?` と `#` は出口なので入力に無いこととした。space はそのまま積まれる
（次が `?` か `#` なら `%20` になるが、その二つは無い）。
-/
theorem run_opaquePath_plain (base : Option Url) : ∀ (l : List Char) (ctx : PCtx) (p : String),
    ctx.url.path = .opaque p →
    (∀ c ∈ l, c0ControlSet c = false ∧ ¬c = '?' ∧ ¬c = '#') →
    run base .opaquePath l ctx = .ok { ctx.url with path := .opaque (p ++ String.ofList l) } := by
  intro l
  induction l with
  | nil =>
    intro ctx p hp _
    rw [run, step]
    simp [← hp]
  | cons c tail ih =>
    intro ctx p hp hd
    have hc := hd c (by simp)
    have henc : encChar c0ControlSet c = String.ofList [c] := by
      unfold encChar
      rw [utf8PercentEncode_id (by intro x hx; simp at hx; subst hx; exact hc.1)]
    have hstep : run base .opaquePath (c :: tail) ctx
        = run base .opaquePath tail
            { ctx with url := appendOpaque ctx.url (encChar c0ControlSet c) } := by
      by_cases hsp : c = ' '
      · -- space。次が `?` でも `#` でもないので、そのまま積む。
        subst hsp
        rw [run, step]
        cases tail with
        | nil => simp [henc]
        | cons d t =>
          have h1 : ¬d = '?' := (hd d (by simp)).2.1
          have h2 : ¬d = '#' := (hd d (by simp)).2.2
          simp only [List.head?_cons]
          split
          · next hq => exact absurd (Option.some.inj hq) h1
          · next hq => exact absurd (Option.some.inj hq) h2
          · simp [henc]
      · rw [run, step]
        all_goals first
          | rfl
          | (intro he; exact absurd he hc.2.1)
          | (intro he; exact absurd he hc.2.2)
          | (intro he; exact absurd he hsp)
    rw [hstep]
    rw [ih { ctx with url := appendOpaque ctx.url (encChar c0ControlSet c) }
      (p ++ encChar c0ControlSet c) (by simp [appendOpaque, hp])
      (fun x hx => hd x (by simp [hx]))]
    simp only [appendOpaque, hp, henc]
    simp
    rw [String.push_eq_append, String.append_assoc]

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

/--
**opaque path を持つ URL は、serialize して parse し直すと元に戻る。**

`parse ∘ serialize = id` のうち、いちばん短い経路（scheme start → scheme → opaque path）を
閉じたものである。仮定はその経路を通る形であること、つまり
`canonicalUrl` のうち scheme と opaque path に当たる分である。
query と fragment が付く場合はその二つの state の補題が要る。
-/
theorem roundtrip_opaque {s o : String} {a : Char} {rest : List Char}
    (hs : s.toList = a :: rest) (ha : isAsciiLowerAlpha a = true)
    (hr : ∀ c ∈ rest, schemeChar c = true)
    (hlow : s.toList.map asciiLowerChar = s.toList)
    (hsp : isSpecialScheme s = false)
    (ho : ∀ c ∈ o.toList, c0ControlSet c = false ∧ ¬c = '?' ∧ ¬c = '#')
    (hlast : ∀ c ∈ o.toList.reverse.head?, isC0ControlOrSpace c = false)
    (hhead : ∀ c ∈ o.toList.head?, ¬c = '/') :
    basicUrlParse (urlSerializer { scheme := s, path := .opaque o }) none
      = some { scheme := s, path := .opaque o } := by
  have haa : isAsciiAlpha a = true := by
    simp only [isAsciiAlpha, Bool.or_eq_true]; exact Or.inr ha
  have hstr : (urlSerializer { scheme := s, path := .opaque o }).toList
      = s.toList ++ ':' :: o.toList := by
    simp [urlSerializer, serializerTail, pathSerializer]
  have hbuf : ([] : List Char) ++ [asciiLowerChar a] ++ rest.map asciiLowerChar = s.toList := by
    rw [List.nil_append, List.singleton_append, ← List.map_cons, ← hs, hlow]
  have hfile : ¬s = "file" := by
    intro he; rw [he] at hsp; exact absurd hsp (by decide)
  have hpre : preprocess (urlSerializer { scheme := s, path := .opaque o })
      = s.toList ++ ':' :: o.toList := by
    rw [preprocess_eq_self (str := urlSerializer { scheme := s, path := .opaque o }) ?head ?last
      ?tab, hstr]
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
      rw [hstr, reverse_head_mid] at hcm
      cases hx : o.toList.isEmpty with
      | true => rw [hx] at hcm; simp only [if_true, Option.mem_def, Option.some.injEq] at hcm
                subst hcm; decide
      | false => rw [hx] at hcm; exact hlast c hcm
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
        · have := (ho c hcm).1
          simp only [c0ControlSet, isC0Control, Bool.or_eq_false_iff, decide_eq_false_iff_not,
            Nat.not_le, Nat.not_lt] at this
          omega
  unfold basicUrlParse
  rw [hpre, hs, List.cons_append]
  rw [run_schemeStart_step none _ a (rest ++ ':' :: o.toList) haa]
  rw [run_scheme_prefix none rest (':' :: o.toList) _ hr]
  rw [run_scheme_opaque none o.toList _ rfl
    (by rw [hbuf, String.ofList_toList]; exact hfile)
    (by rw [hbuf, String.ofList_toList]; exact hsp)
    (by intro r hrr; exact hhead r hrr)]
  rw [run_opaquePath_plain none o.toList _ "" rfl ho]
  rw [hbuf, String.ofList_toList]
  simp

/-- 仮定が空でないことの確認。`sc:x` は実際にこの形である。 -/
example : basicUrlParse (urlSerializer { scheme := "sc", path := .opaque "x" }) none
    = some { scheme := "sc", path := .opaque "x" } :=
  roundtrip_opaque (a := 's') (rest := ['c']) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

end Url
