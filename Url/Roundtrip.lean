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
少なくとも次が必要で、どれも §4.1 には無い。

* scheme は小文字で、先頭が ASCII alpha、残りが alphanumeric か `+` `-` `.`
* port は既定 port でない
* credentials / query / fragment / path segment / opaque path は、それぞれの set で
  percent-encode 済み（`utf8PercentEncode set x = x`）
* path segment は `.` でも `..` でもない
* host は `hostParser (hostSerializer h) = some h` を満たす
* serialize した文字列の先頭と末尾が C0 control or space でない

## この file が閉じた分

いちばん短い経路（scheme start → scheme → opaque path）だけである。
`roundtrip_opaque` が、scheme が小文字の ASCII で opaque path が素通しの文字だけの場合に
`parse ∘ serialize = id` を言う。経路ごとに state の等式を積む形で、
`Url/ApiValid.lean` の setter の肯定側と同じやり方である。

残りは authority / host / port / path を通る経路で、こちらは state も条件も多い。
実行時の検査（`UrlMain.lean` の ROUNDTRIP）が WPT の 820 件で裏を取っている。
-/

namespace Url

open Infra

set_option maxHeartbeats 1000000

/-- 先頭から落とす文字が無ければ `dropWhile` は何もしない。 -/
theorem dropWhile_self : ∀ (l : List Char) (p : Char → Bool), (∀ c ∈ l, p c = false) →
    List.dropWhile p l = l
  | [], _, _ => rfl
  | c :: rest, p, h => by
    rw [List.dropWhile_cons, if_neg (by rw [h c (by simp)]; simp)]

/-- C0 control でも space でもない文字だけなら、前処理は何もしない。 -/
theorem preprocess_eq_self {str : String} (h : ∀ c ∈ str.toList, isC0ControlOrSpace c = false) :
    preprocess str = str.toList := by
  unfold preprocess
  simp only [dropWhile_self str.toList isC0ControlOrSpace h]
  rw [dropWhile_self str.toList.reverse isC0ControlOrSpace (fun c hc => h c (by simpa using hc)),
    List.reverse_reverse]
  refine stripTabNewline_eq_self fun c hc => ?_
  have := h c hc
  simp only [isC0ControlOrSpace, decide_eq_false_iff_not, Nat.not_le] at this
  omega

/-- scheme state は alphanumeric を小文字にして buffer に積む。 -/
theorem run_scheme_prefix (base : Option Url) : ∀ (pre rest : List Char) (ctx : PCtx),
    (∀ c ∈ pre, isAsciiAlphanumeric c = true) →
    run base .scheme (pre ++ rest) ctx
      = run base .scheme rest { ctx with buffer := ctx.buffer ++ pre.map asciiLowerChar } := by
  intro pre
  induction pre with
  | nil => intro rest ctx _; simp
  | cons c tail ih =>
    intro rest ctx hd
    simp only [List.cons_append]
    rw [run, step, if_pos (by simp [hd c (by simp)])]
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

/-- opaque path state は、素通しの文字をそのまま path の末尾に足す。 -/
theorem run_opaquePath_plain (base : Option Url) : ∀ (l : List Char) (ctx : PCtx) (p : String),
    ctx.url.path = .opaque p → (∀ c ∈ l, isAsciiAlphanumeric c = true) →
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
    have hnot : c0ControlSet c = false := by
      simp only [isAsciiAlphanumeric, isAsciiDigit, isAsciiAlpha, isAsciiUpperAlpha,
        isAsciiLowerAlpha, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hc
      simp only [c0ControlSet, isC0Control, Bool.or_eq_false_iff, decide_eq_false_iff_not,
        Nat.not_le, decide_eq_false_iff_not, Nat.not_lt]
      omega
    have henc : encChar c0ControlSet c = String.ofList [c] := by
      unfold encChar
      rw [utf8PercentEncode_id (by intro x hx; simp at hx; subst hx; exact hnot)]
    rw [run, step]
    simp +zetaDelta only []
    rw [ih { ctx with url := appendOpaque ctx.url (encChar c0ControlSet c) }
      (p ++ encChar c0ControlSet c) (by simp [appendOpaque, hp])
      (fun x hx => hd x (by simp [hx]))]
    simp only [appendOpaque, hp, henc]
    all_goals first
      | (intro he; rw [he] at hc; revert hc; decide)
      | (simp; rw [String.push_eq_append, String.append_assoc])

/--
**opaque path を持つ URL は、serialize して parse し直すと元に戻る。**

`parse ∘ serialize = id` のうち、いちばん短い経路（scheme start → scheme → opaque path）だけを
閉じたものである。仮定は「その経路を通る形であること」で、
scheme は小文字の ASCII、opaque path は素通しされる文字だけ、とした。
-/
theorem roundtrip_opaque {s o : String} {a : Char} {rest : List Char}
    (hs : s.toList = a :: rest) (ha : isAsciiAlpha a = true)
    (hr : ∀ c ∈ rest, isAsciiAlphanumeric c = true)
    (hlow : s.toList.map asciiLowerChar = s.toList)
    (hsp : isSpecialScheme s = false)
    (ho : ∀ c ∈ o.toList, isAsciiAlphanumeric c = true) :
    basicUrlParse (urlSerializer { scheme := s, path := .opaque o }) none
      = some { scheme := s, path := .opaque o } := by
  have hstr : (urlSerializer { scheme := s, path := .opaque o }).toList
      = s.toList ++ ':' :: o.toList := by
    simp [urlSerializer, serializerTail, pathSerializer]
  have hnc : ∀ c ∈ (urlSerializer { scheme := s, path := .opaque o }).toList,
      isC0ControlOrSpace c = false := by
    intro c hc
    rw [hstr] at hc
    have halnum : isAsciiAlphanumeric c = true ∨ c = ':' := by
      rcases List.mem_append.mp hc with hc | hc
      · rw [hs] at hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact Or.inl (by simp [isAsciiAlphanumeric, ha])
        · exact Or.inl (hr c hc)
      · rcases List.mem_cons.mp hc with rfl | hc
        · exact Or.inr rfl
        · exact Or.inl (ho c hc)
    rcases halnum with h | rfl
    · simp only [isAsciiAlphanumeric, isAsciiDigit, isAsciiAlpha, isAsciiUpperAlpha,
        isAsciiLowerAlpha, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [isC0ControlOrSpace, decide_eq_false_iff_not, Nat.not_le]
      omega
    · decide
  have hpre : preprocess (urlSerializer { scheme := s, path := .opaque o })
      = s.toList ++ ':' :: o.toList := by
    rw [preprocess_eq_self hnc, hstr]
  have hbuf : ([] : List Char) ++ [asciiLowerChar a] ++ rest.map asciiLowerChar = s.toList := by
    rw [List.nil_append, List.singleton_append, ← List.map_cons, ← hs, hlow]
  have hfile : ¬s = "file" := by
    intro he; rw [he] at hsp; exact absurd hsp (by decide)
  unfold basicUrlParse
  rw [hpre, hs, List.cons_append]
  rw [run_schemeStart_step none _ a (rest ++ ':' :: o.toList) ha]
  rw [run_scheme_prefix none rest (':' :: o.toList) _ hr]
  rw [run_scheme_opaque none o.toList _ rfl
    (by rw [hbuf, String.ofList_toList]; exact hfile)
    (by rw [hbuf, String.ofList_toList]; exact hsp)
    (by intro r hrr
        have := ho r (List.mem_of_mem_head? hrr)
        intro he; rw [he] at this; revert this; decide)]
  rw [run_opaquePath_plain none o.toList _ "" rfl ho]
  rw [hbuf, String.ofList_toList]
  simp

/-- 仮定が空でないことの確認。`sc:x` は実際にこの形である。 -/
example : basicUrlParse (urlSerializer { scheme := "sc", path := .opaque "x" }) none
    = some { scheme := "sc", path := .opaque "x" } :=
  roundtrip_opaque (a := 's') (rest := ['c']) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

end Url
