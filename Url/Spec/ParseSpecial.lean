import Url.Spec.ParseEquiv

/-!
# basic URL parser と関数的な仕様の一致（§4.4、base 無し・special な scheme、`file` を除く）

`Url/Spec/ParseEquiv.lean` の続き。special な scheme は scheme state から
special authority slashes state と special authority ignore slashes state を通って authority state に入る。
二つの state は先頭の `/` と `\` をいくつでも読み飛ばすだけである（`run_specialAuthoritySlashes_drop`）。

authority から先は special でない URL と同じ形の補題を、区切りに `\` を加え、空の host を失敗にして積む。
-/

namespace Url.Spec

open Infra Url

/-! ## slash を読み飛ばす二つの state -/

/-- **special authority ignore slashes state は、先頭の `/` と `\` をすべて読み飛ばして authority state へ渡す。** -/
theorem run_ignoreSlashes (base : Option Url) : ∀ (l : List Char) (ctx : PCtx),
    run base .specialAuthorityIgnoreSlashes l ctx = run base .authority (l.dropWhile isSlashBS) ctx
  | [], ctx => by rw [run, step]; rfl
  | c :: t, ctx => by
    rw [run, step]
    by_cases hc : isSlashBS c = true
    · have : (c == '/' || c == '\\') = true := hc
      rw [if_pos this, run_ignoreSlashes base t ctx]
      simp [hc]
    · have : (c == '/' || c == '\\') = false := by simpa [isSlashBS] using hc
      rw [if_neg (by simp [this])]
      simp [show isSlashBS c = false by simpa using hc]

/-- **special authority slashes state も同じである。** `//` を読むか読まないかは、読み飛ばした後に違いを残さない。 -/
theorem run_specialAuthoritySlashes_drop (base : Option Url) (l : List Char) (ctx : PCtx) :
    run base .specialAuthoritySlashes l ctx = run base .authority (l.dropWhile isSlashBS) ctx := by
  by_cases h2 : ∃ r2, l = '/' :: '/' :: r2
  · obtain ⟨r2, rfl⟩ := h2
    rw [run, step, run_ignoreSlashes]
    simp [isSlashBS]
  · cases l with
    | nil =>
      rw [run, step]
      · exact run_ignoreSlashes base [] ctx
      · intro _ _ h; cases h
    | cons c t =>
      rw [run, step]
      · exact run_ignoreSlashes base (c :: t) ctx
      · intro r2 hc ht
        simp only [Option.some.injEq] at hc
        exact h2 ⟨r2, by rw [hc, ht]⟩

/-! ## 述語で選ぶ区切り -/

theorem splitFirstBy_append (p : Char → Bool) : ∀ (a r : List Char) (d : Char),
    (∀ c ∈ a, p c = false) → p d = true → splitFirstBy p (a ++ d :: r) = (a, some r)
  | [], r, d, _, hd => by simp [splitFirstBy, hd]
  | x :: a, r, d, h, hd => by
    have hx : p x = false := h x (by simp)
    simp [splitFirstBy, hx, splitFirstBy_append p a r d (fun c hc => h c (by simp [hc])) hd]

theorem splitFirstBy_none (p : Char → Bool) : ∀ (l : List Char), (∀ c ∈ l, p c = false) →
    splitFirstBy p l = (l, none)
  | [], _ => rfl
  | x :: l, h => by
    have hx : p x = false := h x (by simp)
    simp [splitFirstBy, hx, splitFirstBy_none p l (fun c hc => h c (by simp [hc]))]

theorem first_occurrence_by (p : Char → Bool) : ∀ (l : List Char),
    (∀ c ∈ l, p c = false) ∨ ∃ a d r, l = a ++ d :: r ∧ p d = true ∧ ∀ c ∈ a, p c = false
  | [] => .inl (by simp)
  | x :: l => by
    by_cases hx : p x = true
    · exact .inr ⟨[], x, l, rfl, hx, by simp⟩
    · have hx' : p x = false := by simpa using hx
      rcases first_occurrence_by p l with h | ⟨a, d, r, rfl, hd, ha⟩
      · exact .inl (fun c hc => by rcases List.mem_cons.mp hc with rfl | hc; exact hx'; exact h c hc)
      · exact .inr ⟨x :: a, d, r, rfl, hd,
          fun c hc => by rcases List.mem_cons.mp hc with rfl | hc; exact hx'; exact ha c hc⟩

/-- special な URL の terminator は、区切り（`/` と `\`）と `?` と `#` である。 -/
theorem isTerminator_sp (c : Char) :
    isTerminator true (some c) = (isSlashBS c || c == '?' || c == '#') := by
  simp only [isTerminator, isSlashBS, Bool.true_and]
  cases c == '/' <;> cases c == '?' <;> cases c == '#' <;> cases c == '\\' <;> rfl

/-! ## path start state（special な URL） -/

theorem run_pathStart_sep_sp (base : Option Url) {c : Char} (r : List Char) (ctx : PCtx)
    (hsp : ctx.url.isSpecial = true) (hc : isSlashBS c = true) :
    run base .pathStart (c :: r) ctx = run base .path r ctx := by
  rw [run, step]
  have : (some c == some '/' || some c == some '\\') = true := by
    simp only [isSlashBS, Bool.or_eq_true, beq_iff_eq] at hc
    rcases hc with rfl | rfl <;> simp
  simp only [hsp, if_true]
  rw [if_pos this]

theorem run_pathStart_other_sp (base : Option Url) (T : List Char) (ctx : PCtx)
    (hsp : ctx.url.isSpecial = true) (hT : ∀ c r, T = c :: r → isSlashBS c = false) :
    run base .pathStart T ctx = run base .path T ctx := by
  cases T with
  | nil => rw [run, step]; simp [hsp]
  | cons c r =>
    have hc := hT c r rfl
    have : (some c == some '/' || some c == some '\\') = false := by
      simp only [isSlashBS, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hc
      simp [hc.1, hc.2]
    rw [run, step]
    simp only [hsp, if_true, this, Bool.false_eq_true, if_false]

/-- path start state から先の続き（special な URL）。 -/
def PathStartContSp (base : Option Url) (T1 : List Char) (P : List String)
    (Q F : Option String) : Prop :=
  ∀ ctx' : PCtx, ctx'.over = none → ctx'.buffer = [] → ctx'.url.query = none →
    ctx'.url.fragment = none → ctx'.url.path = .list [] → ctx'.url.isSpecial = true →
    ctx'.url.scheme ≠ "file" →
    run base .pathStart T1 ctx' = .ok { ctx'.url with path := .list P, query := Q, fragment := F }

/-- path が無い authority の続き（`http://h`、`http://h?q`）。path は空の segment が一つになる。 -/
theorem pathStartContSp_none (base : Option Url) (q f : Option (List Char))
    (hqh : ∀ x, q = some x → '#' ∉ x) :
    PathStartContSp base (qfTail q f) (resolveSegs false [] (pathSegments true []))
      (q.map (queryText true)) (f.map fragmentText) := by
  intro ctx' hov hbuf hq0 hf0 hpath hsp hnf
  rw [run_pathStart_other_sp base _ ctx' hsp (fun c r he => by
    rcases qfTail_head q f with h | h | h <;> rw [he] at h <;> simp at h <;> subst h <;> decide)]
  have := run_path_ref base ([] ++ qfTail q f) ctx' hpath hov hbuf hq0 hf0
  rw [List.nil_append] at this
  rw [this, show qfTail q f = [] ++ qfTail q f from rfl, splitRef_parts (by simp) (by simp) hqh,
    hsp, show (ctx'.url.scheme == "file") = false by simpa using hnf]

/-- path がある authority の続き（`http://h/p`、`http://h\p`）。 -/
theorem pathStartContSp_some (base : Option Url) {d : Char} (hd : isSlashBS d = true)
    (pp : List Char) (q f : Option (List Char))
    (hq : '?' ∉ pp) (hh : '#' ∉ pp) (hqh : ∀ x, q = some x → '#' ∉ x) :
    PathStartContSp base (d :: (pp ++ qfTail q f)) (resolveSegs false [] (pathSegments true pp))
      (q.map (queryText true)) (f.map fragmentText) := by
  intro ctx' hov hbuf hq0 hf0 hpath hsp hnf
  rw [run_pathStart_sep_sp base _ ctx' hsp hd, run_path_ref base _ ctx' hpath hov hbuf hq0 hf0,
    splitRef_parts hq hh hqh, hsp, show (ctx'.url.scheme == "file") = false by simpa using hnf]

/-! ## host と authority（special な URL） -/

/-- 仕様の host と port の部分（special な URL）。host が空なら失敗する。 -/
def hostResultSp (t : List Char → Option String) (u : Url) (hp : List Char) (P : List String)
    (Q F : Option String) : Option Url :=
  if (splitHostPort false hp).1.isEmpty then none
  else
    match hostParser t (splitHostPort false hp).1 false, specPort u.scheme (splitHostPort false hp).2 with
    | some host, some port =>
      some { u with host := some host, port, path := .list P, query := Q, fragment := F }
    | _, _ => none

/-- **host state から先**（special な URL）。 -/
theorem host_flow_sp (base : Option Url) (hp T1 : List Char) (ctxH : PCtx) {P : List String}
    {Q F : Option String}
    (hov : ctxH.over = none) (hbuf : ctxH.buffer = []) (hib : ctxH.insideBrackets = false)
    (hsp : ctxH.url.isSpecial = true) (hnf : ctxH.url.scheme ≠ "file") (hport : ctxH.url.port = none)
    (hq0 : ctxH.url.query = none) (hf0 : ctxH.url.fragment = none) (hpath : ctxH.url.path = .list [])
    (hhp : ∀ c ∈ hp, isTerminator true (some c) = false)
    (hT1 : ∀ c r, T1 = c :: r → isTerminator true (some c) = true)
    (hcont : PathStartContSp base T1 P Q F) :
    run base .host (hp ++ T1) ctxH = toResult (hostResultSp ctxH.toAscii ctxH.url hp P Q F) := by
  have hterm : ∀ c ∈ hp, isTerminator ctxH.url.isSpecial (some c) = false := by
    intro c hc; rw [hsp]; exact hhp c hc
  rw [run_host_read base hp T1 ctxH hov hterm, hib]
  unfold hostResultSp
  rcases hsplit : splitHostPort false hp with ⟨h, _ | p⟩
  · simp only
    rw [run_host_term base T1 _ (by exact hov) (fun c r he => ⟨by rw [hsp]; exact hT1 c r he, by
      intro e; subst e; have := hT1 _ r he; simp [isTerminator] at this⟩)]
    simp only [hsp, Bool.true_and, hbuf, List.nil_append, Bool.not_true]
    by_cases he : h.isEmpty = true
    · rw [if_pos he, if_pos he]; rfl
    · rw [if_neg he, if_neg he]
      cases hostParser ctxH.toAscii h false with
      | none => rfl
      | some host =>
        simp only [specPort]
        rw [hcont _ (by exact hov) rfl (by exact hq0) (by exact hf0) (by exact hpath) (by exact hsp)
          (by exact hnf)]
        simp [toResult, ← hport]
  · simp only
    rw [run_host_colon base _ _ (by exact hov) rfl]
    simp only [hbuf, List.nil_append]
    by_cases he : h.isEmpty = true
    · rw [if_pos he, if_pos he]; rfl
    · rw [if_neg he, if_neg he]
      simp only [hsp, Bool.not_true]
      cases hostParser ctxH.toAscii h false with
      | none => rfl
      | some host =>
        simp only
        have hpp : ∀ c ∈ p, isTerminator true (some c) = false := by
          intro c hc
          exact hhp c (by rw [splitHostPort_some hsplit]; simp [hc])
        rw [run_port_read base p T1 _ (by exact hov) rfl (by exact hport)
          (by rw [show ({ ctxH.url with host := some host } : Url).isSpecial = true from hsp]; exact hpp)
          (by intro c r he; rw [show ({ ctxH.url with host := some host } : Url).isSpecial = true from hsp]
              exact hT1 c r he)]
        simp only
        cases specPort ctxH.url.scheme (some p) with
        | none => rfl
        | some port =>
          simp only
          rw [hcont _ (by exact hov) rfl (by exact hq0) (by exact hf0) (by exact hpath) (by exact hsp)
            (by exact hnf)]
          rfl

/-- 仕様の authority の部分（special な URL）。 -/
def authResultSp (t : List Char → Option String) (s : String) (auth : List Char) (P : List String)
    (Q F : Option String) : Option Url :=
  if (splitLast '@' auth).1.isSome && (splitLast '@' auth).2.isEmpty then none
  else hostResultSp t { scheme := s, username := (userinfoParts (splitLast '@' auth).1).1,
                                     password := (userinfoParts (splitLast '@' auth).1).2 }
         (splitLast '@' auth).2 P Q F

/-- **authority state から先**（special な URL）。 -/
theorem authority_flow_sp (base : Option Url) (t : List Char → Option String) (s : String)
    (hsp : isSpecialScheme s = true) (hnf : s ≠ "file") (auth T1 : List Char)
    {P : List String} {Q F : Option String}
    (hauth : ∀ c ∈ auth, isTerminator true (some c) = false)
    (hT1 : ∀ c r, T1 = c :: r → isTerminator true (some c) = true)
    (hcont : PathStartContSp base T1 P Q F) :
    run base .authority (auth ++ T1) { url := { scheme := s }, toAscii := t }
      = toResult (authResultSp t s auth P Q F) := by
  have hsp' : ({ scheme := s } : Url).isSpecial = true := hsp
  have h0 : ({ url := { scheme := s }, toAscii := t } : PCtx)
      = authCtx { url := { scheme := s }, toAscii := t } [] := by
    rw [authCtx_of_none (splitLast_nil '@')]
  rw [h0, run_authority_read base _ rfl rfl auth T1 [] (by rw [hsp']; exact hauth), List.nil_append]
  unfold authResultSp
  rcases hs : splitLast '@' auth with ⟨_ | x, y⟩
  · have hy := splitLast_none hs
    subst hy
    rw [authCtx_of_none hs, run_authority_end]
    · simp only [Bool.false_and, Bool.false_eq_true, if_false, Option.isSome_none]
      exact host_flow_sp base y T1 _ rfl rfl rfl hsp' hnf rfl rfl rfl rfl hauth hT1 hcont
    · intro c r he; rw [hsp']; exact hT1 c r he
  · rw [authCtx_of_some hs, run_authority_end]
    · simp only [Bool.true_and, Option.isSome_some]
      by_cases hy : y.isEmpty = true
      · rw [if_pos hy, if_pos hy]; simp [fail, toResult]
      · rw [if_neg hy, if_neg hy]
        rw [userinfoFold_false]
        exact host_flow_sp base y T1 _ rfl rfl rfl hsp' hnf rfl rfl rfl rfl
          (fun c hc => hauth c (mem_of_splitLast hs hc)) hT1 hcont
    · intro c r he
      rw [show ((List.foldl userinfoStep ((({ scheme := s } : Url)), false) x).1).isSpecial = true by
        rw [userinfoFold_false]; exact hsp]
      exact hT1 c r he

/-! ## 組み立て -/

/-- **authority から先の全体**（special な URL）。 -/
theorem branch_special (base : Option Url) (t : List Char → Option String) (s : String)
    (hsp : isSpecialScheme s = true) (hnf : s ≠ "file") (rest : List Char) :
    run base .authority (rest.dropWhile isSlashBS) { url := { scheme := s }, toAscii := t }
      = toResult (specParseSpecial t s rest) := by
  obtain ⟨hdec, hnq, hnh, hqh⟩ := splitRef_decomp (rest.dropWhile isSlashBS)
  have hspec : specParseSpecial t s rest
      = authResultSp t s (splitFirstBy isSlashBS (splitRef (rest.dropWhile isSlashBS)).1).1
          (resolveSegs false []
            (pathSegments true ((splitFirstBy isSlashBS (splitRef (rest.dropWhile isSlashBS)).1).2.getD [])))
          ((splitRef (rest.dropWhile isSlashBS)).2.1.map (queryText true))
          ((splitRef (rest.dropWhile isSlashBS)).2.2.map fragmentText) := rfl
  rw [hspec]
  generalize rest.dropWhile isSlashBS = l at hdec hnq hnh hqh ⊢
  generalize (splitRef l).1 = ap at hdec hnq hnh
  generalize (splitRef l).2.1 = q at hdec hqh
  generalize (splitRef l).2.2 = f at hdec
  subst hdec
  have hterm : ∀ {x : List Char}, (∀ c ∈ x, isSlashBS c = false) → '?' ∉ x → '#' ∉ x →
      ∀ c ∈ x, isTerminator true (some c) = false := by
    intro x hs hq hh c hc
    rw [isTerminator_sp, hs c hc]
    have : c ≠ '?' := fun e => hq (e ▸ hc)
    have : c ≠ '#' := fun e => hh (e ▸ hc)
    simp [*]
  rcases first_occurrence_by isSlashBS ap with hns | ⟨a, d, pp, rfl, hd, ha⟩
  · rw [splitFirstBy_none _ _ hns]
    exact authority_flow_sp base t s hsp hnf ap (qfTail q f) (hterm hns hnq hnh)
      (fun c r he => by
        rcases qfTail_head q f with h | h | h <;> rw [he] at h <;> simp at h <;> subst h <;> decide)
      (pathStartContSp_none base q f hqh)
  · rw [splitFirstBy_append _ _ _ _ ha hd, List.append_assoc, List.cons_append]
    exact authority_flow_sp base t s hsp hnf a _
      (hterm ha (fun hm => hnq (by simp [hm])) (fun hm => hnh (by simp [hm])))
      (fun c r he => by simp at he; rw [← he.1, isTerminator_sp, hd]; rfl)
      (pathStartContSp_some base hd pp q f (fun hm => hnq (by simp [hm]))
        (fun hm => hnh (by simp [hm])) hqh)

/-- scheme state が special な scheme（`file` を除く）を読み終えると、base 無しなら special authority slashes state へ。 -/
theorem run_schemeStart_special (t : List Char → Option String)
    {a : Char} {pre rest : List Char} (ha : isAsciiAlpha a = true)
    (hpre : ∀ c ∈ pre, schemeChar c = true)
    (hsp : isSpecialScheme (String.ofList ((a :: pre).map asciiLowerChar)) = true)
    (hnf : String.ofList ((a :: pre).map asciiLowerChar) ≠ "file") :
    run none .schemeStart (a :: (pre ++ ':' :: rest)) { url := {}, toAscii := t }
      = run none .specialAuthoritySlashes rest
          { url := { scheme := String.ofList ((a :: pre).map asciiLowerChar) }, toAscii := t } := by
  rw [run, step, if_pos ha, run_scheme_prefix none pre _ _ hpre]
  rw [run, step]
  have hcol : (isAsciiAlphanumeric ':' || ':' == '+' || ':' == '-' || ':' == '.') = false := by
    decide
  have hsp' : isSpecialScheme (String.ofList (asciiLowerChar a :: pre.map asciiLowerChar)) = true := by
    simpa using hsp
  have hnf' : (String.ofList (asciiLowerChar a :: pre.map asciiLowerChar) == "file") = false := by
    simpa using hnf
  simp only [asciiLowercase, List.nil_append, String.toList_ofList, List.map_cons, List.map_nil,
    List.cons_append, hcol, Bool.false_eq_true, if_false, beq_self_eq_true, if_true,
    Option.isSome_none, Url.isSpecial, hsp', hnf', Bool.and_false]

/--
**special な scheme（`file` を除く）を持つ入力について、basic URL parser は関数的な仕様と一致する**（base 無し）。
-/
theorem run_spec_special (t : List Char → Option String)
    {l rest : List Char} {s : String} (hs : splitScheme l = some (s, rest))
    (hsp : isSpecialScheme s = true) (hnf : s ≠ "file") :
    run none .schemeStart l { url := {}, toAscii := t } = toResult (specParseSpecial t s rest) := by
  obtain ⟨a, pre, rfl, ha, hpre, rfl⟩ := splitScheme_some hs
  rw [run_schemeStart_special t ha hpre hsp hnf, run_specialAuthoritySlashes_drop,
    branch_special none t _ hsp hnf rest]

/--
**basic URL parser は、base 無しの入力について関数的な仕様と一致する。** 前提は「scheme が `file` でない」だけで、
special な scheme も special でない scheme も、scheme の無い入力（失敗する）も含む。
-/
theorem basicUrlParse_eq_specParse_noFile (t : List Char → Option String) (input : String)
    (h : ∀ s rest, splitScheme (preprocess input) = some (s, rest) → s ≠ "file") :
    basicUrlParse input none t = specParse t (preprocess input) := by
  cases hs : splitScheme (preprocess input) with
  | none => exact basicUrlParse_eq_specParse t input (fun _ _ he => by rw [hs] at he; cases he)
  | some p =>
    obtain ⟨sc, rest⟩ := p
    have hnf := h sc rest hs
    by_cases hsp : isSpecialScheme sc = true
    · unfold basicUrlParse
      rw [run_spec_special t hs hsp hnf]
      simp only [specParse, hs, hnf, hsp, if_true, if_false]
      cases specParseSpecial t sc rest <;> rfl
    · exact basicUrlParse_eq_specParse t input (fun s r he => by
        rw [hs] at he; cases he; simpa using hsp)

end Url.Spec
