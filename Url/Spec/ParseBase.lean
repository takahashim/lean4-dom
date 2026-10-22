import Url.Spec.ParseFile
import Url.StepValid

/-!
# basic URL parser と関数的な仕様の一致（§4.4、base を持つ入力）

`specParseBase`（`Url/Spec/Parse.lean`）が base を持つ入力の parse を書く。ここで parser との一致を示す。

* scheme の無い入力は no scheme state から、base が opaque path なら fragment だけ、`file` なら file state、
  それ以外は relative state に入る（`relRef`）。
* scheme を持つ入力は base の無いときと同じ道を通る。違うのは二つだけで、base と同じ special scheme なら
  special relative or authority state で相対参照として読み直すことと、`file` の base を file state が使うことである。
-/

namespace Url.Spec

open Infra Url

/-! ## query と fragment から始まる参照 -/

/-- query state は最初の `#` までを query にし、残りを fragment にする。 -/
theorem run_query_rest (base : Option Url) (x : List Char) (ctx : PCtx) (hov : ctx.over = none)
    (hbuf : ctx.buffer = []) (hq : ctx.url.query = some "") (hf0 : ctx.url.fragment = none) :
    run base .query x ctx
      = .ok { ctx.url with query := some (queryText ctx.url.isSpecial (splitFirst '#' x).1),
                           fragment := (splitFirst '#' x).2.map fragmentText } := by
  rcases first_occurrence '#' x with hn | ⟨a, f, rfl, hn⟩
  · rw [splitFirst_of_not_mem _ _ hn, Spec.run_query base x _ (fun c hc e => hn (e ▸ hc))]
    simp [queryOf, queryText, hbuf, hq, hf0]
  · rw [splitFirst_append _ _ _ hn, run_query_until_hash base a f _ hov hn,
      Spec.run_fragment base f _ "" rfl]
    simp [queryOf, queryText, hbuf, hq]

theorem splitRef_q (x : List Char) :
    splitRef ('?' :: x) = ([], some (splitFirst '#' x).1, (splitFirst '#' x).2) := by
  rcases first_occurrence '#' x with hn | ⟨a, f, rfl, hn⟩
  · rw [splitFirst_of_not_mem _ _ hn]
    simp [splitRef, splitFirst, splitFirst_of_not_mem _ _ hn]
  · rw [splitFirst_append _ _ _ hn]
    have : '?' :: (a ++ '#' :: f) = ('?' :: a) ++ '#' :: f := rfl
    simp only [splitRef, this, splitFirst_append '#' ('?' :: a) f (by simp [hn])]
    simp [splitFirst]

theorem splitRef_h (x : List Char) : splitRef ('#' :: x) = ([], none, some x) := by
  simp [splitRef, splitFirst]

/-! ## relative state から先 -/

/-- relative state の区切り。relative slash state へ。 -/
theorem run_relative_sep (b : Url) (t : List Char → Option String) {c : Char} (x : List Char)
    (hc : isPathSep b.isSpecial c = true) :
    run (some b) .relative (c :: x) { url := {}, toAscii := t }
      = run (some b) .relativeSlash x { url := { scheme := b.scheme }, toAscii := t } := by
  rw [run, step]
  simp only [isPathSep, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at hc
  rcases hc with rfl | ⟨hsp, rfl⟩
  · simp
  · simp [Url.isSpecial, ← hsp]

/-- relative slash state の二つ目の区切り（special な URL）。 -/
theorem run_relativeSlash_sp (b : Url) {d : Char} (x : List Char) (ctx : PCtx)
    (hsp : ctx.url.isSpecial = true) (hd : isSlashBS d = true) :
    run (some b) .relativeSlash (d :: x) ctx = run (some b) .specialAuthorityIgnoreSlashes x ctx := by
  rw [run, step]
  have : (some d == some '/' || some d == some '\\') = true := by
    simp only [isSlashBS, Bool.or_eq_true, beq_iff_eq] at hd
    rcases hd with rfl | rfl <;> simp
  rw [if_pos (by rw [hsp, Bool.true_and]; exact this)]

/-- relative slash state の二つ目の `/`（special でない URL）。 -/
theorem run_relativeSlash_ns (b : Url) (x : List Char) (ctx : PCtx)
    (hsp : ctx.url.isSpecial = false) :
    run (some b) .relativeSlash ('/' :: x) ctx = run (some b) .authority x ctx := by
  rw [run, step]; simp [hsp]

/-- **relative state から先は `relRef` である。** base は opaque path を持たず、`file` でない。 -/
theorem run_relative_ref (b : Url) (t : List Char → Option String) {Pb : List String}
    (hbp : b.path = .list Pb) (hbf : b.scheme ≠ "file") (l : List Char) :
    run (some b) .relative l { url := {}, toAscii := t } = toResult (relRef t b l) := by
  have hbf' : (b.scheme == "file") = false := by simpa using hbf
  unfold relRef
  rw [hbp]
  simp only
  match l with
  | [] =>
    rw [run, step]
    simp only [beq_iff_eq, reduceCtorEq, if_false]
    cases b; simp_all [toResult]
  | c :: x =>
    by_cases hq : c = '?'
    · subst hq
      rw [run, step]
      simp only [splitRef_q]
      rw [if_neg (by decide), if_neg (by simp), if_pos (Or.inl trivial)]
      rw [run_query_rest _ x _ rfl rfl rfl rfl]
      simp only [toResult, Option.isSome_some, if_true, Option.map_some]
      rw [← hbp]
      rfl
    by_cases hh : c = '#'
    · subst hh
      rw [run, step]
      simp only [splitRef_h]
      rw [if_neg (by decide), if_neg (by simp), if_pos (Or.inr trivial)]
      rw [Spec.run_fragment _ x _ "" rfl]
      simp only [toResult, Option.isSome_none, Bool.false_eq_true, if_false, Option.map_some]
      rw [← hbp]
      simp
    have hnqh : ¬(c = '?' ∨ c = '#') := fun h => h.elim hq hh
    simp only
    rw [if_neg hnqh]
    by_cases hs : isPathSep b.isSpecial c = true
    · rw [if_pos hs]
      match x with
      | [] =>
        rw [run_relative_absRef b [c] _ rfl rfl rfl rfl hs (by intro d t h; cases h) hbf]
        rfl
      | d :: x' =>
        simp only
        by_cases h1 : (b.isSpecial && isSlashBS d) = true
        · rw [if_pos h1]
          simp only [Bool.and_eq_true] at h1
          rw [run_relative_sep b t _ hs, run_relativeSlash_sp b _ _ h1.1 h1.2, run_ignoreSlashes,
            branch_special (some b) t b.scheme h1.1 hbf]
        · rw [if_neg h1]
          by_cases h2 : (!b.isSpecial && d == '/') = true
          · rw [if_pos h2]
            simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h2
            obtain ⟨hsp, rfl⟩ := h2
            rw [run_relative_sep b t _ hs, run_relativeSlash_ns b x' _ hsp,
              branch_authority (some b) t b.scheme hsp x']
          · rw [if_neg h2]
            refine run_relative_absRef b _ _ rfl rfl rfl rfl hs ?_ hbf
            intro d' t' he
            simp only [List.cons.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            cases hsp : b.isSpecial
            · simp only [hsp, Bool.not_false, Bool.true_and] at h2
              simpa [isPathSep] using h2
            · simp only [hsp, Bool.true_and] at h1
              simpa [isPathSep, isSlashBS] using h1
    · rw [if_neg hs]
      exact run_relative_pathRef b (c :: x) _ hbp hbf rfl rfl rfl rfl (by simpa using hs) hq hh

/-! ## base を見ない state -/

/-- fragment state は base を見ない。 -/
theorem run_fragment_base (b1 b2 : Option Url) : ∀ (l : List Char) (ctx : PCtx),
    run b1 .fragment l ctx = run b2 .fragment l ctx
  | [], ctx => by rw [run, step, run, step]
  | c :: t, ctx => by
    rw [run, step, run, step]
    exact run_fragment_base b1 b2 t _

/-- query state は base を見ない。 -/
theorem run_query_base (b1 b2 : Option Url) : ∀ (l : List Char) (ctx : PCtx),
    run b1 .query l ctx = run b2 .query l ctx
  | [], ctx => by rw [run, step]; conv => rhs; rw [run, step]
  | c :: t, ctx => by
    by_cases hc : c = '#'
    · subst hc
      rw [run, step]; conv => rhs; rw [run, step]
      split
      · exact run_query_base b1 b2 t _
      · exact run_fragment_base b1 b2 t _
    · rw [run, step]
      · have e : run b2 .query (c :: t) ctx
            = run b2 .query t { ctx with buffer := ctx.buffer ++ [c] } := by
          rw [run, step]; exact hc
        rw [e]
        exact run_query_base b1 b2 t _
      · exact hc

/-- path state は base を見ない。 -/
theorem run_path_base (b1 b2 : Option Url) : ∀ (l : List Char) (ctx : PCtx),
    run b1 .path l ctx = run b2 .path l ctx
  | [], ctx => by rw [run, step]; conv => rhs; rw [run, step]
  | c :: t, ctx => by
    rw [run, step]; conv => rhs; rw [run, step]
    (repeat' split) <;> first
      | rfl
      | exact run_path_base b1 b2 t _
      | exact run_query_base b1 b2 t _
      | exact run_fragment_base b1 b2 t _

/-- path start state は base を見ない。 -/
theorem run_pathStart_base (b1 b2 : Option Url) (l : List Char) (ctx : PCtx) :
    run b1 .pathStart l ctx = run b2 .pathStart l ctx := by
  cases l <;>
  · rw [run, step]; conv => rhs; rw [run, step]
    (repeat' split) <;> first
      | rfl
      | exact run_path_base b1 b2 _ _
      | exact run_query_base b1 b2 _ _
      | exact run_fragment_base b1 b2 _ _

/-- file host state は base を見ない。 -/
theorem run_fileHost_base (b1 b2 : Option Url) : ∀ (l : List Char) (ctx : PCtx),
    run b1 .fileHost l ctx = run b2 .fileHost l ctx
  | [], ctx => by
    rw [run, step]; conv => rhs; rw [run, step]
    (repeat' split) <;> first
      | rfl
      | exact run_path_base b1 b2 _ _
      | exact run_pathStart_base b1 b2 _ _
  | c :: t, ctx => by
    rw [run, step]; conv => rhs; rw [run, step]
    (repeat' split) <;> first
      | rfl
      | exact run_fileHost_base b1 b2 t _
      | exact run_path_base b1 b2 _ _
      | exact run_pathStart_base b1 b2 _ _

/-- file state は url の scheme と host を書き換えてから読むので、入る前の url の違いを残さない。 -/
theorem run_file_url (base : Option Url) (l : List Char) (t : List Char → Option String) :
    run base .file l { url := {}, toAscii := t } = run base .file l { url := { scheme := "file" }, toAscii := t } := by
  cases l <;>
  · rw [run, step.eq_def]
    conv => rhs; rw [run, step.eq_def]

/-! ## `file` の base -/

theorem shortenPath_eq {u : Url} {P : List String} (hp : u.path = .list P) :
    shortenPath u = { u with path := .list (shorten (u.scheme == "file") P) } := by
  unfold shortenPath shorten
  rw [hp]
  dsimp only
  have hgd : P.getD 0 "" = P.headD "" := by cases P <;> rfl
  rw [hgd]
  split
  · next h => rw [← hp]
  · rfl

/-- base が `file` のときの file state で、区切りでない入力。 -/
theorem run_file_fbase (b : Url) (hbf : b.scheme = "file") (c : Char) (x : List Char)
    (t : List Char → Option String) (hc : isSlashBS c = false) :
    run (some b) .file (c :: x) { url := { scheme := "file" }, toAscii := t }
      = (if c = '?' then
          run (some b) .query x
            { url := { scheme := "file", host := b.host, path := b.path, query := some "" }, toAscii := t }
        else if c = '#' then
          run (some b) .fragment x
            { url := { scheme := "file", host := b.host, path := b.path, query := b.query,
                       fragment := some "" }, toAscii := t }
        else
          run (some b) .path (c :: x)
            { url := fileBasePath { scheme := "file", host := b.host, path := b.path } (c :: x),
              toAscii := t }) := by
  have hns : ¬(some c == some '/' || some c == some '\\') = true := by
    simp only [isSlashBS, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hc
    simp [hc.1, hc.2]
  by_cases hq : c = '?'
  · subst hq
    rw [run, step, if_neg hns]
    simp [hbf]
  · by_cases hh : c = '#'
    · subst hh
      rw [run, step, if_neg hns]
      simp [hbf]
    · rw [if_neg hq, if_neg hh, run, step, if_neg hns]
      · simp [hbf]
      all_goals first | exact hq | exact hh | simp

theorem run_file_fbase_nil (b : Url) (hbf : b.scheme = "file") (t : List Char → Option String) :
    run (some b) .file [] { url := { scheme := "file" }, toAscii := t }
      = .ok { scheme := "file", host := b.host, path := b.path, query := b.query } := by
  rw [run, step]; simp [hbf]

/-- base が `file` のときの file slash state で、区切りでない入力。 -/
theorem run_fileSlash_fbase (b : Url) (hbf : b.scheme = "file") (T : List Char) (ctx : PCtx)
    (hT : ∀ c r, T = c :: r → isSlashBS c = false) :
    run (some b) .fileSlash T ctx
      = run (some b) .path T
          { ctx with url := fileSlashDrive { ctx.url with host := b.host } b.path T } := by
  cases T with
  | nil => rw [run, step]; simp [hbf]
  | cons c r =>
    have hc := hT c r rfl
    have hns : ¬(some c == some '/' || some c == some '\\') = true := by
      simp only [isSlashBS, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hc
      simp [hc.1, hc.2]
    rw [run, step, if_neg hns]
    simp [hbf]

/-- file slash state 2.1 の drive letter の引き継ぎは、仕様の `driveOf` である。 -/
theorem fileSlashDrive_eq (u : Url) (b : Url) {Pb : List String} (hbp : b.path = .list Pb)
    (hu : u.path = .list []) (x : List Char) :
    fileSlashDrive u b.path x = { u with path := .list (specParseFileBase.driveOf b x) } := by
  unfold fileSlashDrive specParseFileBase.driveOf
  rw [hbp]
  cases Pb with
  | nil => simp only; rw [← hu]
  | cons s P =>
    simp only
    split
    · unfold appendSegment; rw [hu]; rfl
    · rw [← hu]

/-- **base が `file` のときの file state から先は `specParseFileBase` である。** -/
theorem branch_file_base (b : Url) (hbf : b.scheme = "file") {Pb : List String}
    (hbp : b.path = .list Pb) (t : List Char → Option String) (l : List Char) :
    run (some b) .file l { url := { scheme := "file" }, toAscii := t }
      = toResult (specParseFileBase t b l) := by
  have hpl : specParseFileBase.pathList b = Pb := by simp [specParseFileBase.pathList, hbp]
  unfold specParseFileBase
  match l with
  | [] =>
    rw [run_file_fbase_nil b hbf t]
    simp [toResult, hpl, hbp, splitRef, splitFirst]
  | c1 :: x =>
    simp only
    by_cases h1 : isSlashBS c1 = true
    · rw [if_pos h1, run_file_sep (some b) _ _ h1]
      have hc1q : c1 ≠ '?' := by intro e; subst e; simp [isSlashBS] at h1
      have hc1h : c1 ≠ '#' := by intro e; subst e; simp [isSlashBS] at h1
      rw [splitRef_cons hc1q hc1h]
      match x with
      | c2 :: X =>
        simp only
        by_cases h2 : isSlashBS c2 = true
        · rw [if_pos h2, run_fileSlash_sep (some b) _ _ h2, run_fileHost_base (some b) none]
          refine Eq.trans ?_ (branch_file none (by simp) t (c1 :: c2 :: X))
          rw [run_file_sep none _ _ h1, run_fileSlash_sep none _ _ h2]
        · rw [if_neg h2, run_fileSlash_fbase b hbf _ _ (fun c r he => by
            simp at he; rw [← he.1]; simpa using h2)]
          rw [fileSlashDrive_eq _ b hbp rfl]
          rw [run_path_ref (some b) _ _ (P := specParseFileBase.driveOf b (c2 :: X)) rfl rfl rfl rfl rfl]
          simp [toResult, Url.isSpecial, isSpecialScheme]
      | [] =>
        simp only
        rw [run_fileSlash_fbase b hbf [] _ (fun c r he => by cases he)]
        rw [fileSlashDrive_eq _ b hbp rfl]
        rw [run_path_ref (some b) _ _ (P := specParseFileBase.driveOf b []) rfl rfl rfl rfl rfl]
        simp [toResult, Url.isSpecial, isSpecialScheme, splitRef, splitFirst]
    · have h1' : isSlashBS c1 = false := by simpa using h1
      rw [if_neg h1, run_file_fbase b hbf c1 x t h1']
      by_cases hq : c1 = '?'
      · subst hq
        rw [if_pos rfl, if_pos (Or.inl rfl), run_query_rest _ x _ rfl rfl rfl rfl, splitRef_q]
        simp [toResult, hbp, Url.isSpecial, isSpecialScheme]
      · by_cases hh : c1 = '#'
        · subst hh
          rw [if_neg (by decide), if_pos rfl, if_pos (Or.inr rfl), Spec.run_fragment _ x _ "" rfl,
            splitRef_h]
          simp [toResult, hbp]
        · rw [if_neg hq, if_neg hh, if_neg (fun h => h.elim hq hh)]
          have hfb : fileBasePath ({ scheme := "file", host := b.host, path := b.path } : Url) (c1 :: x)
              = { scheme := "file", host := b.host,
                  path := .list (if startsWithWindowsDrive (c1 :: x) then [] else shorten true Pb) } := by
            unfold fileBasePath
            split
            · rfl
            · rw [shortenPath_eq (P := Pb) (by simp [hbp])]; simp
          rw [hfb, run_path_ref (some b) _ _ rfl rfl rfl rfl rfl, hpl]
          simp [toResult, Url.isSpecial, isSpecialScheme]

/-! ## 入口 -/

/-- scheme state が special な scheme（`file` を除く）を読み終えたときの行き先（base あり）。 -/
theorem run_schemeStart_special_base (b : Url) (t : List Char → Option String)
    {a : Char} {pre rest : List Char} (ha : isAsciiAlpha a = true)
    (hpre : ∀ c ∈ pre, schemeChar c = true)
    (hsp : isSpecialScheme (String.ofList ((a :: pre).map asciiLowerChar)) = true)
    (hnf : String.ofList ((a :: pre).map asciiLowerChar) ≠ "file") :
    run (some b) .schemeStart (a :: (pre ++ ':' :: rest)) { url := {}, toAscii := t }
      = if b.scheme = String.ofList ((a :: pre).map asciiLowerChar) then
          run (some b) .specialRelativeOrAuthority rest
            { url := { scheme := String.ofList ((a :: pre).map asciiLowerChar) }, toAscii := t }
        else
          run (some b) .specialAuthoritySlashes rest
            { url := { scheme := String.ofList ((a :: pre).map asciiLowerChar) }, toAscii := t } := by
  rw [run, step, if_pos ha, run_scheme_prefix (some b) pre _ _ hpre]
  rw [run, step]
  have hcol : (isAsciiAlphanumeric ':' || ':' == '+' || ':' == '-' || ':' == '.') = false := by
    decide
  have hsp' : isSpecialScheme (String.ofList (asciiLowerChar a :: pre.map asciiLowerChar)) = true := by
    simpa using hsp
  have hnf' : (String.ofList (asciiLowerChar a :: pre.map asciiLowerChar) == "file") = false := by
    simpa using hnf
  simp only [asciiLowercase, List.nil_append, String.toList_ofList, List.map_cons, List.map_nil,
    List.cons_append, hcol, Bool.false_eq_true, if_false, beq_self_eq_true, if_true,
    Option.isSome_none, Url.isSpecial, hsp', hnf', Bool.true_and]
  by_cases he : b.scheme = String.ofList (asciiLowerChar a :: pre.map asciiLowerChar)
  · rw [if_pos (by simp [he]), if_pos (by simpa using he)]
  · rw [if_neg (by simpa using he), if_neg (by simpa using he)]

/-- scheme の無い入力は、no scheme state の結果がそのまま parse の結果になる（失敗も含む）。 -/
theorem basicUrlParse_noScheme_eq {input : String} {b : Url} {toAscii : List Char → Option String}
    (hs : ¬ HasScheme (preprocess input)) :
    basicUrlParse input (some b) toAscii
      = match run (some b) .noScheme (preprocess input) { url := {}, toAscii } with
        | .ok u => some u
        | _ => none := by
  unfold basicUrlParse
  rcases run_schemeStart_cases (some b) (preprocess input) { url := {}, toAscii } rfl hs with hc | hc
  · rw [hc]
    simp only
    cases run (some b) .noScheme (preprocess input) { url := {}, toAscii } <;> rfl
  · rw [hc]
    cases run (some b) .noScheme (preprocess input) { url := {}, toAscii } <;> rfl

theorem toResult_match (o : Option Url) :
    (match toResult o with | .ok u => some u | _ => none) = o := by
  cases o <;> rfl

/--
**basic URL parser は、base を持つ全入力について関数的な仕様と一致する。** base は `ValidUrl` を満たすこと
（parse の結果ならいつでも満たす）。
-/
theorem basicUrlParse_eq_specParseBase (t : List Char → Option String) (input : String) (b : Url)
    (hb : ValidUrl b) :
    basicUrlParse input (some b) t = specParseBase t b (preprocess input) := by
  have hlist : b.isSpecial = true → ∃ Pb, b.path = .list Pb := by
    intro hsp
    have := hb.specialHasList hsp
    cases hp : b.path with
    | «opaque» o => simp [Url.hasOpaquePath, hp, Path.isOpaque] at this
    | list P => exact ⟨P, rfl⟩
  cases hs : splitScheme (preprocess input) with
  | none =>
    have hns := (splitScheme_none_iff _).mp hs
    rw [basicUrlParse_noScheme_eq hns]
    simp only [specParseBase, hs]
    cases hbp : b.path with
    | «opaque» o =>
      have hop : b.hasOpaquePath = true := by simp [Url.hasOpaquePath, hbp, Path.isOpaque]
      simp only
      generalize hl : preprocess input = l at hns ⊢
      by_cases hh : ∃ f, l = '#' :: f
      · obtain ⟨f, rfl⟩ := hh
        rw [run, step, if_neg (by simp), if_pos hop]
        rw [Spec.run_fragment _ f _ "" rfl]
        simp [hbp]
      · rw [run_noScheme_opaque b l _ rfl hop (by
          intro c t he hc; subst he; subst hc; exact hh ⟨t, rfl⟩)]
        simp only
        split
        · simp_all
        · rfl
    | list Pb =>
      have hop : b.hasOpaquePath = false := by simp [Url.hasOpaquePath, hbp, Path.isOpaque]
      simp only
      by_cases hf : b.scheme = "file"
      · rw [if_pos hf]
        have hnf : run (some b) .noScheme (preprocess input) { url := {}, toAscii := t }
            = run (some b) .file (preprocess input) { url := {}, toAscii := t } := by
          cases preprocess input <;> (rw [run, step]; simp [hop, hf])
        rw [hnf, run_file_url, branch_file_base b hf hbp t, toResult_match]
      · rw [if_neg hf, run_noScheme_relative b _ _ hop hf, run_relative_ref b t hbp hf, toResult_match]
  | some p =>
    obtain ⟨sc, rest⟩ := p
    obtain ⟨a, pre, hl, ha, hpre, hsc⟩ := splitScheme_some hs
    simp only [specParseBase, hs]
    unfold basicUrlParse
    rw [hl]
    by_cases hfile : sc = "file"
    · rw [run_schemeStart_file (some b) t ha hpre (by rw [← hsc, hfile]), if_pos hfile]
      by_cases hbf : b.scheme = "file"
      · rw [if_pos hbf]
        obtain ⟨Pb, hbp⟩ := hlist (by simp [Url.isSpecial, hbf, isSpecialScheme])
        rw [branch_file_base b hbf hbp t rest]
        cases specParseFileBase t b rest <;> rfl
      · rw [if_neg hbf, branch_file (some b) (fun b' h => by cases h; exact hbf) t rest]
        cases specParseFile t rest <;> rfl
    · rw [if_neg hfile]
      by_cases hsp : isSpecialScheme sc = true
      · rw [run_schemeStart_special_base b t ha hpre (by rw [← hsc]; exact hsp)
          (by rw [← hsc]; exact hfile), ← hsc]
        by_cases heq : b.scheme = sc
        · rw [if_pos heq, if_pos (by simp [hsp, heq])]
          obtain ⟨Pb, hbp⟩ := hlist (by simp [Url.isSpecial, heq, hsp])
          by_cases h2 : ∃ r2, rest = '/' :: '/' :: r2
          · obtain ⟨r2, rfl⟩ := h2
            simp only
            rw [run, step, run_ignoreSlashes]
            have := branch_special (some b) t sc hsp hfile ('/' :: '/' :: r2)
            simp only [List.dropWhile, isSlashBS, beq_self_eq_true, Bool.true_or] at this
            rw [this]
            cases specParseSpecial t sc ('/' :: '/' :: r2) <;> rfl
          · have hr : ∀ r2, rest ≠ '/' :: '/' :: r2 := fun r2 he => h2 ⟨r2, he⟩
            rw [run_specialRelativeOrAuthority_relative _ _ _ hr]
            rw [run_relative_scheme_irrelevant b rest { url := {}, toAscii := t } sc]
            rw [run_relative_ref b t hbp (by rw [heq]; exact hfile) rest]
            generalize relRef t b rest = R
            cases R <;>
            · simp only [toResult]
              try (split <;> first | rfl | simp_all)
        · rw [if_neg heq, if_neg (by simp [heq]), if_pos hsp, run_specialAuthoritySlashes_drop,
            branch_special (some b) t sc hsp hfile rest]
          cases specParseSpecial t sc rest <;> rfl
      · have hns : isSpecialScheme sc = false := by simpa using hsp
        rw [← hl, run_spec_nonSpecial (some b) t hs hns]
        rw [if_neg (by simp [hns]), if_neg (by simp [hns])]
        cases specParseNonSpecial t sc rest <;> rfl

/--
**`URL(input, base)` は関数的な仕様 `specParseUrl` と一致する。** 入力にも base にも制限は無い。

state も pointer も buffer も持たない仕様が、basic URL parser と同じ結果（失敗を含む）を返す。
base は仕様の側でも parse するので、parser を一度も呼ばない形である。
-/
theorem parseUrl_eq_specParseUrl (t : List Char → Option String) (input : String)
    (base : Option String) : parseUrl input base t = specParseUrl t input base := by
  cases base with
  | none => exact basicUrlParse_eq_specParse_all t input
  | some bs =>
    simp only [parseUrl, specParseUrl]
    rw [← basicUrlParse_eq_specParse_all t bs]
    cases hb : basicUrlParse bs none t with
    | none => rfl
    | some bu =>
      have hv : ValidUrl bu := basicUrlParse_valid (fun _ h => by cases h) hb
      simp only [Option.bind_some]
      exact basicUrlParse_eq_specParseBase t input bu hv

end Url.Spec
