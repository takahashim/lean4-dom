import Url.Spec.ParseSpecial
import Url.Roundtrip.Path

/-!
# basic URL parser と関数的な仕様の一致（§4.4、base 無し・`file`）

`file` URL は scheme state から file state、file slash state、file host state を通る。
base が無ければ、file state と file slash state は区切りでない文字を path state に渡すだけである。
file host state は区切りまでを buffer に積み、Windows drive letter なら host ではなく path として読み直させる。
-/

namespace Url.Spec

open Infra Url

/-! ## 三つの state -/

theorem run_file_sep (base : Option Url) {c : Char} (r : List Char) (ctx : PCtx)
    (hc : isSlashBS c = true) :
    run base .file (c :: r) ctx
      = run base .fileSlash r
          { ctx with url := { ctx.url with scheme := "file", host := some .empty } } := by
  have : (some c == some '/' || some c == some '\\') = true := by
    simp only [isSlashBS, Bool.or_eq_true, beq_iff_eq] at hc
    rcases hc with rfl | rfl <;> simp
  cases base <;> (rw [run, step]; rw [if_pos this])

theorem run_file_other (base : Option Url) (hb : ∀ b, base = some b → b.scheme ≠ "file")
    (T : List Char) (ctx : PCtx) (hT : ∀ c r, T = c :: r → isSlashBS c = false) :
    run base .file T ctx
      = run base .path T { ctx with url := { ctx.url with scheme := "file", host := some .empty } } := by
  cases T with
  | nil =>
    cases base with
    | none => rw [run, step]; simp
    | some b => rw [run, step]; simp [hb b rfl]
  | cons c r =>
    have hc := hT c r rfl
    have : ¬(some c == some '/' || some c == some '\\') = true := by
      simp only [isSlashBS, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hc
      simp [hc.1, hc.2]
    cases base with
    | none => rw [run, step, if_neg this]
    | some b => rw [run, step, if_neg this]; simp [hb b rfl]

theorem run_fileSlash_sep (base : Option Url) {c : Char} (r : List Char) (ctx : PCtx)
    (hc : isSlashBS c = true) :
    run base .fileSlash (c :: r) ctx = run base .fileHost r ctx := by
  have : (some c == some '/' || some c == some '\\') = true := by
    simp only [isSlashBS, Bool.or_eq_true, beq_iff_eq] at hc
    rcases hc with rfl | rfl <;> simp
  cases base <;> (rw [run, step]; rw [if_pos this])

theorem run_fileSlash_other (base : Option Url) (hb : ∀ b, base = some b → b.scheme ≠ "file")
    (T : List Char) (ctx : PCtx)
    (hT : ∀ c r, T = c :: r → isSlashBS c = false) :
    run base .fileSlash T ctx = run base .path T ctx := by
  cases T with
  | nil =>
    cases base with
    | none => rw [run, step]; simp
    | some b => rw [run, step]; simp [hb b rfl]
  | cons c r =>
    have hc := hT c r rfl
    have : ¬(some c == some '/' || some c == some '\\') = true := by
      simp only [isSlashBS, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hc
      simp [hc.1, hc.2]
    cases base with
    | none => rw [run, step, if_neg this]
    | some b => rw [run, step, if_neg this]; simp [hb b rfl]

/-- file host state の区切り。 -/
def fileDelim (c : Char) : Bool := isSlashBS c || c == '?' || c == '#'

/-- file host state は区切りまでを buffer に積む。 -/
theorem run_fileHost_read (base : Option Url) : ∀ (hs T : List Char) (ctx : PCtx),
    (∀ c ∈ hs, fileDelim c = false) →
    run base .fileHost (hs ++ T) ctx = run base .fileHost T { ctx with buffer := ctx.buffer ++ hs }
  | [], T, ctx, _ => by simp
  | c :: hs, T, ctx, h => by
    have hc := h c (by simp)
    simp only [fileDelim, isSlashBS, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hc
    rw [List.cons_append, run, step, if_neg (by simp [hc.1.1.1, hc.1.1.2, hc.1.2, hc.2])]
    rw [run_fileHost_read base hs T _ (fun x hx => h x (by simp [hx]))]
    simp [List.append_assoc]

/-- file host state 1.3.3：`localhost` は空の host にする。 -/
def fileHostOf (h : Host) : Host := if hostSerializer h == "localhost" then .empty else h

/-- file host state の終わり。 -/
theorem run_fileHost_end (base : Option Url) (T : List Char) (ctx : PCtx) (hov : ctx.over = none)
    (hT : ∀ c r, T = c :: r → fileDelim c = true) :
    run base .fileHost T ctx
      = if isWindowsDrive ctx.buffer then run base .path T ctx
        else if ctx.buffer.isEmpty then
          run base .pathStart T { ctx with url := { ctx.url with host := some .empty } }
        else match hostParser ctx.toAscii ctx.buffer (!ctx.url.isSpecial) with
          | none => .failure
          | some h =>
            run base .pathStart T
              { ctx with buffer := [], url := { ctx.url with host := some (fileHostOf h) } } := by
  have hcommon :
      (if (ctx.over.isNone && isWindowsDrive ctx.buffer) = true then run base .path T ctx
       else if ctx.buffer.isEmpty = true then
         (if ctx.over.isSome = true then PResult.ok { ctx.url with host := some .empty }
          else run base .pathStart T { ctx with url := { ctx.url with host := some .empty } })
       else match hostParser ctx.toAscii ctx.buffer (!ctx.url.isSpecial) with
         | none => fail ctx
         | some h =>
           if ctx.over.isSome = true then
             PResult.ok { ctx.url with host := some (fileHostOf h) }
           else run base .pathStart T
             { ctx with buffer := [], url := { ctx.url with host := some (fileHostOf h) } })
      = (if isWindowsDrive ctx.buffer then run base .path T ctx
        else if ctx.buffer.isEmpty then
          run base .pathStart T { ctx with url := { ctx.url with host := some .empty } }
        else match hostParser ctx.toAscii ctx.buffer (!ctx.url.isSpecial) with
          | none => .failure
          | some h =>
            run base .pathStart T
              { ctx with buffer := [], url := { ctx.url with host := some (fileHostOf h) } }) := by
    simp only [hov, Option.isNone_none, Bool.true_and, Option.isSome_none, Bool.false_eq_true,
      if_false]
    split
    · rfl
    · split
      · rfl
      · cases hostParser ctx.toAscii ctx.buffer (!ctx.url.isSpecial) <;> simp [fail, hov]
  cases T with
  | nil => rw [run, step, if_pos (by simp)]; exact hcommon
  | cons c r =>
    have hd := hT c r rfl
    simp only [fileDelim, isSlashBS, Bool.or_eq_true, beq_iff_eq] at hd
    rw [run, step, if_pos (by rcases hd with ((h | h) | h) | h <;> simp [h])]
    exact hcommon

/-! ## path -/

/-- Windows drive letter の文字は path percent-encode set に入らず、区切りでもない。 -/
theorem drive_chars {B : List Char} (h : isWindowsDrive B = true) (sp : Bool) :
    ∀ c ∈ B, pathSet c = false ∧ isTerminator sp (some c) = false := by
  match B, h with
  | [a, b], h =>
    simp only [isWindowsDrive, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨ha, hb⟩ := h
    have hra : pathSet a = false ∧ isTerminator sp (some a) = false := by
      simp only [isAsciiAlpha, isAsciiUpperAlpha, isAsciiLowerAlpha, Bool.or_eq_true,
        Bool.and_eq_true, decide_eq_true_eq] at ha
      have ha' : (65 ≤ a.toNat ∧ a.toNat ≤ 90) ∨ (97 ≤ a.toNat ∧ a.toNat ≤ 122) := ha
      have key : ∀ ch : Char, (ch.toNat < 65 ∨ (90 < ch.toNat ∧ ch.toNat < 97) ∨ 122 < ch.toNat) →
          (a == ch) = false := by
        intro ch hch; simp only [beq_eq_false_iff_ne]; intro e; subst e; omega
      constructor
      · unfold pathSet querySet c0ControlSet isC0Control
        simp only [key ' ' (by decide), key '"' (by decide), key '#' (by decide), key '<' (by decide),
          key '>' (by decide), key '?' (by decide), key '^' (by decide), key '`' (by decide),
          key '{' (by decide), key '}' (by decide), Bool.or_false, Bool.or_eq_false_iff,
          decide_eq_false_iff_not]
        omega
      · simp only [isTerminator, key '/' (by decide), key '?' (by decide), key '#' (by decide),
          key '\\' (by decide), Bool.or_false, Bool.and_false]
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact hra
    · rcases hb with rfl | rfl <;> cases sp <;> decide

/-- `file` URL の path state から先。 -/
theorem run_path_file (base : Option Url) (Y : List Char) (q f : Option (List Char)) (ctx : PCtx)
    (hs : ctx.url.scheme = "file") (hov : ctx.over = none) (hbuf : ctx.buffer = [])
    (hq0 : ctx.url.query = none) (hf0 : ctx.url.fragment = none) (hpath : ctx.url.path = .list [])
    (hq : '?' ∉ Y) (hh : '#' ∉ Y) (hqh : ∀ x, q = some x → '#' ∉ x) :
    run base .path (Y ++ qfTail q f) ctx
      = .ok { ctx.url with path := .list (resolveSegs true [] (pathSegments true Y)),
                           query := q.map (queryText true), fragment := f.map fragmentText } := by
  have hsp : ctx.url.isSpecial = true := by simp [Url.isSpecial, hs, isSpecialScheme]
  rw [run_path_ref base _ ctx hpath hov hbuf hq0 hf0, splitRef_parts hq hh hqh, hsp, hs]
  rfl

/-- `file` URL の path start state から先。区切りが一つあれば読み飛ばす。 -/
theorem run_pathStart_file (base : Option Url) (pathPart : Option (List Char)) (q f : Option (List Char)) (ctx : PCtx)
    (hs : ctx.url.scheme = "file") (hov : ctx.over = none) (hbuf : ctx.buffer = [])
    (hq0 : ctx.url.query = none) (hf0 : ctx.url.fragment = none) (hpath : ctx.url.path = .list [])
    (hq : ∀ pp, pathPart = some pp → '?' ∉ pp) (hh : ∀ pp, pathPart = some pp → '#' ∉ pp)
    (hqh : ∀ x, q = some x → '#' ∉ x) {d : Char} (hd : isSlashBS d = true) :
    run base .pathStart ((pathPart.map (d :: ·)).getD [] ++ qfTail q f) ctx
      = .ok { ctx.url with
          path := .list (resolveSegs true [] (pathSegments true (pathPart.getD []))),
          query := q.map (queryText true), fragment := f.map fragmentText } := by
  have hsp : ctx.url.isSpecial = true := by simp [Url.isSpecial, hs, isSpecialScheme]
  cases pathPart with
  | none =>
    simp only [Option.map_none, Option.getD_none, List.nil_append]
    rw [run_pathStart_other_sp base _ ctx hsp (fun c r he => by
      rcases qfTail_head q f with h | h | h <;> rw [he] at h <;> simp at h <;> subst h <;> decide)]
    have := run_path_file base [] q f ctx hs hov hbuf hq0 hf0 hpath (by simp) (by simp) hqh
    simpa using this
  | some pp =>
    simp only [Option.map_some, Option.getD_some, List.cons_append]
    rw [run_pathStart_sep_sp base _ ctx hsp hd]
    exact run_path_file base pp q f ctx hs hov hbuf hq0 hf0 hpath (hq pp rfl) (hh pp rfl) hqh

/-! ## 組み立て -/

theorem fileHostOf_eq (h : Host) :
    (if hostSerializer h = "localhost" then Host.empty else h) = fileHostOf h := by
  unfold fileHostOf
  by_cases hl : hostSerializer h = "localhost" <;> simp [hl]

theorem qfTail_not_slash (q f : Option (List Char)) :
    ∀ c r, qfTail q f = c :: r → isSlashBS c = false := by
  intro c r he
  rcases qfTail_head q f with h | h | h <;> rw [he] at h <;> simp at h <;> subst h <;> decide

/-- **`file` URL の分岐**（base 無し）。 -/
theorem branch_file (base : Option Url) (hb : ∀ b, base = some b → b.scheme ≠ "file")
    (t : List Char → Option String) (rest : List Char) :
    run base .file rest { url := { scheme := "file" }, toAscii := t }
      = toResult (specParseFile t rest) := by
  obtain ⟨hdec, hnq, hnh, hqh⟩ := splitRef_decomp rest
  dsimp only [specParseFile]
  generalize (splitRef rest).1 = hier at hdec hnq hnh ⊢
  generalize (splitRef rest).2.1 = q at hdec hqh ⊢
  generalize (splitRef rest).2.2 = f at hdec ⊢
  subst hdec
  have hF : ∀ (Y : List Char), '?' ∉ Y → '#' ∉ Y →
      run base .path (Y ++ qfTail q f)
        { url := { scheme := "file", host := some .empty }, toAscii := t }
      = .ok { scheme := "file", host := some .empty,
              path := .list (resolveSegs true [] (pathSegments true Y)),
              query := q.map (queryText true), fragment := f.map fragmentText } := by
    intro Y hq hh
    exact run_path_file base Y q f _ rfl rfl rfl rfl rfl rfl hq hh hqh
  match hier, hnq, hnh with
  | [], _, _ =>
    rw [List.nil_append, run_file_other base hb _ _ (qfTail_not_slash q f)]
    have := hF [] (by simp) (by simp)
    rw [List.nil_append] at this
    exact this
  | [s1], hq1, hh1 =>
    by_cases hs1 : isSlashBS s1 = true
    · rw [List.singleton_append, run_file_sep base _ _ hs1, run_fileSlash_other base hb _ _ (qfTail_not_slash q f)]
      simp only [hs1, if_true]
      have := hF [] (by simp) (by simp)
      rw [List.nil_append] at this
      exact this
    · rw [run_file_other base hb _ _ (fun c r he => by simp at he; rw [← he.1]; simpa using hs1)]
      simp only [hs1, Bool.false_eq_true, if_false]
      exact hF [s1] hq1 hh1
  | s1 :: s2 :: X, hq1, hh1 =>
    by_cases hs1 : isSlashBS s1 = true
    · by_cases hs2 : isSlashBS s2 = true
      · simp only [hs1, hs2, Bool.and_self, if_true]
        rw [List.cons_append, List.cons_append, run_file_sep base _ _ hs1, run_fileSlash_sep base _ _ hs2]
        have hqX : '?' ∉ X := fun hm => hq1 (by simp [hm])
        have hhX : '#' ∉ X := fun hm => hh1 (by simp [hm])
        have key : ∀ (hs : List Char) (pathPart : Option (List Char)) (d : Char),
            isSlashBS d = true → (∀ c ∈ hs, fileDelim c = false) →
            (∀ pp, pathPart = some pp → '?' ∉ pp ∧ '#' ∉ pp) →
            run base .fileHost (hs ++ ((pathPart.map (d :: ·)).getD [] ++ qfTail q f))
              { url := { scheme := "file", host := some .empty }, toAscii := t }
            = toResult
                (if isWindowsDrive hs then
                  some { scheme := "file", host := some .empty,
                         path := .list (resolveSegs true [] (pathSegments true
                           (hs ++ (pathPart.map (d :: ·)).getD []))),
                         query := q.map (queryText true), fragment := f.map fragmentText }
                else if hs.isEmpty then
                  some { scheme := "file", host := some .empty,
                         path := .list (resolveSegs true [] (pathSegments true (pathPart.getD []))),
                         query := q.map (queryText true), fragment := f.map fragmentText }
                else match hostParser t hs false with
                  | none => none
                  | some h =>
                    some { scheme := "file", host := some (fileHostOf h),
                           path := .list (resolveSegs true [] (pathSegments true (pathPart.getD []))),
                           query := q.map (queryText true), fragment := f.map fragmentText }) := by
          intro hs pathPart d hd hdel hpp
          have hT : ∀ c r, (pathPart.map (d :: ·)).getD [] ++ qfTail q f = c :: r →
              fileDelim c = true := by
            intro c r he
            cases pathPart with
            | none =>
              simp only [Option.map_none, Option.getD_none, List.nil_append] at he
              rcases qfTail_head q f with h | h | h <;> rw [he] at h <;> simp at h <;> subst h <;> decide
            | some pp =>
              simp only [Option.map_some, Option.getD_some, List.cons_append] at he
              simp at he; rw [← he.1]; simp [fileDelim, hd]
          rw [run_fileHost_read base hs _ _ hdel, run_fileHost_end base _ _ rfl hT]
          simp only [List.nil_append]
          by_cases hw : isWindowsDrive hs = true
          · rw [if_pos hw, if_pos hw]
            have hc := run_path_chunk base true hs ((pathPart.map (d :: ·)).getD [] ++ qfTail q f)
              { url := { scheme := "file", host := some .empty }, toAscii := t } rfl rfl
              (drive_chars hw true)
            simp only [List.nil_append] at hc
            rw [← hc, ← List.append_assoc]
            have hdq : d ≠ '?' := by intro e; subst e; simp [isSlashBS] at hd
            have hdh : d ≠ '#' := by intro e; subst e; simp [isSlashBS] at hd
            have hext : '?' ∉ (pathPart.map (d :: ·)).getD [] ∧ '#' ∉ (pathPart.map (d :: ·)).getD [] := by
              cases pathPart with
              | none => simp
              | some pp =>
                simp only [Option.map_some, Option.getD_some, List.mem_cons, not_or]
                exact ⟨⟨Ne.symm hdq, (hpp pp rfl).1⟩, ⟨Ne.symm hdh, (hpp pp rfl).2⟩⟩
            have hhq : '?' ∉ hs := fun hm => by have := hdel _ hm; simp [fileDelim] at this
            have hhh : '#' ∉ hs := fun hm => by have := hdel _ hm; simp [fileDelim] at this
            exact hF _ (by simp [List.mem_append, hhq, hext.1]) (by simp [List.mem_append, hhh, hext.2])
          · rw [if_neg hw, if_neg hw]
            by_cases he : hs.isEmpty = true
            · rw [if_pos he, if_pos he]
              have : hs = [] := by simpa using he
              subst this
              exact run_pathStart_file base pathPart q f _ rfl rfl rfl rfl rfl rfl
                (fun pp h => (hpp pp h).1) (fun pp h => (hpp pp h).2) hqh hd
            · rw [if_neg he, if_neg he]
              simp only [show ({ scheme := "file", host := some .empty } : Url).isSpecial = true by decide,
                Bool.not_true]
              cases hostParser t hs false with
              | none => rfl
              | some h =>
                exact run_pathStart_file base pathPart q f _ rfl rfl rfl rfl rfl rfl
                  (fun pp h => (hpp pp h).1) (fun pp h => (hpp pp h).2) hqh hd
        have hdelOf : ∀ {hs : List Char}, (∀ c ∈ hs, isSlashBS c = false) → '?' ∉ hs → '#' ∉ hs →
            ∀ c ∈ hs, fileDelim c = false := by
          intro hs h1 h2 h3 c hc
          have : c ≠ '?' := fun e => h2 (e ▸ hc)
          have : c ≠ '#' := fun e => h3 (e ▸ hc)
          simp [fileDelim, h1 c hc, *]
        rcases first_occurrence_by isSlashBS X with hns | ⟨a, d, pp, rfl, hd, ha⟩
        · rw [splitFirstBy_none _ _ hns]
          simp only [fileHostOf_eq]
          have := key X none '/' (by decide) (hdelOf hns hqX hhX) (by simp)
          simp only [Option.map_none, Option.getD_none, List.append_nil, List.nil_append] at this
          exact this
        · rw [splitFirstBy_append _ _ _ _ ha hd]
          simp only [fileHostOf_eq]
          have := key a (some pp) d hd (hdelOf ha (fun hm => hqX (by simp [hm]))
            (fun hm => hhX (by simp [hm])))
            (fun pp' h => by
              cases h; exact ⟨fun hm => hqX (by simp [hm]), fun hm => hhX (by simp [hm])⟩)
          simp only [Option.map_some, Option.getD_some, List.cons_append] at this
          simp only [Option.getD_some, List.cons_append, List.append_assoc]
          exact this
      · rw [List.cons_append, run_file_sep base _ _ hs1,
          run_fileSlash_other base hb _ _ (fun c r he => by simp at he; rw [← he.1]; simpa using hs2)]
        simp only [hs1, hs2, Bool.and_false, Bool.false_eq_true, if_false, if_true]
        exact hF (s2 :: X) (fun hm => hq1 (by simp_all)) (fun hm => hh1 (by simp_all))
    · rw [run_file_other base hb _ _ (fun c r he => by simp at he; rw [← he.1]; simpa using hs1)]
      simp only [hs1, Bool.false_and, Bool.false_eq_true, if_false]
      exact hF (s1 :: s2 :: X) hq1 hh1

/-- scheme state が `file` を読み終えると file state へ。 -/
theorem run_schemeStart_file (base : Option Url) (t : List Char → Option String)
    {a : Char} {pre rest : List Char} (ha : isAsciiAlpha a = true)
    (hpre : ∀ c ∈ pre, schemeChar c = true)
    (hf : String.ofList ((a :: pre).map asciiLowerChar) = "file") :
    run base .schemeStart (a :: (pre ++ ':' :: rest)) { url := {}, toAscii := t }
      = run base .file rest { url := { scheme := "file" }, toAscii := t } := by
  rw [run, step, if_pos ha, run_scheme_prefix base pre _ _ hpre]
  rw [run, step]
  have hcol : (isAsciiAlphanumeric ':' || ':' == '+' || ':' == '-' || ':' == '.') = false := by
    decide
  have hf' : String.ofList (asciiLowerChar a :: pre.map asciiLowerChar) = "file" := by simpa using hf
  simp only [asciiLowercase, List.nil_append, String.toList_ofList, List.map_cons, List.map_nil,
    List.cons_append, hcol, Bool.false_eq_true, if_false, beq_self_eq_true, if_true,
    Option.isSome_none, hf']

/--
**basic URL parser は、base 無しの全入力について関数的な仕様と一致する。** 入力に制限は無い。

special でない scheme（`basicUrlParse_eq_specParse`）、special な scheme（`run_spec_special`）、
`file`（`branch_file`）、scheme の無い入力（失敗）の四つをまとめたものである。
-/
theorem basicUrlParse_eq_specParse_all (t : List Char → Option String) (input : String) :
    basicUrlParse input none t = specParse t (preprocess input) := by
  cases hs : splitScheme (preprocess input) with
  | none => exact basicUrlParse_eq_specParse t input (fun _ _ he => by rw [hs] at he; cases he)
  | some p =>
    obtain ⟨sc, rest⟩ := p
    by_cases hf : sc = "file"
    · subst hf
      obtain ⟨a, pre, he, ha, hpre, hsc⟩ := splitScheme_some hs
      unfold basicUrlParse
      rw [he, run_schemeStart_file none t ha hpre hsc.symm, branch_file none (by simp) t, ← he]
      simp only [specParse, hs, if_true]
      cases specParseFile t rest <;> rfl
    · exact basicUrlParse_eq_specParse_noFile t input (fun s r he => by
        rw [hs] at he; cases he; exact hf)

end Url.Spec
