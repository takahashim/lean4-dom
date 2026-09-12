import Url.Invariant

namespace Url

set_option linter.unusedSimpArgs false

-- 20 の定理は `step_valid` が `cases st` で並べるので signature を揃えてある。
-- `hlen` を使わない state が四つあるが、そこだけ名前を変えると揃わなくなる。
set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/--
帰納法の仮定。測度は `(stateRank st, input.length)` の辞書式である。

**辞書式を一つの自然数に潰すことはできない。** authority state が
「pointer を buffer の長さだけ戻す」（仕様 §4.4 authority state の最後）ので、
そこでは入力が伸びる。rank が先に減るから停止するのであって、長さは減らない。
-/
def RunIH (base : Option Url) (r n : Nat) : Prop :=
  ∀ (st : PState) (input : List Char) (ctx : PCtx) (u : Url),
    run base st input ctx = .ok u →
    (stateRank st < r ∨ (stateRank st = r ∧ input.length < n)) →
    PInv base st ctx → ValidUrl u

/-!
### `userinfoStep` 一歩分

`userinfoFold_*` は `foldl` の形にしか当たらない。`step` が buffer の前に
literal を足す case では simp が `List.foldl_cons` で先頭を剥がしてしまい、
一歩分の適用が残る。そこを閉じる。
-/

@[simp] theorem userinfoStep_scheme (p : Url × Bool) (c : Char) :
    (userinfoStep p c).1.scheme = p.1.scheme := by
  unfold userinfoStep; split
  · rfl
  · split <;> rfl

@[simp] theorem userinfoStep_host (p : Url × Bool) (c : Char) :
    (userinfoStep p c).1.host = p.1.host := by
  unfold userinfoStep; split
  · rfl
  · split <;> rfl

@[simp] theorem userinfoStep_port (p : Url × Bool) (c : Char) :
    (userinfoStep p c).1.port = p.1.port := by
  unfold userinfoStep; split
  · rfl
  · split <;> rfl

@[simp] theorem userinfoStep_path (p : Url × Bool) (c : Char) :
    (userinfoStep p c).1.path = p.1.path := by
  unfold userinfoStep; split
  · rfl
  · split <;> rfl

@[simp] theorem userinfoStep_isSpecial (p : Url × Bool) (c : Char) :
    (userinfoStep p c).1.isSpecial = p.1.isSpecial := by
  simp [Url.isSpecial]

@[simp] theorem userinfoStep_hasOpaquePath (p : Url × Bool) (c : Char) :
    (userinfoStep p c).1.hasOpaquePath = p.1.hasOpaquePath := by
  simp [Url.hasOpaquePath]

local macro "url_simp_state" : tactic =>
  `(tactic| simp_all (config := { maxDischargeDepth := 1 }) +zetaDelta
      [mayOpaque, mayCred, usesBasePath, freshHost, freshCredPort, fail])

local macro "url_simp_url" : tactic =>
  `(tactic| simp_all (config := { maxDischargeDepth := 1 }) +zetaDelta
      [mayOpaque, mayCred, usesBasePath, freshHost, freshCredPort, fail,
       Url.isSpecial, Url.hasOpaquePath, Url.includesCredentials])

local macro "url_simp_scheme" : tactic =>
  `(tactic| simp_all (config := { maxDischargeDepth := 1 }) +zetaDelta
      [mayOpaque, mayCred, usesBasePath, freshHost, freshCredPort, fail,
       Url.isSpecial, Url.hasOpaquePath, Url.includesCredentials, isSpecialScheme, defaultPort])

local macro "url_close " ih:ident hinv:ident hlen:ident u:ident heq:ident : tactic =>
  `(tactic| first
    -- 失敗の枝。`fail` や `schemeOverride` を開くと `heq` が矛盾する。
    | (url_simp_state; done)
    | (url_simp_url; done)
    | (url_simp_scheme; done)
    -- 終端。`.ok X` を返すので `ValidUrl X` を示す。
    | (injection $heq with hu
       subst hu
       first
         | exact ($hinv).valid (by decide)
         | (url_simp_state; done) | (url_simp_url; done) | (url_simp_scheme; done)
         | (refine valid_of_inv ?_ ?_ ?_ ?_ ?_ ?_ <;>
             first | (url_simp_state; done) | (url_simp_url; done) | (url_simp_scheme; done)))
    -- port state から path start state への移送。`portDone` を挟むので専用の補題が要る。
    | (refine $ih _ _ _ $u $heq ?_ (($hinv).portStep ?_)
       · first
         | exact Or.inl (by decide)
         | exact Or.inr ⟨by decide, by simp at $hlen:ident ⊢; omega⟩
       · first | assumption | (url_simp_state; done) | (url_simp_scheme; done))
    -- 再帰。測度が減ることと `PInv` が保たれることを示す。
    | (refine $ih _ _ _ $u $heq ?_ ?_
       · first
         | exact Or.inl (by decide)
         | exact Or.inr ⟨by decide, by simp at $hlen:ident ⊢; omega⟩
         | exact Or.inr ⟨by decide, by simp [stateRank] at *; omega⟩
         | (simp only [stateRank] at *; omega)
       · constructor <;>
           first | (url_simp_state; done) | (url_simp_url; done) | (url_simp_scheme; done)))

theorem step_schemeStart_valid (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hlen : rest.length + (if c.isSome then 1 else 0) = input.length)
    (ih : RunIH base (stateRank .schemeStart) input.length) (hinv : PInv base .schemeStart ctx) :
    ∀ u, step base .schemeStart c rest input ctx = .ok u → ValidUrl u := by
  intro u heq
  have ⟨hov, hbv, hbp, hsp, hnp, hoc, hopo, hoh, hos, hcs, hph, hsn, hfs⟩ := hinv
  have bsp := fun b (hb : base = some b) => (hinv.baseValid b hb).specialHasList
  have bnc := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoCredentials
  have bnp := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoPort
  have boc := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoCredentials
  have bop := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoPort
  have boh := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoHost
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals url_close ih hinv hlen u heq

theorem step_scheme_valid (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hlen : rest.length + (if c.isSome then 1 else 0) = input.length)
    (ih : RunIH base (stateRank .scheme) input.length) (hinv : PInv base .scheme ctx) :
    ∀ u, step base .scheme c rest input ctx = .ok u → ValidUrl u := by
  intro u heq
  have ⟨hov, hbv, hbp, hsp, hnp, hoc, hopo, hoh, hos, hcs, hph, hsn, hfs⟩ := hinv
  have bsp := fun b (hb : base = some b) => (hinv.baseValid b hb).specialHasList
  have bnc := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoCredentials
  have bnp := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoPort
  have boc := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoCredentials
  have bop := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoPort
  have boh := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoHost
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals url_close ih hinv hlen u heq

theorem step_noScheme_valid (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hlen : rest.length + (if c.isSome then 1 else 0) = input.length)
    (ih : RunIH base (stateRank .noScheme) input.length) (hinv : PInv base .noScheme ctx) :
    ∀ u, step base .noScheme c rest input ctx = .ok u → ValidUrl u := by
  intro u heq
  have ⟨hov, hbv, hbp, hsp, hnp, hoc, hopo, hoh, hos, hcs, hph, hsn, hfs⟩ := hinv
  have bsp := fun b (hb : base = some b) => (hinv.baseValid b hb).specialHasList
  have bnc := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoCredentials
  have bnp := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoPort
  have boc := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoCredentials
  have bop := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoPort
  have boh := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoHost
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals url_close ih hinv hlen u heq

theorem step_specialRelativeOrAuthority_valid (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hlen : rest.length + (if c.isSome then 1 else 0) = input.length)
    (ih : RunIH base (stateRank .specialRelativeOrAuthority) input.length) (hinv : PInv base .specialRelativeOrAuthority ctx) :
    ∀ u, step base .specialRelativeOrAuthority c rest input ctx = .ok u → ValidUrl u := by
  intro u heq
  have ⟨hov, hbv, hbp, hsp, hnp, hoc, hopo, hoh, hos, hcs, hph, hsn, hfs⟩ := hinv
  have bsp := fun b (hb : base = some b) => (hinv.baseValid b hb).specialHasList
  have bnc := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoCredentials
  have bnp := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoPort
  have boc := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoCredentials
  have bop := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoPort
  have boh := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoHost
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals url_close ih hinv hlen u heq

theorem step_pathOrAuthority_valid (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hlen : rest.length + (if c.isSome then 1 else 0) = input.length)
    (ih : RunIH base (stateRank .pathOrAuthority) input.length) (hinv : PInv base .pathOrAuthority ctx) :
    ∀ u, step base .pathOrAuthority c rest input ctx = .ok u → ValidUrl u := by
  intro u heq
  have ⟨hov, hbv, hbp, hsp, hnp, hoc, hopo, hoh, hos, hcs, hph, hsn, hfs⟩ := hinv
  have bsp := fun b (hb : base = some b) => (hinv.baseValid b hb).specialHasList
  have bnc := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoCredentials
  have bnp := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoPort
  have boc := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoCredentials
  have bop := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoPort
  have boh := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoHost
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals url_close ih hinv hlen u heq

theorem step_relative_valid (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hlen : rest.length + (if c.isSome then 1 else 0) = input.length)
    (ih : RunIH base (stateRank .relative) input.length) (hinv : PInv base .relative ctx) :
    ∀ u, step base .relative c rest input ctx = .ok u → ValidUrl u := by
  intro u heq
  have ⟨hov, hbv, hbp, hsp, hnp, hoc, hopo, hoh, hos, hcs, hph, hsn, hfs⟩ := hinv
  have bsp := fun b (hb : base = some b) => (hinv.baseValid b hb).specialHasList
  have bnc := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoCredentials
  have bnp := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoPort
  have boc := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoCredentials
  have bop := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoPort
  have boh := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoHost
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals url_close ih hinv hlen u heq

theorem step_relativeSlash_valid (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hlen : rest.length + (if c.isSome then 1 else 0) = input.length)
    (ih : RunIH base (stateRank .relativeSlash) input.length) (hinv : PInv base .relativeSlash ctx) :
    ∀ u, step base .relativeSlash c rest input ctx = .ok u → ValidUrl u := by
  intro u heq
  have ⟨hov, hbv, hbp, hsp, hnp, hoc, hopo, hoh, hos, hcs, hph, hsn, hfs⟩ := hinv
  have bsp := fun b (hb : base = some b) => (hinv.baseValid b hb).specialHasList
  have bnc := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoCredentials
  have bnp := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoPort
  have boc := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoCredentials
  have bop := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoPort
  have boh := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoHost
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals url_close ih hinv hlen u heq

theorem step_specialAuthoritySlashes_valid (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hlen : rest.length + (if c.isSome then 1 else 0) = input.length)
    (ih : RunIH base (stateRank .specialAuthoritySlashes) input.length) (hinv : PInv base .specialAuthoritySlashes ctx) :
    ∀ u, step base .specialAuthoritySlashes c rest input ctx = .ok u → ValidUrl u := by
  intro u heq
  have ⟨hov, hbv, hbp, hsp, hnp, hoc, hopo, hoh, hos, hcs, hph, hsn, hfs⟩ := hinv
  have bsp := fun b (hb : base = some b) => (hinv.baseValid b hb).specialHasList
  have bnc := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoCredentials
  have bnp := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoPort
  have boc := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoCredentials
  have bop := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoPort
  have boh := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoHost
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals url_close ih hinv hlen u heq

theorem step_specialAuthorityIgnoreSlashes_valid (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hlen : rest.length + (if c.isSome then 1 else 0) = input.length)
    (ih : RunIH base (stateRank .specialAuthorityIgnoreSlashes) input.length) (hinv : PInv base .specialAuthorityIgnoreSlashes ctx) :
    ∀ u, step base .specialAuthorityIgnoreSlashes c rest input ctx = .ok u → ValidUrl u := by
  intro u heq
  have ⟨hov, hbv, hbp, hsp, hnp, hoc, hopo, hoh, hos, hcs, hph, hsn, hfs⟩ := hinv
  have bsp := fun b (hb : base = some b) => (hinv.baseValid b hb).specialHasList
  have bnc := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoCredentials
  have bnp := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoPort
  have boc := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoCredentials
  have bop := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoPort
  have boh := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoHost
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals url_close ih hinv hlen u heq

theorem step_authority_valid (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hlen : rest.length + (if c.isSome then 1 else 0) = input.length)
    (ih : RunIH base (stateRank .authority) input.length) (hinv : PInv base .authority ctx) :
    ∀ u, step base .authority c rest input ctx = .ok u → ValidUrl u := by
  intro u heq
  have ⟨hov, hbv, hbp, hsp, hnp, hoc, hopo, hoh, hos, hcs, hph, hsn, hfs⟩ := hinv
  have bsp := fun b (hb : base = some b) => (hinv.baseValid b hb).specialHasList
  have bnc := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoCredentials
  have bnp := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoPort
  have boc := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoCredentials
  have bop := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoPort
  have boh := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoHost
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals url_close ih hinv hlen u heq

theorem step_host_valid (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hlen : rest.length + (if c.isSome then 1 else 0) = input.length)
    (ih : RunIH base (stateRank .host) input.length) (hinv : PInv base .host ctx) :
    ∀ u, step base .host c rest input ctx = .ok u → ValidUrl u := by
  intro u heq
  have ⟨hov, hbv, hbp, hsp, hnp, hoc, hopo, hoh, hos, hcs, hph, hsn, hfs⟩ := hinv
  have bsp := fun b (hb : base = some b) => (hinv.baseValid b hb).specialHasList
  have bnc := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoCredentials
  have bnp := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoPort
  have boc := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoCredentials
  have bop := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoPort
  have boh := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoHost
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals url_close ih hinv hlen u heq

theorem step_port_valid (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hlen : rest.length + (if c.isSome then 1 else 0) = input.length)
    (ih : RunIH base (stateRank .port) input.length) (hinv : PInv base .port ctx) :
    ∀ u, step base .port c rest input ctx = .ok u → ValidUrl u := by
  intro u heq
  have ⟨hov, hbv, hbp, hsp, hnp, hoc, hopo, hoh, hos, hcs, hph, hsn, hfs⟩ := hinv
  have bsp := fun b (hb : base = some b) => (hinv.baseValid b hb).specialHasList
  have bnc := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoCredentials
  have bnp := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoPort
  have boc := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoCredentials
  have bop := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoPort
  have boh := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoHost
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals url_close ih hinv hlen u heq

theorem step_file_valid (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hlen : rest.length + (if c.isSome then 1 else 0) = input.length)
    (ih : RunIH base (stateRank .file) input.length) (hinv : PInv base .file ctx) :
    ∀ u, step base .file c rest input ctx = .ok u → ValidUrl u := by
  intro u heq
  have ⟨hov, hbv, hbp, hsp, hnp, hoc, hopo, hoh, hos, hcs, hph, hsn, hfs⟩ := hinv
  have bsp := fun b (hb : base = some b) => (hinv.baseValid b hb).specialHasList
  have bnc := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoCredentials
  have bnp := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoPort
  have boc := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoCredentials
  have bop := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoPort
  have boh := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoHost
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals url_close ih hinv hlen u heq

theorem step_fileSlash_valid (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hlen : rest.length + (if c.isSome then 1 else 0) = input.length)
    (ih : RunIH base (stateRank .fileSlash) input.length) (hinv : PInv base .fileSlash ctx) :
    ∀ u, step base .fileSlash c rest input ctx = .ok u → ValidUrl u := by
  intro u heq
  have ⟨hov, hbv, hbp, hsp, hnp, hoc, hopo, hoh, hos, hcs, hph, hsn, hfs⟩ := hinv
  have bsp := fun b (hb : base = some b) => (hinv.baseValid b hb).specialHasList
  have bnc := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoCredentials
  have bnp := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoPort
  have boc := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoCredentials
  have bop := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoPort
  have boh := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoHost
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals url_close ih hinv hlen u heq

theorem step_fileHost_valid (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hlen : rest.length + (if c.isSome then 1 else 0) = input.length)
    (ih : RunIH base (stateRank .fileHost) input.length) (hinv : PInv base .fileHost ctx) :
    ∀ u, step base .fileHost c rest input ctx = .ok u → ValidUrl u := by
  intro u heq
  have ⟨hov, hbv, hbp, hsp, hnp, hoc, hopo, hoh, hos, hcs, hph, hsn, hfs⟩ := hinv
  have bsp := fun b (hb : base = some b) => (hinv.baseValid b hb).specialHasList
  have bnc := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoCredentials
  have bnp := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoPort
  have boc := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoCredentials
  have bop := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoPort
  have boh := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoHost
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals url_close ih hinv hlen u heq

theorem step_pathStart_valid (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hlen : rest.length + (if c.isSome then 1 else 0) = input.length)
    (ih : RunIH base (stateRank .pathStart) input.length) (hinv : PInv base .pathStart ctx) :
    ∀ u, step base .pathStart c rest input ctx = .ok u → ValidUrl u := by
  intro u heq
  have ⟨hov, hbv, hbp, hsp, hnp, hoc, hopo, hoh, hos, hcs, hph, hsn, hfs⟩ := hinv
  have bsp := fun b (hb : base = some b) => (hinv.baseValid b hb).specialHasList
  have bnc := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoCredentials
  have bnp := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoPort
  have boc := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoCredentials
  have bop := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoPort
  have boh := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoHost
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals url_close ih hinv hlen u heq

theorem step_path_valid (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hlen : rest.length + (if c.isSome then 1 else 0) = input.length)
    (ih : RunIH base (stateRank .path) input.length) (hinv : PInv base .path ctx) :
    ∀ u, step base .path c rest input ctx = .ok u → ValidUrl u := by
  intro u heq
  have ⟨hov, hbv, hbp, hsp, hnp, hoc, hopo, hoh, hos, hcs, hph, hsn, hfs⟩ := hinv
  have bsp := fun b (hb : base = some b) => (hinv.baseValid b hb).specialHasList
  have bnc := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoCredentials
  have bnp := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoPort
  have boc := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoCredentials
  have bop := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoPort
  have boh := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoHost
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals url_close ih hinv hlen u heq

theorem step_opaquePath_valid (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hlen : rest.length + (if c.isSome then 1 else 0) = input.length)
    (ih : RunIH base (stateRank .opaquePath) input.length) (hinv : PInv base .opaquePath ctx) :
    ∀ u, step base .opaquePath c rest input ctx = .ok u → ValidUrl u := by
  intro u heq
  have ⟨hov, hbv, hbp, hsp, hnp, hoc, hopo, hoh, hos, hcs, hph, hsn, hfs⟩ := hinv
  have bsp := fun b (hb : base = some b) => (hinv.baseValid b hb).specialHasList
  have bnc := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoCredentials
  have bnp := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoPort
  have boc := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoCredentials
  have bop := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoPort
  have boh := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoHost
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals url_close ih hinv hlen u heq

theorem step_query_valid (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hlen : rest.length + (if c.isSome then 1 else 0) = input.length)
    (ih : RunIH base (stateRank .query) input.length) (hinv : PInv base .query ctx) :
    ∀ u, step base .query c rest input ctx = .ok u → ValidUrl u := by
  intro u heq
  have ⟨hov, hbv, hbp, hsp, hnp, hoc, hopo, hoh, hos, hcs, hph, hsn, hfs⟩ := hinv
  have bsp := fun b (hb : base = some b) => (hinv.baseValid b hb).specialHasList
  have bnc := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoCredentials
  have bnp := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoPort
  have boc := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoCredentials
  have bop := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoPort
  have boh := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoHost
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals url_close ih hinv hlen u heq

theorem step_fragment_valid (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hlen : rest.length + (if c.isSome then 1 else 0) = input.length)
    (ih : RunIH base (stateRank .fragment) input.length) (hinv : PInv base .fragment ctx) :
    ∀ u, step base .fragment c rest input ctx = .ok u → ValidUrl u := by
  intro u heq
  have ⟨hov, hbv, hbp, hsp, hnp, hoc, hopo, hoh, hos, hcs, hph, hsn, hfs⟩ := hinv
  have bsp := fun b (hb : base = some b) => (hinv.baseValid b hb).specialHasList
  have bnc := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoCredentials
  have bnp := fun b (hb : base = some b) => (hinv.baseValid b hb).nullHostNoPort
  have boc := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoCredentials
  have bop := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoPort
  have boh := fun b (hb : base = some b) => (hinv.baseValid b hb).opaqueNoHost
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals url_close ih hinv hlen u heq


/-! ## 組み上げ -/

/-- **`step` の一歩は `PInv` を保つ。** state ごとの定理を並べるだけ。 -/
theorem step_valid (base : Option Url) (st : PState) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hlen : rest.length + (if c.isSome then 1 else 0) = input.length)
    (ih : RunIH base (stateRank st) input.length) (hinv : PInv base st ctx) :
    ∀ u, step base st c rest input ctx = .ok u → ValidUrl u := by
  cases st
  · exact step_schemeStart_valid base c rest input ctx hlen ih hinv
  · exact step_scheme_valid base c rest input ctx hlen ih hinv
  · exact step_noScheme_valid base c rest input ctx hlen ih hinv
  · exact step_specialRelativeOrAuthority_valid base c rest input ctx hlen ih hinv
  · exact step_pathOrAuthority_valid base c rest input ctx hlen ih hinv
  · exact step_relative_valid base c rest input ctx hlen ih hinv
  · exact step_relativeSlash_valid base c rest input ctx hlen ih hinv
  · exact step_specialAuthoritySlashes_valid base c rest input ctx hlen ih hinv
  · exact step_specialAuthorityIgnoreSlashes_valid base c rest input ctx hlen ih hinv
  · exact step_authority_valid base c rest input ctx hlen ih hinv
  · exact step_host_valid base c rest input ctx hlen ih hinv
  · exact step_port_valid base c rest input ctx hlen ih hinv
  · exact step_file_valid base c rest input ctx hlen ih hinv
  · exact step_fileSlash_valid base c rest input ctx hlen ih hinv
  · exact step_fileHost_valid base c rest input ctx hlen ih hinv
  · exact step_pathStart_valid base c rest input ctx hlen ih hinv
  · exact step_path_valid base c rest input ctx hlen ih hinv
  · exact step_opaquePath_valid base c rest input ctx hlen ih hinv
  · exact step_query_valid base c rest input ctx hlen ih hinv
  · exact step_fragment_valid base c rest input ctx hlen ih hinv

/--
**state machine は `PInv` を保つ。**

`(stateRank st, input.length)` の辞書式についての帰納法。
rank について強い帰納法を回し、その中で長さについて強い帰納法を回す。
-/
theorem run_valid (base : Option Url) : ∀ (st : PState) (input : List Char) (ctx : PCtx),
    PInv base st ctx → ∀ u, run base st input ctx = .ok u → ValidUrl u := by
  have H : ∀ r n (st : PState) (input : List Char), stateRank st = r → input.length = n →
      ∀ ctx, PInv base st ctx → ∀ u, run base st input ctx = .ok u → ValidUrl u := by
    intro r
    induction r using Nat.strongRecOn with
    | _ r ihr =>
      intro n
      induction n using Nat.strongRecOn with
      | _ n ihn =>
        intro st input hr hn ctx hinv u heq
        have ih : RunIH base (stateRank st) input.length := by
          intro st' input' ctx' u' heq' hlt hinv'
          rcases hlt with h | ⟨he, hl⟩
          · exact ihr (stateRank st') (hr ▸ h) input'.length st' input' rfl rfl ctx' hinv' u' heq'
          · exact ihn input'.length (hn ▸ hl) st' input' (hr ▸ he) rfl ctx' hinv' u' heq'
        cases input with
        | nil =>
          rw [run.eq_def] at heq
          exact step_valid base st none [] [] ctx (by simp) ih hinv u heq
        | cons ch t =>
          rw [run.eq_def] at heq
          exact step_valid base st (some ch) t (ch :: t) ctx (by simp) ih hinv u heq
  intro st input ctx
  exact H _ _ st input rfl rfl ctx

/-- **basic URL parser は `ValidUrl` を保つ。** -/
theorem basicUrlParse_valid {input : String} {base : Option Url}
    {toAscii : List Char → Option String}
    (hb : ∀ b, base = some b → ValidUrl b) {u : Url}
    (h : basicUrlParse input base toAscii = some u) : ValidUrl u :=
  basicUrlParse_valid_of_step (fun b st i c hi u' he => run_valid b st i c hi u' he) hb h

/-- `URL(url, base)` の入口についても同じ。base も parse で作るので妥当である。 -/
theorem parseUrl_valid {input : String} {base : Option String}
    {toAscii : List Char → Option String} {u : Url}
    (h : parseUrl input base toAscii = some u) : ValidUrl u := by
  unfold parseUrl at h
  split at h
  · exact basicUrlParse_valid (fun b hb => absurd hb (by simp)) h
  · split at h
    · simp at h
    · next bu hbu =>
      refine basicUrlParse_valid (fun b hb => ?_) h
      rw [← Option.some.inj hb]
      exact basicUrlParse_valid (fun b' hb' => absurd hb' (by simp)) hbu

end Url
