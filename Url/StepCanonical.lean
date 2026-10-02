import Url.CanonicalParts

/-!
# `CInv` の帰納段

`Url/StepValid.lean` と同じ組み方で、state ごとに独立した定理を立てる。
違いは二つある。

* `CInv` は残りの入力を見るので、`step` が受け取る `c` と `rest` と `input` の関係
  （`input` は `c :: rest`、EOF なら空）を仮定に持つ。
* 終端（`.ok X` を返す枝）は「`X` を持って fragment state の EOF にいる」と見なし、
  `CInv` を組んで `CInv.canonical` に渡す（`canonical_of_frag`）。
  終端ごとに `canonicalUrl` の成分を並べ直さずに済む。

各 state の定理は `step` を split して、枝ごとに `cs_close` で閉じる。
`cs_close` は失敗の枝を捨て、終端なら上の形に、再帰なら測度と次の `CInv` に落とし、
`CInv` は field ごとに `cs_field` で閉じる。自動化に任せにくい遷移には二つの口がある。

* field 用の手（`cs_close` の一つ目の括弧）。host parser の出力や userinfo の畳み込みなど、
  split で得た仮定を名指しで使うもの。
* `CInv` 全体を作る補題（二つ目の括弧）。port state の `CInv.portStep`、opaque path state の
  `CInv.opaqueAppend` 系、path state の `CInv.path*` がそれで、`pathStepUrl` や
  `appendOpaque` を挟む遷移を simp に任せないためにある。

## 速さについて

`assumption` は reducible な透明度に限っている（`with_reducible assumption`）。
既定の透明度だと、型の合わない仮定とも `canonicalUrl` のような大きな Bool 関数を
展開して比べにいき、一つの補題に数分かかる。そのかわり、仮定と goal の state の述語は
先に畳んで形を揃えておく（`cs_norm`）。
-/

namespace Url

open Infra

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- `step` の `rest` は `input` から一文字落としたものなので、末尾は変わらない。 -/
theorem rest_getLast {c : Cp} {rest input : List Char} {d : Char} (hin : input = cpList c rest)
    (hrn : c = none → rest = []) (h : input.getLast? ≠ some d) : rest.getLast? ≠ some d := by
  cases c with
  | none => rw [hrn rfl]; simp
  | some ch => subst hin; exact getLast?_cons_ne h

/-- 帰納法の仮定。測度は `StepValid.lean` の `RunIH` と同じ。 -/
def CRunIH (t : List Char → Option String) (base : Option Url) (r n : Nat) : Prop :=
  ∀ (st : PState) (input : List Char) (ctx : PCtx) (u : Url),
    run base st input ctx = .ok u →
    (stateRank st < r ∨ (stateRank st = r ∧ input.length < n)) →
    CInv t base st input ctx → canonicalUrl u t = true

/-- fragment state の EOF にいると見なせる record は canonical である。 -/
theorem canonical_of_frag {t : List Char → Option String} {base : Option Url} {ctx : PCtx} {X : Url}
    (h : CInv t base .fragment [] { ctx with url := X, buffer := [] }) :
    canonicalUrl X t = true := by
  have h1 : hostOpen .fragment = false := rfl
  have h2 : schemeSet .fragment = true := rfl
  have h3 : termState .fragment = true := rfl
  have := CInv.canonical h h1 (fun _ => rfl) h2 (h.termNonEmpty h3)
  simpa using this

/-- `canonical_of_frag` の base を帰納法の仮定から決める。split が base を書き換えても使える。 -/
theorem canonical_of_frag' {t : List Char → Option String} {base : Option Url} {r n : Nat}
    (_ : CRunIH t base r n) {ctx : PCtx}
    {X : Url} (h : CInv t base .fragment [] { ctx with url := X, buffer := [] }) :
    canonicalUrl X t = true :=
  canonical_of_frag h

local macro "cs_simp" : tactic =>
  `(tactic| simp_all (config := { maxDischargeDepth := 1 }) +zetaDelta
      [earlyState, hostOpen, pathFresh, schemeSet, emptyBuf, termState, inputEndState, hostSet,
       freshHost, freshPort, freshCred, notFileState, usesBasePath, fileState, fail, cpList,
       Url.isSpecial, Url.includesCredentials, List.head?_eq_some_iff,
       pathCanon_shortenPath, pathCanon_appendSegment, pathCanon_pathStepUrl,
       pathCanon_fileBasePath, pathCanon_fileSlashDrive,
       driveOk_shortenPath, driveOk_pathStepUrl, driveOk_fileBasePath, driveOk_fileSlashDrive,
       pathStepUrl_ne_nil, appendSegment_ne_nil, isSpecialScheme_file])

/-- scheme を具体的な文字列として見る必要があるとき。 -/
local macro "cs_simp2" : tactic =>
  `(tactic| simp_all (config := { maxDischargeDepth := 1 }) +zetaDelta
      [earlyState, hostOpen, pathFresh, schemeSet, emptyBuf, termState, inputEndState, hostSet,
       freshHost, freshPort, freshCred, notFileState, usesBasePath, fileState, fail, cpList,
       Url.isSpecial, Url.includesCredentials, List.head?_eq_some_iff, isSpecialScheme, defaultPort,
       pathCanon_shortenPath, pathCanon_appendSegment, pathCanon_pathStepUrl,
       pathCanon_fileBasePath, pathCanon_fileSlashDrive,
       driveOk_shortenPath, driveOk_pathStepUrl, driveOk_fileBasePath, driveOk_fileSlashDrive,
       pathStepUrl_ne_nil, appendSegment_ne_nil, isSpecialScheme_file])

local macro "cs_base" base:ident hbc:ident hbv:ident : tactic =>
  `(tactic| (
    have bs := fun b (hb : $base = some b) => (canonical_parts ($hbc b hb)).scheme
    have bpo := fun b (hb : $base = some b) => (canonical_parts ($hbc b hb)).port
    have bu := fun b (hb : $base = some b) => (canonical_parts ($hbc b hb)).username
    have bpw := fun b (hb : $base = some b) => (canonical_parts ($hbc b hb)).password
    have bq := fun b (hb : $base = some b) => (canonical_parts ($hbc b hb)).query
    have bf := fun b (hb : $base = some b) => (canonical_parts ($hbc b hb)).fragment
    have bpa := fun b (hb : $base = some b) => (canonical_parts ($hbc b hb)).path
    have btr := fun b (hb : $base = some b) => (canonical_parts ($hbc b hb)).trailing
    have bhp := fun b (hb : $base = some b) => (canonical_parts ($hbc b hb)).hostPath
    have bsp := fun b (hb : $base = some b) => (canonical_parts ($hbc b hb)).specialPath
    have bhi := fun b (hb : $base = some b) => (canonical_parts ($hbc b hb)).hostIdem
    have bnl := fun b (hb : $base = some b) => (canonical_parts ($hbc b hb)).notLocal
    have bdr := fun b (hb : $base = some b) => (canonical_parts ($hbc b hb)).drive
    have bsh := fun b (hb : $base = some b) => (canonical_parts ($hbc b hb)).specialHost
    have bec := fun b (hb : $base = some b) => (canonical_parts ($hbc b hb)).emptyNoCred
    have btn := fun b (hb : $base = some b) => (canonical_parts ($hbc b hb)).pathNil
    have bvl := fun b (hb : $base = some b) => ($hbv b hb).specialHasList
    have bvh := fun b (hb : $base = some b) => ($hbv b hb).opaqueNoHost
    have bvc := fun b (hb : $base = some b) => ($hbv b hb).opaqueNoCredentials
    have bvp := fun b (hb : $base = some b) => ($hbv b hb).opaqueNoPort))

/-- state の述語と record の更新を畳む。仮定と goal の形を揃えて `assumption` を安くする。 -/
local macro "cs_norm" : tactic =>
  `(tactic| try simp only [earlyState, hostOpen, pathFresh, schemeSet, emptyBuf, termState,
      inputEndState, hostSet, freshHost, freshPort, freshCred, notFileState, usesBasePath, fileState,
      Url.isSpecial, Url.includesCredentials, Bool.false_eq_true, false_implies, true_implies,
      implies_true, reduceCtorEq, forall_const, eq_self_iff_true] at *)

local macro "cs_norm_goal" : tactic =>
  `(tactic| simp only [earlyState, hostOpen, pathFresh, schemeSet, emptyBuf, termState,
      inputEndState, hostSet, freshHost, freshPort, freshCred, notFileState, usesBasePath, fileState,
      Url.isSpecial, Url.includesCredentials, Bool.false_eq_true, false_implies, true_implies,
      implies_true, reduceCtorEq, forall_const, eq_self_iff_true])

/--
field 一つを閉じる。安い順に試す。

* 前提が state の等式や述語で、新しい state では偽になるもの（`cases` で消える）。
* 元の field がそのまま使えるもの。`assumption` は reducible に限る。
  既定の透明度だと `canonicalUrl` のような大きな Bool 関数を展開しにいって遅い。
* goal の state の述語を畳めば元の field になるもの。
* state ごとに渡す専用の手（`extra`）。
* それ以外は simp_all。
-/
local syntax "cs_field " "(" tacticSeq ")" : tactic
macro_rules
  | `(tactic| cs_field ($t)) =>
    `(tactic| first
      | (intro h; cases h; done)
      | with_reducible assumption
      | (cs_norm_goal; done)
      | (cs_norm_goal; with_reducible assumption)
      | (($t); done)
      | (cs_simp; done)
      | (cs_simp2; done))

/-- port state から path start state への移送。`portDone` を挟む。 -/
theorem portDone_toAscii {ctx ctx2 : PCtx} (h : portDone ctx = some ctx2) :
    ctx2.toAscii = ctx.toAscii := by
  unfold portDone at h
  split at h
  · rw [← Option.some.inj h]
  · split at h
    · simp at h
    · rw [← Option.some.inj h]; rfl

theorem CInv.portStep {t : List Char → Option String} {base : Option Url} {input : List Char} {ctx ctx2 : PCtx}
    (h : CInv t base .port input ctx) (hp : portDone ctx = some ctx2) :
    CInv t base .pathStart input ctx2 := by
  have hpo := portDone_portOk hp h.portOk
  obtain ⟨p, hu, ho⟩ := portDone_spec hp
  have hb := portDone_buffer hp
  have ht := portDone_toAscii hp
  have ⟨hov, hta, hbv, hbc, hbnf, hbse, hse, hso, hsb, hhn, hpn, hcn, hpnil, hqn, hfn, hpo', huo,
    hpwo, hqo, hfo, hpao, htr, hoh, hie, hbe, hpb, hdo, htne, hhs, hsh, hhi, hnl, henc, haa, hab,
    hhc, hnf, hpoa, hfsc⟩ := h
  rw [hu] at hpo
  constructor <;> (try rw [hu]) <;> first
    | (intro h; cases h; done)
    | with_reducible assumption
    | (rw [ho]; with_reducible assumption)
    | (rw [ht]; with_reducible assumption)
    | cs_simp

local syntax "cs_close " ident ident ident ident ident ident ident "(" tacticSeq ")" "(" tacticSeq ")" : tactic
macro_rules
  | `(tactic| cs_close $hinv $ctx $hov $hin $ih $u $heq ($t) ($inv)) =>
  `(tactic| first
    | (simp only [fail, $hov:ident, reduceCtorEq] at $heq:ident; done)
    | (simp only [reduceCtorEq] at $heq:ident; done)
    | (exfalso
       simp_all only [Option.isSome_none, Option.isNone_none, Bool.false_eq_true, Bool.false_and,
         Bool.and_false, Bool.not_true, Bool.true_and, Bool.and_true, Bool.false_or]
       done)
    | (injection $heq with hu
       subst hu
       first
       | (($inv); done)
       | (apply canonical_of_frag' $ih (ctx := $ctx)
          constructor <;> cs_field ($t)))
    | (refine $ih _ _ _ $u $heq ?_ ?_
       · first
         | (apply Or.inl; decide)
         | (apply Or.inr; refine ⟨rfl, ?_⟩; simp only [$hin:ident, cpList, List.length_cons]; omega)
       · first
         | (apply CInv.portStep (ctx := $ctx) $hinv; assumption)
         | (($inv); done)
         | (constructor <;> cs_field ($t))))

/-! ## path state

path state の遷移は `pathStepUrl` を挟むので、simp に任せると重い。遷移ごとに補題にしてある。
-/

/-- path state で segment を確定させた url の、path の条件。 -/
theorem CInv.pathFacts {t : List Char → Option String} {base : Option Url} {input : List Char} {ctx : PCtx}
    (h : CInv t base .path input ctx) (slash : Bool) :
    pathCanon ctx.url.isSpecial (pathStepUrl ctx.url slash ctx.buffer).path = true ∧
      Url.driveOk ctx.url.scheme (pathStepUrl ctx.url slash ctx.buffer).path = true ∧
      (∀ o : String, (pathStepUrl ctx.url slash ctx.buffer).path = .opaque o →
        o.toList.getLast? ≠ some ' ') := by
  refine ⟨pathCanon_pathStepUrl h.pathOk (h.pathBuf rfl).1 (h.pathBuf rfl).2,
    driveOk_pathStepUrl h.driveOk, ?_⟩
  intro o hp hl
  rw [pathStepUrl_path_opaque] at hp
  exact absurd (h.trailing o hp hl).1 (by decide)

local macro "cs_path" : tactic =>
  `(tactic| first
    | (intro h; cases h; done)
    | with_reducible assumption
    | (simp only [pathStepUrl_scheme, pathStepUrl_host, pathStepUrl_port, pathStepUrl_username,
        pathStepUrl_password, pathStepUrl_query, pathStepUrl_fragment, pathStepUrl_isSpecial,
        pathStepUrl_includesCredentials]; assumption)
    | (simp only [pathStepUrl_scheme, pathStepUrl_host, pathStepUrl_port, pathStepUrl_username,
        pathStepUrl_password, pathStepUrl_query, pathStepUrl_fragment, pathStepUrl_isSpecial,
        pathStepUrl_includesCredentials]; with_reducible assumption))

/-- path state が `/` で segment を確定させて path state に戻る。 -/
theorem CInv.pathNext {t : List Char → Option String} {base : Option Url} {input : List Char} {ctx : PCtx}
    (h : CInv t base .path input ctx) (slash : Bool) (rest : List Char) :
    CInv t base .path rest { ctx with url := pathStepUrl ctx.url slash ctx.buffer, buffer := [] } := by
  obtain ⟨hP, hD, hT⟩ := h.pathFacts slash
  have hN : True := trivial
  have ⟨hov, hta, hbv, hbc, hbnf, hbse, hse, hso, hsb, hhn, hpn, hcn, hpnil, hqn, hfn, hpo, huo,
    hpwo, hqo, hfo, hpao, htr, hoh, hie, hbe, hpb, hdo, htne, hhs, hsh, hhi, hnl, henc, haa, hab,
    hhc, hnf, hpoa, hfsc⟩ := h
  constructor
  all_goals first
    | cs_path
    | (intro o hp hl; exact absurd hl (hT o hp))
    | (intro _; exact ⟨rfl, fun _ _ h => by cases h⟩)
    | (intro q hq; cases hq; rfl)
    | (intro _; rfl)
    | (intro _ hp; exact absurd hp hN)

/-- path state が `?` で segment を確定させて query state へ。 -/
theorem CInv.pathQuery {t : List Char → Option String} {base : Option Url} {input : List Char} {ctx : PCtx}
    (h : CInv t base .path input ctx) (rest : List Char) {slash : Bool} (hs : slash = false) :
    CInv t base .query rest
      { ctx with url := { (pathStepUrl ctx.url slash ctx.buffer) with query := some "" }, buffer := [] } := by
  subst hs
  obtain ⟨hP, hD, hT⟩ := h.pathFacts false
  have hN := pathStepUrl_ne_nil ctx.url ctx.buffer
  have ⟨hov, hta, hbv, hbc, hbnf, hbse, hse, hso, hsb, hhn, hpn, hcn, hpnil, hqn, hfn, hpo, huo,
    hpwo, hqo, hfo, hpao, htr, hoh, hie, hbe, hpb, hdo, htne, hhs, hsh, hhi, hnl, henc, haa, hab,
    hhc, hnf, hpoa, hfsc⟩ := h
  constructor
  all_goals first
    | cs_path
    | (intro o hp hl; exact absurd hl (hT o hp))
    | (intro _; exact ⟨rfl, fun _ _ h => by cases h⟩)
    | (intro q hq; cases hq; rfl)
    | (intro _; rfl)
    | (intro _ hp; exact absurd hp hN)

/-- path state が `#` で segment を確定させて fragment state へ。 -/
theorem CInv.pathFragment {t : List Char → Option String} {base : Option Url} {input : List Char} {ctx : PCtx}
    (h : CInv t base .path input ctx) (rest : List Char) {slash : Bool} (hs : slash = false) :
    CInv t base .fragment rest
      { ctx with
        url := { (pathStepUrl ctx.url slash ctx.buffer) with fragment := some "" }, buffer := [] } := by
  subst hs
  obtain ⟨hP, hD, hT⟩ := h.pathFacts false
  have hN := pathStepUrl_ne_nil ctx.url ctx.buffer
  have ⟨hov, hta, hbv, hbc, hbnf, hbse, hse, hso, hsb, hhn, hpn, hcn, hpnil, hqn, hfn, hpo, huo,
    hpwo, hqo, hfo, hpao, htr, hoh, hie, hbe, hpb, hdo, htne, hhs, hsh, hhi, hnl, henc, haa, hab,
    hhc, hnf, hpoa, hfsc⟩ := h
  constructor
  all_goals first
    | cs_path
    | (intro o hp hl; exact absurd hl (hT o hp))
    | (intro _; exact ⟨rfl, fun _ _ h => by cases h⟩)
    | (intro q hq; cases hq; rfl)
    | (intro _; rfl)
    | (intro _ hp; exact absurd hp hN)

/-- path state が EOF で segment を確定させて返す。 -/
theorem CInv.pathEnd {t : List Char → Option String} {base : Option Url} {input : List Char} {ctx : PCtx}
    (h : CInv t base .path input ctx) {slash : Bool} (hs : slash = false) :
    canonicalUrl (pathStepUrl ctx.url slash ctx.buffer) t = true := by
  subst hs
  obtain ⟨hP, hD, hT⟩ := h.pathFacts false
  have hN := pathStepUrl_ne_nil ctx.url ctx.buffer
  have ⟨hov, hta, hbv, hbc, hbnf, hbse, hse, hso, hsb, hhn, hpn, hcn, hpnil, hqn, hfn, hpo, huo,
    hpwo, hqo, hfo, hpao, htr, hoh, hie, hbe, hpb, hdo, htne, hhs, hsh, hhi, hnl, henc, haa, hab,
    hhc, hnf, hpoa, hfsc⟩ := h
  apply canonical_of_frag (base := base) (ctx := ctx)
  constructor
  all_goals first
    | cs_path
    | (intro o hp hl; exact absurd hl (hT o hp))
    | (intro _; exact ⟨rfl, fun _ _ h => by cases h⟩)
    | (intro q hq; cases hq; rfl)
    | (intro _; rfl)
    | (intro _ hp; exact absurd hp hN)

/-- path state が区切りでない文字を encode して buffer に積む。 -/
theorem CInv.pathPush {t : List Char → Option String} {base : Option Url} {input rest : List Char} {ch : Char} {ctx : PCtx}
    (h : CInv t base .path input ctx) (hin : input = ch :: rest)
    (hc : ¬(some ch == none || some ch == some '/' || (ctx.url.isSpecial && some ch == some '\\') ||
      (ctx.over.isNone && (some ch == some '?' || some ch == some '#'))) = true) :
    CInv t base .path rest { ctx with buffer := ctx.buffer ++ (encChar pathSet ch).toList } := by
  have hb := h.pathBuf rfl
  have h1 : ¬ch = '/' := by intro he; subst he; simp at hc
  have h2 : ctx.url.isSpecial = true → ¬ch = '\\' := by
    intro hs he; subst he; simp [hs] at hc
  have ⟨hov, hta, hbv, hbc, hbnf, hbse, hse, hso, hsb, hhn, hpn, hcn, hpnil, hqn, hfn, hpo, huo,
    hpwo, hqo, hfo, hpao, htr, hoh, hie, hbe, hpb, hdo, htne, hhs, hsh, hhi, hnl, henc, haa, hab,
    hhc, hnf, hpoa, hfsc⟩ := h
  constructor <;> first
    | (intro h; cases h; done)
    | with_reducible assumption
    | (intro o hp hl; exact absurd (htr o hp hl).1 (by decide))
    | skip
  case pathBuf =>
    intro _
    refine ⟨?_, fun hsp c hc => ?_⟩
    · rw [String.ofList_append, String.ofList_toList, encodedWith_append, hb.1,
        encodedWith_encChar_path]; rfl
    · rcases List.mem_append.mp hc with hc | hc
      · exact hb.2 hsp c hc
      · exact encChar_avoid (by decide) (by decide) (h2 hsp) c hc

/-! ## state ごとの帰納段 -/

theorem step_schemeStart_canon {t : List Char → Option String} (htok : ToAsciiOk t)
    (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hin : input = cpList c rest) (hrn : c = none → rest = [])
    (ih : CRunIH t base (stateRank .schemeStart) input.length)
    (hinv : CInv t base .schemeStart input ctx) :
    ∀ u, step base .schemeStart c rest input ctx = .ok u → canonicalUrl u t = true := by
  intro u heq
  have ⟨hov, hta, hbv, hbc, hbnf, hbse, hse, hso, hsb, hhn, hpn, hcn, hpnil, hqn, hfn, hpo, huo,
    hpwo, hqo, hfo, hpao, htr, hoh, hie, hbe, hpb, hdo, htne, hhs, hsh, hhi, hnl, henc, haa, hab,
    hhc, hnf, hpoa, hfsc⟩ := hinv
  have hrest := fun (h : input.getLast? ≠ some ' ') => rest_getLast hin hrn h
  cs_norm
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals cs_close hinv ctx hov hin ih u heq (fail) (fail)

theorem step_scheme_canon {t : List Char → Option String} (htok : ToAsciiOk t)
    (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hin : input = cpList c rest) (hrn : c = none → rest = [])
    (ih : CRunIH t base (stateRank .scheme) input.length)
    (hinv : CInv t base .scheme input ctx) :
    ∀ u, step base .scheme c rest input ctx = .ok u → canonicalUrl u t = true := by
  intro u heq
  have ⟨hov, hta, hbv, hbc, hbnf, hbse, hse, hso, hsb, hhn, hpn, hcn, hpnil, hqn, hfn, hpo, huo,
    hpwo, hqo, hfo, hpao, htr, hoh, hie, hbe, hpb, hdo, htne, hhs, hsh, hhi, hnl, henc, haa, hab,
    hhc, hnf, hpoa, hfsc⟩ := hinv
  have hrest := fun (h : input.getLast? ≠ some ' ') => rest_getLast hin hrn h
  cs_norm
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals cs_close hinv ctx hov hin ih u heq (fail) (fail)

theorem step_noScheme_canon {t : List Char → Option String} (htok : ToAsciiOk t)
    (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hin : input = cpList c rest) (hrn : c = none → rest = [])
    (ih : CRunIH t base (stateRank .noScheme) input.length)
    (hinv : CInv t base .noScheme input ctx) :
    ∀ u, step base .noScheme c rest input ctx = .ok u → canonicalUrl u t = true := by
  intro u heq
  have ⟨hov, hta, hbv, hbc, hbnf, hbse, hse, hso, hsb, hhn, hpn, hcn, hpnil, hqn, hfn, hpo, huo,
    hpwo, hqo, hfo, hpao, htr, hoh, hie, hbe, hpb, hdo, htne, hhs, hsh, hhi, hnl, henc, haa, hab,
    hhc, hnf, hpoa, hfsc⟩ := hinv
  have hrest := fun (h : input.getLast? ≠ some ' ') => rest_getLast hin hrn h
  cs_norm
  cs_base base hbc hbv
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals cs_close hinv ctx hov hin ih u heq (fail) (fail)

theorem step_specialRelativeOrAuthority_canon {t : List Char → Option String} (htok : ToAsciiOk t)
    (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hin : input = cpList c rest) (hrn : c = none → rest = [])
    (ih : CRunIH t base (stateRank .specialRelativeOrAuthority) input.length)
    (hinv : CInv t base .specialRelativeOrAuthority input ctx) :
    ∀ u, step base .specialRelativeOrAuthority c rest input ctx = .ok u → canonicalUrl u t = true := by
  intro u heq
  have ⟨hov, hta, hbv, hbc, hbnf, hbse, hse, hso, hsb, hhn, hpn, hcn, hpnil, hqn, hfn, hpo, huo,
    hpwo, hqo, hfo, hpao, htr, hoh, hie, hbe, hpb, hdo, htne, hhs, hsh, hhi, hnl, henc, haa, hab,
    hhc, hnf, hpoa, hfsc⟩ := hinv
  have hrest := fun (h : input.getLast? ≠ some ' ') => rest_getLast hin hrn h
  cs_norm
  cs_base base hbc hbv
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals cs_close hinv ctx hov hin ih u heq (fail) (fail)

theorem step_pathOrAuthority_canon {t : List Char → Option String} (htok : ToAsciiOk t)
    (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hin : input = cpList c rest) (hrn : c = none → rest = [])
    (ih : CRunIH t base (stateRank .pathOrAuthority) input.length)
    (hinv : CInv t base .pathOrAuthority input ctx) :
    ∀ u, step base .pathOrAuthority c rest input ctx = .ok u → canonicalUrl u t = true := by
  intro u heq
  have ⟨hov, hta, hbv, hbc, hbnf, hbse, hse, hso, hsb, hhn, hpn, hcn, hpnil, hqn, hfn, hpo, huo,
    hpwo, hqo, hfo, hpao, htr, hoh, hie, hbe, hpb, hdo, htne, hhs, hsh, hhi, hnl, henc, haa, hab,
    hhc, hnf, hpoa, hfsc⟩ := hinv
  have hrest := fun (h : input.getLast? ≠ some ' ') => rest_getLast hin hrn h
  cs_norm
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals cs_close hinv ctx hov hin ih u heq (fail) (fail)

theorem step_relative_canon {t : List Char → Option String} (htok : ToAsciiOk t)
    (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hin : input = cpList c rest) (hrn : c = none → rest = [])
    (ih : CRunIH t base (stateRank .relative) input.length)
    (hinv : CInv t base .relative input ctx) :
    ∀ u, step base .relative c rest input ctx = .ok u → canonicalUrl u t = true := by
  intro u heq
  have ⟨hov, hta, hbv, hbc, hbnf, hbse, hse, hso, hsb, hhn, hpn, hcn, hpnil, hqn, hfn, hpo, huo,
    hpwo, hqo, hfo, hpao, htr, hoh, hie, hbe, hpb, hdo, htne, hhs, hsh, hhi, hnl, henc, haa, hab,
    hhc, hnf, hpoa, hfsc⟩ := hinv
  have hrest := fun (h : input.getLast? ≠ some ' ') => rest_getLast hin hrn h
  cs_norm
  cs_base base hbc hbv
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals cs_close hinv ctx hov hin ih u heq (fail) (fail)

theorem step_relativeSlash_canon {t : List Char → Option String} (htok : ToAsciiOk t)
    (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hin : input = cpList c rest) (hrn : c = none → rest = [])
    (ih : CRunIH t base (stateRank .relativeSlash) input.length)
    (hinv : CInv t base .relativeSlash input ctx) :
    ∀ u, step base .relativeSlash c rest input ctx = .ok u → canonicalUrl u t = true := by
  intro u heq
  have ⟨hov, hta, hbv, hbc, hbnf, hbse, hse, hso, hsb, hhn, hpn, hcn, hpnil, hqn, hfn, hpo, huo,
    hpwo, hqo, hfo, hpao, htr, hoh, hie, hbe, hpb, hdo, htne, hhs, hsh, hhi, hnl, henc, haa, hab,
    hhc, hnf, hpoa, hfsc⟩ := hinv
  have hrest := fun (h : input.getLast? ≠ some ' ') => rest_getLast hin hrn h
  cs_norm
  cs_base base hbc hbv
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals cs_close hinv ctx hov hin ih u heq (fail) (fail)

theorem step_specialAuthoritySlashes_canon {t : List Char → Option String} (htok : ToAsciiOk t)
    (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hin : input = cpList c rest) (hrn : c = none → rest = [])
    (ih : CRunIH t base (stateRank .specialAuthoritySlashes) input.length)
    (hinv : CInv t base .specialAuthoritySlashes input ctx) :
    ∀ u, step base .specialAuthoritySlashes c rest input ctx = .ok u → canonicalUrl u t = true := by
  intro u heq
  have ⟨hov, hta, hbv, hbc, hbnf, hbse, hse, hso, hsb, hhn, hpn, hcn, hpnil, hqn, hfn, hpo, huo,
    hpwo, hqo, hfo, hpao, htr, hoh, hie, hbe, hpb, hdo, htne, hhs, hsh, hhi, hnl, henc, haa, hab,
    hhc, hnf, hpoa, hfsc⟩ := hinv
  have hrest := fun (h : input.getLast? ≠ some ' ') => rest_getLast hin hrn h
  cs_norm
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals cs_close hinv ctx hov hin ih u heq (fail) (fail)

theorem step_specialAuthorityIgnoreSlashes_canon {t : List Char → Option String} (htok : ToAsciiOk t)
    (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hin : input = cpList c rest) (hrn : c = none → rest = [])
    (ih : CRunIH t base (stateRank .specialAuthorityIgnoreSlashes) input.length)
    (hinv : CInv t base .specialAuthorityIgnoreSlashes input ctx) :
    ∀ u, step base .specialAuthorityIgnoreSlashes c rest input ctx = .ok u → canonicalUrl u t = true := by
  intro u heq
  have ⟨hov, hta, hbv, hbc, hbnf, hbse, hse, hso, hsb, hhn, hpn, hcn, hpnil, hqn, hfn, hpo, huo,
    hpwo, hqo, hfo, hpao, htr, hoh, hie, hbe, hpb, hdo, htne, hhs, hsh, hhi, hnl, henc, haa, hab,
    hhc, hnf, hpoa, hfsc⟩ := hinv
  have hrest := fun (h : input.getLast? ≠ some ' ') => rest_getLast hin hrn h
  cs_norm
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals cs_close hinv ctx hov hin ih u heq (fail) (fail)

theorem step_authority_canon {t : List Char → Option String} (htok : ToAsciiOk t)
    (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hin : input = cpList c rest) (hrn : c = none → rest = [])
    (ih : CRunIH t base (stateRank .authority) input.length)
    (hinv : CInv t base .authority input ctx) :
    ∀ u, step base .authority c rest input ctx = .ok u → canonicalUrl u t = true := by
  intro u heq
  have ⟨hov, hta, hbv, hbc, hbnf, hbse, hse, hso, hsb, hhn, hpn, hcn, hpnil, hqn, hfn, hpo, huo,
    hpwo, hqo, hfo, hpao, htr, hoh, hie, hbe, hpb, hdo, htne, hhs, hsh, hhi, hnl, henc, haa, hab,
    hhc, hnf, hpoa, hfsc⟩ := hinv
  have hrest := fun (h : input.getLast? ≠ some ' ') => rest_getLast hin hrn h
  cs_norm
  have hU1a := fun (l : List Char) (b : Bool) => (userinfoFold_enc l (ctx.url, b) huo hpwo).1
  have hU1b := fun (l : List Char) (b : Bool) => (userinfoFold_enc l (ctx.url, b) huo hpwo).2
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals cs_close hinv ctx hov hin ih u heq (first
    | exact (hU1a _ _)
    | exact (hU1b _ _)
    | (intro _ _ hc; refine authority_hostCred haa hab ?_ hc; assumption)
    | (intro _ c hc
       rcases List.mem_append.mp hc with hc | hc
       · exact hab c hc
       · simp only [List.mem_singleton] at hc; subst hc; simp_all)) (fail)

theorem step_host_canon {t : List Char → Option String} (htok : ToAsciiOk t)
    (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hin : input = cpList c rest) (hrn : c = none → rest = [])
    (ih : CRunIH t base (stateRank .host) input.length)
    (hinv : CInv t base .host input ctx) :
    ∀ u, step base .host c rest input ctx = .ok u → canonicalUrl u t = true := by
  intro u heq
  have ⟨hov, hta, hbv, hbc, hbnf, hbse, hse, hso, hsb, hhn, hpn, hcn, hpnil, hqn, hfn, hpo, huo,
    hpwo, hqo, hfo, hpao, htr, hoh, hie, hbe, hpb, hdo, htne, hhs, hsh, hhi, hnl, henc, haa, hab,
    hhc, hnf, hpoa, hfsc⟩ := hinv
  have hrest := fun (h : input.getLast? ≠ some ' ') => rest_getLast hin hrn h
  cs_norm
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals cs_close hinv ctx hov hin ih u heq (first
    | (apply host_emptyNoCred hhc hin <;> assumption)
    | (apply host_idem hta htok; assumption)
    | (apply host_some_ne_empty <;> assumption)) (fail)

theorem step_port_canon {t : List Char → Option String} (htok : ToAsciiOk t)
    (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hin : input = cpList c rest) (hrn : c = none → rest = [])
    (ih : CRunIH t base (stateRank .port) input.length)
    (hinv : CInv t base .port input ctx) :
    ∀ u, step base .port c rest input ctx = .ok u → canonicalUrl u t = true := by
  intro u heq
  have ⟨hov, hta, hbv, hbc, hbnf, hbse, hse, hso, hsb, hhn, hpn, hcn, hpnil, hqn, hfn, hpo, huo,
    hpwo, hqo, hfo, hpao, htr, hoh, hie, hbe, hpb, hdo, htne, hhs, hsh, hhi, hnl, henc, haa, hab,
    hhc, hnf, hpoa, hfsc⟩ := hinv
  have hrest := fun (h : input.getLast? ≠ some ' ') => rest_getLast hin hrn h
  cs_norm
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals cs_close hinv ctx hov hin ih u heq (fail) (fail)

theorem step_file_canon {t : List Char → Option String} (htok : ToAsciiOk t)
    (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hin : input = cpList c rest) (hrn : c = none → rest = [])
    (ih : CRunIH t base (stateRank .file) input.length)
    (hinv : CInv t base .file input ctx) :
    ∀ u, step base .file c rest input ctx = .ok u → canonicalUrl u t = true := by
  intro u heq
  have ⟨hov, hta, hbv, hbc, hbnf, hbse, hse, hso, hsb, hhn, hpn, hcn, hpnil, hqn, hfn, hpo, huo,
    hpwo, hqo, hfo, hpao, htr, hoh, hie, hbe, hpb, hdo, htne, hhs, hsh, hhi, hnl, henc, haa, hab,
    hhc, hnf, hpoa, hfsc⟩ := hinv
  have hrest := fun (h : input.getLast? ≠ some ' ') => rest_getLast hin hrn h
  cs_norm
  cs_base base hbc hbv
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals cs_close hinv ctx hov hin ih u heq (fail) (fail)

theorem step_fileSlash_canon {t : List Char → Option String} (htok : ToAsciiOk t)
    (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hin : input = cpList c rest) (hrn : c = none → rest = [])
    (ih : CRunIH t base (stateRank .fileSlash) input.length)
    (hinv : CInv t base .fileSlash input ctx) :
    ∀ u, step base .fileSlash c rest input ctx = .ok u → canonicalUrl u t = true := by
  intro u heq
  have ⟨hov, hta, hbv, hbc, hbnf, hbse, hse, hso, hsb, hhn, hpn, hcn, hpnil, hqn, hfn, hpo, huo,
    hpwo, hqo, hfo, hpao, htr, hoh, hie, hbe, hpb, hdo, htne, hhs, hsh, hhi, hnl, henc, haa, hab,
    hhc, hnf, hpoa, hfsc⟩ := hinv
  have hrest := fun (h : input.getLast? ≠ some ' ') => rest_getLast hin hrn h
  cs_norm
  cs_base base hbc hbv
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals cs_close hinv ctx hov hin ih u heq (first
    | (apply pathCanon_fileSlashDrive <;> cs_simp)
    | (apply driveOk_fileSlashDrive; cs_simp)) (fail)

theorem step_fileHost_canon {t : List Char → Option String} (htok : ToAsciiOk t)
    (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hin : input = cpList c rest) (hrn : c = none → rest = [])
    (ih : CRunIH t base (stateRank .fileHost) input.length)
    (hinv : CInv t base .fileHost input ctx) :
    ∀ u, step base .fileHost c rest input ctx = .ok u → canonicalUrl u t = true := by
  intro u heq
  have ⟨hov, hta, hbv, hbc, hbnf, hbse, hse, hso, hsb, hhn, hpn, hcn, hpnil, hqn, hfn, hpo, huo,
    hpwo, hqo, hfo, hpao, htr, hoh, hie, hbe, hpb, hdo, htne, hhs, hsh, hhi, hnl, henc, haa, hab,
    hhc, hnf, hpoa, hfsc⟩ := hinv
  have hrest := fun (h : input.getLast? ≠ some ' ') => rest_getLast hin hrn h
  cs_norm
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals cs_close hinv ctx hov hin ih u heq (first
    | (apply fileHost_idem hta htok; assumption)
    | (apply host_idem hta htok; assumption)
    | (exact fileHost_notLocal)
    | (intro _; refine ⟨(pathBuf_of_drive ?_).1, fun _ => (pathBuf_of_drive ?_).2⟩ <;> simp_all)) (fail)

theorem step_pathStart_canon {t : List Char → Option String} (htok : ToAsciiOk t)
    (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hin : input = cpList c rest) (hrn : c = none → rest = [])
    (ih : CRunIH t base (stateRank .pathStart) input.length)
    (hinv : CInv t base .pathStart input ctx) :
    ∀ u, step base .pathStart c rest input ctx = .ok u → canonicalUrl u t = true := by
  intro u heq
  have ⟨hov, hta, hbv, hbc, hbnf, hbse, hse, hso, hsb, hhn, hpn, hcn, hpnil, hqn, hfn, hpo, huo,
    hpwo, hqo, hfo, hpao, htr, hoh, hie, hbe, hpb, hdo, htne, hhs, hsh, hhi, hnl, henc, haa, hab,
    hhc, hnf, hpoa, hfsc⟩ := hinv
  have hrest := fun (h : input.getLast? ≠ some ' ') => rest_getLast hin hrn h
  cs_norm
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals cs_close hinv ctx hov hin ih u heq (fail) (fail)

theorem step_path_canon {t : List Char → Option String} (htok : ToAsciiOk t)
    (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hin : input = cpList c rest) (hrn : c = none → rest = [])
    (ih : CRunIH t base (stateRank .path) input.length)
    (hinv : CInv t base .path input ctx) :
    ∀ u, step base .path c rest input ctx = .ok u → canonicalUrl u t = true := by
  intro u heq
  have ⟨hov, hta, hbv, hbc, hbnf, hbse, hse, hso, hsb, hhn, hpn, hcn, hpnil, hqn, hfn, hpo, huo,
    hpwo, hqo, hfo, hpao, htr, hoh, hie, hbe, hpb, hdo, htne, hhs, hsh, hhi, hnl, henc, haa, hab,
    hhc, hnf, hpoa, hfsc⟩ := hinv
  have hrest := fun (h : input.getLast? ≠ some ' ') => rest_getLast hin hrn h
  cs_norm
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals cs_close hinv ctx hov hin ih u heq (fail) (first
    | (apply CInv.pathEnd hinv; simp)
    | (apply CInv.pathNext hinv)
    | (apply CInv.pathQuery hinv; simp)
    | (apply CInv.pathFragment hinv; simp)
    | (apply CInv.pathPush hinv hin; assumption))

theorem step_opaquePath_canon {t : List Char → Option String} (htok : ToAsciiOk t)
    (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hin : input = cpList c rest) (hrn : c = none → rest = [])
    (ih : CRunIH t base (stateRank .opaquePath) input.length)
    (hinv : CInv t base .opaquePath input ctx) :
    ∀ u, step base .opaquePath c rest input ctx = .ok u → canonicalUrl u t = true := by
  intro u heq
  have ⟨hov, hta, hbv, hbc, hbnf, hbse, hse, hso, hsb, hhn, hpn, hcn, hpnil, hqn, hfn, hpo, huo,
    hpwo, hqo, hfo, hpao, htr, hoh, hie, hbe, hpb, hdo, htne, hhs, hsh, hhi, hnl, henc, haa, hab,
    hhc, hnf, hpoa, hfsc⟩ := hinv
  have hrest := fun (h : input.getLast? ≠ some ' ') => rest_getLast hin hrn h
  cs_norm
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals cs_close hinv ctx hov hin ih u heq (fail) (first
    | (apply CInv.opaquePct hinv hin)
    | (apply CInv.opaqueSpace hinv hin <;> assumption)
    | (apply CInv.opaqueEnc hinv hin <;> assumption))

theorem step_query_canon {t : List Char → Option String} (htok : ToAsciiOk t)
    (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hin : input = cpList c rest) (hrn : c = none → rest = [])
    (ih : CRunIH t base (stateRank .query) input.length)
    (hinv : CInv t base .query input ctx) :
    ∀ u, step base .query c rest input ctx = .ok u → canonicalUrl u t = true := by
  intro u heq
  have ⟨hov, hta, hbv, hbc, hbnf, hbse, hse, hso, hsb, hhn, hpn, hcn, hpnil, hqn, hfn, hpo, huo,
    hpwo, hqo, hfo, hpao, htr, hoh, hie, hbe, hpb, hdo, htne, hhs, hsh, hhi, hnl, henc, haa, hab,
    hhc, hnf, hpoa, hfsc⟩ := hinv
  have hrest := fun (h : input.getLast? ≠ some ' ') => rest_getLast hin hrn h
  cs_norm
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals cs_close hinv ctx hov hin ih u heq ((intro q hq; cases hq; exact queryOf_enc hqo)) (fail)

theorem step_fragment_canon {t : List Char → Option String} (htok : ToAsciiOk t)
    (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hin : input = cpList c rest) (hrn : c = none → rest = [])
    (ih : CRunIH t base (stateRank .fragment) input.length)
    (hinv : CInv t base .fragment input ctx) :
    ∀ u, step base .fragment c rest input ctx = .ok u → canonicalUrl u t = true := by
  intro u heq
  have ⟨hov, hta, hbv, hbc, hbnf, hbse, hse, hso, hsb, hhn, hpn, hcn, hpnil, hqn, hfn, hpo, huo,
    hpwo, hqo, hfo, hpao, htr, hoh, hie, hbe, hpb, hdo, htne, hhs, hsh, hhi, hnl, henc, haa, hab,
    hhc, hnf, hpoa, hfsc⟩ := hinv
  have hrest := fun (h : input.getLast? ≠ some ' ') => rest_getLast hin hrn h
  cs_norm
  simp only [step.eq_def] at heq
  repeat' split at heq
  all_goals cs_close hinv ctx hov hin ih u heq ((intro f hf; cases hf; simp only [encodedWith_append, encodedWith_encChar_fragment, Bool.and_true]; exact encodedWith_getD hfo)) (fail)

/-! ## 組み上げ -/

/-- **`step` の一歩は `CInv` を保つ。** state ごとの定理を並べるだけ。 -/
theorem step_canon {t : List Char → Option String} (htok : ToAsciiOk t)
    (base : Option Url) (st : PState) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hin : input = cpList c rest) (hrn : c = none → rest = [])
    (ih : CRunIH t base (stateRank st) input.length) (hinv : CInv t base st input ctx) :
    ∀ u, step base st c rest input ctx = .ok u → canonicalUrl u t = true := by
  cases st
  · exact step_schemeStart_canon htok base c rest input ctx hin hrn ih hinv
  · exact step_scheme_canon htok base c rest input ctx hin hrn ih hinv
  · exact step_noScheme_canon htok base c rest input ctx hin hrn ih hinv
  · exact step_specialRelativeOrAuthority_canon htok base c rest input ctx hin hrn ih hinv
  · exact step_pathOrAuthority_canon htok base c rest input ctx hin hrn ih hinv
  · exact step_relative_canon htok base c rest input ctx hin hrn ih hinv
  · exact step_relativeSlash_canon htok base c rest input ctx hin hrn ih hinv
  · exact step_specialAuthoritySlashes_canon htok base c rest input ctx hin hrn ih hinv
  · exact step_specialAuthorityIgnoreSlashes_canon htok base c rest input ctx hin hrn ih hinv
  · exact step_authority_canon htok base c rest input ctx hin hrn ih hinv
  · exact step_host_canon htok base c rest input ctx hin hrn ih hinv
  · exact step_port_canon htok base c rest input ctx hin hrn ih hinv
  · exact step_file_canon htok base c rest input ctx hin hrn ih hinv
  · exact step_fileSlash_canon htok base c rest input ctx hin hrn ih hinv
  · exact step_fileHost_canon htok base c rest input ctx hin hrn ih hinv
  · exact step_pathStart_canon htok base c rest input ctx hin hrn ih hinv
  · exact step_path_canon htok base c rest input ctx hin hrn ih hinv
  · exact step_opaquePath_canon htok base c rest input ctx hin hrn ih hinv
  · exact step_query_canon htok base c rest input ctx hin hrn ih hinv
  · exact step_fragment_canon htok base c rest input ctx hin hrn ih hinv

/--
**state machine は `CInv` を保つ。**

`run_valid` と同じく `(stateRank st, input.length)` の辞書式についての帰納法。
-/
theorem run_canonical {t : List Char → Option String} (htok : ToAsciiOk t) (base : Option Url) :
    ∀ (st : PState) (input : List Char) (ctx : PCtx),
    CInv t base st input ctx → ∀ u, run base st input ctx = .ok u → canonicalUrl u t = true := by
  have H : ∀ r n (st : PState) (input : List Char), stateRank st = r → input.length = n →
      ∀ ctx, CInv t base st input ctx → ∀ u, run base st input ctx = .ok u →
        canonicalUrl u t = true := by
    intro r
    induction r using Nat.strongRecOn with
    | _ r ihr =>
      intro n
      induction n using Nat.strongRecOn with
      | _ n ihn =>
        intro st input hr hn ctx hinv u heq
        have ih : CRunIH t base (stateRank st) input.length := by
          intro st' input' ctx' u' heq' hlt hinv'
          rcases hlt with h | ⟨he, hl⟩
          · exact ihr (stateRank st') (hr ▸ h) input'.length st' input' rfl rfl ctx' hinv' u' heq'
          · exact ihn input'.length (hn ▸ hl) st' input' (hr ▸ he) rfl ctx' hinv' u' heq'
        cases input with
        | nil =>
          rw [run.eq_def] at heq
          exact step_canon htok base st none [] [] ctx rfl (fun _ => rfl) ih hinv u heq
        | cons ch tl =>
          rw [run.eq_def] at heq
          exact step_canon htok base st (some ch) tl (ch :: tl) ctx rfl (fun h => by cases h) ih hinv u
            heq
  intro st input ctx
  exact H _ _ st input rfl rfl ctx

/--
**basic URL parser が返す record は canonical である。**

ToASCII は `ToAsciiOk` を満たすものなら一般でよい（既定の `asciiDomainToASCII` は `toAsciiOk_ascii`）。
base を与えるなら、base も妥当で canonical であることを仮定する。
`parseUrl` では base も parse で作るので、この仮定は外れる（`parseUrl_canonical`）。
-/
theorem basicUrlParse_canonical {t : List Char → Option String} (htok : ToAsciiOk t)
    {input : String} {base : Option Url}
    (hb : ∀ b, base = some b → ValidUrl b) (hbc : ∀ b, base = some b → canonicalUrl b t = true)
    {u : Url} (h : basicUrlParse input base t = some u) : canonicalUrl u t = true :=
  basicUrlParse_canonical_of_step (fun b st i c hi u' he => run_canonical htok b st i c hi u' he)
    hb hbc h

/-- `URL(url, base)` の入口についても同じ。 -/
theorem parseUrl_canonical {t : List Char → Option String} (htok : ToAsciiOk t)
    {input : String} {base : Option String} {u : Url}
    (h : parseUrl input base t = some u) : canonicalUrl u t = true := by
  unfold parseUrl at h
  split at h
  · exact basicUrlParse_canonical htok (fun b hb => absurd hb (by simp))
      (fun b hb => absurd hb (by simp)) h
  · split at h
    · simp at h
    · next bu hbu =>
      refine basicUrlParse_canonical htok (fun b hb => ?_) (fun b hb => ?_) h
      · rw [← Option.some.inj hb]
        exact basicUrlParse_valid (fun b' hb' => absurd hb' (by simp)) hbu
      · rw [← Option.some.inj hb]
        exact basicUrlParse_canonical htok (fun b' hb' => absurd hb' (by simp))
          (fun b' hb' => absurd hb' (by simp)) hbu

end Url
