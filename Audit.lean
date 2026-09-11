import Lean
import Dom
import Dom.Exec.Invariant

/-!
# 公開主定理の axiom audit

`notes/research-foundation-roadmap.md` §11.1。

公開する主定理が、許容した三つの axiom
（`propext` / `Classical.choice` / `Quot.sound`）以外に依存していないことを検査する。
`sorryAx` や意図しない独自 axiom が入ったら、この file の elaboration が失敗する。

CI からは次で走らせる。

```sh
lake env lean Audit.lean
```

この file は `lake build` の対象外なので、`Dom` library の依存関係は増やさない。
-/

namespace Dom.Audit

open Lean Elab Command

/--
許容する axiom。

* `propext` — 命題の外延性。`Prop` の等式を扱う補題が使う。
* `Classical.choice` — 古典論理。`by_cases` と `Decidable` の古典 instance が使う。
* `Quot.sound` — 商型。`List` などの core の定義が使う。

`sorryAx` は当然ここに入れない。
-/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- 指定した定数が許容外の axiom に依存していないことを検査する。 -/
syntax (name := auditAxioms) "#audit_axioms" ident+ : command

@[command_elab auditAxioms]
def elabAuditAxioms : CommandElab := fun stx => do
  for id in stx[1].getArgs do
    let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let axs ← liftCoreM <| collectAxioms c
    for a in axs do
      unless allowedAxioms.contains a do
        throwErrorAt id "{c} が許容外の axiom {a} に依存している"
    logInfo m!"{c}: {axs.toList}"

end Dom.Audit

open Dom.Audit

/-! ## 主定理 -/

-- §7 操作列に対する主定理
#audit_axioms
  Dom.Exec.admissible_applyOperation
  Dom.Exec.run_preserves_admissibility
  Dom.Exec.reachable_admissible
  Dom.Exec.runOperations_no_violation

-- §8 `BoundaryLE` の negative result
#audit_axioms
  Dom.exists_insert_breaking_boundaryLE
  Dom.boundaryLE_not_preserved_by_insert

-- §4.2.3 の algorithm の admissibility 保存
#audit_axioms
  Dom.admissible_remove
  Dom.admissible_insert
  Dom.admissible_replace
  Dom.admissible_replaceAll
  Dom.admissible_move
  Dom.admissible_moveBefore
  Dom.admissible_replaceData

-- public API の admissibility 保存
#audit_axioms
  Dom.admissible_appendChild
  Dom.admissible_insertBefore
  Dom.admissible_replaceChild
  Dom.admissible_removeChild
  Dom.admissible_replaceChildren
  Dom.admissible_before
  Dom.admissible_after
  Dom.admissible_replaceWith
  Dom.admissible_nodeRemove
  Dom.admissible_appendData
  Dom.admissible_insertData
  Dom.admissible_deleteData
  Dom.admissible_setData

-- §16 の live object をまとめた形
#audit_axioms
  Dom.remove_preserves_live_objects
  Dom.insert_preserves_endpoints
  Dom.move_matches_remove_insert_observation
  Dom.replaceData_preserves_live_object_validity

-- MutationObserver の配送
#audit_axioms
  Dom.admissible_observe
  Dom.admissible_disconnect
  Dom.admissible_takeRecords
  Dom.admissible_notifyMutationObservers

-- 契約
#audit_axioms
  Dom.remove_succeeds_iff
  Dom.remove_error_iff
  Dom.replace_cycle_precedes_notFound
  Dom.insertBefore_cycle_precedes_notFound
  Dom.moveValidity_step1
  Dom.moveValidity_step2
  Dom.moveValidity_step3
  Dom.moveValidity_step4

-- boolean checker と Prop の対応
#audit_axioms
  Dom.checkAdmissibleDOMState_iff
  Dom.checkWellFormed_iff
  Dom.checkStructurallyValid_iff
  Dom.checkNodeDocumentsValid_iff
  Dom.checkDocumentTreesValid_iff
  Dom.checkRangeEndpointsValid_iff
  Dom.checkIteratorsValid_iff
