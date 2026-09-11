import Dom.Exec.Scenario
import Dom.Validity.Admissible

/-!
# oracle が自分の invariant を破らないこと

`notes/research-foundation-roadmap.md` Phase B の
`runOperations_never_reports_invariant_violation`。

`Dom/Exec/Scenario.lean` の `runOperations` は各 step の後に
`AdmissibleDOMState` の六つの成分を実行時に検査し、
破れていればその step 番号を返す。

`Dom/Validity/Admissible.lean` の preservation 定理から、
初期状態が admissible なら **この検査は決して発火しない**ことが従う。
つまり `invariantViolation` が出たときは model の algorithm ではなく
harness の側（初期状態の構築や操作の割り当て）を疑えばよい。
-/

namespace Dom.Exec

open Dom

/-- `nextNode()` / `previousNode()` を一つの iterator に適用しても admissible のままである。 -/
theorem admissible_stepIterator {s : DOMState} {i : Nat}
    {f : Tree → IteratorState → Option (NodeId × IteratorState)}
    (hf : ∀ it ∈ s.iterators, ∀ n it', f s.tree it = some (n, it') → ValidIterator s.tree it')
    (h : AdmissibleDOMState s) : AdmissibleDOMState (stepIterator s i f) := by
  unfold stepIterator
  split
  · exact h
  · next it hit =>
    split
    · exact h
    · next m it' hp =>
      have hitmem : it ∈ s.iterators := List.mem_of_getElem? hit
      refine ⟨h.structural, h.nodeDocuments, h.documentTrees, h.rangeEndpoints, ?_, ?_⟩
      · intro x hx
        rcases ListUtil.mem_set_cases s.iterators i it' x hx with hxe | hx'
        · rw [hxe]
          exact hf it hitmem m it' hp
        · exact h.iterators x hx'
      · exact h.observerRegistrations

/-- 一つの操作は admissibility を保つ。 -/
theorem admissible_applyOperation {s s' : DOMState} {op : Operation}
    (h : AdmissibleDOMState s) (hop : applyOperation s op = .ok s') : AdmissibleDOMState s' := by
  cases op with
  | appendChild p n => exact admissible_appendChild h hop
  | insertBefore p n c => exact admissible_insertBefore h hop
  | replaceChild p n c => exact admissible_replaceChild h hop
  | removeChild p n => exact admissible_removeChild h hop
  | replaceChildren p n => exact admissible_replaceChildren h hop
  | before tgt n => exact admissible_before h hop
  | after tgt n => exact admissible_after h hop
  | replaceWith tgt n => exact admissible_replaceWith h hop
  | remove tgt => exact admissible_nodeRemove h hop
  | moveBefore p n c => exact admissible_moveBefore h hop
  | iteratorNext i =>
    rw [← Except.ok.inj hop]
    exact admissible_stepIterator
      (fun it _ n it' hs => validIterator_nextNode h.wellFormed (h.iterators it (by assumption)) hs)
      h
  | iteratorPrevious i =>
    rw [← Except.ok.inj hop]
    exact admissible_stepIterator
      (fun it _ n it' hs =>
        validIterator_previousNode h.wellFormed (h.iterators it (by assumption)) hs) h
  | replaceData n o c d => exact admissible_replaceData h hop
  | appendData n d => exact admissible_appendData h hop
  | insertData n o d => exact admissible_insertData h hop
  | deleteData n o c => exact admissible_deleteData h hop
  | setData n d => exact admissible_setData h hop

/--
admissible な初期状態から始めれば、`runOperations` は invariant 違反を報告しない。

PLAN §7.2 の実行時検査は、`AdmissibleDOMState` の preservation 定理がある以上、
model の algorithm では発火しない。発火したなら harness 側の誤りである。
-/
theorem runOperations_no_violation :
    ∀ (ops : List Operation) {s : DOMState} (i : Nat),
      AdmissibleDOMState s → (runOperations s ops i).2 = none
  | [], _, _, _ => rfl
  | op :: ops, s, i, h => by
    rw [runOperations]
    split
    · rfl
    · next s' hop =>
      have h' : AdmissibleDOMState s' := admissible_applyOperation h hop
      rw [if_neg (by simp [(checkWellFormed_iff s'.tree).mpr h'.wellFormed])]
      rw [if_neg (by simp [(checkStructurallyValid_iff s'.tree).mpr h'.structural])]
      rw [if_neg (by simp [(checkNodeDocumentsValid_iff s'.tree).mpr h'.nodeDocuments])]
      rw [if_neg (by simp [(checkDocumentTreesValid_iff s'.tree).mpr h'.documentTrees])]
      rw [if_neg (by simp [(checkRangeEndpointsValid_iff s').mpr h'.rangeEndpoints])]
      rw [if_neg (by simp [(checkIteratorsValid_iff h'.wellFormed).mpr h'.iterators])]
      simp only []
      exact runOperations_no_violation ops (i + 1) h'

end Dom.Exec
