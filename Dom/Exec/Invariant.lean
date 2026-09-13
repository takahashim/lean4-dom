import Dom.Exec.Eval
import Dom.Validity.Admissible
import Dom.Validity.Normalize
import Dom.Validity.RangeApi
import Dom.Validity.Walkers

/-!
# oracle が自分の invariant を破らないこと

`notes/research-foundation-roadmap.md` Phase B の
`runOperations_never_reports_invariant_violation`。

`Dom/Exec/Scenario.lean` の `runOperations` は各 step の後に
`AdmissibleDOMState` の七つの成分を実行時に検査し、
破れていればその step 番号と成分の名前を返す。

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
    (h : AdmissibleDOMState s) : AdmissibleDOMState (stepIterator s i f).1 := by
  unfold stepIterator
  split
  · exact h
  · next it hit =>
    split
    · exact h
    · next m it' hp =>
      have hitmem : it ∈ s.iterators := List.mem_of_getElem? hit
      refine ⟨h.structural, h.nodeDocuments, h.documentTrees, h.rangeEndpoints, ?_, ?_,
        h.attributes⟩
      · intro x hx
        rcases ListUtil.mem_set_cases s.iterators i it' x hx with hxe | hx'
        · rw [hxe]
          exact hf it hitmem m it' hp
        · exact h.iterators x hx'
      · exact h.observerRegistrations

/-- 値を返すだけの操作は状態を変えない。 -/
theorem admissible_requireNodes {s s' : DOMState} {ns : List NodeId}
    (h : AdmissibleDOMState s) (hr : requireNodes s ns = .ok s') : AdmissibleDOMState s' := by
  unfold requireNodes at hr
  split at hr
  · rw [← Except.ok.inj hr]; exact h
  · simp at hr

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
  | normalize tgt => exact admissible_normalize h hop
  | rangeSetStart i n o => exact admissible_rangeSetStart h hop
  | rangeSetEnd i n o => exact admissible_rangeSetEnd h hop
  | rangeSetStartSibling i n a => exact admissible_rangeSetStartSibling h hop
  | rangeSetEndSibling i n a => exact admissible_rangeSetEndSibling h hop
  | rangeCollapse i t => exact admissible_rangeCollapse h hop
  | rangeSelectNode i n => exact admissible_rangeSelectNode h hop
  | rangeSelectNodeContents i n => exact admissible_rangeSelectNodeContents h hop
  | rangeIsPointInRange i n o =>
    simp only [applyOperation, Except.map] at hop
    split at hop
    · simp at hop
    · rw [← Except.ok.inj hop]; exact h
  | rangeIntersectsNode i n =>
    simp only [applyOperation, Except.map] at hop
    split at hop
    · simp at hop
    · rw [← Except.ok.inj hop]; exact h
  | rangeCompareBoundaryPoints i how j =>
    simp only [applyOperation, Except.map] at hop
    split at hop
    · simp at hop
    · rw [← Except.ok.inj hop]; exact h
  | rangeComparePoint i n o =>
    simp only [applyOperation, Except.map] at hop
    split at hop
    · simp at hop
    · rw [← Except.ok.inj hop]; exact h
  | rangeDeleteContents i => exact admissible_rangeDeleteContents h hop
  | rangeInsertNode i n => exact admissible_rangeInsertNode h hop
  | walkerMove i m =>
    -- `applyOperation` は返した node を捨てるので、`Except.map` を剥がす。
    simp only [applyOperation, Except.map] at hop
    split at hop
    · simp at hop
    · next res he =>
      obtain ⟨r, s₁⟩ := res
      have : s₁ = s' := by simpa using hop
      subst this
      exact admissible_walkerStep h he
  | rangeToString i =>
    -- 値を返すだけなので状態は変わらない。
    simp only [applyOperation, Except.map] at hop
    split at hop
    · simp at hop
    · next res he =>
      have : s = s' := by simpa using hop
      subst this
      exact h
  | substringData n o c =>
    simp only [applyOperation, Except.map] at hop
    split at hop
    · simp at hop
    · next res he =>
      have : s = s' := by simpa using hop
      subst this
      exact h
  | compareDocumentPosition n o => exact admissible_requireNodes h hop
  | nodeContains n o => exact admissible_requireNodes h hop
  | getRootNode n => exact admissible_requireNodes h hop
  | isEqualNode n o => exact admissible_requireNodes h hop
  | getTextContent n => exact admissible_requireNodes h hop
  | getNodeValue n => exact admissible_requireNodes h hop
  | getAttribute e q => exact admissible_requireNodes h hop
  | hasAttribute e q => exact admissible_requireNodes h hop
  | getAttributeNames e => exact admissible_requireNodes h hop
  | lookupNamespaceURI n p => exact admissible_requireNodes h hop
  | lookupPrefix n ns => exact admissible_requireNodes h hop
  | isDefaultNamespace n ns => exact admissible_requireNodes h hop
  | setAttribute e qn v => exact admissible_setAttribute h hop
  | setAttributeNS e ns qn v => exact admissible_setAttributeNS h hop
  | removeAttribute e qn => exact admissible_removeAttribute h hop
  | removeAttributeNS e ns ln => exact admissible_removeAttributeNS h hop
  | toggleAttribute e qn f =>
    -- `applyOperation` は返り値の `Bool` を捨てるので、`Except.map` を剥がす。
    simp only [applyOperation, Except.map] at hop
    split at hop
    · simp at hop
    · next res he =>
      obtain ⟨s₁, b⟩ := res
      have : s₁ = s' := by simpa using hop
      subst this
      exact admissible_toggleAttribute h he
  | observe mo target opts => exact admissible_observe h hop
  | disconnect mo =>
    rw [← Except.ok.inj hop]
    exact admissible_disconnect h mo
  | takeRecords mo =>
    rw [← Except.ok.inj hop]
    exact admissible_takeRecords h mo
  | notify =>
    rw [← Except.ok.inj hop]
    exact admissible_notifyMutationObservers h

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
      rw [if_neg (by simp [(checkObserverRegistrationsValid_iff s').mpr h'.observerRegistrations])]
      rw [if_neg (by simp [(checkAttributesValid_iff s'.tree).mpr h'.attributes])]
      simp only []
      exact runOperations_no_violation ops (i + 1) h'

/-! ## 操作列と到達可能性 -/

/-- 操作列を順に適用する。例外が起きたらそこで止める。 -/
def run : DOMState → List Operation → Except DOMException DOMState
  | s, [] => .ok s
  | s, op :: ops =>
    match applyOperation s op with
    | .error e => .error e
    | .ok s' => run s' ops

/-- 有限の操作列は admissibility を保つ。 -/
theorem run_preserves_admissibility :
    ∀ (ops : List Operation) {s s' : DOMState},
      AdmissibleDOMState s → run s ops = .ok s' → AdmissibleDOMState s'
  | [], _, _, h, hr => by rw [run] at hr; rw [← Except.ok.inj hr]; exact h
  | op :: ops, s, s', h, hr => by
    rw [run] at hr
    split at hr
    · simp at hr
    · next s₁ hop =>
      exact run_preserves_admissibility ops (admissible_applyOperation h hop) hr

/--
指定した初期状態の集合から public API だけで到達できる状態。

`AdmissibleDOMState` が **局所不変条件の閉包**であるのに対し、
こちらは **構成可能性**である。両者は別の概念なので混同しない
（`notes/research-foundation-roadmap.md` §4）。
-/
inductive ReachableFrom (initial : DOMState → Prop) : DOMState → Prop where
  | base {s : DOMState} : initial s → ReachableFrom initial s
  | step {s s' : DOMState} {op : Operation} :
      ReachableFrom initial s → applyOperation s op = .ok s' → ReachableFrom initial s'

/-- admissible な初期状態から到達できる状態は admissible である。 -/
theorem reachable_admissible {initial : DOMState → Prop}
    (hinit : ∀ s, initial s → AdmissibleDOMState s) {s : DOMState}
    (hr : ReachableFrom initial s) : AdmissibleDOMState s := by
  induction hr with
  | base h => exact hinit _ h
  | step _ hop ih => exact admissible_applyOperation ih hop

end Dom.Exec
