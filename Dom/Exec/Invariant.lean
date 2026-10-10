import Dom.Exec.Eval
import Dom.Validity.Admissible
import Dom.Validity.Normalize
import Dom.Validity.RangeApi
import Dom.Validity.Walkers
import Dom.Validity.Events
import Dom.Validity.Clone
import Dom.Validity.AttrNode
import Dom.Validity.AttrAsNode
import Dom.Properties.Import
import Dom.Validity.Variadic
import Dom.Validity.Reflect

/-!
# oracle が自分の invariant を破らないこと

`docs/theorems.md` の `Dom.Exec.runOperations_no_violation`。

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
theorem admissible_requireRefs {s s' : DOMState} {rs : List NodeRef}
    (h : AdmissibleDOMState s) (hr : requireRefs s rs = .ok s') : AdmissibleDOMState s' := by
  unfold requireRefs at hr
  split at hr
  · rw [← Except.ok.inj hr]; exact h
  · simp at hr

theorem admissible_requireNodes {s s' : DOMState} {ns : List NodeId}
    (h : AdmissibleDOMState s) (hr : requireNodes s ns = .ok s') : AdmissibleDOMState s' := by
  unfold requireNodes at hr
  split at hr
  · rw [← Except.ok.inj hr]; exact h
  · simp at hr

/-- 検査だけして状態をそのまま返す操作も、状態を変えない。 -/
theorem admissible_mapConst {α : Type} {s s' : DOMState} {r : Except DOMException α}
    (h : AdmissibleDOMState s) (hr : r.map (fun _ => s) = .ok s') : AdmissibleDOMState s' := by
  cases r with
  | error e => simp [Except.map] at hr
  | ok a =>
    simp only [Except.map, Except.ok.injEq] at hr
    rw [← hr]; exact h

/-- 一つの操作は admissibility を保つ。 -/
theorem admissible_applyOperation {s s' : DOMState} {op : Operation}
    (h : AdmissibleDOMState s) (hop : applyOperation s op = .ok s') : AdmissibleDOMState s' := by
  cases op with
  | appendChild p n => exact admissible_appendChild h hop
  | insertBefore p n c => exact admissible_insertBefore h hop
  | replaceChild p n c => exact admissible_replaceChild h hop
  | removeChild p n => exact admissible_removeChild h hop
  | replaceChildren p ns =>
    exact (closed_replaceChildrenNodes admissible_variadicClosed h _ _).1 s' (dropState_ok hop)
  | prepend p ns => exact (closed_prependNodes admissible_variadicClosed h _ _).1 s' (dropState_ok hop)
  | append p ns => exact (closed_appendNodes admissible_variadicClosed h _ _).1 s' (dropState_ok hop)
  | before tgt ns => exact (closed_beforeNodes admissible_variadicClosed h _ _).1 s' (dropState_ok hop)
  | after tgt ns => exact (closed_afterNodes admissible_variadicClosed h _ _).1 s' (dropState_ok hop)
  | replaceWith tgt ns =>
    exact (closed_replaceWithNodes admissible_variadicClosed h _ _).1 s' (dropState_ok hop)
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
  | createElement doc ln =>
    obtain ⟨n, hr⟩ := dropNode_ok hop
    exact admissible_createElement h hr
  | createElementNS doc ns qn =>
    obtain ⟨n, hr⟩ := dropNode_ok hop
    exact admissible_createElementNS h hr
  | createTextNode doc d =>
    obtain ⟨n, hr⟩ := dropNode_ok hop
    exact admissible_createTextNode h hr
  | createComment doc d =>
    obtain ⟨n, hr⟩ := dropNode_ok hop
    exact admissible_createComment h hr
  | createDocumentFragment doc =>
    obtain ⟨n, hr⟩ := dropNode_ok hop
    exact admissible_createDocumentFragment h hr
  | cloneNode n deep =>
    obtain ⟨c, hr⟩ := dropNode_ok hop
    exact admissible_cloneNode h hr
  | importNode doc n o =>
    obtain ⟨c, hr⟩ := dropNode_ok hop
    exact admissible_importNode h hr
  | adoptNode doc n =>
    obtain ⟨c, hr⟩ := dropNode_ok hop
    exact admissible_adoptNode h hr
  | createAttribute doc ln =>
    obtain ⟨a, hr⟩ := dropAttr_ok hop
    exact admissible_createAttribute h hr
  | createAttributeNS doc ns qn =>
    obtain ⟨a, hr⟩ := dropAttr_ok hop
    exact admissible_createAttributeNS h hr
  | getAttributeNode e qn =>
    simp only [applyOperation, Except.map] at hop
    split at hop
    · simp at hop
    · rw [← Except.ok.inj hop]; exact h
  | getAttributeNodeNS e ns ln =>
    simp only [applyOperation, Except.map] at hop
    split at hop
    · simp at hop
    · rw [← Except.ok.inj hop]; exact h
  | setAttributeNode e a =>
    obtain ⟨r, hr⟩ := dropAttr?_ok hop
    exact admissible_setAttributeNode h hr
  | removeAttributeNode e a =>
    obtain ⟨r, hr⟩ := dropAttr_ok hop
    exact admissible_removeAttributeNode h hr
  | removeNamedItem e qn =>
    obtain ⟨r, hr⟩ := dropAttr_ok hop
    exact admissible_removeNamedItem h hr
  | rangeSetStart i n o =>
    cases n with
    | none => simp [applyOperation, withNode] at hop
    | some n => exact admissible_rangeSetStart h hop
  | rangeSetEnd i n o =>
    cases n with
    | none => simp [applyOperation, withNode] at hop
    | some n => exact admissible_rangeSetEnd h hop
  | rangeSetStartSibling i n a =>
    cases n with
    | none => simp [applyOperation, withNode] at hop
    | some n => exact admissible_rangeSetStartSibling h hop
  | rangeSetEndSibling i n a =>
    cases n with
    | none => simp [applyOperation, withNode] at hop
    | some n => exact admissible_rangeSetEndSibling h hop
  | rangeCollapse i t => exact admissible_rangeCollapse h hop
  | rangeSelectNode i n =>
    cases n with
    | none => simp [applyOperation, withNode] at hop
    | some n => exact admissible_rangeSelectNode h hop
  | rangeSelectNodeContents i n =>
    cases n with
    | none => simp [applyOperation, withNode] at hop
    | some n => exact admissible_rangeSelectNodeContents h hop
  | rangeIsPointInRange i n o =>
    cases n with
    | none => simp [applyOperation, withNode] at hop
    | some n =>
      simp only [applyOperation, withNode, Except.map] at hop
      split at hop
      · simp at hop
      · rw [← Except.ok.inj hop]; exact h
  | rangeIntersectsNode i n =>
    cases n with
    | none => simp [applyOperation, withNode] at hop
    | some n =>
      simp only [applyOperation, withNode, Except.map] at hop
      split at hop
      · simp at hop
      · rw [← Except.ok.inj hop]; exact h
  | rangeCompareBoundaryPoints i how j =>
    simp only [applyOperation, Except.map] at hop
    split at hop
    · simp at hop
    · rw [← Except.ok.inj hop]; exact h
  | rangeComparePoint i n o =>
    cases n with
    | none => simp [applyOperation, withNode] at hop
    | some n =>
      simp only [applyOperation, withNode, Except.map] at hop
      split at hop
      · simp at hop
      · rw [← Except.ok.inj hop]; exact h
  | rangeDeleteContents i => exact admissible_rangeDeleteContents h hop
  | rangeInsertNode i n =>
    cases n with
    | none => simp [applyOperation, withNode] at hop
    | some n => exact admissible_rangeInsertNode h hop
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
  | getOwnerDocument n => exact admissible_requireNodes h hop
  | isEqualNode n o => exact admissible_requireNodes h hop
  | getTextContent n => exact admissible_requireNodes h hop
  | getNodeValue n => exact admissible_requireNodes h hop
  | getAttribute e q => exact admissible_requireNodes h hop
  | hasAttribute e q => exact admissible_requireNodes h hop
  | getAttributeNames e => exact admissible_requireNodes h hop
  | querySelector n sel => exact admissible_mapConst h hop
  | querySelectorAll n sel => exact admissible_mapConst h hop
  | matchesSelector e sel => exact admissible_mapConst h hop
  | closest e sel => exact admissible_mapConst h hop
  | getElementById n i => exact admissible_mapConst h hop
  | getElementsByClassName n c => exact admissible_mapConst h hop
  | getElementsByName n m => exact admissible_mapConst h hop
  | lookupNamespaceURI n p => exact admissible_requireNodes h hop
  | lookupPrefix n ns => exact admissible_requireNodes h hop
  | isDefaultNamespace n ns => exact admissible_requireNodes h hop
  | attrQuery a q => exact admissible_requireRefs h hop
  | compareDocumentPositionRef n o => exact admissible_requireRefs h hop
  | nodeContainsRef n o => exact admissible_requireRefs h hop
  | isEqualNodeRef n o => exact admissible_requireRefs h hop
  | nodeContainsNull n => exact admissible_requireRefs h hop
  | isEqualNodeNull n => exact admissible_requireRefs h hop
  | argumentTypeError _ => cases hop; exact h
  | appendChildRef p n => exact admissible_appendChildRef h hop
  | adoptAttr d a =>
    obtain ⟨r, hr⟩ := dropAttr_ok hop
    exact admissible_adoptAttr h hr
  | importAttr d a =>
    obtain ⟨r, hr⟩ := dropAttr_ok hop
    exact admissible_importAttr h hr
  | cloneAttr a =>
    obtain ⟨r, hr⟩ := dropAttr_ok hop
    exact admissible_cloneAttr h hr
  | setAttrValue a v via => exact admissible_setAttrValue h hop
  | attrLookupNamespaceURI a p => exact admissible_requireRefs h hop
  | attrLookupPrefix a ns => exact admissible_requireRefs h hop
  | attrIsDefaultNamespace a ns => exact admissible_requireRefs h hop
  | addEventListener t ty src o => exact admissible_addEventListener h hop
  | removeEventListener t ty cb o => exact admissible_removeEventListener h hop
  | dispatchEvent t ty b c =>
    -- `applyOperation` は戻り値と log を捨てるので、`Except.map` を剥がす。
    simp only [applyOperation, Except.map] at hop
    split at hop
    · simp at hop
    · next res he =>
      obtain ⟨s₁, r, log⟩ := res
      have : s₁ = s' := by simpa using hop
      subst this
      exact admissible_dispatchEvent h he
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
  | getReflected e p r => exact admissible_mapConst h hop
  | setReflected e p r v => exact admissible_setReflectedProp h hop
  | setReflectedBool e p r b => exact admissible_setReflectedBool h hop
  | datasetGet e n => exact admissible_mapConst h hop
  | datasetSet e n v => exact admissible_datasetSet h hop
  | datasetDelete e n => exact admissible_datasetDelete h hop
  | datasetKeys e => exact admissible_mapConst h hop
  | classListAdd e ts => exact admissible_classListAdd h hop
  | classListRemove e ts => exact admissible_classListRemove h hop
  | classListToggle e tok f =>
    simp only [applyOperation, Except.map] at hop
    split at hop
    · simp at hop
    · next res he =>
      obtain ⟨s₁, b⟩ := res
      have : s₁ = s' := by simpa using hop
      subst this
      exact admissible_classListToggle h he
  | classListReplace e tok nt =>
    simp only [applyOperation, Except.map] at hop
    split at hop
    · simp at hop
    · next res he =>
      obtain ⟨s₁, b⟩ := res
      have : s₁ = s' := by simpa using hop
      subst this
      exact admissible_classListReplace h he
  | classListContains e tok => exact admissible_mapConst h hop
  | childrenNamedItem n k => exact admissible_mapConst h hop
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
      have h' : AdmissibleDOMState s' := admissible_applyOperation h (applyOperation_of_invoke hop)
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
def run : DOMState → List Operation → Except IdlException DOMState
  | s, [] => .ok s
  | s, op :: ops =>
    match invokeOperation s op with
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
      exact run_preserves_admissibility ops (admissible_applyOperation h (applyOperation_of_invoke hop)) hr

/--
指定した初期状態の集合から public API だけで到達できる状態。

`AdmissibleDOMState` が **局所不変条件の閉包**であるのに対し、
こちらは **構成可能性**である。両者は別の概念なので混同しない
（`docs/status.md` の「admissibility」）。
-/
inductive ReachableFrom (initial : DOMState → Prop) : DOMState → Prop where
  | base {s : DOMState} : initial s → ReachableFrom initial s
  | step {s s' : DOMState} {op : Operation} :
      ReachableFrom initial s → invokeOperation s op = .ok s' → ReachableFrom initial s'

/-- admissible な初期状態から到達できる状態は admissible である。 -/
theorem reachable_admissible {initial : DOMState → Prop}
    (hinit : ∀ s, initial s → AdmissibleDOMState s) {s : DOMState}
    (hr : ReachableFrom initial s) : AdmissibleDOMState s := by
  induction hr with
  | base h => exact hinit _ h
  | step _ hop ih => exact admissible_applyOperation ih (applyOperation_of_invoke hop)

end Dom.Exec
