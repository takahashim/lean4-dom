import Dom.Exec.Invariant
import Dom.Validity.AttrIdsOps
import Dom.Validity.AttrIdsAttr

/-!
# 操作列は attribute の id の一意性を保つ

`Dom/Exec/Invariant.lean` の `admissible_applyOperation` と同じ形で、
admissible な状態で attribute の id が一意なら、どの操作の後も一意であることを示す。
admissibility は `AttributesValid`（attribute の鍵が element ごとに一意）を使うために要る。
-/

namespace Dom.Exec

open Dom

/-- 値を返すだけの操作は状態を変えない。 -/
private theorem unique_of_eq {s s' : DOMState} (hu : AttrIdsUnique s) (h : s = s') :
    AttrIdsUnique s' := h ▸ hu

private theorem unique_requireNodes {s s' : DOMState} {ns : List NodeId} (hu : AttrIdsUnique s)
    (h : requireNodes s ns = .ok s') : AttrIdsUnique s' := by
  unfold requireNodes at h
  split at h
  · cases h; exact hu
  · cases h

private theorem unique_requireRefs {s s' : DOMState} {rs : List NodeRef} (hu : AttrIdsUnique s)
    (h : requireRefs s rs = .ok s') : AttrIdsUnique s' := by
  unfold requireRefs at h
  split at h
  · cases h; exact hu
  · cases h

private theorem unique_mapConst {α : Type} {s s' : DOMState} {r : Except DOMException α}
    (hu : AttrIdsUnique s) (h : r.map (fun _ => s) = .ok s') : AttrIdsUnique s' := by
  cases r with
  | error e => cases h
  | ok a => cases h; exact hu

private theorem unique_stepIterator {s : DOMState} (hu : AttrIdsUnique s) (i : Nat)
    (f : Tree → IteratorState → Option (NodeId × IteratorState)) :
    AttrIdsUnique (stepIterator s i f).1 := by
  unfold stepIterator
  split
  · exact hu
  · split
    · exact hu
    · next it _ n it' _ =>
      exact (AttrFrame.of_eq (s := s) (s' := { s with iterators := s.iterators.set i it' })
        rfl rfl).unique hu

/-- **admissible で attribute の id が一意な状態に操作を当てても、一意のままである。** -/
theorem attrIdsUnique_applyOperation {s s' : DOMState} {op : Operation}
    (h : AdmissibleDOMState s) (hu : AttrIdsUnique s) (hop : applyOperation s op = .ok s') :
    AttrIdsUnique s' := by
  cases op with
  | appendChild p n => exact (attrFrame_appendChild hop).unique hu
  | insertBefore p n c => exact (attrFrame_insertBefore hop).unique hu
  | replaceChild p n c => exact (attrFrame_replaceChild hop).unique hu
  | removeChild p n => exact (attrFrame_removeChild hop).unique hu
  | replaceChildren p ns =>
    exact ((closed_replaceChildrenNodes good_variadicClosed ⟨h, hu⟩ _ _).1 s' (dropState_ok hop)).2
  | prepend p ns =>
    exact ((closed_prependNodes good_variadicClosed ⟨h, hu⟩ _ _).1 s' (dropState_ok hop)).2
  | append p ns =>
    exact ((closed_appendNodes good_variadicClosed ⟨h, hu⟩ _ _).1 s' (dropState_ok hop)).2
  | before tgt ns =>
    exact ((closed_beforeNodes good_variadicClosed ⟨h, hu⟩ _ _).1 s' (dropState_ok hop)).2
  | after tgt ns =>
    exact ((closed_afterNodes good_variadicClosed ⟨h, hu⟩ _ _).1 s' (dropState_ok hop)).2
  | replaceWith tgt ns =>
    exact ((closed_replaceWithNodes good_variadicClosed ⟨h, hu⟩ _ _).1 s' (dropState_ok hop)).2
  | remove tgt => exact (attrFrame_nodeRemove hop).unique hu
  | moveBefore p n c => exact (attrFrame_moveBefore hop).unique hu
  | iteratorNext i => rw [← Except.ok.inj hop]; exact unique_stepIterator hu i _
  | iteratorPrevious i => rw [← Except.ok.inj hop]; exact unique_stepIterator hu i _
  | replaceData n o c d => exact (attrFrame_replaceData hop).unique hu
  | appendData n d => exact (attrFrame_appendData hop).unique hu
  | insertData n o d => exact (attrFrame_replaceData hop).unique hu
  | deleteData n o c => exact (attrFrame_replaceData hop).unique hu
  | setData n d => exact (attrFrame_setData hop).unique hu
  | normalize tgt => exact (attrFrame_normalize hop).unique hu
  | createElement doc ln =>
    obtain ⟨n, hr⟩ := dropNode_ok hop; exact unique_createElement hu hr
  | createElementNS doc ns qn =>
    obtain ⟨n, hr⟩ := dropNode_ok hop; exact unique_createElementNS hu hr
  | createTextNode doc d =>
    obtain ⟨n, hr⟩ := dropNode_ok hop; exact unique_createTextNode hu hr
  | createComment doc d =>
    obtain ⟨n, hr⟩ := dropNode_ok hop; exact unique_createComment hu hr
  | createDocumentFragment doc =>
    obtain ⟨n, hr⟩ := dropNode_ok hop; exact unique_createDocumentFragment hu hr
  | cloneNode n deep =>
    obtain ⟨c, hr⟩ := dropNode_ok hop; exact unique_cloneNode hu hr
  | importNode doc n deep =>
    obtain ⟨c, hr⟩ := dropNode_ok hop; exact unique_importNode hu hr
  | adoptNode doc n =>
    obtain ⟨c, hr⟩ := dropNode_ok hop; exact (attrFrame_adoptNode hr).unique hu
  | createAttribute doc ln =>
    obtain ⟨a, hr⟩ := dropAttr_ok hop; exact unique_createAttribute hu hr
  | createAttributeNS doc ns qn =>
    obtain ⟨a, hr⟩ := dropAttr_ok hop; exact unique_createAttributeNS hu hr
  | getAttributeNode e qn => exact unique_mapConst hu hop
  | getAttributeNodeNS e ns ln => exact unique_mapConst hu hop
  | setAttributeNode e a =>
    obtain ⟨r, hr⟩ := dropAttr?_ok hop; exact unique_setAttributeNode hu h.attributes hr
  | removeAttributeNode e a =>
    obtain ⟨r, hr⟩ := dropAttr_ok hop; exact unique_removeAttributeNode hu h.attributes hr
  | removeNamedItem e qn =>
    obtain ⟨r, hr⟩ := dropAttr_ok hop; exact unique_removeNamedItem hu h.attributes hr
  | rangeSetStart i n o =>
    cases n with
    | none => simp [applyOperation, withNode] at hop
    | some n => exact (attrFrame_rangeSetStart hop).unique hu
  | rangeSetEnd i n o =>
    cases n with
    | none => simp [applyOperation, withNode] at hop
    | some n => exact (attrFrame_rangeSetEnd hop).unique hu
  | rangeSetStartSibling i n a =>
    cases n with
    | none => simp [applyOperation, withNode] at hop
    | some n => exact (attrFrame_rangeSetStartSibling hop).unique hu
  | rangeSetEndSibling i n a =>
    cases n with
    | none => simp [applyOperation, withNode] at hop
    | some n => exact (attrFrame_rangeSetEndSibling hop).unique hu
  | rangeCollapse i t => exact (attrFrame_rangeCollapse hop).unique hu
  | rangeSelectNode i n =>
    cases n with
    | none => simp [applyOperation, withNode] at hop
    | some n => exact (attrFrame_rangeSelectNode hop).unique hu
  | rangeSelectNodeContents i n =>
    cases n with
    | none => simp [applyOperation, withNode] at hop
    | some n => exact (attrFrame_rangeSelectNodeContents hop).unique hu
  | rangeIsPointInRange i n o =>
    cases n with
    | none => simp [applyOperation, withNode] at hop
    | some n => exact unique_mapConst hu hop
  | rangeIntersectsNode i n =>
    cases n with
    | none => simp [applyOperation, withNode] at hop
    | some n => exact unique_mapConst hu hop
  | rangeCompareBoundaryPoints i how j => exact unique_mapConst hu hop
  | rangeComparePoint i n o =>
    cases n with
    | none => simp [applyOperation, withNode] at hop
    | some n => exact unique_mapConst hu hop
  | rangeDeleteContents i => exact (attrFrame_rangeDeleteContents hop).unique hu
  | rangeInsertNode i n =>
    cases n with
    | none => simp [applyOperation, withNode] at hop
    | some n => exact (attrFrame_rangeInsertNode hop).unique hu
  | walkerMove i m =>
    simp only [applyOperation, Except.map] at hop
    split at hop
    · simp at hop
    · next res he =>
      obtain ⟨r, s₁⟩ := res
      have : s₁ = s' := by simpa using hop
      subst this
      exact (attrFrame_walkerStep he).unique hu
  | rangeToString i => exact unique_mapConst hu hop
  | substringData n o c => exact unique_mapConst hu hop
  | compareDocumentPosition n o => exact unique_requireNodes hu hop
  | nodeContains n o => exact unique_requireNodes hu hop
  | getRootNode n => exact unique_requireNodes hu hop
  | isEqualNode n o => exact unique_requireNodes hu hop
  | getTextContent n => exact unique_requireNodes hu hop
  | getNodeValue n => exact unique_requireNodes hu hop
  | getAttribute e q => exact unique_requireNodes hu hop
  | hasAttribute e q => exact unique_requireNodes hu hop
  | getAttributeNames e => exact unique_requireNodes hu hop
  | querySelector n sel => exact unique_mapConst hu hop
  | querySelectorAll n sel => exact unique_mapConst hu hop
  | matchesSelector e sel => exact unique_mapConst hu hop
  | closest e sel => exact unique_mapConst hu hop
  | getElementById n i => exact unique_mapConst hu hop
  | getElementsByClassName n c => exact unique_mapConst hu hop
  | getElementsByName n m => exact unique_mapConst hu hop
  | lookupNamespaceURI n p => exact unique_requireNodes hu hop
  | lookupPrefix n ns => exact unique_requireNodes hu hop
  | isDefaultNamespace n ns => exact unique_requireNodes hu hop
  | attrQuery a q => exact unique_requireRefs hu hop
  | compareDocumentPositionRef n o => exact unique_requireRefs hu hop
  | nodeContainsRef n o => exact unique_requireRefs hu hop
  | isEqualNodeRef n o => exact unique_requireRefs hu hop
  | appendChildRef p n =>
    simp only [applyOperation] at hop
    unfold appendChildRef at hop
    repeat' split at hop
    all_goals first
      | exact (attrFrame_appendChild hop).unique hu
      | (cases hop; done)
      | simp at hop
  | adoptAttr d a =>
    obtain ⟨r, hr⟩ := dropAttr_ok hop; exact unique_adoptAttr hu hr
  | importAttr d a =>
    obtain ⟨r, hr⟩ := dropAttr_ok hop; exact unique_importAttr hu h.attributes hr
  | cloneAttr a =>
    obtain ⟨r, hr⟩ := dropAttr_ok hop; exact unique_cloneAttr hu h.attributes hr
  | setAttrValue a v via => exact unique_setAttrValue hu hop
  | attrLookupNamespaceURI a p => exact unique_requireRefs hu hop
  | attrLookupPrefix a ns => exact unique_requireRefs hu hop
  | attrIsDefaultNamespace a ns => exact unique_requireRefs hu hop
  | addEventListener t ty src cap once => exact (attrFrame_addEventListener hop).unique hu
  | removeEventListener t ty cb cap => exact (attrFrame_removeEventListener hop).unique hu
  | dispatchEvent t ty b c =>
    simp only [applyOperation, Except.map] at hop
    split at hop
    · simp at hop
    · next res he =>
      obtain ⟨s₁, r, log⟩ := res
      have : s₁ = s' := by simpa using hop
      subst this
      exact (attrFrame_dispatchEvent he).unique hu
  | setAttribute e qn v => exact unique_setAttribute hu hop
  | setAttributeNS e ns qn v => exact unique_setAttributeNS hu hop
  | removeAttribute e qn => exact unique_removeAttribute hu hop
  | removeAttributeNS e ns ln => exact unique_removeAttributeNS hu hop
  | toggleAttribute e qn f =>
    simp only [applyOperation, Except.map] at hop
    split at hop
    · simp at hop
    · next res he =>
      obtain ⟨s₁, b⟩ := res
      have : s₁ = s' := by simpa using hop
      subst this
      exact unique_toggleAttribute hu he
  | getReflected e p r => exact unique_mapConst hu hop
  | setReflected e p r v => exact unique_setReflectedProp hu hop
  | setReflectedBool e p r b => exact unique_setReflectedBool hu hop
  | datasetGet e n => exact unique_mapConst hu hop
  | datasetSet e n v => exact unique_datasetSet hu hop
  | datasetDelete e n => exact unique_datasetDelete hu hop
  | datasetKeys e => exact unique_mapConst hu hop
  | classListAdd e ts => exact unique_classListAdd hu hop
  | classListRemove e ts => exact unique_classListRemove hu hop
  | classListToggle e tok f =>
    simp only [applyOperation, Except.map] at hop
    split at hop
    · simp at hop
    · next res he =>
      obtain ⟨s₁, b⟩ := res
      have : s₁ = s' := by simpa using hop
      subst this
      exact unique_classListToggle hu he
  | classListReplace e tok nt =>
    simp only [applyOperation, Except.map] at hop
    split at hop
    · simp at hop
    · next res he =>
      obtain ⟨s₁, b⟩ := res
      have : s₁ = s' := by simpa using hop
      subst this
      exact unique_classListReplace hu he
  | classListContains e tok => exact unique_mapConst hu hop
  | childrenNamedItem n k => exact unique_mapConst hu hop
  | observe mo target opts => exact (attrFrame_observe hop).unique hu
  | disconnect mo => rw [← Except.ok.inj hop]; exact (attrFrame_disconnect s mo).unique hu
  | takeRecords mo => rw [← Except.ok.inj hop]; exact (attrFrame_takeRecords s mo).unique hu
  | notify => rw [← Except.ok.inj hop]; exact (attrFrame_notifyMutationObservers s).unique hu

/-! ## 操作列と到達可能性 -/

/-- 有限の操作列は admissibility と attribute の id の一意性を保つ。 -/
theorem run_preserves_attrIdsUnique :
    ∀ (ops : List Operation) {s s' : DOMState},
      AdmissibleDOMState s → AttrIdsUnique s → run s ops = .ok s' → AttrIdsUnique s'
  | [], _, _, _, hu, hr => by rw [run] at hr; rw [← Except.ok.inj hr]; exact hu
  | op :: ops, s, s', h, hu, hr => by
    rw [run] at hr
    split at hr
    · simp at hr
    · next s₁ hop =>
      exact run_preserves_attrIdsUnique ops (admissible_applyOperation h (applyOperation_of_invoke hop))
        (attrIdsUnique_applyOperation h hu (applyOperation_of_invoke hop)) hr

/-- admissible で id が一意な初期状態から到達できる状態では、id は一意である。 -/
theorem reachable_attrIdsUnique {initial : DOMState → Prop}
    (hinit : ∀ s, initial s → AdmissibleDOMState s ∧ AttrIdsUnique s) {s : DOMState}
    (hr : ReachableFrom initial s) : AdmissibleDOMState s ∧ AttrIdsUnique s := by
  induction hr with
  | base h => exact hinit _ h
  | step _ hop ih =>
    exact ⟨admissible_applyOperation ih.1 (applyOperation_of_invoke hop),
      attrIdsUnique_applyOperation ih.1 ih.2 (applyOperation_of_invoke hop)⟩

end Dom.Exec
