import Dom.Validity.DocumentTree
import Dom.Validity.AttributeList
import Dom.Range.BoundaryPoint
import Dom.Traversal.NodeIterator
import Dom.Observer.Record

/-!
# 状態の妥当性

`docs/status.md` の「admissibility」が立てた層の `AdmissibleDOMState`。

対象範囲の **局所不変条件** をすべて満たすことを表す。
公開 API から実際に構成できること（reachability）とは別物で、
そちらは `Dom/Exec/Invariant.lean` の `ReachableFrom` で扱う。

Range については両端が木の中にあることだけを要求する。
順序（`BoundaryLE`）は仕様の invariant ではない
（`docs/status.md` の「`insert` 側の `BoundaryLE` は保たれない」）。
-/

namespace Dom

/-- registration の node が、その observer の node list にある。 -/
def ListedIn (s : DOMState) (r : Registration) : Prop :=
  ∃ o, s.observers[r.observer]? = some o ∧ r.node ∈ o.nodeList

/--
MutationObserver の登録の整合性。

* registration が指す observer は `observers` の範囲内にある。
* registration が指す node は木の中にある。
* registration が指す node は、その observer の node list にある（`ListedIn`）。`observe()` は target を
  node list に足し、"add transient registered observers" は transient を置いた node を transient node set に足す
  （model の node list は二つを合わせたもの。`Dom/Observer/Deliver.lean` の冒頭）。notify step 6.3 と
  `disconnect()` step 1-2 は「node list（transient node set）の node から」外すので、この条件があれば
  「その observer の registration を全部外す」と同じになる。

transient registration は次の notify（"notify mutation observers" step 6.3）まで残るので、
その間も指す先が壊れていないことをここで要求する。
-/
def ObserverRegistrationsValid (s : DOMState) : Prop :=
  ∀ r ∈ s.registrations, r.observer < s.observers.length ∧ (s.tree.get? r.node).isSome ∧
    ListedIn s r

/-- 対象範囲の局所不変条件をすべて満たす状態。 -/
structure AdmissibleDOMState (s : DOMState) : Prop where
  structural : StructurallyValid s.tree
  nodeDocuments : NodeDocumentsValid s.tree
  documentTrees : DocumentTreesValid s.tree
  rangeEndpoints : RangeEndpointsValid s
  iterators : IteratorsValid s
  observerRegistrations : ObserverRegistrationsValid s
  attributes : AttributesValid s.tree

namespace AdmissibleDOMState

theorem wellFormed {s : DOMState} (h : AdmissibleDOMState s) : WellFormed s.tree :=
  h.structural.wellFormed

end AdmissibleDOMState

/-! ## 実行時の検査 -/

/--
`checkValidIterator` の健全性・完全性。

`isInclusiveAncestorOf` が `InclusiveAncestor` と一致するのは well-formed な木の上でなので、
`WellFormed` を仮定する。
-/
theorem checkValidIterator_iff {t : Tree} (hwf : WellFormed t) (it : IteratorState) :
    checkValidIterator t it = true ↔ ValidIterator t it := by
  simp only [checkValidIterator, ValidIterator, Bool.and_eq_true, Option.isSome_iff_exists,
    isInclusiveAncestorOf_iff hwf]

theorem checkIteratorsValid_iff {s : DOMState} (hwf : WellFormed s.tree) :
    checkIteratorsValid s = true ↔ IteratorsValid s := by
  simp only [checkIteratorsValid, IteratorsValid, List.all_eq_true, checkValidIterator_iff hwf]

def checkListedIn (s : DOMState) (r : Registration) : Bool :=
  match s.observers[r.observer]? with
  | none => false
  | some o => o.nodeList.contains r.node

theorem checkListedIn_iff (s : DOMState) (r : Registration) :
    checkListedIn s r = true ↔ ListedIn s r := by
  unfold checkListedIn ListedIn
  cases s.observers[r.observer]? <;> simp

def checkObserverRegistrationsValid (s : DOMState) : Bool :=
  s.registrations.all fun r =>
    r.observer < s.observers.length && (s.tree.get? r.node).isSome && checkListedIn s r

theorem checkObserverRegistrationsValid_iff (s : DOMState) :
    checkObserverRegistrationsValid s = true ↔ ObserverRegistrationsValid s := by
  simp only [checkObserverRegistrationsValid, ObserverRegistrationsValid, List.all_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, checkListedIn_iff, and_assoc]

def checkAdmissibleDOMState (s : DOMState) : Bool :=
  checkStructurallyValid s.tree && checkNodeDocumentsValid s.tree &&
    checkDocumentTreesValid s.tree && checkRangeEndpointsValid s &&
    checkIteratorsValid s && checkObserverRegistrationsValid s &&
    checkAttributesValid s.tree

/-- PLAN §3.5 の形の健全性・完全性。`AdmissibleDOMState` は決定可能である。 -/
theorem checkAdmissibleDOMState_iff (s : DOMState) :
    checkAdmissibleDOMState s = true ↔ AdmissibleDOMState s := by
  constructor
  · intro h
    simp only [checkAdmissibleDOMState, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
    have hs := (checkStructurallyValid_iff s.tree).mp h1
    exact ⟨hs, (checkNodeDocumentsValid_iff s.tree).mp h2,
      (checkDocumentTreesValid_iff s.tree).mp h3,
      (checkRangeEndpointsValid_iff s).mp h4,
      (checkIteratorsValid_iff hs.wellFormed).mp h5,
      (checkObserverRegistrationsValid_iff s).mp h6,
      (checkAttributesValid_iff s.tree).mp h7⟩
  · intro h
    simp only [checkAdmissibleDOMState, Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨⟨(checkStructurallyValid_iff s.tree).mpr h.structural,
      (checkNodeDocumentsValid_iff s.tree).mpr h.nodeDocuments⟩,
      (checkDocumentTreesValid_iff s.tree).mpr h.documentTrees⟩,
      (checkRangeEndpointsValid_iff s).mpr h.rangeEndpoints⟩,
      (checkIteratorsValid_iff h.wellFormed).mpr h.iterators⟩,
      (checkObserverRegistrationsValid_iff s).mpr h.observerRegistrations⟩,
      (checkAttributesValid_iff s.tree).mpr h.attributes⟩

end Dom
