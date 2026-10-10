import Dom.Mutation.InsertAdjacent
import Dom.Validity.Admissible
import Dom.Validity.Create
import Dom.Validity.AttrIdsAttr

/-!
# `insertAdjacentElement()`・`insertAdjacentText()` の妥当性

どの枝も pre-insert か「何もしない」なので、pre-insert の定理に帰着する。
-/

namespace Dom

/-- `inserted` が成功したなら、pre-insert が成功している。 -/
theorem insertAdjacent.inserted_ok {node : NodeId} {r : Except DOMException DOMState}
    {ret : Option NodeId} {s' : DOMState} (h : insertAdjacent.inserted node r = .ok (ret, s')) :
    r = .ok s' := by
  unfold insertAdjacent.inserted at h
  split at h
  · cases h
  · cases h; rfl

theorem admissible_insertAdjacent {s s' : DOMState} {element node : NodeId} {w : String}
    {r : Option NodeId} (h : AdmissibleDOMState s)
    (hr : insertAdjacent s element w node = .ok (r, s')) : AdmissibleDOMState s' := by
  unfold insertAdjacent at hr
  split at hr
  · cases hr
  · split at hr
    · cases hr; exact h
    · exact admissible_preInsert h (insertAdjacent.inserted_ok hr)
  · exact admissible_preInsert h (insertAdjacent.inserted_ok hr)
  · exact admissible_preInsert h (insertAdjacent.inserted_ok hr)
  · split at hr
    · cases hr; exact h
    · exact admissible_preInsert h (insertAdjacent.inserted_ok hr)

theorem unique_insertAdjacent {s s' : DOMState} {element node : NodeId} {w : String}
    {r : Option NodeId} (hu : AttrIdsUnique s)
    (hr : insertAdjacent s element w node = .ok (r, s')) : AttrIdsUnique s' := by
  unfold insertAdjacent at hr
  split at hr
  · cases hr
  · split at hr
    · cases hr; exact hu
    · exact (attrFrame_preInsert (insertAdjacent.inserted_ok hr)).unique hu
  · exact (attrFrame_preInsert (insertAdjacent.inserted_ok hr)).unique hu
  · exact (attrFrame_preInsert (insertAdjacent.inserted_ok hr)).unique hu
  · split at hr
    · cases hr; exact hu
    · exact (attrFrame_preInsert (insertAdjacent.inserted_ok hr)).unique hu

theorem admissible_insertAdjacentElement {s s' : DOMState} {element node : NodeId} {w : String}
    {r : Option NodeId} (h : AdmissibleDOMState s)
    (hr : insertAdjacentElement s element w node = .ok (r, s')) : AdmissibleDOMState s' := by
  unfold insertAdjacentElement at hr
  split at hr
  · cases hr
  · exact admissible_insertAdjacent h hr

theorem unique_insertAdjacentElement {s s' : DOMState} {element node : NodeId} {w : String}
    {r : Option NodeId} (hu : AttrIdsUnique s)
    (hr : insertAdjacentElement s element w node = .ok (r, s')) : AttrIdsUnique s' := by
  unfold insertAdjacentElement at hr
  split at hr
  · cases hr
  · exact unique_insertAdjacent hu hr

theorem admissible_insertAdjacentText {s s' : DOMState} {element : NodeId} {w data : String}
    (h : AdmissibleDOMState s) (hr : insertAdjacentText s element w data = .ok s') :
    AdmissibleDOMState s' := by
  unfold insertAdjacentText at hr
  split at hr
  · cases hr
  · split at hr
    · cases hr
    · next t s₁ hc =>
      split at hr
      · cases hr
      · cases hr; exact h
      · next r s₂ hi =>
        cases hr
        exact admissible_insertAdjacent (admissible_createTextNode h hc) hi

theorem unique_insertAdjacentText {s s' : DOMState} {element : NodeId} {w data : String}
    (hu : AttrIdsUnique s) (hr : insertAdjacentText s element w data = .ok s') :
    AttrIdsUnique s' := by
  unfold insertAdjacentText at hr
  split at hr
  · cases hr
  · split at hr
    · cases hr
    · next t s₁ hc =>
      split at hr
      · cases hr
      · cases hr; exact hu
      · next r s₂ hi =>
        cases hr
        exact unique_insertAdjacent (unique_createTextNode hu hc) hi

end Dom
