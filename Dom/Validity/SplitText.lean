import Dom.CharacterData.SplitText
import Dom.Validity.Admissible
import Dom.Validity.Create
import Dom.Validity.AttrIdsAttr

/-!
# `splitText()` の妥当性

createTextNode → pre-insert → range の調整 → replace data の順で、range の調整は妥当な先にしか
動かさない（`splitTextBP`）ので、それぞれの定理をつなぐ。
-/

namespace Dom

theorem validBoundaryPoint_splitTextBP {t : Tree} {node newNode parent : NodeId} {offset idx : Nat}
    {bp : BoundaryPoint} (h : ValidBoundaryPoint t bp) :
    ValidBoundaryPoint t (splitTextBP t node newNode parent offset idx bp) := by
  unfold splitTextBP guardBP
  split
  · next hc => exact (checkValidBoundaryPoint_iff t _).mp hc
  · exact h

theorem endpointsValid_splitTextAdjust {s : DOMState} {node newNode parent : NodeId}
    {offset : Nat} (h : RangeEndpointsValid s) :
    RangeEndpointsValid (splitTextAdjust s node newNode parent offset) := by
  intro r hr
  simp only [splitTextAdjust] at hr
  simp only [List.mem_map] at hr
  obtain ⟨r₀, hr₀, rfl⟩ := hr
  obtain ⟨hs, he⟩ := h r₀ hr₀
  exact ⟨validBoundaryPoint_splitTextBP hs, validBoundaryPoint_splitTextBP he⟩

theorem admissible_splitText {s s' : DOMState} {node newNode : NodeId} {offset : Nat}
    (h : AdmissibleDOMState s) (hr : splitText s node offset = .ok (newNode, s')) :
    AdmissibleDOMState s' := by
  unfold splitText at hr
  split at hr
  · cases hr
  · split at hr
    · cases hr
    · split at hr
      · cases hr
      · split at hr
        · cases hr
        · split at hr
          · cases hr
          · next n s₁ hc =>
            have h₁ := admissible_createTextNode h hc
            split at hr
            · split at hr
              · cases hr
              · next s₄ hrep =>
                cases hr
                exact admissible_replaceData h₁ hrep
            · split at hr
              · cases hr
              · next s₂ hpre =>
                have h₂ := admissible_preInsert h₁ hpre
                split at hr
                · cases hr
                · next s₄ hrep =>
                  cases hr
                  refine admissible_replaceData ?_ hrep
                  exact ⟨h₂.structural, h₂.nodeDocuments, h₂.documentTrees,
                    endpointsValid_splitTextAdjust h₂.rangeEndpoints, h₂.iterators,
                    h₂.observerRegistrations, h₂.attributes⟩

theorem unique_splitText {s s' : DOMState} {node newNode : NodeId} {offset : Nat}
    (hu : AttrIdsUnique s) (hr : splitText s node offset = .ok (newNode, s')) :
    AttrIdsUnique s' := by
  unfold splitText at hr
  split at hr
  · cases hr
  · split at hr
    · cases hr
    · split at hr
      · cases hr
      · split at hr
        · cases hr
        · split at hr
          · cases hr
          · next n s₁ hc =>
            have hu₁ := unique_createTextNode hu hc
            split at hr
            · split at hr
              · cases hr
              · next s₄ hrep =>
                cases hr
                exact (attrFrame_replaceData hrep).unique hu₁
            · next parent hpar =>
              split at hr
              · cases hr
              · next s₂ hpre =>
                have hu₂ := (attrFrame_preInsert hpre).unique hu₁
                split at hr
                · cases hr
                · next s₄ hrep =>
                  cases hr
                  have hf : AttrFrame s₂ (splitTextAdjust s₂ node newNode parent offset) :=
                    AttrFrame.of_eq (by unfold splitTextAdjust; rfl) (by unfold splitTextAdjust; rfl)
                  exact (attrFrame_replaceData hrep).unique (hf.unique hu₂)

end Dom
