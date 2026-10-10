import Dom.Mutation.SetText
import Dom.Validity.Admissible
import Dom.Validity.Create
import Dom.Validity.AttrIdsAttr

/-!
# `textContent`・`nodeValue` の setter の妥当性

"string replace all" は parent が Element か DocumentFragment のときにだけ呼ぶ（"set text content" の
振り分け）。そのとき replace all の前提（parent は children を持て、Document ではない。入れる node は
Text）が満たされる。
-/

namespace Dom

/-- parent が Element か DocumentFragment である。 -/
def ElementOrFragment (t : Tree) (parent : NodeId) : Prop :=
  ∃ pd, t.get? parent = some pd ∧ (pd.kind = .element ∨ pd.kind = .documentFragment)

theorem admissible_stringReplaceAll {s s' : DOMState} {str : String} {parent : NodeId}
    (h : AdmissibleDOMState s) (hp : ElementOrFragment s.tree parent)
    (hr : stringReplaceAll s str parent = .ok s') : AdmissibleDOMState s' := by
  obtain ⟨pd, hpd, hpk⟩ := hp
  have hcan : pd.kind.canHaveChildren = true := by
    rcases hpk with hk | hk <;> simp [hk, NodeKind.canHaveChildren]
  unfold stringReplaceAll at hr
  rw [hpd] at hr
  simp only at hr
  split at hr
  · exact admissible_replaceAll h (fun _ hn => by cases hn) (fun _ hn => by cases hn)
      (fun _ hn => by cases hn) (fun _ _ hn => by cases hn) hr
  · split at hr
    · cases hr
    · next n s₁ hc =>
      have h₁ := admissible_createTextNode h hc
      have hadd := (createTextNode_creates hc).1
      have hne : parent ≠ n := hadd.ne_of_mem hpd
      have hpd₁ : s₁.tree.get? parent = some pd := by rw [hadd.others parent hne, hpd]
      refine admissible_replaceAll h₁ ?_ ?_ ?_ ?_ hr
      · intro m hm pd' hpd'
        cases hm
        rw [hpd₁] at hpd'
        cases hpd'
        exact hcan
      · intro m hm nd hnd
        cases hm
        rw [hadd.created] at hnd
        cases hnd
        simp
      · intro m hm nd hnd hk
        cases hm
        rw [hadd.created] at hnd
        cases hnd
        simp at hk
      · intro hdoc
        exfalso
        simp [kindOf, hpd₁] at hdoc
        rcases hpk with hk | hk <;> simp [hk] at hdoc

theorem unique_stringReplaceAll {s s' : DOMState} {str : String} {parent : NodeId}
    (hu : AttrIdsUnique s) (hr : stringReplaceAll s str parent = .ok s') : AttrIdsUnique s' := by
  unfold stringReplaceAll at hr
  split at hr
  · cases hr
  · split at hr
    · exact (attrFrame_replaceAll hr).unique hu
    · split at hr
      · cases hr
      · next n s₁ hc => exact (attrFrame_replaceAll hr).unique (unique_createTextNode hu hc)

theorem admissible_setTextContent {s s' : DOMState} {n : NodeId} {v : String}
    (h : AdmissibleDOMState s) (hr : setTextContent s n v = .ok s') : AdmissibleDOMState s' := by
  unfold setTextContent at hr
  split at hr
  · cases hr
  · next d hd =>
    split at hr
    · next hk =>
      refine admissible_stringReplaceAll h ⟨d, hd, ?_⟩ hr
      simpa [Bool.or_eq_true, beq_iff_eq, or_comm] using hk
    · split at hr
      · exact admissible_replaceData h hr
      · cases hr
        exact h

theorem unique_setTextContent {s s' : DOMState} {n : NodeId} {v : String}
    (hu : AttrIdsUnique s) (hr : setTextContent s n v = .ok s') : AttrIdsUnique s' := by
  unfold setTextContent at hr
  split at hr
  · cases hr
  · split at hr
    · exact unique_stringReplaceAll hu hr
    · split at hr
      · exact (attrFrame_replaceData hr).unique hu
      · cases hr
        exact hu

theorem admissible_setNodeValue {s s' : DOMState} {n : NodeId} {v : String}
    (h : AdmissibleDOMState s) (hr : setNodeValue s n v = .ok s') : AdmissibleDOMState s' := by
  unfold setNodeValue at hr
  split at hr
  · cases hr
  · split at hr
    · exact admissible_replaceData h hr
    · cases hr
      exact h

theorem unique_setNodeValue {s s' : DOMState} {n : NodeId} {v : String}
    (hu : AttrIdsUnique s) (hr : setNodeValue s n v = .ok s') : AttrIdsUnique s' := by
  unfold setNodeValue at hr
  split at hr
  · cases hr
  · split at hr
    · exact (attrFrame_replaceData hr).unique hu
    · cases hr
      exact hu

end Dom
