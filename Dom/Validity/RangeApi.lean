import Dom.Validity.Admissible
import Dom.Range.Api

/-!
# `Range` の API が `AdmissibleDOMState` を保つこと

boundary point を動かす method はどれも `ranges` の一要素を差し替えるだけなので、
保存は「差し替えた range の両端が木の中にある」ことに尽きる（`admissible_withRange`）。

新しい端点の妥当性の出どころは三つある。`setStart` / `setEnd` は仕様の step 1-2 の
検査（`rangeBoundaryError`）から、`collapse` は元の range から、
`selectNode` は「子の index は parent の length 未満」から出る。
-/

namespace Dom

/-- 差し替えた要素か、元からあった要素か。 -/
theorem mem_set {α : Type} : ∀ (l : List α) (i : Nat) (b x : α), x ∈ l.set i b → x = b ∨ x ∈ l
  | [], _, _, _, h => by simp at h
  | a :: t, 0, b, x, h => by
    simp only [List.set] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (List.mem_cons_of_mem _ h)
  | a :: t, n + 1, b, x, h => by
    simp only [List.set] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inr List.mem_cons_self
    · rcases mem_set t n b x h with rfl | h2
      · exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem _ h2)

/-- range を一つ差し替える操作は、その端点が妥当なら admissibility を保つ。 -/
theorem admissible_withRange {s : DOMState} {i : Nat} {r : RangeState}
    (h : AdmissibleDOMState s) (hr : EndpointsValid s.tree r) :
    AdmissibleDOMState (withRange s i r) := by
  refine ⟨h.structural, h.nodeDocuments, h.documentTrees, ?_, h.iterators,
    h.observerRegistrations, h.attributes⟩
  intro r' hr'
  rcases mem_set s.ranges i r r' hr' with rfl | hmem
  · exact hr
  · exact h.rangeEndpoints r' hmem

/-- `rangeBoundaryError` が `none` なら、その boundary point は妥当である。 -/
theorem validBoundaryPoint_of_rangeBoundaryError {t : Tree} {bp : BoundaryPoint}
    (h : rangeBoundaryError t bp = none) : ValidBoundaryPoint t bp := by
  unfold rangeBoundaryError at h
  split at h
  · simp at h
  · next d hd =>
    split at h
    · simp at h
    · split at h
      · simp at h
      · next hlen => exact ⟨d, hd, by omega⟩

/-- `setStart` は admissibility を保つ。 -/
theorem admissible_rangeSetStart {s s' : DOMState} {i : Nat} {bp : BoundaryPoint}
    (h : AdmissibleDOMState s) (hr : rangeSetStart s i bp = .ok s') : AdmissibleDOMState s' := by
  unfold rangeSetStart at hr
  split at hr
  · simp at hr
  · next r hrr =>
    split at hr
    · simp at hr
    · next he =>
      rw [← Except.ok.inj hr]
      have hbp := validBoundaryPoint_of_rangeBoundaryError he
      have hend := (h.rangeEndpoints r (List.mem_of_getElem? hrr)).2
      refine admissible_withRange h ?_
      unfold setStartBP
      split
      · exact ⟨hbp, hbp⟩
      · exact ⟨hbp, hend⟩

/-- `setEnd` も同じ。 -/
theorem admissible_rangeSetEnd {s s' : DOMState} {i : Nat} {bp : BoundaryPoint}
    (h : AdmissibleDOMState s) (hr : rangeSetEnd s i bp = .ok s') : AdmissibleDOMState s' := by
  unfold rangeSetEnd at hr
  split at hr
  · simp at hr
  · next r hrr =>
    split at hr
    · simp at hr
    · next he =>
      rw [← Except.ok.inj hr]
      have hbp := validBoundaryPoint_of_rangeBoundaryError he
      have hstart := (h.rangeEndpoints r (List.mem_of_getElem? hrr)).1
      refine admissible_withRange h ?_
      unfold setEndBP
      split
      · exact ⟨hbp, hbp⟩
      · exact ⟨hstart, hbp⟩

theorem admissible_rangeSetStartSibling {s s' : DOMState} {i : Nat} {n : NodeId} {a : Bool}
    (h : AdmissibleDOMState s) (hr : rangeSetStartSibling s i n a = .ok s') :
    AdmissibleDOMState s' := by
  unfold rangeSetStartSibling at hr
  split at hr
  · simp at hr
  · exact admissible_rangeSetStart h hr

theorem admissible_rangeSetEndSibling {s s' : DOMState} {i : Nat} {n : NodeId} {a : Bool}
    (h : AdmissibleDOMState s) (hr : rangeSetEndSibling s i n a = .ok s') :
    AdmissibleDOMState s' := by
  unfold rangeSetEndSibling at hr
  split at hr
  · simp at hr
  · exact admissible_rangeSetEnd h hr

/-- `collapse` は片方の端点を両端に置くので、妥当さはそのまま移る。 -/
theorem admissible_rangeCollapse {s s' : DOMState} {i : Nat} {toStart : Bool}
    (h : AdmissibleDOMState s) (hr : rangeCollapse s i toStart = .ok s') :
    AdmissibleDOMState s' := by
  unfold rangeCollapse at hr
  split at hr
  · simp at hr
  · next r hrr =>
    rw [← Except.ok.inj hr]
    have hv := h.rangeEndpoints r (List.mem_of_getElem? hrr)
    refine admissible_withRange h ?_
    split
    · exact ⟨hv.1, hv.1⟩
    · exact ⟨hv.2, hv.2⟩

/-- `selectNode` は parent の中の位置を両端にする。 -/
theorem admissible_rangeSelectNode {s s' : DOMState} {i : Nat} {n : NodeId}
    (h : AdmissibleDOMState s) (hr : rangeSelectNode s i n = .ok s') : AdmissibleDOMState s' := by
  unfold rangeSelectNode at hr
  split at hr
  · simp at hr
  · split at hr
    · next p idx hp hidx =>
      rw [← Except.ok.inj hr]
      have hlen : ChildCountKind s.tree p := h.childCountKind hp
      have hilt : idx < (childrenOf s.tree p).length := index_lt_children_length hp hidx
      obtain ⟨pd, hpd⟩ : ∃ pd, s.tree.get? p = some pd :=
        exists_data_of_parentOf h.wellFormed hp
      have hpl : pd.length = (childrenOf s.tree p).length := by
        have := lengthOf_eq_children hlen
        unfold lengthOf at this
        rw [hpd] at this
        exact this
      refine admissible_withRange h ⟨⟨pd, hpd, ?_⟩, ⟨pd, hpd, ?_⟩⟩
      · show idx ≤ pd.length
        omega
      · show idx + 1 ≤ pd.length
        omega
    · simp at hr

/-- `selectNodeContents` は node の中の全体を指す。 -/
theorem admissible_rangeSelectNodeContents {s s' : DOMState} {i : Nat} {n : NodeId}
    (h : AdmissibleDOMState s) (hr : rangeSelectNodeContents s i n = .ok s') :
    AdmissibleDOMState s' := by
  unfold rangeSelectNodeContents at hr
  split at hr
  · simp at hr
  · simp at hr
  · next d hrr hd =>
    split at hr
    · simp at hr
    · rw [← Except.ok.inj hr]
      refine admissible_withRange h ⟨⟨d, hd, ?_⟩, ⟨d, hd, ?_⟩⟩
      · show (0 : Nat) ≤ d.length
        omega
      · show d.length ≤ d.length
        omega

end Dom
