import Dom.Properties.Tree

/-!
# 構造上の妥当性

`WellFormed`（parent と children の整合、children の重複禁止、非循環性、
node document が Document であること）に、**kind から来る構造制約** を重ねる。

`notes/research-foundation-roadmap.md` §4 の `StructurallyValid` である。
`WellFormed` は一般的な木の整合性なのでそのまま残し、
DOM 固有の妥当性はこの層から上に足していく。
-/

namespace Dom

/--
kind から決まる構造制約。

* Document は parent を持たない（tree order の root であるため）。
* children を持てるのは Document / DocumentFragment / Element だけである
  （§4.2.3 "ensure pre-insertion validity" step 1 が parent に許す種別）。
  したがって CharacterData と DocumentType の children は常に空である。
-/
structure StructurallyValid (t : Tree) : Prop where
  wellFormed : WellFormed t
  documentHasNoParent : ∀ n d, t.get? n = some d → d.kind = .document → d.parent = none
  childrenOnlyUnderContainers :
    ∀ n d, t.get? n = some d → d.children ≠ [] → d.kind.canHaveChildren = true

namespace StructurallyValid

/-- leaf の children は空である。`childrenOnlyUnderContainers` の対偶。 -/
theorem children_eq_nil {t : Tree} (h : StructurallyValid t) {n : NodeId} {d : NodeData}
    (hn : t.get? n = some d) (hk : d.kind.canHaveChildren = false) : d.children = [] := by
  by_cases hc : d.children = []
  · exact hc
  · exact absurd (h.childrenOnlyUnderContainers n d hn hc) (by rw [hk]; simp)

/-- leaf は parent になれない。 -/
theorem canHaveChildren_of_parentOf {t : Tree} (h : StructurallyValid t) {c p : NodeId}
    {pd : NodeData} (hp : parentOf t c = some p) (hpd : t.get? p = some pd) :
    pd.kind.canHaveChildren = true := by
  refine h.childrenOnlyUnderContainers p pd hpd ?_
  intro hnil
  obtain ⟨cd, hcd, hcdp⟩ := parentOf_eq_some hp
  obtain ⟨pd', hpd', hmem⟩ := h.wellFormed.child_parent c cd p hcd hcdp
  rw [hpd] at hpd'
  cases hpd'
  rw [hnil] at hmem
  simp at hmem

/-- Document は root である。 -/
theorem parentOf_document {t : Tree} (h : StructurallyValid t) {n : NodeId} {d : NodeData}
    (hn : t.get? n = some d) (hk : d.kind = .document) : parentOf t n = none := by
  simp [parentOf, hn, h.documentHasNoParent n d hn hk]

end StructurallyValid

/-! ## 実行時の検査 -/

def checkStructurallyValid (t : Tree) : Bool :=
  t.checkWellFormed &&
    t.nodes.checkAll fun _ d =>
      (!(d.kind == .document) || d.parent.isNone) &&
        (d.children.isEmpty || d.kind.canHaveChildren)

theorem checkStructurallyValid_iff (t : Tree) :
    checkStructurallyValid t = true ↔ StructurallyValid t := by
  simp only [checkStructurallyValid, Bool.and_eq_true, checkWellFormed_iff,
    NodeStore.checkAll_iff]
  constructor
  · rintro ⟨hwf, hall⟩
    refine ⟨hwf, ?_, ?_⟩
    · intro n d hn hk
      have := hall n d hn
      simp only [hk] at this
      simpa using this.1
    · intro n d hn hc
      have := hall n d hn
      simp only [Bool.or_eq_true] at this
      rcases this.2 with he | hk
      · exact absurd (List.isEmpty_iff.mp he) hc
      · exact hk
  · intro h
    refine ⟨h.wellFormed, ?_⟩
    intro n d hn
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne]
    constructor
    · by_cases hk : d.kind = NodeKind.document
      · exact Or.inr (by simp [h.documentHasNoParent n d hn hk])
      · exact Or.inl (by simpa using hk)
    · by_cases hc : d.children = []
      · exact Or.inl (by simp [hc])
      · exact Or.inr (h.childrenOnlyUnderContainers n d hn hc)

end Dom
