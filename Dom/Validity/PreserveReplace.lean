import Dom.Validity.PreserveInsertDocument

/-!
# `replace` による保存
-/

namespace Dom

/-! ## replace -/

/--
`replace` は adopt → （必要なら）child の remove → insert という三段である。

`ensure pre-insertion validity` は元の tree に対して `child` を除外して走るので、
`insert` に渡す前提は kind に関する三つの事実として持ち回る。
-/
theorem structurallyValid_replace {s s' : DOMState} {child node parent : NodeId}
    (hwf : WellFormed s.tree) (h : StructurallyValid s.tree)
    (hr : replace s child node parent = .ok s') : StructurallyValid s'.tree := by
  obtain ⟨pd, s₁, s₂, s₃, hv, hpd, ha, hrm, hi, hs⟩ := replace_cases hr
  have hwf₁ := adopt_preserves_wellformed hwf (isDocument_ownerDocument hwf hpd) ha
  have h₁ : StructurallyValid s₁.tree := structurallyValid_adopt h
    (isDocument_ownerDocument hwf hpd) ha
  have hkp₁ : ShapePreserving s.tree s₁.tree := shapePreserving_adopt ha
  have hstep : StructurallyValid s₂.tree ∧ ShapePreserving s₁.tree s₂.tree ∧
      WellFormed s₂.tree := by
    rcases hrm with ⟨_, rfl⟩ | ⟨_, hrm'⟩
    · exact ⟨h₁, ShapePreserving.refl _, hwf₁⟩
    · exact ⟨structurallyValid_remove h₁ hrm', shapePreserving_remove hrm',
        remove_preserves_wellformed hwf₁ hrm'⟩
  obtain ⟨h₂, hkp₂, hwf₂⟩ := hstep
  have hkp : ShapePreserving s.tree s₂.tree := hkp₁.trans hkp₂
  have f1 := kindFact_of_kindPreserving hkp (P := fun k => k.canHaveChildren = true)
    (ensurePreInsertionValidity_parentCanHaveChildren hv)
  have f2 := kindFact_of_kindPreserving hkp (P := fun k => k ≠ NodeKind.document)
    (ensurePreInsertionValidity_nodeNotDocument hv)
  have f3 := doctypeFact_of_kindPreserving hkp
    (ensurePreInsertionValidity_doctypeParentIsDocument hv)
  have h₃ : StructurallyValid s₃.tree :=
    structurallyValid_insert_of_facts h₂ f1 f2 f3 hi
  rw [hs]
  simpa using h₃

theorem nodeDocumentsValid_replace {s s' : DOMState} {child node parent : NodeId}
    (hwf : WellFormed s.tree) (hsv : StructurallyValid s.tree) (h : NodeDocumentsValid s.tree)
    (hr : replace s child node parent = .ok s') : NodeDocumentsValid s'.tree := by
  obtain ⟨pd, s₁, s₂, s₃, hv, hpd, ha, hrm, hi, hstate⟩ := replace_cases hr
  have hwf₁ := adopt_preserves_wellformed hwf (isDocument_ownerDocument hwf hpd) ha
  have hs₁ : StructurallyValid s₁.tree := structurallyValid_adopt hsv
    (isDocument_ownerDocument hwf hpd) ha
  have h₁ : NodeDocumentsValid s₁.tree := nodeDocumentsValid_adopt hsv h
    (isDocument_ownerDocument hwf hpd) (ensurePreInsertionValidity_nodeNotDocument hv) ha
  have hkp₁ : ShapePreserving s.tree s₁.tree := shapePreserving_adopt ha
  have hstep : NodeDocumentsValid s₂.tree ∧ StructurallyValid s₂.tree ∧
      ShapePreserving s₁.tree s₂.tree ∧ WellFormed s₂.tree := by
    rcases hrm with ⟨_, rfl⟩ | ⟨_, hrm'⟩
    · exact ⟨h₁, hs₁, ShapePreserving.refl _, hwf₁⟩
    · exact ⟨nodeDocumentsValid_remove hwf₁ h₁ hrm', structurallyValid_remove hs₁ hrm',
        shapePreserving_remove hrm', remove_preserves_wellformed hwf₁ hrm'⟩
  obtain ⟨h₂, hs₂, hkp₂, hwf₂⟩ := hstep
  have hkp : ShapePreserving s.tree s₂.tree := hkp₁.trans hkp₂
  have f1 := kindFact_of_kindPreserving hkp (P := fun k => k.canHaveChildren = true)
    (ensurePreInsertionValidity_parentCanHaveChildren hv)
  have f2 := kindFact_of_kindPreserving hkp (P := fun k => k ≠ NodeKind.document)
    (ensurePreInsertionValidity_nodeNotDocument hv)
  have f3 := doctypeFact_of_kindPreserving hkp
    (ensurePreInsertionValidity_doctypeParentIsDocument hv)
  have h₃ : NodeDocumentsValid s₃.tree :=
    nodeDocumentsValid_insert_of_facts hs₂ h₂ f1 f2 f3 hi
  rw [hstate]
  simpa using h₃

end Dom
