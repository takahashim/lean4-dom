import Dom.Validity.PreserveMove

/-!
# `adopt` による保存と、node document への効果
-/

namespace Dom

/-! ## adopt -/

theorem structurallyValid_adopt {s s' : DOMState} {node doc : NodeId}
    (h : StructurallyValid s.tree) (hdoc : IsDocument s.tree doc)
    (ha : adopt s node doc = .ok s') : StructurallyValid s'.tree := by
  obtain ⟨s₁, hstep, hfinal⟩ := adopt_ok_cases ha
  have hstep' : StructurallyValid s₁.tree ∧ ShapePreserving s.tree s₁.tree := by
    rcases hstep with ⟨_, rfl⟩ | hr
    · exact ⟨h, ShapePreserving.refl _⟩
    · exact ⟨structurallyValid_remove h hr, shapePreserving_remove hr⟩
  rcases hfinal with rfl | rfl
  · exact hstep'.1
  · obtain ⟨dd, hdd, hk⟩ := hdoc.map hstep'.2
    exact structurallyValid_setOwnerDocument hstep'.1.wellFormed hstep'.1 hdd hk

/--
adopt は node document を整える step である。

step 2 の remove で node は parent を失うので、step 3 の `setOwnerDocument` は
閉じた部分木を書き換える。node が Document でないことは insert 側の validity 検査から来る。
-/
theorem nodeDocumentsValid_adopt {s s' : DOMState} {node doc : NodeId}
    (hs : StructurallyValid s.tree) (h : NodeDocumentsValid s.tree)
    (hdoc : IsDocument s.tree doc)
    (hnk : ∀ nd, s.tree.get? node = some nd → nd.kind ≠ .document)
    (ha : adopt s node doc = .ok s') : NodeDocumentsValid s'.tree := by
  obtain ⟨s₁, hstep, hfinal⟩ := adopt_ok_cases ha
  have hstep' : NodeDocumentsValid s₁.tree ∧ StructurallyValid s₁.tree ∧
      ShapePreserving s.tree s₁.tree ∧ parentOf s₁.tree node = none := by
    rcases hstep with ⟨hnp, rfl⟩ | hr
    · exact ⟨h, hs, ShapePreserving.refl _, hnp⟩
    · exact ⟨nodeDocumentsValid_remove hs.wellFormed h hr, structurallyValid_remove hs hr,
        shapePreserving_remove hr, remove_parentOf hr⟩
  rcases hfinal with rfl | rfl
  · exact hstep'.1
  · refine nodeDocumentsValid_setOwnerDocument hstep'.2.1.wellFormed hstep'.2.1 hstep'.1
      hstep'.2.2.2 ?_
    exact kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.document) hstep'.2.2.1 hnk

/-! ## adopt / removeEach / replaceData の document tree 保存 -/

theorem documentTreesValid_setOwnerDocument {t : Tree} (n doc : NodeId)
    (h : DocumentTreesValid t) : DocumentTreesValid (setOwnerDocument t n doc) :=
  documentTreesValid_of_sameShape (shapePreserving_setOwnerDocument t n doc).kind
    (childrenOf_setOwnerDocument t n doc) h

theorem documentTreesValid_adopt {s s' : DOMState} {node doc : NodeId}
    (hwf : WellFormed s.tree) (h : DocumentTreesValid s.tree)
    (ha : adopt s node doc = .ok s') : DocumentTreesValid s'.tree := by
  obtain ⟨s₁, hstep, hfinal⟩ := adopt_ok_cases ha
  have h₁ : DocumentTreesValid s₁.tree ∧ WellFormed s₁.tree := by
    rcases hstep with ⟨_, rfl⟩ | hr
    · exact ⟨h, hwf⟩
    · exact ⟨documentTreesValid_remove hwf h hr, remove_preserves_wellformed hwf hr⟩
  rcases hfinal with rfl | rfl
  · exact h₁.1
  · exact documentTreesValid_setOwnerDocument node doc h₁.1

theorem documentTreesValid_removeEach :
    ∀ (ns : List NodeId) {s s' : DOMState} {b : Bool},
      WellFormed s.tree → DocumentTreesValid s.tree → removeEach s ns b = .ok s' →
      DocumentTreesValid s'.tree
  | [], _, _, _, _, h, hr => by rw [← Except.ok.inj hr]; exact h
  | n :: ns, s, s', b, hwf, h, hr => by
    simp only [removeEach] at hr
    split at hr
    · simp at hr
    · next s₁ h₁ =>
      exact documentTreesValid_removeEach ns (remove_preserves_wellformed hwf h₁)
        (documentTreesValid_remove hwf h h₁) hr

/-! ## adopt が node document に与える効果 -/

/-- adopt の後、node の node document は `doc` になっている。 -/
theorem adopt_ownerDocument_self {s s' : DOMState} {node doc : NodeId}
    (hwf : WellFormed s.tree) (ha : adopt s node doc = .ok s') :
    ownerDocumentOf s'.tree node = some doc := by
  obtain ⟨old, s₁, hold, hstep, hfinal⟩ := adopt_cases ha
  have hown₁ : ownerDocumentOf s₁.tree node = some old := by
    rcases hstep with ⟨_, rfl⟩ | ⟨_, hr⟩
    · exact hold
    · rw [ownerDocumentOf_detach (remove_ok hr).2]; exact hold
  have hwf₁ : WellFormed s₁.tree := by
    rcases hstep with ⟨_, rfl⟩ | ⟨_, hr⟩
    · exact hwf
    · exact remove_preserves_wellformed hwf hr
  obtain ⟨nd₁, hnd₁⟩ : ∃ nd₁, s₁.tree.get? node = some nd₁ := by
    cases h1 : s₁.tree.get? node with
    | some x => exact ⟨x, rfl⟩
    | none => rw [ownerDocumentOf_eq, h1] at hown₁; simp at hown₁
  rcases hfinal with ⟨he, rfl⟩ | ⟨-, rfl⟩
  · rw [hown₁, he]
  · show ownerDocumentOf (setOwnerDocument s₁.tree node doc) node = some doc
    rw [ownerDocumentOf_setOwnerDocument_eq, hnd₁]
    simp [mem_preorder_self hwf₁ hnd₁]

/-- adopt は「parent の node document が `doc` である」という条件を壊さない。 -/
theorem adopt_ownerDocument_other {s s' : DOMState} {node doc parent : NodeId}
    (ha : adopt s node doc = .ok s') (hp : ownerDocumentOf s.tree parent = some doc) :
    ownerDocumentOf s'.tree parent = some doc := by
  obtain ⟨s₁, hstep, hfinal⟩ := adopt_ok_cases ha
  have hp₁ : ownerDocumentOf s₁.tree parent = some doc := by
    rcases hstep with ⟨_, rfl⟩ | hr
    · exact hp
    · rw [ownerDocumentOf_detach (remove_ok hr).2]; exact hp
  rcases hfinal with rfl | rfl
  · exact hp₁
  · show ownerDocumentOf (setOwnerDocument s₁.tree node doc) parent = some doc
    rw [ownerDocumentOf_setOwnerDocument_eq]
    cases h1 : s₁.tree.get? parent with
    | none => rw [ownerDocumentOf_eq, h1] at hp₁; simp at hp₁
    | some pd =>
      simp only [Option.map_some]
      split
      · rfl
      · rw [ownerDocumentOf_eq, h1] at hp₁; simpa using hp₁

end Dom
