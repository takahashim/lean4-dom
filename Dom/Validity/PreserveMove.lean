import Dom.Validity.PreserveInsertAt

/-!
# `move` / `moveBefore` による保存
-/

namespace Dom

/-! ## move -/

/-- children も kind も同じなら Document の制約も同じである。 -/
theorem documentChildrenOk_congr {t t' : Tree} {doc : NodeId}
    (hkind : ∀ m, kindOf t' m = kindOf t m) (hch : childrenOf t' doc = childrenOf t doc)
    (h : DocumentChildrenOk t doc) : DocumentChildrenOk t' doc := by
  have he : elementChildren t' doc = elementChildren t doc := by
    unfold elementChildren; simp only [hch, hkind]
  have hdt : doctypeChildren t' doc = doctypeChildren t doc := by
    unfold doctypeChildren; simp only [hch, hkind]
  have htx : textChildren t' doc = textChildren t doc := by
    unfold textChildren; simp only [hch, hkind]
  have hf : ∀ c, doctypeFollows t' doc c = doctypeFollows t doc c := by
    intro c; exact doctypeFollows_congr hch hkind
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by rw [he]; exact h1, by rw [hdt]; exact h2, by rw [htx]; exact h3,
    fun e hm => by rw [hf]; exact h4 e (by rw [← he]; exact hm)⟩

/-- `insertAt` は挿入先以外の Document の制約を変えない。 -/
theorem documentChildrenOk_insertAt_ne {t t' : Tree} {parent node : NodeId}
    {child : Option NodeId} (hwf : WellFormed t) (hi : insertAt t parent node child = .ok t')
    {doc : NodeId} (hne : doc ≠ parent) (h : DocumentChildrenOk t doc) :
    DocumentChildrenOk t' doc :=
  documentChildrenOk_congr (shapePreserving_insertAt hi).kind (insertAt_childrenOf_ne hwf hi hne) h

/--
`move` は「validity 検査を通ってから detach して insertAt する」ものなので、
`remove` 側と `insertAt` 側を繋げば三つの層がすべて保たれる。

`newParent` が children を持てる kind であることは step 1-6 では検査されない。
これは `moveBefore` が `ParentNode` の method であることによる IDL 側の制約なので、
仮定として受け取り、`moveBefore` の側で discharge する。
-/
theorem structurallyValid_move {s s' : DOMState} {node newParent : NodeId}
    {child : Option NodeId} (h : StructurallyValid s.tree)
    (hpk : ∀ pd, s.tree.get? newParent = some pd → pd.kind.canHaveChildren = true)
    (hm : move s node newParent child = .ok s') : StructurallyValid s'.tree := by
  obtain ⟨s₁, hr, hi⟩ := move_eq_remove_insertAt hm
  obtain ⟨nd, pd, hnd, hpd, _, hk4, _, _⟩ := moveValidity_ok (move_moveValidity hm)
  have hkp : ShapePreserving s.tree s₁.tree := shapePreserving_remove hr
  have hnotdoc : ∀ d, s.tree.get? node = some d → d.kind ≠ NodeKind.document := by
    intro d hd
    obtain rfl : d = nd := by rw [hnd] at hd; exact (Option.some.inj hd).symm
    rcases hk4 with hk | hk
    · rw [hk]; simp
    · intro hdoc; rw [hdoc] at hk; simp [NodeKind.isCharacterData] at hk
  have hnotdt : ∀ d, s.tree.get? node = some d → d.kind = NodeKind.documentType →
      ∀ pd', s.tree.get? newParent = some pd' → pd'.kind = NodeKind.document := by
    intro d hd hdt
    obtain rfl : d = nd := by rw [hnd] at hd; exact (Option.some.inj hd).symm
    exfalso
    rcases hk4 with hk | hk
    · rw [hk] at hdt; simp at hdt
    · rw [hdt] at hk; simp [NodeKind.isCharacterData] at hk
  -- move の step 4 は Element と CharacterData しか動かさないので、fragment は来ない。
  have hnotfrag : ∀ d, s.tree.get? node = some d → d.kind ≠ NodeKind.documentFragment := by
    intro d hd
    obtain rfl : d = nd := by rw [hnd] at hd; exact (Option.some.inj hd).symm
    rcases hk4 with hk | hk
    · rw [hk]; simp
    · intro hfrag; rw [hfrag] at hk; simp [NodeKind.isCharacterData] at hk
  exact structurallyValid_insertAt (structurallyValid_remove h hr)
    (kindFact_of_kindPreserving hkp (P := fun k => k.canHaveChildren = true) hpk)
    (kindFact_of_kindPreserving hkp (P := fun k => k ≠ NodeKind.document) hnotdoc)
    (kindFact_of_kindPreserving hkp (P := fun k => k ≠ NodeKind.documentFragment) hnotfrag)
    (doctypeFact_of_kindPreserving hkp hnotdt) hi

/-- `move` は node document を付け替えないが、step 1 が同じ root を要求するので整合性は保たれる。 -/
theorem nodeDocumentsValid_move {s s' : DOMState} {node newParent : NodeId}
    {child : Option NodeId} (hwf : WellFormed s.tree) (h : NodeDocumentsValid s.tree)
    (hm : move s node newParent child = .ok s') : NodeDocumentsValid s'.tree := by
  obtain ⟨s₁, hr, hi⟩ := move_eq_remove_insertAt hm
  obtain ⟨nd, pd, hnd, hpd, hroot, _, _, _⟩ := moveValidity_ok (move_moveValidity hm)
  have hd := (remove_ok hr).2
  have hown0 : ownerDocumentOf s.tree node = ownerDocumentOf s.tree newParent := by
    have h1 : ownerDocumentOf s.tree node = ownerDocumentOf s.tree (root s.tree node) :=
      h.ownerDocument_eq_of_inclusiveAncestor (root_inclusive_ancestor s.tree node)
    have h2 : ownerDocumentOf s.tree newParent
        = ownerDocumentOf s.tree (root s.tree newParent) :=
      h.ownerDocument_eq_of_inclusiveAncestor (root_inclusive_ancestor s.tree newParent)
    rw [h1, h2, hroot]
  have hown : ownerDocumentOf s₁.tree node = ownerDocumentOf s₁.tree newParent := by
    rw [ownerDocumentOf_detach hd, ownerDocumentOf_detach hd]
    exact hown0
  exact nodeDocumentsValid_insertAt (nodeDocumentsValid_remove hwf h hr) hown hi

/-- `move` の step 5 と step 6 が、Document の children 制約をそのまま与える。 -/
theorem documentTreesValid_move {s s' : DOMState} {node newParent : NodeId}
    {child : Option NodeId} (hwf : WellFormed s.tree) (h : DocumentTreesValid s.tree)
    (hm : move s node newParent child = .ok s') : DocumentTreesValid s'.tree := by
  obtain ⟨s₁, hr, hi⟩ := move_eq_remove_insertAt hm
  obtain ⟨nd, pd, hnd, hpd, _, hk4, hk5, hk6⟩ := moveValidity_ok (move_moveValidity hm)
  have hd := (remove_ok hr).2
  have hwf₁ : WellFormed s₁.tree := remove_preserves_wellformed hwf hr
  have hkind : ∀ m, kindOf s₁.tree m = kindOf s.tree m := (shapePreserving_detach hd).kind
  have h₁ : DocumentTreesValid s₁.tree := documentTreesValid_remove hwf h hr
  refine ⟨fun doc dd hdoc hkdoc => ?_⟩
  obtain ⟨dd₁, hdoc₁, hkdd⟩ := shapePreserving_get? (shapePreserving_insertAt hi) hdoc
  have hk₁ : dd₁.kind = NodeKind.document := by rw [hkdd]; exact hkdoc
  have hok₁ : DocumentChildrenOk s₁.tree doc := h₁.documentChildren doc dd₁ hdoc₁ hk₁
  by_cases hne : doc = newParent
  · subst hne
    -- `doc` が挿入先。step 5 / 6 の事実を `s₁` 側に移して使う。
    have hpdoc : pd.kind = NodeKind.document := by
      have hkp := hkind doc
      rw [kindOf_eq, kindOf_eq, hdoc₁, hpd] at hkp
      simp only [Option.map_some, Option.some.injEq] at hkp
      rw [← hkp]; exact hk₁
    have hnode : kindOf s₁.tree node = some nd.kind := by
      rw [hkind node, kindOf_eq, hnd]; rfl
    refine documentChildrenOk_of_insertAt hwf₁ hi ?_ ?_ ?_ hok₁
    · -- step 5：Document の子に Text は置けない
      intro k hk
      rw [hnode] at hk
      obtain rfl : k = nd.kind := (Option.some.inj hk).symm
      exact hk5 hpdoc
    · -- step 6：element を入れるなら他に element は無く、後ろに doctype も無い
      intro helem
      rw [hnode] at helem
      have hkelem : nd.kind = NodeKind.element := Option.some.inj helem
      obtain ⟨hempty, hafter⟩ := hk6 hpdoc hkelem
      refine ⟨elementChildren_eq_nil_of_detach hwf hd hempty, ?_⟩
      intro c hc
      subst hc
      unfold doctypeAtOrAfter at hafter
      simp only at hafter
      rw [Bool.or_eq_false_iff] at hafter
      refine ⟨by rw [hkind c]; exact hafter.1, ?_⟩
      exact doctypeFollows_of_removeAll hkind (detach_childrenOf_removeAll hwf hd doc) hafter.2
    · -- step 4：move する node は doctype ではないので、この場合は起こらない
      intro hdt
      exfalso
      rw [hnode] at hdt
      have hkdt : nd.kind = NodeKind.documentType := Option.some.inj hdt
      rcases hk4 with hkk | hkk
      · rw [hkdt] at hkk; simp at hkk
      · rw [hkdt] at hkk; simp [NodeKind.isCharacterData] at hkk
  · exact documentChildrenOk_insertAt_ne hwf₁ hi hne hok₁

/-! ## moveBefore -/

/--
`moveBefore` は `ParentNode` の method なので、receiver が children を持てることを検査する。
これが `move` の仮定 `hpk` を discharge する。
-/
theorem structurallyValid_moveBefore {s s' : DOMState} {parent node : NodeId}
    {child : Option NodeId} (h : StructurallyValid s.tree)
    (hm : moveBefore s parent node child = .ok s') : StructurallyValid s'.tree := by
  obtain ⟨pd, ref, hpd, hk, hmove⟩ := moveBefore_ok hm
  refine structurallyValid_move h ?_ hmove
  intro pd' hpd'
  obtain rfl : pd' = pd := by rw [hpd] at hpd'; exact (Option.some.inj hpd').symm
  exact hk

theorem nodeDocumentsValid_moveBefore {s s' : DOMState} {parent node : NodeId}
    {child : Option NodeId} (hwf : WellFormed s.tree) (h : NodeDocumentsValid s.tree)
    (hm : moveBefore s parent node child = .ok s') : NodeDocumentsValid s'.tree := by
  obtain ⟨_, _, _, _, hmove⟩ := moveBefore_ok hm
  exact nodeDocumentsValid_move hwf h hmove

theorem documentTreesValid_moveBefore {s s' : DOMState} {parent node : NodeId}
    {child : Option NodeId} (hwf : WellFormed s.tree) (h : DocumentTreesValid s.tree)
    (hm : moveBefore s parent node child = .ok s') : DocumentTreesValid s'.tree := by
  obtain ⟨_, _, _, _, hmove⟩ := moveBefore_ok hm
  exact documentTreesValid_move hwf h hmove

end Dom
