import Dom.Validity.PreserveInsertEach

/-!
# `insert` による保存

validity 検査が前提を確立するので、そこで primitive の条件を discharge する。
-/

namespace Dom

/-! ## insert -/

/-- `StructurallyValid` から、Document でない parent の children に doctype は無い。 -/
theorem child_not_doctype {t : Tree} (h : StructurallyValid t) {p c : NodeId} {pd : NodeData}
    (hpd : t.get? p = some pd) (hk : pd.kind ≠ .document) (hc : c ∈ pd.children) :
    ∀ cd, t.get? c = some cd → cd.kind ≠ .documentType := by
  intro cd hcd hkc
  obtain ⟨cd', hcd', hcdp⟩ := h.wellFormed.parent_child p pd hpd c hc
  rw [hcd] at hcd'
  cases hcd'
  exact hk (h.doctypeParentIsDocument c cd hcd hkc p hcdp pd hpd)

/-- `StructurallyValid` から、木の中の node の children は DocumentFragment ではない。 -/
theorem child_not_fragment {t : Tree} (h : StructurallyValid t) {p c : NodeId} {pd : NodeData}
    (hpd : t.get? p = some pd) (hc : c ∈ pd.children) :
    ∀ cd, t.get? c = some cd → cd.kind ≠ .documentFragment := by
  intro cd hcd hk
  obtain ⟨cd', hcd', hcdp⟩ := h.wellFormed.parent_child p pd hpd c hc
  rw [hcd] at hcd'
  cases hcd'
  exact absurd hcdp (by rw [h.fragmentHasNoParent c cd hcd hk]; simp)

/-- `StructurallyValid` から、木の中の node の children は Document ではない。 -/
theorem child_not_document {t : Tree} (h : StructurallyValid t) {p c : NodeId} {pd : NodeData}
    (hpd : t.get? p = some pd) (hc : c ∈ pd.children) :
    ∀ cd, t.get? c = some cd → cd.kind ≠ .document := by
  intro cd hcd hk
  obtain ⟨cd', hcd', hcdp⟩ := h.wellFormed.parent_child p pd hpd c hc
  rw [hcd] at hcd'
  cases hcd'
  exact absurd hcdp (by rw [h.documentHasNoParent c cd hcd hk]; simp)

theorem structurallyValid_insertNodesAt {s s' : DOMState} {parent : NodeId}
    {child : Option NodeId} {nodes : List NodeId} {b : Bool}
    (h : StructurallyValid s.tree)
    (hpk : ∀ pd, s.tree.get? parent = some pd → pd.kind.canHaveChildren = true)
    (hnk : ∀ n ∈ nodes, ∀ nd, s.tree.get? n = some nd → nd.kind ≠ .document)
    (hnf : ∀ n ∈ nodes, ∀ nd, s.tree.get? n = some nd → nd.kind ≠ .documentFragment)
    (hdt : ∀ n ∈ nodes, ∀ nd, s.tree.get? n = some nd → nd.kind = .documentType →
      ∀ pd, s.tree.get? parent = some pd → pd.kind = .document)
    (hi : insertNodesAt s parent child nodes b = .ok s') : StructurallyValid s'.tree := by
  obtain ⟨sx, hx, hrec⟩ := insertNodesAt_cases hi
  have htree : s'.tree = sx.tree := by
    rcases hrec with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · rfl
    · simp
  rw [htree]
  obtain ⟨pd, hpd, hx⟩ := insertEachAt_cases hx
  have hpd' : s.tree.get? parent = some pd := by simpa using hpd
  refine structurallyValid_insertEach nodes (by simpa using h) (by simpa using hpk)
    (by simpa using hnk) (by simpa using hnf) (by simpa using hdt) ?_ hx
  exact ⟨_, by simpa using (isDocument_ownerDocument h.wellFormed hpd').choose_spec.1,
    (isDocument_ownerDocument h.wellFormed hpd').choose_spec.2⟩

/--
PLAN §6.3 の形。`insert` は構造上の妥当性を保つ。

fragment を展開する側では、入れる node は fragment の children なので
「Document は parent を持たない」という invariant から Document でないことが出る。
単独の node の側では validity 検査の step 4 から出る。
-/
theorem structurallyValid_insert_of_facts {s s' : DOMState} {node parent : NodeId}
    {child : Option NodeId} {b : Bool} (h : StructurallyValid s.tree)
    (hpk : ∀ pd, s.tree.get? parent = some pd → pd.kind.canHaveChildren = true)
    (hnk : ∀ nd, s.tree.get? node = some nd → nd.kind ≠ NodeKind.document)
    (hdtf : ∀ nd, s.tree.get? node = some nd → nd.kind = NodeKind.documentType →
      ∀ pd, s.tree.get? parent = some pd → pd.kind = NodeKind.document)
    (hi : insert s node parent child b = .ok s') : StructurallyValid s'.tree := by
  obtain ⟨nd, hnd, hcase⟩ := insert_cases hi
  rcases hcase with ⟨_, _, hsx⟩ | ⟨hk, _, s₁, hre, hins⟩ | ⟨hnotfrag, hins⟩
  · rw [hsx]; exact h
  · -- fragment を展開する
    have h₁ : StructurallyValid s₁.tree := structurallyValid_removeEach _ h hre
    have hkp : ShapePreserving s.tree s₁.tree := shapePreserving_removeEach _ hre
    have hfragkind : nd.kind ≠ NodeKind.document := by rw [hk]; simp
    refine structurallyValid_insertNodesAt (s := queueTreeMutationRecord s₁ node []
      nd.children none none) (by simpa using h₁) ?_ ?_ ?_ ?_ hins
    · simpa using
        kindFact_of_kindPreserving (P := fun k => k.canHaveChildren = true) hkp hpk
    · intro m hm
      simpa using kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.document) hkp
        (child_not_document h hnd hm)
    · intro m hm
      simpa using
        kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.documentFragment) hkp
          (child_not_fragment h hnd hm)
    · intro m hm md hmd hkm _ _
      refine absurd hkm ?_
      have := kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.documentType) hkp
        (child_not_doctype h hnd hfragkind hm)
      exact this md (by simpa using hmd)
  · -- 単独の node
    refine structurallyValid_insertNodesAt h hpk ?_ ?_ ?_ hins
    · intro m hm
      rcases List.mem_singleton.mp hm with rfl
      exact hnk
    · intro m hm
      rcases List.mem_singleton.mp hm with rfl
      intro md hmd
      rw [hnd] at hmd
      cases hmd
      exact hnotfrag
    · intro m hm
      rcases List.mem_singleton.mp hm with rfl
      exact hdtf

/--
PLAN §6.3 の形。`insert` は構造上の妥当性を保つ。

必要な三つの事実は `ensure pre-insertion validity` の step 1 / 4 / 5 が与える。
-/
theorem structurallyValid_insert {s s' : DOMState} {node parent : NodeId}
    {child : Option NodeId} {b : Bool} (h : StructurallyValid s.tree)
    (hv : ensurePreInsertionValidity s.tree node parent child [] = .ok ())
    (hi : insert s node parent child b = .ok s') : StructurallyValid s'.tree :=
  structurallyValid_insert_of_facts h
    (ensurePreInsertionValidity_parentCanHaveChildren hv)
    (ensurePreInsertionValidity_nodeNotDocument hv)
    (ensurePreInsertionValidity_doctypeParentIsDocument hv) hi

theorem nodeDocumentsValid_insertNodesAt {s s' : DOMState} {parent : NodeId}
    {child : Option NodeId} {nodes : List NodeId} {b : Bool}
    (hs : StructurallyValid s.tree) (h : NodeDocumentsValid s.tree)
    (hpk : ∀ pd, s.tree.get? parent = some pd → pd.kind.canHaveChildren = true)
    (hnk : ∀ n ∈ nodes, ∀ nd, s.tree.get? n = some nd → nd.kind ≠ .document)
    (hnf : ∀ n ∈ nodes, ∀ nd, s.tree.get? n = some nd → nd.kind ≠ .documentFragment)
    (hdt : ∀ n ∈ nodes, ∀ nd, s.tree.get? n = some nd → nd.kind = .documentType →
      ∀ pd, s.tree.get? parent = some pd → pd.kind = .document)
    (hi : insertNodesAt s parent child nodes b = .ok s') : NodeDocumentsValid s'.tree := by
  obtain ⟨sx, hx, hrec⟩ := insertNodesAt_cases hi
  have htree : s'.tree = sx.tree := by
    rcases hrec with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · rfl
    · simp
  rw [htree]
  obtain ⟨pd, hpd, hx⟩ := insertEachAt_cases hx
  have hpd' : s.tree.get? parent = some pd := by simpa using hpd
  refine nodeDocumentsValid_insertEach nodes (by simpa using hs) (by simpa using h)
    ?_ (by simpa using hpk) ?_ (by simpa using hnk) (by simpa using hnf)
    (by simpa using hdt) hx
  · exact ⟨_, by simpa using (isDocument_ownerDocument hs.wellFormed hpd').choose_spec.1,
      (isDocument_ownerDocument hs.wellFormed hpd').choose_spec.2⟩
  · simp only [liveRangeInsertAdjust_tree]
    simp [ownerDocumentOf_eq, hpd']

/-- PLAN §6.3 の形。`insert` は node document の整合性を保つ。 -/
theorem nodeDocumentsValid_insert_of_facts {s s' : DOMState} {node parent : NodeId}
    {child : Option NodeId} {b : Bool}
    (hs : StructurallyValid s.tree) (h : NodeDocumentsValid s.tree)
    (hpk : ∀ pd, s.tree.get? parent = some pd → pd.kind.canHaveChildren = true)
    (hnk : ∀ nd, s.tree.get? node = some nd → nd.kind ≠ NodeKind.document)
    (hdtf : ∀ nd, s.tree.get? node = some nd → nd.kind = NodeKind.documentType →
      ∀ pd, s.tree.get? parent = some pd → pd.kind = NodeKind.document)
    (hi : insert s node parent child b = .ok s') : NodeDocumentsValid s'.tree := by
  obtain ⟨nd, hnd, hcase⟩ := insert_cases hi
  rcases hcase with ⟨_, _, hsx⟩ | ⟨hk, _, s₁, hre, hins⟩ | ⟨hnotfrag, hins⟩
  · rw [hsx]; exact h
  · have hs₁ : StructurallyValid s₁.tree := structurallyValid_removeEach _ hs hre
    have h₁ : NodeDocumentsValid s₁.tree := nodeDocumentsValid_removeEach _ hs h hre
    have hkp : ShapePreserving s.tree s₁.tree := shapePreserving_removeEach _ hre
    have hfragkind : nd.kind ≠ NodeKind.document := by rw [hk]; simp
    refine nodeDocumentsValid_insertNodesAt (s := queueTreeMutationRecord s₁ node []
      nd.children none none) (by simpa using hs₁) (by simpa using h₁) ?_ ?_ ?_ ?_ hins
    · simpa using
        kindFact_of_kindPreserving (P := fun k => k.canHaveChildren = true) hkp hpk
    · intro m hm
      simpa using kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.document) hkp
        (child_not_document hs hnd hm)
    · intro m hm
      simpa using
        kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.documentFragment) hkp
          (child_not_fragment hs hnd hm)
    · intro m hm md hmd hkm _ _
      refine absurd hkm ?_
      have := kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.documentType) hkp
        (child_not_doctype hs hnd hfragkind hm)
      exact this md (by simpa using hmd)
  · refine nodeDocumentsValid_insertNodesAt hs h hpk ?_ ?_ ?_ hins
    · intro m hm
      rcases List.mem_singleton.mp hm with rfl
      exact hnk
    · intro m hm
      rcases List.mem_singleton.mp hm with rfl
      intro md hmd
      rw [hnd] at hmd
      cases hmd
      exact hnotfrag
    · intro m hm
      rcases List.mem_singleton.mp hm with rfl
      exact hdtf

/-- PLAN §6.3 の形。`insert` は node document の整合性を保つ。 -/
theorem nodeDocumentsValid_insert {s s' : DOMState} {node parent : NodeId}
    {child : Option NodeId} {b : Bool}
    (hs : StructurallyValid s.tree) (h : NodeDocumentsValid s.tree)
    (hv : ensurePreInsertionValidity s.tree node parent child [] = .ok ())
    (hi : insert s node parent child b = .ok s') : NodeDocumentsValid s'.tree :=
  nodeDocumentsValid_insert_of_facts hs h
    (ensurePreInsertionValidity_parentCanHaveChildren hv)
    (ensurePreInsertionValidity_nodeNotDocument hv)
    (ensurePreInsertionValidity_doctypeParentIsDocument hv) hi

end Dom
