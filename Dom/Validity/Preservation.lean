import Dom.Validity.Derived

/-!
# primitive による admissibility の保存

`notes/research-foundation-roadmap.md` Phase A の後半。
まず Phase 2 の primitive（`detach`, `insertAt`, `setOwnerDocument`）について
`StructurallyValid` と `NodeDocumentsValid` の保存を示す。

`DocumentTreesValid` は primitive では保たれない（`insertAt` は制約を検査しない）ので、
§4.2.3 の algorithm の側で扱う。
-/

namespace Dom

/-! ## detach -/

/-- `detach` は kind を変えないので、children を持てる kind かどうかも変わらない。 -/
theorem structurallyValid_detach {t t' : Tree} {n : NodeId}
    (h : StructurallyValid t) (hd : detach t n = .ok t') : StructurallyValid t' := by
  have hkind : ∀ m, kindOf t' m = kindOf t m := kindPreserving_detach hd
  refine ⟨detach_preserves_wellformed h.wellFormed hd, ?_, ?_, ?_⟩
  · intro m d hm hk
    rcases detach_ok_cases hd with ⟨nd, hnd, hnp, rfl⟩ | ⟨nd, p, pd, hnd, hnp, hpd, rfl⟩
    · exact h.documentHasNoParent m d hm hk
    · rw [get?_detachFrom] at hm
      split at hm
      · next he =>
        -- 外した node 自身。parent は `none` になっている。
        cases hm; rfl
      · split at hm
        · next hne he =>
          -- 旧 parent。parent は変わらない。
          subst he
          cases hm
          exact h.documentHasNoParent _ pd hpd hk
        · exact h.documentHasNoParent m d hm hk
  · intro m d hm hc
    rcases detach_ok_cases hd with ⟨nd, hnd, hnp, rfl⟩ | ⟨nd, p, pd, hnd, hnp, hpd, rfl⟩
    · exact h.childrenOnlyUnderContainers m d hm hc
    · rw [get?_detachFrom] at hm
      split at hm
      · cases hm
        exact h.childrenOnlyUnderContainers n nd hnd (by simpa using hc)
      · split at hm
        · next hne he =>
          subst he
          cases hm
          refine h.childrenOnlyUnderContainers _ pd hpd ?_
          intro hnil
          exact hc (by simp [hnil]; rfl)
        · exact h.childrenOnlyUnderContainers m d hm hc
  · -- doctype の parent。`detach` は辺を減らすだけなので、残った辺は元からある辺である。
    intro m d hm hk p hp pd hpd
    have hpar : parentOf t' m = some p := by simp [parentOf, hm, hp]
    have hpar' : parentOf t m = some p := by
      rw [parentOf_detach hd] at hpar
      split at hpar
      · simp at hpar
      · exact hpar
    obtain ⟨md, hmd, hmdp⟩ := parentOf_eq_some hpar'
    obtain ⟨pd', hpd'⟩ : ∃ pd', t.get? p = some pd' := exists_data_of_parentOf h.wellFormed hpar'
    have hkm : md.kind = .documentType := by
      have hkm' := hkind m
      simp only [kindOf, hm, hmd, Option.map_some, Option.some.injEq] at hkm'
      rw [← hkm']; exact hk
    have hdocp := h.doctypeParentIsDocument m md hmd hkm p hmdp pd' hpd'
    have hkp := hkind p
    simp only [kindOf, hpd, hpd', Option.map_some, Option.some.injEq] at hkp
    rw [hkp]; exact hdocp

/-- `detach` は node document を変えない。 -/
theorem ownerDocumentOf_detach {t t' : Tree} {n : NodeId} (hd : detach t n = .ok t') (m : NodeId) :
    ownerDocumentOf t' m = ownerDocumentOf t m := by
  rcases detach_ok_cases hd with ⟨nd, hnd, hnp, rfl⟩ | ⟨nd, p, pd, hnd, hnp, hpd, rfl⟩
  · rfl
  · simp only [ownerDocumentOf, get?_detachFrom]
    split
    · next he => rw [he, hnd]; rfl
    · split
      · next hne he => rw [he, hpd]; rfl
      · rfl

/-- `detach` は node document の整合性を保つ。 -/
theorem nodeDocumentsValid_detach {t t' : Tree} {n : NodeId}
    (hwf : WellFormed t) (h : NodeDocumentsValid t) (hd : detach t n = .ok t') :
    NodeDocumentsValid t' := by
  have hown : ∀ m, ownerDocumentOf t' m = ownerDocumentOf t m := ownerDocumentOf_detach hd
  refine ⟨?_, ?_⟩
  · intro m d hm hk
    rcases detach_ok_cases hd with ⟨nd, hnd, hnp, rfl⟩ | ⟨nd, p, pd, hnd, hnp, hpd, rfl⟩
    · exact h.documentIsOwnNodeDocument m d hm hk
    · rw [get?_detachFrom] at hm
      split at hm
      · next he => subst he; cases hm; exact h.documentIsOwnNodeDocument _ nd hnd hk
      · split at hm
        · next hne he =>
          subst he
          cases hm
          exact h.documentIsOwnNodeDocument _ pd hpd hk
        · exact h.documentIsOwnNodeDocument m d hm hk
  · intro c p hp
    rw [hown, hown]
    refine h.treeEdgePreservesNodeDocument c p ?_
    rw [parentOf_detach hd] at hp
    split at hp
    · simp at hp
    · exact hp

/-! ## insertAt -/

/--
`insertAt` は kind の制約を検査しないので、次の二つを前提として要求する。

* parent は children を持てる kind である（§4.2.3 ensure pre-insertion validity step 1）。
* node は Document でない（Document は parent を持てない。同 step 4）。

§4.2.3 の algorithm 側はどちらも validity 検査で確立するので、
そこで discharge される。
-/
theorem structurallyValid_insertAt {t t' : Tree} {parent node : NodeId} {child : Option NodeId}
    (h : StructurallyValid t)
    (hpk : ∀ pd, t.get? parent = some pd → pd.kind.canHaveChildren = true)
    (hnk : ∀ nd, t.get? node = some nd → nd.kind ≠ .document)
    (hdt : ∀ nd, t.get? node = some nd → nd.kind = .documentType →
      ∀ pd, t.get? parent = some pd → pd.kind = .document)
    (hi : insertAt t parent node child = .ok t') : StructurallyValid t' := by
  have hwf' := insertAt_preserves_wellformed h.wellFormed hi
  obtain ⟨pd, nd, hpd, hnd, hnone, hanc, hchild, rfl⟩ := insertAt_ok_cases hi
  refine ⟨hwf', ?_, ?_, ?_⟩
  · intro m d hm hk
    rw [get?_insertAtIn] at hm
    split at hm
    · next he =>
      subst he
      cases hm
      exact absurd hk (by simpa using hnk nd hnd)
    · split at hm
      · next hne he =>
        subst he
        cases hm
        exact h.documentHasNoParent _ pd hpd hk
      · exact h.documentHasNoParent m d hm hk
  · intro m d hm hc
    rw [get?_insertAtIn] at hm
    split at hm
    · next he =>
      subst he
      cases hm
      exact h.childrenOnlyUnderContainers _ nd hnd (by simpa using hc)
    · split at hm
      · next hne he =>
        subst he
        cases hm
        exact hpk pd hpd
      · exact h.childrenOnlyUnderContainers m d hm hc
  · -- doctype の parent。新しい辺は node → parent の一本だけである。
    intro m d hm hk p hp pd' hpd'
    have hkind : ∀ x, kindOf (insertAtIn t parent node child pd nd) x = kindOf t x :=
      kindPreserving_insertAt hi
    have hpar : parentOf (insertAtIn t parent node child pd nd) m = some p := by
      simp [parentOf, hm, hp]
    rw [parentOf_insertAtIn hpd] at hpar
    split at hpar
    · next he =>
      subst he
      cases hpar
      have hkn : nd.kind = .documentType := by
        have hk' := hkind m
        simp only [kindOf, hm, hnd, Option.map_some, Option.some.injEq] at hk'
        rw [← hk']; exact hk
      have hdoc := hdt nd hnd hkn pd hpd
      have hkp := hkind parent
      simp only [kindOf, hpd', hpd, Option.map_some, Option.some.injEq] at hkp
      rw [hkp]; exact hdoc
    · obtain ⟨md, hmd, hmdp⟩ := parentOf_eq_some hpar
      obtain ⟨pd₀, hpd₀⟩ : ∃ pd₀, t.get? p = some pd₀ := exists_data_of_parentOf h.wellFormed hpar
      have hkm : md.kind = .documentType := by
        have hk' := hkind m
        simp only [kindOf, hm, hmd, Option.map_some, Option.some.injEq] at hk'
        rw [← hk']; exact hk
      have hdoc := h.doctypeParentIsDocument m md hmd hkm p hmdp pd₀ hpd₀
      have hkp := hkind p
      simp only [kindOf, hpd', hpd₀, Option.map_some, Option.some.injEq] at hkp
      rw [hkp]; exact hdoc

/-- `insertAt` は node document を変えない。 -/
theorem ownerDocumentOf_insertAt {t t' : Tree} {parent node : NodeId} {child : Option NodeId}
    (hi : insertAt t parent node child = .ok t') (m : NodeId) :
    ownerDocumentOf t' m = ownerDocumentOf t m := by
  obtain ⟨pd, nd, hpd, hnd, hnone, hanc, hchild, rfl⟩ := insertAt_ok_cases hi
  simp only [ownerDocumentOf, get?_insertAtIn]
  split
  · next he => rw [he, hnd]; rfl
  · split
    · next hne he => rw [he, hpd]; rfl
    · rfl

/--
`insertAt` は node document を変えないので、
辺の両端が同じ node document であるという条件だけを新しく要求する。
§4.2.3 の insert は step 7 の adopt でこれを確立する。
-/
theorem nodeDocumentsValid_insertAt {t t' : Tree} {parent node : NodeId} {child : Option NodeId}
    (h : NodeDocumentsValid t)
    (hown : ownerDocumentOf t node = ownerDocumentOf t parent)
    (hi : insertAt t parent node child = .ok t') : NodeDocumentsValid t' := by
  have hown' : ∀ m, ownerDocumentOf t' m = ownerDocumentOf t m := ownerDocumentOf_insertAt hi
  obtain ⟨pd, nd, hpd, hnd, hnone, hanc, hchild, rfl⟩ := insertAt_ok_cases hi
  refine ⟨?_, ?_⟩
  · intro m d hm hk
    rw [get?_insertAtIn] at hm
    split at hm
    · next he => subst he; cases hm; exact h.documentIsOwnNodeDocument _ nd hnd hk
    · split at hm
      · next hne he => subst he; cases hm; exact h.documentIsOwnNodeDocument _ pd hpd hk
      · exact h.documentIsOwnNodeDocument m d hm hk
  · intro c p hp
    rw [hown', hown']
    rw [parentOf_insertAtIn hpd] at hp
    split at hp
    · next he =>
      subst he
      cases hp
      exact hown
    · exact h.treeEdgePreservesNodeDocument c p hp

/-! ## setOwnerDocument -/

/-- `preorder` が空でないなら、その根は木の中にある。 -/
theorem exists_data_of_mem_preorder {t : Tree} {n m : NodeId} (h : m ∈ preorder t n) :
    ∃ d, t.get? n = some d := by
  cases hn : t.get? n with
  | some d => exact ⟨d, rfl⟩
  | none =>
    exfalso
    unfold preorder at h
    cases hs : t.size with
    | zero => rw [hs] at h; simp at h
    | succ f => rw [hs, preorderFuel_succ_neg hn] at h; simp at h

/-- `setOwnerDocument` は kind と parent / children を変えない。 -/
theorem structurallyValid_setOwnerDocument {t : Tree} {n doc : NodeId}
    (hwf : WellFormed t) (h : StructurallyValid t) {dd : NodeData}
    (hdd : t.get? doc = some dd) (hk : dd.kind = .document) :
    StructurallyValid (setOwnerDocument t n doc) := by
  have hget : ∀ m d, (setOwnerDocument t n doc).get? m = some d →
      ∃ d', t.get? m = some d' ∧ d.kind = d'.kind ∧ d.parent = d'.parent ∧
        d.children = d'.children := by
    intro m d hm
    rw [get?_setOwnerDocument] at hm
    cases hm' : t.get? m with
    | none => rw [hm'] at hm; simp at hm
    | some d' =>
      rw [hm'] at hm
      simp only [Option.map_some, Option.some.injEq] at hm
      subst hm
      refine ⟨d', rfl, ?_, ?_, ?_⟩ <;> (split <;> rfl)
  refine ⟨setOwnerDocument_preserves_wellformed hwf hdd hk, ?_, ?_, ?_⟩
  · intro m d hm hkm
    obtain ⟨d', hm', hkk, hpp, _⟩ := hget m d hm
    rw [hpp]
    exact h.documentHasNoParent m d' hm' (by rw [← hkk]; exact hkm)
  · intro m d hm hc
    obtain ⟨d', hm', hkk, _, hcc⟩ := hget m d hm
    rw [hkk]
    exact h.childrenOnlyUnderContainers m d' hm' (by rw [← hcc]; exact hc)
  · intro m d hm hkm p hp pd hpd
    obtain ⟨d', hm', hkk, hpp, _⟩ := hget m d hm
    obtain ⟨pd', hpd', hkkp, _, _⟩ := hget p pd hpd
    rw [hkkp]
    exact h.doctypeParentIsDocument m d' hm' (by rw [← hkk]; exact hkm) p
      (by rw [← hpp]; exact hp) pd' hpd'

/--
`setOwnerDocument` が node document の整合性を保つ条件。

* `n` は parent を持たない。部分木が閉じていて、辺が部分木の内と外をまたがない。
* `n` は Document でない。`StructurallyValid` から Document は parent を持たないので、
  これで部分木の中に Document が無いことも従う。

adopt の step 3 は step 2 で remove を済ませているので一つ目を満たし、
insert の validity 検査（step 4）が二つ目を満たす。
-/
theorem nodeDocumentsValid_setOwnerDocument {t : Tree} {n doc : NodeId}
    (hwf : WellFormed t) (hs : StructurallyValid t) (h : NodeDocumentsValid t)
    (hnp : parentOf t n = none)
    (hnk : ∀ nd, t.get? n = some nd → nd.kind ≠ .document) :
    NodeDocumentsValid (setOwnerDocument t n doc) := by
  -- 部分木の中に Document は無い。
  have hnodoc : ∀ m, m ∈ preorder t n → ∀ d, t.get? m = some d → d.kind ≠ .document := by
    intro m hm d hmd hk
    obtain ⟨nd, hnd⟩ := exists_data_of_mem_preorder hm
    rcases (mem_preorder_iff hwf hnd m).mp hm with rfl | hanc
    · exact hnk d hmd hk
    · obtain ⟨q, hq⟩ := hanc.parent_isSome
      rw [parentOf, hmd] at hq
      simp only [Option.bind_some] at hq
      exact absurd hq (by rw [hs.documentHasNoParent m d hmd hk]; simp)
  have hget : ∀ m d, (setOwnerDocument t n doc).get? m = some d →
      ∃ d', t.get? m = some d' ∧ d.kind = d'.kind ∧
        d.ownerDocument = (if m ∈ preorder t n then doc else d'.ownerDocument) := by
    intro m d hm
    rw [get?_setOwnerDocument] at hm
    cases hm' : t.get? m with
    | none => rw [hm'] at hm; simp at hm
    | some d' =>
      rw [hm'] at hm
      simp only [Option.map_some, Option.some.injEq] at hm
      subst hm
      exact ⟨d', rfl, by split <;> rfl, by split <;> rfl⟩
  have hown : ∀ m, ownerDocumentOf (setOwnerDocument t n doc) m =
      (t.get? m).map fun d' => if m ∈ preorder t n then doc else d'.ownerDocument := by
    intro m
    simp only [ownerDocumentOf, get?_setOwnerDocument, Option.map_map]
    cases t.get? m <;> simp <;> split <;> rfl
  refine ⟨?_, ?_⟩
  · intro m d hm hk
    obtain ⟨d', hm', hkk, hoo⟩ := hget m d hm
    have hk' : d'.kind = .document := by rw [← hkk]; exact hk
    by_cases hin : m ∈ preorder t n
    · exact absurd hk' (hnodoc m hin d' hm')
    · rw [hoo, if_neg hin]
      exact h.documentIsOwnNodeDocument m d' hm' hk'
  · intro c p hp
    have hpar : parentOf t c = some p := by
      rw [parentOf_setOwnerDocument] at hp; exact hp
    have hcd : ∃ cd, t.get? c = some cd := by
      obtain ⟨cd, hcd, _⟩ := parentOf_eq_some hpar; exact ⟨cd, hcd⟩
    obtain ⟨cd, hcd⟩ := hcd
    obtain ⟨pd, hpd⟩ := exists_data_of_parentOf hwf hpar
    -- 部分木の内と外をまたぐ辺は無い。
    have hiff : c ∈ preorder t n ↔ p ∈ preorder t n := by
      constructor
      · intro hin
        obtain ⟨nd, hnd⟩ := exists_data_of_mem_preorder hin
        rcases (mem_preorder_iff hwf hnd c).mp hin with rfl | hanc
        · exact absurd hpar (by rw [hnp]; simp)
        · exact (mem_preorder_iff hwf hnd p).mpr
            (inclusiveAncestor_of_ancestor_parent hanc hpar)
      · intro hin
        obtain ⟨nd, hnd⟩ := exists_data_of_mem_preorder hin
        exact (mem_preorder_iff hwf hnd c).mpr
          ((mem_preorder_iff hwf hnd p).mp hin |>.trans_inclusive
            (InclusiveAncestor.of_ancestor (Ancestor.step hpar)))
    rw [hown, hown, hcd, hpd]
    simp only [Option.map_some]
    by_cases hin : c ∈ preorder t n
    · rw [if_pos hin, if_pos (hiff.mp hin)]
    · rw [if_neg hin, if_neg (fun hc => hin (hiff.mpr hc))]
      have := h.treeEdgePreservesNodeDocument c p hpar
      simp only [ownerDocumentOf, hcd, hpd, Option.map_some] at this
      exact this

/-- `setOwnerDocument` は部分木の中を `doc` に、外を元のままにする。 -/
theorem ownerDocumentOf_setOwnerDocument_eq (t : Tree) (n doc m : NodeId) :
    ownerDocumentOf (setOwnerDocument t n doc) m =
      (t.get? m).map fun d => if m ∈ preorder t n then doc else d.ownerDocument := by
  simp only [ownerDocumentOf, get?_setOwnerDocument, Option.map_map]
  cases t.get? m <;> simp <;> split <;> rfl

/-- `n` は自分の preorder に入っている。 -/
theorem mem_preorder_self {t : Tree} (hwf : WellFormed t) {n : NodeId} {d : NodeData}
    (hn : t.get? n = some d) : n ∈ preorder t n :=
  (mem_preorder_iff hwf hn n).mpr (InclusiveAncestor.refl t n)

end Dom
