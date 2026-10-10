import Dom.Mutation.Variadic
import Dom.Validity.Create
import Dom.Validity.AttrIds

/-!
# 参照されなくなった node を消しても、状態は妥当なままである

`discard`（`Dom/Mutation/Variadic.lean`）が消すのは、parent・children・attribute を持たず、Document でなく、
live range・iterator・registered observer のどれからも指されていない node だけである。
そのような node は、木の他の node の parent・children・node document にも現れない（well-formed なので）。
だから消しても、残る node の parent・children・kind・node document は変わらず、admissibility の
七つの成分と attribute の id の一意性はそのまま保たれる。
-/

namespace Dom

theorem Tree.get?_eraseNode (t : Tree) (n m : NodeId) :
    (t.eraseNode n).get? m = if n = m then none else t.get? m :=
  NodeStore.get?_erase t.nodes n m

/-- `unreferenced` が言うことのうち、admissibility に要るもの。 -/
theorem unreferenced_spec {s : DOMState} {n : NodeId} (h : unreferenced s n = true) :
    ∃ d, s.tree.get? n = some d ∧ d.parent = none ∧ d.children = [] ∧ d.attributes = [] ∧
      d.kind ≠ .document ∧
      (∀ r ∈ s.ranges, r.start.node ≠ n ∧ r.«end».node ≠ n) ∧
      (∀ it ∈ s.iterators, it.root ≠ n ∧ it.reference ≠ n) ∧
      (∀ r ∈ s.registrations, r.node ≠ n) := by
  unfold unreferenced at h
  split at h
  · cases h
  · rename_i d hd
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, List.isEmpty_iff, bne_iff_ne, ne_eq,
      List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hp, hc⟩, ha⟩, hk⟩, hr⟩, hi⟩, -⟩, -⟩, hreg⟩, -⟩ := h
    exact ⟨d, hd, hp, hc, ha, hk, fun r hr' => (hr r hr'), fun it hit => (hi it hit),
      fun r hr' => (hreg r hr').1⟩

section Erase

variable {s : DOMState} {n : NodeId} {d : NodeData}

/-- 消した後の木の node は、消す前の木に同じ data である。 -/
theorem get?_of_eraseNode {m : NodeId} {md : NodeData} (h : (s.tree.eraseNode n).get? m = some md) :
    m ≠ n ∧ s.tree.get? m = some md := by
  rw [Tree.get?_eraseNode] at h
  split at h
  · cases h
  · rename_i hne; exact ⟨fun he => hne he.symm, h⟩

theorem get?_eraseNode_ne {m : NodeId} (hne : m ≠ n) :
    (s.tree.eraseNode n).get? m = s.tree.get? m := by
  rw [Tree.get?_eraseNode, if_neg (fun he => hne he.symm)]

variable (hwf : WellFormed s.tree) (hd : s.tree.get? n = some d) (hp : d.parent = none)
  (hc : d.children = []) (hk : d.kind ≠ .document)

include hwf hd hp in
/-- 消す node は誰の child でもない。 -/
theorem not_mem_children_of_isolated {p : NodeId} {pd : NodeData} (hpd : s.tree.get? p = some pd) :
    n ∉ pd.children := by
  intro hm
  obtain ⟨cd, hcd, hcp⟩ := hwf.parent_child p pd hpd n hm
  rw [hd] at hcd
  cases hcd
  rw [hp] at hcp
  cases hcp

include hwf hd hc in
/-- 消す node は誰の parent でもない。 -/
theorem not_parent_of_isolated {c : NodeId} {cd : NodeData} (hcd : s.tree.get? c = some cd) :
    cd.parent ≠ some n := by
  intro hpc
  obtain ⟨pd, hpd, hm⟩ := hwf.child_parent c cd n hcd hpc
  rw [hd] at hpd
  cases hpd
  rw [hc] at hm
  cases hm

include hwf hd hk in
/-- 消す node は誰の node document でもない。 -/
theorem not_owner_of_isolated {m : NodeId} {md : NodeData} (hmd : s.tree.get? m = some md) :
    md.ownerDocument ≠ n := by
  intro he
  obtain ⟨dd, hdd, hkd⟩ := hwf.ownerDocument_is_document m md hmd
  rw [he, hd] at hdd
  cases hdd
  exact hk hkd

include hd hp in
theorem parentOf_eraseNode (m : NodeId) : parentOf (s.tree.eraseNode n) m = parentOf s.tree m := by
  by_cases hm : m = n
  · subst hm
    simp [parentOf, Tree.get?_eraseNode, hd, hp]
  · simp only [parentOf, get?_eraseNode_ne hm]

include hd hc in
theorem childrenOf_eraseNode (m : NodeId) :
    childrenOf (s.tree.eraseNode n) m = childrenOf s.tree m := by
  by_cases hm : m = n
  · subst hm
    simp [childrenOf, Tree.get?_eraseNode, hd, hc]
  · simp only [childrenOf, get?_eraseNode_ne hm]

include hd hp in
theorem ancestor_eraseNode_iff {a b : NodeId} :
    Ancestor (s.tree.eraseNode n) a b ↔ Ancestor s.tree a b := by
  have h := parentOf_eraseNode hd hp
  constructor
  · exact ancestor_of_parentOf_subset (fun x y hxy => by rw [← h]; exact hxy)
  · exact ancestor_of_parentOf_subset (fun x y hxy => by rw [h]; exact hxy)

end Erase

/-- **参照されなくなった node を消しても、admissibility は保たれる。** -/
theorem admissible_discard {s : DOMState} (hv : AdmissibleDOMState s) (n : NodeId) :
    AdmissibleDOMState (discard s n) := by
  unfold discard
  split
  · rename_i hu
    obtain ⟨d, hd, hp, hc, -, hk, hr, hi, hreg⟩ := unreferenced_spec hu
    have hwf := hv.wellFormed
    have hpar := parentOf_eraseNode hd hp
    have hch := childrenOf_eraseNode hd hc
    have hanc : ∀ {a b}, Ancestor (s.tree.eraseNode n) a b ↔ Ancestor s.tree a b :=
      ancestor_eraseNode_iff hd hp
    have hsome : ∀ {m md}, (s.tree.eraseNode n).get? m = some md → m ≠ n ∧ s.tree.get? m = some md :=
      fun h => get?_of_eraseNode (s := s) h
    have hst := hv.structural
    refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_⟩, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩⟩
    -- WellFormed
    · intro p pd hpd c hcm
      obtain ⟨-, hpd'⟩ := hsome hpd
      obtain ⟨cd, hcd, hcp⟩ := hwf.parent_child p pd hpd' c hcm
      have hcn : c ≠ n := fun he => not_mem_children_of_isolated hwf hd hp hpd' (he ▸ hcm)
      exact ⟨cd, by rw [get?_eraseNode_ne hcn]; exact hcd, hcp⟩
    · intro c cd p hcd hcp
      obtain ⟨-, hcd'⟩ := hsome hcd
      obtain ⟨pd, hpd, hm⟩ := hwf.child_parent c cd p hcd' hcp
      have hpn : p ≠ n := fun he => not_parent_of_isolated hwf hd hc hcd' (he ▸ hcp)
      exact ⟨pd, by rw [get?_eraseNode_ne hpn]; exact hpd, hm⟩
    · intro m md hmd
      exact hwf.children_nodup m md (hsome hmd).2
    · intro m hm
      exact hwf.acyclic m (hanc.mp hm)
    · intro m md hmd
      obtain ⟨-, hmd'⟩ := hsome hmd
      obtain ⟨dd, hdd, hkd⟩ := hwf.ownerDocument_is_document m md hmd'
      have hon := not_owner_of_isolated hwf hd hk hmd'
      exact ⟨dd, by rw [get?_eraseNode_ne hon]; exact hdd, hkd⟩
    -- StructurallyValid の残り
    · intro m md hmd; exact hst.documentHasNoParent m md (hsome hmd).2
    · intro m md hmd; exact hst.fragmentHasNoParent m md (hsome hmd).2
    · intro m md hmd; exact hst.childrenOnlyUnderContainers m md (hsome hmd).2
    · intro m md hmd hkm p hpm pd hpd
      exact hst.doctypeParentIsDocument m md (hsome hmd).2 hkm p hpm pd (hsome hpd).2
    -- NodeDocumentsValid
    · intro m md hmd hkm; exact hv.nodeDocuments.documentIsOwnNodeDocument m md (hsome hmd).2 hkm
    · intro c p hcp
      rw [hpar] at hcp
      have h0 := hv.nodeDocuments.treeEdgePreservesNodeDocument c p hcp
      obtain ⟨cd, hcd, hcpp⟩ := (parentOf_eq_some hcp)
      have hcn : c ≠ n := by
        intro he; subst he; rw [hd] at hcd; cases hcd; rw [hp] at hcpp; cases hcpp
      have hpn : p ≠ n := fun he => not_parent_of_isolated hwf hd hc hcd (he ▸ hcpp)
      simp only [ownerDocumentOf, get?_eraseNode_ne hcn, get?_eraseNode_ne hpn]
      exact h0
    -- DocumentTreesValid
    · intro doc dd hdd hkd
      obtain ⟨hdn, hdd'⟩ := hsome hdd
      refine documentChildrenOk_congr_of_children (hch doc) (fun c hcm => ?_)
        (hv.documentTrees.documentChildren doc dd hdd' hkd)
      have hcn : c ≠ n := by
        intro he; subst he
        rw [childrenOf, hdd'] at hcm
        exact not_mem_children_of_isolated hwf hd hp hdd' hcm
      simp only [kindOf, get?_eraseNode_ne hcn]
    -- RangeEndpointsValid
    · intro r hrm
      obtain ⟨⟨sd, hsd, hso⟩, ⟨ed, hed, heo⟩⟩ := hv.rangeEndpoints r hrm
      obtain ⟨hsn, hen⟩ := hr r hrm
      exact ⟨⟨sd, by show (s.tree.eraseNode n).get? _ = _; rw [get?_eraseNode_ne hsn]; exact hsd, hso⟩,
        ⟨ed, by show (s.tree.eraseNode n).get? _ = _; rw [get?_eraseNode_ne hen]; exact hed, heo⟩⟩
    -- IteratorsValid
    · intro it hit
      obtain ⟨⟨rd, hrd⟩, hdesc⟩ := hv.iterators it hit
      obtain ⟨-, hrefn⟩ := hi it hit
      refine ⟨⟨rd, by show (s.tree.eraseNode n).get? _ = _; rw [get?_eraseNode_ne hrefn]; exact hrd⟩, ?_⟩
      rcases hdesc with he | ha
      · exact Or.inl he
      · exact Or.inr (hanc.mpr ha)
    -- ObserverRegistrationsValid
    · intro r hrm
      obtain ⟨hlt, hsm⟩ := hv.observerRegistrations r hrm
      refine ⟨hlt, ?_⟩
      show ((s.tree.eraseNode n).get? r.node).isSome = true
      rw [get?_eraseNode_ne (hreg r hrm)]
      exact hsm
    -- AttributesValid
    · intro m md hmd hkm; exact hv.attributes.onlyElements m md (hsome hmd).2 hkm
    · intro m md hmd; exact hv.attributes.keysNodup m md (hsome hmd).2
    · intro m md hmd; exact hv.attributes.prefixHasNamespace m md (hsome hmd).2
  · exact hv

/-- 列に沿って消しても、admissibility は保たれる。 -/
theorem admissible_discardAll {s : DOMState} (hv : AdmissibleDOMState s) :
    ∀ ns, AdmissibleDOMState (discardAll s ns) := by
  intro ns
  induction ns generalizing s with
  | nil => exact hv
  | cons n rest ih => exact ih (admissible_discard hv n)

/-- **消しても、attribute の id は変わらない。** 消す node は attribute を持たない。 -/
theorem attrFrame_discard (s : DOMState) (n : NodeId) : AttrFrame s (discard s n) := by
  unfold discard
  split
  · rename_i hu
    obtain ⟨d, hd, -, -, ha, -⟩ := unreferenced_spec hu
    refine ⟨fun m => ?_, rfl⟩
    by_cases hm : m = n
    · subst hm
      show attrSigAt (s.tree.eraseNode m) m = attrSigAt s.tree m
      simp [attrSigAt, Tree.get?_eraseNode, hd, ha]
    · show attrSigAt (s.tree.eraseNode n) m = attrSigAt s.tree m
      simp only [attrSigAt, get?_eraseNode_ne hm]
  · exact AttrFrame.of_eq rfl rfl

theorem attrFrame_discardAll (s : DOMState) : ∀ ns, AttrFrame s (discardAll s ns) := by
  intro ns
  induction ns generalizing s with
  | nil => exact AttrFrame.of_eq rfl rfl
  | cons n rest ih => exact (attrFrame_discard s n).trans (ih _)

end Dom
