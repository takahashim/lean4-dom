import Dom.Validity.Preservation
import Dom.Properties.Algorithms

/-!
# §4.2.3 の algorithm による admissibility の保存

`notes/research-foundation-roadmap.md` Phase A の完了条件
「全対象 operation の `preserves_admissible`」に向けて、
まず木に関する三つの層（`StructurallyValid` / `NodeDocumentsValid` /
`DocumentTreesValid`）を algorithm ごとに積み上げる。

`remove` は node を外すだけなので、三つとも無条件に保たれる。
`insert` 側は validity 検査が前提を確立するので、そこで primitive の条件を discharge する。
-/

namespace Dom

/-! ## remove -/

theorem structurallyValid_remove {s s' : DOMState} {n : NodeId} {b : Bool}
    (h : StructurallyValid s.tree) (hr : remove s n b = .ok s') :
    StructurallyValid s'.tree :=
  structurallyValid_detach h (remove_ok hr).2

theorem nodeDocumentsValid_remove {s s' : DOMState} {n : NodeId} {b : Bool}
    (hwf : WellFormed s.tree) (h : NodeDocumentsValid s.tree) (hr : remove s n b = .ok s') :
    NodeDocumentsValid s'.tree :=
  nodeDocumentsValid_detach hwf h (remove_ok hr).2

/--
`remove` は Document の children から一つ外すだけなので、document tree の制約は保たれる。

element / doctype / Text の個数はどれも増えず、
element より後ろの doctype も増えないためである。
-/
theorem documentChildrenOk_of_detach {t t' : Tree} {n : NodeId}
    (hwf : WellFormed t) (hd : detach t n = .ok t') {doc : NodeId}
    (h : DocumentChildrenOk t doc) : DocumentChildrenOk t' doc := by
  have hkind : ∀ m, kindOf t' m = kindOf t m := kindPreserving_detach hd
  -- children は、旧 parent なら `removeAll`、それ以外なら不変。
  have hch : ∃ a, childrenOf t' doc = ListUtil.removeAll (childrenOf t doc) a := by
    cases hp : parentOf t n with
    | none =>
      exact ⟨n, by
        rw [detach_of_no_parent hp (by
          rcases detach_ok_cases hd with ⟨d, hdd, _, _⟩ | ⟨d, _, _, hdd, _, _, _⟩ <;>
            simp [hdd])] at hd
        rw [← Except.ok.inj hd, ListUtil.removeAll_eq_self]
        intro hmem
        exact absurd (parentOf_of_mem_childrenOf hwf hmem) (by rw [hp]; simp)⟩
    | some p =>
      by_cases hdp : doc = p
      · subst hdp
        exact ⟨n, detach_childrenOf hwf hp hd⟩
      · exact ⟨n, by
          rw [detach_childrenOf_ne hp hd hdp, ListUtil.removeAll_eq_self]
          intro hmem
          have := parentOf_of_mem_childrenOf hwf hmem
          rw [hp] at this
          exact hdp (Option.some.inj this).symm⟩
  obtain ⟨a, hch⟩ := hch
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold elementChildren at h1 ⊢
    simp only [hch, hkind]
    exact Nat.le_trans (ListUtil.length_filter_removeAll a _ _) h1
  · unfold doctypeChildren at h2 ⊢
    simp only [hch, hkind]
    exact Nat.le_trans (ListUtil.length_filter_removeAll a _ _) h2
  · unfold textChildren at h3 ⊢
    simp only [hch, hkind]
    exact ListUtil.filter_removeAll_eq_nil h3
  · intro e he
    have hmemA : e ∈ ListUtil.removeAll (childrenOf t doc) a ∧
        (kindOf t e == some NodeKind.element) = true := by
      unfold elementChildren at he
      simp only [hch, hkind] at he
      exact List.mem_filter.mp he
    have hne : e ≠ a := ((ListUtil.mem_removeAll _ _ _).mp hmemA.1).1
    have hmem : e ∈ childrenOf t doc := ((ListUtil.mem_removeAll _ _ _).mp hmemA.1).2
    have he' : e ∈ elementChildren t doc := by
      unfold elementChildren
      exact List.mem_filter.mpr ⟨hmem, hmemA.2⟩
    have h4e := h4 e he'
    unfold doctypeFollows at h4e ⊢
    simp only [hch, hkind]
    cases hs : ListUtil.splitAt? (childrenOf t doc) e with
    | none =>
      exfalso
      have := ListUtil.splitAt?_isSome_of_mem hmem
      rw [hs] at this
      simp at this
    | some q =>
      obtain ⟨u, v⟩ := q
      rw [hs] at h4e
      rw [ListUtil.splitAt?_removeAll hne hs]
      rw [Bool.eq_false_iff] at h4e ⊢
      intro hcon
      obtain ⟨x, hx, hxk⟩ := List.any_eq_true.mp hcon
      exact h4e (List.any_eq_true.mpr ⟨x, ((ListUtil.mem_removeAll _ _ _).mp hx).2, hxk⟩)

/--
`remove` は Document の children から一つ外すだけなので、document tree の制約は保たれる。

element / doctype / Text の個数はどれも増えず、
element より後ろの doctype も増えないためである。
-/
theorem documentTreesValid_remove {s s' : DOMState} {n : NodeId} {b : Bool}
    (hwf : WellFormed s.tree) (h : DocumentTreesValid s.tree) (hr : remove s n b = .ok s') :
    DocumentTreesValid s'.tree := by
  have hd := (remove_ok hr).2
  refine ⟨fun doc d hdoc hk => ?_⟩
  refine documentChildrenOk_of_detach hwf hd ?_
  have hkind := kindPreserving_detach hd doc
  cases hdoc' : s.tree.get? doc with
  | none =>
    exfalso
    rw [hdoc, hdoc'] at hkind
    simp at hkind
  | some d' =>
    refine h.documentChildren doc d' hdoc' ?_
    rw [hdoc, hdoc'] at hkind
    simpa [hk] using hkind.symm

end Dom
