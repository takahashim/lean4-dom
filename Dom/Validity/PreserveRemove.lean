import Dom.Validity.PreserveShared

/-!
# `remove` / `removeEach` による保存

node を外すだけなので三つの層とも無条件に保たれる。
kind の事実が kind を変えない操作で移ることもここ。
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

/-- `detach` の後の children は、元の children から高々一つ取り除いたものである。 -/
theorem detach_childrenOf_removeAll {t t' : Tree} {n : NodeId}
    (hwf : WellFormed t) (hd : detach t n = .ok t') (p : NodeId) :
    childrenOf t' p = ListUtil.removeAll (childrenOf t p) n := by
  cases hp : parentOf t n with
  | none =>
    rw [detach_of_no_parent hp (by
      rcases detach_ok_cases hd with ⟨d, hdd, _, _⟩ | ⟨d, _, _, hdd, _, _, _⟩ <;>
        simp [hdd])] at hd
    rw [← Except.ok.inj hd, ListUtil.removeAll_eq_self]
    intro hmem
    exact absurd (parentOf_of_mem_childrenOf hwf hmem) (by rw [hp]; simp)
  | some q =>
    by_cases hdp : p = q
    · subst hdp
      exact detach_childrenOf hwf hp hd
    · rw [detach_childrenOf_ne hp hd hdp, ListUtil.removeAll_eq_self]
      intro hmem
      have hpar := parentOf_of_mem_childrenOf hwf hmem
      rw [hp] at hpar
      exact hdp (Option.some.inj hpar).symm

/-- children から取り除くだけなら、「後ろに doctype がある」が新たに成り立つことはない。 -/
theorem doctypeFollows_of_removeAll {t t' : Tree} {p c a : NodeId}
    (hkind : ∀ m, kindOf t' m = kindOf t m)
    (hch : childrenOf t' p = ListUtil.removeAll (childrenOf t p) a)
    (h : doctypeFollows t p c = false) : doctypeFollows t' p c = false := by
  by_cases hca : c = a
  · subst hca
    exact doctypeFollows_of_splitAt?_none
      (by rw [hch]; exact ListUtil.splitAt?_eq_none_of_not_mem (ListUtil.not_mem_removeAll _ _))
  · cases hs : ListUtil.splitAt? (childrenOf t p) c with
    | none =>
      exact doctypeFollows_of_splitAt?_none
        (by rw [hch]; exact ListUtil.splitAt?_removeAll_none hs)
    | some q =>
      obtain ⟨u, v⟩ := q
      rw [doctypeFollows_of_splitAt? hs] at h
      rw [doctypeFollows_of_splitAt? (by rw [hch]; exact ListUtil.splitAt?_removeAll hca hs)]
      simp only [hkind]
      rw [Bool.eq_false_iff] at h ⊢
      intro hcon
      obtain ⟨x, hx, hxk⟩ := List.any_eq_true.mp hcon
      exact h (List.any_eq_true.mpr ⟨x, ((ListUtil.mem_removeAll _ _ _).mp hx).2, hxk⟩)

/--
`remove` は Document の children から一つ外すだけなので、document tree の制約は保たれる。

element / doctype / Text の個数はどれも増えず、
element より後ろの doctype も増えないためである。
-/
theorem documentChildrenOk_of_detach {t t' : Tree} {n : NodeId}
    (hwf : WellFormed t) (hd : detach t n = .ok t') {doc : NodeId}
    (h : DocumentChildrenOk t doc) : DocumentChildrenOk t' doc := by
  have hkind : ∀ m, kindOf t' m = kindOf t m := (shapePreserving_detach hd).kind
  have hch := detach_childrenOf_removeAll hwf hd doc
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold elementChildren at h1 ⊢
    simp only [hch, hkind]
    exact Nat.le_trans (ListUtil.length_filter_removeAll n _ _) h1
  · unfold doctypeChildren at h2 ⊢
    simp only [hch, hkind]
    exact Nat.le_trans (ListUtil.length_filter_removeAll n _ _) h2
  · unfold textChildren at h3 ⊢
    simp only [hch, hkind]
    exact ListUtil.filter_removeAll_eq_nil h3
  · intro e he
    have hmemA : e ∈ ListUtil.removeAll (childrenOf t doc) n ∧
        (kindOf t e == some NodeKind.element) = true := by
      unfold elementChildren at he
      simp only [hch, hkind] at he
      exact List.mem_filter.mp he
    have hmem : e ∈ childrenOf t doc := ((ListUtil.mem_removeAll _ _ _).mp hmemA.1).2
    have he' : e ∈ elementChildren t doc := by
      unfold elementChildren
      exact List.mem_filter.mpr ⟨hmem, hmemA.2⟩
    exact doctypeFollows_of_removeAll hkind hch (h4 e he')

/-- `detach` は「element の子が無い」を壊さない。 -/
theorem elementChildren_eq_nil_of_detach {t t' : Tree} {n : NodeId}
    (hwf : WellFormed t) (hd : detach t n = .ok t') {p : NodeId}
    (h : elementChildren t p = []) : elementChildren t' p = [] := by
  have hkind : ∀ m, kindOf t' m = kindOf t m := (shapePreserving_detach hd).kind
  have hch := detach_childrenOf_removeAll hwf hd p
  unfold elementChildren at h ⊢
  simp only [hch, hkind]
  exact ListUtil.filter_removeAll_eq_nil h

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
  have hkind := (shapePreserving_detach hd).kind doc
  cases hdoc' : s.tree.get? doc with
  | none =>
    exfalso
    rw [hdoc, hdoc'] at hkind
    simp at hkind
  | some d' =>
    refine h.documentChildren doc d' hdoc' ?_
    rw [hdoc, hdoc'] at hkind
    simpa [hk] using hkind.symm

/-! ## removeEach -/

theorem structurallyValid_removeEach :
    ∀ (ns : List NodeId) {s s' : DOMState} {b : Bool},
      StructurallyValid s.tree → removeEach s ns b = .ok s' → StructurallyValid s'.tree
  | [], _, _, _, h, hr => by rw [← Except.ok.inj hr]; exact h
  | n :: ns, s, s', b, h, hr => by
    simp only [removeEach] at hr
    split at hr
    · simp at hr
    · next s₁ h₁ => exact structurallyValid_removeEach ns (structurallyValid_remove h h₁) hr

theorem nodeDocumentsValid_removeEach :
    ∀ (ns : List NodeId) {s s' : DOMState} {b : Bool},
      StructurallyValid s.tree → NodeDocumentsValid s.tree → removeEach s ns b = .ok s' →
      NodeDocumentsValid s'.tree
  | [], _, _, _, _, h, hr => by rw [← Except.ok.inj hr]; exact h
  | n :: ns, s, s', b, hs, h, hr => by
    simp only [removeEach] at hr
    split at hr
    · simp at hr
    · next s₁ h₁ =>
      exact nodeDocumentsValid_removeEach ns (structurallyValid_remove hs h₁)
        (nodeDocumentsValid_remove hs.wellFormed h h₁) hr

/-! ## kind の事実は kind を変えない操作で移る -/

theorem kindFact_of_kindPreserving {t t' : Tree} (h : ShapePreserving t t') {n : NodeId}
    {P : NodeKind → Prop} (hp : ∀ d, t.get? n = some d → P d.kind) :
    ∀ d, t'.get? n = some d → P d.kind := by
  intro d hd
  have hk := h.kind n
  rw [hd] at hk
  cases hd' : t.get? n with
  | none => rw [hd'] at hk; simp at hk
  | some d' =>
    rw [hd'] at hk
    simp only [Option.map_some, Option.some.injEq] at hk
    rw [hk]
    exact hp d' hd'

/-- kind が同じなら、node の有無も一致する。 -/
theorem shapePreserving_get? {t t' : Tree} (h : ShapePreserving t t') {m : NodeId} {d : NodeData}
    (hd : t'.get? m = some d) : ∃ d₀, t.get? m = some d₀ ∧ d₀.kind = d.kind := by
  have hk := h.kind m
  rw [hd] at hk
  cases hd₀ : t.get? m with
  | none => rw [hd₀] at hk; simp at hk
  | some d₀ =>
    rw [hd₀] at hk
    simp only [Option.map_some, Option.some.injEq] at hk
    exact ⟨d₀, rfl, hk.symm⟩

/-- 「doctype を入れる先は Document である」という事実も kind を変えない操作で移る。 -/
theorem doctypeFact_of_kindPreserving {t t' : Tree} (h : ShapePreserving t t') {n p : NodeId}
    (hp : ∀ nd, t.get? n = some nd → nd.kind = .documentType →
      ∀ pd, t.get? p = some pd → pd.kind = .document) :
    ∀ nd, t'.get? n = some nd → nd.kind = .documentType →
      ∀ pd, t'.get? p = some pd → pd.kind = .document := by
  intro nd hnd hk pd hpd
  obtain ⟨nd₀, hnd₀, hkn⟩ := shapePreserving_get? h hnd
  obtain ⟨pd₀, hpd₀, hkp⟩ := shapePreserving_get? h hpd
  rw [← hkp]
  exact hp nd₀ hnd₀ (by rw [hkn]; exact hk) pd₀ hpd₀

end Dom
