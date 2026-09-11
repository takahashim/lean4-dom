import Dom.Validity.Preservation
import Dom.Properties.Algorithms
import Dom.Properties.CharacterData

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

/-! ## 木の形を変えない操作 -/

/--
kind と children が同じなら、document tree の制約も同じである。

`setOwnerDocument` と `replaceData` はどちらもこれに当たる。
-/
theorem documentTreesValid_of_sameShape {t t' : Tree}
    (hkind : ∀ m, kindOf t' m = kindOf t m)
    (hch : ∀ m, childrenOf t' m = childrenOf t m)
    (h : DocumentTreesValid t) : DocumentTreesValid t' := by
  have helem : ∀ m, elementChildren t' m = elementChildren t m := by
    intro m; unfold elementChildren; simp [hch, hkind]
  have hdt : ∀ m, doctypeChildren t' m = doctypeChildren t m := by
    intro m; unfold doctypeChildren; simp [hch, hkind]
  have htx : ∀ m, textChildren t' m = textChildren t m := by
    intro m; unfold textChildren; simp [hch, hkind]
  have hfol : ∀ m c, doctypeFollows t' m c = doctypeFollows t m c := by
    intro m c; unfold doctypeFollows; simp [hch, hkind]
  refine ⟨fun doc d hdoc hk => ?_⟩
  have hdoc' : ∃ d', t.get? doc = some d' ∧ d'.kind = .document := by
    have := hkind doc
    rw [kindOf, kindOf, hdoc] at this
    cases hd' : t.get? doc with
    | none => rw [hd'] at this; simp at this
    | some d' =>
      rw [hd'] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨d', rfl, by rw [← this]; exact hk⟩
  obtain ⟨d', hd', hk'⟩ := hdoc'
  obtain ⟨h1, h2, h3, h4⟩ := h.documentChildren doc d' hd' hk'
  exact ⟨by rw [helem]; exact h1, by rw [hdt]; exact h2, by rw [htx]; exact h3,
    fun e he => by rw [hfol]; exact h4 e (by rw [← helem]; exact he)⟩

/-! ## ensure pre-insert validity が確立する kind の事実 -/

/--
step 1。parent は Document / DocumentFragment / Element のいずれかである。
すなわち children を持てる kind である。
-/
theorem ensurePreInsertionValidity_parentCanHaveChildren {t : Tree} {node parent : NodeId}
    {child : Option NodeId} {excl : List NodeId}
    (h : ensurePreInsertionValidity t node parent child excl = .ok ()) :
    ∀ pd, t.get? parent = some pd → pd.kind.canHaveChildren = true := by
  intro pd hpd
  unfold ensurePreInsertionValidity at h
  rw [hpd] at h
  simp only at h
  split at h
  · simp at h
  · split at h
    · next hk => simp at h
    · next hk =>
      simp only [Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hk
      cases hkk : pd.kind <;> simp_all [NodeKind.canHaveChildren]

/-- step 5。parent が Document でないなら doctype は入れられない。逆に言えば、doctype を入れる先は Document である。 -/
theorem ensurePreInsertionValidity_doctypeParentIsDocument {t : Tree} {node parent : NodeId}
    {child : Option NodeId} {excl : List NodeId}
    (h : ensurePreInsertionValidity t node parent child excl = .ok ()) :
    ∀ nd, t.get? node = some nd → nd.kind = .documentType →
      ∀ pd, t.get? parent = some pd → pd.kind = .document := by
  intro nd hnd hk pd hpd
  unfold ensurePreInsertionValidity at h
  rw [hpd, hnd] at h
  simp only at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · next hkp => simp [hk] at h
          · next hkp => simpa using hkp

/-- step 3。`child` が指定されていれば、その parent は `parent` である。 -/
theorem ensurePreInsertionValidity_childParent {t : Tree} {node parent : NodeId}
    {child : Option NodeId} {excl : List NodeId}
    (h : ensurePreInsertionValidity t node parent child excl = .ok ()) :
    ∀ c, child = some c → parentOf t c = some parent := by
  intro c hc
  subst hc
  unfold ensurePreInsertionValidity at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · next hk =>
            simp only [Bool.not_eq_true', childHasParent, decide_eq_false_iff_not,
              Decidable.not_not] at hk
            exact hk

/-- step 4。node は DocumentFragment / DocumentType / Element / CharacterData であり、Document ではない。 -/
theorem ensurePreInsertionValidity_nodeNotDocument {t : Tree} {node parent : NodeId}
    {child : Option NodeId} {excl : List NodeId}
    (h : ensurePreInsertionValidity t node parent child excl = .ok ()) :
    ∀ nd, t.get? node = some nd → nd.kind ≠ .document := by
  intro nd hnd
  unfold ensurePreInsertionValidity at h
  split at h
  · simp at h
  · next pd hpd =>
    rw [hnd] at h
    simp only at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · next hk => simp at h
          · next hk =>
            simp only [Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hk
            cases hkk : nd.kind <;> simp_all [NodeKind.isCharacterData]

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
  unfold doctypeFollows at h ⊢
  simp only [hch, hkind]
  by_cases hca : c = a
  · subst hca
    rw [ListUtil.splitAt?_eq_none_of_not_mem (ListUtil.not_mem_removeAll _ _)]
  · cases hs : ListUtil.splitAt? (childrenOf t p) c with
    | none => rw [ListUtil.splitAt?_removeAll_none hs]
    | some q =>
      obtain ⟨u, v⟩ := q
      rw [hs] at h
      rw [ListUtil.splitAt?_removeAll hca hs]
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
  have hkind : ∀ m, kindOf t' m = kindOf t m := kindPreserving_detach hd
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
  have hkind : ∀ m, kindOf t' m = kindOf t m := kindPreserving_detach hd
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

theorem kindFact_of_kindPreserving {t t' : Tree} (h : KindPreserving t t') {n : NodeId}
    {P : NodeKind → Prop} (hp : ∀ d, t.get? n = some d → P d.kind) :
    ∀ d, t'.get? n = some d → P d.kind := by
  intro d hd
  have hk := h n
  rw [hd] at hk
  cases hd' : t.get? n with
  | none => rw [hd'] at hk; simp at hk
  | some d' =>
    rw [hd'] at hk
    simp only [Option.map_some, Option.some.injEq] at hk
    rw [hk]
    exact hp d' hd'

/-- kind が同じなら、node の有無も一致する。 -/
theorem kindPreserving_get? {t t' : Tree} (h : KindPreserving t t') {m : NodeId} {d : NodeData}
    (hd : t'.get? m = some d) : ∃ d₀, t.get? m = some d₀ ∧ d₀.kind = d.kind := by
  have hk := h m
  rw [hd] at hk
  cases hd₀ : t.get? m with
  | none => rw [hd₀] at hk; simp at hk
  | some d₀ =>
    rw [hd₀] at hk
    simp only [Option.map_some, Option.some.injEq] at hk
    exact ⟨d₀, rfl, hk.symm⟩

/-- 「doctype を入れる先は Document である」という事実も kind を変えない操作で移る。 -/
theorem doctypeFact_of_kindPreserving {t t' : Tree} (h : KindPreserving t t') {n p : NodeId}
    (hp : ∀ nd, t.get? n = some nd → nd.kind = .documentType →
      ∀ pd, t.get? p = some pd → pd.kind = .document) :
    ∀ nd, t'.get? n = some nd → nd.kind = .documentType →
      ∀ pd, t'.get? p = some pd → pd.kind = .document := by
  intro nd hnd hk pd hpd
  obtain ⟨nd₀, hnd₀, hkn⟩ := kindPreserving_get? h hnd
  obtain ⟨pd₀, hpd₀, hkp⟩ := kindPreserving_get? h hpd
  rw [← hkp]
  exact hp nd₀ hnd₀ (by rw [hkn]; exact hk) pd₀ hpd₀

/-! ## insertAt が Document の children 制約に与える効果 -/

/-- children の分割が与えられれば `splitAt?` はその分割を返す。 -/
theorem splitAt?_childrenOf_of_split {t : Tree} (hwf : WellFormed t) {parent c : NodeId}
    {s₁ s₂ : List NodeId} (h : childrenOf t parent = s₁ ++ c :: s₂) :
    ListUtil.splitAt? (childrenOf t parent) c = some (s₁, s₂) := by
  have hnd : (childrenOf t parent).Nodup := childrenOf_nodup hwf parent
  rw [h] at hnd
  have hcnot : c ∉ s₁ := fun hm => (List.nodup_append.mp hnd).2.2 c hm c (by simp) rfl
  rw [h]
  exact ListUtil.splitAt?_append_cons_self hcnot s₂

/--
挿入点より後ろの node から見た「後ろに doctype があるか」は、
挿入した node の kind によらず変わらない。
-/
theorem doctypeFollows_split_of_mem_right {t t' : Tree} {parent node : NodeId}
    (hkind : ∀ m, kindOf t' m = kindOf t m) {A B : List NodeId}
    (hAB : childrenOf t parent = A ++ B) (hAB' : childrenOf t' parent = A ++ node :: B)
    {e : NodeId} (hnotA : e ∉ A) (hne : e ≠ node) (hmemB : e ∈ B) :
    doctypeFollows t' parent e = doctypeFollows t parent e := by
  unfold doctypeFollows
  simp only [hAB, hAB', hkind]
  obtain ⟨u, v, hs⟩ := ListUtil.exists_splitAt?_of_mem hmemB
  have hnotA' : e ∉ A ++ [node] := by
    intro hm
    rcases List.mem_append.mp hm with h | h
    · exact hnotA h
    · exact hne (by simpa using h)
  have hrw : A ++ node :: B = (A ++ [node]) ++ B := by simp
  rw [hrw, ListUtil.splitAt?_append_right hnotA' hs, ListUtil.splitAt?_append_right hnotA hs]

/--
挿入する node が doctype でなければ、
他の node から見た「後ろに doctype があるか」は変わらない。
-/
theorem doctypeFollows_insertAt_of_ne {t t' : Tree} {parent node : NodeId}
    {child : Option NodeId} (hwf : WellFormed t) (hi : insertAt t parent node child = .ok t')
    (hdoctype : (kindOf t node == some NodeKind.documentType) = false) {e : NodeId}
    (hne : e ≠ node) : doctypeFollows t' parent e = doctypeFollows t parent e := by
  have hkind : ∀ m, kindOf t' m = kindOf t m := kindPreserving_insertAt hi
  obtain ⟨A, B, hAB, hAB'⟩ := insertAt_children_split_general hwf hi
  have hnot : node ∉ childrenOf t parent := insertAt_node_not_mem hwf hi
  have hnotA : node ∉ A := fun hm => hnot (by rw [hAB]; exact List.mem_append_left _ hm)
  unfold doctypeFollows
  simp only [hAB, hAB', hkind]
  by_cases hmem : e ∈ A
  · obtain ⟨u, v, hs⟩ := ListUtil.exists_splitAt?_of_mem hmem
    rw [ListUtil.splitAt?_append_left hs B, ListUtil.splitAt?_append_left hs (node :: B)]
    simp [List.any_append, hdoctype]
  · by_cases hmemB : e ∈ B
    · obtain ⟨u, v, hs⟩ := ListUtil.exists_splitAt?_of_mem hmemB
      have hnotA' : e ∉ A ++ [node] := by
        intro hm
        rcases List.mem_append.mp hm with h | h
        · exact hmem h
        · exact hne (by simpa using h)
      have hrw : A ++ node :: B = (A ++ [node]) ++ B := by simp
      rw [hrw, ListUtil.splitAt?_append_right hnotA' hs,
        ListUtil.splitAt?_append_right hmem hs]
    · have hnotAB : e ∉ A ++ B := by
        intro hm; rcases List.mem_append.mp hm with h | h
        · exact hmem h
        · exact hmemB h
      have hnotAB' : e ∉ A ++ node :: B := by
        intro hm
        rcases List.mem_append.mp hm with h | h
        · exact hmem h
        · rcases List.mem_cons.mp h with h | h
          · exact hne h
          · exact hmemB h
      rw [ListUtil.splitAt?_eq_none_of_not_mem hnotAB,
        ListUtil.splitAt?_eq_none_of_not_mem hnotAB']

/-- 挿入した node 自身の後ろに doctype が無いことは、validity 検査から従う。 -/
theorem doctypeFollows_insertAt_self {t t' : Tree} {parent node : NodeId}
    {child : Option NodeId} (hwf : WellFormed t) (hi : insertAt t parent node child = .ok t')
    (hafter : ∀ c, child = some c →
      (kindOf t c == some NodeKind.documentType) = false ∧ doctypeFollows t parent c = false) :
    doctypeFollows t' parent node = false := by
  have hkind : ∀ m, kindOf t' m = kindOf t m := kindPreserving_insertAt hi
  have hnot : node ∉ childrenOf t parent := insertAt_node_not_mem hwf hi
  unfold doctypeFollows
  cases child with
  | none =>
    have hch : childrenOf t' parent = childrenOf t parent ++ node :: [] := by
      rw [insertAt_childrenOf hwf hi, ListUtil.insertBefore_none]
    rw [hch, ListUtil.splitAt?_append_cons_self hnot]
    simp
  | some c =>
    obtain ⟨s₁, s₂, h₁, h₂⟩ := insertAt_children_split hwf hi
    have hnots₁ : node ∉ s₁ := fun hm => hnot (by rw [h₁]; exact List.mem_append_left _ hm)
    have hrw : s₁ ++ node :: c :: s₂ = s₁ ++ node :: (c :: s₂) := rfl
    rw [h₂, hrw, ListUtil.splitAt?_append_cons_self hnots₁]
    obtain ⟨hc, hfol⟩ := hafter c rfl
    have hs : ListUtil.splitAt? (childrenOf t parent) c = some (s₁, s₂) :=
      splitAt?_childrenOf_of_split hwf h₁
    unfold doctypeFollows at hfol
    rw [hs] at hfol
    simp only [List.any_cons, hkind, Bool.or_eq_false_iff]
    exact ⟨hc, hfol⟩

/--
`insertAt` は parent の children に一つ挿すだけなので、
挿す node の kind に関する条件があれば Document の children 制約は保たれる。

条件は §4.2.3 "ensure pre-insertion validity" step 6 / 9 と
"move" step 5 / 6 が確立するものと同じである。
-/
theorem documentChildrenOk_of_insertAt {t t' : Tree} {parent node : NodeId}
    {child : Option NodeId} (hwf : WellFormed t) (hi : insertAt t parent node child = .ok t')
    (htext : ∀ k, kindOf t node = some k → k.isText = false)
    (helem : kindOf t node = some NodeKind.element →
      elementChildren t parent = [] ∧
        ∀ c, child = some c →
          (kindOf t c == some NodeKind.documentType) = false ∧
            doctypeFollows t parent c = false)
    (hdoct : kindOf t node = some NodeKind.documentType →
      doctypeChildren t parent = [] ∧
        (∀ c, child = some c → elementPrecedes t parent c = false) ∧
        (child = none → elementChildren t parent = []))
    (h : DocumentChildrenOk t parent) : DocumentChildrenOk t' parent := by
  have hkind : ∀ m, kindOf t' m = kindOf t m := kindPreserving_insertAt hi
  have hch : childrenOf t' parent = ListUtil.insertBefore (childrenOf t parent) child node :=
    insertAt_childrenOf hwf hi
  have hnot : node ∉ childrenOf t parent := insertAt_node_not_mem hwf hi
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- element の子は高々一つ
    unfold elementChildren at h1 ⊢
    simp only [hch, hkind, ListUtil.length_filter_insertBefore]
    by_cases he : (kindOf t node == some NodeKind.element) = true
    · have hnil : elementChildren t parent = [] := (helem (by simpa using he)).1
      unfold elementChildren at hnil
      simp [he, hnil]
    · simp only [Bool.not_eq_true] at he
      simpa [he] using h1
  · -- doctype の子は高々一つ
    unfold doctypeChildren at h2 ⊢
    simp only [hch, hkind, ListUtil.length_filter_insertBefore]
    by_cases he : (kindOf t node == some NodeKind.documentType) = true
    · have hnil : doctypeChildren t parent = [] := (hdoct (by simpa using he)).1
      unfold doctypeChildren at hnil
      simp [he, hnil]
    · simp only [Bool.not_eq_true] at he
      simpa [he] using h2
  · -- Text の子は無い。述語は `textChildren` が生成した match なので goal 側から取る。
    unfold textChildren at h3 ⊢
    simp only [hch, hkind]
    refine Eq.trans (ListUtil.filter_insertBefore_of_neg ?_ _ _) h3
    cases hk : kindOf t node with
    | none => rfl
    | some k => exact htext k hk
  · -- element より後ろに doctype は無い
    intro e he
    have hek : (kindOf t e == some NodeKind.element) = true := by
      unfold elementChildren at he
      have hk := (List.mem_filter.mp he).2
      simpa [hkind] using hk
    have hmem : e = node ∨ e ∈ elementChildren t parent := by
      unfold elementChildren at he ⊢
      simp only [hch, hkind] at he
      obtain ⟨hm, hk⟩ := List.mem_filter.mp he
      rcases (ListUtil.mem_insertBefore _ _ _ _).mp hm with hx | hx
      · exact Or.inl hx
      · exact Or.inr (List.mem_filter.mpr ⟨hx, hk⟩)
    rcases hmem with rfl | hmem
    · exact doctypeFollows_insertAt_self hwf hi (helem (by simpa using hek)).2
    · have hne : e ≠ node := by
        intro hx
        exact hnot (hx ▸ (List.mem_filter.mp hmem).1)
      by_cases hnd : (kindOf t node == some NodeKind.documentType) = true
      · -- node が doctype の場合。挿入点より前に element は無い。
        obtain ⟨_, hprec, hnone⟩ := hdoct (by simpa using hnd)
        have hmemch : e ∈ childrenOf t parent := (List.mem_filter.mp hmem).1
        cases hcv : child with
        | none =>
          exfalso
          rw [hnone hcv] at hmem
          simp at hmem
        | some c =>
          have hi' : insertAt t parent node (some c) = .ok t' := hcv ▸ hi
          obtain ⟨s₁, s₂, h₁, h₂⟩ := insertAt_children_split hwf hi'
          have hs : ListUtil.splitAt? (childrenOf t parent) c = some (s₁, s₂) :=
            splitAt?_childrenOf_of_split hwf h₁
          have hprec' : (s₁.any fun x => kindOf t x == some NodeKind.element) = false := by
            have hp := hprec c hcv
            unfold elementPrecedes at hp
            rw [hs] at hp
            exact hp
          have hnotA : e ∉ s₁ := by
            intro hm
            have hany : (s₁.any fun x => kindOf t x == some NodeKind.element) = true :=
              List.any_eq_true.mpr ⟨e, hm, (List.mem_filter.mp hmem).2⟩
            rw [hprec'] at hany
            simp at hany
          have hmemB : e ∈ c :: s₂ := by
            rw [h₁] at hmemch
            rcases List.mem_append.mp hmemch with hx | hx
            · exact absurd hx hnotA
            · exact hx
          rw [doctypeFollows_split_of_mem_right hkind (A := s₁) (B := c :: s₂) h₁ h₂
            hnotA hne hmemB]
          exact h4 e hmem
      · rw [doctypeFollows_insertAt_of_ne hwf hi (by simpa using hnd) hne]
        exact h4 e hmem

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
    intro c; unfold doctypeFollows; simp only [hch, hkind]
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by rw [he]; exact h1, by rw [hdt]; exact h2, by rw [htx]; exact h3,
    fun e hm => by rw [hf]; exact h4 e (by rw [← he]; exact hm)⟩

/-- `insertAt` は挿入先以外の Document の制約を変えない。 -/
theorem documentChildrenOk_insertAt_ne {t t' : Tree} {parent node : NodeId}
    {child : Option NodeId} (hwf : WellFormed t) (hi : insertAt t parent node child = .ok t')
    {doc : NodeId} (hne : doc ≠ parent) (h : DocumentChildrenOk t doc) :
    DocumentChildrenOk t' doc :=
  documentChildrenOk_congr (kindPreserving_insertAt hi) (insertAt_childrenOf_ne hwf hi hne) h

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
  have hkp : KindPreserving s.tree s₁.tree := kindPreserving_remove hr
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
  exact structurallyValid_insertAt (structurallyValid_remove h hr)
    (kindFact_of_kindPreserving hkp (P := fun k => k.canHaveChildren = true) hpk)
    (kindFact_of_kindPreserving hkp (P := fun k => k ≠ NodeKind.document) hnotdoc)
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
  have hkind : ∀ m, kindOf s₁.tree m = kindOf s.tree m := kindPreserving_detach hd
  have h₁ : DocumentTreesValid s₁.tree := documentTreesValid_remove hwf h hr
  refine ⟨fun doc dd hdoc hkdoc => ?_⟩
  obtain ⟨dd₁, hdoc₁, hkdd⟩ := kindPreserving_get? (kindPreserving_insertAt hi) hdoc
  have hk₁ : dd₁.kind = NodeKind.document := by rw [hkdd]; exact hkdoc
  have hok₁ : DocumentChildrenOk s₁.tree doc := h₁.documentChildren doc dd₁ hdoc₁ hk₁
  by_cases hne : doc = newParent
  · subst hne
    -- `doc` が挿入先。step 5 / 6 の事実を `s₁` 側に移して使う。
    have hpdoc : pd.kind = NodeKind.document := by
      have hkp := hkind doc
      rw [kindOf, kindOf, hdoc₁, hpd] at hkp
      simp only [Option.map_some, Option.some.injEq] at hkp
      rw [← hkp]; exact hk₁
    have hnode : kindOf s₁.tree node = some nd.kind := by
      rw [hkind node, kindOf, hnd]; rfl
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

/-! ## adopt -/

theorem structurallyValid_adopt {s s' : DOMState} {node doc : NodeId}
    (h : StructurallyValid s.tree) (hdoc : IsDocument s.tree doc)
    (ha : adopt s node doc = .ok s') : StructurallyValid s'.tree := by
  obtain ⟨s₁, hstep, hfinal⟩ := adopt_ok_cases ha
  have hstep' : StructurallyValid s₁.tree ∧ KindPreserving s.tree s₁.tree := by
    rcases hstep with ⟨_, rfl⟩ | hr
    · exact ⟨h, KindPreserving.refl _⟩
    · exact ⟨structurallyValid_remove h hr, kindPreserving_remove hr⟩
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
      KindPreserving s.tree s₁.tree ∧ parentOf s₁.tree node = none := by
    rcases hstep with ⟨hnp, rfl⟩ | hr
    · exact ⟨h, hs, KindPreserving.refl _, hnp⟩
    · exact ⟨nodeDocumentsValid_remove hs.wellFormed h hr, structurallyValid_remove hs hr,
        kindPreserving_remove hr, remove_parentOf hr⟩
  rcases hfinal with rfl | rfl
  · exact hstep'.1
  · refine nodeDocumentsValid_setOwnerDocument hstep'.2.1.wellFormed hstep'.2.1 hstep'.1
      hstep'.2.2.2 ?_
    exact kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.document) hstep'.2.2.1 hnk

/-! ## adopt / removeEach / replaceData の document tree 保存 -/

theorem documentTreesValid_setOwnerDocument {t : Tree} (n doc : NodeId)
    (h : DocumentTreesValid t) : DocumentTreesValid (setOwnerDocument t n doc) :=
  documentTreesValid_of_sameShape (kindPreserving_setOwnerDocument t n doc)
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
  unfold adopt at ha
  split at ha
  · simp at ha
  · next old hold =>
    split at ha
    · simp at ha
    · next s₁ hr =>
      have hown₁ : ownerDocumentOf s₁.tree node = some old := by
        revert hr
        split
        · intro hr; rw [← Except.ok.inj hr]; exact hold
        · intro hr
          rw [ownerDocumentOf_detach (remove_ok hr).2]; exact hold
      have hwf₁ : WellFormed s₁.tree := by
        revert hr
        split
        · intro hr; rw [← Except.ok.inj hr]; exact hwf
        · intro hr; exact remove_preserves_wellformed hwf hr
      obtain ⟨nd₁, hnd₁⟩ : ∃ nd₁, s₁.tree.get? node = some nd₁ := by
        cases h1 : s₁.tree.get? node with
        | some x => exact ⟨x, rfl⟩
        | none => rw [ownerDocumentOf, h1] at hown₁; simp at hown₁
      split at ha
      · next he => rw [← Except.ok.inj ha, hown₁, he]
      · rw [← Except.ok.inj ha]
        show ownerDocumentOf (setOwnerDocument s₁.tree node doc) node = some doc
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
    | none => rw [ownerDocumentOf, h1] at hp₁; simp at hp₁
    | some pd =>
      simp only [Option.map_some]
      split
      · rfl
      · rw [ownerDocumentOf, h1] at hp₁; simpa using hp₁

/-! ## insertEach -/

/--
`insertEach` は node ごとに adopt してから `insertAt` する。

必要な前提は次の三つで、いずれも §4.2.3 の validity 検査か invariant から出る。

* parent は children を持てる kind である（step 1）。
* 入れる node はどれも Document でない（step 4、fragment の場合は
  「Document は parent を持たない」という invariant から）。
* `doc` は Document である（parent の node document なので `WellFormed` から）。
-/
theorem structurallyValid_insertEach :
    ∀ (ns : List NodeId) {s s' : DOMState} {parent : NodeId} {child : Option NodeId}
      {doc : NodeId},
      StructurallyValid s.tree →
      (∀ pd, s.tree.get? parent = some pd → pd.kind.canHaveChildren = true) →
      (∀ n ∈ ns, ∀ nd, s.tree.get? n = some nd → nd.kind ≠ .document) →
      (∀ n ∈ ns, ∀ nd, s.tree.get? n = some nd → nd.kind = .documentType →
        ∀ pd, s.tree.get? parent = some pd → pd.kind = .document) →
      IsDocument s.tree doc →
      insertEach s parent child doc ns = .ok s' → StructurallyValid s'.tree
  | [], s, s', parent, child, doc, h, _, _, _, _, hi => by
    rw [insertEach] at hi; rw [← Except.ok.inj hi]; exact h
  | n :: ns, s, s', parent, child, doc, h, hpk, hnk, hdt, hdoc, hi => by
    rw [insertEach] at hi
    split at hi
    · simp at hi
    · next s₁ ha =>
      split at hi
      · simp at hi
      · next s₂ hins =>
        have hkp₁ : KindPreserving s.tree s₁.tree := kindPreserving_adopt ha
        have h₁ : StructurallyValid s₁.tree := structurallyValid_adopt h hdoc ha
        have h₂ : StructurallyValid s₂.tree := by
          refine structurallyValid_insertAt h₁ ?_ ?_ ?_ (DOMState.mapTree_eq_ok hins).1
          · exact kindFact_of_kindPreserving (P := fun k => k.canHaveChildren = true) hkp₁ hpk
          · exact kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.document) hkp₁
              (hnk n (List.mem_cons_self ..))
          · exact doctypeFact_of_kindPreserving hkp₁ (hdt n (List.mem_cons_self ..))
        have hkp₂ : KindPreserving s₁.tree s₂.tree :=
          kindPreserving_insertAt (DOMState.mapTree_eq_ok hins).1
        have hkp : KindPreserving s.tree s₂.tree := hkp₁.trans hkp₂
        refine structurallyValid_insertEach ns h₂ ?_ ?_ ?_ ?_ hi
        · exact kindFact_of_kindPreserving (P := fun k => k.canHaveChildren = true) hkp hpk
        · intro m hm
          exact kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.document) hkp
            (hnk m (List.mem_cons_of_mem _ hm))
        · intro m hm
          exact doctypeFact_of_kindPreserving hkp (hdt m (List.mem_cons_of_mem _ hm))
        · exact hdoc.map hkp

/--
`insertEach` の node document 保存。

ループ不変条件は「parent の node document が `doc` である」ことだけでよい。
adopt はこれを壊さない（parent が部分木の外なら不変、中なら `doc` に揃う）。
各 node は adopt の後 node document が `doc` になるので、
`insertAt` が要求する「辺の両端が同じ node document」が満たされる。
-/
theorem nodeDocumentsValid_insertEach :
    ∀ (ns : List NodeId) {s s' : DOMState} {parent : NodeId} {child : Option NodeId}
      {doc : NodeId},
      StructurallyValid s.tree → NodeDocumentsValid s.tree →
      IsDocument s.tree doc →
      (∀ pd, s.tree.get? parent = some pd → pd.kind.canHaveChildren = true) →
      ownerDocumentOf s.tree parent = some doc →
      (∀ n ∈ ns, ∀ nd, s.tree.get? n = some nd → nd.kind ≠ .document) →
      (∀ n ∈ ns, ∀ nd, s.tree.get? n = some nd → nd.kind = .documentType →
        ∀ pd, s.tree.get? parent = some pd → pd.kind = .document) →
      insertEach s parent child doc ns = .ok s' → NodeDocumentsValid s'.tree
  | [], s, s', parent, child, doc, _, h, _, _, _, _, _, hi => by
    rw [insertEach] at hi; rw [← Except.ok.inj hi]; exact h
  | n :: ns, s, s', parent, child, doc, hs, h, hdoc, hpk, hpar, hnk, hdt, hi => by
    rw [insertEach] at hi
    split at hi
    · simp at hi
    · next s₁ ha =>
      split at hi
      · simp at hi
      · next s₂ hins =>
        have hkp₁ : KindPreserving s.tree s₁.tree := kindPreserving_adopt ha
        have hnkn := hnk n (List.mem_cons_self ..)
        have hs₁ : StructurallyValid s₁.tree := structurallyValid_adopt hs hdoc ha
        have h₁ : NodeDocumentsValid s₁.tree := nodeDocumentsValid_adopt hs h hdoc hnkn ha
        have hpar₁ : ownerDocumentOf s₁.tree parent = some doc :=
          adopt_ownerDocument_other ha hpar
        -- node が木の中にあることは adopt の成功から出る。
        obtain ⟨nd, hnd⟩ : ∃ nd, s.tree.get? n = some nd := by
          unfold adopt at ha
          split at ha
          · simp at ha
          · next old hold =>
            cases h1 : s.tree.get? n with
            | some x => exact ⟨x, rfl⟩
            | none => rw [ownerDocumentOf, h1] at hold; simp at hold
        have hself : ownerDocumentOf s₁.tree n = some doc :=
          adopt_ownerDocument_self hs.wellFormed ha
        have hi' := (DOMState.mapTree_eq_ok hins).1
        have h₂ : NodeDocumentsValid s₂.tree :=
          nodeDocumentsValid_insertAt h₁ (by rw [hself, hpar₁]) hi'
        have hpk₁ : ∀ pd, s₁.tree.get? parent = some pd → pd.kind.canHaveChildren = true :=
          kindFact_of_kindPreserving (P := fun k => k.canHaveChildren = true) hkp₁ hpk
        have hs₂ : StructurallyValid s₂.tree :=
          structurallyValid_insertAt hs₁ hpk₁
            (kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.document) hkp₁ hnkn)
            (doctypeFact_of_kindPreserving hkp₁ (hdt n (List.mem_cons_self ..))) hi'
        have hkp₂ : KindPreserving s₁.tree s₂.tree := kindPreserving_insertAt hi'
        refine nodeDocumentsValid_insertEach ns hs₂ h₂ (hdoc.map (hkp₁.trans hkp₂)) ?_ ?_ ?_ ?_ hi
        · exact kindFact_of_kindPreserving (P := fun k => k.canHaveChildren = true) hkp₂ hpk₁
        · rw [ownerDocumentOf_insertAt hi']; exact hpar₁
        · intro m hm
          exact kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.document)
            (hkp₁.trans hkp₂) (hnk m (List.mem_cons_of_mem _ hm))
        · intro m hm
          exact doctypeFact_of_kindPreserving (hkp₁.trans hkp₂)
            (hdt m (List.mem_cons_of_mem _ hm))

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
    (hdt : ∀ n ∈ nodes, ∀ nd, s.tree.get? n = some nd → nd.kind = .documentType →
      ∀ pd, s.tree.get? parent = some pd → pd.kind = .document)
    (hi : insertNodesAt s parent child nodes b = .ok s') : StructurallyValid s'.tree := by
  unfold insertNodesAt at hi
  simp only at hi
  split at hi
  · simp at hi
  · next sx hx =>
    have htree : s'.tree = sx.tree := by
      split at hi
      · rw [← Except.ok.inj hi]
      · rw [← Except.ok.inj hi]; simp
    rw [htree]
    unfold insertEachAt at hx
    split at hx
    · simp at hx
    · next pd hpd =>
      have hpd' : s.tree.get? parent = some pd := by simpa using hpd
      refine structurallyValid_insertEach nodes (by simpa using h) (by simpa using hpk)
        (by simpa using hnk) (by simpa using hdt) ?_ hx
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
  unfold insert at hi
  split at hi
  · simp at hi
  · next nd hnd =>
    split at hi
    · -- fragment を展開する
      split at hi
      · rw [← Except.ok.inj hi]; exact h
      · split at hi
        · simp at hi
        · next s₁ hre =>
          have h₁ : StructurallyValid s₁.tree := structurallyValid_removeEach _ h hre
          have hkp : KindPreserving s.tree s₁.tree := kindPreserving_removeEach _ hre
          have hfragkind : nd.kind ≠ NodeKind.document := by
            rename_i hfrag _ _
            intro hc; rw [hc] at hfrag; simp at hfrag
          refine structurallyValid_insertNodesAt (s := queueTreeMutationRecord s₁ node []
            nd.children none none) (by simpa using h₁) ?_ ?_ ?_ hi
          · simpa using
              kindFact_of_kindPreserving (P := fun k => k.canHaveChildren = true) hkp hpk
          · intro m hm
            simpa using kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.document) hkp
              (child_not_document h hnd hm)
          · intro m hm md hmd hkm _ _
            refine absurd hkm ?_
            have := kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.documentType) hkp
              (child_not_doctype h hnd hfragkind hm)
            exact this md (by simpa using hmd)
    · -- 単独の node
      refine structurallyValid_insertNodesAt h hpk ?_ ?_ hi
      · intro m hm
        rcases List.mem_singleton.mp hm with rfl
        exact hnk
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
    (hdt : ∀ n ∈ nodes, ∀ nd, s.tree.get? n = some nd → nd.kind = .documentType →
      ∀ pd, s.tree.get? parent = some pd → pd.kind = .document)
    (hi : insertNodesAt s parent child nodes b = .ok s') : NodeDocumentsValid s'.tree := by
  unfold insertNodesAt at hi
  simp only at hi
  split at hi
  · simp at hi
  · next sx hx =>
    have htree : s'.tree = sx.tree := by
      split at hi
      · rw [← Except.ok.inj hi]
      · rw [← Except.ok.inj hi]; simp
    rw [htree]
    unfold insertEachAt at hx
    split at hx
    · simp at hx
    · next pd hpd =>
      have hpd' : s.tree.get? parent = some pd := by simpa using hpd
      refine nodeDocumentsValid_insertEach nodes (by simpa using hs) (by simpa using h)
        ?_ (by simpa using hpk) ?_ (by simpa using hnk) (by simpa using hdt) hx
      · exact ⟨_, by simpa using (isDocument_ownerDocument hs.wellFormed hpd').choose_spec.1,
          (isDocument_ownerDocument hs.wellFormed hpd').choose_spec.2⟩
      · simp only [liveRangeInsertAdjust_tree]
        simp [ownerDocumentOf, hpd']

/-- PLAN §6.3 の形。`insert` は node document の整合性を保つ。 -/
theorem nodeDocumentsValid_insert_of_facts {s s' : DOMState} {node parent : NodeId}
    {child : Option NodeId} {b : Bool}
    (hs : StructurallyValid s.tree) (h : NodeDocumentsValid s.tree)
    (hpk : ∀ pd, s.tree.get? parent = some pd → pd.kind.canHaveChildren = true)
    (hnk : ∀ nd, s.tree.get? node = some nd → nd.kind ≠ NodeKind.document)
    (hdtf : ∀ nd, s.tree.get? node = some nd → nd.kind = NodeKind.documentType →
      ∀ pd, s.tree.get? parent = some pd → pd.kind = NodeKind.document)
    (hi : insert s node parent child b = .ok s') : NodeDocumentsValid s'.tree := by
  unfold insert at hi
  split at hi
  · simp at hi
  · next nd hnd =>
    split at hi
    · split at hi
      · rw [← Except.ok.inj hi]; exact h
      · split at hi
        · simp at hi
        · next s₁ hre =>
          have hs₁ : StructurallyValid s₁.tree := structurallyValid_removeEach _ hs hre
          have h₁ : NodeDocumentsValid s₁.tree := nodeDocumentsValid_removeEach _ hs h hre
          have hkp : KindPreserving s.tree s₁.tree := kindPreserving_removeEach _ hre
          have hfragkind : nd.kind ≠ NodeKind.document := by
            rename_i hfrag _ _
            intro hc; rw [hc] at hfrag; simp at hfrag
          refine nodeDocumentsValid_insertNodesAt (s := queueTreeMutationRecord s₁ node []
            nd.children none none) (by simpa using hs₁) (by simpa using h₁) ?_ ?_ ?_ hi
          · simpa using
              kindFact_of_kindPreserving (P := fun k => k.canHaveChildren = true) hkp hpk
          · intro m hm
            simpa using kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.document) hkp
              (child_not_document hs hnd hm)
          · intro m hm md hmd hkm _ _
            refine absurd hkm ?_
            have := kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.documentType) hkp
              (child_not_doctype hs hnd hfragkind hm)
            exact this md (by simpa using hmd)
    · refine nodeDocumentsValid_insertNodesAt hs h hpk ?_ ?_ hi
      · intro m hm
        rcases List.mem_singleton.mp hm with rfl
        exact hnk
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

/-! ## insert が Document の children 制約を保つこと -/

/-- 除外リストに全部入っているなら、その list は空である。 -/
theorem eq_nil_of_forall_mem_nil {α : Type _} {l : List α} (h : ∀ e ∈ l, e ∈ ([] : List α)) :
    l = [] := by
  cases hl : l with
  | nil => rfl
  | cons y r => exact absurd (h y (by rw [hl]; simp)) (by simp)

/-- step 9 / 8 の element 挿入検査が通ったときに得られる事実。 -/
theorem checkElementInsertion_ok {t : Tree} {parent : NodeId} {child : Option NodeId}
    {excl : List NodeId} (h : checkElementInsertion t parent child excl = .ok ()) :
    (∀ e ∈ elementChildren t parent, e ∈ excl) ∧
      ∀ c, child = some c →
        ((kindOf t c == some NodeKind.documentType) = false ∨ c ∈ excl) ∧
          doctypeFollows t parent c = false := by
  unfold checkElementInsertion at h
  split at h
  · simp at h
  · next hany =>
    have hall : ∀ e ∈ elementChildren t parent, e ∈ excl := by
      simp only [List.any_eq_true, Bool.not_eq_true', not_exists, not_and] at hany
      intro e he
      have hb := hany e he
      simpa using hb
    refine ⟨hall, ?_⟩
    intro c hc
    subst hc
    simp only at h
    split at h
    · simp at h
    · next hfol =>
      split at h
      · simp at h
      · next hk =>
        refine ⟨?_, by simpa using hfol⟩
        by_cases hcm : c ∈ excl
        · exact Or.inr hcm
        · refine Or.inl ?_
          have hcont : excl.contains c = false := by simpa using hcm
          rw [Bool.not_eq_true, Bool.and_eq_false_iff, hcont] at hk
          simpa using hk

/-- step 10-11 の doctype 挿入検査が通ったときに得られる事実。 -/
theorem checkDoctypeInsertion_ok {t : Tree} {parent : NodeId} {child : Option NodeId}
    {excl : List NodeId} (h : checkDoctypeInsertion t parent child excl = .ok ()) :
    (∀ e ∈ doctypeChildren t parent, e ∈ excl) ∧
      (∀ c, child = some c → elementPrecedes t parent c = false) ∧
      (child = none → ∀ e ∈ elementChildren t parent, e ∈ excl) := by
  unfold checkDoctypeInsertion at h
  split at h
  · simp at h
  · next hany =>
    have hall : ∀ e ∈ doctypeChildren t parent, e ∈ excl := by
      simp only [List.any_eq_true, Bool.not_eq_true', not_exists, not_and] at hany
      intro e he
      simpa using hany e he
    refine ⟨hall, ?_, ?_⟩
    · intro c hc
      subst hc
      simp only at h
      split at h
      · simp at h
      · next hp => simpa using hp
    · intro hc
      subst hc
      simp only at h
      split at h
      · simp at h
      · next hany' =>
        simp only [List.any_eq_true, Bool.not_eq_true', not_exists, not_and] at hany'
        intro e he
        simpa using hany' e he

/--
parent が Document のとき、`ensure pre-insertion validity` が確立する事実。

step 6（Text は入れられない）、step 8（fragment の中身）、
step 9（element を入れる条件）、step 10-11（doctype を入れる条件）に対応する。
-/
theorem ensurePreInsertionValidity_documentFacts {t : Tree} {node parent : NodeId}
    {child : Option NodeId} {excl : List NodeId} {pd nd : NodeData}
    (hpd : t.get? parent = some pd) (hnd : t.get? node = some nd)
    (hdoc : pd.kind = NodeKind.document)
    (hv : ensurePreInsertionValidity t node parent child excl = .ok ()) :
    nd.kind.isText = false ∧
    (nd.kind = NodeKind.documentFragment →
      (elementChildren t node).length ≤ 1 ∧ textChildren t node = []) ∧
    ((nd.kind = NodeKind.element ∨
        (nd.kind = NodeKind.documentFragment ∧ elementChildren t node ≠ [])) →
      (∀ e ∈ elementChildren t parent, e ∈ excl) ∧
        ∀ c, child = some c →
          ((kindOf t c == some NodeKind.documentType) = false ∨ c ∈ excl) ∧
            doctypeFollows t parent c = false) ∧
    (nd.kind = NodeKind.documentType →
      (∀ e ∈ doctypeChildren t parent, e ∈ excl) ∧
        (∀ c, child = some c → elementPrecedes t parent c = false) ∧
        (child = none → ∀ e ∈ elementChildren t parent, e ∈ excl)) := by
  unfold ensurePreInsertionValidity at hv
  rw [hpd, hnd] at hv
  simp only at hv
  split at hv
  · simp at hv
  · split at hv
    · simp at hv
    · split at hv
      · simp at hv
      · split at hv
        · simp at hv
        · split at hv
          · next hne => exact absurd hdoc hne
          · split at hv
            · simp at hv
            · next hisText =>
              have htext : nd.kind.isText = false := by simpa using hisText
              refine ⟨htext, ?_, ?_, ?_⟩ <;> split at hv
              -- step 7：CharacterData ならここで終わり
              · next hcd =>
                intro hfrag
                rw [hfrag] at hcd
                simp [NodeKind.isCharacterData] at hcd
              · next hcd =>
                split at hv
                · next hfrag =>
                  split at hv
                  · simp at hv
                  · next hsizes =>
                    intro _
                    rw [Bool.not_eq_true, Bool.or_eq_false_iff] at hsizes
                    obtain ⟨hlen, hemp⟩ := hsizes
                    refine ⟨by simp at hlen; omega, ?_⟩
                    rw [Bool.not_eq_false', List.isEmpty_iff] at hemp
                    exact hemp
                · next hnfrag =>
                  intro hfrag
                  rw [hfrag] at hnfrag
                  simp at hnfrag
              · next hcd =>
                intro hcase
                exfalso
                rcases hcase with hk | ⟨hk, _⟩
                · rw [hk] at hcd; simp [NodeKind.isCharacterData] at hcd
                · rw [hk] at hcd; simp [NodeKind.isCharacterData] at hcd
              · next hcd =>
                split at hv
                · next hfrag =>
                  split at hv
                  · simp at hv
                  · split at hv
                    · next hempty =>
                      intro hcase
                      rcases hcase with hk | ⟨_, hne⟩
                      · rw [hk] at hfrag; simp at hfrag
                      · exact absurd (by simpa using hempty) hne
                    · intro _
                      exact checkElementInsertion_ok hv
                · next hnfrag =>
                  split at hv
                  · intro _
                    exact checkElementInsertion_ok hv
                  · next hnelem =>
                    intro hcase
                    exfalso
                    rcases hcase with hk | ⟨hk, _⟩
                    · rw [hk] at hnelem; simp at hnelem
                    · rw [hk] at hnfrag; simp at hnfrag
              · next hcd =>
                intro hdt
                exfalso
                rw [hdt] at hcd
                simp [NodeKind.isCharacterData] at hcd
              · next hcd =>
                split at hv
                · next hfrag =>
                  intro hdt
                  rw [hdt] at hfrag
                  simp at hfrag
                · split at hv
                  · next helem =>
                    intro hdt
                    rw [hdt] at helem
                    simp at helem
                  · intro _
                    exact checkDoctypeInsertion_ok hv

/-- `adopt` は children から adopt する node 自身を取り除くだけである。 -/
theorem adopt_childrenOf {s s' : DOMState} {node doc : NodeId}
    (hwf : WellFormed s.tree) (ha : adopt s node doc = .ok s') (p : NodeId) :
    childrenOf s'.tree p = ListUtil.removeAll (childrenOf s.tree p) node := by
  obtain ⟨s₁, hstep, hfinal⟩ := adopt_ok_cases ha
  have h₁ : childrenOf s₁.tree p = ListUtil.removeAll (childrenOf s.tree p) node := by
    rcases hstep with ⟨hn, rfl⟩ | hr
    · rw [ListUtil.removeAll_eq_self]
      intro hmem
      have hpar := parentOf_of_mem_childrenOf hwf hmem
      rw [hn] at hpar
      simp at hpar
    · exact detach_childrenOf_removeAll hwf (remove_ok hr).2 p
  rcases hfinal with rfl | rfl
  · exact h₁
  · rw [DOMState.withTree_tree, childrenOf_setOwnerDocument]
    exact h₁

/--
Document `parent` の `child` の直前に `ns` を順に入れても
Document の children 制約が保たれるための十分条件。

§4.2.3 "ensure pre-insertion validity" の step 6 / 8 / 9 / 10-11 が確立する事実に対応する。
`insert` が一回の呼び出しで入れる node は、element か doctype のどちらかを高々一つしか含まない。
（fragment の children に doctype は無く、fragment でなければ node は一つだからである。）

`parent` が Document でなければ何も要求しない。
-/
def InsertSeqOk (t : Tree) (parent : NodeId) (child : Option NodeId)
    (ns : List NodeId) : Prop :=
  kindOf t parent = some NodeKind.document →
    -- Text は Document の子になれない
    (∀ n ∈ ns, ∀ k, kindOf t n = some k → k.isText = false) ∧
    -- 一度に入れる element と doctype は合わせて高々一つ
    ((ns.filter fun n => kindOf t n == some NodeKind.element).length +
      (ns.filter fun n => kindOf t n == some NodeKind.documentType).length ≤ 1) ∧
    -- element の子は高々一つ
    ((elementChildren t parent).length +
      (ns.filter fun n => kindOf t n == some NodeKind.element).length ≤ 1) ∧
    -- doctype の子は高々一つ
    ((doctypeChildren t parent).length +
      (ns.filter fun n => kindOf t n == some NodeKind.documentType).length ≤ 1) ∧
    -- element を入れるなら、挿入点より後ろに doctype は無い
    (∀ n ∈ ns, kindOf t n = some NodeKind.element → ∀ c, child = some c →
      (kindOf t c == some NodeKind.documentType) = false ∧
        doctypeFollows t parent c = false) ∧
    -- doctype を入れるなら、挿入点より前に element は無い
    (∀ n ∈ ns, kindOf t n = some NodeKind.documentType →
      (∀ c, child = some c → elementPrecedes t parent c = false) ∧
      (child = none → elementChildren t parent = []))

/-- children から取り除くだけなら、「前に element がある」が新たに成り立つことはない。 -/
theorem elementPrecedes_of_removeAll {t t' : Tree} {p c a : NodeId}
    (hkind : ∀ m, kindOf t' m = kindOf t m)
    (hch : childrenOf t' p = ListUtil.removeAll (childrenOf t p) a)
    (h : elementPrecedes t p c = false) : elementPrecedes t' p c = false := by
  unfold elementPrecedes at h ⊢
  simp only [hch, hkind]
  by_cases hca : c = a
  · subst hca
    rw [ListUtil.splitAt?_eq_none_of_not_mem (ListUtil.not_mem_removeAll _ _)]
  · cases hs : ListUtil.splitAt? (childrenOf t p) c with
    | none => rw [ListUtil.splitAt?_removeAll_none hs]
    | some q =>
      obtain ⟨u, v⟩ := q
      rw [hs] at h
      rw [ListUtil.splitAt?_removeAll hca hs]
      rw [Bool.eq_false_iff] at h ⊢
      intro hcon
      obtain ⟨x, hx, hxk⟩ := List.any_eq_true.mp hcon
      exact h (List.any_eq_true.mpr ⟨x, ((ListUtil.mem_removeAll _ _ _).mp hx).2, hxk⟩)

/-- children が減るだけの操作は `InsertSeqOk` を壊さない。 -/
theorem insertSeqOk_of_removeAll {t t' : Tree} {parent : NodeId} {child : Option NodeId}
    {ns : List NodeId} {a : NodeId} (hkind : ∀ m, kindOf t' m = kindOf t m)
    (hch : ∀ p, childrenOf t' p = ListUtil.removeAll (childrenOf t p) a)
    (h : InsertSeqOk t parent child ns) : InsertSeqOk t' parent child ns := by
  intro hdoc
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h (by rw [← hkind]; exact hdoc)
  have helem : (elementChildren t' parent).length ≤ (elementChildren t parent).length := by
    unfold elementChildren
    simp only [hch, hkind]
    exact ListUtil.length_filter_removeAll a _ _
  have hdt : (doctypeChildren t' parent).length ≤ (doctypeChildren t parent).length := by
    unfold doctypeChildren
    simp only [hch, hkind]
    exact ListUtil.length_filter_removeAll a _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn k hk; exact h1 n hn k (by rw [← hkind]; exact hk)
  · simpa only [hkind] using h2
  · simp only [hkind]
    exact Nat.le_trans (Nat.add_le_add_right helem _) h3
  · simp only [hkind]
    exact Nat.le_trans (Nat.add_le_add_right hdt _) h4
  · intro n hn hk c hc
    obtain ⟨hc1, hc2⟩ := h5 n hn (by rw [← hkind]; exact hk) c hc
    exact ⟨by rw [hkind]; exact hc1, doctypeFollows_of_removeAll hkind (hch parent) hc2⟩
  · intro n hn hk
    obtain ⟨hp1, hp2⟩ := h6 n hn (by rw [← hkind]; exact hk)
    refine ⟨fun c hc => elementPrecedes_of_removeAll hkind (hch parent) (hp1 c hc), fun hc => ?_⟩
    have hnil := hp2 hc
    unfold elementChildren at hnil ⊢
    simp only [hch, hkind]
    exact ListUtil.filter_removeAll_eq_nil hnil

/-- 先頭を入れた後、残りについて `InsertSeqOk` は保たれる。 -/
theorem insertSeqOk_insertAt {t t' : Tree} {parent n : NodeId} {child : Option NodeId}
    {ns : List NodeId} (hwf : WellFormed t) (hi : insertAt t parent n child = .ok t')
    (h : InsertSeqOk t parent child (n :: ns)) : InsertSeqOk t' parent child ns := by
  have hkind : ∀ m, kindOf t' m = kindOf t m := kindPreserving_insertAt hi
  intro hdoc
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h (by rw [← hkind]; exact hdoc)
  have hmemtail : ∀ m, m ∈ ns → m ∈ n :: ns := fun m hm => List.mem_cons_of_mem _ hm
  have hcons : ∀ (p : NodeId → Bool),
      ((n :: ns).filter p).length = (if p n then 1 else 0) + (ns.filter p).length := by
    intro p
    by_cases hp : p n
    · simp [List.filter, hp, Nat.add_comm]
    · simp [List.filter, hp]
  have hlenE : (elementChildren t' parent).length =
      (elementChildren t parent).length +
        (if (kindOf t n == some NodeKind.element) = true then 1 else 0) := by
    unfold elementChildren
    simp only [insertAt_childrenOf hwf hi, hkind, ListUtil.length_filter_insertBefore]
  have hlenD : (doctypeChildren t' parent).length =
      (doctypeChildren t parent).length +
        (if (kindOf t n == some NodeKind.documentType) = true then 1 else 0) := by
    unfold doctypeChildren
    simp only [insertAt_childrenOf hwf hi, hkind, ListUtil.length_filter_insertBefore]
  have hcE := hcons (fun m => kindOf t m == some NodeKind.element)
  have hcD := hcons (fun m => kindOf t m == some NodeKind.documentType)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm k hk; exact h1 m (hmemtail m hm) k (by rw [← hkind]; exact hk)
  · simp only [hkind]
    simp only [hcE, hcD] at h2
    omega
  · simp only [hkind, hlenE]
    simp only [hcE] at h3
    omega
  · simp only [hkind, hlenD]
    simp only [hcD] at h4
    omega
  · intro m hm hk c hc
    obtain ⟨hc1, hc2⟩ := h5 m (hmemtail m hm) (by rw [← hkind]; exact hk) c hc
    subst hc
    obtain ⟨s₁, s₂, hs₁, hs₂⟩ := insertAt_children_split hwf hi
    have hne : c ≠ n := fun hx =>
      insertAt_node_not_mem hwf hi
        (hx ▸ (by rw [hs₁]; exact List.mem_append_right _ (by simp)))
    have hcnot : c ∉ s₁ := by
      have hnd : (childrenOf t parent).Nodup := childrenOf_nodup hwf parent
      rw [hs₁] at hnd
      exact fun hm' => (List.nodup_append.mp hnd).2.2 c hm' c (by simp) rfl
    refine ⟨by rw [hkind]; exact hc1, ?_⟩
    rw [doctypeFollows_split_of_mem_right hkind (A := s₁) (B := c :: s₂) hs₁ hs₂
      hcnot hne (by simp)]
    exact hc2
  · intro m hm hk
    have hkm : kindOf t m = some NodeKind.documentType := by rw [← hkind]; exact hk
    -- `m` が doctype なので、先頭 `n` は element ではない
    have hnE : (kindOf t n == some NodeKind.element) = false := by
      have hmem : m ∈ ns.filter fun x => kindOf t x == some NodeKind.documentType :=
        List.mem_filter.mpr ⟨hm, by rw [hkm]; simp⟩
      have hmD : 1 ≤ (ns.filter fun x => kindOf t x == some NodeKind.documentType).length := by
        cases hl : ns.filter fun x => kindOf t x == some NodeKind.documentType with
        | nil => rw [hl] at hmem; simp at hmem
        | cons y l => simp
      cases hcon : (kindOf t n == some NodeKind.element) with
      | false => rfl
      | true =>
        exfalso
        have hcnt : ((n :: ns).filter fun x => kindOf t x == some NodeKind.element).length
            = 1 + (ns.filter fun x => kindOf t x == some NodeKind.element).length := by
          simp [List.filter, hcon, Nat.add_comm]
        have hcnt2 : (ns.filter fun x => kindOf t x == some NodeKind.documentType).length
            ≤ ((n :: ns).filter fun x => kindOf t x == some NodeKind.documentType).length := by
          rw [hcD]; omega
        omega
    obtain ⟨hp1, hp2⟩ := h6 m (hmemtail m hm) hkm
    refine ⟨fun c hc => ?_, fun hc => ?_⟩
    · subst hc
      obtain ⟨s₁, s₂, hs₁, hs₂⟩ := insertAt_children_split hwf hi
      have hne : c ≠ n := fun hx =>
        insertAt_node_not_mem hwf hi
          (hx ▸ (by rw [hs₁]; exact List.mem_append_right _ (by simp)))
      have hcnot : c ∉ s₁ ++ [n] := by
        have hnd : (childrenOf t parent).Nodup := childrenOf_nodup hwf parent
        rw [hs₁] at hnd
        intro hmm
        rcases List.mem_append.mp hmm with hx | hx
        · exact (List.nodup_append.mp hnd).2.2 c hx c (by simp) rfl
        · exact hne (by simpa using hx)
      have hsplit : ListUtil.splitAt? (childrenOf t parent) c = some (s₁, s₂) :=
        splitAt?_childrenOf_of_split hwf hs₁
      have hsplit' : ListUtil.splitAt? (childrenOf t' parent) c = some (s₁ ++ [n], s₂) := by
        rw [hs₂]
        have hrw : s₁ ++ n :: c :: s₂ = (s₁ ++ [n]) ++ c :: s₂ := by simp
        rw [hrw]
        exact ListUtil.splitAt?_append_cons_self hcnot s₂
      have hp := hp1 c rfl
      unfold elementPrecedes at hp ⊢
      simp only [hsplit] at hp
      simp only [hsplit', hkind, List.any_append, List.any_cons, List.any_nil, Bool.or_false]
      simp [hp, hnE]
    · have hnil := hp2 hc
      unfold elementChildren at hnil ⊢
      simp only [insertAt_childrenOf hwf hi, hkind]
      rw [ListUtil.filter_insertBefore_of_neg
        (p := fun x => kindOf t x == some NodeKind.element) (a := n) hnE]
      exact hnil

/-- `insertEach` は Document の children 制約を保つ。 -/
theorem documentTreesValid_insertEach :
    ∀ (ns : List NodeId) {s s' : DOMState} {parent : NodeId} {child : Option NodeId}
      {doc : NodeId},
      WellFormed s.tree → DocumentTreesValid s.tree → IsDocument s.tree doc →
      InsertSeqOk s.tree parent child ns →
      insertEach s parent child doc ns = .ok s' → DocumentTreesValid s'.tree
  | [], _, _, _, _, _, _, h, _, _, hi => by rw [insertEach] at hi; rw [← Except.ok.inj hi]; exact h
  | n :: ns, s, s', parent, child, doc, hwf, h, hdoc, hok, hi => by
    rw [insertEach] at hi
    split at hi
    · simp at hi
    · next s₁ ha =>
      split at hi
      · simp at hi
      · next s₂ hins =>
        have hins' := (DOMState.mapTree_eq_ok hins).1
        have hwf₁ : WellFormed s₁.tree := adopt_preserves_wellformed hwf hdoc ha
        have h₁ : DocumentTreesValid s₁.tree := documentTreesValid_adopt hwf h ha
        have hok₁ : InsertSeqOk s₁.tree parent child (n :: ns) :=
          insertSeqOk_of_removeAll (kindPreserving_adopt ha) (adopt_childrenOf hwf ha) hok
        have hwf₂ : WellFormed s₂.tree := insertAt_preserves_wellformed hwf₁ hins'
        have h₂ : DocumentTreesValid s₂.tree := by
          refine ⟨fun d dd hd hk => ?_⟩
          obtain ⟨dd₁, hd₁, hkdd⟩ := kindPreserving_get? (kindPreserving_insertAt hins') hd
          have hk₁ : dd₁.kind = NodeKind.document := by rw [hkdd]; exact hk
          have hok' : DocumentChildrenOk s₁.tree d := h₁.documentChildren d dd₁ hd₁ hk₁
          by_cases hne : d = parent
          · subst hne
            have hdockind : kindOf s₁.tree d = some NodeKind.document := by
              simp [kindOf, hd₁, hk₁]
            obtain ⟨f1, _, f3, f4, f5, f6⟩ := hok₁ hdockind
            refine documentChildrenOk_of_insertAt hwf₁ hins' ?_ ?_ ?_ hok'
            · intro k hk'
              exact f1 n (List.mem_cons_self ..) k hk'
            · intro helem
              refine ⟨?_, f5 n (List.mem_cons_self ..) helem⟩
              have hkn : (kindOf s₁.tree n == some NodeKind.element) = true := by
                rw [helem]; simp
              have hcnt : ((n :: ns).filter fun m =>
                  kindOf s₁.tree m == some NodeKind.element).length
                  = 1 + (ns.filter fun m =>
                    kindOf s₁.tree m == some NodeKind.element).length := by
                simp [List.filter, hkn, Nat.add_comm]
              rw [hcnt] at f3
              have hzero : (elementChildren s₁.tree d).length = 0 := by omega
              simpa using hzero
            · intro hdt
              have hkn : (kindOf s₁.tree n == some NodeKind.documentType) = true := by
                rw [hdt]; simp
              have hcnt : ((n :: ns).filter fun m =>
                  kindOf s₁.tree m == some NodeKind.documentType).length
                  = 1 + (ns.filter fun m =>
                    kindOf s₁.tree m == some NodeKind.documentType).length := by
                simp [List.filter, hkn, Nat.add_comm]
              rw [hcnt] at f4
              have hzero : (doctypeChildren s₁.tree d).length = 0 := by omega
              obtain ⟨hp1, hp2⟩ := f6 n (List.mem_cons_self ..) hdt
              exact ⟨by simpa using hzero, hp1, hp2⟩
          · exact documentChildrenOk_insertAt_ne hwf₁ hins' hne hok'
        have hok₂ : InsertSeqOk s₂.tree parent child ns :=
          insertSeqOk_insertAt hwf₁ hins' hok₁
        exact documentTreesValid_insertEach ns hwf₂ h₂
          (hdoc.map ((kindPreserving_adopt ha).trans (kindPreserving_insertAt hins'))) hok₂ hi



/-- `remove` は `InsertSeqOk` を壊さない。 -/
theorem insertSeqOk_remove {s s' : DOMState} {n : NodeId} {b : Bool} {parent : NodeId}
    {child : Option NodeId} {ns : List NodeId} (hwf : WellFormed s.tree)
    (hr : remove s n b = .ok s') (h : InsertSeqOk s.tree parent child ns) :
    InsertSeqOk s'.tree parent child ns :=
  insertSeqOk_of_removeAll (kindPreserving_remove hr)
    (detach_childrenOf_removeAll hwf (remove_ok hr).2) h

/-- fragment の children を外す step 4 も `InsertSeqOk` を壊さない。 -/
theorem insertSeqOk_removeEach :
    ∀ (ms : List NodeId) {s s' : DOMState} {b : Bool} {parent : NodeId}
      {child : Option NodeId} {ns : List NodeId},
      WellFormed s.tree → removeEach s ms b = .ok s' →
      InsertSeqOk s.tree parent child ns → InsertSeqOk s'.tree parent child ns
  | [], _, _, _, _, _, _, _, hr, h => by rw [← Except.ok.inj hr]; exact h
  | m :: ms, s, s', b, parent, child, ns, hwf, hr, h => by
    simp only [removeEach] at hr
    split at hr
    · simp at hr
    · next s₁ h₁ =>
      exact insertSeqOk_removeEach ms (remove_preserves_wellformed hwf h₁) hr
        (insertSeqOk_remove hwf h₁ h)

theorem documentTreesValid_insertNodesAt {s s' : DOMState} {parent : NodeId}
    {child : Option NodeId} {nodes : List NodeId} {b : Bool}
    (hwf : WellFormed s.tree) (h : DocumentTreesValid s.tree)
    (hok : InsertSeqOk s.tree parent child nodes)
    (hi : insertNodesAt s parent child nodes b = .ok s') : DocumentTreesValid s'.tree := by
  unfold insertNodesAt at hi
  simp only at hi
  split at hi
  · simp at hi
  · next sx hx =>
    have htree : s'.tree = sx.tree := by
      split at hi
      · rw [← Except.ok.inj hi]
      · rw [← Except.ok.inj hi]; simp
    rw [htree]
    unfold insertEachAt at hx
    split at hx
    · simp at hx
    · next pd hpd =>
      have hpd' : s.tree.get? parent = some pd := by simpa using hpd
      refine documentTreesValid_insertEach nodes (by simpa using hwf) (by simpa using h) ?_
        (by simpa using hok) hx
      exact ⟨_, by simpa using (isDocument_ownerDocument hwf hpd').choose_spec.1,
        (isDocument_ownerDocument hwf hpd').choose_spec.2⟩

/--
`insert` の Document 制約の保存を `InsertSeqOk` だけに依存させた形。

`replace` / `replace all` は `ensure pre-insertion validity` を
別の tree・別の reference child で通しているので、この形で使う。
-/
theorem documentTreesValid_insert_of_seqOk {s s' : DOMState} {node parent : NodeId}
    {child : Option NodeId} {b : Bool} (hwf : WellFormed s.tree)
    (h : DocumentTreesValid s.tree)
    (hok : ∀ nd, s.tree.get? node = some nd →
      InsertSeqOk s.tree parent child
        (if nd.kind = NodeKind.documentFragment then nd.children else [node]))
    (hi : insert s node parent child b = .ok s') : DocumentTreesValid s'.tree := by
  unfold insert at hi
  split at hi
  · simp at hi
  · next nd hnd =>
    split at hi
    · next hfrag =>
      have hfragkind : nd.kind = NodeKind.documentFragment := by simpa using hfrag
      have hok' : InsertSeqOk s.tree parent child nd.children := by
        have hx := hok nd hnd
        rwa [if_pos hfragkind] at hx
      split at hi
      · rw [← Except.ok.inj hi]; exact h
      · split at hi
        · simp at hi
        · next s₁ hre =>
          have hwf₁ : WellFormed s₁.tree := removeEach_preserves_wellformed _ hwf hre
          have h₁ : DocumentTreesValid s₁.tree := documentTreesValid_removeEach _ hwf h hre
          have hok₁ : InsertSeqOk s₁.tree parent child nd.children :=
            insertSeqOk_removeEach _ hwf hre hok'
          exact documentTreesValid_insertNodesAt (s := queueTreeMutationRecord s₁ node []
            nd.children none none) (by simpa using hwf₁) (by simpa using h₁)
            (by simpa using hok₁) hi
    · next hfrag =>
      have hnfrag : ¬ nd.kind = NodeKind.documentFragment := by
        intro hc; rw [hc] at hfrag; simp at hfrag
      have hok' : InsertSeqOk s.tree parent child [node] := by
        have hx := hok nd hnd
        rwa [if_neg hnfrag] at hx
      exact documentTreesValid_insertNodesAt hwf h hok' hi

/--
PLAN §6.3 の形。`insert` は Document の children 制約を保つ。

fragment を展開する側では step 8 が、単独の node の側では step 6 / 9 / 10-11 が
`InsertSeqOk` を与える。
-/
theorem documentTreesValid_insert {s s' : DOMState} {node parent : NodeId}
    {child : Option NodeId} {b : Bool} (hwf : WellFormed s.tree)
    (hsv : StructurallyValid s.tree) (h : DocumentTreesValid s.tree)
    (hv : ensurePreInsertionValidity s.tree node parent child [] = .ok ())
    (hi : insert s node parent child b = .ok s') : DocumentTreesValid s'.tree := by
  refine documentTreesValid_insert_of_seqOk hwf h ?_ hi
  intro nd hnd
  have hfacts : ∀ pd, s.tree.get? parent = some pd → pd.kind = NodeKind.document →
      nd.kind.isText = false ∧
      (nd.kind = NodeKind.documentFragment →
        (elementChildren s.tree node).length ≤ 1 ∧ textChildren s.tree node = []) ∧
      ((nd.kind = NodeKind.element ∨
          (nd.kind = NodeKind.documentFragment ∧ elementChildren s.tree node ≠ [])) →
        elementChildren s.tree parent = [] ∧
          ∀ c, child = some c →
            (kindOf s.tree c == some NodeKind.documentType) = false ∧
              doctypeFollows s.tree parent c = false) ∧
      (nd.kind = NodeKind.documentType →
        doctypeChildren s.tree parent = [] ∧
          (∀ c, child = some c → elementPrecedes s.tree parent c = false) ∧
          (child = none → elementChildren s.tree parent = [])) :=
    fun pd hpd hk => by
      obtain ⟨g1, g2, g3, g4⟩ := ensurePreInsertionValidity_documentFacts hpd hnd hk hv
      refine ⟨g1, g2, ?_, ?_⟩
      · intro hcase
        obtain ⟨a1, a2⟩ := g3 hcase
        exact ⟨eq_nil_of_forall_mem_nil a1,
          fun c hc => ⟨(a2 c hc).1.resolve_right (by simp), (a2 c hc).2⟩⟩
      · intro hdt
        obtain ⟨b1, b2, b3⟩ := g4 hdt
        exact ⟨eq_nil_of_forall_mem_nil b1, b2, fun hc => eq_nil_of_forall_mem_nil (b3 hc)⟩
  have hparentOk : ∀ pd, s.tree.get? parent = some pd → pd.kind = NodeKind.document →
      DocumentChildrenOk s.tree parent := fun pd hpd hk => h.documentChildren parent pd hpd hk
  have hexists : kindOf s.tree parent = some NodeKind.document →
      ∃ pd, s.tree.get? parent = some pd ∧ pd.kind = NodeKind.document := by
    intro hkp
    cases hpd : s.tree.get? parent with
    | none => rw [kindOf, hpd] at hkp; simp at hkp
    | some pd =>
      refine ⟨pd, rfl, ?_⟩
      rw [kindOf, hpd] at hkp
      simpa using hkp
  by_cases hfragkind : nd.kind = NodeKind.documentFragment
  · rw [if_pos hfragkind]
    -- fragment の children に doctype は無い
    have hnodt : ∀ m ∈ nd.children,
        (kindOf s.tree m == some NodeKind.documentType) = false := by
      intro m hm
      have hne := child_not_doctype hsv hnd (by rw [hfragkind]; simp) hm
      cases hmd : s.tree.get? m with
      | none => simp [kindOf, hmd]
      | some md => simp [kindOf, hmd, hne md hmd]
    intro hkp
    obtain ⟨pd, hpd, hpk⟩ := hexists hkp
    obtain ⟨_, f2, f3, _⟩ := hfacts pd hpd hpk
    obtain ⟨hlen, htx⟩ := f2 hfragkind
    obtain ⟨he1, he2, _, _⟩ := hparentOk pd hpd hpk
    have hchn : childrenOf s.tree node = nd.children := childrenOf_eq hnd
    have hdtnil : (nd.children.filter fun m =>
        kindOf s.tree m == some NodeKind.documentType) = [] := by
      cases hl : nd.children.filter fun m =>
          kindOf s.tree m == some NodeKind.documentType with
      | nil => rfl
      | cons y l =>
        exfalso
        have hy : y ∈ nd.children.filter fun m =>
            kindOf s.tree m == some NodeKind.documentType := by rw [hl]; simp
        obtain ⟨hy1, hy2⟩ := List.mem_filter.mp hy
        rw [hnodt y hy1] at hy2
        simp at hy2
    have helemfilter : (nd.children.filter fun m =>
        kindOf s.tree m == some NodeKind.element) = elementChildren s.tree node := by
      unfold elementChildren
      rw [hchn]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro m hm k hk
      have hnot : m ∉ textChildren s.tree node := by rw [htx]; simp
      unfold textChildren at hnot
      rw [hchn] at hnot
      cases hik : k.isText with
      | false => rfl
      | true => exact absurd (List.mem_filter.mpr ⟨hm, by rw [hk]; exact hik⟩) hnot
    · rw [helemfilter, hdtnil]
      simpa using hlen
    · rw [helemfilter]
      by_cases hnil : elementChildren s.tree node = []
      · rw [hnil]; simpa using he1
      · rw [(f3 (Or.inr ⟨hfragkind, hnil⟩)).1]
        simpa using hlen
    · rw [hdtnil]
      simpa using he2
    · intro m hm hk c hc
      refine (f3 (Or.inr ⟨hfragkind, ?_⟩)).2 c hc
      intro hnil
      have hmem : m ∈ elementChildren s.tree node := by
        unfold elementChildren
        rw [hchn]
        exact List.mem_filter.mpr ⟨hm, by rw [hk]; simp⟩
      rw [hnil] at hmem
      simp at hmem
    · intro m hm hk
      exfalso
      have hb := hnodt m hm
      rw [hk] at hb
      simp at hb
  · rw [if_neg hfragkind]
    intro hkp
    obtain ⟨pd, hpd, hpk⟩ := hexists hkp
    obtain ⟨f1, _, f3, f4⟩ := hfacts pd hpd hpk
    obtain ⟨he1, he2, _, _⟩ := hparentOk pd hpd hpk
    have hkn : kindOf s.tree node = some nd.kind := by rw [kindOf, hnd]; rfl
    have hE : ([node].filter fun m => kindOf s.tree m == some NodeKind.element).length
        = if nd.kind = NodeKind.element then 1 else 0 := by
      by_cases hk : nd.kind = NodeKind.element
      · simp [List.filter, hkn, hk]
      · have hb : (nd.kind == NodeKind.element) = false := by simpa using hk
        simp [List.filter, hkn, hb, hk]
    have hD : ([node].filter fun m => kindOf s.tree m == some NodeKind.documentType).length
        = if nd.kind = NodeKind.documentType then 1 else 0 := by
      by_cases hk : nd.kind = NodeKind.documentType
      · simp [List.filter, hkn, hk]
      · have hb : (nd.kind == NodeKind.documentType) = false := by simpa using hk
        simp [List.filter, hkn, hb, hk]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro m hm k hk
      rcases List.mem_singleton.mp hm with rfl
      rw [hkn] at hk
      obtain rfl : k = nd.kind := (Option.some.inj hk).symm
      exact f1
    · rw [hE, hD]
      by_cases hk : nd.kind = NodeKind.element
      · simp [hk]
      · rw [if_neg hk]
        by_cases hk2 : nd.kind = NodeKind.documentType <;> simp [hk2]
    · rw [hE]
      by_cases hk : nd.kind = NodeKind.element
      · rw [if_pos hk, (f3 (Or.inl hk)).1]
        simp
      · rw [if_neg hk]
        simpa using he1
    · rw [hD]
      by_cases hk : nd.kind = NodeKind.documentType
      · rw [if_pos hk, (f4 hk).1]
        simp
      · rw [if_neg hk]
        simpa using he2
    · intro m hm hk c hc
      rcases List.mem_singleton.mp hm with rfl
      rw [hkn] at hk
      exact (f3 (Or.inl (Option.some.inj hk))).2 c hc
    · intro m hm hk
      rcases List.mem_singleton.mp hm with rfl
      rw [hkn] at hk
      exact ⟨(f4 (Option.some.inj hk)).2.1, (f4 (Option.some.inj hk)).2.2⟩


/-! ## replace -/

/--
`replace` は adopt → （必要なら）child の remove → insert という三段である。

`ensure pre-insertion validity` は元の tree に対して `child` を除外して走るので、
`insert` に渡す前提は kind に関する三つの事実として持ち回る。
-/
theorem structurallyValid_replace {s s' : DOMState} {child node parent : NodeId}
    (hwf : WellFormed s.tree) (h : StructurallyValid s.tree)
    (hr : replace s child node parent = .ok s') : StructurallyValid s'.tree := by
  unfold replace at hr
  split at hr
  · simp at hr
  · next hv =>
    split at hr
    · simp at hr
    · next pd hpd =>
      simp only at hr
      split at hr
      · simp at hr
      · next s₁ ha =>
        have hwf₁ := adopt_preserves_wellformed hwf (isDocument_ownerDocument hwf hpd) ha
        have h₁ : StructurallyValid s₁.tree := structurallyValid_adopt h
          (isDocument_ownerDocument hwf hpd) ha
        have hkp₁ : KindPreserving s.tree s₁.tree := kindPreserving_adopt ha
        split at hr
        · simp at hr
        · next s₂ hrm =>
          have hstep : StructurallyValid s₂.tree ∧ KindPreserving s₁.tree s₂.tree ∧
              WellFormed s₂.tree := by
            revert hrm; split
            · intro hrm
              rw [← Except.ok.inj hrm]
              exact ⟨h₁, KindPreserving.refl _, hwf₁⟩
            · intro hrm
              have hrm' : remove s₁ child true = .ok s₂ := by simpa using hrm
              exact ⟨structurallyValid_remove h₁ hrm', kindPreserving_remove hrm',
                remove_preserves_wellformed hwf₁ hrm'⟩
          obtain ⟨h₂, hkp₂, hwf₂⟩ := hstep
          have hkp : KindPreserving s.tree s₂.tree := hkp₁.trans hkp₂
          split at hr
          · simp at hr
          · next s₃ hi =>
            have f1 := kindFact_of_kindPreserving hkp (P := fun k => k.canHaveChildren = true)
              (ensurePreInsertionValidity_parentCanHaveChildren hv)
            have f2 := kindFact_of_kindPreserving hkp (P := fun k => k ≠ NodeKind.document)
              (ensurePreInsertionValidity_nodeNotDocument hv)
            have f3 := doctypeFact_of_kindPreserving hkp
              (ensurePreInsertionValidity_doctypeParentIsDocument hv)
            have h₃ : StructurallyValid s₃.tree :=
              structurallyValid_insert_of_facts h₂ f1 f2 f3 hi
            rw [← Except.ok.inj hr]
            simpa using h₃

theorem nodeDocumentsValid_replace {s s' : DOMState} {child node parent : NodeId}
    (hwf : WellFormed s.tree) (hsv : StructurallyValid s.tree) (h : NodeDocumentsValid s.tree)
    (hr : replace s child node parent = .ok s') : NodeDocumentsValid s'.tree := by
  unfold replace at hr
  split at hr
  · simp at hr
  · next hv =>
    split at hr
    · simp at hr
    · next pd hpd =>
      simp only at hr
      split at hr
      · simp at hr
      · next s₁ ha =>
        have hwf₁ := adopt_preserves_wellformed hwf (isDocument_ownerDocument hwf hpd) ha
        have hs₁ : StructurallyValid s₁.tree := structurallyValid_adopt hsv
          (isDocument_ownerDocument hwf hpd) ha
        have h₁ : NodeDocumentsValid s₁.tree := nodeDocumentsValid_adopt hsv h
          (isDocument_ownerDocument hwf hpd) (ensurePreInsertionValidity_nodeNotDocument hv) ha
        have hkp₁ : KindPreserving s.tree s₁.tree := kindPreserving_adopt ha
        split at hr
        · simp at hr
        · next s₂ hrm =>
          have hstep : NodeDocumentsValid s₂.tree ∧ StructurallyValid s₂.tree ∧
              KindPreserving s₁.tree s₂.tree ∧ WellFormed s₂.tree := by
            revert hrm; split
            · intro hrm
              rw [← Except.ok.inj hrm]
              exact ⟨h₁, hs₁, KindPreserving.refl _, hwf₁⟩
            · intro hrm
              have hrm' : remove s₁ child true = .ok s₂ := by simpa using hrm
              exact ⟨nodeDocumentsValid_remove hwf₁ h₁ hrm', structurallyValid_remove hs₁ hrm',
                kindPreserving_remove hrm', remove_preserves_wellformed hwf₁ hrm'⟩
          obtain ⟨h₂, hs₂, hkp₂, hwf₂⟩ := hstep
          have hkp : KindPreserving s.tree s₂.tree := hkp₁.trans hkp₂
          split at hr
          · simp at hr
          · next s₃ hi =>
            have f1 := kindFact_of_kindPreserving hkp (P := fun k => k.canHaveChildren = true)
              (ensurePreInsertionValidity_parentCanHaveChildren hv)
            have f2 := kindFact_of_kindPreserving hkp (P := fun k => k ≠ NodeKind.document)
              (ensurePreInsertionValidity_nodeNotDocument hv)
            have f3 := doctypeFact_of_kindPreserving hkp
              (ensurePreInsertionValidity_doctypeParentIsDocument hv)
            have h₃ : NodeDocumentsValid s₃.tree :=
              nodeDocumentsValid_insert_of_facts hs₂ h₂ f1 f2 f3 hi
            rw [← Except.ok.inj hr]
            simpa using h₃



/-! ## replace が Document の children 制約を保つこと -/

/-- children の分割から次の兄弟が読み取れる。 -/
theorem nextSibling_of_split {t : Tree} (hwf : WellFormed t) {parent c : NodeId}
    {A B : List NodeId} (hpar : parentOf t c = some parent)
    (hsplit : childrenOf t parent = A ++ c :: B) : nextSibling t c = B.head? := by
  unfold nextSibling
  simp only [hpar, splitAt?_childrenOf_of_split hwf hsplit]

/--
`replace` の reference child は、`child` のあった位置より後ろで最初に残る node である。

step 2-3 は「`child` の次の兄弟。ただしそれが `node` なら `node` の次の兄弟」だが、
`node` は step 6 の adopt で外れるので、結局この形になる。
-/
theorem replace_reference_head {s : DOMState} {child node parent : NodeId}
    (hwf : WellFormed s.tree) (hpar : parentOf s.tree child = some parent)
    {A B : List NodeId} (hsplit : childrenOf s.tree parent = A ++ child :: B) :
    (if nextSibling s.tree child = some node then nextSibling s.tree node
      else nextSibling s.tree child) = (ListUtil.removeAll B node).head? := by
  have hnd : (childrenOf s.tree parent).Nodup := childrenOf_nodup hwf parent
  have hns : nextSibling s.tree child = B.head? := nextSibling_of_split hwf hpar hsplit
  by_cases hb : nextSibling s.tree child = some node
  · rw [if_pos hb]
    rw [hns] at hb
    cases hB : B with
    | nil => rw [hB] at hb; simp at hb
    | cons y B' =>
      rw [hB] at hb
      simp only [List.head?_cons, Option.some.injEq] at hb
      have hsplity : childrenOf s.tree parent = (A ++ [child]) ++ y :: B' := by
        rw [hsplit, hB]; simp
      have hndy : y ∉ A ++ [child] ∧ y ∉ B' := by
        refine ListUtil.nodup_split ?_
        rw [← hsplity]; exact hnd
      have hypar : parentOf s.tree y = some parent := by
        refine parentOf_of_mem_childrenOf hwf ?_
        rw [hsplity]
        exact List.mem_append_right _ (by simp)
      have hnsy : nextSibling s.tree y = B'.head? := nextSibling_of_split hwf hypar hsplity
      subst hb
      rw [hnsy, ListUtil.removeAll_cons, if_pos rfl, ListUtil.removeAll_eq_self hndy.2]
  · rw [if_neg hb, hns]
    cases hB : B with
    | nil => simp [ListUtil.removeAll]
    | cons y B' =>
      have hyn : ¬ y = node := by
        rw [hns, hB] at hb
        simpa using hb
      rw [ListUtil.removeAll_cons, if_neg hyn]
      simp


/-- 述語を満たす要素が無ければ filter は空。 -/
theorem filter_eq_nil_of_all_false {α : Type _} (l : List α) (p : α → Bool)
    (h : ∀ x ∈ l, p x = false) : l.filter p = [] := by
  cases hl : l.filter p with
  | nil => rfl
  | cons y r =>
    exfalso
    have hy : y ∈ l.filter p := by rw [hl]; simp
    obtain ⟨hy1, hy2⟩ := List.mem_filter.mp hy
    rw [h y hy1] at hy2
    simp at hy2

/-- 空でない filter からは、述語を満たす要素が取り出せる。 -/
theorem exists_mem_of_filter_ne_nil {α : Type _} {l : List α} {p : α → Bool}
    (h : l.filter p ≠ []) : ∃ x ∈ l, p x = true := by
  cases hl : l.filter p with
  | nil => exact absurd hl h
  | cons y r =>
    have hy : y ∈ l.filter p := by rw [hl]; simp
    obtain ⟨hy1, hy2⟩ := List.mem_filter.mp hy
    exact ⟨y, hy1, hy2⟩

/--
`replace` が `insert` を呼ぶ時点で `InsertSeqOk` が成り立つ。

step 1 の検査は元の tree で `child` を除外して走るが、`child` は step 7 で外れるので、
除外が効いていた条件（element の子、doctype の子）は素直に空になる。
reference child は `child` のあった位置の直後なので、
「後ろに doctype が無い」「前に element が無い」もそのまま移る。
-/
theorem insertSeqOk_of_replace {s s₂ : DOMState} {child node parent : NodeId}
    {pd nd nd₂ : NodeData}
    (hwf : WellFormed s.tree) (hsv : StructurallyValid s.tree)
    (hpd : s.tree.get? parent = some pd) (hnd : s.tree.get? node = some nd)
    (hv : ensurePreInsertionValidity s.tree node parent (some child) [child] = .ok ())
    (h₂ : DocumentTreesValid s₂.tree)
    (hkind : ∀ m, kindOf s₂.tree m = kindOf s.tree m)
    (hch : ∀ p, childrenOf s₂.tree p =
      ListUtil.removeAll (ListUtil.removeAll (childrenOf s.tree p) node) child)
    (hnd₂ : s₂.tree.get? node = some nd₂) :
    InsertSeqOk s₂.tree parent
      (if nextSibling s.tree child = some node then nextSibling s.tree node
        else nextSibling s.tree child)
      (if nd₂.kind = NodeKind.documentFragment then nd₂.children else [node]) := by
  intro hdocparent
  -- parent は Document
  have hpk : pd.kind = NodeKind.document := by
    have hk := hkind parent
    rw [hdocparent, kindOf, hpd] at hk
    simpa using hk.symm
  obtain ⟨f1, f2, f3, f4⟩ := ensurePreInsertionValidity_documentFacts hpd hnd hpk hv
  have hkd : nd₂.kind = nd.kind := by
    have hk := hkind node
    rw [kindOf, kindOf, hnd₂, hnd] at hk
    simpa using hk
  -- children の列は `node` と `child` を抜いたものである
  have hsub₂ : ∀ p, (childrenOf s₂.tree p).Sublist (childrenOf s.tree p) := by
    intro p
    rw [hch p]
    exact (ListUtil.removeAll_sublist _ _).trans (ListUtil.removeAll_sublist _ _)
  have hnotchild : ∀ p, child ∉ childrenOf s₂.tree p := by
    intro p
    rw [hch p]
    exact ListUtil.not_mem_removeAll _ _
  -- 入れる node の列は元の列の sublist
  have hnschild : nd₂.children.Sublist nd.children := by
    have h1 := hsub₂ node
    rw [childrenOf_eq hnd₂, childrenOf_eq hnd] at h1
    exact h1
  have hns : ((if nd₂.kind = NodeKind.documentFragment then nd₂.children
        else [node])).Sublist (if nd.kind = NodeKind.documentFragment then nd.children
        else [node]) := by
    by_cases hk : nd₂.kind = NodeKind.documentFragment
    · rw [if_pos hk, if_pos (by rw [← hkd]; exact hk)]
      exact hnschild
    · rw [if_neg hk, if_neg (by rw [← hkd]; exact hk)]
      exact List.Sublist.refl _
  -- `child` の位置
  have hchildpar : parentOf s.tree child = some parent :=
    ensurePreInsertionValidity_childParent hv child rfl
  have hchildmem : child ∈ childrenOf s.tree parent :=
    (mem_childrenOf_iff hwf child parent).mp hchildpar
  obtain ⟨A, B, hsplit⟩ := ListUtil.exists_splitAt?_of_mem hchildmem
  have hLAB : childrenOf s.tree parent = A ++ child :: B := ListUtil.splitAt?_eq_some hsplit
  have hndL : (A ++ child :: B).Nodup := by
    rw [← hLAB]; exact childrenOf_nodup hwf parent
  have hdisj : ∀ x ∈ B, x ∉ A := by
    intro x hx hxa
    exact (List.nodup_append.mp hndL).2.2 x hxa x (List.mem_cons_of_mem _ hx) rfl
  have hch₂ : childrenOf s₂.tree parent =
      ListUtil.removeAll A node ++ ListUtil.removeAll B node := by
    rw [hch parent, hLAB]
    exact ListUtil.removeAll_removeAll_split (ListUtil.nodup_split hndL).1
      (ListUtil.nodup_split hndL).2
  have href : (if nextSibling s.tree child = some node then nextSibling s.tree node
      else nextSibling s.tree child) = (ListUtil.removeAll B node).head? :=
    replace_reference_head hwf hchildpar hLAB
  -- 除外されていた条件は `child` が外れることで空になる
  have hnodoctypeB : doctypeFollows s.tree parent child
      = B.any fun x => kindOf s.tree x == some NodeKind.documentType := by
    unfold doctypeFollows
    rw [hsplit]
  have hnoelemA : elementPrecedes s.tree parent child
      = A.any fun x => kindOf s.tree x == some NodeKind.element := by
    unfold elementPrecedes
    rw [hsplit]
  -- ns₂ の中の element と doctype の数
  have hDzero : nd.kind = NodeKind.documentFragment →
      ∀ m ∈ nd₂.children, (kindOf s.tree m == some NodeKind.documentType) = false := by
    intro hfrag m hm
    have hne := child_not_doctype hsv hnd (by rw [hfrag]; simp) (hnschild.subset hm)
    cases hmd : s.tree.get? m with
    | none => simp [kindOf, hmd]
    | some md => simp [kindOf, hmd, hne md hmd]
  have helemcount : ((if nd₂.kind = NodeKind.documentFragment then nd₂.children else [node]).filter
      fun m => kindOf s.tree m == some NodeKind.element).length ≤ 1 := by
    by_cases hk : nd₂.kind = NodeKind.documentFragment
    · rw [if_pos hk]
      have hfrag : nd.kind = NodeKind.documentFragment := by rw [← hkd]; exact hk
      obtain ⟨hlen, _⟩ := f2 hfrag
      refine Nat.le_trans ?_ hlen
      have hsl := hnschild.filter fun m => kindOf s.tree m == some NodeKind.element
      have := hsl.length_le
      unfold elementChildren
      rw [childrenOf_eq hnd]
      exact this
    · rw [if_neg hk]
      by_cases hke : (kindOf s.tree node == some NodeKind.element) = true <;>
        simp [List.filter, hke]
  have hdtcount : ((if nd₂.kind = NodeKind.documentFragment then nd₂.children else [node]).filter
      fun m => kindOf s.tree m == some NodeKind.documentType).length ≤ 1 := by
    by_cases hk : nd₂.kind = NodeKind.documentFragment
    · rw [if_pos hk, filter_eq_nil_of_all_false _ _ (hDzero (by rw [← hkd]; exact hk))]
      simp
    · rw [if_neg hk]
      by_cases hke : (kindOf s.tree node == some NodeKind.documentType) = true <;>
        simp [List.filter, hke]
  -- ns₂ に element があれば step 9 / 8 の条件が使える
  have hf3 : ((if nd₂.kind = NodeKind.documentFragment then nd₂.children else [node]).filter
      fun m => kindOf s.tree m == some NodeKind.element) ≠ [] →
      (nd.kind = NodeKind.element ∨
        (nd.kind = NodeKind.documentFragment ∧ elementChildren s.tree node ≠ [])) := by
    intro hne
    obtain ⟨x, hx, hxk⟩ := exists_mem_of_filter_ne_nil hne
    by_cases hk : nd₂.kind = NodeKind.documentFragment
    · rw [if_pos hk] at hx
      refine Or.inr ⟨by rw [← hkd]; exact hk, ?_⟩
      intro hnil
      have hmem : x ∈ elementChildren s.tree node := by
        unfold elementChildren
        rw [childrenOf_eq hnd]
        exact List.mem_filter.mpr ⟨hnschild.subset hx, hxk⟩
      rw [hnil] at hmem
      simp at hmem
    · rw [if_neg hk, List.mem_singleton] at hx
      subst hx
      refine Or.inl ?_
      rw [kindOf, hnd] at hxk
      simpa using hxk
  have hf4 : ((if nd₂.kind = NodeKind.documentFragment then nd₂.children else [node]).filter
      fun m => kindOf s.tree m == some NodeKind.documentType) ≠ [] →
      nd.kind = NodeKind.documentType := by
    intro hne
    obtain ⟨x, hx, hxk⟩ := exists_mem_of_filter_ne_nil hne
    by_cases hk : nd₂.kind = NodeKind.documentFragment
    · exfalso
      rw [if_pos hk] at hx
      rw [hDzero (by rw [← hkd]; exact hk) x hx] at hxk
      simp at hxk
    · rw [if_neg hk, List.mem_singleton] at hx
      subst hx
      rw [kindOf, hnd] at hxk
      simpa using hxk
  -- `child` が外れるので、除外されていた子は残らない
  have helemnil : ((if nd₂.kind = NodeKind.documentFragment then nd₂.children else [node]).filter
      fun m => kindOf s.tree m == some NodeKind.element) ≠ [] →
      elementChildren s₂.tree parent = [] := by
    intro hne
    obtain ⟨hall, _⟩ := f3 (hf3 hne)
    unfold elementChildren
    refine filter_eq_nil_of_all_false _ _ ?_
    intro x hx
    cases hxk : (kindOf s₂.tree x == some NodeKind.element) with
    | false => rfl
    | true =>
      exfalso
      have hxk' : (kindOf s.tree x == some NodeKind.element) = true := by
        rw [← hkind x]; exact hxk
      have hmem : x ∈ elementChildren s.tree parent := by
        unfold elementChildren
        exact List.mem_filter.mpr ⟨hsub₂ parent |>.subset hx, hxk'⟩
      have := hall x hmem
      rw [List.mem_singleton] at this
      subst this
      exact hnotchild parent hx
  have hdtnil : ((if nd₂.kind = NodeKind.documentFragment then nd₂.children else [node]).filter
      fun m => kindOf s.tree m == some NodeKind.documentType) ≠ [] →
      doctypeChildren s₂.tree parent = [] := by
    intro hne
    obtain ⟨hall, _, _⟩ := f4 (hf4 hne)
    unfold doctypeChildren
    refine filter_eq_nil_of_all_false _ _ ?_
    intro x hx
    cases hxk : (kindOf s₂.tree x == some NodeKind.documentType) with
    | false => rfl
    | true =>
      exfalso
      have hxk' : (kindOf s.tree x == some NodeKind.documentType) = true := by
        rw [← hkind x]; exact hxk
      have hmem : x ∈ doctypeChildren s.tree parent := by
        unfold doctypeChildren
        exact List.mem_filter.mpr ⟨hsub₂ parent |>.subset hx, hxk'⟩
      have := hall x hmem
      rw [List.mem_singleton] at this
      subst this
      exact hnotchild parent hx
  -- s₂ 側で parent が Document であること
  obtain ⟨pd₂, hpd₂⟩ : ∃ pd₂, s₂.tree.get? parent = some pd₂ := by
    cases hq : s₂.tree.get? parent with
    | none => rw [kindOf, hq] at hdocparent; simp at hdocparent
    | some q => exact ⟨q, rfl⟩
  have hpk₂ : pd₂.kind = NodeKind.document := by
    rw [kindOf, hpd₂] at hdocparent
    simpa using hdocparent
  obtain ⟨hb1, hb2, _, _⟩ := h₂.documentChildren parent pd₂ hpd₂ hpk₂
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Text は入れない
    intro m hm k hk
    have hm' := hns.subset hm
    have hk' : kindOf s.tree m = some k := by rw [← hkind m]; exact hk
    by_cases hfrag : nd.kind = NodeKind.documentFragment
    · rw [if_pos hfrag] at hm'
      obtain ⟨_, htx⟩ := f2 hfrag
      have hnot : m ∉ textChildren s.tree node := by rw [htx]; simp
      unfold textChildren at hnot
      rw [childrenOf_eq hnd] at hnot
      cases hik : k.isText with
      | false => rfl
      | true => exact absurd (List.mem_filter.mpr ⟨hm', by rw [hk']; exact hik⟩) hnot
    · rw [if_neg hfrag, List.mem_singleton] at hm'
      subst hm'
      rw [kindOf, hnd] at hk'
      obtain rfl : k = nd.kind := (Option.some.inj hk').symm
      exact f1
  · -- element と doctype は合わせて高々一つ
    simp only [hkind]
    by_cases hk : nd₂.kind = NodeKind.documentFragment
    · rw [if_pos hk, filter_eq_nil_of_all_false _ _ (hDzero (by rw [← hkd]; exact hk))]
      simp only [List.length_nil, Nat.add_zero]
      have := helemcount
      rw [if_pos hk] at this
      exact this
    · rw [if_neg hk]
      by_cases hke : (kindOf s.tree node == some NodeKind.element) = true
      · have hkd' : (kindOf s.tree node == some NodeKind.documentType) = false := by
          have : kindOf s.tree node = some NodeKind.element := by simpa using hke
          rw [this]; simp
        simp [List.filter, hke, hkd']
      · simp only [Bool.not_eq_true] at hke
        by_cases hkt : (kindOf s.tree node == some NodeKind.documentType) = true
        · simp [List.filter, hke, hkt]
        · simp only [Bool.not_eq_true] at hkt
          simp [List.filter, hke, hkt]
  · -- element の子は高々一つ
    simp only [hkind]
    by_cases hne : ((if nd₂.kind = NodeKind.documentFragment then nd₂.children else [node]).filter
        fun m => kindOf s.tree m == some NodeKind.element) = []
    · rw [hne]
      simpa using hb1
    · rw [helemnil hne]
      simpa using helemcount
  · -- doctype の子は高々一つ
    simp only [hkind]
    by_cases hne : ((if nd₂.kind = NodeKind.documentFragment then nd₂.children else [node]).filter
        fun m => kindOf s.tree m == some NodeKind.documentType) = []
    · rw [hne]
      simpa using hb2
    · rw [hdtnil hne]
      simpa using hdtcount
  · -- element を入れるなら、reference child より後ろに doctype は無い
    intro m hm hkm c hc
    have hne : ((if nd₂.kind = NodeKind.documentFragment then nd₂.children else [node]).filter
        fun x => kindOf s.tree x == some NodeKind.element) ≠ [] := by
      intro hnil
      have hmem : m ∈ (if nd₂.kind = NodeKind.documentFragment then nd₂.children
          else [node]).filter fun x => kindOf s.tree x == some NodeKind.element :=
        List.mem_filter.mpr ⟨hm, by rw [← hkind m, hkm]; simp⟩
      rw [hnil] at hmem
      simp at hmem
    obtain ⟨_, hafter⟩ := f3 (hf3 hne)
    have hdocfol : doctypeFollows s.tree parent child = false := (hafter child rfl).2
    rw [hnodoctypeB] at hdocfol
    -- reference child は `removeAll B node` の先頭
    rw [href] at hc
    cases hQ : ListUtil.removeAll B node with
    | nil => rw [hQ] at hc; simp at hc
    | cons y Q' =>
      rw [hQ] at hc
      simp only [List.head?_cons, Option.some.injEq] at hc
      subst hc
      have hyB : y ∈ B := by
        have hm : y ∈ ListUtil.removeAll B node := by rw [hQ]; simp
        exact ((ListUtil.mem_removeAll _ _ _).mp hm).2
      have hQ'B : ∀ x ∈ Q', x ∈ B := by
        intro x hx
        have hm : x ∈ ListUtil.removeAll B node := by rw [hQ]; exact List.mem_cons_of_mem _ hx
        exact ((ListUtil.mem_removeAll _ _ _).mp hm).2
      have hnoDT : ∀ x ∈ B, (kindOf s.tree x == some NodeKind.documentType) = false := by
        intro x hx
        cases hxk : (kindOf s.tree x == some NodeKind.documentType) with
        | false => rfl
        | true =>
          exfalso
          rw [Bool.eq_false_iff] at hdocfol
          exact hdocfol (List.any_eq_true.mpr ⟨x, hx, hxk⟩)
      refine ⟨by rw [hkind]; exact hnoDT y hyB, ?_⟩
      have hcnotA : y ∉ ListUtil.removeAll A node := fun hx =>
        hdisj y hyB ((ListUtil.mem_removeAll _ _ _).mp hx).2
      have hsplit₂ : ListUtil.splitAt? (childrenOf s₂.tree parent) y
          = some (ListUtil.removeAll A node, Q') := by
        rw [hch₂, hQ]
        exact ListUtil.splitAt?_append_cons_self hcnotA Q'
      unfold doctypeFollows
      rw [hsplit₂, Bool.eq_false_iff]
      intro hcon
      obtain ⟨x, hx, hxk⟩ := List.any_eq_true.mp hcon
      rw [hkind, hnoDT x (hQ'B x hx)] at hxk
      simp at hxk
  · -- doctype を入れるなら、reference child より前に element は無い
    intro m hm hkm
    have hne : ((if nd₂.kind = NodeKind.documentFragment then nd₂.children else [node]).filter
        fun x => kindOf s.tree x == some NodeKind.documentType) ≠ [] := by
      intro hnil
      have hmem : m ∈ (if nd₂.kind = NodeKind.documentFragment then nd₂.children
          else [node]).filter fun x => kindOf s.tree x == some NodeKind.documentType :=
        List.mem_filter.mpr ⟨hm, by rw [← hkind m, hkm]; simp⟩
      rw [hnil] at hmem
      simp at hmem
    obtain ⟨_, hprec, _⟩ := f4 (hf4 hne)
    have hnoEL : elementPrecedes s.tree parent child = false := hprec child rfl
    rw [hnoelemA] at hnoEL
    have hnoE : ∀ x ∈ A, (kindOf s.tree x == some NodeKind.element) = false := by
      intro x hx
      cases hxk : (kindOf s.tree x == some NodeKind.element) with
      | false => rfl
      | true =>
        exfalso
        rw [Bool.eq_false_iff] at hnoEL
        exact hnoEL (List.any_eq_true.mpr ⟨x, hx, hxk⟩)
    have hnoEA' : ∀ x ∈ ListUtil.removeAll A node,
        (kindOf s.tree x == some NodeKind.element) = false :=
      fun x hx => hnoE x ((ListUtil.mem_removeAll _ _ _).mp hx).2
    refine ⟨fun c hc => ?_, fun hc => ?_⟩
    · rw [href] at hc
      cases hQ : ListUtil.removeAll B node with
      | nil => rw [hQ] at hc; simp at hc
      | cons y Q' =>
        rw [hQ] at hc
        simp only [List.head?_cons, Option.some.injEq] at hc
        subst hc
        have hyB : y ∈ B := by
          have hm : y ∈ ListUtil.removeAll B node := by rw [hQ]; simp
          exact ((ListUtil.mem_removeAll _ _ _).mp hm).2
        have hcnotA : y ∉ ListUtil.removeAll A node := fun hx =>
          hdisj y hyB ((ListUtil.mem_removeAll _ _ _).mp hx).2
        have hsplit₂ : ListUtil.splitAt? (childrenOf s₂.tree parent) y
            = some (ListUtil.removeAll A node, Q') := by
          rw [hch₂, hQ]
          exact ListUtil.splitAt?_append_cons_self hcnotA Q'
        unfold elementPrecedes
        rw [hsplit₂, Bool.eq_false_iff]
        intro hcon
        obtain ⟨x, hx, hxk⟩ := List.any_eq_true.mp hcon
        rw [hkind, hnoEA' x hx] at hxk
        simp at hxk
    · rw [href] at hc
      have hQnil : ListUtil.removeAll B node = [] := by
        cases hQ : ListUtil.removeAll B node with
        | nil => rfl
        | cons y Q' => rw [hQ] at hc; simp at hc
      have hchA : childrenOf s₂.tree parent = ListUtil.removeAll A node := by
        rw [hch₂, hQnil, List.append_nil]
      unfold elementChildren
      rw [hchA]
      refine filter_eq_nil_of_all_false _ _ (fun x hx => ?_)
      rw [hkind]
      exact hnoEA' x hx


/-- PLAN §6.3 の形。`replace` は Document の children 制約を保つ。 -/
theorem documentTreesValid_replace {s s' : DOMState} {child node parent : NodeId}
    (hwf : WellFormed s.tree) (hsv : StructurallyValid s.tree) (h : DocumentTreesValid s.tree)
    (hr : replace s child node parent = .ok s') : DocumentTreesValid s'.tree := by
  unfold replace at hr
  split at hr
  · simp at hr
  · next hv =>
    split at hr
    · simp at hr
    · next pd hpd =>
      simp only at hr
      split at hr
      · simp at hr
      · next s₁ ha =>
        have hwf₁ := adopt_preserves_wellformed hwf (isDocument_ownerDocument hwf hpd) ha
        have h₁ : DocumentTreesValid s₁.tree := documentTreesValid_adopt hwf h ha
        have hkp₁ : KindPreserving s.tree s₁.tree := kindPreserving_adopt ha
        have hch₁ : ∀ p, childrenOf s₁.tree p =
            ListUtil.removeAll (childrenOf s.tree p) node := adopt_childrenOf hwf ha
        split at hr
        · simp at hr
        · next s₂ hrm =>
          have hstep : DocumentTreesValid s₂.tree ∧ KindPreserving s₁.tree s₂.tree ∧
              WellFormed s₂.tree ∧
              (∀ p, childrenOf s₂.tree p = ListUtil.removeAll (childrenOf s₁.tree p) child) := by
            revert hrm
            split
            · next hnone =>
              intro hrm
              rw [← Except.ok.inj hrm]
              refine ⟨h₁, KindPreserving.refl _, hwf₁, fun p => ?_⟩
              rw [ListUtil.removeAll_eq_self]
              intro hmem
              have hpar := parentOf_of_mem_childrenOf hwf₁ hmem
              rw [hnone] at hpar
              simp at hpar
            · intro hrm
              have hrm' : remove s₁ child true = .ok s₂ := by simpa using hrm
              exact ⟨documentTreesValid_remove hwf₁ h₁ hrm', kindPreserving_remove hrm',
                remove_preserves_wellformed hwf₁ hrm',
                detach_childrenOf_removeAll hwf₁ (remove_ok hrm').2⟩
          obtain ⟨h₂, hkp₂, hwf₂, hch₂⟩ := hstep
          have hkind : ∀ m, kindOf s₂.tree m = kindOf s.tree m := hkp₁.trans hkp₂
          have hchall : ∀ p, childrenOf s₂.tree p =
              ListUtil.removeAll (ListUtil.removeAll (childrenOf s.tree p) node) child := by
            intro p
            rw [hch₂ p, hch₁ p]
          split at hr
          · simp at hr
          · next s₃ hi =>
            have h₃ : DocumentTreesValid s₃.tree := by
              refine documentTreesValid_insert_of_seqOk hwf₂ h₂ ?_ hi
              intro nd₂ hnd₂
              obtain ⟨nd, hnd, _⟩ := kindPreserving_get? (hkp₁.trans hkp₂) hnd₂
              exact insertSeqOk_of_replace hwf hsv hpd hnd hv h₂ hkind hchall hnd₂
            rw [← Except.ok.inj hr]
            simpa using h₃

/-! ## replace all -/

/-- `removeEach` は children を減らすだけで、外した node はどこの children にも残らない。 -/
theorem removeEach_childrenOf_sub :
    ∀ (ms : List NodeId) {s s' : DOMState} {b : Bool}, WellFormed s.tree →
      removeEach s ms b = .ok s' →
      ∀ p, (childrenOf s'.tree p).Sublist (childrenOf s.tree p) ∧
        (∀ m ∈ ms, m ∉ childrenOf s'.tree p)
  | [], _, _, _, _, hr, p => by
    rw [← Except.ok.inj hr]
    exact ⟨List.Sublist.refl _, fun m hm => absurd hm (by simp)⟩
  | n :: ms, s, s', b, hwf, hr, p => by
    simp only [removeEach] at hr
    split at hr
    · simp at hr
    · next s₁ h₁ =>
      have hch : childrenOf s₁.tree p = ListUtil.removeAll (childrenOf s.tree p) n :=
        detach_childrenOf_removeAll hwf (remove_ok h₁).2 p
      have hwf₁ := remove_preserves_wellformed hwf h₁
      obtain ⟨hsub, hnot⟩ := removeEach_childrenOf_sub ms hwf₁ hr p
      have hsub' : (childrenOf s₁.tree p).Sublist (childrenOf s.tree p) := by
        rw [hch]; exact ListUtil.removeAll_sublist _ _
      refine ⟨hsub.trans hsub', fun m hm => ?_⟩
      rcases List.mem_cons.mp hm with rfl | hm'
      · intro hmem
        have hx₁ := hsub.subset hmem
        rw [hch] at hx₁
        exact ((ListUtil.mem_removeAll _ _ _).mp hx₁).1 rfl
      · exact hnot m hm'

/-- §4.2.3 replace all step 4 の後、parent の children は空になる。 -/
theorem removeEach_childrenOf_nil {s s' : DOMState} {parent : NodeId} {b : Bool}
    (hwf : WellFormed s.tree) (hr : removeEach s (childrenOf s.tree parent) b = .ok s') :
    childrenOf s'.tree parent = [] := by
  obtain ⟨hsub, hnot⟩ := removeEach_childrenOf_sub _ hwf hr parent
  cases hl : childrenOf s'.tree parent with
  | nil => rfl
  | cons y l =>
    exfalso
    have hy : y ∈ childrenOf s'.tree parent := by rw [hl]; simp
    exact hnot y (hsub.subset hy) hy

/--
`replace all` は node tree の制約を自分では検査しない。

したがって `insert` に必要な kind の事実は仮定として受け取る。
呼び出し側（`replaceChildren` など）が `ensure pre-insertion validity` で確立する。
-/
theorem structurallyValid_replaceAll {s s' : DOMState} {node : Option NodeId} {parent : NodeId}
    (h : StructurallyValid s.tree)
    (hpk : ∀ pd, s.tree.get? parent = some pd → pd.kind.canHaveChildren = true)
    (hnk : ∀ n, node = some n → ∀ nd, s.tree.get? n = some nd → nd.kind ≠ NodeKind.document)
    (hdtf : ∀ n, node = some n → ∀ nd, s.tree.get? n = some nd →
      nd.kind = NodeKind.documentType →
      ∀ pd, s.tree.get? parent = some pd → pd.kind = NodeKind.document)
    (hr : replaceAll s node parent = .ok s') : StructurallyValid s'.tree := by
  unfold replaceAll at hr
  simp only at hr
  split at hr
  · simp at hr
  · next s₁ hre =>
    have h₁ : StructurallyValid s₁.tree := structurallyValid_removeEach _ h hre
    have hkp : KindPreserving s.tree s₁.tree := kindPreserving_removeEach _ hre
    split at hr
    · simp at hr
    · next s₂ hins =>
      have h₂ : StructurallyValid s₂.tree := by
        revert hins
        split
        · intro hins; rw [← Except.ok.inj hins]; exact h₁
        · next _ _ m =>
          intro hins
          refine structurallyValid_insert_of_facts h₁ ?_ ?_ ?_ (by simpa using hins)
          · exact kindFact_of_kindPreserving hkp (P := fun k => k.canHaveChildren = true) hpk
          · exact kindFact_of_kindPreserving hkp (P := fun k => k ≠ NodeKind.document)
              (hnk m rfl)
          · exact doctypeFact_of_kindPreserving hkp (hdtf m rfl)
      rw [← Except.ok.inj hr]
      simpa using h₂

theorem nodeDocumentsValid_replaceAll {s s' : DOMState} {node : Option NodeId} {parent : NodeId}
    (hs : StructurallyValid s.tree) (h : NodeDocumentsValid s.tree)
    (hpk : ∀ pd, s.tree.get? parent = some pd → pd.kind.canHaveChildren = true)
    (hnk : ∀ n, node = some n → ∀ nd, s.tree.get? n = some nd → nd.kind ≠ NodeKind.document)
    (hdtf : ∀ n, node = some n → ∀ nd, s.tree.get? n = some nd →
      nd.kind = NodeKind.documentType →
      ∀ pd, s.tree.get? parent = some pd → pd.kind = NodeKind.document)
    (hr : replaceAll s node parent = .ok s') : NodeDocumentsValid s'.tree := by
  unfold replaceAll at hr
  simp only at hr
  split at hr
  · simp at hr
  · next s₁ hre =>
    have hs₁ : StructurallyValid s₁.tree := structurallyValid_removeEach _ hs hre
    have h₁ : NodeDocumentsValid s₁.tree := nodeDocumentsValid_removeEach _ hs h hre
    have hkp : KindPreserving s.tree s₁.tree := kindPreserving_removeEach _ hre
    split at hr
    · simp at hr
    · next s₂ hins =>
      have h₂ : NodeDocumentsValid s₂.tree := by
        revert hins
        split
        · intro hins; rw [← Except.ok.inj hins]; exact h₁
        · next _ _ m =>
          intro hins
          refine nodeDocumentsValid_insert_of_facts hs₁ h₁ ?_ ?_ ?_ (by simpa using hins)
          · exact kindFact_of_kindPreserving hkp (P := fun k => k.canHaveChildren = true) hpk
          · exact kindFact_of_kindPreserving hkp (P := fun k => k ≠ NodeKind.document)
              (hnk m rfl)
          · exact doctypeFact_of_kindPreserving hkp (hdtf m rfl)
      rw [← Except.ok.inj hr]
      simpa using h₂

/--
`replace all` は parent の children を空にしてから入れるので、
Document の制約には「入れる node の側」の条件しか要らない。
-/
theorem documentTreesValid_replaceAll {s s' : DOMState} {node : Option NodeId} {parent : NodeId}
    (hwf : WellFormed s.tree) (h : DocumentTreesValid s.tree)
    (hok : ∀ n, node = some n → ∀ nd, s.tree.get? n = some nd →
      (∀ m ∈ (if nd.kind = NodeKind.documentFragment then nd.children else [n]),
        ∀ k, kindOf s.tree m = some k → k.isText = false) ∧
      (((if nd.kind = NodeKind.documentFragment then nd.children else [n]).filter fun m =>
          kindOf s.tree m == some NodeKind.element).length +
        ((if nd.kind = NodeKind.documentFragment then nd.children else [n]).filter fun m =>
          kindOf s.tree m == some NodeKind.documentType).length ≤ 1))
    (hr : replaceAll s node parent = .ok s') : DocumentTreesValid s'.tree := by
  unfold replaceAll at hr
  simp only at hr
  split at hr
  · simp at hr
  · next s₁ hre =>
    have hwf₁ : WellFormed s₁.tree := removeEach_preserves_wellformed _ hwf hre
    have h₁ : DocumentTreesValid s₁.tree := documentTreesValid_removeEach _ hwf h hre
    have hkp : KindPreserving s.tree s₁.tree := kindPreserving_removeEach _ hre
    have hnil : childrenOf s₁.tree parent = [] := removeEach_childrenOf_nil hwf hre
    have helemnil : elementChildren s₁.tree parent = [] := by
      unfold elementChildren; rw [hnil]; rfl
    have hdtnil : doctypeChildren s₁.tree parent = [] := by
      unfold doctypeChildren; rw [hnil]; rfl
    split at hr
    · simp at hr
    · next s₂ hins =>
      have h₂ : DocumentTreesValid s₂.tree := by
        revert hins
        split
        · intro hins; rw [← Except.ok.inj hins]; exact h₁
        · next _ _ m =>
          intro hins
          refine documentTreesValid_insert_of_seqOk hwf₁ h₁ ?_ (by simpa using hins)
          intro nd hnd
          obtain ⟨nd₀, hnd₀, hkd⟩ := kindPreserving_get? hkp hnd
          obtain ⟨g1, g2⟩ := hok m rfl nd₀ hnd₀
          have hkind : ∀ x, kindOf s₁.tree x = kindOf s.tree x := hkp
          -- 入れる node の列は `removeEach` で縮むだけである。
          have hsl : ((if nd.kind = NodeKind.documentFragment then nd.children
                else [m])).Sublist
              (if nd₀.kind = NodeKind.documentFragment then nd₀.children else [m]) := by
            by_cases hk : nd.kind = NodeKind.documentFragment
            · rw [if_pos hk, if_pos (by rw [hkd]; exact hk)]
              have hs := (removeEach_childrenOf_sub _ hwf hre m).1
              rw [childrenOf_eq hnd, childrenOf_eq hnd₀] at hs
              exact hs
            · rw [if_neg hk, if_neg (by rw [hkd]; exact hk)]
              exact List.Sublist.refl _
          intro _
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro x hx k hk
            exact g1 x (hsl.subset hx) k (by rw [← hkind x]; exact hk)
          · simp only [hkind]
            exact Nat.le_trans (Nat.add_le_add (hsl.filter _).length_le
              (hsl.filter _).length_le) g2
          · rw [helemnil]
            simp only [hkind, List.length_nil, Nat.zero_add]
            exact Nat.le_trans (Nat.le_trans (hsl.filter _).length_le (Nat.le_add_right _ _)) g2
          · rw [hdtnil]
            simp only [hkind, List.length_nil, Nat.zero_add]
            exact Nat.le_trans (Nat.le_trans (hsl.filter _).length_le (Nat.le_add_left _ _)) g2
          · intro _ _ _ c hc
            exact absurd hc (by simp)
          · intro _ _ _
            exact ⟨fun c hc => absurd hc (by simp), fun _ => helemnil⟩
      rw [← Except.ok.inj hr]
      simpa using h₂

/-! ## replaceData -/

/--
`replaceData` は `data` しか変えないので、木の形に関する妥当性は三層とも保たれる。

`withData` の補題（`Dom/Properties/CharacterData.lean`）がそのまま使える。
-/
theorem structurallyValid_replaceData {s s' : DOMState} {n : NodeId} {offset count : Nat}
    {data : String} (h : StructurallyValid s.tree)
    (hr : replaceData s n offset count data = .ok s') : StructurallyValid s'.tree := by
  obtain ⟨d, hd, _, _, htree, _, _⟩ := replaceData_ok hr
  -- 新しい木の `get?` は、`n` のところだけ `data` が変わった値を返す。
  obtain ⟨nw, hget⟩ : ∃ nw, ∀ m, s'.tree.get? m =
      if m = n then some { d with data := nw } else s.tree.get? m :=
    ⟨spliceData d.data offset (adjustedCount d.length offset count) data,
      fun m => by rw [htree]; exact get?_withData hd _ m⟩
  -- `n` の kind / parent / children は変わらない。
  have hsame : ∀ m dm, s'.tree.get? m = some dm →
      ∃ d₀, s.tree.get? m = some d₀ ∧ dm.kind = d₀.kind ∧ dm.parent = d₀.parent ∧
        dm.children = d₀.children := by
    intro m dm hm
    rw [hget] at hm
    split at hm
    · next he => subst he; cases hm; exact ⟨d, hd, rfl, rfl, rfl⟩
    · exact ⟨dm, hm, rfl, rfl, rfl⟩
  refine ⟨replaceData_preserves_wellformed h.wellFormed hr, ?_, ?_, ?_⟩
  · intro m dm hm hk
    obtain ⟨d₀, hd₀, hkk, hpp, _⟩ := hsame m dm hm
    rw [hpp]; exact h.documentHasNoParent m d₀ hd₀ (by rw [← hkk]; exact hk)
  · intro m dm hm hc
    obtain ⟨d₀, hd₀, hkk, _, hcc⟩ := hsame m dm hm
    rw [hkk]; exact h.childrenOnlyUnderContainers m d₀ hd₀ (by rw [← hcc]; exact hc)
  · intro m dm hm hk p hp pd hpd
    obtain ⟨d₀, hd₀, hkk, hpp, _⟩ := hsame m dm hm
    obtain ⟨pd₀, hpd₀, hkkp, _, _⟩ := hsame p pd hpd
    rw [hkkp]
    exact h.doctypeParentIsDocument m d₀ hd₀ (by rw [← hkk]; exact hk) p
      (by rw [← hpp]; exact hp) pd₀ hpd₀

theorem nodeDocumentsValid_replaceData {s s' : DOMState} {n : NodeId} {offset count : Nat}
    {data : String} (h : NodeDocumentsValid s.tree)
    (hr : replaceData s n offset count data = .ok s') : NodeDocumentsValid s'.tree := by
  obtain ⟨d, hd, _, _, htree, _, _⟩ := replaceData_ok hr
  have hget := get?_withData (t := s.tree) (n := n) (d := d) hd
    (spliceData d.data offset (adjustedCount d.length offset count) data)
  have hown : ∀ m, ownerDocumentOf s'.tree m = ownerDocumentOf s.tree m := by
    intro m
    rw [htree]
    simp only [ownerDocumentOf, hget]
    split
    · next he => rw [he, hd]; rfl
    · rfl
  refine ⟨?_, ?_⟩
  · intro m dm hm hk
    rw [htree, hget] at hm
    split at hm
    · next he => subst he; cases hm; exact h.documentIsOwnNodeDocument m d hd hk
    · exact h.documentIsOwnNodeDocument m dm hm hk
  · intro c p hp
    rw [hown, hown]
    refine h.treeEdgePreservesNodeDocument c p ?_
    rw [htree, parentOf_withData hd] at hp
    exact hp

theorem documentTreesValid_replaceData {s s' : DOMState} {n : NodeId} {offset count : Nat}
    {data : String} (h : DocumentTreesValid s.tree)
    (hr : replaceData s n offset count data = .ok s') : DocumentTreesValid s'.tree := by
  obtain ⟨d, hd, _, _, htree, _, _⟩ := replaceData_ok hr
  refine documentTreesValid_of_sameShape ?_ ?_ h
  · intro m; rw [htree]; exact kindPreserving_withData hd _ m
  · intro m; rw [htree]; exact childrenOf_withData hd _ m

end Dom
