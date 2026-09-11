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
    ∃ a, childrenOf t' p = ListUtil.removeAll (childrenOf t p) a := by
  cases hp : parentOf t n with
  | none =>
    exact ⟨n, by
      rw [detach_of_no_parent hp (by
        rcases detach_ok_cases hd with ⟨d, hdd, _, _⟩ | ⟨d, _, _, hdd, _, _, _⟩ <;>
          simp [hdd])] at hd
      rw [← Except.ok.inj hd, ListUtil.removeAll_eq_self]
      intro hmem
      exact absurd (parentOf_of_mem_childrenOf hwf hmem) (by rw [hp]; simp)⟩
  | some q =>
    by_cases hdp : p = q
    · subst hdp
      exact ⟨n, detach_childrenOf hwf hp hd⟩
    · exact ⟨n, by
        rw [detach_childrenOf_ne hp hd hdp, ListUtil.removeAll_eq_self]
        intro hmem
        have := parentOf_of_mem_childrenOf hwf hmem
        rw [hp] at this
        exact hdp (Option.some.inj this).symm⟩

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
  obtain ⟨a, hch⟩ := detach_childrenOf_removeAll hwf hd doc
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
  obtain ⟨a, hch⟩ := detach_childrenOf_removeAll hwf hd p
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
      obtain ⟨a, ha⟩ := detach_childrenOf_removeAll hwf hd doc
      exact doctypeFollows_of_removeAll hkind ha hafter.2
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
theorem structurallyValid_insert {s s' : DOMState} {node parent : NodeId}
    {child : Option NodeId} {b : Bool} (h : StructurallyValid s.tree)
    (hv : ensurePreInsertionValidity s.tree node parent child [] = .ok ())
    (hi : insert s node parent child b = .ok s') : StructurallyValid s'.tree := by
  have hpk := ensurePreInsertionValidity_parentCanHaveChildren hv
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
        exact ensurePreInsertionValidity_nodeNotDocument hv
      · intro m hm
        rcases List.mem_singleton.mp hm with rfl
        exact ensurePreInsertionValidity_doctypeParentIsDocument hv

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
theorem nodeDocumentsValid_insert {s s' : DOMState} {node parent : NodeId}
    {child : Option NodeId} {b : Bool}
    (hs : StructurallyValid s.tree) (h : NodeDocumentsValid s.tree)
    (hv : ensurePreInsertionValidity s.tree node parent child [] = .ok ())
    (hi : insert s node parent child b = .ok s') : NodeDocumentsValid s'.tree := by
  have hpk := ensurePreInsertionValidity_parentCanHaveChildren hv
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
        exact ensurePreInsertionValidity_nodeNotDocument hv
      · intro m hm
        rcases List.mem_singleton.mp hm with rfl
        exact ensurePreInsertionValidity_doctypeParentIsDocument hv

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
