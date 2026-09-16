import Dom.Validity.PreserveRemove

/-!
# `insertAt` が Document の children 制約に与える効果

primitive の側。`insert` / `replace` / `move` がここを共有する。
-/

namespace Dom

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
  obtain ⟨u, v, hs⟩ := ListUtil.exists_splitAt?_of_mem hmemB
  have hnotA' : e ∉ A ++ [node] := by
    intro hm
    rcases List.mem_append.mp hm with h | h
    · exact hnotA h
    · exact hne (by simpa using h)
  have hrw : A ++ node :: B = (A ++ [node]) ++ B := by simp
  rw [doctypeFollows_of_splitAt? (t := t')
      (by rw [hAB', hrw]; exact ListUtil.splitAt?_append_right hnotA' hs),
    doctypeFollows_of_splitAt? (by rw [hAB]; exact ListUtil.splitAt?_append_right hnotA hs)]
  simp only [hkind]

/--
挿入する node が doctype でなければ、
他の node から見た「後ろに doctype があるか」は変わらない。
-/
theorem doctypeFollows_insertAt_of_ne {t t' : Tree} {parent node : NodeId}
    {child : Option NodeId} (hwf : WellFormed t) (hi : insertAt t parent node child = .ok t')
    (hdoctype : (kindOf t node == some NodeKind.documentType) = false) {e : NodeId}
    (hne : e ≠ node) : doctypeFollows t' parent e = doctypeFollows t parent e := by
  have hkind : ∀ m, kindOf t' m = kindOf t m := (shapePreserving_insertAt hi).kind
  obtain ⟨A, B, hAB, hAB'⟩ := insertAt_children_split_general hwf hi
  have hnot : node ∉ childrenOf t parent := insertAt_node_not_mem hwf hi
  have hnotA : node ∉ A := fun hm => hnot (by rw [hAB]; exact List.mem_append_left _ hm)
  by_cases hmem : e ∈ A
  · obtain ⟨u, v, hs⟩ := ListUtil.exists_splitAt?_of_mem hmem
    rw [doctypeFollows_of_splitAt? (t := t')
        (by rw [hAB']; exact ListUtil.splitAt?_append_left hs (node :: B)),
      doctypeFollows_of_splitAt? (by rw [hAB]; exact ListUtil.splitAt?_append_left hs B)]
    simp [List.any_append, hdoctype, hkind]
  · by_cases hmemB : e ∈ B
    · obtain ⟨u, v, hs⟩ := ListUtil.exists_splitAt?_of_mem hmemB
      have hnotA' : e ∉ A ++ [node] := by
        intro hm
        rcases List.mem_append.mp hm with h | h
        · exact hmem h
        · exact hne (by simpa using h)
      have hrw : A ++ node :: B = (A ++ [node]) ++ B := by simp
      rw [doctypeFollows_of_splitAt? (t := t')
          (by rw [hAB', hrw]; exact ListUtil.splitAt?_append_right hnotA' hs),
        doctypeFollows_of_splitAt? (by rw [hAB]; exact ListUtil.splitAt?_append_right hmem hs)]
      simp only [hkind]
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
      rw [doctypeFollows_of_splitAt?_none
          (by rw [hAB']; exact ListUtil.splitAt?_eq_none_of_not_mem hnotAB'),
        doctypeFollows_of_splitAt?_none
          (by rw [hAB]; exact ListUtil.splitAt?_eq_none_of_not_mem hnotAB)]

/-- 挿入した node 自身の後ろに doctype が無いことは、validity 検査から従う。 -/
theorem doctypeFollows_insertAt_self {t t' : Tree} {parent node : NodeId}
    {child : Option NodeId} (hwf : WellFormed t) (hi : insertAt t parent node child = .ok t')
    (hafter : ∀ c, child = some c →
      (kindOf t c == some NodeKind.documentType) = false ∧ doctypeFollows t parent c = false) :
    doctypeFollows t' parent node = false := by
  have hkind : ∀ m, kindOf t' m = kindOf t m := (shapePreserving_insertAt hi).kind
  have hnot : node ∉ childrenOf t parent := insertAt_node_not_mem hwf hi
  cases child with
  | none =>
    have hch : childrenOf t' parent = childrenOf t parent ++ node :: [] := by
      rw [insertAt_childrenOf hwf hi, ListUtil.insertBefore_none]
    rw [doctypeFollows_of_splitAt?
      (by rw [hch]; exact ListUtil.splitAt?_append_cons_self hnot [])]
    simp
  | some c =>
    obtain ⟨s₁, s₂, h₁, h₂⟩ := insertAt_children_split hwf hi
    have hnots₁ : node ∉ s₁ := fun hm => hnot (by rw [h₁]; exact List.mem_append_left _ hm)
    have hrw : s₁ ++ node :: c :: s₂ = s₁ ++ node :: (c :: s₂) := rfl
    rw [doctypeFollows_of_splitAt?
      (by rw [h₂, hrw]; exact ListUtil.splitAt?_append_cons_self hnots₁ (c :: s₂))]
    obtain ⟨hc, hfol⟩ := hafter c rfl
    have hs : ListUtil.splitAt? (childrenOf t parent) c = some (s₁, s₂) :=
      splitAt?_childrenOf_of_split hwf h₁
    rw [doctypeFollows_of_splitAt? hs] at hfol
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
  have hkind : ∀ m, kindOf t' m = kindOf t m := (shapePreserving_insertAt hi).kind
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

end Dom
