import Dom.Validity.PreserveReplace

/-!
# `replace` が Document の children 制約を保つこと
-/

namespace Dom

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
    rw [hdocparent, kindOf_eq, hpd] at hk
    simpa using hk.symm
  obtain ⟨f1, f2, f3, f4⟩ := ensurePreInsertionValidity_documentFacts hpd hnd hpk hv
  have hkd : nd₂.kind = nd.kind := by
    have hk := hkind node
    rw [kindOf_eq, kindOf_eq, hnd₂, hnd] at hk
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
    rw [doctypeFollows_of_splitAt? hsplit]
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
    | none => simp [kindOf_eq, hmd]
    | some md => simp [kindOf_eq, hmd, hne md hmd]
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
      rw [kindOf_eq, hnd] at hxk
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
      rw [kindOf_eq, hnd] at hxk
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
    | none => rw [kindOf_eq, hq] at hdocparent; simp at hdocparent
    | some q => exact ⟨q, rfl⟩
  have hpk₂ : pd₂.kind = NodeKind.document := by
    rw [kindOf_eq, hpd₂] at hdocparent
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
      rw [kindOf_eq, hnd] at hk'
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
      rw [doctypeFollows_of_splitAt? hsplit₂, Bool.eq_false_iff]
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
  obtain ⟨pd, s₁, s₂, s₃, hv, hpd, ha, hrm, hi, hstate⟩ := replace_cases hr
  have hwf₁ := adopt_preserves_wellformed hwf (isDocument_ownerDocument hwf hpd) ha
  have h₁ : DocumentTreesValid s₁.tree := documentTreesValid_adopt hwf h ha
  have hkp₁ : ShapePreserving s.tree s₁.tree := shapePreserving_adopt ha
  have hch₁ : ∀ p, childrenOf s₁.tree p =
      ListUtil.removeAll (childrenOf s.tree p) node := adopt_childrenOf hwf ha
  have hstep : DocumentTreesValid s₂.tree ∧ ShapePreserving s₁.tree s₂.tree ∧
      WellFormed s₂.tree ∧
      (∀ p, childrenOf s₂.tree p = ListUtil.removeAll (childrenOf s₁.tree p) child) := by
    rcases hrm with ⟨hnone, rfl⟩ | ⟨_, hrm'⟩
    · refine ⟨h₁, ShapePreserving.refl _, hwf₁, fun p => ?_⟩
      rw [ListUtil.removeAll_eq_self]
      intro hmem
      have hpar := parentOf_of_mem_childrenOf hwf₁ hmem
      rw [hnone] at hpar
      simp at hpar
    · exact ⟨documentTreesValid_remove hwf₁ h₁ hrm', shapePreserving_remove hrm',
        remove_preserves_wellformed hwf₁ hrm',
        detach_childrenOf_removeAll hwf₁ (remove_ok hrm').2⟩
  obtain ⟨h₂, hkp₂, hwf₂, hch₂⟩ := hstep
  have hkind : ∀ m, kindOf s₂.tree m = kindOf s.tree m := (hkp₁.trans hkp₂).kind
  have hchall : ∀ p, childrenOf s₂.tree p =
      ListUtil.removeAll (ListUtil.removeAll (childrenOf s.tree p) node) child := by
    intro p
    rw [hch₂ p, hch₁ p]
  have h₃ : DocumentTreesValid s₃.tree := by
    refine documentTreesValid_insert_of_seqOk hwf₂ h₂ ?_ hi
    intro nd₂ hnd₂
    obtain ⟨nd, hnd, _⟩ := shapePreserving_get? (hkp₁.trans hkp₂) hnd₂
    exact insertSeqOk_of_replace hwf hsv hpd hnd hv h₂ hkind hchall hnd₂
  rw [hstate]
  simpa using h₃

end Dom
