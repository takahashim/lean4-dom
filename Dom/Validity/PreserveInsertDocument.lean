import Dom.Validity.PreserveInsert

/-!
# `insert` が Document の children 制約を保つこと

`InsertSeqOk`（入れる node の列が Document の制約を壊さないこと）を経由する。
-/

namespace Dom

/-! ## insert が Document の children 制約を保つこと -/

/-- 除外リストに全部入っているなら、その list は空である。 -/
theorem eq_nil_of_forall_mem_nil {α : Type _} {l : List α} (h : ∀ e ∈ l, e ∈ ([] : List α)) :
    l = [] := by
  cases hl : l with
  | nil => rfl
  | cons y r => exact absurd (h y (by rw [hl]; simp)) (by simp)

/--
Document に入れる node の列は、Text を含まず、
element と doctype を合わせて高々一つしか含まない。

`insert` も `replace all` も、Document の children 制約に効くのはこの二つである。
-/
theorem insertNodes_textAndCount {t : Tree} {node parent : NodeId} {child : Option NodeId}
    {excl : List NodeId} {pd nd : NodeData} (hsv : StructurallyValid t)
    (hpd : t.get? parent = some pd) (hnd : t.get? node = some nd)
    (hpk : pd.kind = NodeKind.document)
    (hv : ensurePreInsertionValidity t node parent child excl = .ok ()) :
    (∀ m ∈ (if nd.kind = NodeKind.documentFragment then nd.children else [node]),
      ∀ k, kindOf t m = some k → k.isText = false) ∧
    (((if nd.kind = NodeKind.documentFragment then nd.children else [node]).filter fun m =>
        kindOf t m == some NodeKind.element).length +
      ((if nd.kind = NodeKind.documentFragment then nd.children else [node]).filter fun m =>
        kindOf t m == some NodeKind.documentType).length ≤ 1) := by
  obtain ⟨f1, f2, _, _⟩ := ensurePreInsertionValidity_documentFacts hpd hnd hpk hv
  by_cases hfrag : nd.kind = NodeKind.documentFragment
  · rw [if_pos hfrag]
    obtain ⟨hlen, htx⟩ := f2 hfrag
    have hchn : childrenOf t node = nd.children := childrenOf_eq hnd
    have hnodt : ∀ m ∈ nd.children, (kindOf t m == some NodeKind.documentType) = false := by
      intro m hm
      have hne := child_not_doctype hsv hnd (by rw [hfrag]; simp) hm
      cases hmd : t.get? m with
      | none => simp [kindOf_eq, hmd]
      | some md => simp [kindOf_eq, hmd, hne md hmd]
    refine ⟨?_, ?_⟩
    · intro m hm k hk
      have hnot : m ∉ textChildren t node := by rw [htx]; simp
      unfold textChildren at hnot
      rw [hchn] at hnot
      cases hik : k.isText with
      | false => rfl
      | true => exact absurd (List.mem_filter.mpr ⟨hm, by rw [hk]; exact hik⟩) hnot
    · rw [filter_eq_nil_of_all_false _ _ hnodt]
      simp only [List.length_nil, Nat.add_zero]
      have helemfilter : (nd.children.filter fun m =>
          kindOf t m == some NodeKind.element) = elementChildren t node := by
        unfold elementChildren
        rw [hchn]
      rw [helemfilter]
      exact hlen
  · rw [if_neg hfrag]
    have hkn : kindOf t node = some nd.kind := by rw [kindOf_eq, hnd]; rfl
    refine ⟨?_, ?_⟩
    · intro m hm k hk
      rcases List.mem_singleton.mp hm with rfl
      rw [hkn] at hk
      obtain rfl : k = nd.kind := (Option.some.inj hk).symm
      exact f1
    · by_cases hk : nd.kind = NodeKind.element
      · have hb : (nd.kind == NodeKind.documentType) = false := by rw [hk]; rfl
        have hb' : (nd.kind == NodeKind.element) = true := by rw [hk]; rfl
        simp [List.filter, hkn, hb, hb']
      · have hb : (nd.kind == NodeKind.element) = false := by simpa using hk
        by_cases hk2 : nd.kind = NodeKind.documentType
        · have hb2 : (nd.kind == NodeKind.documentType) = true := by rw [hk2]; rfl
          simp [List.filter, hkn, hb, hb2]
        · have hb2 : (nd.kind == NodeKind.documentType) = false := by simpa using hk2
          simp [List.filter, hkn, hb, hb2]

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
  have hkind : ∀ m, kindOf t' m = kindOf t m := (shapePreserving_insertAt hi).kind
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
          insertSeqOk_of_removeAll (shapePreserving_adopt ha).kind (adopt_childrenOf hwf ha) hok
        have hwf₂ : WellFormed s₂.tree := insertAt_preserves_wellformed hwf₁ hins'
        have h₂ : DocumentTreesValid s₂.tree := by
          refine ⟨fun d dd hd hk => ?_⟩
          obtain ⟨dd₁, hd₁, hkdd⟩ := shapePreserving_get? (shapePreserving_insertAt hins') hd
          have hk₁ : dd₁.kind = NodeKind.document := by rw [hkdd]; exact hk
          have hok' : DocumentChildrenOk s₁.tree d := h₁.documentChildren d dd₁ hd₁ hk₁
          by_cases hne : d = parent
          · subst hne
            have hdockind : kindOf s₁.tree d = some NodeKind.document := by
              simp [kindOf_eq, hd₁, hk₁]
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
          (hdoc.map ((shapePreserving_adopt ha).trans (shapePreserving_insertAt hins'))) hok₂ hi



/-- `remove` は `InsertSeqOk` を壊さない。 -/
theorem insertSeqOk_remove {s s' : DOMState} {n : NodeId} {b : Bool} {parent : NodeId}
    {child : Option NodeId} {ns : List NodeId} (hwf : WellFormed s.tree)
    (hr : remove s n b = .ok s') (h : InsertSeqOk s.tree parent child ns) :
    InsertSeqOk s'.tree parent child ns :=
  insertSeqOk_of_removeAll (shapePreserving_remove hr).kind
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
  obtain ⟨sx, hx, hrec⟩ := insertNodesAt_cases hi
  have htree : s'.tree = sx.tree := by
    rcases hrec with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · rfl
    · simp
  rw [htree]
  obtain ⟨pd, hpd, hx⟩ := insertEachAt_cases hx
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
  obtain ⟨nd, hnd, hcase⟩ := insert_cases hi
  rcases hcase with ⟨_, _, hsx⟩ | ⟨hk, _, s₁, hre, hins⟩ | ⟨hnfrag, hins⟩
  · rw [hsx]; exact h
  · have hok' : InsertSeqOk s.tree parent child nd.children := by
      have hx := hok nd hnd
      rwa [if_pos hk] at hx
    have hwf₁ : WellFormed s₁.tree := removeEach_preserves_wellformed _ hwf hre
    have h₁ : DocumentTreesValid s₁.tree := documentTreesValid_removeEach _ hwf h hre
    have hok₁ : InsertSeqOk s₁.tree parent child nd.children :=
      insertSeqOk_removeEach _ hwf hre hok'
    exact documentTreesValid_insertNodesAt (s := queueTreeMutationRecord s₁ node []
      nd.children none none) (by simpa using hwf₁) (by simpa using h₁)
      (by simpa using hok₁) hins
  · have hok' : InsertSeqOk s.tree parent child [node] := by
      have hx := hok nd hnd
      rwa [if_neg hnfrag] at hx
    exact documentTreesValid_insertNodesAt hwf h hok' hins

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
    | none => rw [kindOf_eq, hpd] at hkp; simp at hkp
    | some pd =>
      refine ⟨pd, rfl, ?_⟩
      rw [kindOf_eq, hpd] at hkp
      simpa using hkp
  by_cases hfragkind : nd.kind = NodeKind.documentFragment
  · rw [if_pos hfragkind]
    -- fragment の children に doctype は無い
    have hnodt : ∀ m ∈ nd.children,
        (kindOf s.tree m == some NodeKind.documentType) = false := by
      intro m hm
      have hne := child_not_doctype hsv hnd (by rw [hfragkind]; simp) hm
      cases hmd : s.tree.get? m with
      | none => simp [kindOf_eq, hmd]
      | some md => simp [kindOf_eq, hmd, hne md hmd]
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
    have hkn : kindOf s.tree node = some nd.kind := by rw [kindOf_eq, hnd]; rfl
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

end Dom
