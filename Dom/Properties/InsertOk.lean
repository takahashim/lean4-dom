import Dom.Properties.CloneOk

/-!
# `insert` の成功条件

`Dom/Properties/Contract.lean` の success に当たる部分のうち、挿入側である。

`remove` は `remove_succeeds_iff` で両側が言えている。挿入側は
`append_fresh_isOk`（作ったばかりの node を一つ append する場合）しか無く、
**DocumentFragment の children をまとめて入れる場合**が残っていた。

落ちうるのは `insertEach` の各段の `adopt` と `insertAt` である。回し続けられる条件を
`Insertable` に束ねて、各段でそれが保たれることを示す。
-/

namespace Dom

/--
`insertEach` を回し続けられる条件。

`insertAt` の四つの前提（parent が在る／node が在って parent を持たない／
cycle が無い／`child` が parent の子）を、**列の全要素について**述べたものである。
`nodup` が要るのは、同じ node を二度入れようとすると二度目に parent を持っている
からである。
-/
structure Insertable (t : Tree) (parent : NodeId) (child : Option NodeId)
    (ns : List NodeId) : Prop where
  parentExists : ∃ pd, t.get? parent = some pd
  /-- reference child は `parent` の子である。`insertAt` の step 4。 -/
  childParent : ∀ c, child = some c → parentOf t c = some parent
  /--
  reference child は入れる列に入っていない。

  入っていると、その node を adopt した拍子に `parent` の子でなくなり、
  `insertAt` の step 4 が落ちる。`preInsert` は step 2-3 でこの場合を避ける。
  -/
  childNotMem : ∀ c, child = some c → c ∉ ns
  present : ∀ n ∈ ns, ∃ nd, t.get? n = some nd
  notAncestor : ∀ n ∈ ns, ¬ InclusiveAncestor t n parent
  nodup : ns.Nodup

namespace Insertable

/-- 列の先頭を落としても条件は残る。 -/
theorem tail {t : Tree} {parent : NodeId} {child : Option NodeId} {n : NodeId}
    {ns : List NodeId} (h : Insertable t parent child (n :: ns)) :
    Insertable t parent child ns where
  parentExists := h.parentExists
  childParent := h.childParent
  childNotMem := fun c hc hm => h.childNotMem c hc (by simp [hm])
  present := fun m hm => h.present m (by simp [hm])
  notAncestor := fun m hm => h.notAncestor m (by simp [hm])
  nodup := (List.nodup_cons.mp h.nodup).2

/-- 列の要素は `parent` ではない（自分自身は inclusive ancestor だから）。 -/
theorem ne_parent {t : Tree} {parent : NodeId} {child : Option NodeId} {ns : List NodeId}
    (h : Insertable t parent child ns) {n : NodeId} (hn : n ∈ ns) : n ≠ parent := by
  intro he
  exact h.notAncestor n hn (Or.inl he)

end Insertable

/-! ## `setOwnerDocument`（adopt の後半）は条件を保つ -/

theorem insertable_setOwnerDocument {t : Tree} {parent n doc : NodeId} {child : Option NodeId}
    {ns : List NodeId} (h : Insertable t parent child ns) :
    Insertable (setOwnerDocument t n doc) parent child ns where
  parentExists := by
    obtain ⟨pd, hpd⟩ := h.parentExists
    rw [get?_setOwnerDocument, hpd]
    split <;> exact ⟨_, rfl⟩
  childParent := fun c hc => by rw [parentOf_setOwnerDocument]; exact h.childParent c hc
  childNotMem := h.childNotMem
  present := fun m hm => by
    obtain ⟨nd, hnd⟩ := h.present m hm
    rw [get?_setOwnerDocument, hnd]
    split <;> exact ⟨_, rfl⟩
  notAncestor := fun m hm hc => by
    refine h.notAncestor m hm ?_
    rcases hc with he | ha
    · exact Or.inl he
    · exact Or.inr (ancestor_setOwnerDocument.mp ha)
  nodup := h.nodup

/-! ## `insertAt` は残りの列について条件を保つ -/

/-- `insertAt` が動かす parent は入れた node のものだけである。 -/
theorem insertAt_parentOf_ne {t t' : Tree} {parent node : NodeId} {child : Option NodeId}
    (h : insertAt t parent node child = .ok t') {m : NodeId} (hm : m ≠ node) :
    parentOf t' m = parentOf t m := by
  obtain ⟨pd, nd, hpd, hnd, -, -, -, rfl⟩ := insertAt_ok_cases h
  by_cases hp : m = parent
  · subst hp
    have hget : (insertAtIn t m node child pd nd).get? m =
        some { pd with children := Dom.ListUtil.insertBefore pd.children child node } := by
      unfold insertAtIn
      show ((t.nodes.insert m _).insert node _).get? m = _
      rw [NodeStore.get?_insert_ne _ (fun he => hm he.symm), NodeStore.get?_insert_self]
    rw [parentOf_of_get? hget, parentOf_of_get? hpd]
  · rw [parentOf_eq, parentOf_eq, insertAt_frame h hm hp]

/-- 入れた node を通らない祖先の鎖は、入れる前の木にもある。 -/
theorem ancestor_of_insertAt {t t' : Tree} {parent node : NodeId} {child : Option NodeId}
    (hi : insertAt t parent node child = .ok t') {a b : NodeId} (ha : Ancestor t' a b) :
    b ≠ node → ¬ Ancestor t' node b → Ancestor t a b := by
  induction ha with
  | step hp =>
    intro hb _
    exact Ancestor.step (by rw [← insertAt_parentOf_ne hi hb]; exact hp)
  | trans hp _ ih =>
    intro hb hnb
    refine Ancestor.trans (by rw [← insertAt_parentOf_ne hi hb]; exact hp) (ih ?_ ?_)
    · intro he; exact hnb (Ancestor.step (he ▸ hp))
    · intro hq; exact hnb (Ancestor.trans hp hq)

/-- **`insertAt` は、入れ終わった後の列について `Insertable` を保つ。** -/
theorem insertable_insertAt {t t' : Tree} {parent n : NodeId} {child : Option NodeId}
    {ns : List NodeId} (hwf : WellFormed t)
    (hi : insertAt t parent n child = .ok t')
    (h : Insertable t parent child (n :: ns)) : Insertable t' parent child ns := by
  have hwf' : WellFormed t' := insertAt_preserves_wellformed hwf hi
  have hnn : n ∉ ns := (List.nodup_cons.mp h.nodup).1
  have hpn : parent ≠ n := fun he => h.ne_parent (by simp) he.symm
  have hnotanc : ¬ Ancestor t' n parent := by
    intro hq
    exact hwf'.acyclic n (Ancestor.trans (insertAt_parentOf hi) hq)
  refine ⟨?_, ?_, ?_, ?_, ?_, (List.nodup_cons.mp h.nodup).2⟩
  · obtain ⟨pd, hpd⟩ := h.parentExists
    exact exists_get?_of_kindPreserving (shapePreserving_insertAt hi) hpd
  · intro c hc
    rw [insertAt_parentOf_ne hi (fun he => h.childNotMem c hc (by rw [he]; simp))]
    exact h.childParent c hc
  · exact fun c hc hm => h.childNotMem c hc (by simp [hm])
  · intro m hm
    obtain ⟨nd, hnd⟩ := h.present m (by simp [hm])
    exact exists_get?_of_kindPreserving (shapePreserving_insertAt hi) hnd
  · intro m hm hc
    refine h.notAncestor m (by simp [hm]) ?_
    rcases hc with he | ha
    · exact Or.inl he
    · exact Or.inr (ancestor_of_insertAt hi ha (fun he => hpn he) hnotanc)

/-! ## `remove`（adopt の step 2）は条件を保つ -/

/-- `detach` は祖先関係を増やさない。外れるのは `n` の親への辺だけである。 -/
theorem ancestor_of_detach {t t' : Tree} {n : NodeId} (hd : detach t n = .ok t')
    {a x : NodeId} (h : Ancestor t' a x) : Ancestor t a x := by
  have key : ∀ m y, parentOf t' m = some y → parentOf t m = some y := by
    intro m y hm
    rw [parentOf_detach hd] at hm
    by_cases he : m = n
    · rw [if_pos he] at hm; exact absurd hm (by simp)
    · rw [if_neg he] at hm; exact hm
  induction h with
  | step hp => exact Ancestor.step (key _ _ hp)
  | trans hp _ ih => exact Ancestor.trans (key _ _ hp) ih

/-- **`remove` は入れる列についての条件を保つ。** 動くのは外した node の parent だけである。 -/
theorem insertable_remove {s s₁ : DOMState} {parent n : NodeId} {child : Option NodeId}
    {ns : List NodeId} {b : Bool} (hr : remove s n b = .ok s₁)
    (h : Insertable s.tree parent child (n :: ns)) :
    Insertable s₁.tree parent child (n :: ns) := by
  have hd : detach s.tree n = .ok s₁.tree := (remove_ok hr).2
  have hsp : ShapePreserving s.tree s₁.tree := shapePreserving_remove hr
  refine ⟨?_, ?_, h.childNotMem, ?_, ?_, h.nodup⟩
  · obtain ⟨pd, hpd⟩ := h.parentExists
    exact exists_get?_of_kindPreserving hsp hpd
  · intro c hc
    rw [parentOf_detach hd, if_neg (fun he => h.childNotMem c hc (by rw [he]; simp))]
    exact h.childParent c hc
  · intro m hm
    obtain ⟨nd, hnd⟩ := h.present m hm
    exact exists_get?_of_kindPreserving hsp hnd
  · intro m hm hc
    refine h.notAncestor m hm ?_
    rcases hc with he | ha
    · exact Or.inl he
    · exact Or.inr (ancestor_of_detach hd ha)

/-! ## `adopt` は条件を保ち、node を外す -/

/-- **`adopt` の後、node は parent を持たない。** -/
theorem adopt_parentOf_eq_none {s s' : DOMState} {node doc : NodeId}
    (h : adopt s node doc = .ok s') : parentOf s'.tree node = none := by
  obtain ⟨s₁, hstep, hfinal⟩ := adopt_ok_cases h
  have h₁ : parentOf s₁.tree node = none := by
    rcases hstep with ⟨hp, rfl⟩ | hr
    · exact hp
    · exact remove_parentOf hr
  rcases hfinal with rfl | rfl
  · exact h₁
  · rw [DOMState.withTree_tree, parentOf_setOwnerDocument]; exact h₁

/-- **`adopt` は入れる列についての条件を保つ。** -/
theorem insertable_adopt {s s' : DOMState} {parent n doc : NodeId} {child : Option NodeId}
    {ns : List NodeId} (h : adopt s n doc = .ok s')
    (hi : Insertable s.tree parent child (n :: ns)) :
    Insertable s'.tree parent child (n :: ns) := by
  obtain ⟨s₁, hstep, hfinal⟩ := adopt_ok_cases h
  have h₁ : Insertable s₁.tree parent child (n :: ns) := by
    rcases hstep with ⟨-, rfl⟩ | hr
    · exact hi
    · exact insertable_remove hr hi
  rcases hfinal with rfl | rfl
  · exact h₁
  · rw [DOMState.withTree_tree]
    exact insertable_setOwnerDocument h₁

/-! ## `insertEach` の成功 -/

/-- `IsDocument` は shape だけで決まるので、形を保つ変更を跨いで残る。 -/
theorem isDocument_of_shapePreserving {t t' : Tree} {doc : NodeId}
    (hk : ShapePreserving t t') (h : IsDocument t doc) : IsDocument t' doc := by
  obtain ⟨dd, hdd, hkd⟩ := h
  obtain ⟨dd', hdd'⟩ := exists_get?_of_kindPreserving hk hdd
  refine ⟨dd', hdd', ?_⟩
  have hs := hk doc
  rw [hdd, hdd'] at hs
  simp only [Option.map_some, Option.some.injEq] at hs
  have : dd'.kind = dd.kind := by
    rw [← NodeData.shape_kind dd', hs, NodeData.shape_kind]
  rw [this]; exact hkd

/--
**`insertEach` は `Insertable` なら成功する。**

各段で落ちうるのは `adopt` と `insertAt` である。`adopt` は node が parent を
持たないので `remove` を呼ばず、`insertAt` の四つの前提は `Insertable` がそのまま持つ。
残りの列について `Insertable` が保たれることは `insertable_insertAt` である。
-/
theorem insertEach_isOk : ∀ (ns : List NodeId) {s : DOMState} {parent : NodeId}
    {child : Option NodeId} {doc : NodeId}, WellFormed s.tree → IsDocument s.tree doc →
    Insertable s.tree parent child ns →
    ∃ s', insertEach s parent child doc ns = .ok s' := by
  intro ns
  induction ns with
  | nil => intro s _ _ _ _ _ _; exact ⟨s, rfl⟩
  | cons n ns ih =>
    intro s parent child doc hwf hdoc h
    -- step 7.1：adopt は成功する（node に parent があれば外してから node document を付け替える）
    obtain ⟨nd, hnd⟩ := h.present n (by simp)
    obtain ⟨s₁, hadopt⟩ := adopt_isOk (doc := doc) hwf hnd
    have h₁ : Insertable s₁.tree parent child (n :: ns) := insertable_adopt hadopt h
    have hwf₁ : WellFormed s₁.tree := adopt_preserves_wellformed hwf hdoc hadopt
    have hdoc₁ : IsDocument s₁.tree doc :=
      isDocument_of_shapePreserving (shapePreserving_adopt hadopt) hdoc
    -- step 7.2：insertAt の四つの前提
    obtain ⟨pd₁, hpd₁⟩ := h₁.parentExists
    obtain ⟨nd₁, hnd₁⟩ := h₁.present n (by simp)
    have hnp₁ : nd₁.parent = none := by
      have hq := adopt_parentOf_eq_none hadopt
      rw [parentOf_of_get? hnd₁] at hq
      exact hq
    have hanc₁ : isInclusiveAncestorOf s₁.tree n parent = false := by
      cases hb : isInclusiveAncestorOf s₁.tree n parent with
      | false => rfl
      | true =>
        exact absurd ((isInclusiveAncestorOf_iff hwf₁ n parent).mp hb)
          (h₁.notAncestor n (by simp))
    have hchild₁ : ∀ c, child = some c → c ∈ pd₁.children := by
      intro c hc
      rw [← childrenOf_eq hpd₁]
      exact mem_childrenOf_of_parentOf hwf₁ (h₁.childParent c hc)
    have hins := insertAt_eq_ok hpd₁ hnd₁ hnp₁ hanc₁ hchild₁
    obtain ⟨s₂, hs₂⟩ : ∃ s₂ : DOMState,
        s₂ = s₁.withTree (insertAtIn s₁.tree parent n child pd₁ nd₁) := ⟨_, rfl⟩
    have htree₂ : s₂.tree = insertAtIn s₁.tree parent n child pd₁ nd₁ := by
      rw [hs₂, DOMState.withTree_tree]
    have hmap : s₁.mapTree (fun t => insertAt t parent n child) = .ok s₂ := by
      show (match insertAt s₁.tree parent n child with
        | Except.error e => Except.error e
        | Except.ok t => Except.ok (s₁.withTree t)) = _
      rw [hins, hs₂]
    -- step 7.3：残りの列でも条件は保たれる
    have h₂ : Insertable s₂.tree parent child ns := by
      rw [htree₂]
      exact insertable_insertAt hwf₁ hins h₁
    have hwf₂ : WellFormed s₂.tree := by
      rw [htree₂]; exact insertAt_preserves_wellformed hwf₁ hins
    have hdoc₂ : IsDocument s₂.tree doc :=
      isDocument_of_shapePreserving (by rw [htree₂]; exact shapePreserving_insertAt hins) hdoc₁
    obtain ⟨o, ho⟩ := ih hwf₂ hdoc₂ h₂
    refine ⟨o, ?_⟩
    rw [insertEach, hadopt]
    simp only [hmap]
    exact ho

/-! ## step 4：fragment の children を外す -/

/-- **同じ parent を持つ node の列は、順に外せる。** -/
theorem removeEach_isOk : ∀ (ns : List NodeId) {s : DOMState} {b : Bool} {p : NodeId},
    WellFormed s.tree → (∀ n ∈ ns, parentOf s.tree n = some p) → ns.Nodup →
    ∃ s', removeEach s ns b = .ok s' := by
  intro ns
  induction ns with
  | nil => intro s _ _ _ _ _; exact ⟨s, rfl⟩
  | cons n rest ih =>
    intro s b p hwf hp hnd
    obtain ⟨s₁, hr⟩ := (remove_succeeds_iff hwf (n := n) (b := b)).mpr
      (by rw [hp n (by simp)]; rfl)
    have hd : detach s.tree n = .ok s₁.tree := (remove_ok hr).2
    obtain ⟨o, ho⟩ := ih (s := s₁) (b := b) (p := p)
      (remove_preserves_wellformed hwf hr)
      (fun m hm => by
        rw [parentOf_detach hd, if_neg (show ¬ m = n from fun he => (List.nodup_cons.mp hnd).1 (by rw [← he]; exact hm))]
        exact hp m (by simp [hm]))
      (List.nodup_cons.mp hnd).2
    exact ⟨o, by rw [removeEach, hr]; exact ho⟩

/-- `removeEach` は、外す列に入っていない node の parent を動かさない。 -/
theorem parentOf_removeEach_of_not_mem : ∀ (ns : List NodeId) {s s' : DOMState} {b : Bool}
    {m : NodeId}, removeEach s ns b = .ok s' → m ∉ ns → parentOf s'.tree m = parentOf s.tree m := by
  intro ns
  induction ns with
  | nil => intro s s' b m h _; rw [removeEach] at h; rw [← Except.ok.inj h]
  | cons n rest ih =>
    intro s s' b m h hm
    rw [removeEach] at h
    split at h
    · simp at h
    · next s₁ hr =>
      rw [ih h (fun hq => hm (by simp [hq])), parentOf_detach (remove_ok hr).2,
        if_neg (fun he => hm (by simp [he]))]

/-- `removeEach` は祖先関係を増やさない。 -/
theorem ancestor_of_removeEach : ∀ (ns : List NodeId) {s s' : DOMState} {b : Bool},
    removeEach s ns b = .ok s' → ∀ {a x : NodeId}, Ancestor s'.tree a x → Ancestor s.tree a x := by
  intro ns
  induction ns with
  | nil => intro s s' b h a x ha; rw [removeEach] at h; rw [← Except.ok.inj h] at ha; exact ha
  | cons n rest ih =>
    intro s s' b h a x ha
    rw [removeEach] at h
    split at h
    · simp at h
    · next s₁ hr => exact ancestor_of_detach (remove_ok hr).2 (ih h ha)

/-! ## `insert` の成功 -/

/-- **`insertNodesAt` は `Insertable` なら成功する。** -/
theorem insertNodesAt_isOk_of_insertable {s : DOMState} {parent : NodeId}
    {child : Option NodeId} {nodes : List NodeId} {b : Bool} (hwf : WellFormed s.tree)
    (h : Insertable s.tree parent child nodes) :
    ∃ s', insertNodesAt s parent child nodes b = .ok s' := by
  refine insertNodesAt_isOk ?_
  obtain ⟨pd, hpd⟩ := h.parentExists
  have htree : (liveRangeInsertAdjust s parent child nodes.length).tree = s.tree :=
    liveRangeInsertAdjust_tree ..
  rw [insertEachAt_of_get? (show (liveRangeInsertAdjust s parent child nodes.length).tree.get?
      parent = some pd from by rw [htree]; exact hpd)]
  exact insertEach_isOk nodes (by rw [htree]; exact hwf)
    (by rw [htree]; exact isDocument_ownerDocument hwf hpd) (by rw [htree]; exact h)

/--
**`insert` は pre-insertion validity を通っていれば必ず成功する。**

`child` が `node` 自身でないことは別に要る。`preInsert` は step 2-3 の
`preInsertReferenceChild` でその場合を避けている。
-/
theorem insert_isOk_of_validity {s : DOMState} {node parent : NodeId} {child : Option NodeId}
    {b : Bool} (hwf : WellFormed s.tree)
    (hv : ensurePreInsertionValidity s.tree node parent child [] = .ok ())
    (hcn : ∀ c, child = some c → c ≠ node) :
    ∃ s', insert s node parent child b = .ok s' := by
  obtain ⟨⟨pd, hpd⟩, ⟨nd, hnd⟩, hanc, hchild⟩ := ensurePreInsertionValidity_ok hv
  have hnotanc : ¬ InclusiveAncestor s.tree node parent := by
    intro hq
    rw [(isInclusiveAncestorOf_iff hwf node parent).mpr hq] at hanc
    exact Bool.noConfusion hanc
  have hne : node ≠ parent := fun he => hnotanc (Or.inl he)
  unfold insert
  simp only [hnd]
  by_cases hk : nd.kind = NodeKind.documentFragment
  · rw [if_pos (by simp [hk])]
    by_cases hemp : nd.children.isEmpty = true
    · rw [if_pos hemp]; exact ⟨s, rfl⟩
    · rw [if_neg hemp]
      -- step 4：children は `node` を parent に持つので順に外せる
      have hchp : ∀ m ∈ nd.children, parentOf s.tree m = some node := by
        intro m hm
        obtain ⟨md, hmd, hmp⟩ := hwf.parent_child node nd hnd m hm
        rw [parentOf_of_get? hmd]; exact hmp
      have hnodup : nd.children.Nodup := hwf.children_nodup node nd hnd
      obtain ⟨s₁, hre⟩ := removeEach_isOk nd.children hwf hchp hnodup
      have hwf₁ : WellFormed s₁.tree := removeEach_preserves_wellformed _ hwf hre
      have hsp : ShapePreserving s.tree s₁.tree := shapePreserving_removeEach _ hre
      -- reference child は fragment の children には入っていない（parent が違う）
      have hcnot : ∀ c, child = some c → c ∉ nd.children := by
        intro c hc hm
        have h1 := hchild c hc
        rw [hchp c hm] at h1
        exact hne (Option.some.inj h1)
      have hins : Insertable s₁.tree parent child nd.children := by
        refine ⟨exists_get?_of_kindPreserving hsp hpd, ?_, ?_, ?_, ?_, hnodup⟩
        · intro c hc
          rw [parentOf_removeEach_of_not_mem _ hre (hcnot c hc)]
          exact hchild c hc
        · exact hcnot
        · intro m hm
          obtain ⟨md, hmd, -⟩ := hwf.parent_child node nd hnd m hm
          exact exists_get?_of_kindPreserving hsp hmd
        · intro m hm hc
          refine hnotanc ?_
          have hnm : Ancestor s.tree node m := Ancestor.step (hchp m hm)
          rcases hc with he | ha
          · exact Or.inr (by rw [← he]; exact hnm)
          · exact Or.inr (hnm.trans_ancestor (ancestor_of_removeEach _ hre ha))
      obtain ⟨o, ho⟩ := insertNodesAt_isOk_of_insertable (b := b)
        (s := queueTreeMutationRecord s₁ node [] nd.children none none)
        (by simpa using hwf₁) (by simpa using hins)
      exact ⟨o, by rw [hre]; exact ho⟩
  · rw [if_neg (by simp [hk])]
    refine insertNodesAt_isOk_of_insertable hwf ⟨⟨pd, hpd⟩, hchild, ?_, ?_, ?_, by simp⟩
    · intro c hc hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      exact hcn c hc hm
    · intro m hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      exact ⟨nd, by rw [hm]; exact hnd⟩
    · intro m hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rw [hm]
      exact hnotanc

end Dom
