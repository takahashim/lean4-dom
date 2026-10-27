import Dom.Spec.Remove
import Dom.Properties.Iterator
import Dom.Properties.Range
import Dom.Properties.Algorithms
import Dom.Properties.Record
import Dom.Properties.TreeOrder
import Dom.Spec.ObserverOrderSound
import Dom.Spec.RecordSound

/-!
# `remove` は関係意味論を満たす（soundness）

`Dom/Spec/Remove.lean` の `RemoveSpec` を、実行関数 `remove` が満たすことを示す。

仕様の副作用ごとに component を分けてあるので、証明もその単位で書く。
最後に `remove_sound` でまとめる。
-/

namespace Dom.Spec

open Dom

/-! ## step 3：live range pre-remove steps -/

/-- 実行側の boundary point 調整は、関係 `BoundaryAdjusted` を満たす。 -/
theorem boundaryAdjusted_liveRangePreRemoveBP {t : Tree} (hwf : WellFormed t)
    (node parent : NodeId) (index : Nat) (bp : BoundaryPoint) :
    BoundaryAdjusted t node parent index bp (liveRangePreRemoveBP t node parent index bp) := by
  unfold BoundaryAdjusted liveRangePreRemoveBP rangeMoveOutOfSubtree rangeShiftAfterRemove
  by_cases hA : isInclusiveAncestorOf t node bp.node = true
  · -- step 4-5。移した先の offset はちょうど index なので step 6-7 には当たらない。
    left
    refine ⟨(isInclusiveAncestorOf_iff hwf node bp.node).mp hA, ?_⟩
    rw [if_pos hA]
    exact if_neg (by simp)
  · have hA' : ¬ InclusiveAncestor t node bp.node := fun h =>
      hA ((isInclusiveAncestorOf_iff hwf node bp.node).mpr h)
    rw [if_neg hA]
    by_cases hs : bp.node = parent ∧ index < bp.offset
    · exact Or.inr (Or.inl ⟨hA', hs.1, hs.2, by rw [if_pos hs]⟩)
    · exact Or.inr (Or.inr ⟨hA', hs, by rw [if_neg hs]⟩)

/-- **step 3 の soundness。** -/
theorem remove_sound_range {s s' : DOMState} {n p : NodeId} {b : Bool}
    (hwf : WellFormed s.tree) (hp : parentOf s.tree n = some p) (h : remove s n b = .ok s') :
    RangeAdjusted s s' n p ((index s.tree n).getD 0) := by
  have hr := remove_ranges hp h
  constructor
  · rw [hr]; exact List.length_map ..
  · intro i r r' hri hri'
    rw [hr, List.getElem?_map, hri] at hri'
    simp only [Option.map_some, Option.some.injEq] at hri'
    rw [← hri']
    exact ⟨boundaryAdjusted_liveRangePreRemoveBP hwf n p _ r.start,
      boundaryAdjusted_liveRangePreRemoveBP hwf n p _ r.«end»⟩

/-! ## step 7：木からの取り外し -/

/-- **step 7 の soundness。** -/
theorem remove_sound_tree {s s' : DOMState} {n p : NodeId} {b : Bool}
    (hwf : WellFormed s.tree) (hp : parentOf s.tree n = some p) (h : remove s n b = .ok s') :
    TreeRemoved s.tree s'.tree n p := by
  have hd : detach s.tree n = .ok s'.tree := (remove_ok h).2
  -- parent があるので、detach は必ず detachFrom の枝を通る。
  obtain ⟨d0, p0, pd0, hd0, hp0, hpd0, htree⟩ :
      ∃ d p' pd, s.tree.get? n = some d ∧ d.parent = some p' ∧ s.tree.get? p' = some pd ∧
        s'.tree = detachFrom s.tree n p' d pd := by
    rcases detach_ok_cases hd with ⟨d0, hd0, hnp, _⟩ | ⟨d0, p', pd, hd0, hnp, hpd, he⟩
    · rw [parentOf_eq, hd0] at hp; simp [hnp] at hp
    · exact ⟨d0, p', pd, hd0, hnp, hpd, he⟩
  have hpp : p0 = p := by
    rw [parentOf_eq, hd0] at hp
    exact Option.some.inj (hp0 ▸ hp : some p0 = some p)
  subst hpp
  have hpn : p0 ≠ n := fun he => hwf.acyclic n (Ancestor.step (he ▸ hp))
  refine ⟨detach_parentOf hd, ?_, ?_, ?_, ?_, ?_⟩
  · rw [detach_childrenOf hwf hp hd]
    unfold Dom.ListUtil.removeAll
    refine List.filter_congr (fun x _ => ?_)
    show decide (x ≠ n) = !(x == n)
    by_cases hx : x = n
    · simp [hx]
    · simp [hx]
  · intro m hm; rw [parentOf_detach hd m, if_neg hm]
  · intro m hm; exact detach_childrenOf_ne hp hd hm
  · intro m
    rw [htree, get?_detachFrom]
    split
    · next he => rw [he, hd0]; rfl
    · split
      · next he => rw [he, hpd0]; rfl
      · rfl
  · intro m dd dd' hm hm'
    rw [htree, get?_detachFrom] at hm'
    split at hm'
    · next he =>
      rw [he, hd0] at hm
      cases hm
      cases hm'
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · split at hm'
      · next he =>
        rw [he, hpd0] at hm
        cases hm
        cases hm'
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · rw [hm] at hm'
        cases hm'
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## step 3-7 は observer 側を触らない -/

theorem detachWithLiveAdjust_observers {s s₁ : DOMState} {n : NodeId}
    (hd : detachWithLiveAdjust s n = .ok s₁) : s₁.observers = s.observers := by
  obtain ⟨_, _, hs⟩ := detachWithLiveAdjust_cases hd
  rw [hs, DOMState.withTree_observers, iteratorPreRemove_observers,
    liveRangePreRemove_observers]

theorem detachWithLiveAdjust_pending {s s₁ : DOMState} {n : NodeId}
    (hd : detachWithLiveAdjust s n = .ok s₁) : s₁.pendingObservers = s.pendingObservers := by
  obtain ⟨_, _, hs⟩ := detachWithLiveAdjust_cases hd
  rw [hs]
  show (liveRangePreRemove s n).pendingObservers = _
  unfold liveRangePreRemove
  split <;> rfl

theorem detachWithLiveAdjust_microtask {s s₁ : DOMState} {n : NodeId}
    (hd : detachWithLiveAdjust s n = .ok s₁) : s₁.microtaskQueued = s.microtaskQueued := by
  obtain ⟨_, _, hs⟩ := detachWithLiveAdjust_cases hd
  rw [hs]
  show (liveRangePreRemove s n).microtaskQueued = _
  unfold liveRangePreRemove
  split <;> rfl

/-- 外す node は parent の inclusive ancestor ではない（非巡回性）。 -/
theorem not_inclusiveAncestor_of_parentOf {t : Tree} {n p : NodeId} (hwf : WellFormed t)
    (hp : parentOf t n = some p) : ¬ InclusiveAncestor t n p := by
  rintro (he | ha)
  · exact hwf.acyclic n (Ancestor.step (he ▸ hp))
  · exact hwf.acyclic p (Ancestor.trans_ancestor (Ancestor.step hp) ha)

/-- parent の祖先は、その子を外しても変わらない。 -/
theorem ancestors_eq_after_detach {s s₁ : DOMState} {n p : NodeId} (hwf : WellFormed s.tree)
    (hp : parentOf s.tree n = some p) (hd : detachWithLiveAdjust s n = .ok s₁) :
    ancestors s₁.tree p = ancestors s.tree p := by
  have hdt : detach s.tree n = .ok s₁.tree := detachWithLiveAdjust_tree hd
  have hwf' : WellFormed s₁.tree := detach_preserves_wellformed hwf hdt
  obtain ⟨pd, hpd⟩ := exists_data_of_parentOf hwf hp
  obtain ⟨pd', hpd'⟩ := exists_get?_of_kindPreserving (shapePreserving_detach hdt) hpd
  exact ancestors_detach_eq hwf hwf' hdt hpd hpd' (not_inclusiveAncestor_of_parentOf hwf hp)

/-! ## step 15：add transient registered observers -/

/-- step 1.1-1.5 の一歩は、本文の書き方と一致する。 -/
theorem collectTransient_eq (node : NodeId) (ex acc : List Registration) (r : Registration) :
    collectTransient node ex acc r = transientAppend node ex acc r := by
  have hsrc : r.sourceNode = sourceOf r := rfl
  unfold collectTransient transientAppend hasTransientFrom Registration.transientOn
  rw [hsrc]
  by_cases hc : r.subtree = true ∧
      ¬ ∃ t ∈ ex ++ acc, t.transient = true ∧ t.observer = r.observer ∧ t.source = sourceOf r
  · rw [if_pos hc, if_pos]
    obtain ⟨hs, hn⟩ := hc
    simp only [hs, Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false,
      Bool.and_eq_true, beq_iff_eq]
    intro t ht ⟨⟨h1, h2⟩, h3⟩
    exact hn ⟨t, ht, h1, h2, h3⟩
  · rw [if_neg hc, if_neg]
    intro hb
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false,
      Bool.and_eq_true, beq_iff_eq] at hb
    refine hc ⟨hb.1, ?_⟩
    rintro ⟨t, ht, h1, h2, h3⟩
    exact hb.2 t ht ⟨⟨h1, h2⟩, h3⟩

/-- 実行側の `newTransients` は、本文の inclusive ancestor の列で `transientsFor` を取ったものである。 -/
theorem newTransients_eq (s : DOMState) (node parent : NodeId) :
    newTransients s node parent =
      transientsFor s.registrations (parent :: ancestors s.tree parent) node := by
  unfold newTransients transientsFor
  have : collectTransient node (s.registrations.filter fun r => r.node == node) =
      transientAppend node (regsOn s.registrations node) := by
    funext acc r; exact collectTransient_eq _ _ _ _
  rw [this]
  rfl

/-- step 1.7 の畳み込みは、足した transient の observer を順に pending へ append する。 -/
theorem pending_foldl_pendTransient :
    ∀ (l : List Registration) (st : DOMState),
      (l.foldl pendTransient st).pendingObservers = appendNew st.pendingObservers (l.map (·.observer))
  | [], _ => rfl
  | r :: l, st => by
    rw [List.foldl_cons, pending_foldl_pendTransient l, List.map_cons, appendNew_cons]
    congr 1
    have hmt : ∀ x : DOMState,
        (queueMutationObserverMicrotask x).pendingObservers = x.pendingObservers := by
      intro x; unfold queueMutationObserverMicrotask; split <;> rfl
    unfold pendTransient
    rw [hmt]
    unfold addPendingObserver
    by_cases h : r.observer ∈ st.pendingObservers
    · rw [if_pos (by simpa using h), if_pos h]
    · rw [if_neg (by simpa using h), if_neg h]

/-- **step 15 の soundness。** `addTransientObservers` は `TransientAdded` を満たす。 -/
theorem transientAdded_of_add {s : DOMState} (hwf : WellFormed s.tree) (node parent : NodeId) :
    TransientAdded s (addTransientObservers s node parent) node parent where
  tree := by simp
  ranges := by simp
  iterators := by simp
  observersLength := by simp
  records := fun mo o o' ho ho' => records_addTransientObservers s node parent mo o o' ho ho'
  added := by
    refine ⟨_, inclusiveAncestorsUp_of_wf hwf parent, fun n => ?_, ?_, ?_⟩
    · rw [addTransientObservers_registrations, ← newTransients_eq]
      unfold regsOn
      rw [List.filter_append]
      by_cases hn : n = node
      · subst hn
        rw [if_pos rfl]
        congr 1
        exact List.filter_eq_self.mpr fun x hx => by simp [node_of_mem_newTransients hx]
      · rw [if_neg hn]
        have : (newTransients s node parent).filter (fun r => r.node == n) = [] :=
          List.filter_eq_nil_iff.mpr fun x hx => by
            simp [node_of_mem_newTransients hx, Ne.symm hn]
        rw [this, List.append_nil]
    · rw [addTransientObservers_eq, pending_foldl_pendTransient, ← newTransients_eq]
    · rw [addTransientObservers_microtaskQueued, newTransients_eq]
  untouched := untouched_addTransientObservers s node parent

/-! ## step 3-7 -/

/-- `detachWithLiveAdjust` は「observer を抑えた `remove`」の前半である。 -/
theorem remove_suppress_of_detach {s s₁ : DOMState} {node p : NodeId}
    (hp : parentOf s.tree node = some p) (h : detachWithLiveAdjust s node = .ok s₁) :
    remove s node true = .ok (addTransientObservers s₁ node p) := by
  rw [remove_of_detach hp h]
  simp

/-! ## step 4：NodeIterator pre-remove steps -/

/-- tree order の列の中で、`next` より後ろにある node は `next` に先行しない。 -/
theorem precedes_eq_false_of_later_in_treeOrder {t : Tree} (hwf : WellFormed t)
    {n m next : NodeId} {nd : NodeData} (hn : t.get? n = some nd)
    {l₁ l₂ : List NodeId} (hsplit : treeOrder t n = l₁ ++ m :: l₂) (hnext : next ∈ l₁) :
    precedes t m next = false := by
  have hnd : (l₁ ++ m :: l₂).Nodup := hsplit ▸ treeOrder_nodup hwf n
  obtain ⟨-, -, hdisj⟩ := List.nodup_append.mp hnd
  have hm : m ∉ l₁ := fun h => hdisj m h m (List.mem_cons_self ..) rfl
  obtain ⟨rd, hrd⟩ := exists_data_of_inclusiveAncestor hwf (root_inclusive_ancestor t n) hn
  have hmem : ∀ x ∈ treeOrder t n, InclusiveDescendant t x (root t n) := by
    intro x hx
    exact (mem_preorder_iff hwf hrd x).mp hx
  have hmm : InclusiveDescendant t m (root t n) :=
    hmem m (by rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_self ..))
  have hnn : InclusiveDescendant t next (root t n) :=
    hmem next (by rw [hsplit]; exact List.mem_append_left _ hnext)
  rw [precedes_eq_precedesIn_preorder hwf hrd hmm hnn]
  show precedesIn (treeOrder t n) m next = false
  rw [hsplit]
  exact precedesIn_eq_false_of_later l₁ l₂ hm hnext

/-- **`firstFollowingOutside` は仕様の「最初の」を計算している。** -/
theorem firstFollowingOutside_spec {t : Tree} (hwf : WellFormed t) {root n next : NodeId}
    {nd : NodeData} (hn : t.get? n = some nd)
    (h : firstFollowingOutside t root n = some next) :
    FirstFollowingOutside t root n next := by
  unfold firstFollowingOutside at h
  split at h
  · simp at h
  · next before after hs =>
    have hsplit : treeOrder t n = before ++ n :: after := Dom.ListUtil.splitAt?_eq_some hs
    obtain ⟨hP, as, bs, hafter, hnot⟩ := List.find?_eq_some_iff_append.mp h
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hP
    refine ⟨?_, (isInclusiveAncestorOf_iff hwf root next).mp hP.1, ?_, ?_⟩
    · exact (precedes_iff_mem_after hwf hsplit).mpr
        (by rw [hafter]; exact List.mem_append_right _ (List.mem_cons_self ..))
    · intro hc
      rw [(isInclusiveAncestorOf_iff hwf n next).mpr hc] at hP
      simp at hP
    · intro m hprec hroot hnotanc
      have hmem : m ∈ after := (precedes_iff_mem_after hwf hsplit).mp hprec
      have hPm : (isInclusiveAncestorOf t root m && !isInclusiveAncestorOf t n m) = true := by
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
        refine ⟨(isInclusiveAncestorOf_iff hwf root m).mpr hroot, ?_⟩
        cases hb : isInclusiveAncestorOf t n m with
        | false => rfl
        | true => exact absurd ((isInclusiveAncestorOf_iff hwf n m).mp hb) hnotanc
      rw [hafter] at hmem
      rcases List.mem_append.mp hmem with hm | hm
      · exfalso
        have hfalse := hnot m hm
        rw [hPm] at hfalse
        simp at hfalse
      · rcases List.mem_cons.mp hm with rfl | hm'
        · show precedesIn (treeOrder t m) m m = false
          exact precedesIn_self _ _ (treeOrder_nodup hwf m)
        · obtain ⟨c₁, c₂, hc⟩ := List.append_of_mem hm'
          refine precedes_eq_false_of_later_in_treeOrder hwf hn
            (l₁ := before ++ n :: (as ++ next :: c₁)) (l₂ := c₂) ?_ ?_
          · rw [hsplit, hafter, hc]
            simp [List.append_assoc]
          · exact List.mem_append_right _ (List.mem_cons_of_mem _
              (List.mem_append_right _ (List.mem_cons_self ..)))

/-- `firstFollowingOutside` が `none` なら、仕様の条件を満たす node は無い。 -/
theorem not_firstFollowingOutside_of_none {t : Tree} (hwf : WellFormed t) {root n : NodeId}
    (h : firstFollowingOutside t root n = none) :
    ∀ next, ¬ FirstFollowingOutside t root n next := by
  intro next hspec
  unfold firstFollowingOutside at h
  split at h
  · -- 列が切れないのは `n` が木に無いときで、そのとき `n` は誰にも先行しない。
    next hs =>
    have hnmem : n ∉ treeOrder t n := fun hm =>
      absurd (Dom.ListUtil.splitAt?_isSome_of_mem hm) (by rw [hs]; simp)
    have hfalse : precedes t n next = false := precedesIn_of_not_mem (treeOrder t n) hnmem
    rw [hspec.1] at hfalse
    simp at hfalse
  · next before after hs =>
    have hsplit : treeOrder t n = before ++ n :: after := Dom.ListUtil.splitAt?_eq_some hs
    have hmem : next ∈ after := (precedes_iff_mem_after hwf hsplit).mp hspec.1
    have := List.find?_eq_none.mp h next hmem
    exact this (by
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
      refine ⟨(isInclusiveAncestorOf_iff hwf root next).mpr hspec.2.1, ?_⟩
      cases hb : isInclusiveAncestorOf t n next with
      | false => rfl
      | true => exact absurd ((isInclusiveAncestorOf_iff hwf n next).mp hb) hspec.2.2.1)

/-- 仕様の step 3、前の兄弟が無い場合。 -/
theorem lastBeforeRemoval_none {t : Tree} {n p : NodeId} (hp : parentOf t n = some p)
    (hprev : previousSibling t n = none) : LastBeforeRemoval t n p :=
  Or.inl ⟨hprev, hp⟩

/-- 仕様の step 3、前の兄弟がある場合。その部分木の tree order で最後の node になる。 -/
theorem lastBeforeRemoval_some {t : Tree} (hwf : WellFormed t) {n p prev : NodeId}
    (hp : parentOf t n = some p) (hprev : previousSibling t n = some prev) :
    LastBeforeRemoval t n (Dom.ListUtil.lastD (preorder t prev) prev) := by
  obtain ⟨pd, hpd, -⟩ := parentOf_eq_some
    (parentOf_of_mem_childrenOf hwf (previousSibling_mem_children hp hprev))
  refine Or.inr ⟨prev, hprev, inclusiveAncestor_lastD_preorder hwf hpd, ?_⟩
  intro x hx
  have hxmem : x ∈ preorder t prev := (mem_preorder_iff hwf hpd x).mpr hx
  rw [precedes_eq_precedesIn_preorder hwf hpd (inclusiveAncestor_lastD_preorder hwf hpd) hx]
  exact precedesIn_lastD_eq_false _ _ _ (preorder_nodup hwf prev) hxmem

/-- **`adjust a node pointer` は関係 `PointerAdjusted` を満たす。** -/
theorem pointerAdjusted_adjustNodePointer {t : Tree} (hwf : WellFormed t) {root n : NodeId}
    {nd : NodeData} (hn : t.get? n = some nd) {p : NodeId} (hp : parentOf t n = some p)
    (node : NodeId) (before : Bool) :
    PointerAdjusted t root n (node, before) (adjustNodePointer t root n node before) := by
  unfold adjustNodePointer
  by_cases hA : isInclusiveAncestorOf t n node = true
  · rw [if_neg (by simp [hA])]
    by_cases hR : isInclusiveAncestorOf t n root = true
    · rw [if_pos hR]
      exact PointerAdjusted.untouched (Or.inr ((isInclusiveAncestorOf_iff hwf n root).mp hR))
    · rw [if_neg (by simp [hR])]
      have hAnc : InclusiveAncestor t n node := (isInclusiveAncestorOf_iff hwf n node).mp hA
      have hRoot : ¬ InclusiveAncestor t n root := fun hc =>
        hR ((isInclusiveAncestorOf_iff hwf n root).mpr hc)
      cases hb : before with
      | true =>
        cases hf : firstFollowingOutside t root n with
        | some next =>
          exact PointerAdjusted.forward hAnc hRoot (firstFollowingOutside_spec hwf hn hf)
        | none =>
          cases hprev : previousSibling t n with
          | none =>
            dsimp only
            rw [hp]
            exact PointerAdjusted.backward hAnc hRoot
              (Or.inr (not_firstFollowingOutside_of_none hwf hf)) (lastBeforeRemoval_none hp hprev)
          | some prev =>
            dsimp only
            exact PointerAdjusted.backward hAnc hRoot
              (Or.inr (not_firstFollowingOutside_of_none hwf hf))
              (lastBeforeRemoval_some hwf hp hprev)
      | false =>
        rw [if_neg (by simp)]
        cases hprev : previousSibling t n with
        | none =>
          dsimp only
          rw [hp]
          exact PointerAdjusted.backward hAnc hRoot (Or.inl rfl) (lastBeforeRemoval_none hp hprev)
        | some prev =>
          dsimp only
          exact PointerAdjusted.backward hAnc hRoot (Or.inl rfl)
            (lastBeforeRemoval_some hwf hp hprev)
  · rw [if_pos (by simp [hA])]
    exact PointerAdjusted.untouched (Or.inl fun hc =>
      hA ((isInclusiveAncestorOf_iff hwf n node).mpr hc))

/-- **step 4 の soundness。** -/
theorem remove_sound_iterator {s s' : DOMState} {n p : NodeId} {b : Bool}
    (hwf : WellFormed s.tree) (hp : parentOf s.tree n = some p) (h : remove s n b = .ok s') :
    IteratorAdjusted s s' n := by
  obtain ⟨nd, hnd, -⟩ := parentOf_eq_some hp
  have hit := remove_iterators h
  constructor
  · rw [hit]; exact List.length_map ..
  · intro i it it' hi hi'
    rw [hit, List.getElem?_map, hi] at hi'
    simp only [Option.map_some, Option.some.injEq] at hi'
    rw [← hi']
    by_cases hc : ownerDocumentOf s.tree it.root = ownerDocumentOf s.tree n
    · rw [if_pos (by simp [hc])]
      refine ⟨rfl, rfl, ?_⟩
      rw [if_pos hc]
      exact pointerAdjusted_adjustNodePointer hwf hnd hp it.reference it.pointerBeforeReference
    · rw [if_neg (by simp [hc])]
      exact ⟨rfl, rfl, by rw [if_neg hc]⟩

/-! ## まとめ -/

/--
**`detachWithLiveAdjust` は `Detached` を満たす。**

後半（transient registered observer と record）は木・live range・NodeIterator を触らないので、
`suppressObservers` を立てた `remove` に読み替えれば step 3・4・7 の定理がそのまま効く。
-/
theorem detached_of_detach {s s₁ : DOMState} {node p : NodeId} (hwf : WellFormed s.tree)
    (hp : parentOf s.tree node = some p) (h : detachWithLiveAdjust s node = .ok s₁) :
    Detached s s₁ node p ((index s.tree node).getD 0) := by
  have hr := remove_suppress_of_detach hp h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hq := remove_sound_range hwf hp hr
    simpa [RangeAdjusted] using hq
  · have hq := remove_sound_iterator hwf hp hr
    simpa [IteratorAdjusted] using hq
  · have hq := remove_sound_tree hwf hp hr
    simpa using hq
  · obtain ⟨-, hs⟩ := DOMState.mapTree_eq_ok h
    refine ⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩⟩ <;> rw [hs] <;> first | rfl | simp

/--
**`remove` は `RemoveSpec` を満たす。**

仕様の step のうち model が扱うものすべてについて、
実行関数の結果が関係意味論の要求どおりであることを言う。
-/
theorem remove_sound {s s' : DOMState} {n : NodeId} {b : Bool}
    (hwf : WellFormed s.tree) (h : remove s n b = .ok s') : RemoveSpec s n b s' := by
  obtain ⟨p, s₁, hp, hd, hrec⟩ := remove_cases h
  have hwf₁ : WellFormed s₁.tree :=
    detach_preserves_wellformed hwf (detachWithLiveAdjust_tree hd)
  refine ⟨p, (index s.tree n).getD 0, s₁, addTransientObservers s₁ n p, hp, rfl,
    detached_of_detach hwf hp hd, transientAdded_of_add hwf₁ n p, ?_⟩
  rcases hrec with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨treeRecordQueued_of_suppress .., ObserverOnly.refl _⟩
  · exact ⟨treeRecordQueued_of_queue _ (by simpa using hwf₁) p [] [n] _ _ (by simp),
      ⟨by simp, by simp, by simp, by simp, untouched_queueTreeMutationRecord ..⟩⟩

end Dom.Spec
