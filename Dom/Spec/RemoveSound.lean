import Dom.Spec.Remove
import Dom.Properties.Iterator
import Dom.Properties.Range
import Dom.Properties.Algorithms
import Dom.Properties.Record
import Dom.Properties.TreeOrder

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
    · rw [parentOf, hd0] at hp; simp [hnp] at hp
    · exact ⟨d0, p', pd, hd0, hnp, hpd, he⟩
  have hpp : p0 = p := by
    rw [parentOf, hd0] at hp
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
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · split at hm'
      · next he =>
        rw [he, hpd0] at hm
        cases hm
        cases hm'
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · rw [hm] at hm'
        cases hm'
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

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

/-! ## step 20：transient registered observer -/

/-- `remove` の step 3-7 は registration を変えない。 -/
theorem remove_registrations_before_transient {s s₁ : DOMState} {n : NodeId}
    (hd : detachWithLiveAdjust s n = .ok s₁) : s₁.registrations = s.registrations := by
  obtain ⟨_, _, hs⟩ := detachWithLiveAdjust_cases hd
  rw [hs, DOMState.withTree_registrations, iteratorPreRemove_registrations,
    liveRangePreRemove_registrations]

/-- `remove` が積む registration は、step 20 が足す transient の分だけである。 -/
theorem remove_registrations {s s' : DOMState} {n p : NodeId} {b : Bool}
    (hp : parentOf s.tree n = some p) (h : remove s n b = .ok s') :
    ∃ s₁, detachWithLiveAdjust s n = .ok s₁ ∧
      s'.registrations = s.registrations ++
        ((p :: ancestors s₁.tree p).flatMap fun m =>
          (s.registrations.filter fun r => r.node == m && r.subtree).map fun r =>
            { r with node := n, transient := true, source := some r.node }) := by
  simp only [remove, hp] at h
  split at h
  · simp at h
  · next s₁ hd =>
    refine ⟨s₁, hd, ?_⟩
    have hreg : s₁.registrations = s.registrations := remove_registrations_before_transient hd
    have h₂ : s'.registrations = (addTransientObservers s₁ n p).registrations := by
      split at h
      · rw [← Except.ok.inj h]
      · rw [← Except.ok.inj h]; simp
    rw [h₂]
    show s₁.registrations ++ _ = _
    rw [hreg]

/-- **step 20 の soundness。** -/
theorem remove_sound_transient {s s' : DOMState} {n p : NodeId} {b : Bool}
    (hwf : WellFormed s.tree) (hp : parentOf s.tree n = some p) (h : remove s n b = .ok s') :
    TransientAdded s s' n p := by
  obtain ⟨s₁, hd, hreg⟩ := remove_registrations hp h
  rw [ancestors_eq_after_detach hwf hp hd] at hreg
  refine ⟨fun r hr => by rw [hreg]; exact List.mem_append_left _ hr, ?_, ?_⟩
  · intro src hsrc hsub hanc'
    refine ⟨{ src with node := n, transient := true, source := some src.node }, ?_, ?_, rfl, rfl, rfl⟩
    · rw [hreg]
      refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨src.node, ?_, ?_⟩)
      · rcases hanc' with he | ha
        · exact List.mem_cons.mpr (Or.inl he)
        · exact List.mem_cons_of_mem _ ((mem_ancestors_iff hwf p src.node).mpr ha)
      · exact List.mem_map.mpr ⟨src, List.mem_filter.mpr ⟨hsrc, by simp [hsub]⟩, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro r hr hnot
    rw [hreg] at hr
    rcases List.mem_append.mp hr with hmem | hmem
    · exact absurd hmem hnot
    · obtain ⟨m, hm, hrm⟩ := List.mem_flatMap.mp hmem
      obtain ⟨src, hsrc, rfl⟩ := List.mem_map.mp hrm
      obtain ⟨hsrcmem, hcond⟩ := List.mem_filter.mp hsrc
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      refine ⟨src, hsrcmem, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hcond.2, ?_, rfl, rfl, rfl⟩
      rcases List.mem_cons.mp hm with he | hm'
      · exact Or.inl (by rw [hcond.1, he])
      · exact Or.inr (by rw [hcond.1]; exact (mem_ancestors_iff hwf p m).mp hm')

/-! ## step 21：mutation record -/

/-- 実行側が `s₂` で数える interested observer は、元の状態で数えたものと同じである。 -/
theorem interestedIn_childList_bridge {s s₁ : DOMState} {n p : NodeId} (hwf : WellFormed s.tree)
    (hp : parentOf s.tree n = some p) (hd : detachWithLiveAdjust s n = .ok s₁)
    (mo : Nat) (rec : MutationRecord) (hrec : rec.target = p)
    (hty : rec.type = RecordType.childList)
    (hna : rec.attributeName = none) (hns : rec.attributeNamespace = none) :
    mo ∈ (((interestedObservers (addTransientObservers s₁ n p) rec none)).map (·.1)) ↔
      InterestedInChildList s mo p := by
  rw [mem_interestedObservers]
  have htree : (addTransientObservers s₁ n p).tree = s₁.tree := rfl
  have hanc : ancestors s₁.tree p = ancestors s.tree p := ancestors_eq_after_detach hwf hp hd
  have hreg : (addTransientObservers s₁ n p).registrations = s.registrations ++
      ((p :: ancestors s.tree p).flatMap fun m =>
        (s.registrations.filter fun r => r.node == m && r.subtree).map fun r =>
          { r with node := n, transient := true, source := some r.node }) := by
    show s₁.registrations ++ _ = _
    rw [remove_registrations_before_transient hd, hanc]
  have hcond : ∀ r : Registration,
      Registration.interestedIn r rec.target rec.type rec.attributeName rec.attributeNamespace
        = ((r.node == p || r.subtree) && r.childList) := by
    intro r
    rw [hrec, hty, hna, hns]
    rfl
  constructor
  · rintro ⟨r, hrmem, hnode, hc, rfl⟩
    rw [hcond] at hc
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
    rw [hreg] at hrmem
    rcases List.mem_append.mp hrmem with hmem | hmem
    · refine ⟨r, hmem, rfl, hc.2, ?_, hc.1⟩
      rw [htree, hrec, hanc] at hnode
      rcases List.mem_cons.mp hnode with he | hm
      · exact Or.inl he
      · exact Or.inr ((mem_ancestors_iff hwf p r.node).mp hm)
    · -- step 20 が足した transient は node（外した node）に付くので、
      -- parent の inclusive ancestor にはならない。
      exfalso
      obtain ⟨m, -, hrm⟩ := List.mem_flatMap.mp hmem
      obtain ⟨src, -, rfl⟩ := List.mem_map.mp hrm
      rw [htree, hrec, hanc] at hnode
      refine not_inclusiveAncestor_of_parentOf hwf hp ?_
      rcases List.mem_cons.mp hnode with he | hm
      · exact Or.inl he
      · exact Or.inr ((mem_ancestors_iff hwf p n).mp hm)
  · rintro ⟨r, hrmem, rfl, hchild, hanc', hsub⟩
    refine ⟨r, ?_, ?_, ?_, rfl⟩
    · rw [hreg]; exact List.mem_append_left _ hrmem
    · rw [htree, hrec, hanc]
      rcases hanc' with he | ha
      · exact List.mem_cons.mpr (Or.inl he)
      · exact List.mem_cons_of_mem _ ((mem_ancestors_iff hwf p r.node).mpr ha)
    · rw [hcond]
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
      exact ⟨hsub, hchild⟩

/-- 一つの observer が受け取る record は、interested なら一つ、そうでなければ無い。 -/
theorem records_after_queue {s₂ s₃ : DOMState} {rec : MutationRecord} {mo : Nat}
    {o o' : ObserverState} (hrec : rec.type = RecordType.childList)
    (hov : rec.oldValue = none)
    (hq : s₃ = queueMutationRecord s₂ rec none)
    (ho : s₂.observers[mo]? = some o) (ho' : s₃.observers[mo]? = some o') :
    (mo ∈ ((interestedObservers s₂ rec none).map (·.1)) → o'.records = o.records ++ [rec]) ∧
      (mo ∉ ((interestedObservers s₂ rec none).map (·.1)) → o'.records = o.records) := by
  rw [hq, observers_queueMutationRecord] at ho'
  have hfold := records_foldl_enqueue rec _ s₂.observers mo o o' ho ho'
  constructor
  · intro hmem
    obtain ⟨q, hq', hq1⟩ := List.mem_map.mp hmem
    have hq2 : q.2 = none := oldValue_none_of_childList s₂ rec q hq'
    have hqe : q = (mo, none) := by
      cases q with
      | mk a bb => simp only at hq1 hq2; rw [hq1, hq2]
    rw [hfold, filterMap_eq_single
      (fun r : Nat × Option String => ({ rec with oldValue := r.2 } : MutationRecord)) mo none _
      (nodup_interestedObservers s₂ rec none) (by rw [← hqe]; exact hq')]
    have : ({ rec with oldValue := (none : Option String) } : MutationRecord) = rec := by
      rw [← hov]
    rw [this]
  · intro hmem
    rw [hfold, filterMap_eq_nil_of_not_mem
      (fun r : Nat × Option String => ({ rec with oldValue := r.2 } : MutationRecord)) mo _ hmem]
    simp

/-- **step 21 の soundness。** -/
theorem remove_sound_record {s s' : DOMState} {n p : NodeId} {b : Bool}
    (hwf : WellFormed s.tree) (hp : parentOf s.tree n = some p) (h : remove s n b = .ok s') :
    RecordQueued s s' n p (previousSibling s.tree n) (nextSibling s.tree n) b := by
  simp only [remove, hp] at h
  split at h
  · simp at h
  · next s₁ hd =>
    have hobs₁ := detachWithLiveAdjust_observers hd
    have hpend₁ := detachWithLiveAdjust_pending hd
    have hmt₁ := detachWithLiveAdjust_microtask hd
    -- step 20 の後の状態。record を積むのはこの上である。
    have hlen₂ : (addTransientObservers s₁ n p).observers.length = s.observers.length := by
      rw [addTransientObservers_observers_length, hobs₁]
    have hget₂ : ∀ (mo : Nat) (o : ObserverState), s.observers[mo]? = some o →
        ∃ o₂, (addTransientObservers s₁ n p).observers[mo]? = some o₂ ∧ o₂.records = o.records := by
      intro mo o ho
      rcases hq : (addTransientObservers s₁ n p).observers[mo]? with _ | o₂
      · exfalso
        rw [List.getElem?_eq_none_iff, hlen₂] at hq
        rcases Nat.lt_or_ge mo s.observers.length with hk | hk
        · omega
        · rw [List.getElem?_eq_none hk] at ho; simp at ho
      · exact ⟨o₂, rfl, records_addTransientObservers s₁ n p mo o o₂ (by rw [hobs₁]; exact ho) hq⟩
    unfold RecordQueued TreeRecordQueued
    split at h
    · -- suppressObservers が true なら record は積まない。
      next hb =>
      rw [← Except.ok.inj h, if_pos hb]
      refine ⟨hlen₂, ?_, ?_, ?_⟩
      · intro mo o o' ho ho'
        exact records_addTransientObservers s₁ n p mo o o' (by rw [hobs₁]; exact ho) ho'
      · intro mo
        have hp' : (addTransientObservers s₁ n p).pendingObservers = s.pendingObservers := hpend₁
        rw [hp']
      · show (addTransientObservers s₁ n p).microtaskQueued = _
        exact hmt₁
    · next hb =>
      rw [← Except.ok.inj h, if_neg hb]
      have hqueue : queueTreeMutationRecord (addTransientObservers s₁ n p) p [] [n]
          (previousSibling s.tree n) (nextSibling s.tree n)
            = queueMutationRecord (addTransientObservers s₁ n p)
              { type := .childList, target := p, addedNodes := [], removedNodes := [n],
                previousSibling := previousSibling s.tree n,
                nextSibling := nextSibling s.tree n } none := by
        unfold queueTreeMutationRecord
        rw [if_neg (by simp)]
      have hbridge := fun mo => interestedIn_childList_bridge hwf hp hd mo
        ({ type := .childList, target := p, addedNodes := [], removedNodes := [n],
           previousSibling := previousSibling s.tree n,
           nextSibling := nextSibling s.tree n } : MutationRecord) rfl rfl rfl rfl
      rw [hqueue]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [queueMutationRecord_observers_length, hlen₂]
      · intro mo o o' ho ho'
        obtain ⟨o₂, ho₂, hrec₂⟩ := hget₂ mo o ho
        have := records_after_queue (mo := mo) rfl rfl rfl ho₂ ho'
        constructor
        · intro hint
          rw [this.1 ((hbridge mo).mpr hint), hrec₂]
        · intro hint
          rw [this.2 (fun hm => hint ((hbridge mo).mp hm)), hrec₂]
      · intro mo hint
        refine (mem_pendingObservers_queueMutationRecord _ _ _ mo).mpr (Or.inr ?_)
        exact (hbridge mo).mpr hint
      · intro mo hmo
        refine (mem_pendingObservers_queueMutationRecord _ _ _ mo).mpr (Or.inl ?_)
        show mo ∈ s₁.pendingObservers
        rw [hpend₁]
        exact hmo
      · intro mo hmo
        rcases (mem_pendingObservers_queueMutationRecord _ _ _ mo).mp hmo with hm | hm
        · left
          have hm' : mo ∈ s₁.pendingObservers := hm
          rw [hpend₁] at hm'
          exact hm'
        · exact Or.inr ((hbridge mo).mp hm)
      · exact microtaskQueued_queueMutationRecord _ _ _

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
        simp only [if_pos rfl]
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
  have hit := remove_iterators hp h
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
**`remove` は `RemoveSpec` を満たす。**

仕様の step のうち model が扱うものすべてについて、
実行関数の結果が関係意味論の要求どおりであることを言う。
-/
theorem remove_sound {s s' : DOMState} {n : NodeId} {b : Bool}
    (hwf : WellFormed s.tree) (h : remove s n b = .ok s') : RemoveSpec s n b s' := by
  obtain ⟨⟨p, hp⟩, -⟩ := remove_ok h
  exact ⟨p, (index s.tree n).getD 0, hp, rfl,
    remove_sound_range hwf hp h, remove_sound_iterator hwf hp h,
    remove_sound_tree hwf hp h, remove_sound_transient hwf hp h, remove_sound_record hwf hp h⟩

end Dom.Spec
