import Dom.Spec.RemoveDeterministic
import Dom.Spec.ObsEq

/-!
# 観測が等しい状態は `RemoveSpec` に同じ答えを返させる

`Dom/Spec/RemoveDeterministic.lean` は段ごとに「同じ状態から出た二つの結果は観測が一致する」を言う。
関係を繋いだもの（`insert` のように途中に `remove` を持つもの）の一意性には、
それでは足りない。途中の状態は観測としてしか一致しないからである。

そこで **congruence**「入力の観測が等しければ出力の観測も等しい」を示す。

`RemoveSpec` は途中の状態を挟んで段を並べるので、段ごとに congruence を示して繋ぐ。
木から外す段は、各 component が観測の語彙だけで書かれているので、入力を観測の等しい状態に
差し替えても成り立つ（**transport**）。差し替えれば同じ入力から出た結果になるので、
`Dom/Spec/RemoveDeterministic.lean` の一意性がそのまま使える。

`precedes` と `root` は fuel を使うので、`Dom/Spec/ObsEq.lean` の
well-formed を仮定した補題を経由する。
-/

namespace Dom.Spec

open Dom

variable {s s' : DOMState} {t t' : Tree}

/-! ## 木だけを見る component -/

theorem boundaryAdjusted_transport (h : TreeObsEq t t') {node parent : NodeId} {index : Nat}
    {bp bp' : BoundaryPoint} (hb : BoundaryAdjusted t' node parent index bp bp') :
    BoundaryAdjusted t node parent index bp bp' := by
  rcases hb with ⟨ha, he⟩ | ⟨ha, hb, hc, he⟩ | ⟨ha, hb, he⟩
  · exact Or.inl ⟨h.inclusiveAncestor_iff.mp ha, he⟩
  · exact Or.inr (Or.inl ⟨fun hc' => ha (h.inclusiveAncestor_iff.mpr hc'), hb, hc, he⟩)
  · exact Or.inr (Or.inr ⟨fun hc' => ha (h.inclusiveAncestor_iff.mpr hc'), hb, he⟩)

theorem firstFollowingOutside_transport (h : TreeObsEq t t') (hwf : WellFormed t)
    {rt n next : NodeId} (hf : FirstFollowingOutside t' rt n next) :
    FirstFollowingOutside t rt n next := by
  have hwf' : WellFormed t' := h.wellFormed hwf
  obtain ⟨h1, h2, h3, h4⟩ := hf
  refine ⟨?_, h.inclusiveAncestor_iff.mp h2, fun hc => h3 (h.inclusiveAncestor_iff.mpr hc), ?_⟩
  · rw [← h.precedes hwf hwf']; exact h1
  · intro m hm hrt hnot
    rw [← h.precedes hwf hwf']
    exact h4 m (by rw [h.precedes hwf hwf']; exact hm) (h.inclusiveAncestor_iff.mpr hrt)
      (fun hc => hnot (h.inclusiveAncestor_iff.mp hc))

theorem lastBeforeRemoval_transport (h : TreeObsEq t t') (hwf : WellFormed t)
    {n m : NodeId} (hl : LastBeforeRemoval t' n m) : LastBeforeRemoval t n m := by
  have hwf' : WellFormed t' := h.wellFormed hwf
  rcases hl with ⟨hs, hp⟩ | ⟨prev, hs, ha, hlast⟩
  · exact Or.inl ⟨by rw [← h.previousSibling]; exact hs, by rw [← h.parentOf]; exact hp⟩
  · refine Or.inr ⟨prev, by rw [← h.previousSibling]; exact hs,
      h.inclusiveAncestor_iff.mp ha, ?_⟩
    intro x hx
    rw [← h.precedes hwf hwf']
    exact hlast x (h.inclusiveAncestor_iff.mpr hx)

theorem pointerAdjusted_transport (h : TreeObsEq t t') (hwf : WellFormed t)
    {rt n : NodeId} {p q : NodeId × Bool} (hp : PointerAdjusted t' rt n p q) :
    PointerAdjusted t rt n p q := by
  induction hp with
  | untouched hc =>
    refine PointerAdjusted.untouched ?_
    rcases hc with hc | hc
    · exact Or.inl fun hc' => hc (h.inclusiveAncestor_iff.mpr hc')
    · exact Or.inr (h.inclusiveAncestor_iff.mp hc)
  | forward ha hr hf =>
    exact PointerAdjusted.forward (h.inclusiveAncestor_iff.mp ha)
      (fun hc => hr (h.inclusiveAncestor_iff.mpr hc))
      (firstFollowingOutside_transport h hwf hf)
  | backward ha hr hb hl =>
    refine PointerAdjusted.backward (h.inclusiveAncestor_iff.mp ha)
      (fun hc => hr (h.inclusiveAncestor_iff.mpr hc)) ?_
      (lastBeforeRemoval_transport h hwf hl)
    rcases hb with hb | hb
    · exact Or.inl hb
    · exact Or.inr fun next hc => hb next (firstFollowingOutside_transport h.symm
        (h.wellFormed hwf) hc)

theorem treeRemoved_transport (h : TreeObsEq t t') {u : Tree} {node parent : NodeId}
    (hr : TreeRemoved t' u node parent) : TreeRemoved t u node parent where
  detached := hr.detached
  children := by rw [hr.children, h.childrenOf]
  otherParents := fun m hm => by rw [hr.otherParents m hm, h.parentOf]
  otherChildren := fun m hm => by rw [hr.otherChildren m hm, h.childrenOf]
  sameNodes := fun m => by rw [hr.sameNodes m, h m]
  sameData := fun m d d' hd hd' => hr.sameData m d d' (by rw [h]; exact hd) hd'

/-! ## 状態を見る component -/

theorem interestedInChildList_iff (h : MutationObsEq s s') {mo : Nat} {target : NodeId} :
    InterestedInChildList s' mo target ↔ InterestedInChildList s mo target := by
  constructor
  · rintro ⟨r, hr, ho, hc, ha, hs⟩
    exact ⟨r, (h.registrations r).mp hr, ho, hc, h.tree.inclusiveAncestor_iff.mp ha, hs⟩
  · rintro ⟨r, hr, ho, hc, ha, hs⟩
    exact ⟨r, (h.registrations r).mpr hr, ho, hc, h.tree.inclusiveAncestor_iff.mpr ha, hs⟩

theorem treeRecordQueued_transport (h : ObsEq s s') {out : DOMState} {target : NodeId}
    {added removed : List NodeId} {oldPrev oldNext : Option NodeId} {suppress : Bool}
    (hq : TreeRecordQueued s' out target added removed oldPrev oldNext suppress) :
    TreeRecordQueued s out target added removed oldPrev oldNext suppress := by
  cases suppress with
  | true =>
    obtain ⟨hlen, hrec, hpend, hmt, hpo⟩ := hq
    refine ⟨by rw [hlen, h.observers_length], ?_, ?_, ?_, ?_⟩
    · intro mo o o' ho ho'
      obtain ⟨o₂, ho₂, hre⟩ := h.exists_observer ho
      rw [hrec mo o₂ o' ho₂ ho', hre]
    · exact fun mo => (hpend mo).trans (h.pendingObservers mo)
    · rw [hmt, h.microtaskQueued]
    · rw [hpo, h.pendingOrder]
  | false =>
    obtain ⟨hlen, hrec, hin, hkeep, hout, hpa⟩ := hq
    refine ⟨by rw [hlen, h.observers_length], ?_, ?_, ?_, ?_,
      pendingAppended_transport h.tree.parentOf h.registrationOrder h.pendingOrder
        h.microtaskQueued hpa⟩
    · intro mo o o' ho ho'
      obtain ⟨o₂, ho₂, hre⟩ := h.exists_observer ho
      obtain ⟨h1, h2⟩ := hrec mo o₂ o' ho₂ ho'
      refine ⟨fun hi => by rw [h1 (interestedInChildList_iff h.toMutationObsEq |>.mpr hi), hre], ?_⟩
      exact fun hi => by rw [h2 fun hc => hi (interestedInChildList_iff h.toMutationObsEq |>.mp hc), hre]
    · exact fun mo hi => hin mo ((interestedInChildList_iff h.toMutationObsEq).mpr hi)
    · exact fun mo hm => hkeep mo ((h.pendingObservers mo).mpr hm)
    · intro mo hm
      rcases hout mo hm with hc | hc
      · exact Or.inl ((h.pendingObservers mo).mp hc)
      · exact Or.inr ((interestedInChildList_iff h.toMutationObsEq).mp hc)

theorem rangeAdjusted_transport (h : MutationObsEq s s') {out : DOMState} {node parent : NodeId}
    {index : Nat} (hq : RangeAdjusted s' out node parent index) :
    RangeAdjusted s out node parent index := by
  obtain ⟨hlen, hadj⟩ := hq
  refine ⟨by rw [hlen, h.ranges], ?_⟩
  intro i r r' hr hr'
  obtain ⟨h1, h2⟩ := hadj i r r' (by rw [h.ranges]; exact hr) hr'
  exact ⟨boundaryAdjusted_transport h.tree h1, boundaryAdjusted_transport h.tree h2⟩

theorem iteratorAdjusted_transport (hwf : WellFormed s.tree) (h : MutationObsEq s s') {out : DOMState}
    {node : NodeId} (hq : IteratorAdjusted s' out node) : IteratorAdjusted s out node := by
  obtain ⟨hlen, hit⟩ := hq
  refine ⟨by rw [hlen, h.iterators], ?_⟩
  intro i it it' hi hi'
  obtain ⟨hr, hw, hrest⟩ := hit i it it' (by rw [h.iterators]; exact hi) hi'
  refine ⟨hr, hw, ?_⟩
  simp only [h.tree.ownerDocumentOf] at hrest
  by_cases hc : ownerDocumentOf s.tree it.root = ownerDocumentOf s.tree node
  · rw [if_pos hc]
    rw [if_pos hc] at hrest
    exact pointerAdjusted_transport h.tree hwf hrest
  · rw [if_neg hc]
    rw [if_neg hc] at hrest
    exact hrest

/-- record queue が長さも中身も変わらない段では、`records` の像も変わらない。 -/
theorem records_map_of_preserved {s s₁ : DOMState}
    (hlen : s₁.observers.length = s.observers.length)
    (hrec : ∀ (mo : Nat) (o o' : ObserverState), s.observers[mo]? = some o →
      s₁.observers[mo]? = some o' → o'.records = o.records) :
    ∀ mo : Nat, (s₁.observers[mo]?).map (·.records) = (s.observers[mo]?).map (·.records) :=
  records_map_congr hlen rfl fun mo o oa ho hoa ob hob => by
    rw [hob] at ho; cases ho; exact hrec mo _ oa hob hoa

/-- **step 3-7 の congruence。** `move` の step 9-10, 13 も同じ形である。 -/
theorem detached_congr {sb s₁ s₁' : DOMState} {node p : NodeId} {i : Nat} {nd : NodeData}
    (hwf : WellFormed s.tree) (h : ObsEq s sb)
    (hnd : s.tree.get? node = some nd) (hp : parentOf s.tree node = some p)
    (h₁ : Detached s s₁ node p i) (h₂ : Detached sb s₁' node p i) : ObsEq s₁ s₁' := by
  obtain ⟨hr₁, hit₁, ht₁, hu₁⟩ := h₁
  obtain ⟨hr₂, hit₂, ht₂, hu₂⟩ := h₂
  have hr₂' := rangeAdjusted_transport h.toMutationObsEq hr₂
  have hit₂' := iteratorAdjusted_transport hwf h.toMutationObsEq hit₂
  have ht₂' := treeRemoved_transport h.tree ht₂
  exact
    { tree := fun m => (treeRemoved_unique ht₁ ht₂' m).symm
      ranges := (rangeAdjusted_unique hr₁ hr₂').symm
      iterators := (iteratorAdjusted_unique hwf hnd hp hit₁ hit₂').symm
      registrations := fun r => by
        rw [hu₂.registrations, hu₁.registrations]; exact h.registrations r
      records := fun mo => by rw [hu₂.observers, hu₁.observers]; exact h.records mo
      pendingObservers := fun mo => by
        rw [hu₂.pendingObservers, hu₁.pendingObservers]; exact h.pendingObservers mo
      microtaskQueued := by
        rw [hu₂.microtaskQueued, h.microtaskQueued, hu₁.microtaskQueued]
      walkers := by rw [hu₂.untouched.walkers, h.walkers, hu₁.untouched.walkers]
      listeners := by rw [hu₂.untouched.listeners, h.listeners, hu₁.untouched.listeners]
      detachedAttrs := by
        rw [hu₂.untouched.detachedAttrs, h.detachedAttrs, hu₁.untouched.detachedAttrs]
      registrationOrder := fun m => by
        rw [hu₂.registrations, hu₁.registrations]; exact h.registrationOrder m
      pendingOrder := by rw [hu₂.pendingObservers, h.pendingOrder, hu₁.pendingObservers] }

/-- **step 15（add transient registered observers）の congruence。** `move` の step 17 も同じ。 -/
theorem transientAdded_congr {sb o₁ o₂ : DOMState} {node parent : NodeId} (h : ObsEq s sb)
    (h₁ : TransientAdded s o₁ node parent) (h₂ : TransientAdded sb o₂ node parent) :
    ObsEq o₁ o₂ := by
  obtain ⟨n₁, hn₁, hreg₁, hpend₁, hmt₁⟩ := h₁.added
  obtain ⟨n₂, hn₂, hreg₂, hpend₂, hmt₂⟩ := h₂.added
  have hn := inclusiveAncestorsUp_unique (inclusiveAncestorsUp_congr h.tree.parentOf hn₁) hn₂
  subst hn
  have htf := transientsFor_congr h.registrationOrder n₁ node
  have hro : RegistrationsObsEq o₁.registrations o₂.registrations := by
    intro m
    rw [hreg₁ m, hreg₂ m, htf, h.registrationOrder node, h.registrationOrder m]
  have hpo : o₂.pendingObservers = o₁.pendingObservers := by
    rw [hpend₁, hpend₂, htf, h.pendingOrder]
  have hrec₁ := records_map_of_preserved h₁.observersLength h₁.records
  have hrec₂ := records_map_of_preserved h₂.observersLength h₂.records
  exact
    { tree := fun m => by rw [h₂.tree, h₁.tree]; exact h.tree m
      ranges := by rw [h₂.ranges, h.ranges, h₁.ranges]
      iterators := by rw [h₂.iterators, h.iterators, h₁.iterators]
      registrations := fun r => hro.mem_iff r
      records := fun mo => by rw [hrec₂, hrec₁]; exact h.records mo
      pendingObservers := fun mo => by rw [hpo]
      microtaskQueued := by rw [hmt₁, hmt₂, htf, h.microtaskQueued]
      walkers := by rw [h₂.untouched.walkers, h.walkers, h₁.untouched.walkers]
      listeners := by rw [h₂.untouched.listeners, h.listeners, h₁.untouched.listeners]
      detachedAttrs := by
        rw [h₂.untouched.detachedAttrs, h.detachedAttrs, h₁.untouched.detachedAttrs]
      registrationOrder := hro
      pendingOrder := hpo }


/-! ## `TreeRemoved` は well-formed を保つ

連鎖（`removeEach`）の congruence を回すには、途中の木も well-formed である必要がある。
関係だけからそれを言う。実行関数の不変量（`Dom/Validity/`）は使わない。
-/

theorem treeRemoved_exists {u : Tree} {node parent : NodeId} (hr : TreeRemoved t u node parent)
    {m : NodeId} {d : NodeData} (hd : t.get? m = some d) : ∃ d', u.get? m = some d' := by
  have hs := hr.sameNodes m
  rw [hd] at hs
  cases h' : u.get? m with
  | none => rw [h'] at hs; simp at hs
  | some d' => exact ⟨d', rfl⟩

theorem treeRemoved_exists' {u : Tree} {node parent : NodeId} (hr : TreeRemoved t u node parent)
    {m : NodeId} {d' : NodeData} (hd : u.get? m = some d') : ∃ d, t.get? m = some d := by
  have hs := hr.sameNodes m
  rw [hd] at hs
  cases h' : t.get? m with
  | none => rw [h'] at hs; simp at hs
  | some d => exact ⟨d, rfl⟩

/-- 外した木の ancestor は、元の木の ancestor でもある（`node` で鎖が切れるだけ）。 -/
theorem treeRemoved_ancestor {u : Tree} {node parent : NodeId} (hr : TreeRemoved t u node parent)
    {a n : NodeId} (ha : Ancestor u a n) : Ancestor t a n := by
  have key : ∀ (m x : NodeId), parentOf u m = some x → parentOf t m = some x := by
    intro m x hm
    by_cases hn : m = node
    · exfalso; rw [hn, hr.detached] at hm; simp at hm
    · rw [← hr.otherParents m hn]; exact hm
  induction ha with
  | step hp => exact Ancestor.step (key _ _ hp)
  | trans hp _ ih => exact Ancestor.trans (key _ _ hp) ih

/-- **`TreeRemoved` の結果も well-formed である。** -/
theorem treeRemoved_wellFormed {u : Tree} {node parent : NodeId} (hwf : WellFormed t)
    (hp : parentOf t node = some parent) (hr : TreeRemoved t u node parent) : WellFormed u where
  parent_child := by
    intro p pd hpd c hc
    have hcm : c ∈ childrenOf u p := by rw [childrenOf_eq hpd]; exact hc
    have hne : c ≠ node := by
      intro hce
      subst hce
      by_cases hpp : p = parent
      · subst hpp
        rw [hr.children] at hcm
        have hfil := List.mem_filter.mp hcm
        simp at hfil
      · rw [hr.otherChildren p hpp] at hcm
        have : parentOf t c = some p := parentOf_of_mem_childrenOf hwf hcm
        rw [hp] at this
        exact hpp (Option.some.inj this).symm
    have hct : c ∈ childrenOf t p := by
      by_cases hpp : p = parent
      · subst hpp
        rw [hr.children] at hcm
        exact (List.mem_filter.mp hcm).1
      · rw [hr.otherChildren p hpp] at hcm; exact hcm
    have hcp : parentOf u c = some p := by
      rw [hr.otherParents c hne]; exact parentOf_of_mem_childrenOf hwf hct
    obtain ⟨cd, hcd, hcdp⟩ := parentOf_eq_some hcp
    exact ⟨cd, hcd, hcdp⟩
  child_parent := by
    intro c cd p hcd hcdp
    have hcp : parentOf u c = some p := by rw [parentOf_of_get? hcd]; exact hcdp
    have hne : c ≠ node := by
      intro hce
      rw [hce, hr.detached] at hcp
      simp at hcp
    have hct : parentOf t c = some p := by rw [← hr.otherParents c hne]; exact hcp
    have hmem : c ∈ childrenOf t p := mem_childrenOf_of_parentOf hwf hct
    obtain ⟨pd, hpdt, -⟩ := exists_data_of_mem_childrenOf hmem
    obtain ⟨pd', hpd'⟩ := treeRemoved_exists hr hpdt
    refine ⟨pd', hpd', ?_⟩
    rw [← childrenOf_eq hpd']
    by_cases hpp : p = parent
    · subst hpp
      rw [hr.children]
      exact List.mem_filter.mpr ⟨hmem, by simp [hne]⟩
    · rw [hr.otherChildren p hpp]; exact hmem
  children_nodup := by
    intro n d hd
    obtain ⟨d₀, hd₀⟩ := treeRemoved_exists' hr hd
    have hnd : (childrenOf t n).Nodup := by
      rw [childrenOf_eq hd₀]; exact hwf.children_nodup n d₀ hd₀
    rw [← childrenOf_eq hd]
    by_cases hnp : n = parent
    · subst hnp
      rw [hr.children]
      exact List.Pairwise.sublist List.filter_sublist hnd
    · rw [hr.otherChildren n hnp]; exact hnd
  acyclic := fun n hn => hwf.acyclic n (treeRemoved_ancestor hr hn)
  ownerDocument_is_document := by
    intro n d hd
    obtain ⟨d₀, hd₀⟩ := treeRemoved_exists' hr hd
    obtain ⟨dd₀, hdd₀, hkind⟩ := hwf.ownerDocument_is_document n d₀ hd₀
    obtain ⟨hk, hdat, hat, hown, -⟩ := hr.sameData n d₀ d hd₀ hd
    rw [hown]
    obtain ⟨dd, hdd⟩ := treeRemoved_exists hr hdd₀
    obtain ⟨hk', -⟩ := hr.sameData _ dd₀ dd hdd₀ hdd
    exact ⟨dd, hdd, by rw [hk', hkind]⟩

/-- したがって `RemoveSpec` の結果も well-formed である。 -/
theorem removeSpec_wellFormed {out : DOMState} {node : NodeId} {suppress : Bool}
    (hwf : WellFormed s.tree) (hq : RemoveSpec s node suppress out) : WellFormed out.tree := by
  obtain ⟨parent, hpre, htr⟩ := hq.treeRemoved
  exact treeRemoved_wellFormed hwf hpre htr

/-! ## まとめ -/

/--
**record を積む段の congruence。**

`TreeRecordQueued` は observer についてしか言わないので、
木や range が動かないことは `ObserverOnly` から取る。
-/
theorem treeRecordQueued_congr (h : ObsEq s s') {o₁ o₂ : DOMState} {target : NodeId}
    {added removed : List NodeId} {oldPrev oldNext : Option NodeId} {suppress : Bool}
    (h₁ : TreeRecordQueued s o₁ target added removed oldPrev oldNext suppress)
    (h₂ : TreeRecordQueued s' o₂ target added removed oldPrev oldNext suppress)
    (f₁ : ObserverOnly s o₁) (f₂ : ObserverOnly s' o₂) : ObsEq o₁ o₂ := by
  have h₂' := treeRecordQueued_transport h h₂
  obtain ⟨hrec, hpend, hmt⟩ := treeRecordQueued_unique h₁ h₂'
  have hpo := treeRecordQueued_pending_unique h₁ h₂'
  refine ⟨?_, fun m => by rw [f₂.registrations, f₁.registrations]; exact h.registrationOrder m,
    hpo.symm⟩
  exact
    { tree := fun m => by rw [f₂.tree, f₁.tree]; exact h.tree m
      ranges := by rw [f₂.ranges, h.ranges, f₁.ranges]
      iterators := by rw [f₂.iterators, h.iterators, f₁.iterators]
      registrations := fun r => by
        rw [f₂.registrations, f₁.registrations]; exact h.registrations r
      records := fun mo => (hrec mo).symm
      pendingObservers := fun mo => (hpend mo).symm
      microtaskQueued := hmt.symm
      walkers := by rw [f₂.untouched.walkers, h.walkers, f₁.untouched.walkers]
      listeners := by rw [f₂.untouched.listeners, h.listeners, f₁.untouched.listeners]
      detachedAttrs := by
        rw [f₂.untouched.detachedAttrs, h.detachedAttrs, f₁.untouched.detachedAttrs] }


/--
**`RemoveSpec` の congruence。**

入力の観測が等しければ、出力の観測も等しい。
`insert` のように `remove` を途中に持つ関係の一意性は、これを繰り返して示す。
段（木から外す、transient を足す、record を積む）ごとの congruence を繋ぐ。
-/
theorem removeSpec_congr (hwf : WellFormed s.tree) (h : ObsEq s s')
    {s₁ s₂ : DOMState} {node : NodeId} {suppress : Bool}
    (h₁ : RemoveSpec s node suppress s₁) (h₂ : RemoveSpec s' node suppress s₂) :
    ObsEq s₁ s₂ := by
  obtain ⟨p₁, i₁, a₁, b₁, hp₁, hi₁, hd₁, ht₁, hq₁, hf₁⟩ := h₁
  obtain ⟨p₂, i₂, a₂, b₂, hp₂, hi₂, hd₂, ht₂, hq₂, hf₂⟩ := h₂
  -- step 1-2。parent と index は入力の観測から決まる。
  have hpe : p₂ = p₁ := by
    unfold RemovePre at hp₁ hp₂
    rw [h.tree.parentOf, hp₁] at hp₂
    exact (Option.some.inj hp₂).symm
  subst hpe
  have hie : i₂ = i₁ := by rw [hi₁, hi₂, h.tree.index]
  subst hie
  obtain ⟨nd, hnd, -⟩ := parentOf_eq_some hp₁
  have ha : ObsEq a₁ a₂ := detached_congr hwf h hnd hp₁ hd₁ hd₂
  have hb : ObsEq b₁ b₂ := transientAdded_congr ha ht₁ ht₂
  refine treeRecordQueued_congr hb hq₁ ?_ hf₁ hf₂
  unfold RecordQueued at hq₂
  rwa [h.tree.previousSibling, h.tree.nextSibling] at hq₂

/--
**`RemoveSpec` は観測を一つに決める。**

木の表現そのものは決まらない（association list なので同じ `get?` を持つ表現が複数ある）が、
観測できるもの（node ごとの registered observer list と pending の列を含む）はすべて一致する。

soundness（`Dom/Spec/RemoveSound.lean`）と合わせると、
`remove` の結果は関係が許す唯一の観測になっている、と言える。
-/
theorem removeSpec_deterministic (hwf : WellFormed s.tree) {s₁ s₂ : DOMState} {n : NodeId}
    {b : Bool} (h₁ : RemoveSpec s n b s₁) (h₂ : RemoveSpec s n b s₂) : ObsEq s₁ s₂ :=
  removeSpec_congr hwf (ObsEq.refl s) h₁ h₂

/--
**列に対する `remove` の congruence。**

途中の状態は観測としてしか一致しないので、各段で `removeSpec_congr` を使い、
次の段の前提として `removeSpec_wellFormed` を渡す。
-/
theorem removeEachSpec_congr {ns : List NodeId} {b : Bool} :
    ∀ {s s' s₁ s₂ : DOMState}, WellFormed s.tree → ObsEq s s' →
      RemoveEachSpec s ns b s₁ → RemoveEachSpec s' ns b s₂ → ObsEq s₁ s₂ := by
  induction ns with
  | nil =>
    intro s s' s₁ s₂ _ h h₁ h₂
    cases h₁; cases h₂; exact h
  | cons n ns ih =>
    intro s s' s₁ s₂ hwf h h₁ h₂
    cases h₁ with
    | cons hr₁ hrest₁ =>
      cases h₂ with
      | cons hr₂ hrest₂ =>
        exact ih (removeSpec_wellFormed hwf hr₁) (removeSpec_congr hwf h hr₁ hr₂) hrest₁ hrest₂

/-- 列に対する `remove` の結果も well-formed である。 -/
theorem removeEachSpec_wellFormed {ns : List NodeId} {b : Bool} :
    ∀ {s out : DOMState}, WellFormed s.tree → RemoveEachSpec s ns b out → WellFormed out.tree := by
  induction ns with
  | nil => intro s out hwf h; cases h; exact hwf
  | cons n ns ih =>
    intro s out hwf h
    cases h with
    | cons hr hrest => exact ih (removeSpec_wellFormed hwf hr) hrest


/-- `remove` は ancestor を増やさない。 -/
theorem removeSpec_ancestor {out : DOMState} {node : NodeId} {suppress : Bool}
    (hq : RemoveSpec s node suppress out) {a m : NodeId} (h : Ancestor out.tree a m) :
    Ancestor s.tree a m := by
  obtain ⟨parent, -, htr⟩ := hq.treeRemoved
  exact treeRemoved_ancestor htr h

/-- 列に対する `remove` も ancestor を増やさない。 -/
theorem removeEachSpec_ancestor {ns : List NodeId} {b : Bool} :
    ∀ {s out : DOMState}, RemoveEachSpec s ns b out →
      ∀ {a m : NodeId}, Ancestor out.tree a m → Ancestor s.tree a m := by
  induction ns with
  | nil => intro s out h a m ha; cases h; exact ha
  | cons n ns ih =>
    intro s out h a m ha
    cases h with
    | cons hr hrest => exact removeSpec_ancestor hr (ih hrest ha)


/--
`remove` は、外した node の parent 以外の kind と children を変えない。

`replace` のように `remove` を挟んで同じ node を読み直す関係が使う。
-/
theorem removeSpec_data {out : DOMState} {c : NodeId} {b : Bool}
    (hq : RemoveSpec s c b out) {m : NodeId} {d : NodeData} (hd : s.tree.get? m = some d)
    (hm : ∀ p, parentOf s.tree c = some p → m ≠ p) :
    ∃ d', out.tree.get? m = some d' ∧ d'.kind = d.kind ∧ d'.children = d.children := by
  obtain ⟨parent, hpre, htr⟩ := hq.treeRemoved
  obtain ⟨d', hd'⟩ := treeRemoved_exists htr hd
  obtain ⟨hk, -⟩ := htr.sameData m d d' hd hd'
  refine ⟨d', hd', hk, ?_⟩
  have hch : childrenOf out.tree m = childrenOf s.tree m := htr.otherChildren m (hm parent hpre)
  rw [childrenOf_eq hd', childrenOf_eq hd] at hch
  exact hch

end Dom.Spec
