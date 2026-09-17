import Dom.Spec.RemoveDeterministic
import Dom.Spec.ObsEq

/-!
# 観測が等しい状態は `RemoveSpec` に同じ答えを返させる

`Dom/Spec/RemoveDeterministic.lean` は「同じ状態から出た二つの結果は観測が一致する」を言う。
関係を繋いだもの（`insert` のように途中に `remove` を持つもの）の一意性には、
それでは足りない。途中の状態は観測としてしか一致しないからである。

そこで **congruence**「入力の観測が等しければ出力の観測も等しい」を示す。

やり方は二段である。

1. **transport**：`RemoveSpec` の各 component は観測の語彙だけで書かれているので、
   入力を観測の等しい状態に差し替えても成り立つ。
2. 差し替えてしまえば両方が同じ入力から出た結果になるので、
   `removeSpec_deterministic` がそのまま使える。

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

theorem interestedInChildList_iff (h : ObsEq s s') {mo : Nat} {target : NodeId} :
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
    obtain ⟨hlen, hrec, hpend, hmt⟩ := hq
    refine ⟨by rw [hlen, h.observers_length], ?_, ?_, ?_⟩
    · intro mo o o' ho ho'
      obtain ⟨o₂, ho₂, hre⟩ := h.exists_observer ho
      rw [hrec mo o₂ o' ho₂ ho', hre]
    · exact fun mo => (hpend mo).trans (h.pendingObservers mo)
    · rw [hmt, h.microtaskQueued]
  | false =>
    obtain ⟨hlen, hrec, hin, hkeep, hout, hmt⟩ := hq
    refine ⟨by rw [hlen, h.observers_length], ?_, ?_, ?_, ?_, hmt⟩
    · intro mo o o' ho ho'
      obtain ⟨o₂, ho₂, hre⟩ := h.exists_observer ho
      obtain ⟨h1, h2⟩ := hrec mo o₂ o' ho₂ ho'
      refine ⟨fun hi => by rw [h1 (interestedInChildList_iff h |>.mpr hi), hre], ?_⟩
      exact fun hi => by rw [h2 fun hc => hi (interestedInChildList_iff h |>.mp hc), hre]
    · exact fun mo hi => hin mo ((interestedInChildList_iff h).mpr hi)
    · exact fun mo hm => hkeep mo ((h.pendingObservers mo).mpr hm)
    · intro mo hm
      rcases hout mo hm with hc | hc
      · exact Or.inl ((h.pendingObservers mo).mp hc)
      · exact Or.inr ((interestedInChildList_iff h).mp hc)

theorem rangeAdjusted_transport (h : ObsEq s s') {out : DOMState} {node parent : NodeId}
    {index : Nat} (hq : RangeAdjusted s' out node parent index) :
    RangeAdjusted s out node parent index := by
  obtain ⟨hlen, hadj⟩ := hq
  refine ⟨by rw [hlen, h.ranges], ?_⟩
  intro i r r' hr hr'
  obtain ⟨h1, h2⟩ := hadj i r r' (by rw [h.ranges]; exact hr) hr'
  exact ⟨boundaryAdjusted_transport h.tree h1, boundaryAdjusted_transport h.tree h2⟩

theorem iteratorAdjusted_transport (hwf : WellFormed s.tree) (h : ObsEq s s') {out : DOMState}
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

theorem transientAdded_transport (h : ObsEq s s') {out : DOMState} {node parent : NodeId}
    (hq : TransientAdded s' out node parent) : TransientAdded s out node parent := by
  obtain ⟨hkeep, hin, hnew⟩ := hq
  refine ⟨fun r hr => hkeep r ((h.registrations r).mpr hr), ?_, ?_⟩
  · intro src hsrc hsub ha
    exact hin src ((h.registrations src).mpr hsrc) hsub (h.tree.inclusiveAncestor_iff.mpr ha)
  · intro r hr hnot
    obtain ⟨src, hsrc, hsame, hsub, ha, rest⟩ :=
      hnew r hr fun hc => hnot ((h.registrations r).mp hc)
    exact ⟨src, (h.registrations src).mp hsrc, hsame, hsub,
      h.tree.inclusiveAncestor_iff.mp ha, rest⟩


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
  obtain ⟨parent, index, hpre, -, -, -, htr, -, -⟩ := hq
  exact treeRemoved_wellFormed hwf hpre htr

/-! ## まとめ -/

/-- **`RemoveSpec` は観測の等しい入力に差し替えられる。** -/
theorem removeSpec_transport (hwf : WellFormed s.tree) (h : ObsEq s s') {out : DOMState}
    {node : NodeId} {suppress : Bool} (hq : RemoveSpec s' node suppress out) :
    RemoveSpec s node suppress out := by
  obtain ⟨parent, index, hpre, hidx, hr, hit, htr, htn, hrec, hun⟩ := hq
  refine ⟨parent, index, ?_, ?_, rangeAdjusted_transport h hr,
    iteratorAdjusted_transport hwf h hit, treeRemoved_transport h.tree htr,
    transientAdded_transport h htn, ?_, h.untouched.trans hun⟩
  · show parentOf s.tree node = some parent
    rw [← h.tree.parentOf]; exact hpre
  · rw [hidx, h.tree.index]
  · have := treeRecordQueued_transport (target := parent) (added := []) (removed := [node]) h hrec
    rwa [h.tree.previousSibling, h.tree.nextSibling] at this

/--
**`RemoveSpec` の congruence。**

入力の観測が等しければ、出力の観測も等しい。
`insert` のように `remove` を途中に持つ関係の一意性は、これを繰り返して示す。
-/
theorem removeSpec_congr (hwf : WellFormed s.tree) (h : ObsEq s s')
    {s₁ s₂ : DOMState} {node : NodeId} {suppress : Bool}
    (h₁ : RemoveSpec s node suppress s₁) (h₂ : RemoveSpec s' node suppress s₂) :
    ObsEq s₁ s₂ := by
  have h₂' : RemoveSpec s node suppress s₂ := removeSpec_transport hwf h h₂
  obtain ⟨htree, hrng, hit, hreg, hrec, hpend, hmt, hw, hl, ha⟩ :=
    removeSpec_deterministic hwf h₁ h₂'
  exact ⟨fun m => (htree m).symm, hrng.symm, hit.symm, fun r => (hreg r).symm,
    fun mo => (hrec mo).symm, fun mo => (hpend mo).symm, hmt.symm, hw.symm, hl.symm, ha.symm⟩


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
  obtain ⟨hrec, hpend, hmt⟩ := treeRecordQueued_unique h₁ (treeRecordQueued_transport h h₂)
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


/-- `remove` は ancestor を増やさない。 -/
theorem removeSpec_ancestor {out : DOMState} {node : NodeId} {suppress : Bool}
    (hq : RemoveSpec s node suppress out) {a m : NodeId} (h : Ancestor out.tree a m) :
    Ancestor s.tree a m := by
  obtain ⟨parent, -, -, -, -, -, htr, -, -⟩ := hq
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
  obtain ⟨parent, -, hpre, -, -, -, htr, -, -⟩ := hq
  obtain ⟨d', hd'⟩ := treeRemoved_exists htr hd
  obtain ⟨hk, -⟩ := htr.sameData m d d' hd hd'
  refine ⟨d', hd', hk, ?_⟩
  have hch : childrenOf out.tree m = childrenOf s.tree m := htr.otherChildren m (hm parent hpre)
  rw [childrenOf_eq hd', childrenOf_eq hd] at hch
  exact hch

end Dom.Spec
