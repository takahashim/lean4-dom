import Dom.Spec.Remove
import Dom.Properties.TreeOrder

/-!
# `RemoveSpec` は結果を一つに決める

`Dom/Spec/Remove.lean` の関係が、実行関数を縛るだけの強さを持っていることを示す。
関係が緩ければ soundness は簡単に成り立ってしまうので、これが無いと二層に分けた意味が薄い。

木の表現（association list）は観測を決めても一意には決まらないので、
結論は **観測の一致** として述べる（`Dom/Observation.lean` の `Observation` が見るもの）。

* 各 node の `get?`
* live range と NodeIterator
* observer ごとの record queue と pending / microtask
* registered observer list（順序は決めていないので、所属の一致）
-/

namespace Dom.Spec

open Dom

/-! ## component ごとの一意性 -/

theorem boundaryAdjusted_unique {t : Tree} {node parent : NodeId} {index : Nat}
    {bp bp₁ bp₂ : BoundaryPoint}
    (h₁ : BoundaryAdjusted t node parent index bp bp₁)
    (h₂ : BoundaryAdjusted t node parent index bp bp₂) : bp₁ = bp₂ := by
  rcases h₁ with ⟨ha, he⟩ | ⟨ha, hb, hc, he⟩ | ⟨ha, hb, he⟩ <;>
    rcases h₂ with ⟨ha', he'⟩ | ⟨ha', hb', hc', he'⟩ | ⟨ha', hb', he'⟩ <;>
    rw [he, he'] <;>
    first
      | rfl
      | exact absurd ha ha'
      | exact absurd ha' ha
      | exact absurd ⟨hb, hc⟩ hb'
      | exact absurd ⟨hb', hc'⟩ hb

/-- 仕様の「最初の following」は一つしかない。 -/
theorem firstFollowingOutside_unique {t : Tree} (hwf : WellFormed t) {rt n : NodeId}
    {nd : NodeData} (hn : t.get? n = some nd) {next₁ next₂ : NodeId}
    (h₁ : FirstFollowingOutside t rt n next₁) (h₂ : FirstFollowingOutside t rt n next₂) :
    next₁ = next₂ := by
  by_cases he : next₁ = next₂
  · exact he
  · exfalso
    obtain ⟨rd, hrd⟩ := exists_data_of_inclusiveAncestor hwf (root_inclusive_ancestor t n) hn
    have hmem : ∀ x, precedes t n x = true → InclusiveDescendant t x (root t n) := by
      intro x hx
      exact (mem_preorder_iff hwf hrd x).mp (mem_of_precedesIn (treeOrder t n) hx)
    have h12 : precedes t next₁ next₂ = false := h₂.2.2.2 next₁ h₁.1 h₁.2.1 h₁.2.2.1
    have h21 : precedes t next₂ next₁ = false := h₁.2.2.2 next₂ h₂.1 h₂.2.1 h₂.2.2.1
    rcases precedes_total hwf hrd (hmem next₁ h₁.1) (hmem next₂ h₂.1) he with h | h
    · rw [h12] at h; simp at h
    · rw [h21] at h; simp at h

/-- 仕様の step 3 が指す node も一つしかない。 -/
theorem lastBeforeRemoval_unique {t : Tree} (hwf : WellFormed t) {n p : NodeId}
    (hp : parentOf t n = some p) {m₁ m₂ : NodeId}
    (h₁ : LastBeforeRemoval t n m₁) (h₂ : LastBeforeRemoval t n m₂) : m₁ = m₂ := by
  rcases h₁ with ⟨hs₁, hp₁⟩ | ⟨prev₁, hs₁, ha₁, hl₁⟩ <;>
    rcases h₂ with ⟨hs₂, hp₂⟩ | ⟨prev₂, hs₂, ha₂, hl₂⟩
  · exact Option.some.inj (hp₁ ▸ hp₂ : some m₁ = some m₂)
  · rw [hs₁] at hs₂; simp at hs₂
  · rw [hs₂] at hs₁; simp at hs₁
  · have hprev : prev₁ = prev₂ := Option.some.inj (hs₁ ▸ hs₂ : some prev₁ = some prev₂)
    subst hprev
    by_cases he : m₁ = m₂
    · exact he
    · exfalso
      obtain ⟨pd, hpd, -⟩ := parentOf_eq_some
        (parentOf_of_mem_childrenOf hwf (previousSibling_mem_children hp hs₁))
      rcases precedes_total hwf hpd ha₁ ha₂ he with h | h
      · rw [hl₁ m₂ ha₂] at h; simp at h
      · rw [hl₂ m₁ ha₁] at h; simp at h

/-- node pointer の更新も一つに決まる。 -/
theorem pointerAdjusted_unique {t : Tree} (hwf : WellFormed t) {rt n : NodeId}
    {nd : NodeData} (hn : t.get? n = some nd) {p : NodeId} (hp : parentOf t n = some p)
    {ptr q₁ q₂ : NodeId × Bool}
    (h₁ : PointerAdjusted t rt n ptr q₁) (h₂ : PointerAdjusted t rt n ptr q₂) : q₁ = q₂ := by
  cases h₁ with
  | untouched hc₁ =>
    cases h₂ with
    | untouched _ => rfl
    | forward ha₂ hr₂ _ =>
      rcases hc₁ with hc | hc
      · exact absurd ha₂ hc
      · exact absurd hc hr₂
    | backward ha₂ hr₂ _ _ =>
      rcases hc₁ with hc | hc
      · exact absurd ha₂ hc
      · exact absurd hc hr₂
  | forward ha₁ hr₁ hf₁ =>
    cases h₂ with
    | untouched hc₂ =>
      rcases hc₂ with hc | hc
      · exact absurd ha₁ hc
      · exact absurd hc hr₁
    | forward _ _ hf₂ => rw [firstFollowingOutside_unique hwf hn hf₁ hf₂]
    | backward _ _ hb₂ _ =>
      rcases hb₂ with hb | hb
      · simp at hb
      · exact absurd hf₁ (hb _)
  | backward ha₁ hr₁ hb₁ hl₁ =>
    cases h₂ with
    | untouched hc₂ =>
      rcases hc₂ with hc | hc
      · exact absurd ha₁ hc
      · exact absurd hc hr₁
    | forward _ _ hf₂ =>
      rcases hb₁ with hb | hb
      · simp at hb
      · exact absurd hf₂ (hb _)
    | backward _ _ _ hl₂ => rw [lastBeforeRemoval_unique hwf hp hl₁ hl₂]

/-! ## 観測が一つに決まる -/

/-- 木の観測（各 node の `get?`）は一つに決まる。 -/
theorem treeRemoved_unique {t t₁ t₂ : Tree} {node parent : NodeId}
    (h₁ : TreeRemoved t t₁ node parent) (h₂ : TreeRemoved t t₂ node parent) :
    ∀ m, t₁.get? m = t₂.get? m := by
  intro m
  cases hm : t.get? m with
  | none =>
    have e₁ : t₁.get? m = none := by
      have hs := h₁.sameNodes m
      rw [hm] at hs
      simpa using hs
    have e₂ : t₂.get? m = none := by
      have hs := h₂.sameNodes m
      rw [hm] at hs
      simpa using hs
    rw [e₁, e₂]
  | some d =>
    obtain ⟨d₁, hd₁⟩ : ∃ d₁, t₁.get? m = some d₁ := by
      have hs := h₁.sameNodes m
      rw [hm] at hs
      exact Option.isSome_iff_exists.mp (by simpa using hs)
    obtain ⟨d₂, hd₂⟩ : ∃ d₂, t₂.get? m = some d₂ := by
      have hs := h₂.sameNodes m
      rw [hm] at hs
      exact Option.isSome_iff_exists.mp (by simpa using hs)
    -- parent と children 以外は元のまま。
    obtain ⟨k₁, s₁, a₁, o₁, ns₁, p₁, l₁, h₁'⟩ := h₁.sameData m d d₁ hm hd₁
    obtain ⟨k₂, s₂, a₂, o₂, ns₂, p₂, l₂, h₂'⟩ := h₂.sameData m d d₂ hm hd₂
    -- parent は `parentOf`、children は `childrenOf` から決まる。
    have hpar : d₁.parent = d₂.parent := by
      have e₁ : parentOf t₁ m = if m = node then none else parentOf t m := by
        by_cases he : m = node
        · rw [if_pos he, he]; exact h₁.detached
        · rw [if_neg he]; exact h₁.otherParents m he
      have e₂ : parentOf t₂ m = if m = node then none else parentOf t m := by
        by_cases he : m = node
        · rw [if_pos he, he]; exact h₂.detached
        · rw [if_neg he]; exact h₂.otherParents m he
      have : parentOf t₁ m = parentOf t₂ m := by rw [e₁, e₂]
      rw [parentOf_eq, parentOf_eq, hd₁, hd₂] at this
      simpa using this
    have hch : d₁.children = d₂.children := by
      have e₁ : childrenOf t₁ m = if m = parent then
          (childrenOf t parent).filter (· != node) else childrenOf t m := by
        by_cases he : m = parent
        · rw [if_pos he, he]; exact h₁.children
        · rw [if_neg he]; exact h₁.otherChildren m he
      have e₂ : childrenOf t₂ m = if m = parent then
          (childrenOf t parent).filter (· != node) else childrenOf t m := by
        by_cases he : m = parent
        · rw [if_pos he, he]; exact h₂.children
        · rw [if_neg he]; exact h₂.otherChildren m he
      have : childrenOf t₁ m = childrenOf t₂ m := by rw [e₁, e₂]
      rw [childrenOf_eq hd₁, childrenOf_eq hd₂] at this
      simpa using this
    rw [hd₁, hd₂]
    have : d₁ = d₂ := by
      cases d₁; cases d₂
      simp_all
    rw [this]

/-- live range も一つに決まる。 -/
theorem rangeAdjusted_unique {s s₁ s₂ : DOMState} {node parent : NodeId} {index : Nat}
    (h₁ : RangeAdjusted s s₁ node parent index) (h₂ : RangeAdjusted s s₂ node parent index) :
    s₁.ranges = s₂.ranges := by
  refine List.ext_getElem? (fun i => ?_)
  rcases hr : s.ranges[i]? with _ | r
  · have e₁ : s₁.ranges[i]? = none := by
      rw [List.getElem?_eq_none_iff] at hr ⊢; rw [h₁.1]; exact hr
    have e₂ : s₂.ranges[i]? = none := by
      rw [List.getElem?_eq_none_iff] at hr ⊢; rw [h₂.1]; exact hr
    rw [e₁, e₂]
  · obtain ⟨r₁, hr₁⟩ : ∃ r₁, s₁.ranges[i]? = some r₁ := by
      rcases hq : s₁.ranges[i]? with _ | r₁
      · rw [List.getElem?_eq_none_iff, h₁.1, ← List.getElem?_eq_none_iff] at hq
        rw [hq] at hr; simp at hr
      · exact ⟨r₁, rfl⟩
    obtain ⟨r₂, hr₂⟩ : ∃ r₂, s₂.ranges[i]? = some r₂ := by
      rcases hq : s₂.ranges[i]? with _ | r₂
      · rw [List.getElem?_eq_none_iff, h₂.1, ← List.getElem?_eq_none_iff] at hq
        rw [hq] at hr; simp at hr
      · exact ⟨r₂, rfl⟩
    obtain ⟨hs₁, he₁⟩ := h₁.2 i r r₁ hr hr₁
    obtain ⟨hs₂, he₂⟩ := h₂.2 i r r₂ hr hr₂
    rw [hr₁, hr₂]
    have hst : r₁.start = r₂.start := boundaryAdjusted_unique hs₁ hs₂
    have hen : r₁.«end» = r₂.«end» := boundaryAdjusted_unique he₁ he₂
    have : r₁ = r₂ := by cases r₁; cases r₂; simp_all
    rw [this]

/-- NodeIterator も一つに決まる。 -/
theorem iteratorAdjusted_unique {s s₁ s₂ : DOMState} {n p : NodeId} (hwf : WellFormed s.tree)
    {nd : NodeData} (hn : s.tree.get? n = some nd) (hp : parentOf s.tree n = some p)
    (h₁ : IteratorAdjusted s s₁ n) (h₂ : IteratorAdjusted s s₂ n) :
    s₁.iterators = s₂.iterators := by
  refine List.ext_getElem? (fun i => ?_)
  rcases hit : s.iterators[i]? with _ | it
  · have e₁ : s₁.iterators[i]? = none := by
      rw [List.getElem?_eq_none_iff] at hit ⊢; rw [h₁.1]; exact hit
    have e₂ : s₂.iterators[i]? = none := by
      rw [List.getElem?_eq_none_iff] at hit ⊢; rw [h₂.1]; exact hit
    rw [e₁, e₂]
  · obtain ⟨it₁, hit₁⟩ : ∃ it₁, s₁.iterators[i]? = some it₁ := by
      rcases hq : s₁.iterators[i]? with _ | it₁
      · rw [List.getElem?_eq_none_iff, h₁.1, ← List.getElem?_eq_none_iff] at hq
        rw [hq] at hit; simp at hit
      · exact ⟨it₁, rfl⟩
    obtain ⟨it₂, hit₂⟩ : ∃ it₂, s₂.iterators[i]? = some it₂ := by
      rcases hq : s₂.iterators[i]? with _ | it₂
      · rw [List.getElem?_eq_none_iff, h₂.1, ← List.getElem?_eq_none_iff] at hq
        rw [hq] at hit; simp at hit
      · exact ⟨it₂, rfl⟩
    obtain ⟨hr₁, hw₁, hpt₁⟩ := h₁.2 i it it₁ hit hit₁
    obtain ⟨hr₂, hw₂, hpt₂⟩ := h₂.2 i it it₂ hit hit₂
    rw [hit₁, hit₂]
    by_cases hc : ownerDocumentOf s.tree it.root = ownerDocumentOf s.tree n
    · rw [if_pos hc] at hpt₁ hpt₂
      have hq := pointerAdjusted_unique hwf hn hp hpt₁ hpt₂
      have hfst : it₁.reference = it₂.reference := congrArg Prod.fst hq
      have hsnd : it₁.pointerBeforeReference = it₂.pointerBeforeReference := congrArg Prod.snd hq
      have : it₁ = it₂ := by cases it₁; cases it₂; simp_all
      rw [this]
    · rw [if_neg hc] at hpt₁ hpt₂
      rw [hpt₁, hpt₂]

/-- registered observer list は、順序を別にすれば一つに決まる。 -/
theorem transientAdded_unique {s s₁ s₂ : DOMState} {node parent : NodeId}
    (h₁ : TransientAdded s s₁ node parent) (h₂ : TransientAdded s s₂ node parent) :
    ∀ r, r ∈ s₁.registrations ↔ r ∈ s₂.registrations := by
  have key : ∀ (sa sb : DOMState), TransientAdded s sa node parent →
      TransientAdded s sb node parent → ∀ r, r ∈ sa.registrations → r ∈ sb.registrations := by
    intro sa sb ha hb r hr
    by_cases hold : r ∈ s.registrations
    · exact hb.1 r hold
    · obtain ⟨src, hsrc, hsame, hsub, hanc, hnode, htr, hsrcnode⟩ := ha.2.2 r hr hold
      obtain ⟨r', hr', hsame', hnode', htr', hsrcnode'⟩ := hb.2.1 src hsrc hsub hanc
      -- 同じ src から作った transient は、field がすべて一致する。
      have : r = r' := by
        obtain ⟨o, st, cl, at1, aov, af, cd, cdov⟩ := hsame
        obtain ⟨o', st', cl', at1', aov', af', cd', cdov'⟩ := hsame'
        cases r; cases r'
        simp_all
      rw [this]
      exact hr'
  exact fun r => ⟨key s₁ s₂ h₁ h₂ r, key s₂ s₁ h₂ h₁ r⟩

/-- record queue・pending・microtask も一つに決まる。 -/
theorem treeRecordQueued_unique {s s₁ s₂ : DOMState} {target : NodeId}
    {added removed : List NodeId} {oldPrev oldNext : Option NodeId} {suppress : Bool}
    (h₁ : TreeRecordQueued s s₁ target added removed oldPrev oldNext suppress)
    (h₂ : TreeRecordQueued s s₂ target added removed oldPrev oldNext suppress) :
    (∀ mo : Nat, (s₁.observers[mo]?).map (·.records) = (s₂.observers[mo]?).map (·.records)) ∧
      (∀ mo : Nat, mo ∈ s₁.pendingObservers ↔ mo ∈ s₂.pendingObservers) ∧
      s₁.microtaskQueued = s₂.microtaskQueued := by
  -- 長さが同じで、各 observer の queue が同じ規則で決まる、という形は両方に共通である。
  have common : ∀ (sa sb : DOMState), sa.observers.length = s.observers.length →
      sb.observers.length = s.observers.length →
      (∀ (mo : Nat) (o oa : ObserverState), s.observers[mo]? = some o →
        sa.observers[mo]? = some oa → ∀ (ob : ObserverState), sb.observers[mo]? = some ob →
        oa.records = ob.records) →
      ∀ mo : Nat, (sa.observers[mo]?).map (·.records) = (sb.observers[mo]?).map (·.records) := by
    intro sa sb hla hlb hrec mo
    rcases ho : s.observers[mo]? with _ | o
    · have ea : sa.observers[mo]? = none := by
        rw [List.getElem?_eq_none_iff] at ho ⊢; rw [hla]; exact ho
      have eb : sb.observers[mo]? = none := by
        rw [List.getElem?_eq_none_iff] at ho ⊢; rw [hlb]; exact ho
      rw [ea, eb]
    · obtain ⟨oa, hoa⟩ : ∃ oa, sa.observers[mo]? = some oa := by
        rcases hq : sa.observers[mo]? with _ | oa
        · rw [List.getElem?_eq_none_iff, hla, ← List.getElem?_eq_none_iff] at hq
          rw [hq] at ho; simp at ho
        · exact ⟨oa, rfl⟩
      obtain ⟨ob, hob⟩ : ∃ ob, sb.observers[mo]? = some ob := by
        rcases hq : sb.observers[mo]? with _ | ob
        · rw [List.getElem?_eq_none_iff, hlb, ← List.getElem?_eq_none_iff] at hq
          rw [hq] at ho; simp at ho
        · exact ⟨ob, rfl⟩
      rw [hoa, hob]
      simp only [Option.map_some, Option.some.injEq]
      exact hrec mo o oa ho hoa ob hob
  unfold TreeRecordQueued at h₁ h₂
  split at h₁
  · next hsup =>
    rw [if_pos hsup] at h₂
    obtain ⟨hl₁, hr₁, hp₁, hm₁⟩ := h₁
    obtain ⟨hl₂, hr₂, hp₂, hm₂⟩ := h₂
    refine ⟨common s₁ s₂ hl₁ hl₂ (fun mo o oa ho hoa ob hob => ?_), ?_, ?_⟩
    · rw [hr₁ mo o oa ho hoa, hr₂ mo o ob ho hob]
    · exact fun mo => (hp₁ mo).trans (hp₂ mo).symm
    · rw [hm₁, hm₂]
  · next hsup =>
    rw [if_neg hsup] at h₂
    obtain ⟨hl₁, hr₁, hin₁, hkeep₁, hout₁, hm₁⟩ := h₁
    obtain ⟨hl₂, hr₂, hin₂, hkeep₂, hout₂, hm₂⟩ := h₂
    refine ⟨common s₁ s₂ hl₁ hl₂ (fun mo o oa ho hoa ob hob => ?_), ?_, ?_⟩
    · by_cases hint : InterestedInChildList s mo target
      · rw [(hr₁ mo o oa ho hoa).1 hint, (hr₂ mo o ob ho hob).1 hint]
      · rw [(hr₁ mo o oa ho hoa).2 hint, (hr₂ mo o ob ho hob).2 hint]
    · intro mo
      constructor
      · intro hm
        rcases hout₁ mo hm with hold | hint
        · exact hkeep₂ mo hold
        · exact hin₂ mo hint
      · intro hm
        rcases hout₂ mo hm with hold | hint
        · exact hkeep₁ mo hold
        · exact hin₁ mo hint
    · rw [hm₁, hm₂]

/-- `remove` の step 21 についての言い換え。 -/
theorem recordQueued_unique {s s₁ s₂ : DOMState} {node parent : NodeId}
    {oldPrev oldNext : Option NodeId} {suppress : Bool}
    (h₁ : RecordQueued s s₁ node parent oldPrev oldNext suppress)
    (h₂ : RecordQueued s s₂ node parent oldPrev oldNext suppress) :
    (∀ mo : Nat, (s₁.observers[mo]?).map (·.records) = (s₂.observers[mo]?).map (·.records)) ∧
      (∀ mo : Nat, mo ∈ s₁.pendingObservers ↔ mo ∈ s₂.pendingObservers) ∧
      s₁.microtaskQueued = s₂.microtaskQueued :=
  treeRecordQueued_unique h₁ h₂

/-! ## まとめ -/

/--
**`RemoveSpec` は観測を一つに決める。**

木の表現そのものは決まらない（association list なので同じ `get?` を持つ表現が複数ある）が、
観測できるものはすべて一致する。registered observer list だけは順序を決めていないので
所属の一致である。

soundness（`Dom/Spec/RemoveSound.lean`）と合わせると、
`remove` の結果は関係が許す唯一の観測になっている、と言える。
-/
theorem removeSpec_deterministic {s s₁ s₂ : DOMState} {n : NodeId} {b : Bool}
    (hwf : WellFormed s.tree) (h₁ : RemoveSpec s n b s₁) (h₂ : RemoveSpec s n b s₂) :
    (∀ m, s₁.tree.get? m = s₂.tree.get? m) ∧
      s₁.ranges = s₂.ranges ∧
      s₁.iterators = s₂.iterators ∧
      (∀ r, r ∈ s₁.registrations ↔ r ∈ s₂.registrations) ∧
      (∀ mo : Nat, (s₁.observers[mo]?).map (·.records) = (s₂.observers[mo]?).map (·.records)) ∧
      (∀ mo : Nat, mo ∈ s₁.pendingObservers ↔ mo ∈ s₂.pendingObservers) ∧
      s₁.microtaskQueued = s₂.microtaskQueued := by
  obtain ⟨p₁, i₁, hp₁, hi₁, hr₁, hit₁, ht₁, htr₁, hrec₁⟩ := h₁
  obtain ⟨p₂, i₂, hp₂, hi₂, hr₂, hit₂, ht₂, htr₂, hrec₂⟩ := h₂
  -- parent と index は元の状態から決まる。
  have hpe : p₁ = p₂ := Option.some.inj (hp₁ ▸ hp₂ : some p₁ = some p₂)
  subst hpe
  have hie : i₁ = i₂ := by rw [hi₁, hi₂]
  subst hie
  obtain ⟨nd, hnd, -⟩ := parentOf_eq_some hp₁
  obtain ⟨hobs, hpend, hmt⟩ := recordQueued_unique hrec₁ hrec₂
  exact ⟨treeRemoved_unique ht₁ ht₂, rangeAdjusted_unique hr₁ hr₂,
    iteratorAdjusted_unique hwf hnd hp₁ hit₁ hit₂, transientAdded_unique htr₁ htr₂,
    hobs, hpend, hmt⟩

end Dom.Spec
