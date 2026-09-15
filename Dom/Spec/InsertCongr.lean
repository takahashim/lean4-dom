import Dom.Spec.AdoptCongr
import Dom.Spec.Insert
import Dom.Properties.Mutation

/-!
# `insert` の congruence

`Dom/Spec/RemoveCongr.lean` / `Dom/Spec/AdoptCongr.lean` と同じ目的で、
`InsertSpec` について「入力の観測が等しければ出力の観測も等しい」を示す。

`insert` は step 4 で `remove` を、step 7.1 で `adopt` を呼ぶので、
congruence もその二つを composition する。

`TreeInserted` が well-formed を保つには
「入れる node がすでに parent を持っていない」ことと
「入れる node が `parent` の inclusive ancestor でない」ことが要る。
どちらも §4.2.1 の pre-insertion validity が保証するもので、
`insert` 本体は前提として受け取る。
-/

namespace Dom.Spec

open Dom

variable {t tb u ub : Tree} {s sb : DOMState} {parent node : NodeId} {child : Option NodeId}

/-! ## step 7.2-7.3：木への挿入 -/

theorem treeInserted_exists (hi : TreeInserted t u parent node child) {m : NodeId} {d : NodeData}
    (hd : t.get? m = some d) : ∃ d', u.get? m = some d' := by
  have hs := hi.sameNodes m
  rw [hd] at hs
  cases h' : u.get? m with
  | none => rw [h'] at hs; simp at hs
  | some d' => exact ⟨d', rfl⟩

theorem treeInserted_exists' (hi : TreeInserted t u parent node child) {m : NodeId}
    {d' : NodeData} (hd : u.get? m = some d') : ∃ d, t.get? m = some d := by
  have hs := hi.sameNodes m
  rw [hd] at hs
  cases h' : t.get? m with
  | none => rw [h'] at hs; simp at hs
  | some d => exact ⟨d, rfl⟩

theorem treeInserted_parentOf (hi : TreeInserted t u parent node child) (m : NodeId) :
    parentOf u m = if m = node then some parent else parentOf t m := by
  by_cases he : m = node
  · rw [if_pos he, he]; exact hi.attached
  · rw [if_neg he]; exact hi.otherParents m he

theorem treeInserted_childrenOf (hi : TreeInserted t u parent node child) (m : NodeId) :
    childrenOf u m =
      if m = parent then Dom.ListUtil.insertBefore (childrenOf t parent) child node
      else childrenOf t m := by
  by_cases he : m = parent
  · rw [if_pos he, he]; exact hi.children
  · rw [if_neg he]; exact hi.otherChildren m he

/-- **`TreeInserted` の結果も well-formed である。** -/
theorem treeInserted_wellFormed (hwf : WellFormed t) (hnp : parentOf t node = none)
    (hanc : ¬ InclusiveAncestor t node parent) (hi : TreeInserted t u parent node child) :
    WellFormed u := by
  have hne : node ≠ parent := fun he => hanc (Or.inl he)
  have hnodemem : node ∉ childrenOf t parent := by
    intro hmem
    rw [parentOf_of_mem_childrenOf hwf hmem] at hnp
    simp at hnp
  refine wellFormed_of ?_ ?_ ?_ ?_
  · intro c p
    rw [treeInserted_parentOf hi, treeInserted_childrenOf hi]
    by_cases hcn : c = node
    · rw [if_pos hcn]
      by_cases hqp : p = parent
      · rw [if_pos hqp, Dom.ListUtil.mem_insertBefore]
        exact ⟨fun _ => Or.inl hcn, fun _ => by rw [hqp]⟩
      · rw [if_neg hqp]
        refine ⟨fun he => absurd (Option.some.inj he).symm hqp, fun hmem => ?_⟩
        exfalso
        have hq := (mem_childrenOf_iff hwf c p).mpr hmem
        rw [hcn, hnp] at hq
        simp at hq
    · rw [if_neg hcn]
      by_cases hqp : p = parent
      · rw [if_pos hqp, hqp, Dom.ListUtil.mem_insertBefore, ← mem_childrenOf_iff hwf]
        exact ⟨fun h => Or.inr h, fun h => h.resolve_left hcn⟩
      · rw [if_neg hqp, ← mem_childrenOf_iff hwf]
  · intro n d hd
    obtain ⟨d₀, hd₀⟩ := treeInserted_exists' hi hd
    rw [← childrenOf_eq hd, treeInserted_childrenOf hi]
    by_cases hnp' : n = parent
    · rw [if_pos hnp']
      exact Dom.ListUtil.nodup_insertBefore child
        (by rw [childrenOf_eq (hnp' ▸ hd₀ : t.get? parent = some d₀)]
            exact hwf.children_nodup parent d₀ (hnp' ▸ hd₀)) hnodemem
    · rw [if_neg hnp', childrenOf_eq hd₀]
      exact hwf.children_nodup n d₀ hd₀
  · intro n hn
    have hnodep : parentOf u node = some parent := hi.attached
    have hother : ∀ x, x ≠ node → parentOf u x = parentOf t x := hi.otherParents
    rcases ancestor_of_parentOf_insert hnodep hother hn with hmm | ⟨h1, h2⟩
    · exact hwf.acyclic n hmm
    · exact hanc (h1.trans_inclusive h2)
  · refine ownerDocument_is_document_of hwf ?_ ?_
    · intro m d hm
      obtain ⟨d₀, hd₀⟩ := treeInserted_exists' hi hm
      obtain ⟨-, -, -, hown, -⟩ := hi.sameData m d₀ d hd₀ hm
      exact ⟨d₀, hd₀, hown⟩
    · intro m d₀ hm
      obtain ⟨d, hd⟩ := treeInserted_exists hi hm
      obtain ⟨hk, -⟩ := hi.sameData m d₀ d hm hd
      exact ⟨d, hd, hk⟩

/-- 観測の等しい木への挿入は、観測の等しい木を返す。 -/
theorem treeInserted_transport (h : TreeObsEq t tb)
    (hi : TreeInserted tb u parent node child) : TreeInserted t u parent node child where
  attached := hi.attached
  children := by rw [hi.children, h.childrenOf]
  otherParents := fun m hm => by rw [hi.otherParents m hm, h.parentOf]
  otherChildren := fun m hm => by rw [hi.otherChildren m hm, h.childrenOf]
  sameNodes := fun m => by rw [hi.sameNodes m, h m]
  sameData := fun m d d' hd hd' => hi.sameData m d d' (by rw [h]; exact hd) hd'

theorem treeInserted_unique (h₁ : TreeInserted t u parent node child)
    (h₂ : TreeInserted t ub parent node child) : TreeObsEq u ub := by
  intro m
  cases hm : t.get? m with
  | none =>
    have e₁ : u.get? m = none := by
      have hs := h₁.sameNodes m; rw [hm] at hs; simpa using hs
    have e₂ : ub.get? m = none := by
      have hs := h₂.sameNodes m; rw [hm] at hs; simpa using hs
    rw [e₁, e₂]
  | some d =>
    obtain ⟨d₁, hd₁⟩ := treeInserted_exists h₁ hm
    obtain ⟨d₂, hd₂⟩ := treeInserted_exists h₂ hm
    obtain ⟨k₁, s₁, a₁, o₁, ns₁, p₁, l₁, e₁⟩ := h₁.sameData m d d₁ hm hd₁
    obtain ⟨k₂, s₂, a₂, o₂, ns₂, p₂, l₂, e₂⟩ := h₂.sameData m d d₂ hm hd₂
    have hpar : d₁.parent = d₂.parent := by
      have hq : parentOf u m = parentOf ub m := by
        rw [treeInserted_parentOf h₁, treeInserted_parentOf h₂]
      rw [parentOf, parentOf, hd₁, hd₂] at hq
      simpa using hq
    have hch : d₁.children = d₂.children := by
      have hq : childrenOf u m = childrenOf ub m := by
        rw [treeInserted_childrenOf h₁, treeInserted_childrenOf h₂]
      rw [childrenOf, childrenOf, hd₁, hd₂] at hq
      simpa using hq
    rw [hd₁, hd₂]
    have : d₂ = d₁ := by cases d₁; cases d₂; simp_all
    rw [this]

theorem treeInserted_congr (h : TreeObsEq t tb) (h₁ : TreeInserted t u parent node child)
    (h₂ : TreeInserted tb ub parent node child) : TreeObsEq u ub :=
  treeInserted_unique h₁ (treeInserted_transport h h₂)


/-- 挿入は kind を変えないので、document は document のままである。 -/
theorem treeInserted_isDocument (hi : TreeInserted t u parent node child) {d : NodeId}
    (hd : IsDocument t d) : IsDocument u d := by
  obtain ⟨dd, hdd, hk⟩ := hd
  obtain ⟨dd', hdd'⟩ := treeInserted_exists hi hdd
  obtain ⟨hk', -⟩ := hi.sameData _ dd dd' hdd hdd'
  exact ⟨dd', hdd', by rw [hk', hk]⟩

/-! ## step 7：一つずつ入れる -/

/--
step 7 の一段が保つもの。

`adopt` は node を親から外し ancestor を増やさないので、
「入れる node が `parent` の inclusive ancestor でない」は adopt を跨いで残る。
挿入が増やす辺は「その node → `parent`」の一本だけなので、
残りの node についての同じ条件も残る。
-/
theorem insertedEach_step {doc : NodeId} {s sa sb₁ : DOMState} {n : NodeId} {ns : List NodeId}
    (hwf : WellFormed s.tree) (hdoc : IsDocument s.tree doc)
    (hacyc : ∀ m ∈ n :: ns, ¬ InclusiveAncestor s.tree m parent)
    (ha : AdoptSpec s n doc sa) (hi : TreeInserted sa.tree sb₁.tree parent n child) :
    WellFormed sa.tree ∧ ¬ InclusiveAncestor sa.tree n parent ∧
      WellFormed sb₁.tree ∧ IsDocument sb₁.tree doc ∧
      ∀ m ∈ ns, ¬ InclusiveAncestor sb₁.tree m parent := by
  have hwfa : WellFormed sa.tree := adoptSpec_wellFormed hwf hdoc ha
  have hdoca : IsDocument sa.tree doc := adoptSpec_isDocument ha hdoc
  have hdet : parentOf sa.tree n = none := adoptSpec_detached ha
  have hanca : ¬ InclusiveAncestor sa.tree n parent := by
    rintro (rfl | hanc)
    · exact hacyc n (List.mem_cons_self ..) (Or.inl rfl)
    · exact hacyc n (List.mem_cons_self ..) (Or.inr (adoptSpec_ancestor ha hanc))
  refine ⟨hwfa, hanca, treeInserted_wellFormed hwfa hdet hanca hi,
    treeInserted_isDocument hi hdoca, ?_⟩
  rintro m hm (rfl | hanc)
  · exact hacyc m (List.mem_cons_of_mem _ hm) (Or.inl rfl)
  · rcases ancestor_of_parentOf_insert hi.attached hi.otherParents hanc with h | ⟨h1, -⟩
    · exact hacyc m (List.mem_cons_of_mem _ hm) (Or.inr (adoptSpec_ancestor ha h))
    · exact hanca h1

/-- step 7 を最後まで回しても well-formed は保たれる。 -/
theorem insertedEach_wellFormed {doc : NodeId} : ∀ (ns : List NodeId) {s out : DOMState},
    WellFormed s.tree → IsDocument s.tree doc →
    (∀ m ∈ ns, ¬ InclusiveAncestor s.tree m parent) →
    InsertedEach parent child doc s ns out → WellFormed out.tree ∧ IsDocument out.tree doc := by
  intro ns
  induction ns with
  | nil => intro s out hwf hdoc _ h; cases h; exact ⟨hwf, hdoc⟩
  | cons n ns ih =>
    intro s out hwf hdoc hacyc h
    cases h with
    | cons ha hi _ hrest =>
      obtain ⟨-, -, hwfb, hdocb, hacycb⟩ := insertedEach_step hwf hdoc hacyc ha hi
      exact ih hwfb hdocb hacycb hrest


/-- **step 7 の congruence。** -/
theorem insertedEach_congr {doc : NodeId} : ∀ (ns : List NodeId) {s sb o₁ o₂ : DOMState},
    WellFormed s.tree → IsDocument s.tree doc →
    (∀ m ∈ ns, ¬ InclusiveAncestor s.tree m parent) → ObsEq s sb →
    InsertedEach parent child doc s ns o₁ → InsertedEach parent child doc sb ns o₂ →
    ObsEq o₁ o₂ := by
  intro ns
  induction ns with
  | nil =>
    intro s sb o₁ o₂ _ _ _ h h₁ h₂
    cases h₁; cases h₂; exact h
  | cons n ns ih =>
    intro s sb o₁ o₂ hwf hdoc hacyc h h₁ h₂
    cases h₁ with
    | cons ha₁ hi₁ hl₁ hrest₁ =>
      cases h₂ with
      | cons ha₂ hi₂ hl₂ hrest₂ =>
        obtain ⟨-, -, hwfb, hdocb, hacycb⟩ := insertedEach_step hwf hdoc hacyc ha₁ hi₁
        have hobsa : ObsEq _ _ := adoptSpec_congr hwf h ha₁ ha₂
        have hobsb : ObsEq _ _ :=
          { tree := treeInserted_congr hobsa.tree hi₁ hi₂
            ranges := by rw [hl₂.ranges, hobsa.ranges, hl₁.ranges]
            iterators := by rw [hl₂.iterators, hobsa.iterators, hl₁.iterators]
            registrations := fun r => by
              rw [hl₂.registrations, hl₁.registrations]; exact hobsa.registrations r
            records := fun mo => by
              rw [hl₂.observers, hl₁.observers]; exact hobsa.records mo
            pendingObservers := fun mo => by
              rw [hl₂.pendingObservers, hl₁.pendingObservers]; exact hobsa.pendingObservers mo
            microtaskQueued := by
              rw [hl₂.microtaskQueued, hobsa.microtaskQueued, hl₁.microtaskQueued] }
        exact ih hwfb hdocb hacycb hobsb hrest₁ hrest₂

/-! ## step 1・5・6：入れる列と位置 -/

theorem nodesToInsert_unique (h : TreeObsEq t tb) {ns₁ ns₂ : List NodeId}
    (h₁ : NodesToInsert t node ns₁) (h₂ : NodesToInsert tb node ns₂) : ns₁ = ns₂ := by
  obtain ⟨d₁, hd₁, hc₁⟩ := h₁
  obtain ⟨d₂, hd₂, hc₂⟩ := h₂
  have hde : d₂ = d₁ := by
    rw [h] at hd₂
    have he := hd₁
    rw [hd₂] at he
    exact Option.some.inj he
  subst hde
  rcases hc₁ with ⟨hk₁, he₁⟩ | ⟨hk₁, he₁⟩ <;> rcases hc₂ with ⟨hk₂, he₂⟩ | ⟨hk₂, he₂⟩
  · rw [he₁, he₂]
  · exact absurd hk₁ hk₂
  · exact absurd hk₂ hk₁
  · rw [he₁, he₂]

theorem childIndex_unique (h : TreeObsEq t tb) {i₁ i₂ : Nat}
    (h₁ : ChildIndex t child i₁) (h₂ : ChildIndex tb child i₂) : i₁ = i₂ := by
  cases child with
  | none => rw [h₁, h₂]
  | some c =>
    have e₁ : index t c = some i₁ := h₁
    have e₂ : index tb c = some i₂ := h₂
    rw [h.index c, e₁] at e₂
    exact Option.some.inj e₂

theorem previousSiblingOf_unique (h : TreeObsEq t tb) {p₁ p₂ : Option NodeId}
    (h₁ : PreviousSiblingOf t parent child p₁) (h₂ : PreviousSiblingOf tb parent child p₂) :
    p₁ = p₂ := by
  cases child with
  | none =>
    have e₁ : p₁ = (childrenOf t parent).getLast? := h₁
    have e₂ : p₂ = (childrenOf tb parent).getLast? := h₂
    rw [e₁, e₂, h.childrenOf]
  | some c =>
    have e₁ : p₁ = previousSibling t c := h₁
    have e₂ : p₂ = previousSibling tb c := h₂
    rw [e₁, e₂, h.previousSibling]

/-! ## step 5：live range の調整 -/

theorem insertShifted_unique {idx count : Nat} {bp b₁ b₂ : BoundaryPoint}
    (h₁ : InsertShifted parent idx count bp b₁) (h₂ : InsertShifted parent idx count bp b₂) :
    b₁ = b₂ := by
  rcases h₁ with ⟨ha₁, hb₁, he₁⟩ | ⟨ha₁, he₁⟩ <;>
    rcases h₂ with ⟨ha₂, hb₂, he₂⟩ | ⟨ha₂, he₂⟩
  · rw [he₁, he₂]
  · exact absurd ⟨ha₁, hb₁⟩ ha₂
  · exact absurd ⟨ha₂, hb₂⟩ ha₁
  · rw [he₁, he₂]

/-- **step 5 の congruence。** -/
theorem rangeInsertAdjusted_congr {s sb o₁ o₂ : DOMState} {idx count : Nat} (h : ObsEq s sb)
    (h₁ : RangeInsertAdjusted s o₁ parent child idx count)
    (h₂ : RangeInsertAdjusted sb o₂ parent child idx count) : ObsEq o₁ o₂ := by
  have hranges : o₂.ranges = o₁.ranges := by
    refine Dom.ListUtil.ext_of_pointwise (by rw [h₂.length, h.ranges, h₁.length]) ?_
    intro i r₂ r₁ hr₂ hr₁
    obtain ⟨rs, hrs⟩ : ∃ rs, s.ranges[i]? = some rs := by
      rcases hq : s.ranges[i]? with _ | rs
      · exfalso
        rw [List.getElem?_eq_none_iff, ← h₁.length, ← List.getElem?_eq_none_iff] at hq
        rw [hq] at hr₁; simp at hr₁
      · exact ⟨rs, rfl⟩
    have hrsb : sb.ranges[i]? = some rs := by rw [h.ranges]; exact hrs
    have e₁ := h₁.adjusted i rs r₁ hrs hr₁
    have e₂ := h₂.adjusted i rs r₂ hrsb hr₂
    have hboth : r₂.start = r₁.start ∧ r₂.«end» = r₁.«end» := by
      rcases e₁ with ⟨hc, rfl⟩ | ⟨hc, hs₁, he₁⟩
      · rcases e₂ with ⟨-, rfl⟩ | ⟨hc', -, -⟩
        · exact ⟨rfl, rfl⟩
        · exact absurd hc hc'
      · rcases e₂ with ⟨hc', -⟩ | ⟨-, hs₂, he₂⟩
        · exact absurd hc' hc
        · exact ⟨insertShifted_unique hs₂ hs₁, insertShifted_unique he₂ he₁⟩
    cases r₁; cases r₂; simp_all
  exact
    { tree := fun m => by rw [h₂.tree, h₁.tree]; exact h.tree m
      ranges := hranges
      iterators := by rw [h₂.live.iterators, h.iterators, h₁.live.iterators]
      registrations := fun r => by
        rw [h₂.live.registrations, h₁.live.registrations]; exact h.registrations r
      records := fun mo => by
        rw [h₂.live.observers, h₁.live.observers]; exact h.records mo
      pendingObservers := fun mo => by
        rw [h₂.live.pendingObservers, h₁.live.pendingObservers]; exact h.pendingObservers mo
      microtaskQueued := by
        rw [h₂.live.microtaskQueued, h.microtaskQueued, h₁.live.microtaskQueued] }

/-! ## step 4：DocumentFragment を空にする -/

/-- step 4 が一つの derivation について保証すること。 -/
theorem fragmentPrepared_facts {s s₁ : DOMState} {nodes : List NodeId}
    (hwf : WellFormed s.tree) (h : FragmentPrepared s s₁ node nodes) :
    WellFormed s₁.tree ∧ ∀ a m : NodeId, Ancestor s₁.tree a m → Ancestor s.tree a m := by
  obtain ⟨d, hd, hcase⟩ := h
  by_cases hk : d.kind = NodeKind.documentFragment
  · rw [if_pos hk] at hcase
    obtain ⟨sr, hre, -, hframe⟩ := hcase
    refine ⟨?_, ?_⟩
    · rw [hframe.tree]; exact removeEachSpec_wellFormed hwf hre
    · intro a m ha
      rw [hframe.tree] at ha
      exact removeEachSpec_ancestor hre ha
  · rw [if_neg hk] at hcase
    subst hcase
    exact ⟨hwf, fun _ _ ha => ha⟩

/-- **step 4 の congruence。** -/
theorem fragmentPrepared_congr {s sb s₁ s₂ : DOMState} {nodes : List NodeId}
    (hwf : WellFormed s.tree) (h : ObsEq s sb)
    (h₁ : FragmentPrepared s s₁ node nodes) (h₂ : FragmentPrepared sb s₂ node nodes) :
    ObsEq s₁ s₂ := by
  obtain ⟨d₁, hd₁, hc₁⟩ := h₁
  obtain ⟨d₂, hd₂, hc₂⟩ := h₂
  have hde : d₂ = d₁ := by
    rw [h.tree] at hd₂
    have he := hd₁
    rw [hd₂] at he
    exact Option.some.inj he
  subst hde
  by_cases hk : d₂.kind = NodeKind.documentFragment
  · rw [if_pos hk] at hc₁ hc₂
    obtain ⟨sr₁, hre₁, hq₁, hf₁⟩ := hc₁
    obtain ⟨sr₂, hre₂, hq₂, hf₂⟩ := hc₂
    exact treeRecordQueued_congr (removeEachSpec_congr hwf h hre₁ hre₂) hq₁ hq₂ hf₁ hf₂
  · rw [if_neg hk] at hc₁ hc₂
    subst hc₁; subst hc₂
    exact h

/-! ## 全体 -/

/--
**`InsertSpec` の congruence。**

「入れる node が `parent` の inclusive ancestor でない」は §4.2.1 の
pre-insertion validity が保証するもので、`insert` 本体は仮定として受け取る。
-/
theorem insertSpec_congr {s sb o₁ o₂ : DOMState} {suppress : Bool}
    (hwf : WellFormed s.tree) (h : ObsEq s sb)
    (hacyc : ∀ ns : List NodeId, NodesToInsert s.tree node ns →
      ∀ m ∈ ns, ¬ InclusiveAncestor s.tree m parent)
    (h₁ : InsertSpec s node parent child suppress o₁)
    (h₂ : InsertSpec sb node parent child suppress o₂) : ObsEq o₁ o₂ := by
  obtain ⟨ns₁, hn₁, hcase₁⟩ := h₁
  obtain ⟨ns₂, hn₂, hcase₂⟩ := h₂
  have hnse : ns₁ = ns₂ := nodesToInsert_unique h.tree hn₁ hn₂
  subst hnse
  rcases hcase₁ with ⟨hnil₁, rfl⟩ | ⟨hne, s₁, s₂, s₃, idx, prev, pd, hfp₁, hci₁, hps₁, hri₁,
      hpd₁, hie₁, hrec₁, hfr₁⟩
  · rcases hcase₂ with ⟨-, rfl⟩ | ⟨hne, -⟩
    · exact h
    · exact absurd hnil₁ hne
  · rcases hcase₂ with ⟨hnil, -⟩ | ⟨-, s₁', s₂', s₃', idx', prev', pd', hfp₂, hci₂, hps₂, hri₂,
        hpd₂, hie₂, hrec₂, hfr₂⟩
    · exact absurd hnil hne
    -- step 4
    have hobs₁ : ObsEq s₁ s₁' := fragmentPrepared_congr hwf h hfp₁ hfp₂
    obtain ⟨hwf₁, hanc₁⟩ := fragmentPrepared_facts hwf hfp₁
    -- step 5-6 の位置は入力の観測から決まる。
    have hidx : idx = idx' := childIndex_unique hobs₁.tree hci₁ hci₂
    subst hidx
    have hprev : prev = prev' := previousSiblingOf_unique hobs₁.tree hps₁ hps₂
    subst hprev
    have hpde : pd' = pd := by
      rw [hobs₁.tree] at hpd₂
      have he := hpd₁
      rw [hpd₂] at he
      exact Option.some.inj he
    subst hpde
    -- step 5
    have hobs₂ : ObsEq s₂ s₂' := rangeInsertAdjusted_congr hobs₁ hri₁ hri₂
    have hwf₂ : WellFormed s₂.tree := by rw [hri₁.tree]; exact hwf₁
    have hdoc₂ : IsDocument s₂.tree pd'.ownerDocument := by
      refine isDocument_ownerDocument (m := parent) hwf₂ ?_
      rw [hri₁.tree]
      exact hpd₁
    have hacyc₂ : ∀ m ∈ ns₁, ¬ InclusiveAncestor s₂.tree m parent := by
      intro m hm hc
      refine hacyc ns₁ hn₁ m hm ?_
      rcases hc with he | ha
      · exact Or.inl he
      · rw [hri₁.tree] at ha
        exact Or.inr (hanc₁ m parent ha)
    -- step 7
    have hobs₃ : ObsEq s₃ s₃' :=
      insertedEach_congr ns₁ hwf₂ hdoc₂ hacyc₂ hobs₂ hie₁ hie₂
    -- step 9
    exact treeRecordQueued_congr hobs₃ hrec₁ hrec₂ hfr₁ hfr₂

/--
**`InsertSpec` は観測を一つに決める。**

soundness（`Dom/Spec/InsertSound.lean`）と合わせると、
`insert` の結果は関係が許す唯一の観測になっている、と言える。
-/
theorem insertSpec_deterministic {s o₁ o₂ : DOMState} {suppress : Bool}
    (hwf : WellFormed s.tree)
    (hacyc : ∀ ns : List NodeId, NodesToInsert s.tree node ns →
      ∀ m ∈ ns, ¬ InclusiveAncestor s.tree m parent)
    (h₁ : InsertSpec s node parent child suppress o₁)
    (h₂ : InsertSpec s node parent child suppress o₂) : ObsEq o₁ o₂ :=
  insertSpec_congr hwf (ObsEq.refl s) hacyc h₁ h₂

end Dom.Spec
