import Dom.Spec.ReplaceAll
import Dom.Spec.Result
import Dom.Properties.InsertOk

/-!
# `replace all` と `replaceChildren` が関係を満たすこと

* `replaceAll_sound`：成功した `replaceAll` は `ReplaceAllSpec` を満たす。
* `replaceAllSpec_deterministic`：関係は出力を観測として一つに決める。
* `replaceAll_isOk`：step 5 の insert が要る事実があれば、`replaceAll` は失敗しない。
* `ReplaceChildrenResult`：`replaceChildren` の、例外まで含めた関係。

determinism は `replace` と同じく、step 5 の insert が要る acyclicity を仮定する。
`replaceChildren` の step 2（ensure pre-insertion validity）がそれを保証する。
-/

namespace Dom.Spec

open Dom

/-! ## step 4 の removal が保つもの -/

/--
外す node のどの祖先でもない node は、kind と children が残る。

remove が children を変えるのは外す node の parent だけで、
removal の途中で parent になれるのは元の木での祖先だけだからである。
-/
theorem removeEachSpec_data {ns : List NodeId} {b : Bool} {m : NodeId} :
    ∀ {s s' : DOMState}, RemoveEachSpec s ns b s' →
      ∀ {d : NodeData}, s.tree.get? m = some d →
      (∀ c ∈ ns, ∀ q, Ancestor s.tree q c → m ≠ q) →
      ∃ d', s'.tree.get? m = some d' ∧ d'.kind = d.kind ∧ d'.children = d.children := by
  induction ns with
  | nil => intro s s' h d hd _; cases h; exact ⟨d, hd, rfl, rfl⟩
  | cons n ns ih =>
    intro s s' h d hd hside
    cases h with
    | cons hr hrest =>
      obtain ⟨d₁, hd₁, hk₁, hch₁⟩ :=
        removeSpec_data hr hd (fun p hp => hside n (by simp) p (Ancestor.step hp))
      obtain ⟨d₂, hd₂, hk₂, hch₂⟩ := ih hrest hd₁
        (fun c hc q hq => hside c (by simp [hc]) q (removeSpec_ancestor hr hq))
      exact ⟨d₂, hd₂, by rw [hk₂, hk₁], by rw [hch₂, hch₁]⟩

/--
**step 5 の insert が要る acyclicity を `s` から removal の後へ移す。**

`node` が `parent` の inclusive ancestor でなければ、`parent` の children のどの祖先でもない。
したがって `node` の kind と children は removal を跨いで残り、
removal は祖先関係を増やさない。
-/
theorem replaceAll_acyc_step5 {s s₁ : DOMState} {n parent : NodeId} {d : NodeData}
    (hwf : WellFormed s.tree) (hd : s.tree.get? n = some d) (hna : ¬ InclusiveAncestor s.tree n parent)
    (hacyc : ∀ ns : List NodeId, NodesToInsert s.tree n ns →
      ∀ m ∈ ns, ¬ InclusiveAncestor s.tree m parent)
    (hre : RemoveEachSpec s (childrenOf s.tree parent) true s₁) :
    ∀ ns : List NodeId, NodesToInsert s₁.tree n ns →
      ∀ m ∈ ns, ¬ InclusiveAncestor s₁.tree m parent := by
  have hside : ∀ c ∈ childrenOf s.tree parent, ∀ q, Ancestor s.tree q c → n ≠ q := by
    intro c hc q hq hnq
    have hcp : parentOf s.tree c = some parent := (mem_childrenOf_iff hwf c parent).mpr hc
    obtain ⟨p, hp, hqp⟩ := hq.cases_parent
    rw [hcp] at hp
    cases hp
    exact hna (by rw [hnq]; exact hqp)
  intro ns hns m hm hinc
  obtain ⟨d₁, hd₁, hc⟩ := hns
  have hb : NodesToInsert s.tree n ns := by
    obtain ⟨d₁', hd₁', hk, hch⟩ := removeEachSpec_data hre hd hside
    rw [hd₁] at hd₁'
    cases hd₁'
    refine ⟨d, hd, ?_⟩
    rcases hc with ⟨hk', hns'⟩ | ⟨hk', hns'⟩
    · exact Or.inl ⟨by rw [← hk]; exact hk', by rw [hns', hch]⟩
    · exact Or.inr ⟨by rw [← hk]; exact hk', hns'⟩
  refine hacyc ns hb m hm ?_
  rcases hinc with he | ha
  · exact Or.inl he
  · exact Or.inr (removeEachSpec_ancestor hre ha)

/-! ## soundness -/

/-- **`replaceAll` は `ReplaceAllSpec` を満たす。** -/
theorem replaceAll_sound {s s' : DOMState} {node : Option NodeId} {parent : NodeId}
    (hwf : WellFormed s.tree) (h : replaceAll s node parent = .ok s') :
    ReplaceAllSpec s node parent s' := by
  obtain ⟨s₁, s₂, hr, hins, hs'⟩ := replaceAll_cases h
  have hwf₁ : WellFormed s₁.tree := removeEach_preserves_wellformed _ hwf hr
  have hsp : ShapePreserving s.tree s₁.tree := shapePreserving_removeEach _ hr
  -- step 2-3 と step 5
  have hstep : AddedNodes s.tree node (replaceAllNodes s.tree node) ∧
      ReplaceAllInserted s₁ node parent s₂ ∧ WellFormed s₂.tree := by
    rcases hins with ⟨rfl, rfl⟩ | ⟨n, rfl, hi⟩
    · exact ⟨Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩, hwf₁⟩
    · -- insert が成功したので `n` は木にある。removal は node を消さない。
      obtain ⟨nd, hnd⟩ : ∃ nd, s.tree.get? n = some nd := by
        cases hn₁ : s₁.tree.get? n with
        | none => unfold insert at hi; rw [hn₁] at hi; cases hi
        | some nd₁ =>
          have := hsp n
          rw [hn₁] at this
          cases hn : s.tree.get? n with
          | none => rw [hn] at this; cases this
          | some nd => exact ⟨nd, rfl⟩
      refine ⟨Or.inr ⟨n, rfl, ?_⟩, Or.inr ⟨n, rfl, insert_sound hwf₁ hi⟩,
        insert_preserves_wellformed hwf₁ hi⟩
      rw [replaceAllNodes_some, replaceNodes_eq hnd]
      refine ⟨nd, hnd, ?_⟩
      by_cases hk : nd.kind = NodeKind.documentFragment
      · exact Or.inl ⟨hk, by rw [if_pos (by simp [hk])]⟩
      · exact Or.inr ⟨hk, by rw [if_neg (by simp [hk])]⟩
  obtain ⟨hadded, hinserted, hwf₂⟩ := hstep
  refine ⟨_, _, s₁, s₂, rfl, hadded, removeEach_sound _ hwf hr, hinserted, ?_⟩
  -- step 6-7
  by_cases hemp : ((replaceAllNodes s.tree node).isEmpty &&
      (childrenOf s.tree parent).isEmpty) = true
  · simp only [Bool.and_eq_true, List.isEmpty_iff] at hemp
    refine Or.inl ⟨hemp.1, hemp.2, ?_⟩
    rw [hs']
    unfold queueTreeMutationRecord
    rw [if_pos (by simp [hemp.1, hemp.2])]
  · refine Or.inr ⟨?_, hs' ▸ treeRecordQueued_of_queue s₂ hwf₂ parent _ _ none none hemp,
      hs' ▸ ⟨by simp, by simp, by simp, by simp, untouched_queueTreeMutationRecord ..⟩⟩
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hemp
    by_cases ha : replaceAllNodes s.tree node = []
    · exact Or.inr fun hc => hemp ⟨ha, hc⟩
    · exact Or.inl ha

/-! ## determinism -/

/--
**`ReplaceAllSpec` は出力を観測として一つに決める。**

`node` が null でないときは、step 5 の insert が要る事実を仮定する。
`node` が木にあり、`parent` の inclusive ancestor でなく、入る node 列のどれも
`parent` の inclusive ancestor でないこと。どれも pre-insertion validity が保証する。
-/
theorem replaceAllSpec_deterministic {s o₁ o₂ : DOMState} {node : Option NodeId}
    {parent : NodeId} (hwf : WellFormed s.tree)
    (hfacts : ∀ n, node = some n → (∃ d, s.tree.get? n = some d) ∧
      ¬ InclusiveAncestor s.tree n parent ∧
      ∀ ns : List NodeId, NodesToInsert s.tree n ns →
        ∀ m ∈ ns, ¬ InclusiveAncestor s.tree m parent)
    (h₁ : ReplaceAllSpec s node parent o₁) (h₂ : ReplaceAllSpec s node parent o₂) :
    ObsEq o₁ o₂ := by
  obtain ⟨r₁, a₁, s₁, s₂, rfl, ha₁, hre₁, hin₁, hrec₁⟩ := h₁
  obtain ⟨r₂, a₂, s₁', s₂', hr₂, ha₂, hre₂, hin₂, hrec₂⟩ := h₂
  subst hr₂
  -- step 1-3
  have hae : a₂ = a₁ := by
    rcases ha₁ with ⟨rfl, rfl⟩ | ⟨n, rfl, hn₁⟩ <;> rcases ha₂ with ⟨he, rfl⟩ | ⟨n', he, hn₂⟩
    · rfl
    · cases he
    · cases he
    · cases he
      exact nodesToInsert_unique (TreeObsEq.refl _) hn₂ hn₁
  subst hae
  -- step 4
  have hobs₁ : ObsEq s₁ s₁' := removeEachSpec_congr hwf (ObsEq.refl s) hre₁ hre₂
  have hwf₁ : WellFormed s₁.tree := removeEachSpec_wellFormed hwf hre₁
  -- step 5
  have hobs₂ : ObsEq s₂ s₂' := by
    rcases hin₁ with ⟨rfl, rfl⟩ | ⟨n, rfl, hi₁⟩ <;> rcases hin₂ with ⟨he, rfl⟩ | ⟨n', he, hi₂⟩
    · exact hobs₁
    · cases he
    · cases he
    · cases he
      obtain ⟨⟨d, hd⟩, hna, hacyc⟩ := hfacts n rfl
      exact insertSpec_congr hwf₁ hobs₁ (replaceAll_acyc_step5 hwf hd hna hacyc hre₁) hi₁ hi₂
  -- step 6-7
  rcases hrec₁ with ⟨hae, hre, rfl⟩ | ⟨hne, hq₁, hoo₁⟩ <;>
    rcases hrec₂ with ⟨hae', hre', rfl⟩ | ⟨hne', hq₂, hoo₂⟩
  · exact hobs₂
  · exfalso; rcases hne' with h | h <;> contradiction
  · exfalso; rcases hne with h | h <;> contradiction
  · exact treeRecordQueued_congr hobs₂ hq₁ hq₂ hoo₁ hoo₂

/-! ## 成功 -/

/--
**`replaceAll` は step 5 の insert が要る事実があれば成功する。**

step 4 の removal は parent の children を外すだけなので必ず通る。
-/
theorem replaceAll_isOk {s : DOMState} {node : Option NodeId} {parent : NodeId}
    (hwf : WellFormed s.tree)
    (hfacts : ∀ n, node = some n → (∃ pd, s.tree.get? parent = some pd) ∧
      (∃ d, s.tree.get? n = some d) ∧ ¬ InclusiveAncestor s.tree n parent) :
    ∃ s', replaceAll s node parent = .ok s' := by
  obtain ⟨s₁, hr⟩ := removeEach_isOk (childrenOf s.tree parent) (b := true) (p := parent) hwf
    (fun m hm => (mem_childrenOf_iff hwf m parent).mpr hm) (childrenOf_nodup hwf parent)
  unfold replaceAll
  rw [hr]
  simp only []
  cases node with
  | none => exact ⟨_, rfl⟩
  | some n =>
    obtain ⟨⟨pd, hpd⟩, ⟨d, hd⟩, hna⟩ := hfacts n rfl
    have hsp : ShapePreserving s.tree s₁.tree := shapePreserving_removeEach _ hr
    obtain ⟨pd₁, hpd₁⟩ := exists_get?_of_kindPreserving hsp hpd
    obtain ⟨d₁, hd₁⟩ := exists_get?_of_kindPreserving hsp hd
    have hna₁ : ¬ InclusiveAncestor s₁.tree n parent := by
      rintro (he | ha)
      · exact hna (Or.inl he)
      · exact hna (Or.inr (ancestor_of_removeEach _ hr ha))
    obtain ⟨s₂, hi⟩ := insert_isOk_of_facts (child := none) (b := true)
      (removeEach_preserves_wellformed _ hwf hr) hpd₁ hd₁ hna₁ (by simp) (by simp)
    simp only []
    rw [hi]
    exact ⟨_, rfl⟩

/-! ## `replaceChildren(nodes)` -/

/-- step 2 の validity が通れば、`replaceAll` の determinism と成功が要る事実は揃う。 -/
theorem replaceChildren_facts_of_validity {t : Tree} (hwf : WellFormed t) {n parent : NodeId}
    {excl : List NodeId}
    (hv : ensurePreInsertionValidity t n parent none excl = .ok ()) :
    (∃ pd, t.get? parent = some pd) ∧ (∃ d, t.get? n = some d) ∧
      ¬ InclusiveAncestor t n parent ∧
      ∀ ns : List NodeId, NodesToInsert t n ns → ∀ m ∈ ns, ¬ InclusiveAncestor t m parent := by
  obtain ⟨hpd, hnd, hanc, -⟩ := ensurePreInsertionValidity_ok hv
  refine ⟨hpd, hnd, ?_, nodesToInsert_not_ancestor_of_validity hwf hv⟩
  intro hq
  rw [(isInclusiveAncestorOf_iff hwf n parent).mpr hq] at hanc
  exact Bool.noConfusion hanc

/--
**§4.2.6 `replaceChildren(nodes)` の、結果まで含めた関係。**

2. ensure pre-insertion validity of node into this before null。
   model は childrenToExclude に this の children を渡す（直後の replace all がそれらを外す）。
3. replace all with node within this。

`node` が null（引数が空）なら step 2 は無く、replace all は必ず成功する。
-/
def ReplaceChildrenResult (s : DOMState) (parent : NodeId) (node : Option NodeId) :
    Except DOMException DOMState → Prop
  | .ok s' => (∀ n, node = some n →
        PreInsertValidity s.tree n parent none (childrenOf s.tree parent) (.ok ())) ∧
      ReplaceAllSpec s node parent s'
  | .error e => ∃ n, node = some n ∧
      PreInsertValidity s.tree n parent none (childrenOf s.tree parent) (.error e)

theorem replaceChildren_result_sound {s : DOMState} (hwf : WellFormed s.tree)
    (parent : NodeId) (node : Option NodeId) :
    ReplaceChildrenResult s parent node (replaceChildren s parent node) := by
  unfold replaceChildren
  cases node with
  | none =>
    obtain ⟨s', h⟩ := replaceAll_isOk (node := none) (parent := parent) hwf
      (fun n hn => by cases hn)
    simp only []
    rw [h]
    exact ⟨fun n hn => (by cases hn), replaceAll_sound hwf h⟩
  | some n =>
    simp only []
    split
    · next e hv => exact ⟨n, rfl, (preInsertValidity_iff hwf).mpr hv⟩
    · next hv =>
      obtain ⟨hpd, hnd, hna, -⟩ := replaceChildren_facts_of_validity hwf hv
      obtain ⟨s', h⟩ := replaceAll_isOk (node := some n) (parent := parent) hwf
        (fun n' hn' => by cases hn'; exact ⟨hpd, hnd, hna⟩)
      rw [h]
      exact ⟨fun n' hn' => (by cases hn'; exact (preInsertValidity_iff hwf).mpr hv),
        replaceAll_sound hwf h⟩

theorem replaceChildren_result_deterministic {s : DOMState} (hwf : WellFormed s.tree)
    {parent : NodeId} {node : Option NodeId} {r₁ r₂ : Except DOMException DOMState}
    (h₁ : ReplaceChildrenResult s parent node r₁) (h₂ : ReplaceChildrenResult s parent node r₂) :
    ResultObsEq r₁ r₂ := by
  cases r₁ with
  | ok s₁ =>
    cases r₂ with
    | ok s₂ =>
      refine replaceAllSpec_deterministic hwf ?_ h₁.2 h₂.2
      intro n hn
      obtain ⟨-, hnd, hna, hacyc⟩ :=
        replaceChildren_facts_of_validity hwf ((preInsertValidity_iff hwf).mp (h₁.1 n hn))
      exact ⟨hnd, hna, hacyc⟩
    | error e₂ =>
      exfalso
      obtain ⟨n, hn, hv₂⟩ := h₂
      have h1 := (preInsertValidity_iff hwf).mp (h₁.1 n hn)
      rw [(preInsertValidity_iff hwf).mp hv₂] at h1
      cases h1
  | error e₁ =>
    cases r₂ with
    | ok s₂ =>
      exfalso
      obtain ⟨n, hn, hv₁⟩ := h₁
      have h2 := (preInsertValidity_iff hwf).mp (h₂.1 n hn)
      rw [(preInsertValidity_iff hwf).mp hv₁] at h2
      cases h2
    | error e₂ =>
      show e₁ = e₂
      obtain ⟨n, hn, hv₁⟩ := h₁
      obtain ⟨n', hn', hv₂⟩ := h₂
      rw [hn] at hn'
      cases hn'
      have h1 := (preInsertValidity_iff hwf).mp hv₁
      rw [(preInsertValidity_iff hwf).mp hv₂] at h1
      exact (Except.error.inj h1).symm

theorem replaceChildren_result_complete {s : DOMState} (hwf : WellFormed s.tree)
    {parent : NodeId} {node : Option NodeId} {r : Except DOMException DOMState}
    (h : ReplaceChildrenResult s parent node r) :
    ResultObsEq r (replaceChildren s parent node) :=
  replaceChildren_result_deterministic hwf h (replaceChildren_result_sound hwf parent node)

end Dom.Spec
