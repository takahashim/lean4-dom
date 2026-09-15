import Dom.Observer.Record
import Dom.Properties.Tree

/-!
# record を積む step の効果

`queueMutationRecord`（§4.3.4）が、どの observer の queue に何を積むかを述べる。

`interestedObservers` は「target の inclusive ancestor を下から上へ、
各 node の registered observer list を順に見て、条件を満たす observer を初出順に集める」
という二重の畳み込みである。ここではその結果の
**どの observer が入るか**（`mem_interestedObservers`）と
**重複が無いこと**（`nodup_interestedObservers`）を取り出し、
そこから各 observer の record queue の変化を決める。
-/

namespace Dom

/-! ## 畳み込みの一般補題 -/

/-- 一 step が「集合に一つ足すか、何もしない」なら、畳み込みの結果も集合の和になる。 -/
theorem mem_foldl_of_step {α : Type}
    (step : List (Nat × Option String) → α → List (Nat × Option String))
    (Q : α → Nat → Prop)
    (hstep : ∀ acc a mo, mo ∈ ((step acc a).map (·.1)) ↔ mo ∈ (acc.map (·.1)) ∨ Q a mo) :
    ∀ (l : List α) (acc : List (Nat × Option String)) (mo : Nat),
      mo ∈ ((l.foldl step acc).map (·.1)) ↔ mo ∈ (acc.map (·.1)) ∨ ∃ a ∈ l, Q a mo := by
  intro l
  induction l with
  | nil => intro acc mo; simp
  | cons a rest ih =>
    intro acc mo
    rw [List.foldl_cons, ih (step acc a) mo, hstep acc a mo]
    constructor
    · rintro ((h | h) | ⟨b, hb, hQ⟩)
      · exact Or.inl h
      · exact Or.inr ⟨a, List.mem_cons_self, h⟩
      · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, hQ⟩
    · rintro (h | ⟨b, hb, hQ⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.mp hb with rfl | hb'
        · exact Or.inl (Or.inr hQ)
        · exact Or.inr ⟨b, hb', hQ⟩

/-- 一 step が重複を増やさないなら、畳み込みも増やさない。 -/
theorem nodup_foldl_of_step {α : Type}
    (step : List (Nat × Option String) → α → List (Nat × Option String))
    (hstep : ∀ acc a, ((acc.map (·.1)).Nodup) → (((step acc a).map (·.1)).Nodup)) :
    ∀ (l : List α) (acc : List (Nat × Option String)),
      ((acc.map (·.1)).Nodup) → (((l.foldl step acc).map (·.1)).Nodup) := by
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons a rest ih => intro acc h; exact ih (step acc a) (hstep acc a h)

/-! ## `addInterested` -/

theorem map_fst_addInterested (acc : List (Nat × Option String)) (mo : Nat)
    (ov : Option String) :
    (addInterested acc mo ov).map (·.1) =
      if acc.any (fun p => p.1 == mo) then acc.map (·.1) else acc.map (·.1) ++ [mo] := by
  unfold addInterested
  split
  · split
    · rfl
    · simp only [List.map_map]
      refine List.map_congr_left (fun p _ => ?_)
      simp only [Function.comp_apply]
      split <;> rfl
  · simp

theorem mem_addInterested (acc : List (Nat × Option String)) (mo' mo : Nat)
    (ov : Option String) :
    mo ∈ ((addInterested acc mo' ov).map (·.1)) ↔ mo ∈ (acc.map (·.1)) ∨ mo = mo' := by
  rw [map_fst_addInterested]
  split
  · next h =>
    constructor
    · exact Or.inl
    · rintro (h' | rfl)
      · exact h'
      · simp only [List.any_eq_true, beq_iff_eq] at h
        obtain ⟨p, hp, he⟩ := h
        exact List.mem_map.mpr ⟨p, hp, he⟩
  · simp

theorem nodup_addInterested (acc : List (Nat × Option String)) (mo : Nat) (ov : Option String)
    (h : (acc.map (·.1)).Nodup) : ((addInterested acc mo ov).map (·.1)).Nodup := by
  rw [map_fst_addInterested]
  split
  · exact h
  · next hno =>
    have hfresh : ∀ p ∈ acc, p.1 ≠ mo := by
      intro p hp hpm
      exact hno (List.any_eq_true.mpr ⟨p, hp, by simp [hpm]⟩)
    refine List.nodup_append.mpr ⟨h, by simp, ?_⟩
    intro x hx y hy hxy
    have hy' : y = mo := by simpa using hy
    obtain ⟨p, hp, he⟩ := List.mem_map.mp hx
    exact hfresh p hp (by rw [he, hxy, hy'])

/-! ## oldValue が載る observer -/

/-- 一 step が「その対を一つ足すか、何もしない」なら、畳み込みの結果も和になる。 -/
theorem mem_pair_foldl_of_step {α : Type} {ov : Option String}
    (step : List (Nat × Option String) → α → List (Nat × Option String))
    (Q : α → Nat → Prop)
    (hstep : ∀ acc a mo, ((mo, ov) ∈ step acc a) ↔ ((mo, ov) ∈ acc ∨ Q a mo)) :
    ∀ (l : List α) (acc : List (Nat × Option String)) (mo : Nat),
      ((mo, ov) ∈ l.foldl step acc) ↔ ((mo, ov) ∈ acc ∨ ∃ a ∈ l, Q a mo) := by
  intro l
  induction l with
  | nil => intro acc mo; simp
  | cons a rest ih =>
    intro acc mo
    rw [List.foldl_cons, ih (step acc a) mo, hstep acc a mo]
    constructor
    · rintro ((h | h) | ⟨b, hb, hQ⟩)
      · exact Or.inl h
      · exact Or.inr ⟨a, List.mem_cons_self, h⟩
      · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, hQ⟩
    · rintro (h | ⟨b, hb, hQ⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.mp hb with rfl | hb'
        · exact Or.inl (Or.inr hQ)
        · exact Or.inr ⟨b, hb', hQ⟩

/--
`addInterested` が `(mo, ov)` を持つかどうか。

`ov` は非 `none` で、足す値は `ov` か `none` のどちらかという前提を置く
（`interestedObservers` の畳み込みはその形である）。
-/
theorem mem_pair_addInterested (acc : List (Nat × Option String)) (mo' mo : Nat)
    (ov v : Option String) (hov : ov.isSome) (hv : v = ov ∨ v = none) :
    ((mo, ov) ∈ addInterested acc mo' v) ↔ ((mo, ov) ∈ acc ∨ (mo = mo' ∧ v = ov)) := by
  obtain ⟨ov₀, rfl⟩ : ∃ ov₀, ov = some ov₀ := Option.isSome_iff_exists.mp hov
  unfold addInterested
  by_cases hany : (acc.any fun p => p.1 == mo') = true
  · rw [if_pos hany]
    rcases hv with rfl | rfl
    · -- 値を `ov` で上書きする枝
      simp only
      constructor
      · intro h
        obtain ⟨q, hq, he⟩ := List.mem_map.mp h
        by_cases hq' : q.1 = mo'
        · rw [if_pos (by simp [hq'])] at he
          have hfst : q.1 = mo := congrArg Prod.fst he
          refine Or.inr ⟨?_, by simp⟩
          rw [← hfst, hq']
        · rw [if_neg (by simp [hq'])] at he
          exact Or.inl (he ▸ hq)
      · rintro (h | ⟨rfl, -⟩)
        · by_cases hq' : mo = mo'
          · obtain ⟨q, hqm, hqe⟩ : ∃ q ∈ acc, q.1 = mo' := by
              simp only [List.any_eq_true, beq_iff_eq] at hany
              exact hany
            refine List.mem_map.mpr ⟨q, hqm, ?_⟩
            rw [if_pos (by simp [hqe]), hqe, hq']
          · refine List.mem_map.mpr ⟨(mo, some ov₀), h, ?_⟩
            rw [if_neg (by simp [hq'])]
        · obtain ⟨q, hqm, hqe⟩ : ∃ q ∈ acc, q.1 = mo := by
            simp only [List.any_eq_true, beq_iff_eq] at hany
            exact hany
          refine List.mem_map.mpr ⟨q, hqm, ?_⟩
          rw [if_pos (by simp [hqe]), hqe]
    · -- 値が `none` なら何も変わらない
      simp only
      constructor
      · exact Or.inl
      · rintro (h | ⟨-, he⟩)
        · exact h
        · simp at he
  · rw [if_neg hany]
    constructor
    · intro h
      rcases List.mem_append.mp h with h' | h'
      · exact Or.inl h'
      · have he : (mo, some ov₀) = (mo', v) := by simpa using h'
        exact Or.inr ⟨congrArg Prod.fst he, (congrArg Prod.snd he).symm⟩
    · rintro (h | ⟨rfl, he⟩)
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (by rw [he]; simp)

/-! ## `interestedObservers` -/

/-- 内側の畳み込み（一つの node の registered observer list）。 -/
theorem mem_interestedObservers_inner (s : DOMState) (rec : MutationRecord) (ov : Option String)
    (acc : List (Nat × Option String)) (m : NodeId) (mo : Nat) :
    mo ∈ (((s.registrations.filter fun r => r.node == m).foldl (fun acc r =>
        if r.interestedIn rec.target rec.type rec.attributeName rec.attributeNamespace then
          addInterested acc r.observer
            (if (rec.type == .characterData && r.characterDataOldValue)
                || (rec.type == .attributes && r.attributeOldValue) then ov else none)
        else acc) acc).map (·.1)) ↔
      mo ∈ (acc.map (·.1)) ∨
        ∃ r ∈ s.registrations.filter fun r => r.node == m,
          r.interestedIn rec.target rec.type rec.attributeName rec.attributeNamespace = true ∧
            r.observer = mo := by
  refine mem_foldl_of_step _ (fun (r : Registration) (mo : Nat) =>
    Registration.interestedIn r rec.target rec.type rec.attributeName rec.attributeNamespace
        = true ∧ r.observer = mo) ?_ _ acc mo
  intro acc' r mo'
  split
  · next hc =>
    rw [mem_addInterested]
    constructor
    · rintro (h | rfl)
      · exact Or.inl h
      · exact Or.inr ⟨hc, rfl⟩
    · rintro (h | ⟨-, rfl⟩)
      · exact Or.inl h
      · exact Or.inr rfl
  · next hc =>
    constructor
    · exact Or.inl
    · rintro (h | ⟨hc', -⟩)
      · exact h
      · exact absurd hc' hc

/-- **どの observer が record を受け取るか。** -/
theorem mem_interestedObservers (s : DOMState) (rec : MutationRecord) (ov : Option String)
    (mo : Nat) :
    mo ∈ ((interestedObservers s rec ov).map (·.1)) ↔
      ∃ r ∈ s.registrations, r.node ∈ (rec.target :: ancestors s.tree rec.target) ∧
        r.interestedIn rec.target rec.type rec.attributeName rec.attributeNamespace = true ∧
          r.observer = mo := by
  unfold interestedObservers
  rw [mem_foldl_of_step _ (fun (m : NodeId) (mo : Nat) =>
    ∃ r ∈ s.registrations.filter fun r => r.node == m,
      Registration.interestedIn r rec.target rec.type rec.attributeName rec.attributeNamespace
          = true ∧ r.observer = mo)
    (fun acc m mo => mem_interestedObservers_inner s rec ov acc m mo)]
  simp only [List.map_nil, List.not_mem_nil, false_or]
  constructor
  · rintro ⟨m, hm, r, hr, hc, rfl⟩
    obtain ⟨hrmem, hrnode⟩ := List.mem_filter.mp hr
    refine ⟨r, hrmem, ?_, hc, rfl⟩
    simp only [beq_iff_eq] at hrnode
    rw [hrnode]
    exact hm
  · rintro ⟨r, hrmem, hnode, hc, rfl⟩
    exact ⟨r.node, hnode, r, List.mem_filter.mpr ⟨hrmem, by simp⟩, hc, rfl⟩

theorem nodup_interestedObservers (s : DOMState) (rec : MutationRecord) (ov : Option String) :
    ((interestedObservers s rec ov).map (·.1)).Nodup := by
  unfold interestedObservers
  refine nodup_foldl_of_step _ (fun acc m hacc => ?_) _ [] (by simp)
  refine nodup_foldl_of_step _ (fun acc' r hacc' => ?_) _ acc hacc
  split
  · exact nodup_addInterested _ _ _ hacc'
  · exact hacc'

/-! ## oldValue が載る observer（characterData / attributes） -/

theorem allValue_foldl_of_step {α : Type} {P : Option String → Prop}
    (step : List (Nat × Option String) → α → List (Nat × Option String))
    (hstep : ∀ acc a, (∀ p ∈ acc, P p.2) → ∀ p ∈ step acc a, P p.2) :
    ∀ (l : List α) (acc : List (Nat × Option String)),
      (∀ p ∈ acc, P p.2) → ∀ p ∈ l.foldl step acc, P p.2 := by
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons a rest ih => intro acc h; exact ih (step acc a) (hstep acc a h)


/-- 内側の畳み込み。`(mo, ov)` が入るのは、flag の立った registration があるときだけである。 -/
theorem mem_pair_interestedObservers_inner (s : DOMState) (rec : MutationRecord)
    (ov : Option String) (hov : ov.isSome) (acc : List (Nat × Option String)) (m : NodeId)
    (mo : Nat) :
    ((mo, ov) ∈ ((s.registrations.filter fun r => r.node == m).foldl (fun acc r =>
        if r.interestedIn rec.target rec.type rec.attributeName rec.attributeNamespace then
          addInterested acc r.observer
            (if (rec.type == .characterData && r.characterDataOldValue)
                || (rec.type == .attributes && r.attributeOldValue) then ov else none)
        else acc) acc)) ↔
      ((mo, ov) ∈ acc ∨
        ∃ r ∈ s.registrations.filter fun r => r.node == m,
          Registration.interestedIn r rec.target rec.type rec.attributeName rec.attributeNamespace
              = true ∧
            ((rec.type == RecordType.characterData && r.characterDataOldValue)
              || (rec.type == RecordType.attributes && r.attributeOldValue)) = true ∧
            r.observer = mo) := by
  refine mem_pair_foldl_of_step _ (fun (r : Registration) (mo : Nat) =>
    Registration.interestedIn r rec.target rec.type rec.attributeName rec.attributeNamespace
        = true ∧
      ((rec.type == RecordType.characterData && r.characterDataOldValue)
        || (rec.type == RecordType.attributes && r.attributeOldValue)) = true ∧
      r.observer = mo) ?_ _ acc mo
  intro acc' r mo'
  split
  · next hc =>
    rw [mem_pair_addInterested _ _ _ _ _ hov (by split <;> simp)]
    constructor
    · rintro (h | ⟨rfl, hval⟩)
      · exact Or.inl h
      · refine Or.inr ⟨hc, ?_, rfl⟩
        revert hval
        split
        · next hf => intro _; exact hf
        · intro hval; rw [← hval] at hov; simp at hov
    · rintro (h | ⟨-, hf, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨rfl, by rw [if_pos hf]⟩
  · next hc =>
    constructor
    · exact Or.inl
    · rintro (h | ⟨hc', -, -⟩)
      · exact h
      · exact absurd hc' hc

/-- **oldValue が載るのは、flag の立った registration を持つ observer だけである。** -/
theorem mem_pair_interestedObservers (s : DOMState) (rec : MutationRecord) (ov : Option String)
    (hov : ov.isSome) (mo : Nat) :
    ((mo, ov) ∈ interestedObservers s rec ov) ↔
      ∃ r ∈ s.registrations, r.node ∈ (rec.target :: ancestors s.tree rec.target) ∧
        Registration.interestedIn r rec.target rec.type rec.attributeName rec.attributeNamespace
            = true ∧
          ((rec.type == RecordType.characterData && r.characterDataOldValue)
            || (rec.type == RecordType.attributes && r.attributeOldValue)) = true ∧
          r.observer = mo := by
  unfold interestedObservers
  rw [mem_pair_foldl_of_step _ (fun (m : NodeId) (mo : Nat) =>
    ∃ r ∈ s.registrations.filter fun r => r.node == m,
      Registration.interestedIn r rec.target rec.type rec.attributeName rec.attributeNamespace
          = true ∧
        ((rec.type == RecordType.characterData && r.characterDataOldValue)
          || (rec.type == RecordType.attributes && r.attributeOldValue)) = true ∧
        r.observer = mo)
    (fun acc m mo => mem_pair_interestedObservers_inner s rec ov hov acc m mo)]
  simp only [List.not_mem_nil, false_or]
  constructor
  · rintro ⟨m, hm, r, hr, hc, hf, rfl⟩
    obtain ⟨hrmem, hrnode⟩ := List.mem_filter.mp hr
    refine ⟨r, hrmem, ?_, hc, hf, rfl⟩
    simp only [beq_iff_eq] at hrnode
    rw [hrnode]
    exact hm
  · rintro ⟨r, hrmem, hnode, hc, hf, rfl⟩
    exact ⟨r.node, hnode, r, List.mem_filter.mpr ⟨hrmem, by simp⟩, hc, hf, rfl⟩

/-- 畳み込みに現れる値は `ov` か `none` しかない。 -/
theorem value_mem_interestedObservers (s : DOMState) (rec : MutationRecord) (ov : Option String) :
    ∀ p ∈ interestedObservers s rec ov, p.2 = ov ∨ p.2 = none := by
  have hstep : ∀ (acc : List (Nat × Option String)) (mo : Nat) (v : Option String),
      (∀ p ∈ acc, p.2 = ov ∨ p.2 = none) → (v = ov ∨ v = none) →
      ∀ p ∈ addInterested acc mo v, p.2 = ov ∨ p.2 = none := by
    intro acc mo v hacc hv
    unfold addInterested
    split
    · split
      · exact hacc
      · intro p hp
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        split
        · exact hv
        · exact hacc q hq
    · intro p hp
      rcases List.mem_append.mp hp with hp' | hp'
      · exact hacc p hp'
      · have : p = (mo, v) := by simpa using hp'
        rw [this]; exact hv
  unfold interestedObservers
  refine allValue_foldl_of_step (P := fun v => v = ov ∨ v = none) _ (fun acc m hacc => ?_) _ []
    (by simp)
  refine allValue_foldl_of_step (P := fun v => v = ov ∨ v = none) _ (fun acc' r hacc' => ?_) _
    acc hacc
  split
  · exact hstep acc' r.observer _ hacc' (by split <;> simp)
  · exact hacc'

/-! ## childList の record には oldValue が付かない -/

theorem addInterested_none (acc : List (Nat × Option String)) (mo : Nat)
    (h : ∀ p ∈ acc, p.2 = none) : ∀ p ∈ addInterested acc mo none, p.2 = none := by
  unfold addInterested
  split
  · exact h
  · intro p hp
    rcases List.mem_append.mp hp with hp' | hp'
    · exact h p hp'
    · have : p = (mo, none) := by simpa using hp'
      rw [this]

theorem allNone_foldl_of_step {α : Type}
    (step : List (Nat × Option String) → α → List (Nat × Option String))
    (hstep : ∀ acc a, (∀ p ∈ acc, p.2 = none) → ∀ p ∈ step acc a, p.2 = none) :
    ∀ (l : List α) (acc : List (Nat × Option String)),
      (∀ p ∈ acc, p.2 = none) → ∀ p ∈ l.foldl step acc, p.2 = none := by
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons a rest ih => intro acc h; exact ih (step acc a) (hstep acc a h)

/-- `queue a mutation record` の step 2.3.3。childList の record は oldValue を持たない。 -/
theorem oldValue_none_of_childList (s : DOMState) (rec : MutationRecord) :
    ∀ p ∈ interestedObservers s rec none, p.2 = none := by
  unfold interestedObservers
  refine allNone_foldl_of_step _ (fun acc m hacc => ?_) _ [] (by simp)
  refine allNone_foldl_of_step _ (fun acc' r hacc' => ?_) _ acc hacc
  split
  · have hv : (if (rec.type == RecordType.characterData && r.characterDataOldValue)
        || (rec.type == RecordType.attributes && r.attributeOldValue) then
          (none : Option String) else none) = none := by split <;> rfl
    rw [hv]
    exact addInterested_none _ _ hacc'
  · exact hacc'

/-! ## record queue の変化 -/

theorem getElem?_enqueueRecord (obs : List ObserverState) (k mo : Nat) (rec : MutationRecord) :
    (enqueueRecord obs k rec)[mo]? =
      if k = mo then (obs[mo]?).map (fun o => { o with records := o.records ++ [rec] })
      else obs[mo]? := by
  unfold enqueueRecord
  split
  · next h =>
    split
    · next he => rw [← he, h]; rfl
    · rfl
  · next o h =>
    rw [List.getElem?_set]
    split
    · next he =>
      rw [← he, h]
      simp only [Option.map_some]
      have hlt : k < obs.length := by
        rcases Nat.lt_or_ge k obs.length with hk | hk
        · exact hk
        · rw [List.getElem?_eq_none hk] at h; simp at h
      rw [if_pos hlt]
    · rfl

/-- 畳み込みが一つの observer の queue に積むのは、その observer に向いた record だけである。 -/
theorem records_foldl_enqueue (rec : MutationRecord) :
    ∀ (l : List (Nat × Option String)) (obs : List ObserverState) (mo : Nat)
      (o o' : ObserverState), obs[mo]? = some o →
      (l.foldl (fun obs p => enqueueRecord obs p.1 { rec with oldValue := p.2 }) obs)[mo]?
          = some o' →
      o'.records = o.records ++ (l.filterMap fun p =>
        if p.1 = mo then some { rec with oldValue := p.2 } else none) := by
  intro l
  induction l with
  | nil =>
    intro obs mo o o' hobs hfold
    rw [List.foldl_nil, hobs] at hfold
    cases hfold
    simp
  | cons p rest ih =>
    intro obs mo o o' hobs hfold
    rw [List.foldl_cons] at hfold
    by_cases hp : p.1 = mo
    · have hnext : (enqueueRecord obs p.1 { rec with oldValue := p.2 })[mo]?
          = some { o with records := o.records ++ [{ rec with oldValue := p.2 }] } := by
        rw [getElem?_enqueueRecord, if_pos hp, hobs]
        rfl
      have := ih _ mo _ o' hnext hfold
      rw [this]
      simp only [List.filterMap_cons, if_pos hp]
      simp
    · have hnext : (enqueueRecord obs p.1 { rec with oldValue := p.2 })[mo]? = some o := by
        rw [getElem?_enqueueRecord, if_neg hp, hobs]
      have := ih _ mo _ o' hnext hfold
      rw [this]
      simp only [List.filterMap_cons, if_neg hp]

theorem filterMap_eq_nil_of_not_mem {β : Type} (g : Nat × Option String → β) (mo : Nat) :
    ∀ (l : List (Nat × Option String)), mo ∉ l.map (·.1) →
      (l.filterMap fun p => if p.1 = mo then some (g p) else none) = [] := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons p rest ih =>
    intro h
    have hp : p.1 ≠ mo := fun he => h (List.mem_map.mpr ⟨p, List.mem_cons_self, he⟩)
    rw [List.filterMap_cons, if_neg hp]
    exact ih fun hm => h (by simpa using Or.inr hm)

theorem filterMap_eq_single {β : Type} (g : Nat × Option String → β) (mo : Nat)
    (v : Option String) :
    ∀ (l : List (Nat × Option String)), ((l.map (·.1)).Nodup) → (mo, v) ∈ l →
      (l.filterMap fun p => if p.1 = mo then some (g p) else none) = [g (mo, v)] := by
  intro l
  induction l with
  | nil => intro _ h; simp at h
  | cons p rest ih =>
    intro hn hm
    rcases List.mem_cons.mp hm with rfl | hm'
    · rw [List.filterMap_cons, if_pos rfl]
      have hnot : mo ∉ rest.map (·.1) := by
        simp only [List.map_cons, List.nodup_cons] at hn
        exact hn.1
      rw [filterMap_eq_nil_of_not_mem g mo rest hnot]
    · have hp : p.1 ≠ mo := by
        simp only [List.map_cons, List.nodup_cons] at hn
        intro he
        exact hn.1 (by rw [he]; exact List.mem_map.mpr ⟨(mo, v), hm', rfl⟩)
      rw [List.filterMap_cons, if_neg hp]
      exact ih (by simp only [List.map_cons, List.nodup_cons] at hn; exact hn.2) hm'

theorem mem_foldl_addPendingObserver :
    ∀ (l : List (Nat × Option String)) (s : DOMState) (mo : Nat),
      mo ∈ (l.foldl (fun st p => addPendingObserver st p.1) s).pendingObservers ↔
        mo ∈ s.pendingObservers ∨ mo ∈ l.map (·.1) := by
  intro l
  induction l with
  | nil => intro s mo; simp
  | cons p rest ih =>
    intro s mo
    rw [List.foldl_cons, ih]
    have hstep : ∀ x, x ∈ (addPendingObserver s p.1).pendingObservers ↔
        x ∈ s.pendingObservers ∨ x = p.1 := by
      intro x
      unfold addPendingObserver
      split
      · next h =>
        constructor
        · exact Or.inl
        · rintro (hx | rfl)
          · exact hx
          · exact List.mem_of_elem_eq_true (by simpa using h)
      · show x ∈ (s.pendingObservers ++ [p.1]) ↔ _
        simp
    rw [hstep]
    constructor
    · rintro ((h | rfl) | h)
      · exact Or.inl h
      · exact Or.inr (by simp)
      · exact Or.inr (by simp [h])
    · rintro (h | h)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.mp h with rfl | h'
        · exact Or.inl (Or.inr rfl)
        · exact Or.inr h'

/-! ## nodeList だけを触る畳み込みは record queue を変えない -/

theorem records_foldl_preserved {α : Type} (step : List ObserverState → α → List ObserverState)
    (hlen : ∀ obs a, (step obs a).length = obs.length)
    (hstep : ∀ (obs : List ObserverState) (a : α) (mo : Nat) (o o' : ObserverState),
      obs[mo]? = some o → (step obs a)[mo]? = some o' → o'.records = o.records) :
    ∀ (l : List α) (obs : List ObserverState) (mo : Nat) (o o' : ObserverState),
      obs[mo]? = some o → (l.foldl step obs)[mo]? = some o' → o'.records = o.records := by
  intro l
  induction l with
  | nil => intro obs mo o o' h h'; rw [List.foldl_nil, h] at h'; cases h'; rfl
  | cons a rest ih =>
    intro obs mo o o' h h'
    rw [List.foldl_cons] at h'
    have hlt : mo < obs.length := by
      rcases Nat.lt_or_ge mo obs.length with hk | hk
      · exact hk
      · rw [List.getElem?_eq_none hk] at h; simp at h
    obtain ⟨o₁, h₁⟩ : ∃ o₁, (step obs a)[mo]? = some o₁ := by
      rcases hq : (step obs a)[mo]? with _ | o₁
      · rw [List.getElem?_eq_none_iff] at hq
        rw [hlen] at hq
        omega
      · exact ⟨o₁, rfl⟩
    rw [ih _ mo o₁ o' h₁ h', hstep obs a mo o o₁ h h₁]

/-- §4.2.3 remove step 20 は record queue を変えない（node list だけを触る）。 -/
theorem records_addTransientObservers (s : DOMState) (n p : NodeId) (mo : Nat)
    (o o' : ObserverState) (h : s.observers[mo]? = some o)
    (h' : (addTransientObservers s n p).observers[mo]? = some o') : o'.records = o.records := by
  unfold addTransientObservers at h'
  refine records_foldl_preserved _ ?_ ?_ _ s.observers mo o o' h h'
  · intro obs r
    split
    · rfl
    · split
      · rfl
      · exact List.length_set ..
  · intro obs r mo₁ o₁ o₂ h₁ h₂
    revert h₂
    split
    · intro h₂; rw [h₁] at h₂; cases h₂; rfl
    · next oo hoo =>
      split
      · intro h₂; rw [h₁] at h₂; cases h₂; rfl
      · intro h₂
        rw [List.getElem?_set] at h₂
        split at h₂
        · next he =>
          rw [← he, hoo] at h₁
          cases h₁
          split at h₂
          · cases h₂; rfl
          · simp at h₂
        · rw [h₁] at h₂; cases h₂; rfl

/-! ## `queueMutationRecord` の三つの効果 -/

theorem observers_queueMutationRecord (s : DOMState) (rec : MutationRecord) (ov : Option String) :
    (queueMutationRecord s rec ov).observers =
      (interestedObservers s rec ov).foldl
        (fun obs q => enqueueRecord obs q.1 { rec with oldValue := q.2 }) s.observers := by
  unfold queueMutationRecord
  rw [queueMutationObserverMicrotask_observers, foldl_addPendingObserver_observers]

theorem mem_pendingObservers_queueMutationRecord (s : DOMState) (rec : MutationRecord)
    (ov : Option String) (mo : Nat) :
    mo ∈ (queueMutationRecord s rec ov).pendingObservers ↔
      mo ∈ s.pendingObservers ∨ mo ∈ ((interestedObservers s rec ov).map (·.1)) := by
  unfold queueMutationRecord
  have hmt : ∀ st : DOMState,
      (queueMutationObserverMicrotask st).pendingObservers = st.pendingObservers := by
    intro st; unfold queueMutationObserverMicrotask; split <;> rfl
  rw [hmt, mem_foldl_addPendingObserver]

theorem microtaskQueued_queueMutationRecord (s : DOMState) (rec : MutationRecord)
    (ov : Option String) : (queueMutationRecord s rec ov).microtaskQueued = true := by
  have hmt : ∀ st : DOMState, (queueMutationObserverMicrotask st).microtaskQueued = true := by
    intro st
    unfold queueMutationObserverMicrotask
    split
    · next h => exact h
    · rfl
  unfold queueMutationRecord
  exact hmt _

end Dom
