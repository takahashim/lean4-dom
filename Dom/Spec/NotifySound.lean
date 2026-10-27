import Dom.Spec.Notify
import Dom.Validity.Admissible

/-!
# notify・`disconnect()`・`takeRecords()` は関係を満たし、関係は結果を一つに決める

実行関数は「その observer の（transient の）registration を全部」外し、本文は「node list の node にある
もの」を外す。admissible な状態では registration の node はその observer の node list にある
（`ObserverRegistrationsValid` の `ListedIn`）ので、二つは同じ列になる（`filter_listed`）。
-/

namespace Dom.Spec

open Dom

/-- observer が mo の registration は、mo の node list に node がある。 -/
theorem listed_of_valid {s : DOMState} (hv : ObserverRegistrationsValid s) {mo : Nat}
    {o : ObserverState} (ho : s.observers[mo]? = some o) {r : Registration}
    (hr : r ∈ s.registrations) (hmo : r.observer = mo) : o.nodeList.contains r.node = true := by
  obtain ⟨-, -, o', ho', hm⟩ := hv r hr
  rw [hmo, ho] at ho'
  cases ho'
  simpa using hm

/-- observer が無い番号を指す registration は無い。 -/
theorem no_reg_of_none {s : DOMState} (hv : ObserverRegistrationsValid s) {mo : Nat}
    (ho : s.observers[mo]? = none) {r : Registration} (hr : r ∈ s.registrations) :
    r.observer ≠ mo := by
  intro hmo
  obtain ⟨-, -, o', ho', -⟩ := hv r hr
  rw [hmo, ho] at ho'
  cases ho'

theorem filter_listed {s : DOMState} (hv : ObserverRegistrationsValid s) {mo : Nat}
    {o : ObserverState} (ho : s.observers[mo]? = some o) (p : Registration → Bool) :
    s.registrations.filter (fun r => !(p r && r.observer == mo)) =
      s.registrations.filter (fun r => !(p r && r.observer == mo && o.nodeList.contains r.node)) := by
  apply List.filter_congr
  intro r hr
  by_cases hmo : r.observer = mo
  · have hl := listed_of_valid hv ho hr hmo
    have hl' : r.node ∈ o.nodeList := by simpa using hl
    simp [hmo, hl']
  · simp [hmo]

/-! ## notify -/

theorem notifyOne_sound {s : DOMState} (h : AdmissibleDOMState s) (mo : Nat) :
    ObserverNotified s mo (notifyOne s mo).1 (notifyOne s mo).2 := by
  have hv := h.observerRegistrations
  unfold notifyOne MutationObserver.takeRecords removeTransients
  cases ho : s.observers[mo]? with
  | none =>
    refine Or.inr ⟨ho, ?_, rfl⟩
    simp only []
    have : s.registrations.filter (fun r => !(r.transient && r.observer == mo)) = s.registrations := by
      apply List.filter_eq_self.mpr
      intro r hr
      simp [no_reg_of_none hv ho hr]
    rw [this]
  | some o =>
    refine Or.inl ⟨o, ho, rfl, ?_⟩
    simp only []
    rw [filter_listed hv ho (fun r => r.transient)]

theorem notifyEach_sound :
    ∀ (ms : List Nat) {s : DOMState}, AdmissibleDOMState s →
      NotifiedEach s ms (notifyEach s ms).1 (notifyEach s ms).2
  | [], _, _ => .nil
  | mo :: rest, s, h => by
    have h₁ : AdmissibleDOMState (notifyOne s mo).1 :=
      admissible_removeTransients (admissible_takeRecords h mo) mo
    have := NotifiedEach.cons (notifyOne_sound h mo) (notifyEach_sound rest h₁)
    show NotifiedEach s (mo :: rest) (notifyEach (notifyOne s mo).1 rest).1
      (if (notifyOne s mo).2.isEmpty then (notifyEach (notifyOne s mo).1 rest).2
        else (mo, (notifyOne s mo).2) :: (notifyEach (notifyOne s mo).1 rest).2)
    by_cases he : (notifyOne s mo).2 = []
    · rw [if_pos (by simp [he])]
      rw [if_pos he] at this
      exact this
    · rw [if_neg (by simpa using he)]
      rw [if_neg he] at this
      exact this

/-- step 2 の notify list：実行側の `mergeSort` は pending mutation observers を昇順に並べる。 -/
theorem notifyList_sorted (l : List Nat) :
    (l.mergeSort (· ≤ ·)).Perm l ∧ (l.mergeSort (· ≤ ·)).Pairwise (· ≤ ·) := by
  refine ⟨List.mergeSort_perm l _, ?_⟩
  have := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l
  exact this.imp fun h => of_decide_eq_true h

/-- 昇順に並べた列は一つしかない。 -/
theorem notifyList_unique {l₁ l₂ l : List Nat} (hp₁ : l₁.Perm l) (hs₁ : l₁.Pairwise (· ≤ ·))
    (hp₂ : l₂.Perm l) (hs₂ : l₂.Pairwise (· ≤ ·)) : l₁ = l₂ :=
  List.Perm.eq_of_pairwise (fun _ _ _ _ hab hba => Nat.le_antisymm hab hba) hs₁ hs₂
    (hp₁.trans hp₂.symm)

/-- **"notify mutation observers" は関係を満たす。** -/
theorem notifyMutationObservers_sound {s : DOMState} (h : AdmissibleDOMState s) :
    NotifyResult s (notifyMutationObservers s).1 (notifyMutationObservers s).2 :=
  ⟨_, (notifyList_sorted s.pendingObservers).1, (notifyList_sorted s.pendingObservers).2,
    notifyEach_sound _ ⟨h.structural, h.nodeDocuments, h.documentTrees, h.rangeEndpoints,
      h.iterators, fun r hr => h.observerRegistrations r hr, h.attributes⟩⟩

theorem observerNotified_deterministic {s s₁ s₂ : DOMState} {mo : Nat} {r₁ r₂ : List MutationRecord}
    (h₁ : ObserverNotified s mo s₁ r₁) (h₂ : ObserverNotified s mo s₂ r₂) : s₁ = s₂ ∧ r₁ = r₂ := by
  rcases h₁ with ⟨o, ho, rfl, rfl⟩ | ⟨ho, rfl, rfl⟩ <;>
    rcases h₂ with ⟨o', ho', rfl, rfl⟩ | ⟨ho', rfl, rfl⟩
  · rw [ho] at ho'; cases ho'; exact ⟨rfl, rfl⟩
  · rw [ho] at ho'; cases ho'
  · rw [ho] at ho'; cases ho'
  · exact ⟨rfl, rfl⟩

theorem notifiedEach_deterministic :
    ∀ {s : DOMState} {ms : List Nat} {s₁ s₂ : DOMState} {o₁ o₂ : List (Nat × List MutationRecord)},
      NotifiedEach s ms s₁ o₁ → NotifiedEach s ms s₂ o₂ → s₁ = s₂ ∧ o₁ = o₂
  | _, _, _, _, _, _, .nil, .nil => ⟨rfl, rfl⟩
  | _, _, _, _, _, _, .cons ha hrest, .cons hb hrest' => by
    obtain ⟨rfl, rfl⟩ := observerNotified_deterministic ha hb
    obtain ⟨rfl, rfl⟩ := notifiedEach_deterministic hrest hrest'
    exact ⟨rfl, rfl⟩

/-- **関係は配送の結果を一つに決め、それは実行関数の結果である。** -/
theorem notifyMutationObservers_complete {s s' : DOMState} {out : List (Nat × List MutationRecord)}
    (h : AdmissibleDOMState s) (hr : NotifyResult s s' out) :
    (s', out) = notifyMutationObservers s := by
  obtain ⟨l₁, hp₁, hs₁, he₁⟩ := hr
  obtain ⟨l₂, hp₂, hs₂, he₂⟩ := notifyMutationObservers_sound h
  have := notifyList_unique hp₁ hs₁ hp₂ hs₂
  subst this
  obtain ⟨h1, h2⟩ := notifiedEach_deterministic he₁ he₂
  rw [h1, h2]

/-! ## disconnect・takeRecords -/

/-- **`disconnect()` は関係を満たす。** -/
theorem disconnect_sound {s : DOMState} (h : AdmissibleDOMState s) (mo : Nat) :
    DisconnectResult s mo (MutationObserver.disconnect s mo) := by
  have hv := h.observerRegistrations
  unfold MutationObserver.disconnect
  cases ho : s.observers[mo]? with
  | none =>
    refine Or.inr ⟨ho, ?_⟩
    simp only []
    have : s.registrations.filter (fun r => r.observer != mo) = s.registrations := by
      apply List.filter_eq_self.mpr
      intro r hr
      simp [no_reg_of_none hv ho hr]
    rw [this]
  | some o =>
    refine Or.inl ⟨o, ho, ?_⟩
    simp only []
    have e : s.registrations.filter (fun r => r.observer != mo) =
        s.registrations.filter (fun r => !(r.observer == mo && o.nodeList.contains r.node)) := by
      apply List.filter_congr
      intro r hr
      by_cases hmo : r.observer = mo
      · have hl' : r.node ∈ o.nodeList := by simpa using listed_of_valid hv ho hr hmo
        simp [hmo, hl']
      · have : (r.observer == mo) = false := by simpa using hmo
        simp [this, bne]
    rw [e]

theorem disconnect_complete {s s' : DOMState} {mo : Nat} (h : AdmissibleDOMState s)
    (hr : DisconnectResult s mo s') : s' = MutationObserver.disconnect s mo := by
  rcases disconnect_sound h mo with ⟨o, ho, he⟩ | ⟨ho, he⟩ <;>
    rcases hr with ⟨o', ho', rfl⟩ | ⟨ho', rfl⟩
  · rw [ho] at ho'; cases ho'; exact he.symm
  · rw [ho] at ho'; cases ho'
  · rw [ho] at ho'; cases ho'
  · exact he.symm

/-- **`takeRecords()` は関係を満たす。** -/
theorem takeRecords_sound (s : DOMState) (mo : Nat) :
    TakeRecordsResult s mo (MutationObserver.takeRecords s mo).1 (MutationObserver.takeRecords s mo).2 := by
  unfold MutationObserver.takeRecords
  cases ho : s.observers[mo]? with
  | none => exact Or.inr ⟨ho, rfl, rfl⟩
  | some o => exact Or.inl ⟨o, ho, rfl, rfl⟩

theorem takeRecords_complete {s s' : DOMState} {mo : Nat} {records : List MutationRecord}
    (hr : TakeRecordsResult s mo s' records) : (s', records) = MutationObserver.takeRecords s mo := by
  unfold MutationObserver.takeRecords
  rcases hr with ⟨o, ho, rfl, rfl⟩ | ⟨ho, rfl, rfl⟩ <;> rw [ho]

end Dom.Spec
