import Dom.Spec.ObserverOrder
import Dom.Properties.Record

/-!
# record を積む実行関数は pending mutation observers の順を本文どおりにする

`queueMutationRecord` は interested observers を二重の畳み込み（inclusive ancestor ごと、registration ごと）で
集め、その順に `addPendingObserver` する。ここでは、その結果が `PendingAppended`（本文の step 3-4 の順）に
なることを示す（`pendingAppended_queueMutationRecord`）。
-/

namespace Dom.Spec

open Dom

/-! ## 列の補題 -/

/-- ordered set への append を一つ行う。 -/
theorem appendNew_cons (acc : List Nat) (x : Nat) (xs : List Nat) :
    appendNew acc (x :: xs) = appendNew (if x ∈ acc then acc else acc ++ [x]) xs := rfl

theorem appendNew_append (acc xs ys : List Nat) :
    appendNew acc (xs ++ ys) = appendNew (appendNew acc xs) ys := by
  unfold appendNew; rw [List.foldl_append]

theorem appendNew_nil (acc : List Nat) : appendNew acc [] = acc := rfl

/-- 実行側の `ancestors` は、整った木では本文の inclusive ancestor の列を与える。 -/
theorem inclusiveAncestorsUp_ancestors {t : Tree} (hwf : WellFormed t) :
    ∀ (k : Nat) (n : NodeId), (ancestors t n).length ≤ k →
      InclusiveAncestorsUp t n (n :: ancestors t n) := by
  intro k
  induction k with
  | zero =>
    intro n hk
    cases hp : parentOf t n with
    | none =>
      have : ancestors t n = [] := by
        unfold ancestors
        cases t.size with
        | zero => rfl
        | succ f => exact ancestorChain_succ_none hp
      rw [this]; exact .top hp
    | some p => rw [ancestors_eq_cons hwf hp] at hk; simp at hk
  | succ k ih =>
    intro n hk
    cases hp : parentOf t n with
    | none =>
      have : ancestors t n = [] := by
        unfold ancestors
        cases t.size with
        | zero => rfl
        | succ f => exact ancestorChain_succ_none hp
      rw [this]; exact .top hp
    | some p =>
      rw [ancestors_eq_cons hwf hp] at hk ⊢
      exact .up hp (ih p (by simp at hk; omega))

theorem inclusiveAncestorsUp_of_wf {t : Tree} (hwf : WellFormed t) (n : NodeId) :
    InclusiveAncestorsUp t n (n :: ancestors t n) :=
  inclusiveAncestorsUp_ancestors hwf _ n (Nat.le_refl _)

/-! ## interested observers の順 -/

theorem any_fst_iff (acc : List (Nat × Option String)) (mo : Nat) :
    acc.any (fun p => p.1 == mo) = true ↔ mo ∈ acc.map (·.1) := by
  simp [List.any_eq_true]

/-- 一つの node の registered observer list を畳む段。 -/
theorem map_fst_inner (P : Registration → Bool) (val : Registration → Option String) :
    ∀ (l : List Registration) (acc : List (Nat × Option String)),
      (l.foldl (fun acc r => if P r then addInterested acc r.observer (val r) else acc) acc).map (·.1) =
        appendNew (acc.map (·.1)) ((l.filter P).map (·.observer))
  | [], acc => rfl
  | r :: l, acc => by
    rw [List.foldl_cons, map_fst_inner P val l]
    by_cases hp : P r = true
    · rw [if_pos hp, List.filter_cons_of_pos hp, List.map_cons, appendNew_cons, map_fst_addInterested]
      congr 1
      by_cases hm : r.observer ∈ acc.map (·.1)
      · rw [if_pos ((any_fst_iff acc r.observer).mpr hm), if_pos hm]
      · rw [if_neg (fun h => hm ((any_fst_iff acc r.observer).mp h)), if_neg hm]
    · rw [if_neg hp, List.filter_cons_of_neg hp]

/-- **実行側の interested observers の順は、本文の順と一致する。** -/
theorem map_fst_interestedObservers (s : DOMState) (rec : MutationRecord) (ov : Option String)
    (P : Registration → Bool)
    (hP : ∀ r, r.interestedIn rec.target rec.type rec.attributeName rec.attributeNamespace = P r) :
    (interestedObservers s rec ov).map (·.1) =
      interestedOrder s.registrations (rec.target :: ancestors s.tree rec.target) P := by
  unfold interestedObservers interestedOrder
  generalize rec.target :: ancestors s.tree rec.target = nodes
  have key : ∀ (nodes : List NodeId) (acc : List (Nat × Option String)),
      (nodes.foldl (fun acc n =>
        (s.registrations.filter fun r => r.node == n).foldl (fun acc r =>
          if r.interestedIn rec.target rec.type rec.attributeName rec.attributeNamespace then
            addInterested acc r.observer
              (if (rec.type == .characterData && r.characterDataOldValue)
                  || (rec.type == .attributes && r.attributeOldValue) then ov else none)
          else acc) acc) acc).map (·.1) =
        appendNew (acc.map (·.1))
          (nodes.flatMap fun n => ((regsOn s.registrations n).filter P).map (·.observer)) := by
    intro nodes
    induction nodes with
    | nil => intro acc; rfl
    | cons n ns ih =>
      intro acc
      rw [List.foldl_cons, ih, List.flatMap_cons, appendNew_append]
      congr 1
      have := map_fst_inner (fun r => r.interestedIn rec.target rec.type rec.attributeName
          rec.attributeNamespace)
        (fun r => if (rec.type == .characterData && r.characterDataOldValue)
                  || (rec.type == .attributes && r.attributeOldValue) then ov else none)
        (s.registrations.filter fun r => r.node == n) acc
      rw [this]
      have hf : (s.registrations.filter fun r => r.node == n).filter
          (fun r => r.interestedIn rec.target rec.type rec.attributeName rec.attributeNamespace) =
          (regsOn s.registrations n).filter P := by
        unfold regsOn
        congr 1
        funext r
        exact hP r
      rw [hf]
  exact key nodes []

/-! ## pending mutation observers -/

theorem pending_foldl_addPendingObserver :
    ∀ (l : List Nat) (st : DOMState),
      (l.foldl (fun st mo => addPendingObserver st mo) st).pendingObservers =
        appendNew st.pendingObservers l
  | [], _ => rfl
  | mo :: l, st => by
    rw [List.foldl_cons, pending_foldl_addPendingObserver l, appendNew_cons]
    congr 1
    unfold addPendingObserver
    by_cases h : mo ∈ st.pendingObservers
    · rw [if_pos (by simpa using h), if_pos h]
    · rw [if_neg (by simpa using h), if_neg h]

/-- **`queueMutationRecord` は pending mutation observers を本文の順に伸ばす。** -/
theorem pendingAppended_queueMutationRecord {s : DOMState} (hwf : WellFormed s.tree)
    (rec : MutationRecord) (ov : Option String) (P : Registration → Bool)
    (hP : ∀ r, r.interestedIn rec.target rec.type rec.attributeName rec.attributeNamespace = P r) :
    PendingAppended s (queueMutationRecord s rec ov) rec.target P := by
  refine ⟨_, inclusiveAncestorsUp_of_wf hwf rec.target, ?_⟩
  rw [← map_fst_interestedObservers s rec ov P hP]
  unfold queueMutationRecord
  have hmt : ∀ st : DOMState,
      (queueMutationObserverMicrotask st).pendingObservers = st.pendingObservers := by
    intro st; unfold queueMutationObserverMicrotask; split <;> rfl
  rw [hmt]
  have : ∀ (l : List (Nat × Option String)) (st : DOMState),
      l.foldl (fun st p => addPendingObserver st p.1) st =
        (l.map (·.1)).foldl (fun st mo => addPendingObserver st mo) st := by
    intro l; induction l with
    | nil => intro st; rfl
    | cons p l ih => intro st; simp only [List.foldl_cons, List.map_cons]; exact ih _
  rw [this, pending_foldl_addPendingObserver]

/-- well-formed を仮定しない形。interested observers の順は実行側の `ancestors` の列で決まる。 -/
theorem pending_queueMutationRecord (st : DOMState) (rec : MutationRecord) (ov : Option String)
    (P : Registration → Bool)
    (hP : ∀ r, r.interestedIn rec.target rec.type rec.attributeName rec.attributeNamespace = P r) :
    (queueMutationRecord st rec ov).pendingObservers =
      appendNew st.pendingObservers
        (interestedOrder st.registrations (rec.target :: ancestors st.tree rec.target) P) := by
  rw [← map_fst_interestedObservers st rec ov P hP]
  unfold queueMutationRecord
  have hmt : ∀ x : DOMState,
      (queueMutationObserverMicrotask x).pendingObservers = x.pendingObservers := by
    intro x; unfold queueMutationObserverMicrotask; split <;> rfl
  rw [hmt]
  have : ∀ (l : List (Nat × Option String)) (x : DOMState),
      l.foldl (fun x p => addPendingObserver x p.1) x =
        (l.map (·.1)).foldl (fun x mo => addPendingObserver x mo) x := by
    intro l; induction l with
    | nil => intro x; rfl
    | cons p l ih => intro x; simp only [List.foldl_cons, List.map_cons]; exact ih _
  rw [this, pending_foldl_addPendingObserver]

/-- 列に無い node の上の registration を足しても、interested observers の順は変わらない。 -/
theorem interestedOrder_append_off (regs B : List Registration) (nodes : List NodeId)
    (P : Registration → Bool) (h : ∀ x ∈ B, x.node ∉ nodes) :
    interestedOrder (regs ++ B) nodes P = interestedOrder regs nodes P := by
  unfold interestedOrder
  congr 1
  have key : ∀ ns : List NodeId, (∀ n ∈ ns, n ∈ nodes) →
      (ns.flatMap fun n => ((regsOn (regs ++ B) n).filter P).map (·.observer)) =
        (ns.flatMap fun n => ((regsOn regs n).filter P).map (·.observer)) := by
    intro ns
    induction ns with
    | nil => intro _; rfl
    | cons n ns ih =>
      intro hns
      rw [List.flatMap_cons, List.flatMap_cons, ih (fun m hm => hns m (by simp [hm]))]
      have hn := hns n (by simp)
      have : B.filter (fun r => r.node == n) = [] :=
        List.filter_eq_nil_iff.mpr fun x hx he => h x hx (by
          have : x.node = n := by simpa using he
          rw [this]; exact hn)
      unfold regsOn
      rw [List.filter_append, this, List.append_nil]
  exact key nodes (fun _ h => h)

/-! ## record の種類ごとの条件 -/

theorem interestedIn_childList (target : NodeId) (r : Registration) :
    r.interestedIn target .childList none none = childListInterest target r := by
  simp only [Registration.interestedIn, childListInterest, Bool.and_comm]

theorem interestedIn_characterData (target : NodeId) (r : Registration) :
    r.interestedIn target .characterData none none = characterDataInterest target r := by
  simp only [Registration.interestedIn, characterDataInterest, Bool.and_comm]

theorem interestedIn_attributes (target : NodeId) (name : String) (ns : Option String)
    (r : Registration) :
    r.interestedIn target .attributes (some name) ns = attributeInterest target name ns r := by
  unfold Registration.interestedIn attributeInterest
  cases r.attributeFilter <;> simp [Bool.and_comm, Bool.and_left_comm, Bool.and_assoc]

end Dom.Spec
