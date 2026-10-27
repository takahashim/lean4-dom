import Dom.Spec.ObsEq
import Dom.Observer.Deliver

/-! # 順序まで含めた observer の配送は `ObsEq` を保つ -/

namespace Dom.Spec
open Dom

private theorem notifyOne_queues_congr {s sb : DOMState}
    (h : ∀ mo : Nat, (sb.observers[mo]?).map (·.records) = (s.observers[mo]?).map (·.records))
    (mo : Nat) :
    (notifyOne sb mo).2 = (notifyOne s mo).2 ∧
    ∀ i : Nat, (((notifyOne sb mo).1).observers[i]?).map (·.records) =
      (((notifyOne s mo).1).observers[i]?).map (·.records) := by
  have hm := h mo
  cases hs : s.observers[mo]? with
  | none =>
    have hb : sb.observers[mo]? = none := by
      cases hx : sb.observers[mo]? with
      | none => rfl
      | some o => simp [hs, hx] at hm
    simp only [notifyOne, MutationObserver.takeRecords, hs, hb, removeTransients]
    exact ⟨True.intro, h⟩
  | some o =>
    obtain ⟨ob, hb, hrecs⟩ : ∃ ob, sb.observers[mo]? = some ob ∧ ob.records = o.records := by
      cases hx : sb.observers[mo]? with
      | none => simp [hs, hx] at hm
      | some ob => exact ⟨ob, rfl, by simpa [hs, hx] using hm⟩
    simp only [notifyOne, MutationObserver.takeRecords, hs, hb, removeTransients]
    refine ⟨hrecs, ?_⟩
    intro i
    by_cases hi : i = mo
    · subst hi
      have hslt := (List.getElem?_eq_some_iff.mp hs).1
      have hblt := (List.getElem?_eq_some_iff.mp hb).1
      simp [hslt, hblt]
    · simpa [List.getElem?_set, hi, Ne.symm hi] using h i

private theorem notifyEach_delivered_congr (ms : List Nat) {s sb : DOMState}
    (h : ∀ mo : Nat, (sb.observers[mo]?).map (·.records) = (s.observers[mo]?).map (·.records)) :
    (notifyEach sb ms).2 = (notifyEach s ms).2 := by
  induction ms generalizing s sb with
  | nil => rfl
  | cons mo ms ih =>
    obtain ⟨hr, hnext⟩ := notifyOne_queues_congr h mo
    simp only [notifyEach]
    rw [hr, ih hnext]

/-- 順序まで同値な状態は、observer の record をちょうど同じ列で配送する。 -/
theorem notifyMutationObservers_delivered_congr {s sb : DOMState} (h : ObsEq s sb) :
    (notifyMutationObservers sb).2 = (notifyMutationObservers s).2 := by
  unfold notifyMutationObservers
  rw [h.pendingOrder]
  exact notifyEach_delivered_congr _ h.records

end Dom.Spec
