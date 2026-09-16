import Url.RoundtripQuery

/-!
# 文字の性質
-/

namespace Url

open Infra

/-! ## 文字の性質

前処理が落とす文字（前後の C0 control or space、tab と newline）が
serialize した文字列に現れないことを、成分ごとの percent-encode set から出す。
-/

/-- C0 control percent-encode set に入らない文字は tab でも newline でもない。 -/
theorem ne_tab_of_c0Set {c : Char} (h : c0ControlSet c = false) :
    c.toNat ≠ 0x09 ∧ c.toNat ≠ 0x0A ∧ c.toNat ≠ 0x0D := by
  simp only [c0ControlSet, isC0Control, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    Nat.not_le, Nat.not_lt] at h
  omega

/-- C0 control percent-encode set に入らない文字は C0 control でもない。space は別に見る。 -/
theorem ne_c0_of_c0Set {c : Char} (h : c0ControlSet c = false) (hs : ¬c = ' ') :
    isC0ControlOrSpace c = false := by
  simp only [c0ControlSet, isC0Control, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    Nat.not_le, Nat.not_lt] at h
  simp only [isC0ControlOrSpace, decide_eq_false_iff_not, Nat.not_le]
  have h20 : c.toNat ≠ 0x20 := by
    intro he
    exact hs (by rw [← Char.ofNat_toNat c, he])
  omega

/-- query set に入らなければ C0 control percent-encode set にも入らない。 -/
theorem c0Set_of_querySet {c : Char} (h : querySet c = false) : c0ControlSet c = false := by
  simp only [querySet, Bool.or_eq_false_iff] at h
  exact h.1.1.1.1.1

/-- fragment set についても同じ。 -/
theorem c0Set_of_fragmentSet {c : Char} (h : fragmentSet c = false) : c0ControlSet c = false := by
  simp only [fragmentSet, Bool.or_eq_false_iff] at h
  exact h.1.1.1.1.1

/-- query set に入らない文字は space でもない。 -/
theorem ne_space_of_querySet {c : Char} (h : querySet c = false) : ¬c = ' ' := by
  intro he; rw [he] at h; revert h; decide

/-- fragment set についても同じ。 -/
theorem ne_space_of_fragmentSet {c : Char} (h : fragmentSet c = false) : ¬c = ' ' := by
  intro he; rw [he] at h; revert h; decide

/-- special-query set に入らない文字は query set にも入らない。 -/
theorem querySet_of_specialQuerySet {c : Char} (h : specialQuerySet c = false) :
    querySet c = false := by
  simp only [specialQuerySet, Bool.or_eq_false_iff] at h
  exact h.1

/-- special かどうかで選ぶ query set のどちらでも、入らなければ query set に入らない。 -/
theorem querySet_of_ite {b : Bool} {c : Char}
    (h : (if b then specialQuerySet else querySet) c = false) : querySet c = false := by
  cases b with
  | true => exact querySet_of_specialQuerySet (by simpa using h)
  | false => simpa using h

/-- query と fragment に現れる文字は、C0 control でも space でもない。 -/
theorem qfList_c0 {q f : Option String}
    (hqc : ∀ s, q = some s → ∀ c ∈ s.toList, querySet c = false)
    (hfc : ∀ s, f = some s → ∀ c ∈ s.toList, fragmentSet c = false) :
    ∀ c ∈ qfList q f, isC0ControlOrSpace c = false := by
  intro c hcm
  unfold qfList at hcm
  rcases List.mem_append.mp hcm with hcm | hcm
  · cases q with
    | none => simp at hcm
    | some qs =>
      rcases List.mem_cons.mp hcm with rfl | hcm
      · decide
      · exact ne_c0_of_c0Set (c0Set_of_querySet (hqc qs rfl c hcm))
          (ne_space_of_querySet (hqc qs rfl c hcm))
  · cases f with
    | none => simp at hcm
    | some fs =>
      rcases List.mem_cons.mp hcm with rfl | hcm
      · decide
      · exact ne_c0_of_c0Set (c0Set_of_fragmentSet (hfc fs rfl c hcm))
          (ne_space_of_fragmentSet (hfc fs rfl c hcm))

end Url
