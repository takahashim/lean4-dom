import Dom.Spec.Double
import Dom.Idl.Number

/-!
# 倍精度への丸めの実装は、最も近い値の関係を満たす

`Dom/Idl/Number.lean` の `JsNum.roundPos` が、`Dom/Spec/Double.lean` の関係 `NearestDouble` を満たすことを示す。
証明の部品は三つである。

1. `Nat.log2` から binade の指数を求める（`floor_spec`、`binade_roundPos`）。
2. 商と余りで、2^e の倍数のうち最も近いものに丸める（`round_spec`）。
3. 丸めた結果が 2^53 になったら書き直し、指数が 971 を超えれば +∞ にする。
-/

namespace Dom.Spec

open Dom.Idl

/-! ## 2 の冪との比較 -/

theorem ltPow2_iff (n d : Nat) (a : Int) : JsNum.ltPow2 n d a = true ↔ LtPow n d a := by
  unfold JsNum.ltPow2 LtPow JsNum.pow2 expNeg expPos
  split
  · rename_i h
    have h1 : (-a).toNat = 0 := by omega
    simp [h1]
  · rename_i h
    have h1 : a.toNat = 0 := by omega
    have h2 : (-a).toNat = (-a).toNat := rfl
    simp [h1]

theorem gePow_of {n d A B : Nat} {a : Int} (hn : 2 ^ A ≤ n) (hd : d ≤ 2 ^ B)
    (ha : a ≤ (A : Int) - B) : GePow n d a := by
  unfold GePow expPos expNeg
  have h1 : B + a.toNat ≤ A + (-a).toNat := by omega
  calc d * 2 ^ a.toNat ≤ 2 ^ B * 2 ^ a.toNat := Nat.mul_le_mul_right _ hd
    _ = 2 ^ (B + a.toNat) := (Nat.pow_add 2 B _).symm
    _ ≤ 2 ^ (A + (-a).toNat) := Nat.pow_le_pow_right (by decide) h1
    _ = 2 ^ A * 2 ^ (-a).toNat := Nat.pow_add 2 A _
    _ ≤ n * 2 ^ (-a).toNat := Nat.mul_le_mul_right _ hn

theorem ltPow_of {n d A B : Nat} {a : Int} (hn : n < 2 ^ A) (hd : 2 ^ B ≤ d)
    (ha : (A : Int) - B ≤ a) : LtPow n d a := by
  unfold LtPow expPos expNeg
  have h1 : A + (-a).toNat ≤ B + a.toNat := by omega
  have hp : 0 < 2 ^ (-a).toNat := Nat.two_pow_pos _
  calc n * 2 ^ (-a).toNat < 2 ^ A * 2 ^ (-a).toNat := Nat.mul_lt_mul_of_pos_right hn hp
    _ = 2 ^ (A + (-a).toNat) := (Nat.pow_add 2 A _).symm
    _ ≤ 2 ^ (B + a.toNat) := Nat.pow_le_pow_right (by decide) h1
    _ = 2 ^ B * 2 ^ a.toNat := Nat.pow_add 2 B _
    _ ≤ d * 2 ^ a.toNat := Nat.mul_le_mul_right _ hd

theorem ltPow_succ {n d : Nat} {a : Int} (h : LtPow n d a) : LtPow n d (a + 1) := by
  unfold LtPow expPos expNeg at *
  by_cases ha : 0 ≤ a
  · have h1 : (-a).toNat = 0 := by omega
    have h2 : (-(a + 1)).toNat = 0 := by omega
    have h3 : (a + 1).toNat = a.toNat + 1 := by omega
    rw [h1] at h
    rw [h2, h3, Nat.pow_succ]
    calc n * 2 ^ 0 < d * 2 ^ a.toNat := h
      _ ≤ d * (2 ^ a.toNat * 2) := Nat.mul_le_mul_left _ (by omega)
  · have h1 : a.toNat = 0 := by omega
    have h2 : (a + 1).toNat = 0 := by omega
    have h3 : (-a).toNat = (-(a + 1)).toNat + 1 := by omega
    rw [h1, h3, Nat.pow_succ] at h
    rw [h2]
    calc n * 2 ^ (-(a + 1)).toNat ≤ n * (2 ^ (-(a + 1)).toNat * 2) := Nat.mul_le_mul_left _ (by omega)
      _ < d * 2 ^ 0 := h

theorem ltPow_mono {n d : Nat} {a b : Int} (hab : a ≤ b) (h : LtPow n d a) : LtPow n d b := by
  obtain ⟨k, rfl⟩ : ∃ k : Nat, b = a + k := ⟨(b - a).toNat, by omega⟩
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have := ltPow_succ (ih (by omega))
    have e : a + ((k + 1 : Nat) : Int) = a + (k : Int) + 1 := by omega
    rw [e]
    exact this

theorem gePow_of_not_lt {n d : Nat} {a : Int} (h : ¬ LtPow n d a) : GePow n d a := by
  unfold LtPow at h
  unfold GePow
  omega

/-! ## binade -/

/-- `Nat.log2` から、n/d の floor(log₂) を求める。 -/
theorem floor_spec {n d : Nat} (hn : 0 < n) (hd : 0 < d) :
    let l : Int := (n.log2 : Int) - (d.log2 : Int)
    let f : Int := if JsNum.ltPow2 n d l then l - 1 else l
    GePow n d f ∧ LtPow n d (f + 1) := by
  intro l f
  have hn1 : 2 ^ n.log2 ≤ n := Nat.log2_self_le (by omega)
  have hn2 : n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
  have hd1 : 2 ^ d.log2 ≤ d := Nat.log2_self_le (by omega)
  have hd2 : d < 2 ^ (d.log2 + 1) := Nat.lt_log2_self
  show GePow n d (if JsNum.ltPow2 n d l then l - 1 else l) ∧
    LtPow n d ((if JsNum.ltPow2 n d l then l - 1 else l) + 1)
  split
  · rename_i hlt
    have hl := (ltPow2_iff n d l).mp hlt
    refine ⟨gePow_of hn1 (Nat.le_of_lt hd2) (by omega), ?_⟩
    have e : l - 1 + 1 = l := by omega
    rw [e]
    exact hl
  · rename_i hlt
    have hl : ¬ LtPow n d l := fun h => hlt ((ltPow2_iff n d l).mpr h)
    exact ⟨gePow_of_not_lt hl, ltPow_of hn2 hd1 (by omega)⟩

/-! ## 丸め -/

/-- **商と余りによる偶数への丸め。** -/
theorem round_spec (num den : Nat) (hden : 0 < den) :
    let q0 := num / den
    let r := num % den
    let q := if 2 * r > den || (2 * r == den && q0 % 2 == 1) then q0 + 1 else q0
    2 * (num : Int) ≤ (2 * q + 1) * den ∧ (2 * q - 1) * (den : Int) ≤ 2 * num ∧
      ((2 * (num : Int) = (2 * q + 1) * den ∨ 2 * (num : Int) = (2 * q - 1) * den) → q % 2 = 0) := by
  intro q0 r q
  have hdm : den * q0 + r = num := Nat.div_add_mod num den
  have hr : r < den := Nat.mod_lt _ hden
  have hnum : (num : Int) = (den : Int) * q0 + r := by rw [← hdm]; push_cast; rfl
  generalize hP : (den : Int) * q0 = P at hnum
  show 2 * (num : Int) ≤ (2 * (q : Int) + 1) * den ∧ (2 * (q : Int) - 1) * (den : Int) ≤ 2 * num ∧
      ((2 * (num : Int) = (2 * q + 1) * den ∨ 2 * (num : Int) = (2 * q - 1) * den) → q % 2 = 0)
  by_cases hup : (2 * r > den || (2 * r == den && q0 % 2 == 1)) = true
  · have hq : q = q0 + 1 := by simp only [q, hup]; rfl
    have e1 : (2 * ((q0 + 1 : Nat) : Int) + 1) * den = 2 * P + 3 * den := by
      rw [← hP]; push_cast; grind
    have e2 : (2 * ((q0 + 1 : Nat) : Int) - 1) * den = 2 * P + den := by
      rw [← hP]; push_cast; grind
    rw [hq, e1, e2]
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at hup
    refine ⟨by omega, by omega, ?_⟩
    rintro (h | h)
    · omega
    · omega
  · have hq : q = q0 := by simp only [q, hup]; rfl
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq, not_or,
      not_and] at hup
    have e1 : (2 * (q0 : Int) + 1) * den = 2 * P + den := by rw [← hP]; grind
    have e2 : (2 * (q0 : Int) - 1) * den = 2 * P - den := by rw [← hP]; grind
    rw [hq, e1, e2]
    refine ⟨by omega, by omega, ?_⟩
    rintro (h | h)
    · have : 2 * r = den := by omega
      have := hup.2 this
      omega
    · omega

/-! ## 実装の分子と分母 -/

theorem num_eq (n : Nat) (e : Int) :
    (if e ≥ 0 then n else n * JsNum.pow2 (-e)) = n * 2 ^ expNeg e := by
  unfold JsNum.pow2 expNeg
  split
  · have : (-e).toNat = 0 := by omega
    simp [this]
  · rfl

theorem den_eq (d : Nat) (e : Int) :
    (if e ≥ 0 then d * JsNum.pow2 e else d) = d * 2 ^ expPos e := by
  unfold JsNum.pow2 expPos
  split
  · rfl
  · have : e.toNat = 0 := by omega
    simp [this]

/-- binade の上の端は、分子と分母で 2^53 倍の不等式になる。 -/
theorem lt_of_ltPow {n d : Nat} {e : Int} (h : LtPow n d (e + 53)) :
    n * 2 ^ expNeg e < 2 ^ 53 * (d * 2 ^ expPos e) := by
  unfold LtPow expNeg expPos at *
  by_cases he : 0 ≤ e
  · have h1 : (-(e + 53)).toNat = 0 := by omega
    have h2 : (e + 53).toNat = e.toNat + 53 := by omega
    have h3 : (-e).toNat = 0 := by omega
    rw [h1, h2, Nat.pow_add] at h
    rw [h3]
    calc n * 2 ^ 0 < d * (2 ^ e.toNat * 2 ^ 53) := h
      _ = 2 ^ 53 * (d * 2 ^ e.toNat) := by
        rw [Nat.mul_comm (2 ^ e.toNat), ← Nat.mul_assoc, Nat.mul_comm d, Nat.mul_assoc]
  · have h3 : e.toNat = 0 := by omega
    rw [h3]
    by_cases he2 : 0 ≤ e + 53
    · have h1 : (-(e + 53)).toNat = 0 := by omega
      have h4 : (-e).toNat + (e + 53).toNat = 53 := by omega
      rw [h1] at h
      calc n * 2 ^ (-e).toNat < d * 2 ^ (e + 53).toNat * 2 ^ (-e).toNat :=
            Nat.mul_lt_mul_of_pos_right (by simpa using h) (Nat.two_pow_pos _)
        _ = d * 2 ^ ((e + 53).toNat + (-e).toNat) := by rw [Nat.mul_assoc, ← Nat.pow_add]
        _ = 2 ^ 53 * (d * 2 ^ 0) := by rw [Nat.add_comm, h4]; simp [Nat.mul_comm]
    · have h1 : (e + 53).toNat = 0 := by omega
      have h4 : (-e).toNat = (-(e + 53)).toNat + 53 := by omega
      rw [h1] at h
      rw [h4, Nat.pow_add, ← Nat.mul_assoc]
      calc n * 2 ^ (-(e + 53)).toNat * 2 ^ 53 < d * 2 ^ 0 * 2 ^ 53 :=
            Nat.mul_lt_mul_of_pos_right h (Nat.two_pow_pos _)
        _ = 2 ^ 53 * (d * 2 ^ 0) := Nat.mul_comm _ _

/-! ## 主定理 -/

/-- **`JsNum.roundPos` は、正の有理数 n/d に最も近い倍精度の値を返す。** -/
theorem roundPos_spec {n d : Nat} (hn : 0 < n) (hd : 0 < d) :
    NearestDouble n d (JsNum.roundPos n d) := by
  obtain ⟨hge, hlt⟩ := floor_spec hn hd
  unfold JsNum.roundPos
  dsimp only
  generalize hf : (if JsNum.ltPow2 n d ((n.log2 : Int) - (d.log2 : Int))
    then (n.log2 : Int) - (d.log2 : Int) - 1 else (n.log2 : Int) - (d.log2 : Int)) = f at hge hlt ⊢
  generalize he : max (f - 52) (-1074) = e
  -- binade
  have hbin : Binade n d e := by
    refine ⟨by omega, ltPow_mono (by omega) hlt, ?_⟩
    by_cases h : f - 52 ≥ -1074
    · right
      have : e + 52 = f := by omega
      rw [this]; exact hge
    · left; omega
  -- 分子と分母
  rw [num_eq, den_eq]
  have hden : 0 < d * 2 ^ expPos e := Nat.mul_pos hd (Nat.two_pow_pos _)
  obtain ⟨hu, hl, ht⟩ := round_spec (n * 2 ^ expNeg e) (d * 2 ^ expPos e) hden
  generalize hq : (if 2 * (n * 2 ^ expNeg e % (d * 2 ^ expPos e)) > d * 2 ^ expPos e ||
      (2 * (n * 2 ^ expNeg e % (d * 2 ^ expPos e)) == d * 2 ^ expPos e &&
        n * 2 ^ expNeg e / (d * 2 ^ expPos e) % 2 == 1)
    then n * 2 ^ expNeg e / (d * 2 ^ expPos e) + 1 else n * 2 ^ expNeg e / (d * 2 ^ expPos e)) = q
    at hu hl ht ⊢
  have hround : RoundsAt n d q e := ⟨hu, hl, ht⟩
  -- q ≤ 2^53
  have hq53 : q ≤ 2 ^ 53 := by
    have hlt53 := lt_of_ltPow hbin.lt
    have hdiv : n * 2 ^ expNeg e / (d * 2 ^ expPos e) < 2 ^ 53 :=
      (Nat.div_lt_iff_lt_mul hden).mpr hlt53
    rw [← hq]
    split <;> omega
  refine ⟨e, q, hbin, hround, hq53, ?_⟩
  by_cases h53 : q = 2 ^ 53
  · have hb : (q == 2 ^ 53) = true := by simp [h53]
    rw [if_pos hb]
    dsimp only
    by_cases ho : e + 1 > 971
    · rw [if_pos ho]
      exact Or.inr (Or.inr ⟨Or.inr ⟨h53, ho⟩, rfl⟩)
    · rw [if_neg ho]
      exact Or.inr (Or.inl ⟨h53, by omega, rfl⟩)
  · have hb : ¬ (q == 2 ^ 53) = true := by simp [h53]
    rw [if_neg hb]
    dsimp only
    by_cases ho : e > 971
    · rw [if_pos ho]
      exact Or.inr (Or.inr ⟨Or.inl ⟨by omega, ho⟩, rfl⟩)
    · rw [if_neg ho]
      exact Or.inl ⟨by omega, by omega, rfl⟩

end Dom.Spec
