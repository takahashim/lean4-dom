import Dom.Spec.DoubleSound

/-!
# binary64 全体の中で最も近い値への丸め

距離は、どの値にも 2^1074 と入力の正の分母を掛けてから比べる。これは共通の整数の尺度で正確に比べるためで、
浮動小数点の計算ではない。有限の候補は、丸めの algorithm とその binade の選び方から独立に定義する。
-/

set_option maxRecDepth 10000
set_option exponentiation.threshold 2048

namespace Dom.Spec

/-- 負でない有限の binary64 の表現（0 を含む）。 -/
def FiniteDouble (k : Nat) (e : Int) : Prop :=
  k < 2 ^ 53 ∧ -1074 ≤ e ∧ e ≤ 971 ∧ (e = -1074 ∨ 2 ^ 52 ≤ k)

/-- 正の最小の非正規化数 2^-1074 を単位とした値。 -/
def doubleUnits (k : Nat) (e : Int) : Nat := k * 2 ^ (e + 1074).toNat

/-- 共通の整数の尺度での正確な距離。 -/
def scaledDistance (a b : Int) : Int := if a ≤ b then b - a else a - b

/-- 符号付きの有限の binary64 の値。最小の非正規化数を単位とする正確な尺度で表す。 -/
def FiniteBinary64 (value : Int) : Prop :=
  ∃ k e, FiniteDouble k e ∧
    (value = (doubleUnits k e : Int) ∨ value = -(doubleUnits k e : Int))

/-- 有限の binary64 の値すべての中で最も近い、という条件。 -/
def GloballyNearestFinite (n d k : Nat) (e : Int) : Prop :=
  FiniteDouble k e ∧ ∀ k' e', FiniteDouble k' e' →
    scaledDistance (n * 2 ^ 1074) (d * doubleUnits k e) ≤
      scaledDistance (n * 2 ^ 1074) (d * doubleUnits k' e')

private theorem nearest_grid {X V q : Int} (hV : 0 < V)
    (hl : (2 * q - 1) * V ≤ 2 * X) (hu : 2 * X ≤ (2 * q + 1) * V) (k : Int) :
    scaledDistance X (q * V) ≤ scaledDistance X (k * V) := by
  have hl' : 2 * (q * V) - V ≤ 2 * X := by grind
  have hu' : 2 * X ≤ 2 * (q * V) + V := by grind
  by_cases hk : k = q
  · subst hk; exact Int.le_refl _
  · rcases Int.lt_or_gt_of_ne hk with hk | hk
    · have hm := Int.mul_le_mul_of_nonneg_right (show k ≤ q - 1 by omega) (Int.le_of_lt hV)
      have hm' : k * V ≤ q * V - V := by grind
      unfold scaledDistance
      split <;> split <;> omega
    · have hm := Int.mul_le_mul_of_nonneg_right (show q + 1 ≤ k by omega) (Int.le_of_lt hV)
      have hm' : q * V + V ≤ k * V := by grind
      unfold scaledDistance
      split <;> split <;> omega

private theorem grid_tie {X V q k : Int} (hV : 0 < V)
    (hl : (2 * q - 1) * V ≤ 2 * X) (hu : 2 * X ≤ (2 * q + 1) * V)
    (hne : k ≠ q) (ht : scaledDistance X (q * V) = scaledDistance X (k * V)) :
    2 * X = (2 * q + 1) * V ∨ 2 * X = (2 * q - 1) * V := by
  have hl' : 2 * (q * V) - V ≤ 2 * X := by grind
  have hu' : 2 * X ≤ 2 * (q * V) + V := by grind
  rcases Int.lt_or_gt_of_ne hne with hk | hk
  · have hm := Int.mul_le_mul_of_nonneg_right (show k ≤ q - 1 by omega) (Int.le_of_lt hV)
    have hm' : k * V ≤ q * V - V := by grind
    right
    have he : 2 * X = 2 * (q * V) - V := by
      unfold scaledDistance at ht
      split at ht <;> split at ht <;> omega
    grind
  · have hm := Int.mul_le_mul_of_nonneg_right (show q + 1 ≤ k by omega) (Int.le_of_lt hV)
    have hm' : q * V + V ≤ k * V := by grind
    left
    have he : 2 * X = 2 * (q * V) + V := by
      unfold scaledDistance at ht
      split at ht <;> split at ht <;> omega
    grind

private theorem distance_below {X L Y : Int} (hy : Y ≤ L) (hx : L ≤ X) :
    scaledDistance X L ≤ scaledDistance X Y := by
  unfold scaledDistance
  split <;> split <;> omega

private theorem distance_strict_below {X L Y : Int} (hy : Y < L) (hx : L ≤ X) :
    scaledDistance X L < scaledDistance X Y := by
  unfold scaledDistance
  split <;> split <;> omega

private theorem scale_pow {e : Int} (he : -1074 ≤ e) :
    2 ^ expNeg e * 2 ^ (1074 - expNeg e) = (2 ^ 1074 : Nat) ∧
    2 ^ expPos e * 2 ^ (1074 - expNeg e) = (2 ^ (e + 1074).toNat : Nat) := by
  have hn : expNeg e ≤ 1074 := by unfold expNeg; omega
  have hp : expPos e + (1074 - expNeg e) = (e + 1074).toNat := by
    unfold expPos expNeg at *; omega
  rw [← Nat.pow_add, Nat.add_sub_of_le hn, ← Nat.pow_add, hp]
  exact ⟨rfl, rfl⟩

/-- 独立に尺度を合わせた格子でちょうど中間なら、仮数が偶数のほうを選ぶ。 -/
theorem roundsAt_scaled_tie {n d q : Nat} {e : Int} (he : -1074 ≤ e)
    (h : RoundsAt n d q e)
    (ht : 2 * (n * 2 ^ 1074 : Nat) =
      (2 * (q : Int) + 1) * (d * 2 ^ (e + 1074).toNat : Nat) ∨
      2 * (n * 2 ^ 1074 : Nat) =
      (2 * (q : Int) - 1) * (d * 2 ^ (e + 1074).toNat : Nat)) : q % 2 = 0 := by
  obtain ⟨hn, hd⟩ := scale_pow he
  have hc : (2 ^ (1074 - expNeg e) : Nat) ≠ (0 : Int) := by
    exact_mod_cast Nat.ne_of_gt (Nat.two_pow_pos _)
  apply h.tie
  rcases ht with ht | ht
  · left
    apply Int.eq_of_mul_eq_mul_right hc
    simpa only [Int.mul_assoc, ← Int.natCast_mul, Nat.mul_assoc, hn, hd] using ht
  · right
    apply Int.eq_of_mul_eq_mul_right hc
    simpa only [Int.mul_assoc, ← Int.natCast_mul, Nat.mul_assoc, hn, hd] using ht

/-- binade の中での丸めの不等式を、共通の正確な尺度へ移す。 -/
theorem roundsAt_scaled {n d q : Nat} {e : Int} (he : -1074 ≤ e)
    (h : RoundsAt n d q e) :
    (2 * (q : Int) - 1) * (d * 2 ^ (e + 1074).toNat : Nat) ≤
      2 * (n * 2 ^ 1074 : Nat) ∧
    2 * (n * 2 ^ 1074 : Nat) ≤
      (2 * (q : Int) + 1) * (d * 2 ^ (e + 1074).toNat : Nat) := by
  obtain ⟨hneg, hpos⟩ := scale_pow he
  have hc : (0 : Int) ≤ (2 ^ (1074 - expNeg e) : Nat) := Int.natCast_nonneg _
  have hl := Int.mul_le_mul_of_nonneg_right h.lower hc
  have hu := Int.mul_le_mul_of_nonneg_right h.upper hc
  have hn : (n * 2 ^ expNeg e : Nat) * 2 ^ (1074 - expNeg e) = n * 2 ^ 1074 := by
    rw [Nat.mul_assoc, hneg]
  have hd : (d * 2 ^ expPos e : Nat) * 2 ^ (1074 - expNeg e) = d * 2 ^ (e + 1074).toNat := by
    rw [Nat.mul_assoc, hpos]
  simp only [Int.mul_assoc, ← Int.natCast_mul, hn, hd] at hl hu
  exact ⟨hl, hu⟩

/-- binade の境界を、共通の正確な尺度へ移す。 -/
theorem gePow_scaled {n d : Nat} {e : Int} (he : -1074 ≤ e) (h : GePow n d e) :
    d * 2 ^ (e + 1074).toNat ≤ n * 2 ^ 1074 := by
  obtain ⟨hneg, hpos⟩ := scale_pow he
  have hm := Nat.mul_le_mul_right (2 ^ (1074 - expNeg e)) h
  simpa only [Nat.mul_assoc, hneg, hpos] using hm

private theorem units_on_grid {k : Nat} {j e : Int} (he : -1074 ≤ e) (hj : e ≤ j) :
    doubleUnits k j = (k * 2 ^ (j - e).toNat) * 2 ^ (e + 1074).toNat := by
  have hsum : (j + 1074).toNat = (j - e).toNat + (e + 1074).toNat := by omega
  simp only [doubleUnits, hsum, Nat.pow_add, Nat.mul_assoc]

private theorem units_below_binade {k : Nat} {j e : Int}
    (hj : -1074 ≤ j) (hje : j < e) (hk : k < 2 ^ 53) :
    doubleUnits k j < 2 ^ 52 * 2 ^ (e + 1074).toNat := by
  have hs : (j + 1074).toNat + 53 ≤ 52 + (e + 1074).toNat := by omega
  calc doubleUnits k j < 2 ^ 53 * 2 ^ (j + 1074).toNat :=
        Nat.mul_lt_mul_of_pos_right hk (Nat.two_pow_pos _)
    _ = 2 ^ ((j + 1074).toNat + 53) := by rw [Nat.mul_comm, ← Nat.pow_add]
    _ ≤ 2 ^ (52 + (e + 1074).toNat) := Nat.pow_le_pow_right (by decide) hs
    _ = 2 ^ 52 * 2 ^ (e + 1074).toNat := Nat.pow_add _ _ _

/-- binade の中での丸めは、有限の binary64 の値 *すべて* に対して距離を最小にする。 -/
theorem binade_rounding_globally_nearest {n d q : Nat} {e : Int}
    (hd : 0 < d) (hb : Binade n d e) (hr : RoundsAt n d q e)
    (k : Nat) (j : Int) (hf : FiniteDouble k j) :
    scaledDistance (n * 2 ^ 1074) (d * doubleUnits q e) ≤
      scaledDistance (n * 2 ^ 1074) (d * doubleUnits k j) := by
  obtain ⟨hl, hu⟩ := roundsAt_scaled hb.ge hr
  have hV : (0 : Int) < (d * 2 ^ (e + 1074).toNat : Nat) := by
    exact_mod_cast Nat.mul_pos hd (Nat.two_pow_pos _)
  by_cases hje : e ≤ j
  · rw [units_on_grid hb.ge hje]
    have hg := nearest_grid hV hl hu ((k * 2 ^ (j - e).toNat : Nat) : Int)
    simpa only [doubleUnits, Int.natCast_mul, Int.natCast_pow, show ((2 : Nat) : Int) = 2 from rfl, Int.mul_assoc, Int.mul_left_comm] using hg
  · have hlt : j < e := by omega
    have he : e ≠ -1074 := by have := hf.2.1; omega
    have hlo := gePow_scaled (e := e + 52) (by have := hb.ge; omega) (hb.low.resolve_left he)
    have hexp : (e + 52 + 1074).toNat = 52 + (e + 1074).toNat := by have := hb.ge; omega
    rw [hexp, Nat.pow_add] at hlo
    have hX : (d * (2 ^ 52 * 2 ^ (e + 1074).toNat) : Nat) ≤ (n * 2 ^ 1074 : Nat) := by
      simpa only [Nat.mul_assoc] using hlo
    have hy := Nat.mul_le_mul_left d (Nat.le_of_lt (units_below_binade hf.2.1 hlt hf.1))
    have hg := nearest_grid hV hl hu (2 ^ 52)
    have hb' := distance_below (X := (n * 2 ^ 1074 : Nat))
      (Y := (d * doubleUnits k j : Nat))
      (L := (d * (2 ^ 52 * 2 ^ (e + 1074).toNat) : Nat))
      (by exact_mod_cast hy) (by exact_mod_cast hX)
    have hg' : scaledDistance (n * 2 ^ 1074) (d * doubleUnits q e) ≤
        scaledDistance (n * 2 ^ 1074) (d * (2 ^ 52 * 2 ^ (e + 1074).toNat) : Nat) := by
      simpa only [doubleUnits, Int.natCast_mul, Int.natCast_pow, show ((2 : Nat) : Int) = 2 from rfl,
        Int.mul_assoc, Int.mul_left_comm] using hg
    exact Int.le_trans hg' hb'

/-- 同じ最小の距離にある別の有限の値があれば、偶数への丸め（ties-to-even）になる。 -/
theorem binade_rounding_global_tie {n d q : Nat} {e : Int}
    (hd : 0 < d) (hb : Binade n d e) (hr : RoundsAt n d q e)
    (k : Nat) (j : Int) (hf : FiniteDouble k j)
    (hne : doubleUnits k j ≠ doubleUnits q e)
    (ht : scaledDistance (n * 2 ^ 1074) (d * doubleUnits q e) =
      scaledDistance (n * 2 ^ 1074) (d * doubleUnits k j)) : q % 2 = 0 := by
  obtain ⟨hl, hu⟩ := roundsAt_scaled hb.ge hr
  have hV : (0 : Int) < (d * 2 ^ (e + 1074).toNat : Nat) := by
    exact_mod_cast Nat.mul_pos hd (Nat.two_pow_pos _)
  by_cases hje : e ≤ j
  · have hneq : ((k * 2 ^ (j - e).toNat : Nat) : Int) ≠ q := by
      intro heq
      have heq' : k * 2 ^ (j - e).toNat = q := by exact_mod_cast heq
      apply hne
      rw [units_on_grid hb.ge hje, heq']
      rfl
    have ht' : scaledDistance (n * 2 ^ 1074) ((q : Int) * (d * 2 ^ (e + 1074).toNat : Nat)) =
        scaledDistance (n * 2 ^ 1074)
          ((k * 2 ^ (j - e).toNat : Nat) * (d * 2 ^ (e + 1074).toNat : Nat)) := by
      rw [units_on_grid hb.ge hje] at ht
      simpa only [doubleUnits, Int.natCast_mul, Int.mul_assoc, Int.mul_left_comm] using ht
    exact roundsAt_scaled_tie hb.ge hr (grid_tie hV hl hu hneq ht')
  · have hlt : j < e := by omega
    have he : e ≠ -1074 := by have := hf.2.1; omega
    have hlo := gePow_scaled (e := e + 52) (by have := hb.ge; omega) (hb.low.resolve_left he)
    have hexp : (e + 52 + 1074).toNat = 52 + (e + 1074).toNat := by have := hb.ge; omega
    rw [hexp, Nat.pow_add] at hlo
    have hX : (d * (2 ^ 52 * 2 ^ (e + 1074).toNat) : Nat) ≤ (n * 2 ^ 1074 : Nat) := by
      simpa only [Nat.mul_assoc] using hlo
    have hy := Nat.mul_lt_mul_of_pos_left (units_below_binade hf.2.1 hlt hf.1) hd
    have hg := nearest_grid hV hl hu (2 ^ 52)
    have hg' : scaledDistance (n * 2 ^ 1074) (d * doubleUnits q e) ≤
        scaledDistance (n * 2 ^ 1074) (d * (2 ^ 52 * 2 ^ (e + 1074).toNat) : Nat) := by
      simpa only [doubleUnits, Int.natCast_mul, Int.natCast_pow, show ((2 : Nat) : Int) = 2 from rfl,
        Int.mul_assoc, Int.mul_left_comm] using hg
    have hy' : (d * doubleUnits k j : Nat) < (d * (2 ^ 52 * 2 ^ (e + 1074).toNat) : Nat) := hy
    have hstrict : scaledDistance (n * 2 ^ 1074) (d * (2 ^ 52 * 2 ^ (e + 1074).toNat) : Nat) <
        scaledDistance (n * 2 ^ 1074) (d * doubleUnits k j) := by
      have hXi : ((d * (2 ^ 52 * 2 ^ (e + 1074).toNat) : Nat) : Int) ≤ (n * 2 ^ 1074 : Nat) := by exact_mod_cast hX
      have hYi : ((d * doubleUnits k j : Nat) : Int) < (d * (2 ^ 52 * 2 ^ (e + 1074).toNat) : Nat) := by exact_mod_cast hy'
      exact distance_strict_below hYi hXi
    exact False.elim ((Int.ne_of_lt (Int.lt_of_le_of_lt hg' hstrict)) ht)

private theorem rounded_significand_lower {n d q : Nat} {e : Int}
    (hd : 0 < d) (hb : Binade n d e) (hr : RoundsAt n d q e) :
    e = -1074 ∨ 2 ^ 52 ≤ q := by
  by_cases he : e = -1074
  · exact Or.inl he
  · right
    have hl := gePow_scaled (e := e + 52) (by have := hb.ge; omega) (hb.low.resolve_left he)
    have hexp : (e + 52 + 1074).toNat = 52 + (e + 1074).toNat := by have := hb.ge; omega
    rw [hexp, Nat.pow_add] at hl
    obtain ⟨_, hu⟩ := roundsAt_scaled hb.ge hr
    have hV : (0 : Int) < (d * 2 ^ (e + 1074).toNat : Nat) := by
      exact_mod_cast Nat.mul_pos hd (Nat.two_pow_pos _)
    have hlo : (2 ^ 52 : Int) * (d * 2 ^ (e + 1074).toNat : Nat) ≤
        (n * 2 ^ 1074 : Nat) := by
      have hx : (2 ^ 52 * (d * 2 ^ (e + 1074).toNat) : Nat) ≤ n * 2 ^ 1074 := by
        simpa only [Nat.mul_assoc, Nat.mul_left_comm] using hl
      exact_mod_cast hx
    have hm : (2 * (2 ^ 52 : Int)) * (d * 2 ^ (e + 1074).toNat : Nat) ≤
        (2 * (q : Int) + 1) * (d * 2 ^ (e + 1074).toNat : Nat) := by
      calc _ = 2 * ((2 ^ 52 : Int) * (d * 2 ^ (e + 1074).toNat : Nat)) := by grind
        _ ≤ 2 * (n * 2 ^ 1074 : Nat) := Int.mul_le_mul_of_nonneg_left hlo (by decide)
        _ ≤ _ := hu
    have hc := Int.le_of_mul_le_mul_right hm hV
    have hK : ((2 ^ 52 : Nat) : Int) = (2 ^ 52 : Int) := by rw [Int.natCast_pow]; rfl
    rw [← hK] at hc
    omega

private theorem units_carry {e : Int} (he : -1074 ≤ e) :
    doubleUnits (2 ^ 53) e = doubleUnits (2 ^ 52) (e + 1) := by
  have hs : (e + 1 + 1074).toNat = (e + 1074).toNat + 1 := by omega
  unfold doubleUnits
  rw [hs]
  have h53 : (2 ^ 53 : Nat) = 2 ^ 52 * 2 := by rw [show 53 = 52 + 1 from rfl, Nat.pow_succ]
  simp only [h53, Nat.pow_succ]
  grind

/-- 丸めの関係仕様が与える有限の結果は、どれも全体の中で最も近い。 -/
theorem nearestDouble_globally_nearest {n d k : Nat} {j : Int}
    (hd : 0 < d) (h : NearestDouble n d (some (k, j))) : GloballyNearestFinite n d k j := by
  obtain ⟨e, q, hb, hr, hq, hcases⟩ := h
  rcases hcases with ⟨hlt, he, hres⟩ | ⟨heq, he, hres⟩ | ⟨_, hres⟩
  · cases hres
    refine ⟨⟨hlt, hb.ge, he, rounded_significand_lower hd hb hr⟩, ?_⟩
    exact fun k' j' hf => binade_rounding_globally_nearest hd hb hr k' j' hf
  · cases hres
    refine ⟨⟨by decide, by have := hb.ge; omega, he, Or.inr (Nat.le_refl _)⟩, ?_⟩
    intro k' j' hf
    have hg := binade_rounding_globally_nearest hd hb hr k' j' hf
    rw [heq, units_carry hb.ge] at hg
    exact hg
  · cases hres

/-- 異なる有限の値が全体の中で同じ距離に並ぶとき、表現の仮数が偶数のほうを選ぶ。 -/
theorem nearestDouble_global_tie {n d k : Nat} {j : Int}
    (hd : 0 < d) (h : NearestDouble n d (some (k, j)))
    (k' : Nat) (j' : Int) (hf : FiniteDouble k' j')
    (hne : doubleUnits k' j' ≠ doubleUnits k j)
    (ht : scaledDistance (n * 2 ^ 1074) (d * doubleUnits k j) =
      scaledDistance (n * 2 ^ 1074) (d * doubleUnits k' j')) : k % 2 = 0 := by
  obtain ⟨e, q, hb, hr, _, hcases⟩ := h
  rcases hcases with ⟨_, _, hres⟩ | ⟨_, _, hres⟩ | ⟨_, hres⟩
  · cases hres
    exact binade_rounding_global_tie hd hb hr k' j' hf hne ht
  · cases hres
    simp [show 52 = 51 + 1 from rfl, Nat.pow_succ]
  · cases hres

/-- 実行関数も、独立に書いた全体での ties-to-even の条件を満たす。 -/
theorem roundPos_global_tie {n d k : Nat} {e : Int}
    (hn : 0 < n) (hd : 0 < d) (h : Dom.Idl.JsNum.roundPos n d = some (k, e))
    (k' : Nat) (e' : Int) (hf : FiniteDouble k' e')
    (hne : doubleUnits k' e' ≠ doubleUnits k e)
    (ht : scaledDistance (n * 2 ^ 1074) (d * doubleUnits k e) =
      scaledDistance (n * 2 ^ 1074) (d * doubleUnits k' e')) : k % 2 = 0 := by
  exact nearestDouble_global_tie hd (h ▸ roundPos_spec hn hd) k' e' hf hne ht

/-- 実行関数についての、独立に書いた「全体の中で最も近い」の定理。 -/
theorem roundPos_globally_nearest {n d k : Nat} {e : Int}
    (hn : 0 < n) (hd : 0 < d) (h : Dom.Idl.JsNum.roundPos n d = some (k, e)) :
    GloballyNearestFinite n d k e := by
  exact nearestDouble_globally_nearest hd (h ▸ roundPos_spec hn hd)

private theorem distance_nonpositive {X Y : Int} (hx : 0 ≤ X) (hy : Y ≤ 0) :
    scaledDistance X 0 ≤ scaledDistance X Y := by
  unfold scaledDistance
  split <;> split <;> omega

/-- 全体での比較には、負の binary64 の候補も含める。 -/
theorem globallyNearestFinite_signed {n d k : Nat} {e : Int}
    (h : GloballyNearestFinite n d k e) {value : Int} (hv : FiniteBinary64 value) :
    scaledDistance (n * 2 ^ 1074) (d * doubleUnits k e) ≤
      scaledDistance (n * 2 ^ 1074) ((d : Int) * value) := by
  obtain ⟨k', e', hf, hp | hn⟩ := hv
  · rw [hp, ← Int.natCast_mul]
    exact h.2 k' e' hf
  · rw [hn]
    have hz := h.2 0 (-1074) ⟨by decide, by decide, by decide, Or.inl rfl⟩
    simp only [doubleUnits, Nat.zero_mul, Int.natCast_zero] at hz
    have hnegative : (d : Int) * -(doubleUnits k' e' : Int) ≤ 0 := by
      rw [Int.mul_neg, ← Int.natCast_mul]
      exact Int.neg_nonpos_of_nonneg (Int.natCast_nonneg _)
    exact Int.le_trans hz (distance_nonpositive (Int.natCast_nonneg _) hnegative)

/-- 符号付きの有限の binary64 の値全体についての、独立に書いた「最も近い値」の定理。 -/
theorem roundPos_binary64_nearest {n d k : Nat} {e : Int}
    (hn : 0 < n) (hd : 0 < d) (h : Dom.Idl.JsNum.roundPos n d = some (k, e))
    {value : Int} (hv : FiniteBinary64 value) :
    scaledDistance (n * 2 ^ 1074) (d * doubleUnits k e) ≤
      scaledDistance (n * 2 ^ 1074) ((d : Int) * value) := by
  exact globallyNearestFinite_signed (roundPos_globally_nearest hn hd h) hv

end Dom.Spec
