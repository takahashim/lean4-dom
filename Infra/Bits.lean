/-!
# Nat のビット演算の補題

`|||` と `&&&` を算術（足し算・剰余）に直すための汎用補題。
UTF-8 の符号化・復号の証明（`Infra/Utf8Roundtrip.lean`）が使う。
-/

namespace Infra

/-- 上位を空けた値と、その桁未満の値の `|||` は足し算である。 -/
theorem lor_add {k a b : Nat} (hb : b < 2 ^ k) : (a * 2 ^ k) ||| b = a * 2 ^ k + b := by
  have hpos : 0 < 2 ^ k := Nat.pow_pos (by omega)
  have hdiv : ((a * 2 ^ k) ||| b) / 2 ^ k = a := by
    rw [Nat.or_div_two_pow, Nat.mul_div_cancel _ hpos, Nat.div_eq_of_lt hb]
    simp
  have hmod : ((a * 2 ^ k) ||| b) % 2 ^ k = b := by
    rw [Nat.or_mod_two_pow, Nat.mul_mod_left, Nat.mod_eq_of_lt hb]
    simp
  have h2 := Nat.div_add_mod ((a * 2 ^ k) ||| b) (2 ^ k)
  rw [hdiv, hmod, Nat.mul_comm] at h2
  omega

/-- 6 bit の取り出し。 -/
theorem and_3F (x : Nat) : x &&& 0x3F = x % 64 := Nat.and_two_pow_sub_one_eq_mod x 6

theorem and_1F (x : Nat) : x &&& 0x1F = x % 32 := Nat.and_two_pow_sub_one_eq_mod x 5

theorem and_0F (x : Nat) : x &&& 0x0F = x % 16 := Nat.and_two_pow_sub_one_eq_mod x 4

theorem and_07 (x : Nat) : x &&& 0x07 = x % 8 := Nat.and_two_pow_sub_one_eq_mod x 3

/-- continuation byte の判定に使う上位 2 bit。 -/
theorem and_C0 (x : Nat) : x &&& 0xC0 = 64 * ((x / 64) &&& 3) := by
  have hmod : (x &&& 0xC0) % 2 ^ 6 = 0 := by
    rw [Nat.and_mod_two_pow]
    show (x % 64) &&& 0 = 0
    simp
  have hdiv : (x &&& 0xC0) / 2 ^ 6 = (x / 64) &&& 3 := by
    rw [Nat.and_div_two_pow]
  have h2 := Nat.div_add_mod (x &&& 0xC0) (2 ^ 6)
  rw [hdiv, hmod] at h2
  omega

/-- 下位 `k` bit が空いている値には、その桁未満の値を足し込める。 -/
theorem lor_low {k A d : Nat} (hA : A % 2 ^ k = 0) (hd : d < 2 ^ k) : A ||| d = A + d := by
  have h := Nat.div_add_mod A (2 ^ k)
  rw [hA, Nat.add_zero, Nat.mul_comm] at h
  calc A ||| d = ((A / 2 ^ k) * 2 ^ k) ||| d := by rw [h]
    _ = (A / 2 ^ k) * 2 ^ k + d := lor_add hd
    _ = A + d := by rw [h]

/-- 3 byte ぶんの組み立て。 -/
theorem lor3 {a b c : Nat} (hb : b < 64) (hc : c < 64) :
    (a * 2 ^ 12 ||| b * 2 ^ 6) ||| c = a * 4096 + b * 64 + c := by
  have h1 : a * 2 ^ 12 ||| b * 2 ^ 6 = a * 2 ^ 12 + b * 2 ^ 6 :=
    lor_low (k := 12) (by omega) (by omega)
  rw [h1, lor_low (k := 6) (by omega) (by omega)]

/-- 4 byte ぶんの組み立て。 -/
theorem lor4 {a b c d : Nat} (hb : b < 64) (hc : c < 64) (hd : d < 64) :
    ((a * 2 ^ 18 ||| b * 2 ^ 12) ||| c * 2 ^ 6) ||| d
      = a * 262144 + b * 4096 + c * 64 + d := by
  have h1 : a * 2 ^ 18 ||| b * 2 ^ 12 = a * 2 ^ 18 + b * 2 ^ 12 :=
    lor_low (k := 18) (by omega) (by omega)
  have h2 : (a * 2 ^ 18 + b * 2 ^ 12) ||| c * 2 ^ 6
      = (a * 2 ^ 18 + b * 2 ^ 12) + c * 2 ^ 6 := lor_low (k := 12) (by omega) (by omega)
  rw [h1, h2, lor_low (k := 6) (by omega) (by omega)]

end Infra
