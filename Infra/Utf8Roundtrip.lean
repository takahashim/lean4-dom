import Infra.Bytes

/-!
# UTF-8 の往復

`utf8Decode (utf8Encode s) = s.toList`。

符号化はビット演算で書いてあるので、まずそれを算術に直す足場を作る。
`|||` が足し算になるのは「上位を空けた値」と「その桁未満の値」を合わせるときで、
UTF-8 の byte はすべてその形をしている。
-/

namespace Infra

/-! ## ビットの足場 -/

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

/-- 先頭 byte の印と、それに続く桁。 -/
theorem lead_add {k m v : Nat} (hv : v < 2 ^ k) : (m * 2 ^ k) ||| v = m * 2 ^ k + v :=
  lor_add hv

/-- continuation byte。 -/
theorem cont_add {v : Nat} (hv : v < 64) : (0x80 ||| v) = 128 + v := by
  show (2 * 2 ^ 6 ||| v) = _
  rw [lor_add (k := 6) (by omega)]

theorem lead2_add {v : Nat} (hv : v < 32) : (0xC0 ||| v) = 192 + v := by
  show (6 * 2 ^ 5 ||| v) = _
  rw [lor_add (k := 5) (by omega)]

theorem lead3_add {v : Nat} (hv : v < 16) : (0xE0 ||| v) = 224 + v := by
  show (14 * 2 ^ 4 ||| v) = _
  rw [lor_add (k := 4) (by omega)]

theorem lead4_add {v : Nat} (hv : v < 8) : (0xF0 ||| v) = 240 + v := by
  show (30 * 2 ^ 3 ||| v) = _
  rw [lor_add (k := 3) (by omega)]

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

/-- `0x80 + v` は continuation byte として読める。 -/
theorem continuationBits_ofNat {v : Nat} (hv : v < 64) :
    continuationBits (UInt8.ofNat (128 + v)) = some v := by
  have hlt : 128 + v < 256 := by omega
  have hb : (UInt8.ofNat (128 + v)).toNat = 128 + v := by
    simp [Nat.mod_eq_of_lt hlt]
  unfold continuationBits
  rw [hb, and_C0, and_3F]
  have hq : (128 + v) / 64 = 2 := by omega
  rw [hq]
  norm_cast
  simp
  omega

/-! ## `Char` の往復 -/

/-- `Char` の値は必ず scalar value なので、番号から作り直すと元に戻る。 -/
theorem charOfScalar_toNat (c : Char) : charOfScalar c.toNat = c := by
  have hv : c.toNat < 0xD800 ∨ (0xDFFF < c.toNat ∧ c.toNat < 0x110000) := c.valid
  have hcond : (decide (c.toNat < 0xD800) ||
      (decide (0xDFFF < c.toNat) && decide (c.toNat < 0x110000))) = true := by
    rcases hv with h | h
    · simp [h]
    · simp [h.1, h.2]
  unfold charOfScalar
  rw [if_pos hcond]
  exact Char.ofNat_toNat c

/-- `Char` の番号は Unicode の上限未満である。4 byte の場合の先頭 byte の範囲に使う。 -/
theorem toNat_lt (c : Char) : c.toNat < 0x110000 := by
  have hv : c.toNat < 0xD800 ∨ (0xDFFF < c.toNat ∧ c.toNat < 0x110000) := c.valid
  rcases hv with h | h
  · omega
  · exact h.2

/-! ## 一文字ぶんの往復 -/

/--
**一文字を符号化して読み直すと元に戻る。**

先頭 byte の範囲で 4 つに分かれる。どの場合も、符号化した byte を算術の形に直し、
decoder の分岐がそこを通ることを示し、組み立て直すと元の番号になることを見る。
-/
theorem utf8Decode_encodeChar (c : Char) (rest : Bytes) :
    utf8Decode (utf8EncodeChar c ++ rest) = c :: utf8Decode rest := by
  by_cases h1 : c.toNat < 0x80
  · -- 1 byte
    have hb : (UInt8.ofNat c.toNat).toNat = c.toNat := by
      simp [Nat.mod_eq_of_lt (show c.toNat < 256 by omega)]
    simp only [utf8EncodeChar, h1, reduceIte, List.cons_append, List.nil_append]
    rw [utf8Decode.eq_def]
    simp +zetaDelta only [hb, h1, reduceIte]
    rw [charOfScalar_toNat]
  by_cases h2 : c.toNat < 0x800
  · -- 2 byte
    have hqlt : c.toNat / 64 < 32 := by omega
    have hrlt : c.toNat % 64 < 64 := by omega
    have henc : utf8EncodeChar c
        = [UInt8.ofNat (192 + c.toNat / 64), UInt8.ofNat (128 + c.toNat % 64)] := by
      simp +zetaDelta only [utf8EncodeChar, h1, h2, reduceIte, Nat.reducePow,
        Nat.shiftRight_eq_div_pow, and_3F, lead2_add hqlt, cont_add hrlt]
    rw [henc]
    have hb : (UInt8.ofNat (192 + c.toNat / 64)).toNat = 192 + c.toNat / 64 := by
      simp [Nat.mod_eq_of_lt (show 192 + c.toNat / 64 < 256 by omega)]
    rw [utf8Decode.eq_def]
    simp +zetaDelta only [hb, List.cons_append, continuationBits_ofNat hrlt,
      show ¬(192 + c.toNat / 64 < 128) by omega,
      show (decide (194 ≤ 192 + c.toNat / 64) && decide (192 + c.toNat / 64 ≤ 223)) = true by
        simp; omega,
      reduceIte, if_false]
    have hand : (192 + c.toNat / 64) &&& 31 = c.toNat / 64 := by rw [and_1F]; omega
    have hlor : (c.toNat / 64) * 2 ^ 6 ||| c.toNat % 64 = c.toNat := by
      rw [lor_add (show c.toNat % 64 < 2 ^ 6 by omega)]; omega
    rw [hand, Nat.shiftLeft_eq, hlor, charOfScalar_toNat]
    simp
  by_cases h3 : c.toNat < 0x10000
  · -- 3 byte
    have hqlt : c.toNat / 4096 < 16 := by omega
    have hv1 : c.toNat / 64 % 64 < 64 := by omega
    have hv2 : c.toNat % 64 < 64 := by omega
    have henc : utf8EncodeChar c = [UInt8.ofNat (224 + c.toNat / 4096),
        UInt8.ofNat (128 + c.toNat / 64 % 64), UInt8.ofNat (128 + c.toNat % 64)] := by
      simp +zetaDelta only [utf8EncodeChar, h1, h2, h3, reduceIte, Nat.reducePow,
        Nat.shiftRight_eq_div_pow, and_3F, lead3_add hqlt, cont_add hv1, cont_add hv2]
    rw [henc]
    have hb : (UInt8.ofNat (224 + c.toNat / 4096)).toNat = 224 + c.toNat / 4096 := by
      simp [Nat.mod_eq_of_lt (show 224 + c.toNat / 4096 < 256 by omega)]
    rw [utf8Decode.eq_def]
    simp +zetaDelta only [hb, List.cons_append, continuationBits_ofNat hv1,
      continuationBits_ofNat hv2,
      show ¬(224 + c.toNat / 4096 < 128) by omega,
      show (decide (194 ≤ 224 + c.toNat / 4096) && decide (224 + c.toNat / 4096 ≤ 223)) = false by
        simp; omega,
      show (decide (224 ≤ 224 + c.toNat / 4096) && decide (224 + c.toNat / 4096 ≤ 239)) = true by
        simp; omega,
      Bool.false_eq_true, reduceIte, if_false]
    have hand : (224 + c.toNat / 4096) &&& 15 = c.toNat / 4096 := by rw [and_0F]; omega
    rw [hand, Nat.shiftLeft_eq, Nat.shiftLeft_eq, lor3 hv1 hv2,
      show c.toNat / 4096 * 4096 + c.toNat / 64 % 64 * 64 + c.toNat % 64 = c.toNat by omega,
      if_neg (show ¬(c.toNat < 2048) by omega), charOfScalar_toNat]
    simp
  · -- 4 byte
    have hmax := toNat_lt c
    have hqlt : c.toNat / 262144 < 8 := by omega
    have hv1 : c.toNat / 4096 % 64 < 64 := by omega
    have hv2 : c.toNat / 64 % 64 < 64 := by omega
    have hv3 : c.toNat % 64 < 64 := by omega
    have henc : utf8EncodeChar c = [UInt8.ofNat (240 + c.toNat / 262144),
        UInt8.ofNat (128 + c.toNat / 4096 % 64), UInt8.ofNat (128 + c.toNat / 64 % 64),
        UInt8.ofNat (128 + c.toNat % 64)] := by
      simp +zetaDelta only [utf8EncodeChar, h1, h2, h3, reduceIte, Nat.reducePow,
        Nat.shiftRight_eq_div_pow, and_3F, lead4_add hqlt, cont_add hv1, cont_add hv2,
        cont_add hv3]
    rw [henc]
    have hb : (UInt8.ofNat (240 + c.toNat / 262144)).toNat = 240 + c.toNat / 262144 := by
      simp [Nat.mod_eq_of_lt (show 240 + c.toNat / 262144 < 256 by omega)]
    rw [utf8Decode.eq_def]
    simp +zetaDelta only [hb, List.cons_append, continuationBits_ofNat hv1,
      continuationBits_ofNat hv2, continuationBits_ofNat hv3,
      show ¬(240 + c.toNat / 262144 < 128) by omega,
      show (decide (194 ≤ 240 + c.toNat / 262144) &&
        decide (240 + c.toNat / 262144 ≤ 223)) = false by simp; omega,
      show (decide (224 ≤ 240 + c.toNat / 262144) &&
        decide (240 + c.toNat / 262144 ≤ 239)) = false by simp; omega,
      show (decide (240 ≤ 240 + c.toNat / 262144) &&
        decide (240 + c.toNat / 262144 ≤ 244)) = true by simp; omega,
      Bool.false_eq_true, reduceIte, if_false]
    have hand : (240 + c.toNat / 262144) &&& 7 = c.toNat / 262144 := by rw [and_07]; omega
    rw [hand, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq, lor4 hv1 hv2 hv3,
      show c.toNat / 262144 * 262144 + c.toNat / 4096 % 64 * 4096 + c.toNat / 64 % 64 * 64
        + c.toNat % 64 = c.toNat by omega,
      if_neg (show ¬(c.toNat < 65536) by omega), charOfScalar_toNat]
    simp

/-! ## 文字列の往復 -/

/-- 文字の列を符号化して読み直すと元に戻る。 -/
theorem utf8Decode_flatMap : ∀ l : List Char, utf8Decode (l.flatMap utf8EncodeChar) = l
  | [] => by rw [List.flatMap_nil, utf8Decode.eq_def]
  | c :: t => by rw [List.flatMap_cons, utf8Decode_encodeChar, utf8Decode_flatMap t]

/-- **UTF-8 で符号化して読み直すと元の文字列に戻る。** -/
theorem utf8Decode_encode (s : String) : utf8Decode (utf8Encode s) = s.toList :=
  utf8Decode_flatMap s.toList

/-- 文字列に戻す形。 -/
theorem utf8DecodeString_encode (s : String) : utf8DecodeString (utf8Encode s) = s := by
  unfold utf8DecodeString
  rw [utf8Decode_encode]
  simp

end Infra
