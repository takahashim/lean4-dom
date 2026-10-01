import Infra.Bytes
import Infra.Bits

/-!
# UTF-8 の往復

`utf8Decode (utf8Encode s) = s.toList`。

符号化はビット演算で書いてあるので、まずそれを算術に直す足場を作る。
`|||` を足し算に直す汎用補題は `Infra/Bits.lean` にあり、ここでは UTF-8 の
byte の形（先頭 byte の印と continuation byte）に固有の補題だけを置く。
-/

namespace Infra

/-! ## UTF-8 の byte の形 -/

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
  unfold charOfScalar
  rw [if_pos (isScalarValue_toNat c)]
  exact Char.ofNat_toNat c

/-- `Char` の番号は Unicode の上限未満である。4 byte の場合の先頭 byte の範囲に使う。 -/
theorem toNat_lt (c : Char) : c.toNat < 0x110000 := by
  have hv : c.toNat < 0xD800 ∨ (0xDFFF < c.toNat ∧ c.toNat < 0x110000) := c.valid
  rcases hv with h | h
  · omega
  · exact h.2

/-- 3 byte の符号化で、最初の continuation byte が decoder の boundary に入る。 -/
theorem lead3_bound (c : Char) (h2 : ¬ c.toNat < 0x800) (h3 : c.toNat < 0x10000) :
    ((if (224 + c.toNat / 4096) == 0xE0 then (0xA0 : Nat) else 0x80)
        ≤ 128 + c.toNat / 64 % 64 &&
      128 + c.toNat / 64 % 64
        ≤ (if (224 + c.toNat / 4096) == 0xED then (0x9F : Nat) else 0xBF)) = true := by
  have hq : c.toNat / 4096 < 16 := by omega
  have hr : c.toNat / 64 % 64 < 64 := by omega
  by_cases hq0 : c.toNat / 4096 = 0
  · have hlo : (if (224 + c.toNat / 4096) == 0xE0 then (0xA0 : Nat) else 0x80) = 0xA0 := by
      rw [if_pos (by rw [beq_iff_eq]; omega)]
    have hhi : (if (224 + c.toNat / 4096) == 0xED then (0x9F : Nat) else 0xBF) = 0xBF := by
      rw [if_neg (by rw [beq_iff_eq]; omega)]
    rw [hlo, hhi]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  · by_cases hq13 : c.toNat / 4096 = 13
    · have hlo : (if (224 + c.toNat / 4096) == 0xE0 then (0xA0 : Nat) else 0x80) = 0x80 := by
        rw [if_neg (by rw [beq_iff_eq]; omega)]
      have hhi : (if (224 + c.toNat / 4096) == 0xED then (0x9F : Nat) else 0xBF) = 0x9F := by
        rw [if_pos (by rw [beq_iff_eq]; omega)]
      have hsur : c.toNat < 0xD800 := by
        have hv : c.toNat < 0xD800 ∨ (0xDFFF < c.toNat ∧ c.toNat < 0x110000) := c.valid
        rcases hv with h | h
        · exact h
        · omega
      rw [hlo, hhi]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      have h1 : c.toNat / 64 < 864 := by omega
      have h2 : 832 ≤ c.toNat / 64 := by omega
      have hd : c.toNat / 64 / 64 = 13 := by omega
      omega
    · have hlo : (if (224 + c.toNat / 4096) == 0xE0 then (0xA0 : Nat) else 0x80) = 0x80 := by
        rw [if_neg (by rw [beq_iff_eq]; omega)]
      have hhi : (if (224 + c.toNat / 4096) == 0xED then (0x9F : Nat) else 0xBF) = 0xBF := by
        rw [if_neg (by rw [beq_iff_eq]; omega)]
      rw [hlo, hhi]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      omega

/-- 4 byte の符号化で、最初の continuation byte が decoder の boundary に入る。 -/
theorem lead4_bound (c : Char) (h3 : ¬ c.toNat < 0x10000) :
    ((if (240 + c.toNat / 262144) == 0xF0 then (0x90 : Nat) else 0x80)
        ≤ 128 + c.toNat / 4096 % 64 &&
      128 + c.toNat / 4096 % 64
        ≤ (if (240 + c.toNat / 262144) == 0xF4 then (0x8F : Nat) else 0xBF)) = true := by
  have hmax := toNat_lt c
  have hq : c.toNat / 262144 < 8 := by omega
  have hr : c.toNat / 4096 % 64 < 64 := by omega
  by_cases hq0 : c.toNat / 262144 = 0
  · have hlo : (if (240 + c.toNat / 262144) == 0xF0 then (0x90 : Nat) else 0x80) = 0x90 := by
      rw [if_pos (by rw [beq_iff_eq]; omega)]
    have hhi : (if (240 + c.toNat / 262144) == 0xF4 then (0x8F : Nat) else 0xBF) = 0xBF := by
      rw [if_neg (by rw [beq_iff_eq]; omega)]
    rw [hlo, hhi]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    have h1 : 16 ≤ c.toNat / 4096 := by omega
    have h2 : c.toNat / 4096 < 64 := by omega
    have hd : c.toNat / 4096 / 64 = 0 := by
      rw [Nat.div_div_eq_div_mul, show 4096 * 64 = 262144 by omega]
      exact hq0
    omega
  · by_cases hq4 : c.toNat / 262144 = 4
    · have hlo : (if (240 + c.toNat / 262144) == 0xF0 then (0x90 : Nat) else 0x80) = 0x80 := by
        rw [if_neg (by rw [beq_iff_eq]; omega)]
      have hhi : (if (240 + c.toNat / 262144) == 0xF4 then (0x8F : Nat) else 0xBF) = 0x8F := by
        rw [if_pos (by rw [beq_iff_eq]; omega)]
      rw [hlo, hhi]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      have h1 : c.toNat / 4096 < 272 := by omega
      have h2 : 256 ≤ c.toNat / 4096 := by omega
      have hd : c.toNat / 4096 / 64 = 4 := by
        rw [Nat.div_div_eq_div_mul, show 4096 * 64 = 262144 by omega]
        exact hq4
      omega
    · have hlo : (if (240 + c.toNat / 262144) == 0xF0 then (0x90 : Nat) else 0x80) = 0x80 := by
        rw [if_neg (by rw [beq_iff_eq]; omega)]
      have hhi : (if (240 + c.toNat / 262144) == 0xF4 then (0x8F : Nat) else 0xBF) = 0xBF := by
        rw [if_neg (by rw [beq_iff_eq]; omega)]
      rw [hlo, hhi]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      omega

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
    have hb1 : (UInt8.ofNat (128 + c.toNat / 64 % 64)).toNat = 128 + c.toNat / 64 % 64 := by
      simp [Nat.mod_eq_of_lt (show 128 + c.toNat / 64 % 64 < 256 by omega)]
    have hbound0 := lead3_bound c h2 h3
    have hbound : withinBoundary
        (if (224 + c.toNat / 4096) == 0xE0 then 0xA0 else 0x80)
        (if (224 + c.toNat / 4096) == 0xED then 0x9F else 0xBF)
        (128 + c.toNat / 64 % 64) = true := by
      simpa [withinBoundary, beq_iff_eq] using hbound0
    have hmask : (128 + c.toNat / 64 % 64) &&& 63 = c.toNat / 64 % 64 := by rw [and_3F]; omega
    rw [utf8Decode.eq_def]
    simp +zetaDelta only [hb, hb1, hbound, List.cons_append, continuationBits_ofNat hv2,
      show ¬(224 + c.toNat / 4096 < 128) by omega,
      show (decide (194 ≤ 224 + c.toNat / 4096) && decide (224 + c.toNat / 4096 ≤ 223)) = false by
        simp; omega,
      show (decide (224 ≤ 224 + c.toNat / 4096) && decide (224 + c.toNat / 4096 ≤ 239)) = true by
        simp; omega,
      Bool.false_eq_true, reduceIte, if_false]
    have hand : (224 + c.toNat / 4096) &&& 15 = c.toNat / 4096 := by rw [and_0F]; omega
    rw [hand, hmask, Nat.shiftLeft_eq, Nat.shiftLeft_eq, lor3 hv1 hv2,
      show c.toNat / 4096 * 4096 + c.toNat / 64 % 64 * 64 + c.toNat % 64 = c.toNat by omega,
      charOfScalar_toNat]
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
    have hb1 : (UInt8.ofNat (128 + c.toNat / 4096 % 64)).toNat = 128 + c.toNat / 4096 % 64 := by
      simp [Nat.mod_eq_of_lt (show 128 + c.toNat / 4096 % 64 < 256 by omega)]
    have hbound0 := lead4_bound c h3
    have hbound : withinBoundary
        (if (240 + c.toNat / 262144) == 0xF0 then 0x90 else 0x80)
        (if (240 + c.toNat / 262144) == 0xF4 then 0x8F else 0xBF)
        (128 + c.toNat / 4096 % 64) = true := by
      simpa [withinBoundary, beq_iff_eq] using hbound0
    have hmask : (128 + c.toNat / 4096 % 64) &&& 63 = c.toNat / 4096 % 64 := by rw [and_3F]; omega
    rw [utf8Decode.eq_def]
    simp +zetaDelta only [hb, hb1, hbound, List.cons_append, continuationBits_ofNat hv2,
      continuationBits_ofNat hv3,
      show ¬(240 + c.toNat / 262144 < 128) by omega,
      show (decide (194 ≤ 240 + c.toNat / 262144) &&
        decide (240 + c.toNat / 262144 ≤ 223)) = false by simp; omega,
      show (decide (224 ≤ 240 + c.toNat / 262144) &&
        decide (240 + c.toNat / 262144 ≤ 239)) = false by simp; omega,
      show (decide (240 ≤ 240 + c.toNat / 262144) &&
        decide (240 + c.toNat / 262144 ≤ 244)) = true by simp; omega,
      Bool.false_eq_true, reduceIte, if_false]
    have hand : (240 + c.toNat / 262144) &&& 7 = c.toNat / 262144 := by rw [and_07]; omega
    rw [hand, hmask, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq, lor4 hv1 hv2 hv3,
      show c.toNat / 262144 * 262144 + c.toNat / 4096 % 64 * 4096 + c.toNat / 64 % 64 * 64
        + c.toNat % 64 = c.toNat by omega,
      charOfScalar_toNat]
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
