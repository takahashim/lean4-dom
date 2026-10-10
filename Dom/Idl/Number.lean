/-!
# WebIDL の整数型への変換（`unsigned long` と `unsigned short`）

WebIDL Standard §3.2.4「Integer types」の "ConvertToInt"（`docs/spec-version.md` に固定した版）。
`unsigned long` は `ConvertToInt(V, 32, "unsigned")`、`unsigned short` は `ConvertToInt(V, 16, "unsigned")` である。

## JavaScript の値の範囲

scenario は JSON で値を運ぶので、model が受け取る JavaScript の値は JSON の数に限る。
JSON の数は有限の十進小数で、`mantissa × 10^(-exponent)` として正確に持つ（Lean の `JsonNumber` と同じ形）。
NaN と ±∞ は JSON に無い。`-0` は mantissa が 0 になり +0 と区別できないが、ConvertToInt は step で
−0 を +0 にするので結果は変わらない。

JavaScript は JSON の数を二進の倍精度に丸めてから変換する。ここでは十進のまま変換するので、
両者が一致するのは数が倍精度で正確に表せるときである。差分テストの生成器はそのような数だけを作る
（絶対値が 2^53 未満の整数と、それに 0.5 を足したもの）。

## 対象外

ToNumber は数以外（文字列、boolean、null、object）を受けない。[EnforceRange] と [Clamp] の枝は、
model が扱う method の引数に付いていないので書かない。
-/

namespace Dom.Idl

/-- JSON が運ぶ JavaScript の Number。値は `mantissa × 10^(-exponent)` である。 -/
structure JsNumber where
  mantissa : Int
  exponent : Nat
deriving DecidableEq, Repr, Inhabited

namespace JsNumber

/-- 自然数をそのまま Number として表す。 -/
def ofNat (n : Nat) : JsNumber := ⟨n, 0⟩

instance (n : Nat) : OfNat JsNumber n := ⟨ofNat n⟩

/-- 値が 0 か（+0 と −0 の両方）。 -/
def isZero (x : JsNumber) : Bool := x.mantissa == 0

/--
ECMAScript の IntegerPart(x)：絶対値の floor に x の符号を付けたもの、つまり 0 の方向への切り捨て。
-/
def integerPart (x : JsNumber) : Int := x.mantissa.tdiv ((10 : Int) ^ x.exponent)

end JsNumber

/--
**WebIDL の ConvertToInt(V, bitLength, "unsigned")**（[EnforceRange] と [Clamp] の無い場合）。

1-3. bitLength が 64 でなく unsigned なので、範囲は 0 から 2^bitLength − 1（[EnforceRange] と [Clamp] の
     枝でだけ使う）。
4.   x を ToNumber(V) とする（V はすでに Number）。
5.   x が −0 なら +0 にする。
8.   x が NaN、+0、+∞、−∞ なら +0 を返す。
9.   x を IntegerPart(x) にする。
10.  x を x modulo 2^bitLength にする（ECMAScript の modulo は除数の符号を持つので、0 以上になる）。
12.  x を返す。
-/
def convertToIntUnsigned (bitLength : Nat) (x : JsNumber) : Nat :=
  if x.isZero then 0
  else (x.integerPart % ((2 : Int) ^ bitLength)).toNat

/-- **JavaScript の値を IDL の `unsigned long` に変換する。** -/
def toUnsignedLong (x : JsNumber) : Nat := convertToIntUnsigned 32 x

/-- **JavaScript の値を IDL の `unsigned short` に変換する。** -/
def toUnsignedShort (x : JsNumber) : Nat := convertToIntUnsigned 16 x

/-! ## 性質 -/

/-- 結果は 2^bitLength より小さい。 -/
theorem convertToIntUnsigned_lt (b : Nat) (x : JsNumber) : convertToIntUnsigned b x < 2 ^ b := by
  unfold convertToIntUnsigned
  have hpn : 0 < 2 ^ b := Nat.pow_pos (by decide)
  split
  · exact hpn
  · have hc : ((2 : Int) ^ b) = ((2 ^ b : Nat) : Int) := by norm_cast
    rw [hc]
    have hpos : (0 : Int) < ((2 ^ b : Nat) : Int) := by exact_mod_cast hpn
    have h1 := Int.emod_nonneg x.integerPart (Int.ne_of_gt hpos)
    have h2 := Int.emod_lt_of_pos x.integerPart hpos
    omega

/--
**範囲内の自然数は変わらない。** model がそれまで受け取っていた値（2^bitLength 未満の自然数）では、
変換は何もしない。
-/
theorem convertToIntUnsigned_ofNat {b n : Nat} (h : n < 2 ^ b) :
    convertToIntUnsigned b (JsNumber.ofNat n) = n := by
  unfold convertToIntUnsigned JsNumber.ofNat JsNumber.isZero JsNumber.integerPart
  have h10 : ((10 : Int) ^ 0) = 1 := rfl
  simp only [h10, Int.tdiv_one]
  split
  · rename_i hz
    simp at hz
    omega
  · have hlt : (n : Int) < (2 : Int) ^ b := by exact_mod_cast h
    rw [Int.emod_eq_of_lt (by omega) hlt]
    simp

theorem toUnsignedLong_ofNat {n : Nat} (h : n < 2 ^ 32) : toUnsignedLong (JsNumber.ofNat n) = n :=
  convertToIntUnsigned_ofNat h

theorem toUnsignedShort_ofNat {n : Nat} (h : n < 2 ^ 16) : toUnsignedShort (JsNumber.ofNat n) = n :=
  convertToIntUnsigned_ofNat h

/-! ## 例

`decide` で確かめる（kernel が評価する）。
-/

/-- −1 は 2^32 − 1 になる。 -/
example : toUnsignedLong ⟨-1, 0⟩ = 4294967295 := by decide
/-- 2^32 は 0 になる。 -/
example : toUnsignedLong ⟨4294967296, 0⟩ = 0 := by decide
/-- 1.5 は 1、−1.5 は 2^32 − 1 になる（0 の方向へ切り捨ててから剰余を取る）。 -/
example : toUnsignedLong ⟨15, 1⟩ = 1 := by decide
example : toUnsignedLong ⟨-15, 1⟩ = 4294967295 := by decide
/-- −0.5 は 0 になる（IntegerPart が 0）。 -/
example : toUnsignedLong ⟨-5, 1⟩ = 0 := by decide
/-- `unsigned short` では 65536 が 0、−65535 が 1 になる。 -/
example : toUnsignedShort ⟨65536, 0⟩ = 0 := by decide
example : toUnsignedShort ⟨-65535, 0⟩ = 1 := by decide

end Dom.Idl
