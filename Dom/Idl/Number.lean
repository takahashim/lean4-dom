/-!
# ECMAScript の Number と、WebIDL の整数型への変換（`unsigned long` と `unsigned short`）

WebIDL Standard §3.2.4「Integer types」の "ConvertToInt"（`docs/spec-version.md` に固定した版）。
`unsigned long` は `ConvertToInt(V, 32, "unsigned")`、`unsigned short` は `ConvertToInt(V, 16, "unsigned")` である。

## 二つの数の型

* `JsNumber` は JSON が運ぶ十進の数で、`mantissa × 10^(-exponent)` を正確に持つ（Lean の `JsonNumber` と同じ形）。
  scenario の値はこの形で届く。
* `JsNum` は ECMAScript の Number の値（IEEE 754 の倍精度）で、NaN、±∞、有限の値 (−1)^neg × k × 2^j を持つ。
  十進の数は、JavaScript が読むときと同じく最も近い倍精度の値に丸めてから使う（`ofDecimal`）。

ConvertToInt は ToNumber の結果（`JsNum`）に当てる。以前は十進のまま変換していたので、倍精度で正確に表せない数
（2^53 を超える整数など）で JavaScript と結果が違いえた。

## 有効数字が 20 桁を超える十進表記

ECMAScript の RoundMVResult は、有効数字が 20 桁を超える十進表記について、20 桁目で切り捨てたものと切り上げた
もののどちらの丸めを使ってもよいとしている（実装に任せる）。結果が一つに決まらないので、そのような数は model の
対象外とする（`ofDecimal?` が `none`）。

## 対象外

[EnforceRange] と [Clamp] の枝は、model が扱う method の引数に付いていないので書かない。
-/

namespace Dom.Idl

/-- JSON が運ぶ十進の数。値は `mantissa × 10^(-exponent)` である。 -/
structure JsNumber where
  mantissa : Int
  exponent : Nat
deriving DecidableEq, Repr, Inhabited

namespace JsNumber

/-- 自然数をそのまま十進の数として表す。 -/
def ofNat (n : Nat) : JsNumber := ⟨n, 0⟩

instance (n : Nat) : OfNat JsNumber n := ⟨ofNat n⟩

/-- 値が 0 か（+0 と −0 の両方）。 -/
def isZero (x : JsNumber) : Bool := x.mantissa == 0

end JsNumber

/-- **ECMAScript の Number の値。** 有限の値は (−1)^neg × k × 2^j で、k = 0 が ±0 である。 -/
inductive JsNum where
  | nan
  | infinity (neg : Bool)
  | finite (neg : Bool) (k : Nat) (j : Int)
deriving DecidableEq, Repr, Inhabited

namespace JsNum

/-- 自然数（2^53 以下なら倍精度で正確に表せる）をそのまま Number の値にする。 -/
def ofNat (n : Nat) : JsNum := .finite false n 0

/-- 2 の冪。指数が負なら使わない。 -/
def pow2 (j : Int) : Nat := 2 ^ j.toNat

/-- 正の有理数 n / d が 2^a 未満か。 -/
def ltPow2 (n d : Nat) (a : Int) : Bool :=
  if a ≥ 0 then n < d * pow2 a else n * pow2 (-a) < d

/--
**正の有理数 n / d（n > 0、d > 0）を最も近い倍精度の値 k × 2^j に丸める。** 二つの値のちょうど中間なら
k が偶数のほうを取る（IEEE 754 の roundTiesToEven、ECMAScript の「the Number value for x」）。
溢れて ∞ になるなら `none`。

1. 2^52 ≤ n / (d × 2^e) < 2^53 となる e を求める。floor(log₂ n) − floor(log₂ d) を l とすると、
   floor(log₂(n/d)) は l か l − 1 で、n/d < 2^l なら l − 1 である。
2. 非正規化数の範囲では e を −1074 で止める。
3. q を n / (d × 2^e) の整数部、余りで偶数への丸めをする。q が 2^53 になったら q = 2^52、e + 1 とする。
4. e が 971 を超えれば、値は倍精度の最大値（(2^53 − 1) × 2^971）を超えて丸められているので ∞ である。
-/
def roundPos (n d : Nat) : Option (Nat × Int) :=
  let l : Int := (n.log2 : Int) - (d.log2 : Int)
  let e₀ : Int := (if ltPow2 n d l then l - 1 else l) - 52
  let e : Int := max e₀ (-1074)
  let num := if e ≥ 0 then n else n * pow2 (-e)
  let den := if e ≥ 0 then d * pow2 e else d
  let q := num / den
  let r := num % den
  let q := if 2 * r > den || (2 * r == den && q % 2 == 1) then q + 1 else q
  let (q, e) := if q == 2 ^ 53 then (2 ^ 52, e + 1) else (q, e)
  if e > 971 then none else some (q, e)

/-- 符号と有理数 n / d から Number の値を作る（丸める）。 -/
def ofRat (neg : Bool) (n d : Nat) : JsNum :=
  if n == 0 then .finite neg 0 0
  else match roundPos n d with
    | none => .infinity neg
    | some (k, j) => .finite neg k j

/--
符号と十進の値 m × 10^e（m ≥ 0）から Number の値を作る。

m が D 桁なら値は 10^(D+e−1) 以上 10^(D+e) 未満なので、D + e > 310 なら倍精度の最大値（約 1.8 × 10^308）を
超えて ∞、D + e < −330 なら最小の非正規化数（約 4.9 × 10^−324）の半分より小さくて ±0 である。この二つは
冪を計算せずに決める（`"1e1000000000"` のような文字列で巨大な冪を作らないため）。

それ以外は `ofRat` で、その丸め（`roundPos`）が最も近い倍精度の値を返すことは `Dom.Spec.roundPos_spec` で証明してある。
この二つの近道は証明の範囲の外で、10^310 > 2^1024 と 10^(−330) < 2^(−1075) の散文の議論と、`#guard` の例だけが根拠である。
-/
def ofDecimal (neg : Bool) (m : Nat) (e : Int) : JsNum :=
  let digits : Int := (toString m).length
  if m == 0 then .finite neg 0 0
  else if digits + e > 310 then .infinity neg
  else if digits + e < -330 then .finite neg 0 0
  else if e ≥ 0 then ofRat neg (m * 10 ^ e.toNat) 1 else ofRat neg m (10 ^ (-e).toNat)

/-- 十進の数字列の有効数字の桁数（先頭と末尾の 0 を除いた長さ）。 -/
def significantDigits (m : Nat) : Nat :=
  if m == 0 then 0
  else
    let ds := (toString m).toList
    (ds.reverse.dropWhile (· == '0')).length

/-- 有効数字が 20 桁以下なら丸めた値、それを超えれば（丸めが実装に任されるので）`none`。 -/
def ofDecimal? (neg : Bool) (m : Nat) (e : Int) : Option JsNum :=
  if significantDigits m > 20 then none else some (ofDecimal neg m e)

/--
ECMAScript の IntegerPart(x) の絶対値：|x| の floor。有限の値にだけ使う。
-/
def truncAbs (k : Nat) (j : Int) : Nat :=
  if j ≥ 0 then k * 2 ^ j.toNat else k / 2 ^ (-j).toNat

end JsNum

namespace JsNumber

/-- **JSON の十進の数を、JavaScript が読むのと同じく Number の値に丸める。** 有効数字が 20 桁を超えれば `none`。 -/
def toNum? (x : JsNumber) : Option JsNum :=
  JsNum.ofDecimal? (x.mantissa < 0) x.mantissa.natAbs (-(x.exponent : Int))

end JsNumber

/--
**WebIDL の ConvertToInt(V, bitLength, "unsigned")**（[EnforceRange] と [Clamp] の無い場合）。
V はすでに ToNumber を済ませた Number の値である。

1-3. bitLength が 64 でなく unsigned なので、範囲は 0 から 2^bitLength − 1（[EnforceRange] と [Clamp] の
     枝でだけ使う）。
4.   x を ToNumber(V) とする（V はすでに Number）。
5.   x が −0 なら +0 にする。
8.   x が NaN、+0、+∞、−∞ なら +0 を返す。
9.   x を IntegerPart(x) にする。
10.  x を x modulo 2^bitLength にする（ECMAScript の modulo は除数の符号を持つので、0 以上になる）。
12.  x を返す。
-/
def convertToIntUnsigned (bitLength : Nat) : JsNum → Nat
  | .finite neg k j =>
    let a : Int := JsNum.truncAbs k j
    let x : Int := if neg then -a else a
    (x % ((2 : Int) ^ bitLength)).toNat
  | _ => 0

/-- **JavaScript の値を IDL の `unsigned long` に変換する。** -/
def toUnsignedLong (x : JsNum) : Nat := convertToIntUnsigned 32 x

/-- **JavaScript の値を IDL の `unsigned short` に変換する。** -/
def toUnsignedShort (x : JsNum) : Nat := convertToIntUnsigned 16 x

/-! ## 性質 -/

private theorem emod_toNat_lt (b : Nat) (x : Int) : (x % ((2 : Int) ^ b)).toNat < 2 ^ b := by
  have hpn : 0 < 2 ^ b := Nat.pow_pos (by decide)
  have hc : ((2 : Int) ^ b) = ((2 ^ b : Nat) : Int) := by norm_cast
  rw [hc]
  have hpos : (0 : Int) < ((2 ^ b : Nat) : Int) := by exact_mod_cast hpn
  have h1 := Int.emod_nonneg x (Int.ne_of_gt hpos)
  have h2 := Int.emod_lt_of_pos x hpos
  omega

/-- 結果は 2^bitLength より小さい。 -/
theorem convertToIntUnsigned_lt (b : Nat) (x : JsNum) : convertToIntUnsigned b x < 2 ^ b := by
  have hpn : 0 < 2 ^ b := Nat.pow_pos (by decide)
  cases x with
  | nan => exact hpn
  | infinity _ => exact hpn
  | finite neg k j => exact emod_toNat_lt b _

/--
**範囲内の自然数は変わらない。** model がそれまで受け取っていた値（2^bitLength 未満の自然数）では、
変換は何もしない。
-/
theorem convertToIntUnsigned_ofNat {b n : Nat} (h : n < 2 ^ b) :
    convertToIntUnsigned b (JsNum.ofNat n) = n := by
  unfold convertToIntUnsigned JsNum.ofNat JsNum.truncAbs
  simp only [Bool.false_eq_true, if_false]
  have h0 : ((0 : Int) ≥ 0) = True := by simp
  simp only [ge_iff_le, Int.le_refl, if_true, Int.toNat_zero, Nat.pow_zero, Nat.mul_one]
  have hlt : (n : Int) < (2 : Int) ^ b := by exact_mod_cast h
  rw [Int.emod_eq_of_lt (by omega) hlt]
  simp

theorem toUnsignedLong_ofNat {n : Nat} (h : n < 2 ^ 32) : toUnsignedLong (JsNum.ofNat n) = n :=
  convertToIntUnsigned_ofNat h

theorem toUnsignedShort_ofNat {n : Nat} (h : n < 2 ^ 16) : toUnsignedShort (JsNum.ofNat n) = n :=
  convertToIntUnsigned_ofNat h

/-! ## 例 -/

private def u32 (x : JsNumber) : Option Nat := x.toNum?.map toUnsignedLong
private def u16 (x : JsNumber) : Option Nat := x.toNum?.map toUnsignedShort

-- −1 は 2^32 − 1 になる。
#guard u32 ⟨-1, 0⟩ == some 4294967295
-- 2^32 は 0 になる。
#guard u32 ⟨4294967296, 0⟩ == some 0
-- 1.5 は 1、−1.5 は 2^32 − 1 になる（0 の方向へ切り捨ててから剰余を取る）。
#guard u32 ⟨15, 1⟩ == some 1
#guard u32 ⟨-15, 1⟩ == some 4294967295
-- −0.5 は 0 になる（IntegerPart が 0）。
#guard u32 ⟨-5, 1⟩ == some 0
-- `unsigned short` では 65536 が 0、−65535 が 1 になる。
#guard u16 ⟨65536, 0⟩ == some 0
#guard u16 ⟨-65535, 0⟩ == some 1
-- 2^53 + 1 は倍精度で 2^53 に丸まるので、2^32 の剰余は 0 である（十進のままなら 1）。
#guard u32 ⟨9007199254740993, 0⟩ == some 0
-- 4294967295.9999999999 は 2^32 に丸まるので 0 になる（十進のままなら 4294967295）。
#guard u32 ⟨42949672959999999999, 10⟩ == some 0
-- 有効数字が 20 桁を超える数は対象外。
#guard u32 ⟨123456789012345678901, 0⟩ == none
-- 1e309 は ∞ に丸まるので 0 になる。
#guard u32 ⟨10 ^ 309, 0⟩ == some 0
#guard (JsNum.ofDecimal false 1 1000000000) == .infinity false
#guard (JsNum.ofDecimal true 1 (-1000000000)) == .finite true 0 0

end Dom.Idl
