/-!
# 正の有理数を、最も近い倍精度の値に丸める（関係）

ECMA-262 の「the Number value for x」（§6.1.6.1）は、x に最も近い IEEE 754 binary64 の値で、二つの値のちょうど中間なら
仮数が偶数のほうを取る（roundTiesToEven）。x が 2^1024 − 2^970 以上なら +∞ である。ここでは正の有理数 n/d について、
その値を実行関数とは独立に書く（実装は `Dom/Idl/Number.lean` の `JsNum.roundPos`、一致の証明は
`Dom/Spec/DoubleSound.lean`）。

## binade の中で最も近い値を取れば、全体で最も近い値になる

倍精度の有限の値は k × 2^e（0 ≤ k < 2^53、−1074 ≤ e ≤ 971）で、正規数は 2^52 ≤ k、非正規化数は e = −1074 である。
x の binade（`Binade`）は、正規数なら 2^(e+52) ≤ x < 2^(e+53) となる e、x < 2^(−1022) なら e = −1074 である。
この区間の倍精度の値は 2^e の倍数 q × 2^e で、隣り合う値の間隔は 2^e である。区間の外の値は、下の端
2^(e+52)（区間の値）か上の端 2^(e+53)（q = 2^53 にあたる）よりも x から遠い。だから x に最も近い倍精度の値は、
2^e の倍数のうち x に最も近いもの（`RoundsAt`）で、q = 2^53 なら 2^52 × 2^(e+1) と書き直す。e + 1 が 971 を
超えれば、x は 2^1024 − 2^970 以上で、結果は ∞ である。

この節の議論（区間の外の値のほうが遠いこと）は散文で、定理にはしていない。関係はそれを前提に、binade と、その中での
丸めを書く。

## 指数が負になりうる比較

2^a（a は整数）との比較は、a の正の部分 a⁺ と負の部分 a⁻（a = a⁺ − a⁻）を使って、分母を払った自然数の不等式で書く。
n/d ≥ 2^a は d × 2^(a⁺) ≤ n × 2^(a⁻) である。
-/

namespace Dom.Spec

/-- 指数の正の部分 a⁺。 -/
def expPos (a : Int) : Nat := a.toNat

/-- 指数の負の部分 a⁻。 -/
def expNeg (a : Int) : Nat := (-a).toNat

/-- 正の有理数 n/d が 2^a 以上である。 -/
def GePow (n d : Nat) (a : Int) : Prop := d * 2 ^ expPos a ≤ n * 2 ^ expNeg a

/-- 正の有理数 n/d が 2^a より小さい。 -/
def LtPow (n d : Nat) (a : Int) : Prop := n * 2 ^ expNeg a < d * 2 ^ expPos a

/--
**倍精度の binade。** 正規数なら 2^(e+52) ≤ n/d < 2^(e+53)、非正規化数なら e = −1074 で n/d < 2^(−1021)
（このとき n/d は 2^(−1022) より小さいか、丸めて 2^(−1022) になる）。
-/
structure Binade (n d : Nat) (e : Int) : Prop where
  ge : -1074 ≤ e
  lt : LtPow n d (e + 53)
  low : e = -1074 ∨ GePow n d (e + 52)

/--
**n/d を、2^e の倍数のうち最も近いもの q × 2^e に丸める。** |n/d − q × 2^e| ≤ 2^e / 2 で、ちょうど中間なら q は偶数。

分母を払って整数で書く。u = n × 2^(e⁻)、v = d × 2^(e⁺) とすると n/d ÷ 2^e = u/v なので、
|u/v − q| ≤ 1/2 は (2q − 1)v ≤ 2u ≤ (2q + 1)v である。
-/
structure RoundsAt (n d q : Nat) (e : Int) : Prop where
  upper : 2 * ((n * 2 ^ expNeg e : Nat) : Int) ≤ (2 * q + 1) * ((d * 2 ^ expPos e : Nat) : Int)
  lower : (2 * q - 1) * ((d * 2 ^ expPos e : Nat) : Int) ≤ 2 * ((n * 2 ^ expNeg e : Nat) : Int)
  tie : (2 * ((n * 2 ^ expNeg e : Nat) : Int) = (2 * q + 1) * ((d * 2 ^ expPos e : Nat) : Int) ∨
         2 * ((n * 2 ^ expNeg e : Nat) : Int) = (2 * q - 1) * ((d * 2 ^ expPos e : Nat) : Int)) →
        q % 2 = 0

/--
**正の有理数 n/d に最も近い倍精度の値。** `some (k, j)` は有限の値 k × 2^j、`none` は +∞ である。

binade e の中で q に丸め、q = 2^53 なら 2^52 × 2^(e+1) と書き直す。指数が 971 を超えれば +∞ である。
-/
def NearestDouble (n d : Nat) (r : Option (Nat × Int)) : Prop :=
  ∃ e q, Binade n d e ∧ RoundsAt n d q e ∧ q ≤ 2 ^ 53 ∧
    ((q < 2 ^ 53 ∧ e ≤ 971 ∧ r = some (q, e)) ∨
     (q = 2 ^ 53 ∧ e + 1 ≤ 971 ∧ r = some (2 ^ 52, e + 1)) ∨
     (((q < 2 ^ 53 ∧ 971 < e) ∨ (q = 2 ^ 53 ∧ 971 < e + 1)) ∧ r = none))

end Dom.Spec
