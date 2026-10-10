import Dom.Idl.Number

/-!
# Number の文字列化（ECMAScript の Number::toString、基数 10）

DOMString への変換（ToString）は、数を ECMAScript の Number::toString(x, 10) で文字列にする
（ECMA-262 §6.1.6.1.20）。本文は x を表す最短の十進表記 s × 10^(n−k)（k 桁）を選び、n の範囲で
四つの書き方に分ける。

## 最短の十進表記を求めるのは、有効数字が 15 桁以下のときに限る

本文の s と k は「Number の値が x になる最短の十進表記」で、x は JSON の十進表記を倍精度に丸めた値である。
十進の値を d（末尾の 0 を除いて k₀ 桁）とする。倍精度は正規数の範囲で有効数字 15 桁の十進表記を区別できる
（15 桁以下の異なる十進表記は、異なる倍精度の値に丸まる）。k₀ ≤ 15 なら、x に丸まる k₀ 桁以下の十進表記は
d だけなので、本文の s、k、n は d から読める。

そこで、有効数字が 15 桁を超える数と、正規数の範囲（10 進の指数 n − 1 が −307 以上 307 以下）の外の数は
model の対象外（`none`）とする。
-/

namespace Dom.Idl

namespace JsNumber

/-- 十進の数字列の末尾の 0 を落とす。 -/
private def dropTrailingZeros (ds : List Char) : List Char :=
  (ds.reverse.dropWhile (· == '0')).reverse

/--
**ECMAScript の Number::toString(x, 10)。** 対象外の数（上の節）は `none`。

1.  x が NaN なら "NaN"（JSON に無い）。
2.  x が +0 か −0 なら "0"。
3.  x < 0 なら "-" と Number::toString(−x) をつなぐ。
4.  x が +∞ なら "Infinity"（JSON に無い）。
5.  n、k、s を、k ≥ 1、10^(k−1) ≤ s < 10^k、s × 10^(n−k) が x、k が最小となるように取る。
6.  k ≤ n ≤ 21 なら、s の k 桁の後に n − k 個の "0"。
7.  0 < n ≤ 21 なら、s の上位 n 桁、"."、残りの k − n 桁。
8.  −6 < n ≤ 0 なら、"0."、−n 個の "0"、s の k 桁。
9-10. それ以外は指数表記。e = n − 1 として、k = 1 なら s の 1 桁、"e"、符号、|e|。
      k > 1 なら s の上位 1 桁、"."、残りの k − 1 桁、"e"、符号、|e|。符号は e ≥ 0 なら "+"、そうでなければ "-"。
-/
def toJsString (x : JsNumber) : Option String :=
  if x.mantissa == 0 then some "0"
  else
    let sign := if x.mantissa < 0 then "-" else ""
    let all := (toString x.mantissa.natAbs).toList
    let digits := dropTrailingZeros all
    let k : Int := digits.length
    -- 値は digits × 10^(落とした 0 の数 − exponent) = s × 10^(n − k)
    let n : Int := (all.length - digits.length : Nat) - (x.exponent : Int) + k
    if digits.length > 15 || n - 1 < -307 || n - 1 > 307 then none
    else
      let s := String.ofList digits
      let body :=
        if k ≤ n && n ≤ 21 then s ++ String.ofList (List.replicate (n - k).toNat '0')
        else if 0 < n && n ≤ 21 then
          String.ofList (digits.take n.toNat) ++ "." ++ String.ofList (digits.drop n.toNat)
        else if -6 < n && n ≤ 0 then "0." ++ String.ofList (List.replicate (-n).toNat '0') ++ s
        else
          let e := n - 1
          let esign := if e ≥ 0 then "+" else "-"
          let mant := if digits.length = 1 then s
            else String.ofList (digits.take 1) ++ "." ++ String.ofList (digits.drop 1)
          mant ++ "e" ++ esign ++ toString e.natAbs
      some (sign ++ body)

end JsNumber

/-! ## 例 -/

#guard JsNumber.toJsString ⟨0, 0⟩ = some "0"
#guard JsNumber.toJsString ⟨-5, 0⟩ = some "-5"
#guard JsNumber.toJsString ⟨150, 1⟩ = some "15"
#guard JsNumber.toJsString ⟨15, 1⟩ = some "1.5"
#guard JsNumber.toJsString ⟨5, 7⟩ = some "5e-7"
#guard JsNumber.toJsString ⟨5, 6⟩ = some "0.000005"
#guard JsNumber.toJsString ⟨123, 9⟩ = some "1.23e-7"
#guard JsNumber.toJsString ⟨10 ^ 21, 0⟩ = some "1e+21"
#guard JsNumber.toJsString ⟨10 ^ 20, 0⟩ = some "100000000000000000000"
#guard JsNumber.toJsString ⟨1234567890123456, 0⟩ = none

end Dom.Idl
