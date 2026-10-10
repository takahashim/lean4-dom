import Trace.Basic
import Dom

/-!
# ECMA-262 の対応表

Web IDL の変換が呼ぶ ECMAScript の抽象操作の対応表。`docs/spec-version.md` に固定した `spec.html` から、
`spec-trace/extract_ecma.rb` が型変換（§7.1）、Number::toString（§6.1.6.1.20）、`Array.prototype.join`（§23.1.3.18）の
節だけを抜き出し、`ruby spec-trace/check.rb --spec ecma262` が `spec-trace/ecma262.json` と突き合わせる。

鍵は節の id で、一つの節に algorithm が複数ある syntax-directed operation は `<id>/<k>` である。

model の値は JSON が運べる JavaScript の値（`Dom/Idl/Value.lean`）で、Symbol・BigInt・NaN・±∞ の値と、
getter や `toString`・`@@toPrimitive` を持つ利用者の object は無い。
-/

namespace Trace.Ecma

open Trace

def entries : List Entry := [
  /- ## §6.1.6.1.20 Number::toString -/
  { alg := "sec-numeric-types-number-tostring"
    impl := [``Dom.Idl.JsNumber.toJsString]
    omitted := [("1", .other "NaN は JSON の数に無い"),
                ("4", .other "+∞ は JSON の数に無い")]
    approx := [("5", "JSON の十進の値の末尾の 0 を落として n・k・s を読む。倍精度の値に丸まる最短の表記と一致するのは有効数字 15 桁以下で正規数の範囲の数だけなので、それ以外は model の対象外とする"),
               ("6", "radix は 10 だけ")] },

  /- ## §7.1.1 ToPrimitive -/
  { alg := "sec-toprimitive"
    impl := [``Dom.Idl.JsValue.toJsString, ``Dom.Idl.JsValue.toNumber]
    omitted := [("1.1-1.2", .other "@@toPrimitive を持つ object は表せない")]
    approx := [("1.3-1.4", "OrdinaryToPrimitive の結果（普通の object は \"[object Object]\"、配列は join）を ToString と ToNumber の中に書いてある")] },
  { alg := "sec-ordinarytoprimitive"
    impl := [``Dom.Idl.JsValue.toJsString, ``Dom.Idl.JsValue.toNumber]
    approx := [("*", "valueOf は自分を返すので、hint が number でも toString が使われる。普通の object の toString は \"[object Object]\"、配列の toString は join で、どちらも利用者のコードを呼ばない")] },

  /- ## §7.1.2 ToBoolean -/
  { alg := "sec-toboolean"
    impl := [``Dom.Idl.JsValue.toBoolean]
    omitted := [("3", .other "[[IsHTMLDDA]] を持つ object（document.all）は model に無い")]
    approx := [("2", "NaN と BigInt は表せない。数は倍精度の値に丸めてから 0 かを見る")] },

  /- ## §7.1.4 ToNumber -/
  { alg := "sec-tonumber"
    impl := [``Dom.Idl.JsValue.toNumber]
    omitted := [("2", .other "Symbol と BigInt は表せない")]
    approx := [("7-10", "object は普通の object と配列だけで、ToPrimitive の結果の文字列を StringToNumber で読む")] },
  { alg := "sec-stringtonumber"
    impl := [``Dom.Idl.stringToNumber, ``Dom.Idl.isStrWhiteSpace]
    approx := [("1-2", "ParseText の代わりに、StringNumericLiteral の文法を前後の空白・接頭辞・符号で場合分けして手で読む")] },
  { alg := "sec-runtime-semantics-stringnumericvalue/1"
    impl := [``Dom.Idl.stringToNumber] },
  { alg := "sec-runtime-semantics-stringnumericvalue/2"
    impl := [``Dom.Idl.stringToNumber] },
  { alg := "sec-runtime-semantics-stringnumericvalue/3"
    impl := [``Dom.Idl.stringToNumber.nonDecimal, ``Dom.Idl.readDigits, ``Dom.Idl.JsNum.ofRat] },
  { alg := "sec-runtime-semantics-stringnumericvalue/4"
    impl := [``Dom.Idl.stringToNumber.signed] },
  { alg := "sec-runtime-semantics-stringnumericvalue/5"
    impl := [``Dom.Idl.stringToNumber.signed] },
  { alg := "sec-runtime-semantics-stringnumericvalue/6"
    impl := [``Dom.Idl.readUnsignedDecimal, ``Dom.Idl.JsNum.ofDecimal?] },
  { alg := "sec-runtime-semantics-stringnumericvalue/7"
    impl := [``Dom.Idl.readUnsignedDecimal, ``Dom.Idl.JsNum.ofDecimal?] },
  { alg := "sec-runtime-semantics-stringnumericvalue/8"
    impl := [``Dom.Idl.readUnsignedDecimal, ``Dom.Idl.JsNum.ofDecimal?] },
  { alg := "sec-roundmvresult"
    -- 𝔽(n)（最も近い倍精度の値、偶数への丸め）は `JsNum.ofRat` と `JsNum.roundPos`。
    impl := [``Dom.Idl.JsNum.ofDecimal?, ``Dom.Idl.JsNum.ofDecimal, ``Dom.Idl.JsNum.ofRat, ``Dom.Idl.JsNum.roundPos]
    omitted := [("2-5", .other "有効数字が 20 桁を超える十進表記は、丸めが実装に任されて結果が一つに決まらないので、model の対象外とする")] },

  /- ## §7.1.19 ToString -/
  { alg := "sec-tostring"
    impl := [``Dom.Idl.JsValue.toJsString]
    omitted := [("2", .other "Symbol は表せない"),
                ("8", .other "BigInt は表せない")]
    approx := [("9-12", "object は普通の object と配列だけで、ToPrimitive の結果を直接書いてある")] },

  /- ## §23.1.3.18 Array.prototype.join -/
  { alg := "sec-array.prototype.join"
    impl := [``Dom.Idl.JsValue.joinElems, ``Dom.Idl.JsValue.joinElem]
    approx := [("1-4", "配列の ToString からだけ呼ぶので、this は配列で、separator は \",\" である")] }
]

def exclusions : List Exclusion := [
  { target := "sec-type-conversion", reason := .other "Web IDL の変換が呼ばない型変換（ToNumeric、整数への切り詰め、BigInt、ToObject、index ほか）" }
]

end Trace.Ecma
