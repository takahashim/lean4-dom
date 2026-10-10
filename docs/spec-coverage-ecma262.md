# 仕様の step との対応（自動生成）

このファイルは `ruby spec-trace/check.rb --spec ecma262 --write` が `Trace/` の対応表と `spec-trace/ecma262.json` から作る。手で編集しない。

対象は ECMA-262 の `spec.html` commit `5345883164f463e87f8b40aca4956157ecba8783` である。algorithm の鍵は節の id（一つの節に algorithm が複数あれば `<id>/<k>`）で、各行はその commit の source の行に張ってある。

| 項目 | 数 |
| --- | --- |
| `spec.html` の algorithm | 40 |
| 表に載せたもの | 17 |
| 対象外としたもの | 23 |
| 表に載せた algorithm の step | 119 |
| そのうち実装したもの | 61 |
| そのうち近似したもの | 35 |
| そのうち外したもの | 23 |

step の数は入れ子の step も一つと数える。step を持たない一文の algorithm は一つと数える。
「関係」の列は、仕様本文から独立に書いた関係（`Dom/Spec/` ほか）である。

## 表に載せた algorithm

### §6.1.6.1.20（`sec-numeric-types-number-tostring`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [sec-numeric-types-number-tostring](https://github.com/tc39/ecma262/blob/5345883164f463e87f8b40aca4956157ecba8783/spec.html#L2419) | 11/21（近似 8） | `Dom.Idl.JsNumber.toJsString` |  |

### §7.1.1（`sec-toprimitive`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [sec-toprimitive](https://github.com/tc39/ecma262/blob/5345883164f463e87f8b40aca4956157ecba8783/spec.html#L5083) | 2/16（近似 2） | `Dom.Idl.JsValue.toJsString`<br>`Dom.Idl.JsValue.toNumber` |  |

### §7.1.1.1（`sec-ordinarytoprimitive`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [sec-ordinarytoprimitive](https://github.com/tc39/ecma262/blob/5345883164f463e87f8b40aca4956157ecba8783/spec.html#L5114) | 0/10（近似 10） | `Dom.Idl.JsValue.toJsString`<br>`Dom.Idl.JsValue.toNumber` |  |

### §7.1.2（`sec-toboolean`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [sec-toboolean](https://github.com/tc39/ecma262/blob/5345883164f463e87f8b40aca4956157ecba8783/spec.html#L5139) | 2/5（近似 1） | `Dom.Idl.JsValue.toBoolean` |  |

### §7.1.4（`sec-tonumber`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [sec-tonumber](https://github.com/tc39/ecma262/blob/5345883164f463e87f8b40aca4956157ecba8783/spec.html#L5175) | 5/10（近似 4） | `Dom.Idl.JsValue.toNumber` |  |

### §7.1.4.1.1（`sec-stringtonumber`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [sec-stringtonumber](https://github.com/tc39/ecma262/blob/5345883164f463e87f8b40aca4956157ecba8783/spec.html#L5255) | 1/3（近似 2） | `Dom.Idl.stringToNumber`<br>`Dom.Idl.isStrWhiteSpace` |  |

### §7.1.4.1.2（`sec-runtime-semantics-stringnumericvalue`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [sec-runtime-semantics-stringnumericvalue/1](https://github.com/tc39/ecma262/blob/5345883164f463e87f8b40aca4956157ecba8783/spec.html#L5270) | 1/1 | `Dom.Idl.stringToNumber` |  |
| [sec-runtime-semantics-stringnumericvalue/2](https://github.com/tc39/ecma262/blob/5345883164f463e87f8b40aca4956157ecba8783/spec.html#L5274) | 1/1 | `Dom.Idl.stringToNumber` |  |
| [sec-runtime-semantics-stringnumericvalue/3](https://github.com/tc39/ecma262/blob/5345883164f463e87f8b40aca4956157ecba8783/spec.html#L5278) | 1/1 | `Dom.Idl.stringToNumber.nonDecimal`<br>`Dom.Idl.readDigits`<br>`Dom.Idl.JsNum.ofRat` |  |
| [sec-runtime-semantics-stringnumericvalue/4](https://github.com/tc39/ecma262/blob/5345883164f463e87f8b40aca4956157ecba8783/spec.html#L5282) | 3/3 | `Dom.Idl.stringToNumber.signed` |  |
| [sec-runtime-semantics-stringnumericvalue/5](https://github.com/tc39/ecma262/blob/5345883164f463e87f8b40aca4956157ecba8783/spec.html#L5288) | 1/1 | `Dom.Idl.stringToNumber.signed` |  |
| [sec-runtime-semantics-stringnumericvalue/6](https://github.com/tc39/ecma262/blob/5345883164f463e87f8b40aca4956157ecba8783/spec.html#L5292) | 9/9 | `Dom.Idl.readUnsignedDecimal`<br>`Dom.Idl.JsNum.ofDecimal?` |  |
| [sec-runtime-semantics-stringnumericvalue/7](https://github.com/tc39/ecma262/blob/5345883164f463e87f8b40aca4956157ecba8783/spec.html#L5304) | 4/4 | `Dom.Idl.readUnsignedDecimal`<br>`Dom.Idl.JsNum.ofDecimal?` |  |
| [sec-runtime-semantics-stringnumericvalue/8](https://github.com/tc39/ecma262/blob/5345883164f463e87f8b40aca4956157ecba8783/spec.html#L5311) | 3/3 | `Dom.Idl.readUnsignedDecimal`<br>`Dom.Idl.JsNum.ofDecimal?` |  |

### §7.1.4.1.3（`sec-roundmvresult`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [sec-roundmvresult](https://github.com/tc39/ecma262/blob/5345883164f463e87f8b40aca4956157ecba8783/spec.html#L5328) | 1/5 | `Dom.Idl.JsNum.ofDecimal?`<br>`Dom.Idl.JsNum.ofDecimal`<br>`Dom.Idl.JsNum.ofRat`<br>`Dom.Idl.JsNum.roundPos` |  |

### §7.1.19（`sec-tostring`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [sec-tostring](https://github.com/tc39/ecma262/blob/5345883164f463e87f8b40aca4956157ecba8783/spec.html#L5708) | 6/12（近似 4） | `Dom.Idl.JsValue.toJsString` |  |

### §23.1.3.18（`sec-array.prototype.join`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [sec-array.prototype.join](https://github.com/tc39/ecma262/blob/5345883164f463e87f8b40aca4956157ecba8783/spec.html#L41203) | 10/14（近似 4） | `Dom.Idl.JsValue.joinElems`<br>`Dom.Idl.JsValue.joinElem` |  |

## 外した step

| algorithm | step | 理由 |
| --- | --- | --- |
| sec-numeric-types-number-tostring | 1 | other：NaN は JSON の数に無い |
| sec-numeric-types-number-tostring | 4 | other：+∞ は JSON の数に無い |
| sec-toprimitive | 1.1-1.2 | other：@@toPrimitive を持つ object は表せない |
| sec-toboolean | 3 | other：[[IsHTMLDDA]] を持つ object（document.all）は model に無い |
| sec-tonumber | 2 | other：Symbol と BigInt は表せない |
| sec-roundmvresult | 2-5 | other：有効数字が 20 桁を超える十進表記は、丸めが実装に任されて結果が一つに決まらないので、model の対象外とする |
| sec-tostring | 2 | other：Symbol は表せない |
| sec-tostring | 8 | other：BigInt は表せない |

## 近似した step

| algorithm | step | 仕様との違い |
| --- | --- | --- |
| sec-numeric-types-number-tostring | 5 | JSON の十進の値の末尾の 0 を落として n・k・s を読む。倍精度の値に丸まる最短の表記と一致するのは有効数字 15 桁以下で正規数の範囲の数だけなので、それ以外は model の対象外とする |
| sec-numeric-types-number-tostring | 6 | radix は 10 だけ |
| sec-toprimitive | 1.3-1.4 | OrdinaryToPrimitive の結果（普通の object は "[object Object]"、配列は join）を ToString と ToNumber の中に書いてある |
| sec-ordinarytoprimitive | * | valueOf は自分を返すので、hint が number でも toString が使われる。普通の object の toString は "[object Object]"、配列の toString は join で、どちらも利用者のコードを呼ばない |
| sec-toboolean | 2 | NaN と BigInt は表せない。数は倍精度の値に丸めてから 0 かを見る |
| sec-tonumber | 7-10 | object は普通の object と配列だけで、ToPrimitive の結果の文字列を StringToNumber で読む |
| sec-stringtonumber | 1-2 | ParseText の代わりに、StringNumericLiteral の文法を前後の空白・接頭辞・符号で場合分けして手で読む |
| sec-tostring | 9-12 | object は普通の object と配列だけで、ToPrimitive の結果を直接書いてある |
| sec-array.prototype.join | 1-4 | 配列の ToString からだけ呼ぶので、this は配列で、separator は "," である |

## 対象外とした algorithm

| 理由 | algorithm |
| --- | --- |
| other：Web IDL の変換が呼ばない型変換（ToNumeric、整数への切り詰め、BigInt、ToObject、index ほか） | sec-canonicalnumericindexstring, sec-snaptointeger, sec-stringtobigint, sec-toabsoluteindex, sec-tobigint/1, sec-tobigint/2, sec-tobigint64, sec-tobiguint64, sec-toclampedindex, sec-tofixedsizeinteger, sec-toindex, sec-toint16, sec-toint32, sec-toint8, sec-tointegerorinfinity, sec-tolength, sec-tonumeric, sec-toobject, sec-topropertykey, sec-touint16, sec-touint32, sec-touint8, sec-touint8clamp |
