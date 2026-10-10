# 仕様の step との対応（自動生成）

このファイルは `ruby spec-trace/check.rb --spec webidl --write` が `Trace/` の対応表と `spec-trace/webidl.json` から作る。手で編集しない。

対象は Web IDL Standard の `index.bs` commit `8c65329114411ebd3af025106c2267f5bc00faeb` である。algorithm の鍵は描画された仕様の anchor で、各行はその commit の snapshot に張ってある。

| 項目 | 数 |
| --- | --- |
| `index.bs` の algorithm | 191 |
| 表に載せたもの | 14 |
| 対象外としたもの | 177 |
| 表に載せた algorithm の step | 213 |
| そのうち実装したもの | 71 |
| そのうち近似したもの | 40 |
| そのうち外したもの | 102 |

step の数は入れ子の step も一つと数える。step を持たない一文の algorithm は一つと数える。
「関係」の列は、仕様本文から独立に書いた関係（`Dom/Spec/` ほか）である。

## 表に載せた algorithm

### §3.2.3（`js-boolean`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [js-to-boolean](https://webidl.spec.whatwg.org/commit-snapshots/8c65329114411ebd3af025106c2267f5bc00faeb/#js-to-boolean) | 2/2 | `Dom.Idl.JsValue.toBoolean` |  |

### §3.2.4.4（`js-unsigned-short`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [js-to-unsigned-short](https://webidl.spec.whatwg.org/commit-snapshots/8c65329114411ebd3af025106c2267f5bc00faeb/#js-to-unsigned-short) | 2/2 | `Dom.Idl.toUnsignedShort` |  |

### §3.2.4.6（`js-unsigned-long`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [js-to-unsigned-long](https://webidl.spec.whatwg.org/commit-snapshots/8c65329114411ebd3af025106c2267f5bc00faeb/#js-to-unsigned-long) | 2/2 | `Dom.Idl.toUnsignedLong` |  |

### §3.2.4.9（`js-integer-types-abstract-ops`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [abstract-opdef-integerpart](https://webidl.spec.whatwg.org/commit-snapshots/8c65329114411ebd3af025106c2267f5bc00faeb/#abstract-opdef-integerpart) | 0/3（近似 3） | `Dom.Idl.JsNum.truncAbs`<br>`Dom.Idl.convertToIntUnsigned` |  |
| [abstract-opdef-converttoint](https://webidl.spec.whatwg.org/commit-snapshots/8c65329114411ebd3af025106c2267f5bc00faeb/#abstract-opdef-converttoint) | 8/26（近似 1） | `Dom.Idl.convertToIntUnsigned`<br>`Dom.Idl.JsValue.toNumber`<br>`Dom.Idl.JsNumber.toNum?` |  |

### §3.2.10（`js-DOMString`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [js-to-DOMString](https://webidl.spec.whatwg.org/commit-snapshots/8c65329114411ebd3af025106c2267f5bc00faeb/#js-to-DOMString) | 2/3（近似 1） | `Dom.Idl.toDOMString`<br>`Dom.Idl.toLegacyNullDOMString`<br>`Dom.Idl.JsValue.toJsString` |  |

### §3.2.15（`js-interface`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [js-to-interface](https://webidl.spec.whatwg.org/commit-snapshots/8c65329114411ebd3af025106c2267f5bc00faeb/#js-to-interface) | 1/2（近似 1） | `Dom.Exec.Operation.argumentTypeError`<br>`Dom.Exec.idlCheck` |  |

### §3.2.17（`js-dictionary`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [js-to-dictionary](https://webidl.spec.whatwg.org/commit-snapshots/8c65329114411ebd3af025106c2267f5bc00faeb/#js-to-dictionary) | 15/18（近似 2） | `Dom.Idl.toEventListenerOptions`<br>`Dom.Idl.toAddEventListenerOptions`<br>`Dom.Idl.toMutationObserverInit`<br>`Dom.Idl.toImportNodeOptions`<br>`Dom.Idl.boolMember`<br>`Dom.Idl.boolMember?` |  |

### §3.2.20（`js-nullable-type`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [js-to-nullable](https://webidl.spec.whatwg.org/commit-snapshots/8c65329114411ebd3af025106c2267f5bc00faeb/#js-to-nullable) | 2/4 | `Dom.Idl.toNullableDOMString`<br>`Dom.Exec.Operation.nodeContainsNull`<br>`Dom.Exec.Operation.isEqualNodeNull` |  |

### §3.2.21（`js-sequence`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [js-to-sequence](https://webidl.spec.whatwg.org/commit-snapshots/8c65329114411ebd3af025106c2267f5bc00faeb/#js-to-sequence) | 2/4（近似 2） | `Dom.Idl.toSequenceDOMString` |  |

### §3.2.21.1（`create-sequence-from-iterable`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [algorithm:create sequence from iterable](https://webidl.spec.whatwg.org/commit-snapshots/8c65329114411ebd3af025106c2267f5bc00faeb/#algorithm:create sequence from iterable) | 0/7（近似 7） | `Dom.Idl.toSequenceDOMString` |  |

### §3.2.25（`js-union`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [js-to-union](https://webidl.spec.whatwg.org/commit-snapshots/8c65329114411ebd3af025106c2267f5bc00faeb/#js-to-union) | 10/52（近似 1） | `Dom.Idl.toEventListenerOptions`<br>`Dom.Idl.toAddEventListenerOptions`<br>`Dom.Idl.toImportNodeOptions`<br>`Dom.NodeOrString` |  |

### §3.6（`js-overloads`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [dfn-overload-resolution-algorithm](https://webidl.spec.whatwg.org/commit-snapshots/8c65329114411ebd3af025106c2267f5bc00faeb/#dfn-overload-resolution-algorithm) | 16/64（近似 18） | `Dom.Exec.requiredArgs`<br>`Dom.Exec.Operation.argumentTypeError` |  |

### §3.7.7（`js-operations`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [dfn-create-operation-function](https://webidl.spec.whatwg.org/commit-snapshots/8c65329114411ebd3af025106c2267f5bc00faeb/#dfn-create-operation-function) | 9/24（近似 4） | `Dom.Exec.invokeOperation`<br>`Dom.Exec.idlCheck`<br>`Dom.Exec.invokeChecked`<br>`Dom.Exec.returnValueOf` |  |

## 外した step

| algorithm | step | 理由 |
| --- | --- | --- |
| abstract-opdef-converttoint | 1 | other：model が扱う整数型の引数は unsigned の 16・32 bit だけで、64 bit は無い |
| abstract-opdef-converttoint | 3 | other：model が扱う整数型の引数に signed は無い |
| abstract-opdef-converttoint | 6 | other：model が扱う引数に [EnforceRange] は付いていない |
| abstract-opdef-converttoint | 7 | other：model が扱う引数に [Clamp] は付いていない |
| abstract-opdef-converttoint | 11 | other：model が扱う整数型の引数に signed は無い |
| js-to-dictionary | 4.1.6 | other：model が扱う dictionary に required の member は無い |
| js-to-nullable | 1 | other：model が扱う nullable 型に callback function は無い |
| js-to-nullable | 2 | other：model が扱う nullable 型に undefined を含む型は無い |
| js-to-union | 1 | other：model が扱う union は undefined を含まない |
| js-to-union | 2 | other：model が扱う union は nullable 型を含まない |
| js-to-union | 5.2 | other：model が扱う union は object を含まない |
| js-to-union | 6-10 | other：model が扱う union は buffer source・DataView・typed array・callback function を含まない |
| js-to-union | 11.1-11.3 | other：model が扱う union は async sequence・sequence・frozen array を含まない |
| js-to-union | 11.5-11.7 | other：model が扱う union は record・callback interface・object を含まない |
| js-to-union | 13 | other：model が扱う union は numeric 型を含まない |
| js-to-union | 14 | other：model が扱う union は bigint を含まない |
| js-to-union | 16-17 | other：model が扱う union は numeric 型を含まない |
| js-to-union | 19 | other：model が扱う union は bigint を含まない |
| js-to-union | 20 | other：model が扱う union はどれも boolean か string 型を含むので、ここに来ない |
| dfn-overload-resolution-algorithm | 12 | other：model が扱う method に、distinguishing argument index で選ぶ overload は無い |
| dfn-overload-resolution-algorithm | 14 | other：model が扱う method に、distinguishing argument index で選ぶ overload は無い |
| dfn-create-operation-function | 1 | other：関数 object を作らない。操作は scenario の op 名で呼ぶ |
| dfn-create-operation-function | 2.1.2.1-2.1.2.2 | host |
| dfn-create-operation-function | 2.1.7 | other：[Default] の付いた operation（toJSON）を扱わない |
| dfn-create-operation-function | 2.2 | other：promise を返す operation を扱わない |
| dfn-create-operation-function | 3-6 | other：関数 object を作らない |

## 近似した step

| algorithm | step | 仕様との違い |
| --- | --- | --- |
| abstract-opdef-integerpart | * | |n| の floor を `truncAbs` が、符号を `convertToIntUnsigned` が付ける |
| abstract-opdef-converttoint | 4 | ToNumber は scenario を読むときに行う（失敗も副作用も無い）。有効数字が 20 桁を超える十進表記は、ECMAScript が丸めを実装に任せるので受けない |
| js-to-DOMString | 2 | ToString は scenario を読むときに行う（`Idl.toDOMString_error`：TypeError を投げない）。数は有効数字 15 桁以下に限り、object は toString を上書きしない普通の object と配列に限る |
| js-to-interface | 1 | scenario の JSON の数は node、`{"attr": id}` は Attr で、それ以外の値はどの interface も実装しない。this が method の interface を実装するかは node の kind で決める |
| js-to-dictionary | 3 | dictionary ごとに、継承の根から member を辞書順に読む順を変換の関数に書いてある（継承は AddEventListenerOptions が EventListenerOptions を継承する一つだけ） |
| js-to-dictionary | 4.1.3.1 | Get は自分のプロパティを引くだけで、getter や prototype の上の member は無い |
| js-to-sequence | 2-3 | @@iterator を持つのは配列だけとみなす。Set などの配列でない iterable は表せない |
| algorithm:create sequence from iterable | * | 配列の要素を順に読む。iterator object を作らず、利用者の iterator は表せない |
| js-to-union | 5.1 | `(Node or DOMString)` の node は scenario の JSON の数（node の id）で表す |
| dfn-overload-resolution-algorithm | 1-5 | effective overload set は、省略できる引数の数だけ長さが違う一つの operation の entry なので、渡した引数の個数（scenario の `argc`）が必須の個数（`requiredArgs`）より少なければ TypeError とする |
| dfn-overload-resolution-algorithm | 15-16 | 引数の変換は op ごとに書く。渡さなかった optional の引数は field を書かないことで表し、既定値を使う |
| dfn-create-operation-function | 2.1.3-2.1.5 | effective overload set は op ごとの必須の引数の個数（`requiredArgs`）で表す。引数の変換は操作ごとに、例外を投げないものは scenario の読み取りで、投げうるものは `idlCheck` と `invokeChecked` で行う |
| dfn-create-operation-function | 2.1.9 | 戻り値は `ReturnValue` として JSON に書き、JavaScript の値には変換しない |

## 対象外とした algorithm

| 理由 | algorithm |
| --- | --- |
| host | LegacyPlatformObjectGetOwnProperty, algorithm:to invoke the [[DefineOwnProperty]] internal method of legacy platform objects, algorithm:to invoke the [[DefineOwnProperty]] internal method of named properties object, algorithm:to invoke the [[Delete]] internal method of legacy platform objects, algorithm:to invoke the [[Delete]] internal method of named properties object, algorithm:to invoke the [[GetOwnProperty]] internal method of legacy platform objects, algorithm:to invoke the [[PreventExtensions]] internal method of named properties object, algorithm:to invoke the [[SetPrototypeOf]] internal method of a named properties object, algorithm:to invoke the [[Set]] internal method of legacy platform objects, algorithm:to invoke the add method of Sets, algorithm:to invoke the clear method of Maps, algorithm:to invoke the clear method of Sets, algorithm:to invoke the delete method of Maps, algorithm:to invoke the delete method of Sets, algorithm:to invoke the entries method of Maps, algorithm:to invoke the entries method of Sets, algorithm:to invoke the forEach method of Maps, algorithm:to invoke the forEach method of Sets, algorithm:to invoke the get method of Maps, algorithm:to invoke the has method of Maps, algorithm:to invoke the has method of Sets, algorithm:to invoke the internal [[GetOwnProperty]] method of named properties object, algorithm:to invoke the internal [[OwnPropertyKeys]] method of legacy platform objects, algorithm:to invoke the internal [[PreventExtensions]] method of legacy platform objects, algorithm:to invoke the internal [[SetPrototypeOf]] method of a platform object that implements an interface with [Global] extended attribute, algorithm:to invoke the keys method of Maps, algorithm:to invoke the next property of asynchronous iterators, algorithm:to invoke the next property of iterators, algorithm:to invoke the return property of asynchronous iterators, algorithm:to invoke the set method of Maps, algorithm:to invoke the size method of Maps, algorithm:to invoke the size method of Sets, algorithm:to invoke the toString method of interfaces, algorithm:to invoke the values method of Maps, algorithm:to invoke the values method of Sets, collect-attribute-values, collect-attribute-values-of-an-inheritance-stack, converting-arguments-for-an-asynchronous-iterator-method, create-a-legacy-factory-function, create-a-map-iterator, create-a-named-properties-object, create-a-set-iterator, create-an-inheritance-stack, create-an-interface-object, create-an-interface-prototype-object, default-tojson-steps, define-the-asynchronous-iteration-methods, define-the-attributes, define-the-constants, define-the-global-property-references, define-the-iteration-methods, define-the-operations, define-the-regular-attributes, define-the-regular-operations, define-the-static-attributes, define-the-static-operations, define-the-unforgeable-regular-attributes, define-the-unforgeable-regular-operations, dfn-attribute-getter, dfn-attribute-setter, dfn-named-property-visibility, dfn-primary-interface, implementation-check-an-object, implements, internally-create-a-new-object-implementing-the-interface, invoke-indexed-setter, invoke-named-setter, is-a-platform-object, is-an-array-index, iterator-result, new |
| other：IDL の構文と型の定義（§2）。model は IDL fragment を読まず、変換を member ごとに書く | algorithm:QuotaExceededError deserialization steps, algorithm:QuotaExceededError serialization steps, algorithm:execute supports() with optional argument, algorithm:execute supports() with overloads, algorithm:value of integer tokens, compute-the-effective-overload-set, decimal-token-value, dfn-flattened-union-member-types, dfn-number-of-nullable-member-types, idl-type-extended-attribute-associated-with, interface-inclusive-inherited-interfaces, qualified-name, quotaexceedederror-quotaexceedederror-message-options, string-literal |
| other：callback function は model の外 | construct-a-callback-function, invoke-a-callback-function |
| other：callback と利用者の object の呼び出しは model の外（listener の callback は `ListenerAction` で表す） | call-a-user-objects-operation, create-a-legacy-callback-interface-object, web-idl-arguments-list-converting |
| other：model が扱う member に namespace は無い | create-a-namespace-object |
| other：model が扱う member に observable array は無い | algorithm:observable array exotic object defineProperty trap, algorithm:observable array exotic object deleteProperty trap, algorithm:observable array exotic object get trap, algorithm:observable array exotic object getOwnPropertyDescriptor trap, algorithm:observable array exotic object has trap, algorithm:observable array exotic object ownKeys trap, algorithm:observable array exotic object preventExtensions trap, algorithm:observable array exotic object set trap, creating-an-observable-array-exotic-object, observable-array-exotic-object-set-the-indexed-value, observable-array-exotic-object-set-the-length |
| other：model が扱う member に付く拡張属性（[CEReactions] ほか）は観測に効かない。[LegacyNullToEmptyString] は DOMString の変換の step 1 で扱う | dfn-conditionally-exposed, dfn-exposed, dfn-exposure-set, exposure-set-intersection |
| other：model の操作の引数に無い型からの変換と、IDL の値から JavaScript の値への変換（戻り値は `ReturnValue` として JSON で比べる） | USVString-to-js, a-new-promise, a-promise-rejected-with, a-promise-resolved-with, algorithm:convert a JavaScript value to IDL DataView, algorithm:convert a JavaScript value to IDL SharedArrayBuffer, algorithm:convert a JavaScript value to IDL typed array, algorithm:convert a JavaScript value to frozen array, algorithm:create frozen array from iterable, algorithm:observable array backing list, arraybuffer-create, arraybuffer-transfer, arraybuffer-write, arraybufferview-create, arraybufferview-write, async-iterator-close, async-iterator-get-next-value, async-sequence-open, async-sequence-to-js, bigint-to-js, buffer-source-to-js, buffersource-byte-length, buffersource-detached, buffersource-transferable, buffersource-underlying-buffer, dfn-create-frozen-array, dfn-detach, dfn-get-buffer-source-copy, dfn-perform-steps-once-promise-is-settled, dictionary-to-js, js-to-ByteString, js-to-USVString, js-to-any, js-to-async-iterable, js-to-bigint, js-to-bigint-or-numeric, js-to-buffer-source, js-to-byte, js-to-callback-function, js-to-callback-interface, js-to-double, js-to-enumeration, js-to-float, js-to-long, js-to-long-long, js-to-object, js-to-octet, js-to-promise, js-to-record, js-to-short, js-to-symbol, js-to-unrestricted-double, js-to-unrestricted-float, js-to-unsigned-long-long, mark-a-promise-as-handled, nullable-to-js, record-to-js, reject, resolve, sequence-to-js, sharedarraybuffer-create, unrestricted-double-to-js, unrestricted-float-to-js, upon-fulfillment, upon-rejection, wait-for-all, waiting-for-all-promise |
| other：例外は object を作らず、名前（`IdlException.name`）で比べる | algorithm:throw an exception, algorithm:to create a DOMException, algorithm:to create a DOMException derived interface, algorithm:to create a simple exception |
