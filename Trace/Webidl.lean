import Trace.Basic
import Dom

/-!
# Web IDL Standard の対応表

`docs/spec-version.md` に固定した `index.bs` の algorithm のうち、model が実装するものを載せる。
`ruby spec-trace/check.rb --spec webidl` が `spec-trace/webidl.json` と突き合わせる。

model が実装するのは、JavaScript の値から IDL の値への変換のうち model の操作の引数に要るもの（§3.2）と、
operation の関数が this を検査し、引数を変換し、method steps を呼ぶ順（§3.7.5）である。
変換の実装は `Dom/Idl/`、this の検査は `Dom/Exec/Invoke.lean`、例外を投げうる変換は
`Dom/Exec/Eval.lean` の `invokeChecked`、例外を投げない変換は scenario の読み取り（`Dom/Exec/Json.lean`）にある。
-/

namespace Trace.Webidl

open Trace

def entries : List Entry := [
  /- ## §3.2.3 boolean -/
  { alg := "js-to-boolean"
    impl := [``Dom.Idl.JsValue.toBoolean] },

  /- ## §3.2.4 整数型 -/
  { alg := "js-to-unsigned-short"
    impl := [``Dom.Idl.toUnsignedShort] },
  { alg := "js-to-unsigned-long"
    impl := [``Dom.Idl.toUnsignedLong] },
  { alg := "abstract-opdef-integerpart"
    impl := [``Dom.Idl.JsNum.truncAbs, ``Dom.Idl.convertToIntUnsigned]
    approx := [("*", "|n| の floor を `truncAbs` が、符号を `convertToIntUnsigned` が付ける")] },
  { alg := "abstract-opdef-converttoint"
    impl := [``Dom.Idl.convertToIntUnsigned, ``Dom.Idl.JsValue.toNumber, ``Dom.Idl.JsNumber.toNum?]
    omitted := [("1", .other "model が扱う整数型の引数は unsigned の 16・32 bit だけで、64 bit は無い"),
                ("3", .other "model が扱う整数型の引数に signed は無い"),
                ("6", .other "model が扱う引数に [EnforceRange] は付いていない"),
                ("7", .other "model が扱う引数に [Clamp] は付いていない"),
                ("11", .other "model が扱う整数型の引数に signed は無い")]
    approx := [("4", "ToNumber は scenario を読むときに行う（失敗も副作用も無い）。有効数字が 20 桁を超える十進表記は、ECMAScript が丸めを実装に任せるので受けない")] },

  /- ## §3.2.10 DOMString -/
  { alg := "js-to-DOMString"
    impl := [``Dom.Idl.toDOMString, ``Dom.Idl.toLegacyNullDOMString, ``Dom.Idl.JsValue.toJsString]
    approx := [("2", "ToString は scenario を読むときに行う（`Idl.toDOMString_error`：TypeError を投げない）。数は有効数字 15 桁以下に限り、object は toString を上書きしない普通の object と配列に限る")] },

  /- ## §3.2.15 interface 型 -/
  { alg := "js-to-interface"
    impl := [``Dom.Exec.Operation.argumentTypeError, ``Dom.Exec.idlCheck]
    approx := [("1", "scenario の JSON の数は node、`{\"attr\": id}` は Attr で、それ以外の値はどの interface も実装しない。this が method の interface を実装するかは node の kind で決める")] },

  /- ## §3.2.17 dictionary -/
  { alg := "js-to-dictionary"
    impl := [``Dom.Idl.toEventListenerOptions, ``Dom.Idl.toAddEventListenerOptions,
             ``Dom.Idl.toMutationObserverInit, ``Dom.Idl.toImportNodeOptions,
             ``Dom.Idl.boolMember, ``Dom.Idl.boolMember?]
    omitted := [("4.1.6", .other "model が扱う dictionary に required の member は無い")]
    approx := [("3", "dictionary ごとに、継承の根から member を辞書順に読む順を変換の関数に書いてある（継承は AddEventListenerOptions が EventListenerOptions を継承する一つだけ）"),
               ("4.1.3.1", "Get は自分のプロパティを引くだけで、getter や prototype の上の member は無い")] },

  /- ## §3.2.20 nullable 型 -/
  { alg := "js-to-nullable"
    impl := [``Dom.Idl.toNullableDOMString, ``Dom.Exec.Operation.nodeContainsNull,
             ``Dom.Exec.Operation.isEqualNodeNull]
    omitted := [("1", .other "model が扱う nullable 型に callback function は無い"),
                ("2", .other "model が扱う nullable 型に undefined を含む型は無い")] },

  /- ## §3.2.21 sequence -/
  { alg := "js-to-sequence"
    impl := [``Dom.Idl.toSequenceDOMString]
    approx := [("2-3", "@@iterator を持つのは配列だけとみなす。Set などの配列でない iterable は表せない")] },
  { alg := "algorithm:create sequence from iterable"
    impl := [``Dom.Idl.toSequenceDOMString]
    approx := [("*", "配列の要素を順に読む。iterator object を作らず、利用者の iterator は表せない")] },

  /- ## §3.2.25 union -/
  { alg := "js-to-union"
    impl := [``Dom.Idl.toEventListenerOptions, ``Dom.Idl.toAddEventListenerOptions,
             ``Dom.Idl.toImportNodeOptions, ``Dom.NodeOrString]
    omitted := [("1", .other "model が扱う union は undefined を含まない"),
                ("2", .other "model が扱う union は nullable 型を含まない"),
                ("5.2", .other "model が扱う union は object を含まない"),
                ("6-10", .other "model が扱う union は buffer source・DataView・typed array・callback function を含まない"),
                ("11.1-11.3", .other "model が扱う union は async sequence・sequence・frozen array を含まない"),
                ("11.5-11.7", .other "model が扱う union は record・callback interface・object を含まない"),
                ("13", .other "model が扱う union は numeric 型を含まない"),
                ("14", .other "model が扱う union は bigint を含まない"),
                ("16-17", .other "model が扱う union は numeric 型を含まない"),
                ("19", .other "model が扱う union は bigint を含まない"),
                ("20", .other "model が扱う union はどれも boolean か string 型を含むので、ここに来ない")]
    approx := [("5.1", "`(Node or DOMString)` の node は scenario の JSON の数（node の id）で表す")] },

  /- ## §3.7.5 operation の関数 -/
  { alg := "dfn-create-operation-function"
    impl := [``Dom.Exec.invokeOperation, ``Dom.Exec.idlCheck, ``Dom.Exec.invokeChecked,
             ``Dom.Exec.returnValueOf]
    omitted := [("1", .other "関数 object を作らない。操作は scenario の op 名で呼ぶ"),
                ("2.1.2.1-2.1.2.2", .host),
                ("2.1.7", .other "[Default] の付いた operation（toJSON）を扱わない"),
                ("2.2", .other "promise を返す operation を扱わない"),
                ("3-6", .other "関数 object を作らない")]
    approx := [("2.1.3-2.1.5", "overload の選択と引数の個数の検査は無い。引数の変換は操作ごとに、例外を投げないものは scenario の読み取りで、投げうるものは `idlCheck` と `invokeChecked` で行う"),
               ("2.1.9", "戻り値は `ReturnValue` として JSON に書き、JavaScript の値には変換しない")] }
]

def exclusions : List Exclusion := [
  { target := "idl", reason := .other "IDL の構文と型の定義（§2）。model は IDL fragment を読まず、変換を member ごとに書く" },
  { target := "js-type-mapping", reason := .other "model の操作の引数に無い型からの変換と、IDL の値から JavaScript の値への変換（戻り値は `ReturnValue` として JSON で比べる）" },
  { target := "js-extended-attributes", reason := .other "model が扱う member に付く拡張属性（[CEReactions] ほか）は観測に効かない。[LegacyNullToEmptyString] は DOMString の変換の step 1 で扱う" },
  { target := "js-interfaces", reason := .host },
  { target := "js-platform-objects", reason := .host },
  { target := "js-legacy-platform-objects", reason := .host },
  { target := "js-observable-arrays", reason := .other "model が扱う member に observable array は無い" },
  { target := "js-user-objects", reason := .other "callback と利用者の object の呼び出しは model の外（listener の callback は `ListenerAction` で表す）" },
  { target := "js-invoking-callback-functions", reason := .other "callback function は model の外" },
  { target := "js-namespaces", reason := .other "model が扱う member に namespace は無い" },
  { target := "js-exceptions", reason := .other "例外は object を作らず、名前（`IdlException.name`）で比べる" },
  { target := "dfn-overload-resolution-algorithm", reason := .todo "overload の選択と、引数の個数が足りないときの TypeError" }
]

end Trace.Webidl
