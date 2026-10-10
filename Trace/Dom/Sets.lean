import Trace.Basic
import Dom

/-!
# §7 Sets（`DOMTokenList`）・§8 XPath

model の `DOMTokenList` は `Element.classList`（associated attribute は `class`）だけである。
token set を状態に持たず、method のたびに `class` attribute の値を ordered set parser で読み直す
（`Dom.classTokenSet`）。
-/

namespace Trace.Dom.Sets

open Trace

private def classOnly : String :=
  "DOMTokenList は classList だけで、element と attribute name は（受け手の element, \"class\"）に固定"

def entries : List Entry := [
  { alg := "concept-dtl-update"
    impl := [``Dom.tokenListUpdate, ``Dom.getAttributeByKey, ``Dom.setAttributeValue]
    approx := [("*", classOnly)] },
  { alg := "concept-dtl-serialize"
    impl := [``Dom.getAttributeValue]
    approx := [("*", classOnly ++ "。value の getter が無いので、serialize steps を直接呼ぶ所は無い")] },
  { alg := "algorithm:DOMTokenList/attribute change steps"
    impl := [``Dom.classTokenSet, ``Dom.orderedSetParse]
    approx := [("*", "token set を状態に持たない。attribute change steps で更新する代わりに、使うたびに attribute の値から読み直す（値が無ければ空文字列なので空の set になる）")] },
  { alg := "algorithm:DOMTokenList/created"
    impl := [``Dom.classTokenSet]
    approx := [("*", "DOMTokenList object を作らない。token set は使うたびに attribute の値から読み直す")] },
  { alg := "dom-domtokenlist-contains"
    impl := [``Dom.classListContains, ``Dom.classTokenSet] },
  { alg := "dom-domtokenlist-add"
    impl := [``Dom.classListAdd, ``Dom.validateTokens, ``Dom.validateToken,
             ``Dom.orderedSetAppend, ``Dom.tokenListUpdate] },
  { alg := "dom-domtokenlist-remove"
    impl := [``Dom.classListRemove, ``Dom.validateTokens, ``Dom.validateToken,
             ``Dom.tokenListUpdate] },
  { alg := "dom-domtokenlist-toggle"
    impl := [``Dom.classListToggle, ``Dom.validateToken, ``Dom.tokenListUpdate] },
  { alg := "dom-domtokenlist-replace"
    impl := [``Dom.classListReplace, ``Dom.orderedSetReplace, ``Dom.tokenListUpdate] }
]

def exclusions : List Exclusion := [
  { target := "concept-domtokenlist-validation",
    reason := .todo "validation steps（supported tokens）が無い。classList の class は supported tokens を定めないので TypeError になるはずの所" },
  { target := "dom-domtokenlist-supports",
    reason := .todo "supports() が無い（validation steps が未実装）" },
  { target := "dom-domtokenlist-length",
    reason := .todo "length の getter が無い（token set は classTokenSet で読めるが API が無い）" },
  { target := "dom-domtokenlist-item",
    reason := .todo "item() が無い" },
  { target := "dom-domtokenlist-value",
    reason := .todo "value の getter が無い（値は className の reflect getter と同じだが、DOMTokenList 側の API は無い）" },
  { target := "dom-domtokenlist-value/setter",
    reason := .todo "value の setter が無い（className の reflect setter と同じ効果だが、DOMTokenList 側の API は無い）" },
  { target := "xpath",
    reason := .other "XPath（§8）は model の対象外。XPath の評価器を持たない" }
]

end Trace.Dom.Sets
