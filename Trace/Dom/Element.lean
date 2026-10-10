import Trace.Basic
import Dom

/-!
# §4.9 Interface `Element`（§4.9.1 `NamedNodeMap`、§4.9.2 `Attr`）

model の attribute は element の状態（`NodeData.attributes`）で、同一性は `AttrId` で持つ。
どの element にも付いていない `Attr` は `DOMState.detachedAttrs` にいる。
`NamedNodeMap` object は持たず、`removeNamedItem` だけが専用の関数を持つ。
-/

namespace Trace.Dom.Element

open Trace

private def noTT : Reason := .other "Trusted Types（get trusted type compliant attribute value）は対象外"

def entries : List Entry := [
  -- 名前と element の生成
  { alg := "element-html-uppercased-qualified-name"
    impl := [``Dom.tagName, ``Dom.isHTMLDocumentOf, ``Dom.NodeData.qualifiedName] },
  { alg := "concept-create-element"
    impl := [``Dom.createElement, ``Dom.createElementNS, ``Dom.withFresh]
    omitted := [("2-5", .customElements), ("6.3", .customElements)]
    approx := [("6.1", "element interface を持たない。interface は namespace と local name から決まるものとして扱う")] },
  { alg := "create-an-element-internal"
    impl := [``Dom.withFresh]
    approx := [("1", "interface を持たない。node kind が element の `NodeData` を作る"),
               ("2", "custom element registry・custom element state・is value は持たない（custom element は対象外）。namespace・prefix・local name・node document だけを置く")] },
  -- attribute list の変更
  { alg := "handle-attribute-changes"
    impl := [``Dom.handleAttributeChanges]
    spec := [``Dom.Spec.AttributeChangeHandled, ``Dom.Spec.AttributeRecordQueued]
    omitted := [("2", .customElements), ("3", .hook)] },
  { alg := "concept-element-attributes-change"
    impl := [``Dom.changeAttribute]
    spec := [``Dom.Spec.AttributeChanged]
    approx := [("2", "attribute は element の状態なので、attribute list の中の同じ鍵の要素を差し替える")] },
  { alg := "concept-element-attributes-append"
    impl := [``Dom.appendAttribute]
    spec := [``Dom.Spec.AttributeAppended]
    approx := [("2", "attribute の element は持たず、attribute list に入っていることで表す")] },
  { alg := "concept-element-attributes-remove"
    impl := [``Dom.detachAttribute, ``Dom.removeAttributeFrom]
    spec := [``Dom.Spec.AttributeDetached, ``Dom.Spec.AttributeRemoved]
    approx := [("3", "element を null にした `Attr` は detachedAttrs に足して表す。ただし名前で消す経路（removeAttributeFrom：removeAttribute・removeAttributeNS・toggleAttribute・reflect の boolean setter・dataset の deleter）は `Attr` を捨てる")] },
  { alg := "concept-element-attributes-replace"
    impl := [``Dom.replaceAttributeWith]
    spec := [``Dom.Spec.AttributeReplacedWith]
    approx := [("3", "newAttribute の element は attribute list に入っていることで表す"),
               ("5", "oldAttribute の element を null にすることを、detachedAttrs の末尾に足して表す")] },
  -- attribute の探索
  { alg := "concept-element-attributes-get-by-name"
    impl := [``Dom.getAttributeByName, ``Dom.attrNameFor]
    spec := [``Dom.Spec.AttrByName, ``Dom.Spec.AttrNameNormalized] },
  { alg := "concept-element-attributes-get-by-namespace"
    impl := [``Dom.getAttributeByKey, ``Dom.normalizeNamespace]
    spec := [``Dom.Spec.AttrByKey] },
  { alg := "concept-element-attributes-get-value"
    impl := [``Dom.getAttributeValue] },
  -- attribute の設定と削除
  { alg := "concept-element-attributes-set"
    impl := [``Dom.setAttributeNode, ``Dom.findAttr, ``Dom.removeDetached]
    spec := [``Dom.Spec.SetAttributeNodeResult]
    omitted := [("1", noTT)]
    approx := [("5", "step 1 が無いので verifiedValue は attr の value と同じで、書き換えは何もしない")] },
  { alg := "concept-element-attributes-set-value"
    impl := [``Dom.setAttributeValue]
    spec := [``Dom.Spec.SetAttributeValueResult] },
  { alg := "concept-element-attributes-remove-by-name"
    impl := [``Dom.removeAttribute, ``Dom.removeNamedItem]
    spec := [``Dom.Spec.RemoveAttributeResult, ``Dom.Spec.RemoveNamedItemResult]
    approx := [("3", "removeAttribute は戻り値を捨てるので、取り除いた `Attr` を状態に残さない（removeNamedItem は残す）")] },
  { alg := "concept-element-attributes-remove-by-namespace"
    impl := [``Dom.removeAttributeNS]
    spec := [``Dom.Spec.RemoveAttributeNSResult]
    approx := [("3", "removeAttributeNS は戻り値を捨てるので、取り除いた `Attr` を状態に残さない")] },
  -- Element の getter と method
  { alg := "dom-element-namespaceuri"
    impl := [``Dom.NodeData.«namespace»] },
  { alg := "dom-element-prefix"
    impl := [``Dom.NodeData.«prefix»] },
  { alg := "dom-element-localname"
    impl := [``Dom.NodeData.localName] },
  { alg := "dom-element-tagname"
    impl := [``Dom.tagName] },
  { alg := "concept-reflect"
    impl := [``Dom.getReflected, ``Dom.getReflectedProp, ``Dom.setReflectedProp] },
  { alg := "dom-element-classlist"
    impl := [``Dom.classTokenSet, ``Dom.classListContains, ``Dom.classListAdd]
    approx := [("*", "DOMTokenList object を持たず、各 method が element を受けて class attribute の値から token set を読み直す")] },
  { alg := "dom-element-getattributenames"
    impl := [``Dom.getAttributeNames] },
  { alg := "dom-element-getattribute"
    impl := [``Dom.getAttribute, ``Dom.getAttributeByName] },
  { alg := "dom-element-setattribute"
    impl := [``Dom.setAttribute, ``Dom.attrNameFor, ``Dom.isValidAttributeLocalName]
    spec := [``Dom.Spec.SetAttributeResult]
    omitted := [("3", noTT)] },
  { alg := "dom-element-setattributens"
    impl := [``Dom.setAttributeNS, ``Dom.validateAndExtractAttribute, ``Dom.setAttributeValue]
    spec := [``Dom.Spec.SetAttributeValueResult]
    omitted := [("2", noTT)] },
  { alg := "dom-element-removeattribute"
    impl := [``Dom.removeAttribute]
    spec := [``Dom.Spec.RemoveAttributeResult] },
  { alg := "dom-element-removeattributens"
    impl := [``Dom.removeAttributeNS]
    spec := [``Dom.Spec.RemoveAttributeNSResult] },
  { alg := "dom-element-hasattribute"
    impl := [``Dom.hasAttribute, ``Dom.getAttributeByName] },
  { alg := "dom-element-toggleattribute"
    impl := [``Dom.toggleAttribute]
    spec := [``Dom.Spec.ToggleAttributeResult] },
  { alg := "dom-element-getattributenode"
    impl := [``Dom.getAttributeNode] },
  { alg := "dom-element-getattributenodens"
    impl := [``Dom.getAttributeNodeNS] },
  { alg := "dom-element-setattributenode"
    impl := [``Dom.setAttributeNode]
    spec := [``Dom.Spec.SetAttributeNodeResult] },
  { alg := "dom-element-removeattributenode"
    impl := [``Dom.removeAttributeNode, ``Dom.detachAttribute]
    spec := [``Dom.Spec.RemoveAttributeNodeResult] },
  { alg := "dom-element-closest"
    impl := [``Dom.closest, ``Dom.inclusiveAncestorElements]
    approx := [("1-2", "parse a selector は model の Selectors の部分集合（`Dom/Selector/`）")] },
  { alg := "dom-element-matches"
    impl := [``Dom.matchesSelector]
    approx := [("1-2", "parse a selector は model の Selectors の部分集合（`Dom/Selector/`）")] },
  { alg := "dom-element-webkitmatchesselector"
    impl := [``Dom.matchesSelector]
    approx := [("1-2", "parse a selector は model の Selectors の部分集合（`Dom/Selector/`）")] },
  { alg := "dom-element-getelementsbyclassname"
    impl := [``Dom.getElementsByClassName, ``Dom.elementClassesOf]
    approx := [("*", "live な HTMLCollection ではなく、呼んだ時点の element の列を返す")] },
  -- §4.9.1 NamedNodeMap
  { alg := "dom-namednodemap-getnameditem"
    impl := [``Dom.getAttributeNode, ``Dom.getAttributeByName]
    approx := [("*", "NamedNodeMap object を持たない。同じ algorithm（get an attribute by name）を呼ぶ getAttributeNode で計算する")] },
  { alg := "dom-namednodemap-getnameditemns"
    impl := [``Dom.getAttributeNodeNS, ``Dom.getAttributeByKey]
    approx := [("*", "NamedNodeMap object を持たない。同じ algorithm を呼ぶ getAttributeNodeNS で計算する")] },
  { alg := "dom-namednodemap-setnameditem"
    impl := [``Dom.setAttributeNode]
    approx := [("*", "NamedNodeMap object を持たない。同じ algorithm（set an attribute）を呼ぶ setAttributeNode で計算する")] },
  { alg := "dom-namednodemap-setnameditemns"
    impl := [``Dom.setAttributeNode]
    approx := [("*", "NamedNodeMap object を持たない。同じ algorithm（set an attribute）を呼ぶ setAttributeNode で計算する")] },
  { alg := "dom-namednodemap-removenameditem"
    impl := [``Dom.removeNamedItem, ``Dom.removeAttributeNode]
    spec := [``Dom.Spec.RemoveNamedItemResult] },
  -- §4.9.2 Attr
  { alg := "create-an-attribute"
    impl := [``Dom.createAttributeIn, ``Dom.Attr.normalized]
    approx := [("1", "node tree には入れず、detachedAttrs に足す。id は freshStateAttrId")] },
  { alg := "dom-attr-namespaceuri"
    impl := [``Dom.findAttr, ``Dom.Attr.«namespace»] },
  { alg := "dom-attr-prefix"
    impl := [``Dom.findAttr, ``Dom.Attr.«prefix»] },
  { alg := "dom-attr-localname"
    impl := [``Dom.findAttr, ``Dom.Attr.localName] },
  { alg := "dom-attr-name"
    impl := [``Dom.findAttr, ``Dom.Attr.qualifiedName] },
  { alg := "dom-attr-value"
    impl := [``Dom.findAttr, ``Dom.Attr.value] },
  { alg := "set-an-existing-attribute-value"
    impl := [``Dom.setAttrValue, ``Dom.modifyAttr, ``Dom.changeAttribute]
    omitted := [("3", noTT),
                ("4", .other "step 3 が script を走らせないので、attribute の element は step 1 の判定から変わらない")] },
  { alg := "dom-attr-value/setter"
    impl := [``Dom.setAttrValue] },
  { alg := "dom-attr-ownerelement"
    impl := [``Dom.attrOwnerElement, ``Dom.ownerElementOf] }
]

def exclusions : List Exclusion := [
  { target := "dom-element-hasattributes", reason := .todo "hasAttributes() の関数と harness の op が無い" },
  { target := "dom-element-attributes", reason := .todo "NamedNodeMap object（element の attributes getter）を持たない" },
  { target := "dom-element-getattributens", reason := .todo "getAttributeNS() の関数が無い（getAttributeByKey はあるが null と value を返す method が無い）" },
  { target := "dom-element-hasattributens", reason := .todo "hasAttributeNS() の関数が無い" },
  { target := "dom-element-attachshadow", reason := .shadow },
  { target := "concept-attach-a-shadow-root", reason := .shadow },
  { target := "dom-element-shadowroot", reason := .shadow },
  { target := "dom-element-customelementregistry", reason := .customElements },
  { target := "dom-element-getelementsbytagname", reason := .todo "list of elements with qualified name（getElementsByTagName）が無い" },
  { target := "dom-element-getelementsbytagnamens", reason := .todo "list of elements with namespace and local name（getElementsByTagNameNS）が無い" },
  { target := "insert-adjacent", reason := .todo "insert adjacent が無い" },
  { target := "dom-element-insertadjacentelement", reason := .todo "insert adjacent が無い" },
  { target := "dom-element-insertadjacenttext", reason := .todo "insert adjacent が無い" },
  { target := "dom-namednodemap-length", reason := .todo "NamedNodeMap object を持たない（length が無い）" },
  { target := "dom-namednodemap-item", reason := .todo "NamedNodeMap object を持たない（item(index) が無い）" },
  { target := "interface-namednodemap/supported-property-names", reason := .todo "NamedNodeMap の named property が無い" },
  { target := "dom-namednodemap-removenameditemns", reason := .todo "removeNamedItemNS() の関数が無い（removeAttributeNS は NotFoundError も `Attr` を返すことも無い）" },
  { target := "dom-attr-specified", reason := .legacy }
]

end Trace.Dom.Element
