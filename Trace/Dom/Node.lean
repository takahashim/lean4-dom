import Trace.Basic
import Dom
import Dom.Exec.Eval

/-!
# §4.4 Interface `Node`
-/

namespace Trace.Dom.Node

open Trace

def entries : List Entry := [
  { alg := "create-a-node"
    impl := [``Dom.withFresh]
    approx := [("2", "realm を持たない。node document を与えた `NodeData` を `freshId` の位置に置く")] },
  { alg := "dom-node-nodetype"
    impl := [``Dom.NodeKind.nodeType, ``Dom.kindOf]
    approx := [("*", "`NodeKind` に Attr が無いので ATTRIBUTE_NODE (2) は返らない（`Attr` は木の外の別の型で、`getProperty` も `Attr` の nodeType を読まない）")] },
  { alg := "dom-node-nodename"
    impl := [``Dom.nodeName, ``Dom.Exec.attrQueryValue] },
  { alg := "dom-node-isconnected"
    impl := [``Dom.isConnected, ``Dom.Exec.attrQueryValue]
    approx := [("*", "shadow tree が無いので、shadow-including root の代わりに root を見る")] },
  { alg := "dom-node-ownerdocument"
    impl := [``Dom.ownerDocumentGetter, ``Dom.Exec.attrQueryValue] },
  { alg := "dom-node-getrootnode"
    impl := [``Dom.getRootNode, ``Dom.attrGetRootNode]
    spec := [``Dom.Spec.IsRoot]
    approx := [("*", "options[\"composed\"] を受けず、常に root を返す（shadow tree が無いので shadow-including root と同じ値）")] },
  { alg := "dom-node-parentnode"
    impl := [``Dom.parentOf, ``Dom.attrParentNode] },
  { alg := "dom-node-parentelement"
    impl := [``Dom.parentElement] },
  { alg := "dom-node-haschildnodes"
    impl := [``Dom.childrenOf] },
  { alg := "dom-node-childnodes"
    impl := [``Dom.childrenOf]
    approx := [("*", "live な NodeList ではなく、読んだ時点の children の列を返す")] },
  { alg := "dom-node-firstchild"
    impl := [``Dom.childrenOf] },
  { alg := "dom-node-lastchild"
    impl := [``Dom.childrenOf] },
  { alg := "dom-node-previoussibling"
    impl := [``Dom.previousSibling] },
  { alg := "dom-node-nextsibling"
    impl := [``Dom.nextSibling] },
  { alg := "dom-node-nodevalue"
    impl := [``Dom.getNodeValue, ``Dom.Exec.attrQueryValue] },
  { alg := "dom-node-nodevalue/setter"
    impl := [``Dom.setNodeValue, ``Dom.setAttrValue]
    spec := [``Dom.Spec.SetNodeValueResult, ``Dom.Spec.setNodeValue_result_sound]
    approx := [("*", "Attr の枝は `setAttrValue`（harness が `Attr` を受け手にした `setNodeValue` を via = nodeValue に読み替える）。null → 空文字列は scenario を読むときに行う")] },
  { alg := "set-text-content"
    impl := [``Dom.setTextContent, ``Dom.stringReplaceAll, ``Dom.setAttrValue]
    spec := [``Dom.Spec.SetTextContentResult, ``Dom.Spec.setTextContent_result_sound]
    approx := [("*", "Attr の枝は `setAttrValue`（harness が `Attr` を受け手にした `setTextContent` を via = textContent に読み替える）。null → 空文字列は scenario を読むときに行う")] },
  { alg := "string-replace-all"
    impl := [``Dom.stringReplaceAll, ``Dom.createTextNode, ``Dom.replaceAll]
    spec := [``Dom.Spec.StringReplaceAllResult, ``Dom.Spec.stringReplaceAll_result_sound] },
  { alg := "dom-node-textcontent/setter"
    impl := [``Dom.setTextContent, ``Dom.setAttrValue]
    spec := [``Dom.Spec.setTextContent_result_sound] },
  { alg := "get-text-content"
    impl := [``Dom.getTextContent, ``Dom.descendantTextContent, ``Dom.Exec.attrQueryValue]
    spec := [``Dom.Spec.descendantTextContent_spec] },
  { alg := "dom-node-textcontent"
    impl := [``Dom.getTextContent, ``Dom.Exec.attrQueryValue]
    spec := [``Dom.Spec.descendantTextContent_spec] },
  { alg := "dom-node-normalize"
    impl := [``Dom.normalize, ``Dom.normalizeList, ``Dom.normalizeRun, ``Dom.normalizeMergeOne,
             ``Dom.normalizeMergeRange, ``Dom.normalizeMergeBP, ``Dom.followingTexts]
    spec := [``Dom.Spec.NormalizeEngineSpec, ``Dom.Spec.NormalizeStandardSpec, ``Dom.Spec.NormalizeResult]
    approx := [("3-4", "run 全体を一度に連結して replace data を一回呼ぶのではなく、engine に合わせて兄弟ごとに replace data する（data が空の兄弟では呼ばない）。characterData record の並びが違う。木と range の最終状態の一致は未証明"),
               ("6", "兄弟ごとに boundary point を渡してからその兄弟を remove する。step 6 と step 7 を兄弟ごとに交互に行う"),
               ("7", "兄弟ごとに step 6 の直後に remove する（上と同じ）")] },
  { alg := "concept-node-clone"
    impl := [``Dom.cloneNodeIn, ``Dom.cloneMany, ``Dom.cloneAppend]
    spec := [``Dom.CloneOf, ``Dom.cloneNode_cloneOf, ``Dom.cloneNodeIn_deep_spec]
    omitted := [("3", .hook), ("6", .shadow)] },
  { alg := "clone-a-single-node"
    impl := [``Dom.cloneSingle, ``Dom.cloneData, ``Dom.cloneDocumentOf, ``Dom.cloneAttrIn]
    spec := [``Dom.cloneNodeIn_shallow_spec]
    omitted := [("2.1-2.3", .customElements), ("5.2", .customElements)]
    approx := [("2.4", "create an element を呼ばず、`NodeData` を写して element を作る（is value・custom element の処理は無い）"),
               ("5.1", "Document の持ち物のうち model にあるのは type（`isHTMLDocument`）・mode・content type だけで、それを写す。encoding・URL・origin・allow declarative shadow roots は無い")] },
  { alg := "dom-node-clonenode"
    impl := [``Dom.cloneNode, ``Dom.cloneAttr]
    spec := [``Dom.cloneNode_cloneOf, ``Dom.Spec.cloneNode_nodeEquals]
    omitted := [("1", .shadow)] },
  { alg := "concept-node-equals"
    impl := [``Dom.nodeEqualsFuel, ``Dom.nodeOwnPropertiesEqual, ``Dom.attrEquals, ``Dom.nodeRefEquals]
    spec := [``Dom.Spec.NodeEquals, ``Dom.Spec.nodeEquals_iff, ``Dom.Spec.cloneOf_nodeEquals] },
  { alg := "dom-node-isequalnode"
    -- otherNode が null なら false（`isEqualNodeNull`）。
    impl := [``Dom.nodeEquals, ``Dom.nodeRefEquals, ``Dom.Exec.Operation.isEqualNodeNull]
    spec := [``Dom.Spec.nodeEquals_iff] },
  { alg := "dom-node-comparedocumentposition"
    impl := [``Dom.compareDocumentPosition, ``Dom.compareDocumentPositionRef]
    spec := [``Dom.Spec.DocumentPositionSpec] },
  { alg := "dom-node-contains"
    -- other が null なら false（`nodeContainsNull`）。
    impl := [``Dom.nodeContains, ``Dom.nodeContainsRef, ``Dom.Exec.Operation.nodeContainsNull]
    spec := [``Dom.Spec.nodeContains_eq_true_iff] },
  { alg := "locate-a-namespace-prefix"
    impl := [``Dom.locateNamespacePrefixIn, ``Dom.elementChain]
    spec := [``Dom.Spec.LocatePrefixElem, ``Dom.Spec.locatePrefixIn_sound] },
  { alg := "locate-a-namespace"
    impl := [``Dom.locateNamespace, ``Dom.locateNamespaceIn, ``Dom.elementChain,
             ``Dom.attrLookupNamespaceURI]
    spec := [``Dom.Spec.LocateNamespace, ``Dom.Spec.LocateNamespaceElem, ``Dom.Spec.locateNamespace_sound] },
  { alg := "dom-node-lookupprefix"
    impl := [``Dom.lookupPrefix, ``Dom.attrLookupPrefix]
    spec := [``Dom.Spec.LookupPrefixResult, ``Dom.Spec.lookupPrefix_sound] },
  { alg := "dom-node-lookupnamespaceuri"
    impl := [``Dom.lookupNamespaceURI, ``Dom.attrLookupNamespaceURI]
    spec := [``Dom.Spec.lookupNamespaceURI_sound] },
  { alg := "dom-node-isdefaultnamespace"
    impl := [``Dom.isDefaultNamespace, ``Dom.attrIsDefaultNamespace]
    spec := [``Dom.Spec.isDefaultNamespace_sound] },
  { alg := "dom-node-insertbefore"
    impl := [``Dom.insertBefore]
    spec := [``Dom.Spec.insertBefore_result_sound] },
  { alg := "dom-node-appendchild"
    impl := [``Dom.appendChild, ``Dom.appendChildRef]
    spec := [``Dom.Spec.appendChild_result_sound] },
  { alg := "dom-node-replacechild"
    impl := [``Dom.replaceChild]
    spec := [``Dom.Spec.replaceChild_result_sound] },
  { alg := "dom-node-removechild"
    impl := [``Dom.removeChild]
    spec := [``Dom.Spec.removeChild_result_sound] }
]

def exclusions : List Exclusion := [
  { target := "dom-node-baseuri", reason := .todo "document の URL（document base URL）を持たない" },
  { target := "dom-node-issamenode", reason := .todo "harness に操作が無い（`NodeId` の等号そのもので、実行関数を持たない）" }
]

end Trace.Dom.Node
