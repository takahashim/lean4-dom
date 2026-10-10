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
    approx := [("*", "`NodeKind` に Attr が無いので ATTRIBUTE_NODE (2) は返らない（`Attr` は木の外の別の型）。harness に getter の操作は無い")] },
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
    impl := [``Dom.setAttrValue, ``Dom.setData]
    approx := [("*", "setter として振り分ける関数は無い。Attr の枝は `setAttrValue`（harness の `setAttrValue` の via = nodeValue）、CharacterData の枝は同じ replace data をする `setData` が担う。「Otherwise 何もしない」の枝と null → 空文字列の変換は model に無い")] },
  { alg := "get-text-content"
    impl := [``Dom.getTextContent, ``Dom.descendantTextContent, ``Dom.Exec.attrQueryValue] },
  { alg := "dom-node-textcontent"
    impl := [``Dom.getTextContent, ``Dom.Exec.attrQueryValue] },
  { alg := "dom-node-normalize"
    impl := [``Dom.normalize, ``Dom.normalizeList, ``Dom.normalizeRun, ``Dom.normalizeMergeOne,
             ``Dom.normalizeMergeRange, ``Dom.normalizeMergeBP, ``Dom.followingTexts]
    spec := [``Dom.Spec.NormalizeSpec, ``Dom.Spec.NormalizeResult]
    approx := [("3-4", "run 全体を一度に連結して replace data を一回呼ぶのではなく、engine に合わせて兄弟ごとに replace data する（data が空の兄弟では呼ばない）。木と range の最終状態は同じで、characterData record の並びが違う"),
               ("6", "兄弟ごとに boundary point を渡してからその兄弟を remove する。step 6 と step 7 を兄弟ごとに交互に行う"),
               ("7", "兄弟ごとに step 6 の直後に remove する（上と同じ）")] },
  { alg := "concept-node-clone"
    impl := [``Dom.cloneNodeIn, ``Dom.cloneMany, ``Dom.cloneAppend]
    omitted := [("3", .hook), ("6", .shadow)] },
  { alg := "clone-a-single-node"
    impl := [``Dom.cloneSingle, ``Dom.cloneData, ``Dom.cloneDocumentOf, ``Dom.cloneAttrIn]
    omitted := [("2.1-2.3", .customElements), ("5.2", .customElements)]
    approx := [("2.4", "create an element を呼ばず、`NodeData` を写して element を作る（is value・custom element の処理は無い）"),
               ("5", "DocumentType の name・public ID・system ID と ProcessingInstruction の target を model が持たないので写さない"),
               ("5.1", "Document の持ち物のうち model にあるのは type（`isHTMLDocument`）と mode だけで、それを写す。encoding・content type・URL・origin・allow declarative shadow roots は無い")] },
  { alg := "dom-node-clonenode"
    impl := [``Dom.cloneNode, ``Dom.cloneAttr]
    omitted := [("1", .shadow)] },
  { alg := "concept-node-equals"
    impl := [``Dom.nodeEqualsFuel, ``Dom.nodeOwnPropertiesEqual, ``Dom.attrEquals, ``Dom.nodeRefEquals]
    approx := [("*", "DocumentType の name・public ID・system ID と ProcessingInstruction の target は model に無いので比べない（harness はどちらも固定値で作る）")] },
  { alg := "dom-node-isequalnode"
    -- otherNode が null なら false（`isEqualNodeNull`）。
    impl := [``Dom.nodeEquals, ``Dom.nodeRefEquals, ``Dom.Exec.Operation.isEqualNodeNull] },
  { alg := "dom-node-comparedocumentposition"
    impl := [``Dom.compareDocumentPosition, ``Dom.compareDocumentPositionRef]
    spec := [``Dom.Spec.DocumentPositionSpec] },
  { alg := "dom-node-contains"
    -- other が null なら false（`nodeContainsNull`）。
    impl := [``Dom.nodeContains, ``Dom.nodeContainsRef, ``Dom.Exec.Operation.nodeContainsNull] },
  { alg := "locate-a-namespace-prefix"
    impl := [``Dom.locateNamespacePrefixIn, ``Dom.elementChain] },
  { alg := "locate-a-namespace"
    impl := [``Dom.locateNamespace, ``Dom.locateNamespaceIn, ``Dom.elementChain,
             ``Dom.attrLookupNamespaceURI] },
  { alg := "dom-node-lookupprefix"
    impl := [``Dom.lookupPrefix, ``Dom.attrLookupPrefix] },
  { alg := "dom-node-lookupnamespaceuri"
    impl := [``Dom.lookupNamespaceURI, ``Dom.attrLookupNamespaceURI] },
  { alg := "dom-node-isdefaultnamespace"
    impl := [``Dom.isDefaultNamespace, ``Dom.attrIsDefaultNamespace] },
  { alg := "dom-node-insertbefore"
    impl := [``Dom.insertBefore] },
  { alg := "dom-node-appendchild"
    impl := [``Dom.appendChild, ``Dom.appendChildRef] },
  { alg := "dom-node-replacechild"
    impl := [``Dom.replaceChild] },
  { alg := "dom-node-removechild"
    impl := [``Dom.removeChild] }
]

def exclusions : List Exclusion := [
  { target := "dom-node-nodename",
    reason := .todo "Node の nodeName を返す関数が無い（Element は `tagName`、Attr は harness の attrQuery で qualified name を読むだけ）。DocumentType の name と ProcessingInstruction の target も model に無い" },
  { target := "dom-node-baseuri", reason := .todo "document の URL（document base URL）を持たない" },
  { target := "dom-node-isconnected",
    reason := .todo "node の connected を返す関数が無い（Attr だけ harness の attrQuery が false を返す）" },
  { target := "dom-node-issamenode", reason := .todo "harness に操作が無い（`NodeId` の等号そのもので、実行関数を持たない）" },
  { target := "string-replace-all", reason := .todo "文字列から Text node を作って replace all する関数が無い" },
  { target := "set-text-content",
    reason := .todo "Element・DocumentFragment の枝（string replace all）が無い。Attr の枝は `setAttrValue`（via = textContent）、CharacterData の枝は `setData` と同じ処理だが、set text content として振り分ける関数は無い" },
  { target := "dom-node-textcontent/setter", reason := .todo "set text content が無い（同上）" }
]

end Trace.Dom.Node
