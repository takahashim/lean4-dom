import Trace.Basic
import Dom

/-!
# §4.2 Node tree のうち §4.2.3 以外

node の length、§4.2.2 shadow tree と slot、§4.2.4 `NonElementParentNode`、
§4.2.5 `DocumentOrShadowRoot`、§4.2.6 `ParentNode`、§4.2.7 `NonDocumentTypeChildNode`、
§4.2.8 `ChildNode`、§4.2.9 `Slottable`、§4.2.10 `HTMLCollection`。

可変長の `(Node or DOMString)` 引数を取る method は `Dom/Mutation/Variadic.lean` にあり、
「convert nodes into a node」を本文どおりに行う。失敗したときもその時点の状態を返し、変換が作って
参照されなくなった node（空になった DocumentFragment など）は状態から消す（`Dom.discard`）。
-/

namespace Trace.Dom.ParentNode

open Trace

def entries : List Entry := [
  { alg := "convert-nodes-into-a-node"
    impl := [``Dom.convertNodesIntoNode, ``Dom.textsFor, ``Dom.appendAll, ``Dom.discardAll] },
  { alg := "concept-node-length"
    impl := [``Dom.lengthOf, ``Dom.NodeData.length]
    approx := [("1", "Attr は木の node ではない（NodeKind に無い）ので、DocumentType だけが 0 になる")] },
  -- §4.2.4
  { alg := "get-an-element-by-id"
    impl := [``Dom.getElementById, ``Dom.descendantElements, ``Dom.elementIdOf] },
  { alg := "dom-nonelementparentnode-getelementbyid"
    impl := [``Dom.getElementById, ``Dom.requireNonElementParentNode] },
  -- §4.2.6
  { alg := "dom-parentnode-children"
    impl := [``Dom.elementChildrenOf]
    approx := [("*", "live な HTMLCollection は作らない。collection が表す element children をその時点の list として返す。harness に操作は無く、`childrenNamedItem` の中でだけ使う")] },
  { alg := "dom-parentnode-prepend"
    impl := [``Dom.prependNodes, ``Dom.convertNodesIntoNode, ``Dom.preInsert] },
  { alg := "dom-parentnode-append"
    impl := [``Dom.appendNodes, ``Dom.convertNodesIntoNode, ``Dom.append] },
  { alg := "dom-parentnode-replacechildren"
    impl := [``Dom.replaceChildrenNodes, ``Dom.convertNodesIntoNode, ``Dom.replaceChildren,
             ``Dom.ensurePreInsertionValidity, ``Dom.replaceAll]
    -- 関係 `ReplaceChildrenResult` は step 2-3 を変換済みの node について述べる（`replaceChildrenNodes_single`）。
    spec := [``Dom.Spec.ReplaceChildrenResult] },
  { alg := "dom-parentnode-movebefore"
    impl := [``Dom.moveBefore, ``Dom.move]
    spec := [``Dom.Spec.MoveResult] },
  { alg := "dom-parentnode-queryselector"
    impl := [``Dom.querySelector, ``Dom.scopeMatch, ``Dom.matchTree, ``Dom.requireParentNode] },
  { alg := "dom-parentnode-queryselectorall"
    impl := [``Dom.querySelectorAll, ``Dom.scopeMatch, ``Dom.matchTree, ``Dom.requireParentNode]
    approx := [("*", "static な NodeList ではなく、element の list を返す")] },
  -- §4.2.8
  { alg := "dom-childnode-before"
    impl := [``Dom.beforeNodes, ``Dom.convertNodesIntoNode, ``Dom.viablePreviousSibling, ``Dom.preInsert]
    -- 関係（`BeforeResult` ほか）は変換済みの一つの node を受け取る形で書いてあり、引数が node 一つのときは
    -- `beforeNodes_single` ほかにより可変長の method と一致する。文字列や複数の node を含む場合の関係はまだ無い。
    spec := [``Dom.Spec.BeforeResult, ``Dom.Spec.ViablePreviousSibling, ``Dom.beforeNodes_single] },
  { alg := "dom-childnode-after"
    impl := [``Dom.afterNodes, ``Dom.convertNodesIntoNode, ``Dom.viableNextSibling, ``Dom.preInsert]
    spec := [``Dom.Spec.AfterResult, ``Dom.Spec.ViableNextSibling, ``Dom.afterNodes_single] },
  { alg := "dom-childnode-replacewith"
    impl := [``Dom.replaceWithNodes, ``Dom.convertNodesIntoNode, ``Dom.viableNextSibling, ``Dom.replace,
             ``Dom.preInsert]
    spec := [``Dom.Spec.ReplaceWithResult, ``Dom.Spec.ViableNextSibling, ``Dom.replaceWithNodes_single] },
  { alg := "dom-childnode-remove"
    impl := [``Dom.nodeRemove, ``Dom.remove]
    spec := [``Dom.Spec.NodeRemoveResult] },
  -- §4.2.10
  { alg := "dom-htmlcollection-nameditem"
    impl := [``Dom.childrenNamedItem, ``Dom.elementIdOf]
    approx := [("*", "collection は `ParentNode.children` のものに限る（他の HTMLCollection は model に無い）")] }
]

def exclusions : List Exclusion := [
  -- §4.2.2 shadow tree・slot・slottable（find a slot ほか、assign、signal a slot change）
  { target := "shadow-trees", reason := .shadow },
  -- §4.2.9 `assignedSlot`
  { target := "mixin-slotable", reason := .shadow },
  -- §4.2.5
  { target := "dom-documentorshadowroot-customelementregistry", reason := .customElements },
  -- §4.2.6
  { target := "dom-parentnode-firstelementchild"
    reason := .todo "getter の実行関数も harness の操作も無い" },
  { target := "dom-parentnode-lastelementchild"
    reason := .todo "getter の実行関数も harness の操作も無い" },
  { target := "dom-parentnode-childelementcount"
    reason := .todo "getter の実行関数も harness の操作も無い" },
  -- §4.2.7
  { target := "dom-nondocumenttypechildnode-previouselementsibling"
    reason := .todo "getter の実行関数も harness の操作も無い" },
  { target := "dom-nondocumenttypechildnode-nextelementsibling"
    reason := .todo "getter の実行関数も harness の操作も無い" },
  -- §4.2.10
  { target := "dom-htmlcollection-length"
    reason := .todo "HTMLCollection を表す構造が無く、length の実行関数も無い" },
  { target := "dom-htmlcollection-item"
    reason := .todo "HTMLCollection を表す構造が無く、item の実行関数も無い" },
  { target := "interface-htmlcollection/supported-property-names"
    reason := .todo "HTMLCollection の supported property names（WebIDL の named property）の実行関数が無い" }
]

end Trace.Dom.ParentNode
