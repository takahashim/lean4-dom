import Trace.Basic
import Dom

/-!
# §4.2 Node tree のうち §4.2.3 以外

node の length、§4.2.2 shadow tree と slot、§4.2.4 `NonElementParentNode`、
§4.2.5 `DocumentOrShadowRoot`、§4.2.6 `ParentNode`、§4.2.7 `NonDocumentTypeChildNode`、
§4.2.8 `ChildNode`、§4.2.9 `Slottable`、§4.2.10 `HTMLCollection`。

model の method は「convert nodes into a node」を呼び出し側で済ませた一つの node を受け取る
（`Dom/Mutation/Api.lean`）。その step は各 entry の `approx` に書く。
-/

namespace Trace.Dom.ParentNode

open Trace

/-- 「convert nodes into a node」を呼び出し側で済ませる、という近似の説明。 -/
private def convertedByCaller : String :=
  "可変長の nodes と文字列を node にまとめる変換はしない。呼び出し側がまとめた一つの node を受け取る"

def entries : List Entry := [
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
  { alg := "dom-parentnode-append"
    impl := [``Dom.append]
    approx := [("1", convertedByCaller)] },
  { alg := "dom-parentnode-replacechildren"
    impl := [``Dom.replaceChildren, ``Dom.ensurePreInsertionValidity, ``Dom.replaceAll]
    spec := [``Dom.Spec.ReplaceChildrenResult]
    approx := [("1", convertedByCaller)] },
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
    impl := [``Dom.before, ``Dom.viablePreviousSibling, ``Dom.preInsert]
    spec := [``Dom.Spec.BeforeResult, ``Dom.Spec.ViablePreviousSibling]
    approx := [("4", convertedByCaller ++ "。そのため step 1-3 は変換の後の木で評価され、nodes は [node] になる")] },
  { alg := "dom-childnode-after"
    impl := [``Dom.after, ``Dom.viableNextSibling, ``Dom.preInsert]
    spec := [``Dom.Spec.AfterResult, ``Dom.Spec.ViableNextSibling]
    approx := [("4", convertedByCaller ++ "。そのため step 1-3 は変換の後の木で評価され、nodes は [node] になる")] },
  { alg := "dom-childnode-replacewith"
    impl := [``Dom.replaceWith, ``Dom.viableNextSibling, ``Dom.replace, ``Dom.preInsert]
    spec := [``Dom.Spec.ReplaceWithResult, ``Dom.Spec.ViableNextSibling]
    approx := [("4", convertedByCaller ++ "。step 1-3 は変換の後の木で評価され、nodes は [node] になる"),
               ("5-6", "step 1 と step 5 の間で木が変わらないので、step 5 の条件は常に真になる（this が nodes に入っていて fragment に移る場合を区別しない）")] },
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
  { target := "convert-nodes-into-a-node"
    reason := .todo "文字列から Text を作り、複数の node を DocumentFragment にまとめる変換。model の method は変換済みの一つの node を受け取る（呼び出し側で済ませる）" },
  { target := "dom-parentnode-prepend"
    reason := .todo "prepend に当たる関数（this の first child の前への pre-insert）が無い。harness にも操作が無い" },
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
