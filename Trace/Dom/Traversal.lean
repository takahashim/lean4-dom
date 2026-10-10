import Trace.Basic
import Dom
import Dom.Exec.Eval

/-!
# §6 Traversal（NodeFilter、NodeIterator、TreeWalker）

`NodeFilter` の callback は model の外にあり、filter は常に null として扱う。
そのため "filter" は whatToShow の bit だけで決まり（FILTER_ACCEPT か FILTER_SKIP）、
FILTER_REJECT も例外も出ない。走査はどれも「候補を tree order（かその鏡像）に並べ、
accept される最初のものを取る」形に書き直してある。

iterator と walker は scenario が初期状態に与え、番号で指す
（`createNodeIterator`・`createTreeWalker` は model に無い）。
getter は状態（`IteratorState`・`WalkerState`）を読むだけで、各 step の観測（`Dom.observe`）に出る。
-/

namespace Trace.Dom.Traversal

open Trace

private def filterNull : String :=
  "filter は常に null。whatToShow の bit だけで決まるので FILTER_REJECT が出ず、仕様の loop を「候補列の中で accept される最初の node」に書き直してある"

def entries : List Entry := [
  { alg := "concept-node-filter"
    impl := [``Dom.showsNode, ``Dom.walkerAccepts]
    omitted := [("1", .host), ("5-8", .host)]
    approx := [("4", "filter は常に null として扱うので、ここで必ず FILTER_ACCEPT を返す")] },
  -- §6.1 NodeIterator
  { alg := "nodeiterator-pre-removing-steps"
    impl := [``Dom.iteratorPreRemove, ``Dom.iteratorPreRemoveOne]
    spec := [``Dom.Spec.IteratorAdjusted]
    omitted := [("2", .other "candidate reference は traverse の途中（filter の callback の中）でしか非 null にならず、filter が null なので状態に持たない")] },
  { alg := "nodeiterator-adjust-a-node-pointer"
    impl := [``Dom.adjustNodePointer, ``Dom.firstFollowingOutside]
    spec := [``Dom.Spec.PointerAdjusted, ``Dom.Spec.FirstFollowingOutside,
             ``Dom.Spec.LastBeforeRemoval] },
  { alg := "dom-nodeiterator-root"
    impl := [``Dom.IteratorState.root, ``Dom.observe] },
  { alg := "dom-nodeiterator-referencenode"
    impl := [``Dom.IteratorState.reference, ``Dom.observe] },
  { alg := "dom-nodeiterator-pointerbeforereferencenode"
    impl := [``Dom.IteratorState.pointerBeforeReference, ``Dom.observe] },
  { alg := "dom-nodeiterator-whattoshow"
    impl := [``Dom.IteratorState.whatToShow, ``Dom.observe] },
  { alg := "concept-nodeiterator-traverse"
    impl := [``Dom.nextNode, ``Dom.previousNode, ``Dom.iteratorCollection, ``Dom.showsNode,
             ``Dom.Exec.stepIterator]
    approx := [("1-4", "candidate reference を持たず、iterator collection を reference で二つに分けて、pointer before に応じて reference 自身を候補に足した列から whatToShow を満たす最初の node を探す。" ++ filterNull)] },
  { alg := "dom-nodeiterator-nextnode"
    impl := [``Dom.nextNode, ``Dom.Exec.stepIterator] },
  { alg := "dom-nodeiterator-previousnode"
    impl := [``Dom.previousNode, ``Dom.Exec.stepIterator] },
  -- §6.2 TreeWalker
  { alg := "dom-treewalker-root"
    impl := [``Dom.WalkerState.root, ``Dom.observe] },
  { alg := "dom-treewalker-whattoshow"
    impl := [``Dom.WalkerState.whatToShow, ``Dom.observe] },
  { alg := "dom-treewalker-currentnode"
    impl := [``Dom.WalkerState.current, ``Dom.observe] },
  { alg := "dom-treewalker-parentnode"
    impl := [``Dom.walkerParentNode, ``Dom.takeUntilIncl, ``Dom.walkerStep, ``Dom.walkerRun]
    approx := [("2", "current の祖先を root まで（root を含む）並べ、accept される最初のものを取る")] },
  { alg := "concept-traverse-children"
    impl := [``Dom.walkerFirstChild, ``Dom.walkerLastChild, ``Dom.mirrorPreorder,
             ``Dom.walkerStep, ``Dom.walkerRun]
    approx := [("2-4", "current の（自身を除く）部分木を tree order（last なら鏡像）に並べた列で探す。" ++ filterNull)] },
  { alg := "dom-treewalker-firstchild"
    impl := [``Dom.walkerFirstChild, ``Dom.walkerStep] },
  { alg := "dom-treewalker-lastchild"
    impl := [``Dom.walkerLastChild, ``Dom.walkerStep] },
  { alg := "concept-traverse-siblings"
    impl := [``Dom.walkerSibling, ``Dom.walkerSiblingSearch, ``Dom.siblingCandidates,
             ``Dom.followingSiblings, ``Dom.precedingSiblings, ``Dom.walkerStep, ``Dom.walkerRun]
    approx := [("3", "段ごとに兄弟の部分木を順に並べた列で探し、見つからなければ親へ上がる。" ++ filterNull)] },
  { alg := "dom-treewalker-nextsibling"
    impl := [``Dom.walkerSibling, ``Dom.walkerStep] },
  { alg := "dom-treewalker-previoussibling"
    impl := [``Dom.walkerSibling, ``Dom.walkerStep] },
  { alg := "dom-treewalker-previousnode"
    impl := [``Dom.walkerPreviousNode, ``Dom.walkerBase, ``Dom.walkerStep, ``Dom.walkerRun]
    approx := [("2", "`walkerBase`（current が root の外なら current 側の木の根）を根とする preorder を current の手前から逆にたどる。" ++ filterNull)] },
  { alg := "dom-treewalker-nextnode"
    impl := [``Dom.walkerNextNode, ``Dom.walkerBase, ``Dom.walkerStep, ``Dom.walkerRun]
    approx := [("3", "`walkerBase` を根とする preorder を current の次からたどる。" ++ filterNull)] }
]

def exclusions : List Exclusion := [
  { target := "dom-nodeiterator-filter", reason := .host },
  { target := "dom-nodeiterator-detach", reason := .legacy },
  { target := "dom-treewalker-filter", reason := .host },
  { target := "dom-treewalker-currentnode/setter",
    reason := .todo "currentNode を設定する操作が harness に無い（初期状態の current だけを与えられる）" }
]

end Trace.Dom.Traversal
