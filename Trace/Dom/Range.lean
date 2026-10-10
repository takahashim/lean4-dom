import Trace.Basic
import Dom

/-!
# §5 Ranges（boundary point、AbstractRange、StaticRange、Range）

model の live range は `DOMState.ranges` の要素で、scenario が初期状態に与え、番号で指す。
`Range` object を作る API（`new Range()`・`createRange()`・`cloneRange()`）と
`StaticRange` は model に無い。
getter は model の状態（`RangeState` の両端）を読むだけで、各 step の観測（`Dom.observe`）に出る。
-/

namespace Trace.Dom.Range

open Trace

def entries : List Entry := [
  -- §5.2 boundary point
  { alg := "concept-range-bp-position"
    impl := [``Dom.bpPosition, ``Dom.bpPositionDown, ``Dom.childTowards]
    spec := [``Dom.Spec.BPBefore]
    approx := [("1", "assert は書かない。呼び出し側（`BoundaryLE`・`rangeNeedsCollapse` など）が root を別に比べる"),
               ("3", "自分自身を入れ替えて呼ぶ代わりに、`bpPositionDown` を入れ替えて呼んだ結果を `swap` する（入れ子は高々一段）")] },
  -- §5.3 AbstractRange
  { alg := "range-collapsed"
    impl := [``Dom.rangeDeleteContents, ``Dom.rangeInsertNode]
    approx := [("*", "専用の定義は無く、使う側（deleteContents step 1・insert step 13）が `r.start == r.end` を直に書く")] },
  { alg := "dom-range-startcontainer"
    impl := [``Dom.RangeState.start, ``Dom.BoundaryPoint.node, ``Dom.observe] },
  { alg := "dom-range-startoffset"
    impl := [``Dom.RangeState.start, ``Dom.BoundaryPoint.offset, ``Dom.observe] },
  { alg := "dom-range-endcontainer"
    impl := [``Dom.RangeState.«end», ``Dom.BoundaryPoint.node, ``Dom.observe] },
  { alg := "dom-range-endoffset"
    impl := [``Dom.RangeState.«end», ``Dom.BoundaryPoint.offset, ``Dom.observe] },
  -- §5.5 Range
  { alg := "live-range-pre-remove-steps"
    impl := [``Dom.liveRangePreRemove, ``Dom.liveRangePreRemoveRange, ``Dom.liveRangePreRemoveBP,
             ``Dom.rangeMoveOutOfSubtree, ``Dom.rangeShiftAfterRemove]
    spec := [``Dom.Spec.RangeAdjusted, ``Dom.Spec.BoundaryAdjusted]
    approx := [("2", "assert の代わりに、parent が無ければ何もしない"),
               ("4-7", "range ごとに step 4・6（start）と step 5・7（end）を合成して一度に当てる。step 4-5 で移した点の offset は index なので step 6-7 に掛からず、結果は同じ")] },
  { alg := "concept-range-bp-set"
    impl := [``Dom.setStartBP, ``Dom.setEndBP, ``Dom.rangeBoundaryError, ``Dom.rangeNeedsCollapse]
    spec := [``Dom.Spec.StartSet, ``Dom.Spec.EndSet, ``Dom.Spec.BoundaryPointError,
             ``Dom.Spec.BoundaryPointOk]
    approx := [("4", "set the start では range の root を start node ではなく end node の root で比べる（妥当な range では同じ。spec 側は start node の root で書き、定理が RangeValid を仮定する）")] },
  { alg := "dom-range-setstart"
    impl := [``Dom.rangeSetStart]
    spec := [``Dom.Spec.SetStartResult] },
  { alg := "dom-range-setend"
    impl := [``Dom.rangeSetEnd]
    spec := [``Dom.Spec.SetEndResult] },
  { alg := "dom-range-setstartbefore"
    impl := [``Dom.rangeSetStartSibling, ``Dom.siblingBP]
    spec := [``Dom.Spec.SetStartSiblingResult, ``Dom.Spec.SiblingPoint] },
  { alg := "dom-range-setstartafter"
    impl := [``Dom.rangeSetStartSibling, ``Dom.siblingBP]
    spec := [``Dom.Spec.SetStartSiblingResult, ``Dom.Spec.SiblingPoint] },
  { alg := "dom-range-setendbefore"
    impl := [``Dom.rangeSetEndSibling, ``Dom.siblingBP]
    spec := [``Dom.Spec.SetEndSiblingResult, ``Dom.Spec.SiblingPoint] },
  { alg := "dom-range-setendafter"
    impl := [``Dom.rangeSetEndSibling, ``Dom.siblingBP]
    spec := [``Dom.Spec.SetEndSiblingResult, ``Dom.Spec.SiblingPoint] },
  { alg := "dom-range-collapse"
    impl := [``Dom.rangeCollapse]
    spec := [``Dom.Spec.CollapseResult] },
  { alg := "concept-range-select"
    impl := [``Dom.rangeSelectNode]
    spec := [``Dom.Spec.SelectNodeResult] },
  { alg := "dom-range-selectnode"
    impl := [``Dom.rangeSelectNode]
    spec := [``Dom.Spec.SelectNodeResult] },
  { alg := "dom-range-selectnodecontents"
    impl := [``Dom.rangeSelectNodeContents]
    spec := [``Dom.Spec.SelectNodeContentsResult] },
  { alg := "dom-range-compareboundarypoints"
    impl := [``Dom.rangeCompareBoundaryPoints, ``Dom.bpPosition]
    spec := [``Dom.Spec.CompareBoundaryPointsResult, ``Dom.Spec.compareHowPoints,
             ``Dom.Spec.PositionResult] },
  { alg := "dom-range-deletecontents"
    impl := [``Dom.rangeDeleteContents, ``Dom.nodesToRemove, ``Dom.containedInRange,
             ``Dom.deleteContentsNewBP, ``Dom.removeEach, ``Dom.replaceData]
    spec := [``Dom.Spec.DeleteContentsResult, ``Dom.Spec.NodesToRemove, ``Dom.Spec.Contained,
             ``Dom.Spec.DeleteNewBP]
    approx := [("8", "(newNode, newOffset) を step 9-11 の後で置く。step 9-11 の live range 調整はこの点を動かさないので同じ値になるが、実行関数はその点が最終の木で妥当かを検査し、妥当でなければ調整後の start を使う")] },
  { alg := "concept-range-insert"
    impl := [``Dom.rangeInsertNode, ``Dom.ensurePreInsertionValidity, ``Dom.preInsert,
             ``Dom.remove, ``Dom.siblingBP]
    spec := [``Dom.Spec.InsertNodeResult, ``Dom.Spec.InsertNodeTail, ``Dom.Spec.NewOffset,
             ``Dom.Spec.InsertNodeHierarchyError, ``Dom.Spec.ChildAtOffset]
    omitted := [("7", .todo "Text node の split（§4.11 split a Text node）が model に無い。start node が Text なら step 6 の validity を通った後で outsideModel を返す")]
    approx := [("10-11", "newOffset を step 12 の前に数えず、step 13 で「入った最後の node の直後」（`siblingBP`）として求める。空の DocumentFragment なら end を置き直さない")] },
  { alg := "dom-range-insertnode"
    impl := [``Dom.rangeInsertNode]
    spec := [``Dom.Spec.InsertNodeResult] },
  { alg := "dom-range-ispointinrange"
    impl := [``Dom.rangeIsPointInRange]
    spec := [``Dom.Spec.IsPointInRangeResult] },
  { alg := "dom-range-comparepoint"
    impl := [``Dom.rangeComparePoint]
    spec := [``Dom.Spec.ComparePointResult] },
  { alg := "dom-range-intersectsnode"
    impl := [``Dom.rangeIntersectsNode]
    spec := [``Dom.Spec.IntersectsNodeResult] },
  { alg := "dom-range-stringifier"
    impl := [``Dom.rangeToString, ``Dom.containedInRange, ``Dom.substringData]
    approx := [("2-5", "UTF-16 の code unit で切り出す。surrogate pair の途中を指すと outsideModel になる")] }
]

def exclusions : List Exclusion := [
  { target := "dom-range-collapsed",
    reason := .todo "collapsed getter を返す操作が harness に無い（両端は観測に出るので導ける）" },
  { target := "dom-staticrange-staticrange",
    reason := .todo "StaticRange が model に無い" },
  { target := "staticrange-valid",
    reason := .todo "StaticRange が model に無い" },
  { target := "dom-range-range", reason := .host },
  { target := "get-the-common-ancestor",
    reason := .todo "common ancestor を求める定義が無い（使う extract・clone the contents が未実装）" },
  { target := "dom-range-commonancestorcontainer",
    reason := .todo "commonAncestorContainer getter が無い" },
  { target := "concept-range-extract",
    reason := .todo "extract（DocumentFragment への移し替えと部分 clone）が未実装" },
  { target := "dom-range-extractcontents",
    reason := .todo "extract が未実装" },
  { target := "concept-range-clone",
    reason := .todo "clone the contents が未実装" },
  { target := "dom-range-clonecontents",
    reason := .todo "clone the contents が未実装" },
  { target := "dom-range-surroundcontents",
    reason := .todo "extract に依存するので未実装" },
  { target := "dom-range-clonerange",
    reason := .todo "Range object を新しく作る操作が model に無い（range は初期状態で与える）" },
  { target := "dom-range-detach", reason := .legacy }
]

end Trace.Dom.Range
