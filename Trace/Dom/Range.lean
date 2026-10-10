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
    -- step 2 の assert の代わりに、parent が無ければ何もしない。呼び出し元は remove（step 1-2 で parent を確かめる）と
    -- move（step 7-8）だけで、どちらの関係の soundness も parent のある場合に限って調整を述べる。
    -- step 4-7 は range ごとに合成して一度に当てる。二つの調整が可換であることは `liveRangePreRemoveBP_comm`。
    spec := [``Dom.Spec.RangeAdjusted, ``Dom.Spec.BoundaryAdjusted, ``Dom.liveRangePreRemoveBP_comm] },
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
    -- 実行関数は step 8 の点を step 9-11 の後で置き、最終の木で妥当でなければ調整後の start を使う。
    -- 関係は本文の順（step 8 で置いてから step 9-11）で書いてあり、点が step 9-11 で動かないこと
    -- （`newBP_fixed_removeEach`、`newBP_ne_start`、`newBP_ne_end`）と、点が妥当であること
    -- （`deleteContentsNewBP_valid`）から、実行関数がそれを満たす（`rangeDeleteContents_result_sound`）。
    spec := [``Dom.Spec.DeleteContentsResult, ``Dom.Spec.NodesToRemove, ``Dom.Spec.Contained,
             ``Dom.Spec.DeleteNewBP, ``Dom.Spec.rangeDeleteContents_result_sound] },
  { alg := "concept-range-insert"
    impl := [``Dom.rangeInsertNode, ``Dom.ensurePreInsertionValidity, ``Dom.preInsert,
             ``Dom.remove, ``Dom.siblingBP]
    spec := [``Dom.Spec.InsertNodeResult, ``Dom.Spec.InsertNodeTail, ``Dom.Spec.NewOffset,
             ``Dom.Spec.InsertNodeHierarchyError, ``Dom.Spec.ChildAtOffset]
    -- 実行関数は newOffset を前もって数えず、step 13 で「入った最後の node の直後」（`siblingBP`）として求める。
    -- 関係 `InsertNodeTail` は本文どおり step 10-11 で数えて step 13 で使う形で書いてあり、
    -- `rangeInsertNode_result_sound` が実行関数がそれを満たすことを示す。
    omitted := [("7", .todo "Text node の split（§4.11 split a Text node）が model に無い。start node が Text なら step 6 の validity を通った後で outsideModel を返す")] },
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
