import Trace.Basic
import Dom

/-!
# §4.10 CharacterData・§4.11 Text・§4.12 CDATASection・§4.13 ProcessingInstruction・§4.14 Comment
-/

namespace Trace.Dom.CharacterData

open Trace

/-- lone surrogate の近似（`docs/threats-to-validity.md`）。 -/
private def loneSurrogate : String :=
  "offset か offset + count が surrogate pair の途中なら、結果の文字列を Lean の String で表せないので __outsideModel__ を返す"

def entries : List Entry := [
  /- §4.10 CharacterData -/
  { alg := "concept-cd-replace"
    impl := [``Dom.replaceData, ``Dom.adjustedCount, ``Dom.spliceData?,
             ``Dom.queueCharacterDataRecord, ``Dom.replaceDataAdjustRange,
             ``Dom.replaceDataAdjustBP]
    spec := [``Dom.Spec.ReplaceDataSpec, ``Dom.Spec.ReplaceDataResult]
    omitted := [("12", .todo "ProcessingInstruction の attribute map（update attributes from data）が model に無い"),
             ("13", .hook)]
    approx := [("5-7", loneSurrogate)] },
  { alg := "concept-cd-substring"
    impl := [``Dom.substringData, ``Dom.adjustedCount]
    approx := [("3-4", loneSurrogate)] },
  { alg := "dom-characterdata-data"
    impl := [``Dom.NodeData.data, ``Dom.setData]
    spec := [``Dom.Spec.SetDataResult] },
  { alg := "dom-characterdata-length"
    impl := [``Dom.NodeData.length, ``Dom.Utf16.length] },
  { alg := "dom-characterdata-substringdata"
    impl := [``Dom.substringData] },
  { alg := "dom-characterdata-appenddata"
    impl := [``Dom.appendData]
    spec := [``Dom.Spec.AppendDataResult] },
  { alg := "dom-characterdata-insertdata"
    impl := [``Dom.insertData]
    spec := [``Dom.Spec.ReplaceDataResult] },
  { alg := "dom-characterdata-deletedata"
    impl := [``Dom.deleteData]
    spec := [``Dom.Spec.ReplaceDataResult] },
  { alg := "dom-characterdata-replacedata"
    impl := [``Dom.replaceData]
    spec := [``Dom.Spec.ReplaceDataResult] },
  /- §4.11 Text -/
  { alg := "exclusive-text-node"
    impl := [``Dom.isExclusiveText]
    spec := [``Dom.Spec.ExclusiveText] },
  { alg := "contiguous-exclusive-text-nodes"
    impl := [``Dom.followingTexts, ``Dom.isExclusiveText]
    spec := [``Dom.Spec.FollowingContiguousTexts]
    approx := [("*", "node より後ろの兄弟だけを集める（normalize が run の先頭から呼ぶので前側は空になる）。前後両側を集める関数は無い")] },
  { alg := "concept-descendant-text-content"
    impl := [``Dom.descendantTextContent] },
  { alg := "create-a-text-node"
    impl := [``Dom.createTextNode, ``Dom.withFresh]
    approx := [("1", "createTextNode は受け手が Document であることも確かめる（WebIDL の受け手検査。仕様の algorithm には無い）")] },
  /- §4.14 Comment -/
  { alg := "create-a-comment-node"
    impl := [``Dom.createComment, ``Dom.withFresh]
    approx := [("1", "createComment は受け手が Document であることも確かめる（WebIDL の受け手検査。仕様の algorithm には無い）")] }
]

def exclusions : List Exclusion := [
  { target := "contiguous-text-nodes",
    reason := .todo "contiguous Text nodes（CDATASection を含む前後両側）を集める関数が無い。使う側の wholeText も未実装" },
  { target := "concept-child-text-content",
    reason := .todo "child text content を計算する関数が無い" },
  { target := "dom-text-text", reason := .host },
  { target := "concept-text-split",
    reason := .todo "split a Text node が無い（docs/status.md の未着手。固定 scenario でも skip）" },
  { target := "dom-text-splittext",
    reason := .todo "splitText() が無い（split a Text node が未実装）" },
  { target := "dom-text-wholetext",
    reason := .todo "wholeText の getter が無い" },
  -- §4.13。model の NodeData は target も attribute map も持たず、PI を作る関数も無い。
  { target := "interface-processinginstruction",
    reason := .todo "ProcessingInstruction の target・attribute map・createProcessingInstruction が無い（XML Name production も無い）" },
  { target := "dom-comment-comment", reason := .host }
]

end Trace.Dom.CharacterData
