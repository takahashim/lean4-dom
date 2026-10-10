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
  /- §4.11 Text -/
  { alg := "concept-text-split"
    impl := [``Dom.splitText, ``Dom.splitTextAdjust, ``Dom.splitTextRange, ``Dom.splitTextBP,
             ``Dom.splitTextMoved, ``Dom.guardBP]
    approx := [("4", loneSurrogate),
               ("7.1", "insert の代わりに pre-insert を使う。parent は Text の親（Element か DocumentFragment）なので検査は通り、参照する child（node の次の兄弟）は新しい Text ではないので insert と同じ"),
               ("7.2-7.5", "動かした先の boundary point が妥当でなければ動かさない（admissible な状態では必ず妥当なので、観測できる振る舞いは同じ。妥当性の保存を insert 後の木の形を追わずに示すための検査）")] },
  { alg := "dom-text-splittext"
    impl := [``Dom.splitText] },
  { alg := "contiguous-text-nodes"
    impl := [``Dom.contiguousTextNodes, ``Dom.contiguousTextNodes.isTextNode] },
  { alg := "dom-text-wholetext"
    impl := [``Dom.wholeText, ``Dom.contiguousTextNodes] },
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
  -- createTextNode の受け手の WebIDL の検査は `Dom.Exec.idlCheck` が行う。実行関数に残る guard は model の都合。
  { alg := "create-a-text-node"
    impl := [``Dom.createTextNode, ``Dom.withFresh] },
  /- §4.14 Comment -/
  -- createComment の受け手の WebIDL の検査は `Dom.Exec.idlCheck` が行う。実行関数に残る guard は model の都合。
  { alg := "create-a-comment-node"
    impl := [``Dom.createComment, ``Dom.withFresh] }
]

def exclusions : List Exclusion := [
  { target := "concept-child-text-content",
    reason := .todo "child text content を計算する関数が無い" },
  { target := "dom-text-text", reason := .host },
  -- §4.13。model の NodeData は target も attribute map も持たず、PI を作る関数も無い。
  { target := "interface-processinginstruction",
    reason := .todo "ProcessingInstruction の target は持ち `getProperty` で読める（`piTarget`）が、attribute map と createProcessingInstruction が無い（XML Name production も無い）" },
  { target := "dom-comment-comment", reason := .host }
]

end Trace.Dom.CharacterData
