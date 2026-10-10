import Dom.Mutation.Api
import Dom.Mutation.Create
import Dom.CharacterData.ReplaceData
import Dom.Query.Property

/-!
# `Text.splitText()` と `wholeText`（§4.11）

"split a Text node" は、offset から後ろの data で新しい Text を作り、node の次の兄弟の前に入れ、
live range を新しい Text へ移してから、node の data を offset で切る。

step 7.2–7.5 の boundary point の調整は、動かした先が妥当（node が木にあり offset が length 以下）で
なければ動かさない。admissible な状態ではこの条件は必ず成り立つ（新しい Text の length は count で、
動かす offset は count 以下。parent の children には新しい Text が index + 1 に入っている）ので、
観測できる振る舞いは本文と同じである。検査を入れてあるのは、妥当性の保存を insert の後の木の形を
追わずに示すためである。
-/

namespace Dom

/-- "split a Text node" step 7.2–7.5 の boundary point の移し先（検査の前）。 -/
def splitTextMoved (node newNode parent : NodeId) (offset idx : Nat) (bp : BoundaryPoint) :
    BoundaryPoint :=
  if bp.node = node ∧ offset < bp.offset then { node := newNode, offset := bp.offset - offset }
  else if bp.node = parent ∧ bp.offset = idx + 1 then { bp with offset := bp.offset + 1 }
  else bp

/-- 移し先が妥当でなければ元の boundary point のまま。 -/
def guardBP (t : Tree) (bp moved : BoundaryPoint) : BoundaryPoint :=
  if checkValidBoundaryPoint t moved then moved else bp

/-- "split a Text node" step 7.2–7.5 の boundary point。 -/
def splitTextBP (t : Tree) (node newNode parent : NodeId) (offset idx : Nat)
    (bp : BoundaryPoint) : BoundaryPoint :=
  guardBP t bp (splitTextMoved node newNode parent offset idx bp)

/-- `splitTextBP` を range の両端に当てる。 -/
def splitTextRange (t : Tree) (node newNode parent : NodeId) (offset idx : Nat) (r : RangeState) :
    RangeState :=
  { start := splitTextBP t node newNode parent offset idx r.start
    «end» := splitTextBP t node newNode parent offset idx r.«end» }

/-- step 7.2–7.5：live range を調整する。idx は node の index。 -/
def splitTextAdjust (s : DOMState) (node newNode parent : NodeId) (offset : Nat) : DOMState :=
  { s with ranges :=
      s.ranges.map (splitTextRange s.tree node newNode parent offset ((index s.tree node).getD 0)) }

/--
DOM Standard §4.11 "split a Text node"。返り値は新しい Text。

step 7.1 の insert は pre-insert で行う。parent は Text の親なので Element か DocumentFragment で、
pre-insert の検査は通り、参照する child（node の次の兄弟）は新しい Text ではないので、本文の insert と同じ。
-/
def splitText (s : DOMState) (node : NodeId) (offset : Nat) :
    Except DOMException (NodeId × DOMState) :=
  match s.tree.get? node with
  | none => .error .notFoundError
  | some d =>
    if !d.kind.isText then .error .notFoundError
    -- step 1-2
    else if d.length < offset then .error .indexSizeError
    else
      -- step 3-4
      match substringData s.tree node offset (d.length - offset) with
      | .error e => .error e
      | .ok newData =>
        -- step 5
        match createTextNode s d.ownerDocument newData with
        | .error e => .error e
        | .ok (newNode, s₁) =>
          -- step 6-7
          match parentOf s₁.tree node with
          | none =>
            -- step 8-9
            match replaceData s₁ node offset (d.length - offset) "" with
            | .error e => .error e
            | .ok s₄ => .ok (newNode, s₄)
          | some parent =>
            -- step 7.1
            match preInsert s₁ newNode parent (nextSibling s₁.tree node) with
            | .error e => .error e
            | .ok s₂ =>
              -- step 7.2-7.5、8-9
              match replaceData (splitTextAdjust s₂ node newNode parent offset) node offset
                  (d.length - offset) "" with
              | .error e => .error e
              | .ok s₄ => .ok (newNode, s₄)

/--
§4.11 "contiguous Text nodes"：node と、前後に連続する Text（CDATASection を含む）の兄弟を tree order に
並べたもの。parent が無ければ node だけ。
-/
def contiguousTextNodes (t : Tree) (n : NodeId) : List NodeId :=
  match parentOf t n with
  | none => [n]
  | some p =>
    match Dom.ListUtil.splitAt? (childrenOf t p) n with
    | none => [n]
    | some (before, after) =>
      (before.reverse.takeWhile (isTextNode t)).reverse ++ n :: after.takeWhile (isTextNode t)
where
  /-- Text か CDATASection。 -/
  isTextNode (t : Tree) (m : NodeId) : Bool :=
    match kindOf t m with
    | some k => k.isText
    | none => false

/-- §4.11 `wholeText`：contiguous Text nodes の data の連結。 -/
def wholeText (t : Tree) (n : NodeId) : String :=
  String.join ((contiguousTextNodes t n).map fun m =>
    match t.get? m with
    | some d => d.data
    | none => "")

end Dom
