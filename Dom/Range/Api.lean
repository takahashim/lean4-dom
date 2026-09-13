import Dom.Range.BoundaryPoint
import Dom.Mutation.Algorithms
import Dom.CharacterData.ReplaceData

/-!
# `Range` の API（§5.5）

boundary point を動かす側の method。木を変えるもの（`deleteContents` ほか）は別に置く。

model の range は `DOMState.ranges` の要素で、scenario が与えた順に番号で指す。
`Range` object を作る API（`createRange` / `cloneRange`）は object を生むので
roadmap §13.2 の対象外であり、ここでは既にある range を動かすだけである。

## 仕様の要点

"set the start" と "set the end" は、**新しい端点が反対の端より後ろ（前）なら
反対の端もそこへ動かす**。root が違う場合も同じで、range 全体が新しい木へ移る。
この正規化があるので `start ≤ end` は API 経由では保たれる。
木の側の変更（`insert`）では保たれないことが §8 の negative result である。
-/

namespace Dom

/-- DOM Standard §5.5 "set the start/end of a range" の step 1-2。 -/
def rangeBoundaryError (t : Tree) (bp : BoundaryPoint) : Option DOMException :=
  match t.get? bp.node with
  | none => some .notFoundError
  | some d =>
    if d.kind == .documentType then some .invalidNodeTypeError
    else if d.length < bp.offset then some .indexSizeError
    else none

/-- 新しい端点が反対の端より後ろか、別の木にあるか。 -/
def rangeNeedsCollapse (t : Tree) (bp other : BoundaryPoint) : Bool :=
  root t bp.node != root t other.node || bpPosition t bp other == .gt

/-- DOM Standard §5.5 "set the start of a range" の step 3-5。 -/
def setStartBP (t : Tree) (r : RangeState) (bp : BoundaryPoint) : RangeState :=
  if rangeNeedsCollapse t bp r.«end» then { start := bp, «end» := bp }
  else { r with start := bp }

/-- DOM Standard §5.5 "set the end of a range" の step 3-5。 -/
def setEndBP (t : Tree) (r : RangeState) (bp : BoundaryPoint) : RangeState :=
  if rangeNeedsCollapse t r.start bp then { start := bp, «end» := bp }
  else { r with «end» := bp }

/-- 番号で指した range を置き換える。 -/
def withRange (s : DOMState) (i : Nat) (r : RangeState) : DOMState :=
  { s with ranges := s.ranges.set i r }

/-- DOM Standard §5.5 `Range.setStart(node, offset)`。 -/
def rangeSetStart (s : DOMState) (i : Nat) (bp : BoundaryPoint) :
    Except DOMException DOMState :=
  match s.ranges[i]? with
  | none => .error .notFoundError
  | some r =>
    match rangeBoundaryError s.tree bp with
    | some e => .error e
    | none => .ok (withRange s i (setStartBP s.tree r bp))

/-- DOM Standard §5.5 `Range.setEnd(node, offset)`。 -/
def rangeSetEnd (s : DOMState) (i : Nat) (bp : BoundaryPoint) :
    Except DOMException DOMState :=
  match s.ranges[i]? with
  | none => .error .notFoundError
  | some r =>
    match rangeBoundaryError s.tree bp with
    | some e => .error e
    | none => .ok (withRange s i (setEndBP s.tree r bp))

/--
`node` の直前・直後を指す boundary point。

`setStartBefore` ほかの step 1-3 にあたる。parent が無ければ `none` で、
呼び出し側が `InvalidNodeTypeError` にする。
-/
def siblingBP (t : Tree) (n : NodeId) (after : Bool) : Option BoundaryPoint :=
  match parentOf t n, index t n with
  | some p, some idx => some ⟨p, if after then idx + 1 else idx⟩
  | _, _ => none

/-- DOM Standard §5.5 `Range.setStartBefore` / `setStartAfter`。 -/
def rangeSetStartSibling (s : DOMState) (i : Nat) (n : NodeId) (after : Bool) :
    Except DOMException DOMState :=
  match siblingBP s.tree n after with
  | none => .error .invalidNodeTypeError
  | some bp => rangeSetStart s i bp

/-- DOM Standard §5.5 `Range.setEndBefore` / `setEndAfter`。 -/
def rangeSetEndSibling (s : DOMState) (i : Nat) (n : NodeId) (after : Bool) :
    Except DOMException DOMState :=
  match siblingBP s.tree n after with
  | none => .error .invalidNodeTypeError
  | some bp => rangeSetEnd s i bp

/-- DOM Standard §5.5 `Range.collapse(toStart)`。 -/
def rangeCollapse (s : DOMState) (i : Nat) (toStart : Bool) :
    Except DOMException DOMState :=
  match s.ranges[i]? with
  | none => .error .notFoundError
  | some r =>
    let bp := if toStart then r.start else r.«end»
    .ok (withRange s i { start := bp, «end» := bp })

/-- DOM Standard §5.5 `Range.selectNode(node)`。 -/
def rangeSelectNode (s : DOMState) (i : Nat) (n : NodeId) : Except DOMException DOMState :=
  match s.ranges[i]? with
  | none => .error .notFoundError
  | some _ =>
    match parentOf s.tree n, index s.tree n with
    | some p, some idx =>
      .ok (withRange s i { start := ⟨p, idx⟩, «end» := ⟨p, idx + 1⟩ })
    | _, _ => .error .invalidNodeTypeError

/-- DOM Standard §5.5 `Range.selectNodeContents(node)`。 -/
def rangeSelectNodeContents (s : DOMState) (i : Nat) (n : NodeId) :
    Except DOMException DOMState :=
  match s.ranges[i]?, s.tree.get? n with
  | none, _ => .error .notFoundError
  | _, none => .error .notFoundError
  | some _, some d =>
    if d.kind == .documentType then .error .invalidNodeTypeError
    else .ok (withRange s i { start := ⟨n, 0⟩, «end» := ⟨n, d.length⟩ })

/-! ## 値を返すだけの method -/

/--
DOM Standard §5.5 `Range.compareBoundaryPoints(how, sourceRange)`。

`how` は 0 START_TO_START / 1 START_TO_END / 2 END_TO_END / 3 END_TO_START。
step 3 の組み合わせは対称ではない。1 は「this の end と source の start」、
3 は「this の start と source の end」である。
-/
def rangeCompareBoundaryPoints (s : DOMState) (i : Nat) (how : Nat) (j : Nat) :
    Except DOMException Int :=
  match s.ranges[i]?, s.ranges[j]? with
  | some r, some other =>
    if 3 < how then .error .notSupportedError
    else if root s.tree r.start.node != root s.tree other.start.node then
      .error .wrongDocumentError
    else
      let a := if how == 1 || how == 2 then r.«end» else r.start
      let b := if how == 2 || how == 3 then other.«end» else other.start
      .ok (match bpPosition s.tree a b with
           | .lt => -1
           | .eq => 0
           | .gt => 1)
  | _, _ => .error .notFoundError

/-- DOM Standard §5.5 `Range.comparePoint(node, offset)`。 -/
def rangeComparePoint (s : DOMState) (i : Nat) (bp : BoundaryPoint) :
    Except DOMException Int :=
  match s.ranges[i]? with
  | none => .error .notFoundError
  | some r =>
    if s.tree.get? bp.node |>.isNone then .error .notFoundError
    else if root s.tree bp.node != root s.tree r.start.node then .error .wrongDocumentError
    else
      match rangeBoundaryError s.tree bp with
      | some e => .error e
      | none =>
        .ok (if bpPosition s.tree bp r.start == .lt then -1
             else if bpPosition s.tree bp r.«end» == .gt then 1
             else 0)


/-- DOM Standard §5.5 `Range.isPointInRange(node, offset)`。 -/
def rangeIsPointInRange (s : DOMState) (i : Nat) (bp : BoundaryPoint) :
    Except DOMException Bool :=
  match s.ranges[i]? with
  | none => .error .notFoundError
  | some r =>
    -- step 1。別の木なら例外にせず false を返す。
    if root s.tree bp.node != root s.tree r.start.node then .ok false
    else
      match rangeBoundaryError s.tree bp with
      | some e => .error e
      | none => .ok (!(bpPosition s.tree bp r.start == .lt) && !(bpPosition s.tree bp r.«end» == .gt))

/-- DOM Standard §5.5 `Range.intersectsNode(node)`。 -/
def rangeIntersectsNode (s : DOMState) (i : Nat) (n : NodeId) : Except DOMException Bool :=
  match s.ranges[i]? with
  | none => .error .notFoundError
  | some r =>
    if s.tree.get? n |>.isNone then .error .notFoundError
    else if root s.tree n != root s.tree r.start.node then .ok false
    else
      match parentOf s.tree n, index s.tree n with
      -- step 3。root は必ず交わる。
      | none, _ => .ok true
      | _, none => .ok true
      | some p, some idx =>
        .ok (bpPosition s.tree ⟨p, idx⟩ r.«end» == .lt &&
             bpPosition s.tree ⟨p, idx + 1⟩ r.start == .gt)

/-! ## `deleteContents` -/

/-- `a` が `b` の inclusive ancestor か。 -/
def isInclusiveAncestorB (t : Tree) (a b : NodeId) : Bool :=
  a == b || (ancestors t b).contains a

/--
DOM Standard §5.5 "contained"。

node 全体が range の中に入っていること。
-/
def containedInRange (t : Tree) (r : RangeState) (n : NodeId) : Bool :=
  root t n == root t r.start.node &&
    bpPosition t ⟨n, 0⟩ r.start == .gt &&
    bpPosition t ⟨n, lengthOf t n⟩ r.«end» == .lt

/--
DOM Standard §5.5 `deleteContents` の step 4。

range に含まれる node を tree order で並べ、親も含まれるものを落とす。
-/
def nodesToRemove (t : Tree) (r : RangeState) : List NodeId :=
  (treeOrder t r.start.node).filter fun n =>
    containedInRange t r n &&
      !(match parentOf t n with
        | some p => containedInRange t r p
        | none => false)

/--
DOM Standard §5.5 `deleteContents` の step 5-6。

start node が end node の inclusive ancestor ならその場に潰れる。
そうでなければ、start 側の祖先を「end node の inclusive ancestor の子」になるまで上り、
その次の位置に潰れる。
-/
def deleteContentsNewBP (t : Tree) (r : RangeState) : BoundaryPoint :=
  if isInclusiveAncestorB t r.start.node r.«end».node then r.start
  else
    let ref := ((r.start.node :: ancestors t r.start.node).find? fun x =>
        match parentOf t x with
        | none => true
        | some p => isInclusiveAncestorB t p r.«end».node).getD r.start.node
    match parentOf t ref, index t ref with
    | some p, some idx => ⟨p, idx + 1⟩
    | _, _ => r.start

/--
DOM Standard §5.5 `Range.deleteContents()`。

step 10 が置く boundary point が最終状態でも妥当であることは仕様の帰結だが、
本 model ではまだ証明していない。妥当でなければ live range の調整が残した端点を使う
（そちらは `remove_preserves_endpoints` などで妥当である）。
差分テストではこの枝に落ちたことは無い。
-/
def rangeDeleteContents (s : DOMState) (i : Nat) : Except DOMException DOMState :=
  match s.ranges[i]? with
  | none => .error .notFoundError
  | some r =>
    -- step 1
    if r.start == r.«end» then .ok s
    else
      match s.tree.get? r.start.node, s.tree.get? r.«end».node with
      | some ds, some de =>
        -- step 3
        if r.start.node == r.«end».node && ds.kind.isCharacterData then
          replaceData s r.start.node r.start.offset (r.«end».offset - r.start.offset) ""
        else
          let newBP := deleteContentsNewBP s.tree r
          let toRemove := nodesToRemove s.tree r
          -- step 7
          match (if ds.kind.isCharacterData then
                   replaceData s r.start.node r.start.offset (ds.length - r.start.offset) ""
                 else .ok s) with
          | .error e => .error e
          | .ok s₁ =>
            -- step 8
            match removeEach s₁ toRemove with
            | .error e => .error e
            | .ok s₂ =>
              -- step 9
              match (if de.kind.isCharacterData then
                       replaceData s₂ r.«end».node 0 r.«end».offset ""
                     else .ok s₂) with
              | .error e => .error e
              | .ok s₃ =>
                -- step 10
                match s₃.ranges[i]? with
                | none => .error .notFoundError
                | some r₃ =>
                  let bp := if checkValidBoundaryPoint s₃.tree newBP then newBP else r₃.start
                  .ok (withRange s₃ i { start := bp, «end» := bp })
      | _, _ => .error .notFoundError

/-! ## `insertNode` -/

/--
DOM Standard §5.5 `Range.insertNode(node)`。

step 7（start node が Text なら offset で split する）は node を作るので
roadmap §13.2 の対象外である。start node が Text の場合は `outsideModel` を返す。
ただし step 1 の「parent の無い Text」は先に検査するので、そちらは `HierarchyRequestError` になる。

step 10-11 の newOffset は「入った node の最後の次」に等しい。
model はその形で書く（`siblingBP`）。そうすると端点の妥当性が
`index` の上界から出るので、step 13 が置く boundary point を実行時に検査しなくてよい。
DocumentFragment が空なら何も入らないので、range は collapsed のまま動かない。
-/
def rangeInsertNode (s : DOMState) (i : Nat) (node : NodeId) : Except DOMException DOMState :=
  match s.ranges[i]? with
  | none => .error .notFoundError
  | some r =>
    match s.tree.get? r.start.node with
    | none => .error .notFoundError
    | some ds =>
      -- step 1
      if ds.kind == .processingInstruction || ds.kind == .comment ||
          (ds.kind == .text && (parentOf s.tree r.start.node).isNone) ||
          r.start.node == node then
        .error .hierarchyRequestError
      -- step 3 と step 7（split text）
      else if ds.kind == .text then .error .outsideModel
      else
        -- step 4-5。start node は Text ではないので parent は start node 自身である。
        let referenceNode := ds.children[r.start.offset]?
        let parent := r.start.node
        -- step 6
        match ensurePreInsertionValidity s.tree node parent referenceNode [] with
        | .error e => .error e
        | .ok () =>
          -- step 8
          let ref := if referenceNode == some node then nextSibling s.tree node else referenceNode
          -- step 9
          match (if (parentOf s.tree node).isSome then remove s node else .ok s) with
          | .error e => .error e
          | .ok s₁ =>
            -- step 10-11 に使う「最後に入る node」
            let last :=
              match s₁.tree.get? node with
              | some nd => if nd.kind == NodeKind.documentFragment then nd.children.getLast? else some node
              | none => some node
            -- step 12
            match preInsert s₁ node parent ref with
            | .error e => .error e
            | .ok s₂ =>
              -- step 13
              match s₂.ranges[i]? with
              | none => .error .notFoundError
              | some r₂ =>
                if r₂.start == r₂.«end» then
                  match last.bind (fun n => siblingBP s₂.tree n true) with
                  | none => .ok s₂
                  | some bp => .ok (withRange s₂ i { r₂ with «end» := bp })
                else .ok s₂

/-! ## stringifier -/

/--
DOM Standard §5.5 `Range` の stringification behavior。

step 4 の「contained な Text を tree order で」は `nodesToRemove` と同じ
`containedInRange` で決まる。**common ancestor の子だけではない。**

start / end の Text を切り出すところは UTF-16 の code unit で数えるので、
surrogate pair の途中を指していれば `outsideModel` になる（`substringData` と同じ）。
-/
def rangeToString (s : DOMState) (i : Nat) : Except DOMException String :=
  match s.ranges[i]? with
  | none => .error .notFoundError
  | some r =>
    match s.tree.get? r.start.node, s.tree.get? r.«end».node with
    | some ds, some de =>
      -- step 2
      if r.start.node == r.«end».node && ds.kind.isText then
        substringData s.tree r.start.node r.start.offset (r.«end».offset - r.start.offset)
      else
        -- step 3
        match (if ds.kind.isText then
                 substringData s.tree r.start.node r.start.offset (ds.length - r.start.offset)
               else .ok "") with
        | .error e => .error e
        | .ok head =>
          -- step 4
          let mid := ((treeOrder s.tree r.start.node).filterMap fun n =>
            match s.tree.get? n with
            | none => none
            | some d =>
              if d.kind.isText && containedInRange s.tree r n then some d.data else none).foldl
              (· ++ ·) ""
          -- step 5
          match (if de.kind.isText then
                   substringData s.tree r.«end».node 0 r.«end».offset
                 else .ok "") with
          | .error e => .error e
          | .ok tail => .ok (head ++ mid ++ tail)
    | _, _ => .error .notFoundError

end Dom
