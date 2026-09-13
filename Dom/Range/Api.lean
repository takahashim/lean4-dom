import Dom.Range.BoundaryPoint

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

end Dom
