import Dom.Basic.State
import Dom.Basic.Order

/-!
# boundary point

DOM Standard §5.3（boundary point）と §5.5（Range）のうち、
本 model が扱う部分を定義する。

PLAN §8.1。node の length は kind で決まり（`Dom/Basic/NodeId.lean` の `NodeData.length`）、
boundary point の validity は「node が store に存在し、offset が node の length 以下」である。
-/

namespace Dom

/-- boundary point が指す node が木にあり、offset が length 以下であること。 -/
def ValidBoundaryPoint (t : Tree) (bp : BoundaryPoint) : Prop :=
  ∃ d, t.get? bp.node = some d ∧ bp.offset ≤ d.length

/-- 実行時に検査するための boolean 版。 -/
def checkValidBoundaryPoint (t : Tree) (bp : BoundaryPoint) : Bool :=
  match t.get? bp.node with
  | none => false
  | some d => bp.offset ≤ d.length

theorem checkValidBoundaryPoint_iff (t : Tree) (bp : BoundaryPoint) :
    checkValidBoundaryPoint t bp = true ↔ ValidBoundaryPoint t bp := by
  unfold checkValidBoundaryPoint ValidBoundaryPoint
  cases h : t.get? bp.node with
  | none => simp
  | some d => simp

/-! ## boundary point の比較 -/

/--
`a` が `b` の ancestor のとき、`b` へ至る経路上にある `a` の子。

DOM Standard §5.3 boundary point position の step 4
「Let child be nodeB. While child is not a child of nodeA, set child to its parent.」
に対応する。`b` の inclusive ancestor を下から順に見て、parent が `a` である最初のものを返す。
-/
def childTowards (t : Tree) (a b : NodeId) : Option NodeId :=
  (b :: ancestors t b).find? fun x => parentOf t x == some a

/--
DOM Standard §5.3 boundary point position の step 4-5。

`a.node` が `b.node` を follow していない場合（かつ両者が異なる場合）に使う。
-/
def bpPositionDown (t : Tree) (a b : BoundaryPoint) : Ordering :=
  match childTowards t a.node b.node with
  | some c => if (index t c).getD 0 < a.offset then .gt else .lt
  | none => .lt

/--
DOM Standard §5.3 の boundary point position。

`.lt` が before、`.eq` が equal、`.gt` が after に対応する。
仕様の step 3 は自分自身を引数を入れ替えて呼ぶが、
`a.node` が `b.node` を follow しているなら `b.node` は `a.node` を follow しないので、
入れ子は高々一段である。ここでは `bpPositionDown` を直接呼ぶ形で書き下している。
-/
def bpPosition (t : Tree) (a b : BoundaryPoint) : Ordering :=
  if a.node = b.node then compare a.offset b.offset
  else if precedes t b.node a.node then (bpPositionDown t b a).swap
  else bpPositionDown t a b

/--
boundary point の順序。`a` が `b` より前か等しいこと。

PLAN §8.1 に従い、両者が同じ root に属することも条件に含める。
仕様の position の算法は同じ root であることを前提にしている。
-/
def BoundaryLE (t : Tree) (a b : BoundaryPoint) : Prop :=
  root t a.node = root t b.node ∧ bpPosition t a b ≠ .gt

def checkBoundaryLE (t : Tree) (a b : BoundaryPoint) : Bool :=
  root t a.node == root t b.node && !(bpPosition t a b == .gt)

theorem checkBoundaryLE_iff (t : Tree) (a b : BoundaryPoint) :
    checkBoundaryLE t a b = true ↔ BoundaryLE t a b := by
  simp [checkBoundaryLE, BoundaryLE]

/-! ## range の validity -/

/-- 一つの range が満たすべき性質。 -/
def RangeValid (t : Tree) (r : RangeState) : Prop :=
  ValidBoundaryPoint t r.start ∧ ValidBoundaryPoint t r.«end» ∧ BoundaryLE t r.start r.«end»

/--
両端が木の中にあること。

`RangeValid` のうち、順序を除いた部分。
mutation algorithm がこれを保つことを `Dom/Properties/Range.lean` で証明する。
-/
def EndpointsValid (t : Tree) (r : RangeState) : Prop :=
  ValidBoundaryPoint t r.start ∧ ValidBoundaryPoint t r.«end»

/-- PLAN §8.1 の `RangesValid`。 -/
def RangesValid (s : DOMState) : Prop :=
  ∀ r ∈ s.ranges, RangeValid s.tree r

/-- `RangesValid` のうち両端が木の中にある部分。 -/
def RangeEndpointsValid (s : DOMState) : Prop :=
  ∀ r ∈ s.ranges, EndpointsValid s.tree r

theorem RangesValid.endpoints {s : DOMState} (h : RangesValid s) : RangeEndpointsValid s :=
  fun r hr => ⟨(h r hr).1, (h r hr).2.1⟩

/--
実行時の検査のうち、両端が木の中にあることだけを見る部分。

順序（`BoundaryLE`）は **仕様の invariant ではない**。
`setStart` / `setEnd` は順序を保つように collapse するが、
木を変える algorithm の側にはそのような正規化が無く、
insert step 5 と step 7 の adopt→remove の順序のせいで
start と end が逆転することがある（`docs/status.md` 参照）。
differential testing の各 step で model の不具合として扱ってよいのはこちらだけである。
-/
def checkRangeEndpointsValid (s : DOMState) : Bool :=
  s.ranges.all fun r =>
    checkValidBoundaryPoint s.tree r.start && checkValidBoundaryPoint s.tree r.«end»

theorem checkRangeEndpointsValid_iff (s : DOMState) :
    checkRangeEndpointsValid s = true ↔ RangeEndpointsValid s := by
  simp only [checkRangeEndpointsValid, List.all_eq_true, Bool.and_eq_true,
    checkValidBoundaryPoint_iff, RangeEndpointsValid, EndpointsValid]

/-- 両端が木の中にあり、かつ順序も付いていること。 -/
def checkRangesValid (s : DOMState) : Bool :=
  s.ranges.all fun r =>
    checkValidBoundaryPoint s.tree r.start && checkValidBoundaryPoint s.tree r.«end» &&
      checkBoundaryLE s.tree r.start r.«end»

theorem checkRangesValid_iff (s : DOMState) : checkRangesValid s = true ↔ RangesValid s := by
  simp only [checkRangesValid, List.all_eq_true, Bool.and_eq_true,
    checkValidBoundaryPoint_iff, checkBoundaryLE_iff, RangesValid, RangeValid]
  constructor
  · intro h r hr
    obtain ⟨⟨h1, h2⟩, h3⟩ := h r hr
    exact ⟨h1, h2, h3⟩
  · intro h r hr
    obtain ⟨h1, h2, h3⟩ := h r hr
    exact ⟨⟨h1, h2⟩, h3⟩

end Dom
