import Dom.Basic.Exception
import Dom.Basic.WellFormed

/-!
# DOM の状態

PLAN §8.1。木だけでなく、木の変更に追随する live object も含めた状態を扱う。

Phase 4 までの `Tree` に対する操作は、Phase 5 でこの `DOMState` に持ち上げる。
Phase 2 の primitive（`detach`, `insertAt`, `setOwnerDocument`）は木だけを変えるので
`Tree` の上に残し、§4.2.3 の algorithm と public API を `DOMState` の上に置く。

構造体をここにまとめてあるのは、`Range/` と `Traversal/` の両方から参照されるためである。
それぞれの意味論は `Dom/Range/BoundaryPoint.lean` と
`Dom/Traversal/NodeIterator.lean` で定義する。
-/

namespace Dom

/-- DOM Standard §5.3 の boundary point。 -/
structure BoundaryPoint where
  node : NodeId
  offset : Nat
deriving DecidableEq, Repr, Inhabited

/-- DOM Standard §5.5 の live range。 -/
structure RangeState where
  start : BoundaryPoint
  «end» : BoundaryPoint
deriving DecidableEq, Repr, Inhabited

/-- DOM Standard §6.1 の `NodeIterator`。Phase 6 で意味論を入れる。 -/
structure IteratorState where
  root : NodeId
  reference : NodeId
  pointerBeforeReference : Bool
deriving DecidableEq, Repr, Inhabited

/-- 木と live object を合わせた状態。 -/
structure DOMState where
  tree : Tree
  ranges : List RangeState := []
  iterators : List IteratorState := []
deriving Repr, Inhabited

namespace DOMState

/-- 木だけを差し替える。live object は変えない。 -/
def withTree (s : DOMState) (t : Tree) : DOMState := { s with tree := t }

@[simp] theorem withTree_tree (s : DOMState) (t : Tree) : (s.withTree t).tree = t := rfl

@[simp] theorem withTree_ranges (s : DOMState) (t : Tree) : (s.withTree t).ranges = s.ranges := rfl

@[simp] theorem withTree_iterators (s : DOMState) (t : Tree) :
    (s.withTree t).iterators = s.iterators := rfl

/-- 木だけを変える操作を状態に持ち上げる。 -/
def mapTree (s : DOMState) (f : Tree → Except DOMException Tree) : Except DOMException DOMState :=
  match f s.tree with
  | .error e => .error e
  | .ok t => .ok (s.withTree t)

/-- `s` の木が well-formed であること。 -/
abbrev WellFormedState (s : DOMState) : Prop := WellFormed s.tree

theorem mapTree_eq_ok {s s' : DOMState} {f : Tree → Except DOMException Tree}
    (h : s.mapTree f = .ok s') : f s.tree = .ok s'.tree ∧ s' = s.withTree s'.tree := by
  unfold mapTree at h
  split at h
  · simp at h
  · next t ht =>
    have hs : s.withTree t = s' := Except.ok.inj h
    subst hs
    exact ⟨ht, rfl⟩

theorem mapTree_error {s : DOMState} {f : Tree → Except DOMException Tree} {e : DOMException}
    (h : f s.tree = .error e) : s.mapTree f = .error e := by
  unfold mapTree; rw [h]

end DOMState

end Dom
