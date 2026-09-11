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

/-! ## MutationObserver -/

/--
DOM Standard §4.3.1 の `MutationRecord` の type。

model は attribute を持たないので、`attributes` は扱わない。
-/
inductive RecordType where
  | childList
  | characterData
deriving DecidableEq, Repr, Inhabited

/--
DOM Standard §4.3.1 の `MutationRecord`。

`attributeName` / `attributeNamespace` は model が attribute を扱わないので省く。
-/
structure MutationRecord where
  type : RecordType
  target : NodeId
  addedNodes : List NodeId := []
  removedNodes : List NodeId := []
  previousSibling : Option NodeId := none
  nextSibling : Option NodeId := none
  oldValue : Option String := none
deriving DecidableEq, Repr, Inhabited

/--
DOM Standard §4.3.3 の registered observer。

仕様では node ごとの registered observer list だが、model では
`node` を持つ一つの list にまとめる。同じ node の登録は list の順に並ぶので、
仕様の「node の registered observer list を順に見る」はその部分列を見ることになる。

`transient` は transient registered observer であることを表す（remove step 20）。
`observer` は `DOMState.observers` の index である。
-/
structure Registration where
  node : NodeId
  observer : Nat
  subtree : Bool := false
  childList : Bool := false
  characterData : Bool := false
  characterDataOldValue : Bool := false
  transient : Bool := false
  /--
  仕様の transient registered observer の `source`。

  仕様は source registration そのものを持つが、
  一つの observer が一つの node に持つ非 transient な registration は高々一つなので
  （`observe` step 7 は既存のものの options を差し替える）、
  その node の id で一意に指せる。
  -/
  source : Option NodeId := none
deriving DecidableEq, Repr, Inhabited

/--
DOM Standard §4.3.2 の `MutationObserver`。

callback は model の対象外なので、record queue だけを持つ。
配送（queue a mutation observer microtask）も扱わないので、
record は `takeRecords` で取り出すまで貯まる。
-/
structure ObserverState where
  records : List MutationRecord := []
  /--
  仕様の `MutationObserver` の node list。

  `observe` が target を足す。加えて remove step 20 が transient を足した node も足す。
  仕様本文は remove step 20 で node list に触れないが、そう読まないと
  "notify mutation observers" step 5.2 と `observe` step 7.1 の掃除が
  transient を置いた node に届かない（`docs/traceability.md` の近似の表を参照）。
  -/
  nodeList : List NodeId := []
deriving DecidableEq, Repr, Inhabited

/-- 木と live object を合わせた状態。 -/
structure DOMState where
  tree : Tree
  ranges : List RangeState := []
  iterators : List IteratorState := []
  observers : List ObserverState := []
  registrations : List Registration := []
  /-- 仕様の agent の "mutation observer microtask queued"。 -/
  microtaskQueued : Bool := false
  /-- 仕様の agent の "pending mutation observers"。observer の index で持つ。 -/
  pendingObservers : List Nat := []
deriving Repr, Inhabited

namespace DOMState

/-- 木だけを差し替える。live object は変えない。 -/
def withTree (s : DOMState) (t : Tree) : DOMState := { s with tree := t }

@[simp] theorem withTree_tree (s : DOMState) (t : Tree) : (s.withTree t).tree = t := rfl

@[simp] theorem withTree_ranges (s : DOMState) (t : Tree) : (s.withTree t).ranges = s.ranges := rfl

@[simp] theorem withTree_iterators (s : DOMState) (t : Tree) :
    (s.withTree t).iterators = s.iterators := rfl

@[simp] theorem withTree_observers (s : DOMState) (t : Tree) :
    (s.withTree t).observers = s.observers := rfl

@[simp] theorem withTree_registrations (s : DOMState) (t : Tree) :
    (s.withTree t).registrations = s.registrations := rfl

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
