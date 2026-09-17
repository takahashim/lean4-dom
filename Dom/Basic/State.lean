import Dom.Basic.Exception
import Dom.Basic.WellFormed
import Dom.Basic.Fresh

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

/--
DOM Standard §6.1 の `NodeIterator`。

`filter` は callback なので model の外にあり、常に null として扱う。
`whatToShow` は node type の bitmask なので純粋であり、そのまま持つ
（既定は `SHOW_ALL`）。
-/
structure IteratorState where
  root : NodeId
  reference : NodeId
  pointerBeforeReference : Bool
  whatToShow : Nat := 0xFFFFFFFF
deriving DecidableEq, Repr, Inhabited

/--
DOM Standard §6.2 の `TreeWalker`。

`NodeIterator` と同じく `filter` は callback なので model の外にあり、常に null として扱う。
`whatToShow` は node type の bitmask なので純粋であり、そのまま持つ（既定は `SHOW_ALL`）。

`NodeIterator` と違い **remove に追随しない**（仕様に "removing steps" が無い）ので、
`current` は木から外れた node のままになりうる。それでも observation は決まるので、
model はそのまま持つ。
-/
structure WalkerState where
  root : NodeId
  current : NodeId
  whatToShow : Nat := 0xFFFFFFFF
deriving DecidableEq, Repr, Inhabited

/-! ## event listener（§2.7） -/

/--
listener の callback の代わりに置く、決まった副作用。

callback そのものは model の外（`NodeFilter` と同じ）だが、
**何をするか**を scenario が宣言しておけば、配送の順序と打ち切りは model で決まる。
差分テストはそれを比べる。
-/
inductive ListenerAction where
  | none
  | stopPropagation
  | stopImmediatePropagation
  | preventDefault
  /-- 配送中に `index` 番の listener を外す。 -/
  | removeListener (index : Nat)
  /--
  配送中に listener を足す。callback は `source` 番の listener のものを使い回す。

  仕様の "invoke" は listener list の **clone** を回すので、
  ここで足したものはこの配送では呼ばれない。
  -/
  | addListener (target : Nat) («type» : String) (source : Nat) (capture : Bool)
deriving DecidableEq, Repr, Inhabited

/--
DOM Standard §2.7 の event listener。

仕様の listener list は EventTarget ごとだが、model では一本の list に `target` を持たせる。
同じ target の中の順序（登録順）は保たれるので、"inner invoke" の意味は変わらない。

`removed` は仕様のフラグである。"remove an event listener" は list から取り除きつつ
このフラグを立てる。model は取り除かずにフラグだけ立てて、list の index を安定させる
（配送中の clone が「外された listener」を飛ばす、という意味も同じになる）。
-/
structure EventListener where
  target : NodeId
  «type» : String
  /-- callback object の代わりの番号。重複判定（add の step 5）に使う。 -/
  callback : Nat
  capture : Bool := false
  once : Bool := false
  action : ListenerAction := .none
  removed : Bool := false
deriving DecidableEq, Repr, Inhabited

/--
listener が呼ばれたことの記録。

listener そのものではなく **callback の番号**で書く。
配送中に listener を足したり外したりすると list の index は動くが、
callback の番号は scenario が宣言したまま動かないので、差分テストで突き合わせられる。
-/
structure Invocation where
  callback : Nat
  currentTarget : NodeId
  eventPhase : Nat
deriving DecidableEq, Repr, Inhabited

/-! ## MutationObserver -/

/-- DOM Standard §4.3.1 の `MutationRecord` の type。 -/
inductive RecordType where
  | attributes
  | childList
  | characterData
deriving DecidableEq, Repr, Inhabited

/--
DOM Standard §4.3.1 の `MutationRecord`。

`attributeName` は attribute の local name、`attributeNamespace` は namespace である
（"handle attribute changes" step 1）。type が `attributes` 以外なら両方 `none`。
-/
structure MutationRecord where
  type : RecordType
  target : NodeId
  addedNodes : List NodeId := []
  removedNodes : List NodeId := []
  previousSibling : Option NodeId := none
  nextSibling : Option NodeId := none
  attributeName : Option String := none
  attributeNamespace : Option String := none
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
  attributes : Bool := false
  attributeOldValue : Bool := false
  /--
  仕様の `attributeFilter`。存在しないことと空 list であることは区別される
  （"queue a mutation record" step 2.3 の三つ目の条件が、存在するかどうかで分岐する）。
  -/
  attributeFilter : Option (List String) := none
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
  /--
  §6.2 の `TreeWalker`。木の変更に追随しないので、どの algorithm もこれを触らない。
  -/
  walkers : List WalkerState := []
  /-- §2.7 の event listener。target ごとの list を一本にまとめたもの。 -/
  listeners : List EventListener := []
  observers : List ObserverState := []
  registrations : List Registration := []
  /-- 仕様の agent の "mutation observer microtask queued"。 -/
  microtaskQueued : Bool := false
  /-- 仕様の agent の "pending mutation observers"。observer の index で持つ。 -/
  pendingObservers : List Nat := []
  /--
  どの element にも付いていない `Attr`（仕様の「element が null の attribute」）。

  `createAttribute` が作ったもの、`removeAttributeNode` が返したもの、
  `setAttributeNode` が押し出したものが入る。**名前で消した attribute は入らない。**
  仕様では element を null にするだけで object は残るが、それを指す参照がどこにも
  無いので観測できない（`docs/threats-to-validity.md` を参照）。
  -/
  detachedAttrs : List Attr := []
deriving Repr, Inhabited

/-! ## algorithm が触れない成分 -/

/--
**§4.2.3 の algorithm が触れない三成分。**

`DOMState` の十成分のうち `walkers` / `listeners` / `detachedAttrs` は、木を変える
algorithm のどれも読まないし書かない（`Dom/Validity/Walkers.lean` と
`Dom/Validity/Events.lean` がその理由を書いている）。

触れないことを**関係意味論の側に書いておかないと**、関係は「その三つが何であっても
よい」という意味になる。すると `Dom/Spec/ObsEq.lean` の `ObsEq` にその三つを
入れられず、determinism も completeness も「将来の操作から区別できない」ことを
意味しなくなる。

* `walkers` が違えば次の `walkerMove` の結果が違う
* `listeners` が違えば次の `dispatchEvent` の invocation が違う
* `detachedAttrs` が違えば次に割り当てられる `Attr` の id が違いうる

どれも `Dom/Observation.lean` の `Observation` に出るので、観測の等しさに含める。
-/
structure Untouched (s s' : DOMState) : Prop where
  walkers : s'.walkers = s.walkers
  listeners : s'.listeners = s.listeners
  detachedAttrs : s'.detachedAttrs = s.detachedAttrs

namespace Untouched

theorem refl (s : DOMState) : Untouched s s := ⟨rfl, rfl, rfl⟩

theorem symm {s s' : DOMState} (h : Untouched s s') : Untouched s' s :=
  ⟨h.walkers.symm, h.listeners.symm, h.detachedAttrs.symm⟩

theorem trans {s s' s'' : DOMState} (h : Untouched s s') (h' : Untouched s' s'') :
    Untouched s s'' :=
  ⟨h'.walkers.trans h.walkers, h'.listeners.trans h.listeners,
    h'.detachedAttrs.trans h.detachedAttrs⟩

/-- 状態そのものが等しければ、当然触れていない。 -/
theorem of_eq {s s' : DOMState} (h : s' = s) : Untouched s s' := by rw [h]; exact refl s

/-- 一歩ずつ触れないなら、畳み込んでも触れない。 -/
theorem foldl {α : Type} {f : DOMState → α → DOMState} (hf : ∀ s a, Untouched s (f s a)) :
    ∀ (l : List α) (s : DOMState), Untouched s (l.foldl f s)
  | [], s => refl s
  | a :: rest, s => (hf s a).trans (foldl hf rest (f s a))

end Untouched

/-! ## attribute の id -/

/-- detach された attribute の id の最大。 -/
def maxDetachedAttrId (l : List Attr) : Nat := l.foldl (fun m a => max m a.id.id) 0

/--
状態全体での attribute の id の最大。木の中と detach されたものの両方を見る。

`createAttribute` が作った attribute は木の外にいるので、木だけを見ると
その id をまた使ってしまう。
-/
def stateMaxAttrId (s : DOMState) : Nat := max (maxAttrId s.tree) (maxDetachedAttrId s.detachedAttrs)

/-- 新しい attribute に割り当てる id。 -/
def freshStateAttrId (s : DOMState) : AttrId := ⟨stateMaxAttrId s + 1⟩

theorem ne_freshStateAttrId_tree {s : DOMState} {n : NodeId} {d : NodeData} {a : Attr}
    (hd : s.tree.get? n = some d) (ha : a ∈ d.attributes) : a.id ≠ freshStateAttrId s := by
  intro he
  have hle := attrId_le_maxAttrId hd ha
  rw [he] at hle
  simp only [freshStateAttrId, stateMaxAttrId] at hle
  omega

theorem attrId_le_maxDetachedAttrId : ∀ (l : List Attr) (init : Nat) {a : Attr}, a ∈ l →
    a.id.id ≤ l.foldl (fun m a => max m a.id.id) init :=
  attrId_le_foldl_attrMax

theorem ne_freshStateAttrId_detached {s : DOMState} {a : Attr} (ha : a ∈ s.detachedAttrs) :
    a.id ≠ freshStateAttrId s := by
  intro he
  have hle := attrId_le_maxDetachedAttrId s.detachedAttrs 0 ha
  rw [he] at hle
  simp only [freshStateAttrId, stateMaxAttrId, maxDetachedAttrId] at hle
  omega

namespace DOMState

/-- 木だけを差し替える。live object は変えない。 -/
def withTree (s : DOMState) (t : Tree) : DOMState := { s with tree := t }

@[simp] theorem withTree_tree (s : DOMState) (t : Tree) : (s.withTree t).tree = t := rfl

/-- 木だけを差し替える更新は `Untouched` の三成分を持ち越す。 -/
theorem untouched_withTree (s : DOMState) (t : Tree) : Untouched s (s.withTree t) :=
  ⟨rfl, rfl, rfl⟩

@[simp] theorem withTree_ranges (s : DOMState) (t : Tree) : (s.withTree t).ranges = s.ranges := rfl

@[simp] theorem withTree_walkers (s : DOMState) (t : Tree) :
    (s.withTree t).walkers = s.walkers := rfl

@[simp] theorem withTree_listeners (s : DOMState) (t : Tree) :
    (s.withTree t).listeners = s.listeners := rfl

@[simp] theorem withTree_detachedAttrs (s : DOMState) (t : Tree) :
    (s.withTree t).detachedAttrs = s.detachedAttrs := rfl

@[simp] theorem withTree_iterators (s : DOMState) (t : Tree) :
    (s.withTree t).iterators = s.iterators := rfl

@[simp] theorem withTree_observers (s : DOMState) (t : Tree) :
    (s.withTree t).observers = s.observers := rfl

@[simp] theorem withTree_registrations (s : DOMState) (t : Tree) :
    (s.withTree t).registrations = s.registrations := rfl

@[simp] theorem withTree_pendingObservers (s : DOMState) (t : Tree) :
    (s.withTree t).pendingObservers = s.pendingObservers := rfl

@[simp] theorem withTree_microtaskQueued (s : DOMState) (t : Tree) :
    (s.withTree t).microtaskQueued = s.microtaskQueued := rfl

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
