import Dom.Basic.State
import Dom.Basic.Order
import Dom.Spec.Record

/-!
# `remove` の関係意味論（§4.2.3）

本 model はこれまで **実行関数そのものを意味論**としてきた。
それだと仕様の翻訳を誤っても、その誤った関数についての定理は証明できてしまう。
そこで仕様本文から独立に書き写した関係 `RemoveSpec` を置き、
実行関数がそれを満たすこと（soundness）を別に証明する。

## 書き方の制約

**この module は実行側の algorithm を呼ばない。**
`liveRangePreRemove` / `detach` / `adjustNodePointer` / `addTransientObservers` /
`queueTreeMutationRecord` はどれも使わない。使ってよいのは
`parentOf` / `childrenOf` / `ancestors` / `precedes` のような **観測の語彙**だけである
（関係と実行関数を分ける意味が無くなるため）。

## 構成

仕様の remove は三つの段に分かれるので、`RemoveSpec` も途中の状態を挟んで段を並べる。

| component | 仕様の step |
| --- | --- |
| `RemovePre` | 1-2 |
| `Detached`（`RangeAdjusted`・`IteratorAdjusted`・`TreeRemoved`） | 3-4（live range と NodeIterator の pre-remove steps）、7 |
| `TransientAdded` | 15（add transient registered observers） |
| `RecordQueued` | 16 |

step 8-10（slot）・11/14.1（removing steps）・13/14.2（custom element）・17（children changed steps）は
model の対象外である（`docs/traceability.md` の「未対応と対象外」）。
-/

namespace Dom.Spec

open Dom

/-! ## step 1-2：precondition -/

/-- 仕様の step 1-2。parent が非 null であること（assert）。 -/
def RemovePre (t : Tree) (node parent : NodeId) : Prop :=
  parentOf t node = some parent

/-! ## step 3：live range pre-remove steps -/

/--
§5.5 "live range pre-remove steps" の step 4-7 を、boundary point 一つについて書いたもの。

* step 4-5：`node` の inclusive descendant を指していたら、`node` があった位置へ移す。
* step 6-7：`parent` を指していて offset が `index` より後ろなら、一つ手前へ詰める。
* それ以外は動かない。

三つの枝は排他である（step 4-5 で移った先の offset はちょうど `index` なので、
step 6-7 の条件には当てはまらない）。
-/
def BoundaryAdjusted (t : Tree) (node parent : NodeId) (index : Nat)
    (bp bp' : BoundaryPoint) : Prop :=
  (InclusiveAncestor t node bp.node ∧ bp' = ⟨parent, index⟩) ∨
  (¬ InclusiveAncestor t node bp.node ∧ bp.node = parent ∧ index < bp.offset ∧
    bp' = ⟨bp.node, bp.offset - 1⟩) ∨
  (¬ InclusiveAncestor t node bp.node ∧ ¬(bp.node = parent ∧ index < bp.offset) ∧ bp' = bp)

/--
仕様の step 3。

live range の個数と並びは変わらず、各 range の両端が `BoundaryAdjusted` で決まる。
`index` は step 3 の「`node` の index」である。
-/
def RangeAdjusted (s s' : DOMState) (node parent : NodeId) (index : Nat) : Prop :=
  s'.ranges.length = s.ranges.length ∧
  ∀ (i : Nat) (r r' : RangeState), s.ranges[i]? = some r → s'.ranges[i]? = some r' →
    BoundaryAdjusted s.tree node parent index r.start r'.start ∧
    BoundaryAdjusted s.tree node parent index r.«end» r'.«end»

/-! ## step 4：NodeIterator pre-remove steps -/

/--
§6.1 "adjust a node pointer" の step 2.1。

`toBeRemoved` より tree order で後ろにあり、`root` の inclusive descendant であって
`toBeRemoved` の inclusive descendant でない **最初の** node。
「最初の」は「その条件を満たす他のどの node より前にある」と書く。
-/
def FirstFollowingOutside (t : Tree) (root toBeRemoved next : NodeId) : Prop :=
  precedes t toBeRemoved next = true ∧
  InclusiveAncestor t root next ∧ ¬ InclusiveAncestor t toBeRemoved next ∧
  ∀ m, precedes t toBeRemoved m = true → InclusiveAncestor t root m →
    ¬ InclusiveAncestor t toBeRemoved m → precedes t m next = false

/--
§6.1 "adjust a node pointer" の step 3。

前の兄弟が無ければ parent、あれば「前の兄弟の inclusive descendant のうち tree order で最後のもの」。
-/
def LastBeforeRemoval (t : Tree) (toBeRemoved m : NodeId) : Prop :=
  (previousSibling t toBeRemoved = none ∧ parentOf t toBeRemoved = some m) ∨
  (∃ prev, previousSibling t toBeRemoved = some prev ∧
    InclusiveAncestor t prev m ∧ ∀ x, InclusiveAncestor t prev x → precedes t m x = false)

/--
§6.1 "adjust a node pointer" を関係として書いたもの。

node pointer は `(node, pointer before)` の組である。
-/
inductive PointerAdjusted (t : Tree) (root toBeRemoved : NodeId) :
    NodeId × Bool → NodeId × Bool → Prop where
  /-- step 1。部分木の外を指しているか、root ごと外れる場合は動かさない。 -/
  | untouched {p : NodeId × Bool} :
      (¬ InclusiveAncestor t toBeRemoved p.1 ∨ InclusiveAncestor t toBeRemoved root) →
      PointerAdjusted t root toBeRemoved p p
  /-- step 2。pointer が前にあり、部分木の外に「次」がある場合。 -/
  | forward {n next : NodeId} :
      InclusiveAncestor t toBeRemoved n → ¬ InclusiveAncestor t toBeRemoved root →
      FirstFollowingOutside t root toBeRemoved next →
      PointerAdjusted t root toBeRemoved (n, true) (next, true)
  /-- step 3-4。pointer が後ろにあるか、「次」が無い場合。 -/
  | backward {n m : NodeId} {before : Bool} :
      InclusiveAncestor t toBeRemoved n → ¬ InclusiveAncestor t toBeRemoved root →
      (before = false ∨ ∀ next, ¬ FirstFollowingOutside t root toBeRemoved next) →
      LastBeforeRemoval t toBeRemoved m →
      PointerAdjusted t root toBeRemoved (n, before) (m, false)

/--
仕様の step 4。

対象は「root の node document が `node` の node document と同じ」iterator だけで、
残りは動かさない。candidate reference は traverse の途中でしか非 null にならないので、
model は状態として持たない（`Dom/Traversal/NodeIterator.lean`）。
-/
def IteratorAdjusted (s s' : DOMState) (node : NodeId) : Prop :=
  s'.iterators.length = s.iterators.length ∧
  ∀ (i : Nat) (it it' : IteratorState), s.iterators[i]? = some it →
    s'.iterators[i]? = some it' →
    it'.root = it.root ∧ it'.whatToShow = it.whatToShow ∧
    (if ownerDocumentOf s.tree it.root = ownerDocumentOf s.tree node then
      PointerAdjusted s.tree it.root node
        (it.reference, it.pointerBeforeReference) (it'.reference, it'.pointerBeforeReference)
    else it' = it)

/-! ## step 7：木からの取り外し -/

/--
仕様の step 7 と、その frame。

「parent の children から node を取り除く」ことと、
node が parent を失うこと。それ以外の観測は変わらない。
-/
structure TreeRemoved (t t' : Tree) (node parent : NodeId) : Prop where
  /-- node は parent を失う。 -/
  detached : parentOf t' node = none
  /-- parent の children からは node だけが消える。 -/
  children : childrenOf t' parent = (childrenOf t parent).filter (· != node)
  /-- ほかの node の parent は動かない。 -/
  otherParents : ∀ m, m ≠ node → parentOf t' m = parentOf t m
  /-- parent 以外の children は動かない（外した node の children も残る）。 -/
  otherChildren : ∀ m, m ≠ parent → childrenOf t' m = childrenOf t m
  /-- node は増えも減りもしない。 -/
  sameNodes : ∀ m, (t'.get? m).isSome = (t.get? m).isSome
  /-- 各 node の持ち物（kind・data・attribute・名前・node document・document の type と mode）は変わらない。 -/
  sameData : ∀ m d d', t.get? m = some d → t'.get? m = some d' →
    d'.kind = d.kind ∧ d'.data = d.data ∧ d'.attributes = d.attributes ∧
      d'.ownerDocument = d.ownerDocument ∧ d'.namespace = d.namespace ∧
      d'.prefix = d.prefix ∧ d'.localName = d.localName ∧
      d'.isHTMLDocument = d.isHTMLDocument ∧ d'.mode = d.mode ∧ NodeData.SameExtraProps d d'

/-! ## step 3-7 をまとめる -/

/--
step 3-4 と 7。live range と NodeIterator を調整し、木から外す。observer の側は何も動かない。

`move` の step 9-10, 13 も同じ形なので、`MoveSpec` もこれを使う。
-/
def Detached (s s' : DOMState) (node parent : NodeId) (index : Nat) : Prop :=
  RangeAdjusted s s' node parent index ∧
  IteratorAdjusted s s' node ∧
  TreeRemoved s.tree s'.tree node parent ∧
  ObserversUntouched s s'

/-! ## step 15：add transient registered observers -/

/--
§4.3 "add transient registered observers" step 1.3 の source。

transient registered observer ならその source、そうでなければ registered 自身である。
model の source は registration の node で表す（`Registration.source` の doc comment）。
-/
def sourceOf (r : Registration) : Option NodeId :=
  if r.transient then r.source else some r.node

/--
"add transient registered observers" step 1.1-1.5 を一つの registered について。

`existing` は `node` の元の registered observer list、`acc` はここまでに足した transient である。
subtree が false なら何もせず（step 1.1）、`node` の list に source が同じ transient があれば足さない（step 1.4）。
そうでなければ、observer と options を registered から写し、source を step 1.3 のものにした transient を足す
（step 1.5）。source の options ではなく registered の options を写すのは、transient の options が
その source の options と等しいからである（`observe()` step 8.1 が options を差し替える前にそれを外す）。
-/
def transientAppend (node : NodeId) (existing acc : List Registration) (r : Registration) :
    List Registration :=
  if r.subtree = true ∧
      ¬ ∃ t ∈ existing ++ acc, t.transient = true ∧ t.observer = r.observer ∧ t.source = sourceOf r
  then acc ++ [{ r with node := node, transient := true, source := sourceOf r }]
  else acc

/--
step 1 で `node` に足す transient の列。

`nodes`（`parent` の inclusive ancestor を下から上へ）の順に、各 node の registered observer list を list の順に回る。
-/
def transientsFor (regs : List Registration) (nodes : List NodeId) (node : NodeId) :
    List Registration :=
  (nodes.flatMap (regsOn regs)).foldl (transientAppend node (regsOn regs node)) []

/--
**"add transient registered observers" の関係。**

`node` の registered observer list は、元の list に `transientsFor` の transient を続けたものになり、
ほかの node の list は変わらない（step 1.5）。足した transient の observer は、その順に pending mutation
observers へ append され（step 1.7）、一つでも足せば microtask が予約される（step 1.8）。

step 1.6 の transient node set は観測に出ない（`ObserverState.nodeList`）ので、ここでは扱わない。
-/
structure TransientAdded (s s' : DOMState) (node parent : NodeId) : Prop where
  tree : s'.tree = s.tree
  ranges : s'.ranges = s.ranges
  iterators : s'.iterators = s.iterators
  observersLength : s'.observers.length = s.observers.length
  records : ∀ (mo : Nat) (o o' : ObserverState), s.observers[mo]? = some o →
    s'.observers[mo]? = some o' → o'.records = o.records
  added : ∃ nodes, InclusiveAncestorsUp s.tree parent nodes ∧
    (∀ n, regsOn s'.registrations n =
      if n = node then regsOn s.registrations node ++ transientsFor s.registrations nodes node
      else regsOn s.registrations n) ∧
    s'.pendingObservers =
      appendNew s.pendingObservers ((transientsFor s.registrations nodes node).map (·.observer)) ∧
    s'.microtaskQueued =
      (s.microtaskQueued || !(transientsFor s.registrations nodes node).isEmpty)
  /-- `Dom/Basic/State.lean` の `Untouched`。 -/
  untouched : Untouched s s'

/-! ## step 16：mutation record -/

/--
仕様の step 16。`suppressObservers` が false なら childList の record を積む。

一般形は `Dom/Spec/Record.lean` の `TreeRecordQueued` にある。
remove が積むのは「`parent` を target とし、`node` を removedNodes とする record」である。
-/
def RecordQueued (s s' : DOMState) (node parent : NodeId)
    (oldPrev oldNext : Option NodeId) (suppress : Bool) : Prop :=
  TreeRecordQueued s s' parent [] [node] oldPrev oldNext suppress

/-! ## 全体 -/

/--
**`remove` の関係意味論。**

`RemoveSpec s node suppress s'` は「状態 `s` で `node` を remove すると `s'` になる」と読む。
仕様の step のうち model が扱うものをすべて含む。

`s₁` は木から外した後、`s₂` は transient registered observer を足した後の状態である。
record の interested observers は `s₂` で数える。record に載る兄弟は木を変える前の値である（step 5-6）。
-/
def RemoveSpec (s : DOMState) (node : NodeId) (suppress : Bool) (s' : DOMState) : Prop :=
  ∃ parent index s₁ s₂,
    RemovePre s.tree node parent ∧
    index = ((Dom.index s.tree node).getD 0) ∧
    -- step 3-4, 7
    Detached s s₁ node parent index ∧
    -- step 15
    TransientAdded s₁ s₂ node parent ∧
    -- step 16
    RecordQueued s₂ s' node parent (previousSibling s.tree node) (nextSibling s.tree node) suppress ∧
    ObserverOnly s₂ s'

/-! ## 列に対する remove -/

/--
列を順に remove する。

`insert` の step 4（DocumentFragment を空にする）が使う。
`remove` そのものの一部ではないが、`RemoveSpec` だけで書けるのでここに置く。
-/
inductive RemoveEachSpec : DOMState → List NodeId → Bool → DOMState → Prop where
  | nil {s : DOMState} {b : Bool} : RemoveEachSpec s [] b s
  | cons {s s₁ s₂ : DOMState} {n : NodeId} {ns : List NodeId} {b : Bool} :
      RemoveSpec s n b s₁ → RemoveEachSpec s₁ ns b s₂ → RemoveEachSpec s (n :: ns) b s₂

/-! ## 段から全体へ -/

/-- `RemoveSpec` の木は、元の木から `node` を外したものである。 -/
theorem RemoveSpec.treeRemoved {s s' : DOMState} {node : NodeId} {suppress : Bool}
    (h : RemoveSpec s node suppress s') :
    ∃ parent, RemovePre s.tree node parent ∧ TreeRemoved s.tree s'.tree node parent := by
  obtain ⟨parent, -, s₁, s₂, hpre, -, ⟨-, -, htr, -⟩, hta, -, hoo⟩ := h
  refine ⟨parent, hpre, ?_⟩
  rw [hoo.tree, hta.tree]
  exact htr

/-- `RemoveSpec` の live range は step 3 の調整を受けたものである。 -/
theorem RemoveSpec.rangeAdjusted {s s' : DOMState} {node : NodeId} {suppress : Bool}
    (h : RemoveSpec s node suppress s') :
    ∃ parent, RemovePre s.tree node parent ∧
      RangeAdjusted s s' node parent ((Dom.index s.tree node).getD 0) := by
  obtain ⟨parent, index, s₁, s₂, hpre, hidx, ⟨hra, -, -, -⟩, hta, -, hoo⟩ := h
  refine ⟨parent, hpre, ?_⟩
  subst hidx
  obtain ⟨hlen, hadj⟩ := hra
  refine ⟨by rw [hoo.ranges, hta.ranges, hlen], fun i r r' hr hr' => hadj i r r' hr ?_⟩
  rw [← hta.ranges, ← hoo.ranges]; exact hr'

/-- `RemoveSpec` は walker・listener・detach された `Attr` に触れない。 -/
theorem RemoveSpec.untouched {s s' : DOMState} {node : NodeId} {suppress : Bool}
    (h : RemoveSpec s node suppress s') : Untouched s s' := by
  obtain ⟨_, _, s₁, s₂, _, _, ⟨_, _, _, hu⟩, hta, _, hoo⟩ := h
  exact (hu.untouched.trans (TransientAdded.untouched hta)).trans hoo.untouched

end Dom.Spec
