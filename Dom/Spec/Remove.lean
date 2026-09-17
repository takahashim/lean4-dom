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

仕様の remove は五つの副作用を持つので、`RemoveSpec` もその連言にしてある。

| component | 仕様の step |
| --- | --- |
| `RemovePre` | 1-2 |
| `RangeAdjusted` | 3（live range pre-remove steps） |
| `IteratorAdjusted` | 4（NodeIterator pre-remove steps） |
| `TreeRemoved` | 7 |
| `TransientAdded` | 20 |
| `RecordQueued` | 21 |

step 8-10（slot）・11/15（removing steps）・13-14（custom element）は
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
  /-- 各 node の持ち物（kind・data・attribute・名前・node document）は変わらない。 -/
  sameData : ∀ m d d', t.get? m = some d → t'.get? m = some d' →
    d'.kind = d.kind ∧ d'.data = d.data ∧ d'.attributes = d.attributes ∧
      d'.ownerDocument = d.ownerDocument ∧ d'.namespace = d.namespace ∧
      d'.prefix = d.prefix ∧ d'.localName = d.localName ∧
      d'.isHTMLDocument = d.isHTMLDocument

/-! ## step 20：transient registered observer -/

/-- 二つの registration が observer と options を共有していること。 -/
def SameObserverOptions (a b : Registration) : Prop :=
  a.observer = b.observer ∧ a.subtree = b.subtree ∧ a.childList = b.childList ∧
    a.attributes = b.attributes ∧ a.attributeOldValue = b.attributeOldValue ∧
    a.attributeFilter = b.attributeFilter ∧ a.characterData = b.characterData ∧
    a.characterDataOldValue = b.characterDataOldValue

/--
仕様の step 20。

`parent` の inclusive ancestor に subtree 付きで登録されている registration ごとに、
それを source とする transient registered observer が `node` に足される。
元の registration は残る。

**並びは決めない。** registration list の順序は観測に出ない
（record は observer ごとの queue に積まれる）ので、集合として書く。

observer の node list（`ObserverState.nodeList`）については何も言わない。
仕様の step 20 は registered observer list にしか触れないが、model は配送時の掃除が
届くように node list にも足している（`Dom/Observer/Record.lean` の doc comment）。
その差は record の中身には出ないので、ここでは扱わない。
-/
def TransientAdded (s s' : DOMState) (node parent : NodeId) : Prop :=
  (∀ r ∈ s.registrations, r ∈ s'.registrations) ∧
  (∀ src ∈ s.registrations, src.subtree = true → InclusiveAncestor s.tree src.node parent →
    ∃ r ∈ s'.registrations, SameObserverOptions r src ∧ r.node = node ∧
      r.transient = true ∧ r.source = some src.node) ∧
  (∀ r ∈ s'.registrations, r ∉ s.registrations →
    ∃ src ∈ s.registrations, SameObserverOptions r src ∧ src.subtree = true ∧
      InclusiveAncestor s.tree src.node parent ∧ r.node = node ∧
      r.transient = true ∧ r.source = some src.node)

/-! ## step 21：mutation record -/

/--
仕様の step 21。`suppressObservers` が false なら childList の record を積む。

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
-/
def RemoveSpec (s : DOMState) (node : NodeId) (suppress : Bool) (s' : DOMState) : Prop :=
  ∃ parent index,
    RemovePre s.tree node parent ∧
    index = ((Dom.index s.tree node).getD 0) ∧
    RangeAdjusted s s' node parent index ∧
    IteratorAdjusted s s' node ∧
    TreeRemoved s.tree s'.tree node parent ∧
    TransientAdded s s' node parent ∧
    RecordQueued s s' node parent (previousSibling s.tree node) (nextSibling s.tree node) suppress ∧
    -- `walkers` / `listeners` / `detachedAttrs` には触れない（`Dom/Spec/Frame.lean`）
    Untouched s s'

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

end Dom.Spec
