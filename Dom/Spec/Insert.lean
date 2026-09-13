import Dom.Spec.Adopt

/-!
# `insert` の関係意味論（§4.2.3）

`remove` と同じ方針。仕様本文から独立に書き写した関係を置き、
実行関数がそれを満たすことは別に証明する。

`insert` は step 4 で `remove` を、step 7.1 で `adopt` を呼ぶので、
関係もそれぞれ `RemoveSpec` / `AdoptSpec` を composition する。
仕様本文がそう書いているとおりの構成であり、実行関数の再利用ではない。

step 7.4-7.7（slot・insertion steps・custom element）は model の対象外である。
-/

namespace Dom.Spec

open Dom

/-! ## step 1：入れる node の列 -/

/-- DocumentFragment なら children、そうでなければ `node` 一つ。 -/
def NodesToInsert (t : Tree) (node : NodeId) (nodes : List NodeId) : Prop :=
  ∃ d, t.get? node = some d ∧
    ((d.kind = NodeKind.documentFragment ∧ nodes = d.children) ∨
      (d.kind ≠ NodeKind.documentFragment ∧ nodes = [node]))

/-! ## step 4：DocumentFragment を空にする -/

/-- 列を順に remove する。 -/
inductive RemoveEachSpec : DOMState → List NodeId → Bool → DOMState → Prop where
  | nil {s : DOMState} {b : Bool} : RemoveEachSpec s [] b s
  | cons {s s₁ s₂ : DOMState} {n : NodeId} {ns : List NodeId} {b : Bool} :
      RemoveSpec s n b s₁ → RemoveEachSpec s₁ ns b s₂ → RemoveEachSpec s (n :: ns) b s₂

/--
仕様の step 4。

DocumentFragment なら children を（observer を抑えて）外し、
**`suppressObservers` に関わらず** fragment 自身に record を積む（step 4.2 の注）。
fragment でなければ何も起こらない。
-/
def FragmentPrepared (s s₁ : DOMState) (node : NodeId) (nodes : List NodeId) : Prop :=
  ∃ d, s.tree.get? node = some d ∧
    (if d.kind = NodeKind.documentFragment then
      ∃ sr, RemoveEachSpec s nodes true sr ∧
        TreeRecordQueued sr s₁ node [] nodes none none false
    else s₁ = s)

/-! ## step 5：live range の調整 -/

/-- `child` の index。`child` が null なら step 5 は走らないので 0 とする。 -/
def ChildIndex (t : Tree) (child : Option NodeId) (idx : Nat) : Prop :=
  match child with
  | none => idx = 0
  | some c => index t c = some idx

/-- `parent` を指し offset が `index` より後ろの boundary point を `count` だけずらす。 -/
def InsertShifted (parent : NodeId) (index count : Nat) (bp bp' : BoundaryPoint) : Prop :=
  (bp.node = parent ∧ index < bp.offset ∧ bp' = ⟨bp.node, bp.offset + count⟩) ∨
  (¬(bp.node = parent ∧ index < bp.offset) ∧ bp' = bp)

/--
仕様の step 5。`child` が null なら何もしない。

木も iterator も observer も触らない step である。
-/
structure RangeInsertAdjusted (s s' : DOMState) (parent : NodeId) (child : Option NodeId)
    (idx count : Nat) : Prop where
  tree : s'.tree = s.tree
  live : LiveObjectsUnchangedExceptRanges s s'
  length : s'.ranges.length = s.ranges.length
  adjusted : ∀ (i : Nat) (r r' : RangeState), s.ranges[i]? = some r → s'.ranges[i]? = some r' →
    (child = none ∧ r' = r) ∨
      (child ≠ none ∧ InsertShifted parent idx count r.start r'.start ∧
        InsertShifted parent idx count r.«end» r'.«end»)

/-! ## step 6：直前の兄弟 -/

/-- `child` があればその前の兄弟、無ければ `parent` の最後の子。 -/
def PreviousSiblingOf (t : Tree) (parent : NodeId) (child : Option NodeId)
    (prev : Option NodeId) : Prop :=
  match child with
  | some c => prev = previousSibling t c
  | none => prev = (childrenOf t parent).getLast?

/-! ## step 7：一つずつ入れる -/

/-- 一つの node を `parent` の children の `child` の直前に入れる（step 7.2-7.3）。 -/
structure TreeInserted (t t' : Tree) (parent node : NodeId) (child : Option NodeId) : Prop where
  /-- node は parent を得る。 -/
  attached : parentOf t' node = some parent
  /-- parent の children に、`child` の位置で入る。 -/
  children : childrenOf t' parent = Dom.ListUtil.insertBefore (childrenOf t parent) child node
  /-- ほかの node の parent は動かない。 -/
  otherParents : ∀ m, m ≠ node → parentOf t' m = parentOf t m
  /-- parent 以外の children は動かない。 -/
  otherChildren : ∀ m, m ≠ parent → childrenOf t' m = childrenOf t m
  /-- node は増えも減りもしない。 -/
  sameNodes : ∀ m, (t'.get? m).isSome = (t.get? m).isSome
  /-- 各 node の持ち物（kind・data・attribute・名前・node document）は変わらない。 -/
  sameData : ∀ (m : NodeId) (d d' : NodeData), t.get? m = some d → t'.get? m = some d' →
    d'.kind = d.kind ∧ d'.data = d.data ∧ d'.attributes = d.attributes ∧
      d'.ownerDocument = d.ownerDocument ∧ d'.namespace = d.namespace ∧
      d'.prefix = d.prefix ∧ d'.localName = d.localName ∧
      d'.isHTMLDocument = d.isHTMLDocument

/-- 仕様の step 7。各 node を adopt してから木に入れる。 -/
inductive InsertedEach (parent : NodeId) (child : Option NodeId) (doc : NodeId) :
    DOMState → List NodeId → DOMState → Prop where
  | nil {s : DOMState} : InsertedEach parent child doc s [] s
  | cons {s sa sb s' : DOMState} {n : NodeId} {ns : List NodeId} :
      AdoptSpec s n doc sa →
      TreeInserted sa.tree sb.tree parent n child →
      LiveObjectsUnchangedExceptTree sa sb →
      InsertedEach parent child doc sb ns s' →
      InsertedEach parent child doc s (n :: ns) s'

/-! ## 全体 -/

/--
**`insert` の関係意味論。**

`InsertSpec s node parent child suppress s'` は
「状態 `s` で `node` を `parent` の `child` の直前に入れると `s'` になる」と読む。
-/
def InsertSpec (s : DOMState) (node parent : NodeId) (child : Option NodeId)
    (suppress : Bool) (s' : DOMState) : Prop :=
  ∃ nodes, NodesToInsert s.tree node nodes ∧
    ((nodes = [] ∧ s' = s) ∨
      (nodes ≠ [] ∧ ∃ (s₁ s₂ s₃ : DOMState) (idx : Nat) (prev : Option NodeId) (pd : NodeData),
        FragmentPrepared s s₁ node nodes ∧
        ChildIndex s₁.tree child idx ∧
        PreviousSiblingOf s₁.tree parent child prev ∧
        RangeInsertAdjusted s₁ s₂ parent child idx nodes.length ∧
        s₁.tree.get? parent = some pd ∧
        InsertedEach parent child pd.ownerDocument s₂ nodes s₃ ∧
        TreeRecordQueued s₃ s' parent nodes [] prev child suppress))

end Dom.Spec
