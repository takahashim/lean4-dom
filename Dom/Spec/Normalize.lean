import Dom.Spec.ReplaceData
import Dom.Spec.Remove
import Dom.Spec.TreeOrder

/-!
# `Node.normalize()` の関係意味論（§4.4）

`NormalizeEngineSpec` は本 model の兄弟ごとの結合を表す。実行関数の soundness・
determinism・completeness はこの関係に対する定理である。
`NormalizeStandardSpec` は標準本文の手順を別の関係として表す。

標準本文の step 3-4 は run 全体の data を一度に連結して replace data を一回呼び、
step 6 で全 boundary point を渡してから、step 7 で兄弟を外す。
model は兄弟ごとに「data を足す・boundary point を渡す・外す」を繰り返す。
両関係の record queue は異なりうる。標準関係に対する実装の soundness や、
両関係の木・live range の最終状態の一致は、ここでは証明していない。

step 6 の `length` は survivor の元の長さに、それまでの兄弟の長さを足したもの。
`StandardHandoff` は削除前の index とこの長さで全 boundary point を渡す。

## contiguous exclusive Text nodes

仕様の「node の contiguous exclusive Text nodes」は前後両側の兄弟を含むが、
step 3 と step 7 が使うのは後ろ側だけでよい。descendant を tree order で処理し、
run の先頭が後ろを全部畳むので、処理する時点で前側の exclusive Text の兄弟は残っていない
（長さ 0 のものは step 2 で外れ、そうでないものは自分が run の先頭になって後ろを畳んでいる）。
関係は後ろ側だけを `FollowingContiguousTexts` で書く。

## 候補の列

「descendant exclusive Text node ごとに」は、処理の途中で木が変わる。
変わり方は exclusive Text node が外れることだけなので、最初の木で tree order に並べた列を
順に見て、もう `this` の descendant でないもの（先の run で畳まれたもの）を飛ばせばよい。
-/

namespace Dom.Spec

open Dom

/-- exclusive Text node（§4.11）。CDATASection は Text を継承するが exclusive ではない。 -/
def ExclusiveText (t : Tree) (n : NodeId) : Prop :=
  ∃ d, t.get? n = some d ∧ d.kind = .text

/--
`n` の contiguous exclusive Text nodes のうち、`n` より後ろのもの（tree order）。

`n` の parent の children を `pre ++ n :: (sibs ++ post)` と分けたとき、
`sibs` は全部 exclusive Text で、`post` の先頭は exclusive Text でない。
-/
def FollowingContiguousTexts (t : Tree) (n : NodeId) (sibs : List NodeId) : Prop :=
  ∃ parent pre post, parentOf t n = some parent ∧
    childrenOf t parent = pre ++ n :: (sibs ++ post) ∧
    (∀ x ∈ sibs, ExclusiveText t x) ∧ (∀ x, post.head? = some x → ¬ ExclusiveText t x)

/--
step 6.1-6.4 を一つの boundary point に当てる。

畳まれる兄弟 `sib` の中を指していれば survivor の継ぎ目の後ろへ（6.1-6.2）、
parent の中で `sib` の位置（index `idx`）を指していれば survivor の継ぎ目へ（6.3-6.4）移す。
`len` は継ぎ目、つまりこの兄弟を足す直前の survivor の長さである。
-/
def BPHandedOff (survivor sib parent : NodeId) (idx len : Nat) (bp bp' : BoundaryPoint) : Prop :=
  -- step 6.1-6.2
  (bp.node = sib ∧ bp' = ⟨survivor, bp.offset + len⟩) ∨
  -- step 6.3-6.4
  (bp.node = parent ∧ bp.offset = idx ∧ bp' = ⟨survivor, len⟩) ∨
  (bp.node ≠ sib ∧ ¬ (bp.node = parent ∧ bp.offset = idx) ∧ bp' = bp)

/-- step 6 を全 live range の両端に当てる。range 以外は動かない。 -/
def RangesHandedOff (s s' : DOMState) (survivor sib parent : NodeId) (idx len : Nat) : Prop :=
  ∃ rs : List RangeState, s' = { s with ranges := rs } ∧ rs.length = s.ranges.length ∧
    ∀ (i : Nat) (r r' : RangeState), s.ranges[i]? = some r → rs[i]? = some r' →
      BPHandedOff survivor sib parent idx len r.start r'.start ∧
      BPHandedOff survivor sib parent idx len r.«end» r'.«end»

/--
**兄弟を一つ畳む（step 3-7 を兄弟一つについて）。**

data が空の兄弟は、足しても data が変わらないので replace data を呼ばない
（engine も呼ばず、characterData の record を積まない）。boundary point の引き渡しは行う。
-/
def SiblingMerged (s : DOMState) (survivor sib : NodeId) (s' : DOMState) : Prop :=
  ∃ (dsurv dsib : NodeData) (parent : NodeId) (pre post : List NodeId) (s₁ s₂ : DOMState),
    s.tree.get? survivor = some dsurv ∧ s.tree.get? sib = some dsib ∧
    parentOf s.tree sib = some parent ∧ childrenOf s.tree parent = pre ++ sib :: post ∧
    -- step 3-4
    ((dsib.data = "" ∧ s₁ = s) ∨
      (dsib.data ≠ "" ∧ ReplaceDataSpec s survivor dsurv.length 0 dsib.data s₁)) ∧
    -- step 6
    RangesHandedOff s₁ s₂ survivor sib parent pre.length dsurv.length ∧
    -- step 7
    RemoveSpec s₂ sib false s'

/-- 後ろの兄弟を tree order で順に畳む。 -/
inductive RunMerged : DOMState → NodeId → List NodeId → DOMState → Prop where
  | nil {s : DOMState} {survivor : NodeId} : RunMerged s survivor [] s
  | cons {s s₁ s₂ : DOMState} {survivor sib : NodeId} {rest : List NodeId} :
      SiblingMerged s survivor sib s₁ → RunMerged s₁ survivor rest s₂ →
      RunMerged s survivor (sib :: rest) s₂

/--
候補を順に処理する。

* もう `this` の descendant でなければ飛ばす（先の run で畳まれた）。
* step 2。長さ 0 なら外す。
* step 3-7。そうでなければ後ろの contiguous exclusive Text nodes を畳む。
-/
inductive NormalizedEach (this : NodeId) : DOMState → List NodeId → DOMState → Prop where
  | nil {s : DOMState} : NormalizedEach this s [] s
  | skip {s s' : DOMState} {n : NodeId} {rest : List NodeId} :
      ¬ Ancestor s.tree this n → NormalizedEach this s rest s' →
      NormalizedEach this s (n :: rest) s'
  | empty {s s₁ s' : DOMState} {n : NodeId} {rest : List NodeId} {d : NodeData} :
      Ancestor s.tree this n → s.tree.get? n = some d → d.length = 0 →
      RemoveSpec s n false s₁ → NormalizedEach this s₁ rest s' →
      NormalizedEach this s (n :: rest) s'
  | run {s s₁ s' : DOMState} {n : NodeId} {rest sibs : List NodeId} {d : NodeData} :
      Ancestor s.tree this n → s.tree.get? n = some d → d.length ≠ 0 →
      FollowingContiguousTexts s.tree n sibs → RunMerged s n sibs s₁ →
      NormalizedEach this s₁ rest s' →
      NormalizedEach this s (n :: rest) s'

/-- descendant の exclusive Text node すべてを、構造で書いた tree order に並べたもの。 -/
def DescendantExclusiveTexts (t : Tree) (this : NodeId) (nodes : List NodeId) : Prop :=
  (∀ n, n ∈ nodes ↔ Ancestor t this n ∧ ExclusiveText t n) ∧
    nodes.Pairwise (PrecedesStruct t)

/-- engine の読み：兄弟を一つずつ畳んで remove する。 -/
def NormalizeEngineSpec (s : DOMState) (this : NodeId) (s' : DOMState) : Prop :=
  (∃ d, s.tree.get? this = some d) ∧
    ∃ nodes, DescendantExclusiveTexts s.tree this nodes ∧ NormalizedEach this s nodes s'

/-- 本文の step 6：兄弟を一つも remove しないうちに、すべての兄弟の boundary point を引き渡す。 -/
inductive StandardHandoff (survivor parent : NodeId) :
    Nat → Nat → DOMState → List NodeId → DOMState → Prop where
  | nil {idx len : Nat} {s : DOMState} : StandardHandoff survivor parent idx len s [] s
  | cons {idx len : Nat} {s s₁ s₂ : DOMState} {sib : NodeId} {rest : List NodeId} {d : NodeData} :
      s.tree.get? sib = some d →
      RangesHandedOff s s₁ survivor sib parent idx len →
      StandardHandoff survivor parent (idx + 1) (len + d.length) s₁ rest s₂ →
      StandardHandoff survivor parent idx len s (sib :: rest) s₂

/-- 本文の step 3-7：一度に連結し、range を引き渡してから兄弟を remove する。 -/
def StandardRunMerged (s : DOMState) (survivor : NodeId) (sibs : List NodeId)
    (s' : DOMState) : Prop :=
  ∃ d parent idx s₁ s₂,
    s.tree.get? survivor = some d ∧ parentOf s.tree survivor = some parent ∧
    index s.tree survivor = some idx ∧
    ReplaceDataSpec s survivor d.length 0
      (String.join (sibs.map fun n => ((s.tree.get? n).map NodeData.data).getD "")) s₁ ∧
    StandardHandoff survivor parent (idx + 1) d.length s₁ sibs s₂ ∧
    RemoveEachSpec s₂ sibs false s'

/-- 本文の繰り返し：元の descendant の Text node を順にたどる。 -/
inductive StandardNormalizedEach (this : NodeId) :
    DOMState → List NodeId → DOMState → Prop where
  | nil {s : DOMState} : StandardNormalizedEach this s [] s
  | skip {s s' : DOMState} {n : NodeId} {rest : List NodeId} :
      ¬ Ancestor s.tree this n → StandardNormalizedEach this s rest s' →
      StandardNormalizedEach this s (n :: rest) s'
  | empty {s s₁ s' : DOMState} {n : NodeId} {rest : List NodeId} {d : NodeData} :
      Ancestor s.tree this n → s.tree.get? n = some d → d.length = 0 →
      RemoveSpec s n false s₁ → StandardNormalizedEach this s₁ rest s' →
      StandardNormalizedEach this s (n :: rest) s'
  | run {s s₁ s' : DOMState} {n : NodeId} {rest sibs : List NodeId} {d : NodeData} :
      Ancestor s.tree this n → s.tree.get? n = some d → d.length ≠ 0 →
      FollowingContiguousTexts s.tree n sibs → StandardRunMerged s n sibs s₁ →
      StandardNormalizedEach this s₁ rest s' → StandardNormalizedEach this s (n :: rest) s'

/-- DOM Standard の本文どおりの意味。observer の record も状態の一部として残す。 -/
def NormalizeStandardSpec (s : DOMState) (this : NodeId) (s' : DOMState) : Prop :=
  (∃ d, s.tree.get? this = some d) ∧
    ∃ nodes, DescendantExclusiveTexts s.tree this nodes ∧ StandardNormalizedEach this s nodes s'

/--
**`normalize()` の、結果まで含めた関係。**

失敗するのは `this` が木に無いとき（model の都合。IDL の受け手は必ず存在する）だけである。
-/
def NormalizeResult (s : DOMState) (this : NodeId) : Except DOMException DOMState → Prop
  | .ok s' => NormalizeEngineSpec s this s'
  | .error e => s.tree.get? this = none ∧ e = .notFoundError

end Dom.Spec
