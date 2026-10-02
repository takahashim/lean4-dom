import Dom.Spec.ReplaceData
import Dom.Spec.Remove

/-!
# `Node.normalize()` の関係意味論（§4.4）

`replace` と同じ方針。仕様本文から独立に書き写した関係を置き、
実行関数がそれを満たすことは `Dom/Spec/NormalizeSound.lean` で証明する。

step 4 で `ReplaceDataSpec` を、step 7 で `RemoveSpec` を composition する。

## 兄弟ごとに畳む（engine の読み）

仕様を字義どおり読むと、step 3-4 は run 全体の data を一度に連結して replace data を
一回だけ呼び、step 6 で boundary point を全部渡してから、step 7 で兄弟を全部外す。
実際の engine（Blink・WebCore・Gecko）は兄弟ごとに「data を足す・boundary point を渡す・外す」
を繰り返し、record の並びがそれで決まる（`Dom/CharacterData/Normalize.lean` の冒頭）。
本 model はこちらを採るので、関係も兄弟ごとに書く（`SiblingMerged`）。
木と live range の最終状態はどちらの読みでも同じで、違うのは record の並びだけである。

step 6 の `length` は「node の長さに、それまでに渡した兄弟の長さを足したもの」で、
兄弟ごとに畳む読みでは「この兄弟を足す直前の survivor の長さ」にあたる。

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

/-- `this` の descendant exclusive Text node を、最初の木の tree order で並べた列。 -/
def DescendantExclusiveTexts (t : Tree) (this : NodeId) : List NodeId :=
  ((preorder t this).drop 1).filter fun n => (t.get? n).any (·.kind == .text)

/-- **`normalize()` の関係意味論。** -/
def NormalizeSpec (s : DOMState) (this : NodeId) (s' : DOMState) : Prop :=
  (∃ d, s.tree.get? this = some d) ∧
    NormalizedEach this s (DescendantExclusiveTexts s.tree this) s'

/--
**`normalize()` の、結果まで含めた関係。**

失敗するのは `this` が木に無いとき（model の都合。IDL の受け手は必ず存在する）だけである。
-/
def NormalizeResult (s : DOMState) (this : NodeId) : Except DOMException DOMState → Prop
  | .ok s' => NormalizeSpec s this s'
  | .error e => s.tree.get? this = none ∧ e = .notFoundError

end Dom.Spec
