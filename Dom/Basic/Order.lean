import Dom.Basic.Tree
import Dom.Util.List

/-!
# Tree order と実行可能な走査

`Ancestor` は specification 側の（計算可能でない）定義なので、
root を求める、祖先を列挙する、tree order で走査する、といった処理は
fuel 付きの再帰として別に定義する（PLAN §3.2）。

fuel には store の要素数 `Tree.size` を渡す。
well-formed な木では fuel が尽きないことを `Dom/Properties/Tree.lean` で証明する。
-/

namespace Dom

/-! ## parent 方向の走査 -/

/--
`n` から parent を `fuel` 段までたどった結果。
途中で parent が無くなればそこで止まる。fuel が尽きた場合は到達した node を返す。
-/
def rootFuel (t : Tree) : Nat → NodeId → NodeId
  | 0, n => n
  | f + 1, n =>
    match parentOf t n with
    | none => n
    | some p => rootFuel t f p

/--
DOM Standard §4.2 の root。

fuel には store の要素数を渡す。well-formed な木ではこれで十分であることを
`root_parent_eq_none` で示す。
-/
def root (t : Tree) (n : NodeId) : NodeId :=
  rootFuel t t.size n

/-- `n` の strict ancestor を parent 側から順に `fuel` 段まで列挙する。 -/
def ancestorChain (t : Tree) : Nat → NodeId → List NodeId
  | 0, _ => []
  | f + 1, n =>
    match parentOf t n with
    | none => []
    | some p => p :: ancestorChain t f p

/-- `n` の strict ancestor の列。parent が先、root が最後。 -/
def ancestors (t : Tree) (n : NodeId) : List NodeId :=
  ancestorChain t t.size n

/--
`n` の深さ。root からの距離。

fuel 充足性の証明と、`preorder` の正しさの証明で減少量として使う。
-/
def depth (t : Tree) (n : NodeId) : Nat :=
  (ancestors t n).length

/-! ## child 方向の走査 -/

/--
`n` を根とする部分木を tree order（preorder）で列挙する。fuel は木の高さの上界。

木に含まれない node に対しては空列を返す。
-/
def preorderFuel (t : Tree) : Nat → NodeId → List NodeId
  | 0, _ => []
  | f + 1, n =>
    if t.contains n then n :: (childrenOf t n).flatMap (preorderFuel t f) else []

/--
DOM Standard §4.2 の tree order による、`n` の inclusive descendant の列挙。

well-formed な木ではちょうど inclusive descendant 全体を重複なく列挙することを
`mem_preorder_iff` と `preorder_nodup` で示す。
-/
def preorder (t : Tree) (n : NodeId) : List NodeId :=
  preorderFuel t t.size n

/--
`preorder` の鏡像。children を逆順にたどる preorder である。

DOM Standard §6.2 の `lastChild()` / `previousSibling()` は
「最後の子から、さらにその最後の子へ」と降りるので、この順に候補を見る。
列としては `preorder` と同じ node の集合を、逆向きの兄弟順で並べたものになる
（`mem_mirrorPreorderFuel_iff`）。
-/
def mirrorPreorderFuel (t : Tree) : Nat → NodeId → List NodeId
  | 0, _ => []
  | f + 1, n =>
    if t.contains n then n :: (childrenOf t n).reverse.flatMap (mirrorPreorderFuel t f) else []

/-- `mirrorPreorderFuel` に `preorder` と同じ fuel を与えたもの。 -/
def mirrorPreorder (t : Tree) (n : NodeId) : List NodeId :=
  mirrorPreorderFuel t t.size n

/-- `n` が属する木全体を tree order で列挙する。 -/
def treeOrder (t : Tree) (n : NodeId) : List NodeId :=
  preorder t (root t n)

/-! ## tree order での先行関係 -/

/--
`l` の中で `a` が `b` より前に現れるか。

先に現れたほうで判定を打ち切るので、`l` に重複があっても
「最初の出現位置の比較」という意味になる。
-/
def precedesIn : List NodeId → NodeId → NodeId → Bool
  | [], _, _ => false
  | x :: rest, a, b =>
    if x = a then decide (b ∈ rest)
    else if x = b then false
    else precedesIn rest a b

/--
DOM Standard §4.2 の tree order による先行関係。

`a` と `b` が同じ木に属さない場合は `false` を返す。
-/
def precedes (t : Tree) (a b : NodeId) : Bool :=
  precedesIn (treeOrder t a) a b

/-! ## 兄弟 -/

/-- `n` の次の兄弟。 -/
def nextSibling (t : Tree) (n : NodeId) : Option NodeId :=
  match parentOf t n with
  | none => none
  | some p =>
    match Dom.ListUtil.splitAt? (childrenOf t p) n with
    | none => none
    | some (_, after) => after.head?

/-- `n` の前の兄弟。 -/
def previousSibling (t : Tree) (n : NodeId) : Option NodeId :=
  match parentOf t n with
  | none => none
  | some p =>
    match Dom.ListUtil.splitAt? (childrenOf t p) n with
    | none => none
    | some (before, _) => before.getLast?

/-! ## ancestor 関係の決定手続き -/

/--
`a` が `n` の ancestor かを判定する。

`Ancestor` は `Prop` なので、mutation algorithm の前提条件検査にはこの boolean 版を使う。
well-formed な木で `Ancestor` と一致することを `isAncestorOf_iff` で示す。
-/
def isAncestorOf (t : Tree) (a n : NodeId) : Bool :=
  decide (a ∈ ancestors t n)

/-- `a` が `n` の inclusive ancestor かを判定する。 -/
def isInclusiveAncestorOf (t : Tree) (a n : NodeId) : Bool :=
  decide (a = n) || isAncestorOf t a n

/-! ## invariant の実行時検査で使う述語 -/

/-- `n` から parent をたどると `fuel` 段以内に parent を持たない node に到達するか。 -/
def parentChainTerminates (t : Tree) (fuel : Nat) (n : NodeId) : Bool :=
  (parentOf t (rootFuel t fuel n)).isNone

end Dom
