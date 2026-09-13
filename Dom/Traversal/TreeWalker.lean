import Dom.Traversal.NodeIterator

/-!
# TreeWalker

DOM Standard §6.2 `TreeWalker` のうち、本 model が扱う部分を定義する。

`NodeFilter` の callback は model の外なので、filter は常に null として扱う
（`NodeIterator` と同じ `showsNode` を使う）。
**filter が null なら "filter" は FILTER_ACCEPT か FILTER_SKIP しか返さない。**
FILTER_REJECT が出ないので、仕様の走査はどれも
「tree order（あるいはその鏡像）に並べた候補列の先頭から、accept される最初のもの」
になる。以下の定義はその形で書いてある。

## current が root から外れている場合

`NodeIterator` と違い、§6.2 には "removing steps" が無い。
`current` の祖先が remove されれば、`current` は walker の root から外れたままになる。
仕様の走査はそれでも動く——`root` に当たらないまま木の頂上まで上がって止まるので、
**`current` 側の木の中を歩く**ことになる。`walkerBase` がその「上限」である。

`root` が `current` の子孫に来るような状態は、この model の操作からは作れない
（`current` は root の子孫から始まり、remove で外れることはあっても入れ替わらない）ので、
上の対応はその範囲での話である。
-/

namespace Dom

/-- filter が null なので、accept は `whatToShow` だけで決まる。 -/
def walkerAccepts (t : Tree) (w : WalkerState) (n : NodeId) : Bool :=
  showsNode t w.whatToShow n

/--
走査の上限。

`current` が `root` の inclusive descendant なら `root`、
そうでなければ `current` 側の木の根である。
-/
def walkerBase (t : Tree) (w : WalkerState) : NodeId :=
  if isInclusiveAncestorOf t w.root w.current then w.root else root t w.current

/-- `n` の後ろの兄弟を順に。 -/
def followingSiblings (t : Tree) (n : NodeId) : List NodeId :=
  match parentOf t n with
  | none => []
  | some p =>
    match Dom.ListUtil.splitAt? (childrenOf t p) n with
    | none => []
    | some (_, after) => after

/-- `n` の前の兄弟を、近いほうから順に。 -/
def precedingSiblings (t : Tree) (n : NodeId) : List NodeId :=
  match parentOf t n with
  | none => []
  | some p =>
    match Dom.ListUtil.splitAt? (childrenOf t p) n with
    | none => []
    | some (before, _) => before.reverse

/-- `p` を満たす最初の要素までを、それも含めて取る。 -/
def takeUntilIncl {α : Type} (p : α → Bool) : List α → List α
  | [] => []
  | x :: rest => if p x then [x] else x :: takeUntilIncl p rest

/-! ## 走査 -/

/--
DOM Standard §6.2 `nextNode()`。

FILTER_REJECT が無いので、走査は `walkerBase` を根とする部分木の tree order を
`current` の次から順に見ていくことに等しい。
仕様の step 3.4.1「temporary が root なら null」が、`walkerBase` で列を切ることにあたる。
-/
def walkerNextNode (t : Tree) (w : WalkerState) : Option NodeId :=
  match Dom.ListUtil.splitAt? (preorder t (walkerBase t w)) w.current with
  | none => none
  | some (_, after) => after.find? (walkerAccepts t w)

/--
DOM Standard §6.2 `previousNode()`。

仕様の step 2.2.3 は「前の兄弟の、最後の子をたどれるだけたどった先」へ降りる。
これは tree order のひとつ前の node であり、step 2.4-2.5 の親へ上がる枝と合わせると
「tree order を逆にたどる」ことになる。`root` 自身も候補に入る。
-/
def walkerPreviousNode (t : Tree) (w : WalkerState) : Option NodeId :=
  match Dom.ListUtil.splitAt? (preorder t (walkerBase t w)) w.current with
  | none => none
  | some (before, _) => before.reverse.find? (walkerAccepts t w)

/--
DOM Standard §6.2 `firstChild()`（"traverse children" の type=first）。

SKIP された子には降りるので、候補は `current` の（自身を除く）子孫を tree order に
並べたものになる。仕様の step 3.4.4「parent が root か current なら null」が、
`current` の部分木で列を切ることにあたる。
-/
def walkerFirstChild (t : Tree) (w : WalkerState) : Option NodeId :=
  ((preorder t w.current).drop 1).find? (walkerAccepts t w)

/--
DOM Standard §6.2 `lastChild()`（"traverse children" の type=last）。

`firstChild()` の鏡像で、子を後ろから見て、降りるときも最後の子へ降りる。
候補の順序は `mirrorPreorder` である。
-/
def walkerLastChild (t : Tree) (w : WalkerState) : Option NodeId :=
  ((mirrorPreorder t w.current).drop 1).find? (walkerAccepts t w)

/--
DOM Standard §6.2 `parentNode()`。

`current` の祖先を近いほうから見て、最初に accept されたものを返す。
`root` 自身は候補に入るが、その先へは上がらない（step 2 の while 条件）。
`current` が `root` そのものなら何もしない。
-/
def walkerParentNode (t : Tree) (w : WalkerState) : Option NodeId :=
  if w.current == w.root then none
  else (takeUntilIncl (· == w.root) (ancestors t w.current)).find? (walkerAccepts t w)

/-- "traverse siblings" が一つの段で見る候補。兄弟の部分木を順に並べたものである。 -/
def siblingCandidates (t : Tree) (n : NodeId) (after : Bool) : List NodeId :=
  (if after then followingSiblings t n else precedingSiblings t n).flatMap
    fun s => if after then preorder t s else mirrorPreorder t s

/--
DOM Standard §6.2 "traverse siblings" の外側の loop。

引数は `current` から根へ向かう chain である。段ごとに兄弟の部分木を見て、
見つからなければ親へ上がる。**親が root なら、あるいは親が accept されるなら止まる**
（step 3.3-3.5）。降りる途中の node は SKIP されたものばかりなので、
上がるときに引っかかるのは `current` の祖先だけである。
-/
def walkerSiblingSearch (t : Tree) (w : WalkerState) (after : Bool) :
    List NodeId → Option NodeId
  | [] => none
  -- 根まで来た。親が無いので上がれない。
  | [n] => (siblingCandidates t n after).find? (walkerAccepts t w)
  | n :: p :: rest =>
    match (siblingCandidates t n after).find? (walkerAccepts t w) with
    | some x => some x
    | none =>
      if p == w.root || walkerAccepts t w p then none
      else walkerSiblingSearch t w after (p :: rest)

/-- DOM Standard §6.2 `nextSibling()` / `previousSibling()`。 -/
def walkerSibling (t : Tree) (w : WalkerState) (after : Bool) : Option NodeId :=
  if w.current == w.root then none
  else walkerSiblingSearch t w after (w.current :: ancestors t w.current)

/-! ## 状態の更新 -/

/-- walker を一つ差し替える。 -/
def withWalker (s : DOMState) (i : Nat) (w : WalkerState) : DOMState :=
  { s with walkers := s.walkers.set i w }

/--
番号で指した walker を走らせる。

返した node があれば `current` をそこへ動かす。無ければ状態は変わらない。
-/
def walkerRun (s : DOMState) (i : Nat) (f : Tree → WalkerState → Option NodeId) :
    Except DOMException (Option NodeId × DOMState) :=
  match s.walkers[i]? with
  | none => .error .notFoundError
  | some w =>
    match f s.tree w with
    | none => .ok (none, s)
    | some n => .ok (some n, withWalker s i { w with current := n })

/-- §6.2 の走査 method。 -/
inductive WalkerMethod where
  | parentNode
  | firstChild
  | lastChild
  | previousSibling
  | nextSibling
  | previousNode
  | nextNode
deriving DecidableEq, Repr, Inhabited

/-- method から走査を選ぶ。 -/
def walkerMethod : WalkerMethod → Tree → WalkerState → Option NodeId
  | .parentNode, t, w => walkerParentNode t w
  | .firstChild, t, w => walkerFirstChild t w
  | .lastChild, t, w => walkerLastChild t w
  | .previousSibling, t, w => walkerSibling t w false
  | .nextSibling, t, w => walkerSibling t w true
  | .previousNode, t, w => walkerPreviousNode t w
  | .nextNode, t, w => walkerNextNode t w

/-- 番号で指した walker の method を走らせる。 -/
def walkerStep (s : DOMState) (i : Nat) (m : WalkerMethod) :
    Except DOMException (Option NodeId × DOMState) :=
  walkerRun s i (walkerMethod m)

/-! ## validity -/

/--
walker の両端が木にあること。

`NodeIterator` の `ValidIterator` と違い、
**`current` が `root` の inclusive descendant であることは要求しない**。
§6.2 には "removing steps" が無いので、remove はその関係を壊す。
それは仕様どおりの挙動であり、model の不変条件にはできない。
-/
def ValidWalker (t : Tree) (w : WalkerState) : Prop :=
  (∃ d, t.get? w.root = some d) ∧ (∃ d, t.get? w.current = some d)

def WalkersValid (s : DOMState) : Prop :=
  ∀ w ∈ s.walkers, ValidWalker s.tree w

/-- 実行時の検査。 -/
def checkValidWalker (t : Tree) (w : WalkerState) : Bool :=
  (t.get? w.root).isSome && (t.get? w.current).isSome

def checkWalkersValid (s : DOMState) : Bool :=
  s.walkers.all (checkValidWalker s.tree)

end Dom
