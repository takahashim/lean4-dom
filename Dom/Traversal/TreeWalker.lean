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
`current` の祖先が remove されれば、`current` は walker の root から外れたままになる
（scenario の初期状態でも、current を root の外に置ける）。
仕様の走査はそれでも動く。走査は **`current` 側の木の中を歩き**、途中で `root` に当たったときだけ
本文の止まる条件が効く。どこで止まるかは method ごとに違い、それぞれの定義に書いてある
（`nextNode()` は `root` を見終えたところ、"traverse children" と "traverse siblings" は
`root` へ親として上がるところ、`previousNode()` は `previousStopsAtRoot`）。
-/

namespace Dom

/-- filter が null なので、accept は `whatToShow` だけで決まる。 -/
def walkerAccepts (t : Tree) (w : WalkerState) (n : NodeId) : Bool :=
  showsNode t w.whatToShow n

/--
`root` の inclusive descendant のうち tree order で最後のもの（`root` に children が無ければ `root`）。

`nextNode()` の走査は、`root` を見終えて上がろうとするところで止まる（step 3.4.1「temporary が root なら null」）。
それは tree order で見ると、この node を見終えたところで止まることである（`root` が葉でも同じ）。
"traverse children" と "traverse siblings" は親へ上がったときにそれが `root` なら止まるので、
この node で止まるのは `root` に children があるときだけである（`cutAtRootExit`）。
-/
def lastDescendant (t : Tree) (n : NodeId) : NodeId :=
  (preorder t n).getLastD n

/-- `lastDescendant` の鏡像：`mirrorPreorder` で最後のもの。 -/
def mirrorLastDescendant (t : Tree) (n : NodeId) : NodeId :=
  (mirrorPreorder t n).getLastD n

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

/--
子孫へ降りていく走査（"traverse children"・"traverse siblings"）の候補列を、root で止まるところで切る。

`L` は root `r` の最後の inclusive descendant（鏡像の走査なら鏡像の順序で最後のもの）である。
本文の走査は「親へ上がったときにそれが root なら null」（traverse children step 3.4.4、
traverse siblings step 3.3-3.4）なので、止まるのは root の子孫を見終えて root へ上がるときだけである。
root に children があれば、それは `L` を見終えたところにあたるので、`L` で切る。
root に children が無ければ（`L = r`）、走査が root へ親として上がることは無く、
root を見たあとも兄弟へ進む（traverse children step 3.4.2、traverse siblings step 3.2.5）ので、切らない。
-/
def cutAtRootExit (r L : NodeId) (l : List NodeId) : List NodeId :=
  if L == r then l else takeUntilIncl (· == L) l

/--
`previousNode()` の走査が root に達したところで止まるか。

root に children があれば、走査は root の最初の子から root へ親として上がってくる（step 2.4）ので、
root を見たあと step 2 の while 条件で止まる。
root に children が無ければ、走査は root を前の兄弟として（あるいはその最後の子として）見る（step 2.2）。
そのあと root に前の兄弟があれば step 2.2 の inner loop がそちらへ続き、
無ければ step 2.3「node が root なら null」で止まる。
-/
def previousStopsAtRoot (t : Tree) (r : NodeId) : Bool :=
  !(childrenOf t r).isEmpty || (precedingSiblings t r).isEmpty

/-! ## 走査 -/

/--
DOM Standard §6.2 `nextNode()`。

FILTER_REJECT が無いので、走査は `current` の木の tree order を `current` の次から順に見ていくことに
等しい。仕様の step 3.4.1「temporary が root なら null」は、`root` の最後の inclusive descendant を
見終えたところで止まることである（`current` が `root` の外にあっても、走査が `root` の部分木を通れば
そこで止まる）。`current` がその node なら、何も見ずに止まる。
-/
def walkerNextNode (t : Tree) (w : WalkerState) : Option NodeId :=
  match Dom.ListUtil.splitAt? (treeOrder t w.current) w.current with
  | none => none
  | some (_, after) =>
    if w.current == lastDescendant t w.root then none
    else (takeUntilIncl (· == lastDescendant t w.root) after).find? (walkerAccepts t w)

/--
DOM Standard §6.2 `previousNode()`。

仕様の step 2.2.3 は「前の兄弟の、最後の子をたどれるだけたどった先」へ降りる。
これは tree order のひとつ前の node であり、step 2.4-2.5 の親へ上がる枝と合わせると
「tree order を逆にたどる」ことになる。step 2 の while 条件により、`current` が `root` なら何も見ない。
走査が `root` に達したときに止まるかは `previousStopsAtRoot` が決める。止まるなら `root` を見たところで
列を切る（step 2 の while 条件か step 2.3）。止まらないのは `root` に children が無く前の兄弟があるときで、
そのときは `root` を越えて前へ進む（step 2.2.5）。`current` が `root` の外にあっても同じである。
-/
def walkerPreviousNode (t : Tree) (w : WalkerState) : Option NodeId :=
  if w.current == w.root then none
  else
    match Dom.ListUtil.splitAt? (treeOrder t w.current) w.current with
    | none => none
    | some (before, _) =>
      (if previousStopsAtRoot t w.root then takeUntilIncl (· == w.root) before.reverse
       else before.reverse).find? (walkerAccepts t w)

/--
DOM Standard §6.2 `firstChild()`（"traverse children" の type=first）。

SKIP された子には降りるので（step 3.3）、候補は `current` の（自身を除く）子孫を tree order に
並べたものになる。仕様の step 3.4.4「parent が null か root か current なら null」のうち、
current で止まるのは `current` の部分木を見終えたところ（列の終わり）である。
root で止まるのは、`root` が `current` の子孫で children を持ち、その子孫を見終えたときで、
`cutAtRootExit` がそこで切る。
-/
def walkerFirstChild (t : Tree) (w : WalkerState) : Option NodeId :=
  (cutAtRootExit w.root (lastDescendant t w.root) ((preorder t w.current).drop 1)).find?
    (walkerAccepts t w)

/--
DOM Standard §6.2 `lastChild()`（"traverse children" の type=last）。

`firstChild()` の鏡像で、子を後ろから見て、降りるときも最後の子へ降りる。
候補の順序は `mirrorPreorder` で、`root` で切る位置もその鏡像である。
-/
def walkerLastChild (t : Tree) (w : WalkerState) : Option NodeId :=
  (cutAtRootExit w.root (mirrorLastDescendant t w.root) ((mirrorPreorder t w.current).drop 1)).find?
    (walkerAccepts t w)

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
DOM Standard §6.2 "traverse siblings" の外側の loop が見る候補を、段ごとに並べた列。

引数は `current` から根へ向かう chain である。段ごとに兄弟の部分木を見て（step 3.2）、
見つからなければ親へ上がる。**親が root なら、あるいは親が accept されるなら止まる**
（step 3.3-3.5）。
-/
def siblingLevels (t : Tree) (w : WalkerState) (after : Bool) : List NodeId → List NodeId
  | [] => []
  -- 根まで来た。親が無いので上がれない。
  | [n] => siblingCandidates t n after
  | n :: p :: rest =>
    siblingCandidates t n after ++
      (if p == w.root || walkerAccepts t w p then [] else siblingLevels t w after (p :: rest))

/--
DOM Standard §6.2 `nextSibling()` / `previousSibling()`（"traverse siblings"）。

step 2 により `current` が `root` なら null。そうでなければ `siblingLevels` の列で探す。
step 3.2 の inner loop は兄弟の子へ降り（step 3.2.4）、子を尽くすと兄弟の次の兄弟へ進むが（step 3.2.5）、
次の兄弟が無ければ inner loop を抜けて step 3.3 で親へ上がる。だから兄弟の部分木の中から上がるときにも
step 3.4「node が root なら null」が効く。それは `root` が兄弟の部分木の中にあって children を持つとき、
その子孫を見終えたところで止まることであり、`cutAtRootExit` がそこで切る。
（step 3.5 の accept の検査は、兄弟の部分木の中では SKIP された node にしか当たらないので効かない。）
-/
def walkerSibling (t : Tree) (w : WalkerState) (after : Bool) : Option NodeId :=
  if w.current == w.root then none
  else
    (cutAtRootExit w.root
        (if after then lastDescendant t w.root else mirrorLastDescendant t w.root)
        (siblingLevels t w after (w.current :: ancestors t w.current))).find?
      (walkerAccepts t w)

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
