import Dom.Basic.State
import Dom.Basic.Order

/-!
# NodeIterator

DOM Standard §6.1 `NodeIterator` のうち、本 model が扱う部分を定義する。

filter（`whatToShow` と `NodeFilter`）は扱わない。
`whatToShow` が `SHOW_ALL` で filter が null の場合、すなわち
iterator collection がすべての node に一致する場合だけを model にする。
仕様の traverse は filter が accept するまで繰り返すが、
filter が無ければ 1 回で決まるので、`nextNode` / `previousNode` は
候補を一つ求めるだけの形になる。

仕様の candidate reference は traverse の途中でしか非 null にならないので、
状態としては持たない（`IteratorState` は root と reference だけを持つ）。
-/

namespace Dom

/--
DOM Standard §6.1 の iterator collection。

root を根とし、filter がすべての node に一致する collection なので、
root の inclusive descendant を tree order に並べたものになる。
-/
def iteratorCollection (t : Tree) (root : NodeId) : List NodeId :=
  preorder t root

/--
`n` より tree order で後ろにある node のうち、
`root` の inclusive descendant であって `n` の inclusive descendant でない最初のもの。

DOM Standard §6.1 "adjust a node pointer" の step 2.1 に対応する。
仕様の following は tree order の following なので、`n` の子孫も following に含まれる。
そのため「`n` の inclusive descendant でない」という条件が要る。
-/
def firstFollowingOutside (t : Tree) (root n : NodeId) : Option NodeId :=
  match Dom.ListUtil.splitAt? (treeOrder t n) n with
  | none => none
  | some (_, after) =>
    after.find? fun x => isInclusiveAncestorOf t root x && !isInclusiveAncestorOf t n x

/--
DOM Standard §6.1 "adjust a node pointer"。

`toBeRemoved` の removal の直前に、node pointer `(node, pointerBefore)` を更新する。
-/
def adjustNodePointer (t : Tree) (root toBeRemoved : NodeId) (node : NodeId)
    (pointerBefore : Bool) : NodeId × Bool :=
  -- step 1
  if !isInclusiveAncestorOf t toBeRemoved node then (node, pointerBefore)
  else if isInclusiveAncestorOf t toBeRemoved root then (node, pointerBefore)
  else
    -- step 2
    match (if pointerBefore then firstFollowingOutside t root toBeRemoved else none) with
    | some next => (next, true)
    | none =>
      -- step 3-4
      match previousSibling t toBeRemoved with
      | none => ((parentOf t toBeRemoved).getD toBeRemoved, false)
      | some prev => (Dom.ListUtil.lastD (preorder t prev) prev, false)

/-- DOM Standard §6.1 "NodeIterator pre-remove steps" を iterator 一つに適用する。 -/
def iteratorPreRemoveOne (t : Tree) (toBeRemoved : NodeId) (it : IteratorState) :
    IteratorState :=
  let r := adjustNodePointer t it.root toBeRemoved it.reference it.pointerBeforeReference
  { it with reference := r.1, pointerBeforeReference := r.2 }

/--
DOM Standard §4.2.3 remove step 4 / move step 11。

仕様どおり、root の node document が削除する node の node document と同じ
iterator だけを対象にする。
-/
def iteratorPreRemove (s : DOMState) (node : NodeId) : DOMState :=
  { s with
      iterators := s.iterators.map fun it =>
        if ownerDocumentOf s.tree it.root == ownerDocumentOf s.tree node then
          iteratorPreRemoveOne s.tree node it
        else it }

@[simp] theorem iteratorPreRemove_tree (s : DOMState) (n : NodeId) :
    (iteratorPreRemove s n).tree = s.tree := rfl

@[simp] theorem iteratorPreRemove_registrations (s : DOMState) (n : NodeId) :
    (iteratorPreRemove s n).registrations = s.registrations := rfl

@[simp] theorem iteratorPreRemove_observers (s : DOMState) (n : NodeId) :
    (iteratorPreRemove s n).observers = s.observers := rfl


@[simp] theorem iteratorPreRemove_ranges (s : DOMState) (n : NodeId) :
    (iteratorPreRemove s n).ranges = s.ranges := rfl

/-! ## 走査 -/

/--
DOM Standard §6.1 `nextNode()`。

filter が無いので、仕様の traverse は 1 周で決まる。
返り値は「返した node と、更新後の iterator」。collection の終端なら `none`。
-/
def nextNode (t : Tree) (it : IteratorState) : Option (NodeId × IteratorState) :=
  if it.pointerBeforeReference then
    some (it.reference, { it with pointerBeforeReference := false })
  else
    match Dom.ListUtil.splitAt? (iteratorCollection t it.root) it.reference with
    | none => none
    | some (_, after) =>
      match after.head? with
      | none => none
      | some n => some (n, { it with reference := n, pointerBeforeReference := false })

/-- DOM Standard §6.1 `previousNode()`。 -/
def previousNode (t : Tree) (it : IteratorState) : Option (NodeId × IteratorState) :=
  if !it.pointerBeforeReference then
    some (it.reference, { it with pointerBeforeReference := true })
  else
    match Dom.ListUtil.splitAt? (iteratorCollection t it.root) it.reference with
    | none => none
    | some (before, _) =>
      match Dom.ListUtil.lastD (before.map some) none with
      | none => none
      | some n => some (n, { it with reference := n, pointerBeforeReference := true })

/-! ## validity -/

/--
PLAN §9.2 の `IteratorsValid`。

reference が木にあり、root の inclusive descendant であること。
-/
def ValidIterator (t : Tree) (it : IteratorState) : Prop :=
  (∃ d, t.get? it.reference = some d) ∧ InclusiveDescendant t it.reference it.root

def IteratorsValid (s : DOMState) : Prop :=
  ∀ it ∈ s.iterators, ValidIterator s.tree it

/-- 実行時の検査。 -/
def checkValidIterator (t : Tree) (it : IteratorState) : Bool :=
  (t.get? it.reference).isSome && isInclusiveAncestorOf t it.root it.reference

def checkIteratorsValid (s : DOMState) : Bool :=
  s.iterators.all (checkValidIterator s.tree)

end Dom
