import Dom.Mutation.Algorithms

/-!
# public API に相当する操作

PLAN §6.1。`appendChild` などの public API は §4.2.3 の algorithm の薄い wrapper として
定義し、primitive（`detach`, `insertAt`）を直接呼ばない。
この一方向の依存が、`memo.md` の言う「どの API から始めても
live object の調整が迂回されない」ことの土台になる。

仕様の `before()` / `after()` / `replaceWith()` / `replaceChildren()` は
可変長引数を "converting nodes into a node" で一つの node にまとめるが、
本 model は node を生成しないので、まとめた結果の node を引数として受け取る形にする。
-/

namespace Dom

/-- DOM Standard §4.4 `Node.appendChild(node)`。 -/
def appendChild (t : Tree) (parent node : NodeId) : Except DOMException Tree :=
  append t node parent

/-- DOM Standard §4.4 `Node.insertBefore(node, child)`。 -/
def insertBefore (t : Tree) (parent node : NodeId) (child : Option NodeId) :
    Except DOMException Tree :=
  preInsert t node parent child

/-- DOM Standard §4.4 `Node.replaceChild(node, child)`。 -/
def replaceChild (t : Tree) (parent node child : NodeId) : Except DOMException Tree :=
  replace t child node parent

/-- DOM Standard §4.4 `Node.removeChild(child)`。 -/
def removeChild (t : Tree) (parent child : NodeId) : Except DOMException Tree :=
  preRemove t child parent

/--
DOM Standard §4.2.6 `ParentNode.replaceChildren(nodes)`。

step 2 で `ensure pre-insert validity` を通してから replace all を行う。
-/
def replaceChildren (t : Tree) (parent : NodeId) (node : Option NodeId) :
    Except DOMException Tree :=
  match node with
  | none => replaceAll t none parent
  | some n =>
    match ensurePreInsertionValidity t n parent none [] with
    | .error e => .error e
    | .ok () => replaceAll t (some n) parent

/-- DOM Standard §4.2.9 `ChildNode.before(nodes)`。 -/
def before (t : Tree) (this node : NodeId) : Except DOMException Tree :=
  -- step 1-2
  match parentOf t this with
  | none => .ok t
  | some parent =>
    -- step 3, 5, 6
    preInsert t node parent
      (match viablePreviousSibling t this [node] with
       | none => (childrenOf t parent).head?
       | some v => nextSibling t v)

/-- DOM Standard §4.2.9 `ChildNode.after(nodes)`。 -/
def after (t : Tree) (this node : NodeId) : Except DOMException Tree :=
  -- step 1-2
  match parentOf t this with
  | none => .ok t
  | some parent =>
    -- step 3, 5
    preInsert t node parent (viableNextSibling t this [node])

/-- DOM Standard §4.2.9 `ChildNode.replaceWith(nodes)`。 -/
def replaceWith (t : Tree) (this node : NodeId) : Except DOMException Tree :=
  -- step 1-2
  match parentOf t this with
  | none => .ok t
  | some parent =>
    -- step 5-6（step 3 の viableNextSibling は else 側でのみ使う）
    if parentOf t this = some parent then replace t this node parent
    else preInsert t node parent (viableNextSibling t this [node])

/-- DOM Standard §4.2.9 `ChildNode.remove()`。 -/
def nodeRemove (t : Tree) (this : NodeId) : Except DOMException Tree :=
  -- step 1-2
  match parentOf t this with
  | none => .ok t
  | some _ => remove t this

/-- DOM Standard §4.2.6 `ParentNode.moveBefore(node, child)`。 -/
def moveBefore (t : Tree) (parent node : NodeId) (child : Option NodeId) :
    Except DOMException Tree :=
  -- step 1-2
  let referenceChild := if child = some node then nextSibling t node else child
  -- step 3
  move t node parent referenceChild

end Dom
