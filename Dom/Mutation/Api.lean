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
def appendChild (s : DOMState) (parent node : NodeId) : Except DOMException DOMState :=
  append s node parent

/-- DOM Standard §4.4 `Node.insertBefore(node, child)`。 -/
def insertBefore (s : DOMState) (parent node : NodeId) (child : Option NodeId) :
    Except DOMException DOMState :=
  preInsert s node parent child

/-- DOM Standard §4.4 `Node.replaceChild(node, child)`。 -/
def replaceChild (s : DOMState) (parent node child : NodeId) : Except DOMException DOMState :=
  replace s child node parent

/-- DOM Standard §4.4 `Node.removeChild(child)`。 -/
def removeChild (s : DOMState) (parent child : NodeId) : Except DOMException DOMState :=
  preRemove s child parent

/--
DOM Standard §4.2.6 `ParentNode.replaceChildren(nodes)`。

step 2 で `ensure pre-insert validity` を通してから replace all を行う。
-/
def replaceChildren (s : DOMState) (parent : NodeId) (node : Option NodeId) :
    Except DOMException DOMState :=
  match node with
  | none => replaceAll s none parent
  | some n =>
    -- step 2。仕様は childrenToExclude に `this` の children を渡す。
    -- 直後の replace all がそれらを外すので、個数の制約から除いてよい
    -- （whatwg/dom#1045）。
    match ensurePreInsertionValidity s.tree n parent none (childrenOf s.tree parent) with
    | .error e => .error e
    | .ok () => replaceAll s (some n) parent

/-- DOM Standard §4.2.9 `ChildNode.before(nodes)`。 -/
def before (s : DOMState) (this node : NodeId) : Except DOMException DOMState :=
  -- step 1-2
  match parentOf s.tree this with
  | none => .ok s
  | some parent =>
    -- step 3, 5, 6
    preInsert s node parent
      (match viablePreviousSibling s.tree this [node] with
       | none => (childrenOf s.tree parent).head?
       | some v => nextSibling s.tree v)

/-- DOM Standard §4.2.9 `ChildNode.after(nodes)`。 -/
def after (s : DOMState) (this node : NodeId) : Except DOMException DOMState :=
  -- step 1-2
  match parentOf s.tree this with
  | none => .ok s
  | some parent =>
    -- step 3, 5
    preInsert s node parent (viableNextSibling s.tree this [node])

/-- DOM Standard §4.2.9 `ChildNode.replaceWith(nodes)`。 -/
def replaceWith (s : DOMState) (this node : NodeId) : Except DOMException DOMState :=
  -- step 1-2
  match parentOf s.tree this with
  | none => .ok s
  | some parent =>
    -- step 5-6（step 3 の viableNextSibling は else 側でのみ使う）
    if parentOf s.tree this = some parent then replace s this node parent
    else preInsert s node parent (viableNextSibling s.tree this [node])

/-- DOM Standard §4.2.9 `ChildNode.remove()`。 -/
def nodeRemove (s : DOMState) (this : NodeId) : Except DOMException DOMState :=
  -- step 1-2
  match parentOf s.tree this with
  | none => .ok s
  | some _ => remove s this

/-- DOM Standard §4.2.6 `ParentNode.moveBefore(node, child)`。 -/
def moveBefore (s : DOMState) (parent node : NodeId) (child : Option NodeId) :
    Except DOMException DOMState :=
  match s.tree.get? parent with
  | none => .error .notFoundError
  | some pd =>
    -- `moveBefore` は `ParentNode` の method なので、receiver は IDL により
    -- Document / DocumentFragment / Element に限られる。
    -- move algorithm 自身にはこの検査が無いので（step 1-6 を参照）、
    -- API の側で表す。`Dom/Basic/NodeId.lean` の `canHaveChildren` がその三つである。
    if !pd.kind.canHaveChildren then .error .hierarchyRequestError
    else
      -- step 1-2
      let referenceChild := if child = some node then nextSibling s.tree node else child
      -- step 3
      move s node parent referenceChild

end Dom
