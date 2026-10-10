import Dom.Mutation.Api
import Dom.Mutation.Create
import Dom.Attribute.Node

/-!
# `insertAdjacentElement()` と `insertAdjacentText()`（§4.9）

"insert adjacent" は where を ASCII case-insensitive に読み、element の parent か element 自身に
pre-insert する。parent が無い beforebegin / afterend は null を返す（例外ではない）。
-/

namespace Dom

/-- "insert adjacent" の where。 -/
inductive AdjacentPosition where
  | beforebegin | afterbegin | beforeend | afterend
deriving Repr, DecidableEq

/-- where を ASCII case-insensitive に読む。どれでもなければ none（SyntaxError）。 -/
def adjacentPosition? (where_ : String) : Option AdjacentPosition :=
  match asciiLowercase where_ with
  | "beforebegin" => some .beforebegin
  | "afterbegin" => some .afterbegin
  | "beforeend" => some .beforeend
  | "afterend" => some .afterend
  | _ => none

/--
DOM Standard §4.9 "insert adjacent"。返り値の `none` は本文の「return null」で、
pre-insert したときはその node（pre-insert の返り値）を返す。
-/
def insertAdjacent (s : DOMState) (element : NodeId) (where_ : String) (node : NodeId) :
    Except DOMException (Option NodeId × DOMState) :=
  match adjacentPosition? where_ with
  | none => .error .syntaxError
  | some .beforebegin =>
    match parentOf s.tree element with
    | none => .ok (none, s)
    | some p => inserted (preInsert s node p (some element))
  | some .afterbegin => inserted (preInsert s node element (childrenOf s.tree element).head?)
  | some .beforeend => inserted (preInsert s node element none)
  | some .afterend =>
    match parentOf s.tree element with
    | none => .ok (none, s)
    | some p => inserted (preInsert s node p (nextSibling s.tree element))
where
  /-- pre-insert の結果に、返す node を添える。 -/
  inserted : Except DOMException DOMState → Except DOMException (Option NodeId × DOMState)
    | .error e => .error e
    | .ok s' => .ok (some node, s')

/-- DOM Standard §4.9 `Element.insertAdjacentElement(where, element)`。 -/
def insertAdjacentElement (s : DOMState) (element : NodeId) (where_ : String) (node : NodeId) :
    Except DOMException (Option NodeId × DOMState) :=
  match requireElement s.tree element with
  | .error e => .error e
  | .ok _ => insertAdjacent s element where_ node

/--
DOM Standard §4.9 `Element.insertAdjacentText(where, data)`。this の node document で Text を作り
（step 1）、insert adjacent する（step 2）。parent が無くて null が返るときは、作った Text をどこからも
参照できないので、状態は元のままにする。
-/
def insertAdjacentText (s : DOMState) (element : NodeId) (where_ : String) (data : String) :
    Except DOMException DOMState :=
  match requireElement s.tree element with
  | .error e => .error e
  | .ok d =>
    match createTextNode s d.ownerDocument data with
    | .error e => .error e
    | .ok (t, s₁) =>
      match insertAdjacent s₁ element where_ t with
      | .error e => .error e
      | .ok (none, _) => .ok s
      | .ok (some _, s₂) => .ok s₂

end Dom
