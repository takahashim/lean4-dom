import Dom.Selector.Match

/-!
# selector を使う DOM の API

DOM Standard §1.3 "scope-match a selectors string"、§4.2.6 `ParentNode` の
`querySelector()` / `querySelectorAll()`、§4.8 `Element` の `matches()` / `closest()`。

どれも parse に失敗したら `SyntaxError` を投げる。
-/

namespace Dom

open Selectors

/--
DOM Standard §1.3 "scope-match a selectors string"。

候補は `node` の root の inclusive descendant のうち element であるもので、
scoping root `node` の descendant に絞る。つまり `node` 自身は入らない。
-/
def scopeMatch (t : Tree) (selectors : String) (node : NodeId) :
    Except DOMException (List NodeId) :=
  match parseSelector selectors with
  | none => .error .syntaxError
  | some sel =>
    let ctx : MatchCtx := { tree := t, scope := some node }
    let cands := (preorder t node).tail.filter (isElementNode t)
    .ok (cands.filter (fun e => matchSelList ctx sel e))

/--
receiver が `ParentNode`（Document / DocumentFragment / Element）か検査する。

`querySelector()` はこの三つにしか無い method なので、それ以外の node に対しては
WebIDL の `TypeError` になる。検査は method 本体より前、つまり
`parse a selector` より前に起きる。
-/
def requireParentNode (t : Tree) (node : NodeId) : Except DOMException Unit :=
  match t.get? node with
  | none => .error .typeError
  | some d => if d.kind.canHaveChildren then .ok () else .error .typeError

/-- `matches()` と `closest()` は `Element` の method である。 -/
def requireElementNode (t : Tree) (node : NodeId) : Except DOMException Unit :=
  match t.get? node with
  | none => .error .typeError
  | some d => if d.kind == .element then .ok () else .error .typeError

/-- §4.2.6 `ParentNode.querySelector()`。 -/
def querySelector (t : Tree) (selectors : String) (node : NodeId) :
    Except DOMException (Option NodeId) := do
  let _ <- requireParentNode t node
  return (<- scopeMatch t selectors node).head?

/-- §4.2.6 `ParentNode.querySelectorAll()`。 -/
def querySelectorAll (t : Tree) (selectors : String) (node : NodeId) :
    Except DOMException (List NodeId) := do
  let _ <- requireParentNode t node
  scopeMatch t selectors node

/-- §4.8 `Element.matches()`。scoping root は element 自身である。 -/
def matchesSelector (t : Tree) (selectors : String) (element : NodeId) :
    Except DOMException Bool := do
  let _ <- requireElementNode t element
  match parseSelector selectors with
  | none => .error .syntaxError
  | some sel => .ok (matchSelList { tree := t, scope := some element } sel element)

/--
§4.8 `Element.closest()`。

inclusive ancestor を tree order の逆、つまり自分から root へ向かって見る。
-/
def closest (t : Tree) (selectors : String) (element : NodeId) :
    Except DOMException (Option NodeId) := do
  let _ <- requireElementNode t element
  match parseSelector selectors with
  | none => .error .syntaxError
  | some sel =>
    let ctx : MatchCtx := { tree := t, scope := some element }
    let chain := (element :: ancestors t element).filter (isElementNode t)
    .ok (chain.find? (fun e => matchSelList ctx sel e))

end Dom
