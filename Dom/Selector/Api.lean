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
Selectors Level 4 §17.3 "match a selector against a tree"。

step 1 の候補は root element とその descendant すべてを tree order に並べたもので、
ここでは `node` の root からではなく `node` から下だけを見れば足りる。
scoping root は `node` なので、step 2 でそれ以外は落ちるからである。
step 2 は `e != node` と `isElementNode` の二つで表す。`node` 自身は
descendant ではないので候補に入らない。
-/
def matchTree (t : Tree) (sel : SelectorList) (node : NodeId) : List NodeId :=
  let ctx : MatchCtx := { tree := t, scope := some node }
  ((preorder t node).filter (fun e => e != node && isElementNode t e)).filter
    (fun e => matchSelList ctx sel e)

/-- DOM Standard §1.3 "scope-match a selectors string"。 -/
def scopeMatch (t : Tree) (selectors : String) (node : NodeId) :
    Except DOMException (List NodeId) :=
  match parseSelector selectors with
  | none => .error .syntaxError
  | some sel => .ok (matchTree t sel node)

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
    Except DOMException (Option NodeId) :=
  match requireParentNode t node with
  | .error e => .error e
  | .ok _ =>
    match scopeMatch t selectors node with
    | .error e => .error e
    | .ok l => .ok l.head?

/-- §4.2.6 `ParentNode.querySelectorAll()`。 -/
def querySelectorAll (t : Tree) (selectors : String) (node : NodeId) :
    Except DOMException (List NodeId) :=
  match requireParentNode t node with
  | .error e => .error e
  | .ok _ => scopeMatch t selectors node

/-- §4.8 `Element.matches()`。scoping root は element 自身である。 -/
def matchesSelector (t : Tree) (selectors : String) (element : NodeId) :
    Except DOMException Bool :=
  match requireElementNode t element with
  | .error e => .error e
  | .ok _ =>
    match parseSelector selectors with
    | none => .error .syntaxError
    | some sel => .ok (matchSelList { tree := t, scope := some element } sel element)

/--
`closest()` が見る列。自分から root へ向かう inclusive ancestor のうち element。

tree order の逆に並ぶので、先頭にあるものほど `element` に近い。
-/
def inclusiveAncestorElements (t : Tree) (n : NodeId) : List NodeId :=
  (n :: ancestors t n).filter (isElementNode t)

/--
§4.8 `Element.closest()`。

inclusive ancestor を tree order の逆、つまり自分から root へ向かって見る。
-/
def closest (t : Tree) (selectors : String) (element : NodeId) :
    Except DOMException (Option NodeId) :=
  match requireElementNode t element with
  | .error e => .error e
  | .ok _ =>
  match parseSelector selectors with
  | none => .error .syntaxError
  | some sel =>
    let ctx : MatchCtx := { tree := t, scope := some element }
    .ok ((inclusiveAncestorElements t element).find? (fun e => matchSelList ctx sel e))

end Dom
