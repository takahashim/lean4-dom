import Dom.Attribute.Node
import Dom.Query.NodeQuery
import Dom.Mutation.Api
import Dom.Mutation.Import

/-!
# `Attr` を `Node` として扱う（§4.4・§4.5・§4.9）

仕様の `Attr` は `Node` を継承するので、`Node` の method と、`Node` を受ける method に渡せる。
model の attribute は node tree に入らない（element の状態として持つ）が、`Attr` が node として
持つ性質は次のとおりで、どれも attribute の持ち物か、その element から決まる。

| 性質 | 仕様 | model |
| --- | --- | --- |
| parent | `Attr` は木に入らないので常に null | `attrParentNode` |
| node document | "create an attribute" は受け手、"append" と "replace" は element のもの、adopt で書き換わる | `Attr.ownerDocument` |
| root | parent が無いので自分自身 | `attrGetRootNode` |
| tree order | 入らない。`compareDocumentPosition` だけが element の位置を借りて比べる（step 3-5） | `compareDocumentPositionRef` |
| `nodeValue` / `textContent` | value。書くと "set an existing attribute value" | `setAttrValue` |
| `equals` | namespace・local name・value | `nodeRefEquals` |
| 子 | 持てない。`appendChild` は pre-insertion validity の step 1 か 4 で `HierarchyRequestError` | `appendChildRef` |

## adopt

§4.5 "adopt" は node の parent を外して node document を書き換える。`Attr` は parent を持たない
ので、**element に付いたままでも外さずに node document だけを変える**。仕様の本文はそう読める。
browser（Chromium・Firefox・WebKit）は element から外す（DOM4 にあった振る舞い）。
model は本文どおりに書いてある。
-/

namespace Dom

open Dom.ListUtil

/-- `Node` を受ける引数。node tree の node か、`Attr`。 -/
inductive NodeRef where
  | node (n : NodeId)
  | attr (a : AttrId)
deriving DecidableEq, Repr, Inhabited

/-! ## `Attr` の持ち物 -/

/-- `Attr` の element（仕様の "element"、IDL の `ownerElement`）。 -/
def attrOwnerElement (s : DOMState) (aid : AttrId) : Option NodeId :=
  match findAttr s aid with
  | some (_, owner) => owner
  | none => none

/-- `Attr` の parent。木に入らないので常に null。 -/
def attrParentNode (_s : DOMState) (_aid : AttrId) : Option NodeId := none

/-- `getRootNode()`。parent が無いので自分自身が root である。 -/
def attrGetRootNode (_s : DOMState) (aid : AttrId) : NodeRef := .attr aid

/-! ## `Attr` を一つ書き換える -/

/--
`aid` の attribute だけを `f` で書き換える。element に付いていればその attribute list の中で、
付いていなければ detach された list の中で書き換える。
-/
def modifyAttr (s : DOMState) (aid : AttrId) (f : Attr → Attr) : DOMState :=
  match ownerElementOf s.tree aid with
  | some n =>
    match s.tree.get? n with
    | none => s
    | some d =>
      if d.kind = .element then
        s.withTree (setAttributes s.tree n d (d.attributes.map fun b => if b.id == aid then f b else b))
      else s
  | none => { s with detachedAttrs := s.detachedAttrs.map fun b => if b.id == aid then f b else b }

/-! ## `adoptNode` / `importNode` / `cloneNode` -/

/--
DOM Standard §4.5 `adoptNode(node)` に `Attr` を渡したとき。

step 1-2（Document・shadow root）は当たらない。step 3 の "adopt" は、parent が無いので
step 2 を飛ばし、node document が違えば `Attr` 自身（shadow-including inclusive descendant は
自分だけ）の node document を書き換える。element からは外さない。
-/
def adoptAttr (s : DOMState) (doc : NodeId) (aid : AttrId) : Except DOMException (AttrId × DOMState) :=
  match requireDocument s.tree doc with
  | .error e => .error e
  | .ok _ =>
    match findAttr s aid with
    | none => .error .notFoundError
    | some (a, _) =>
      -- adopt step 1・3
      if doc = a.ownerDocument then .ok (aid, s)
      else .ok (aid, modifyAttr s aid (·.withOwnerDocument doc))

/--
"clone a single node" の `Attr` の枝。namespace・prefix・local name・value を写し、
node document は `doc`、element は null の新しい `Attr` を作る。
-/
def cloneAttrIn (s : DOMState) (a : Attr) (doc : NodeId) : AttrId × DOMState :=
  let c : Attr :=
    { id := freshStateAttrId s, «namespace» := a.namespace, «prefix» := a.prefix,
      localName := a.localName, value := a.value, ownerDocument := doc }
  (c.id, { s with detachedAttrs := s.detachedAttrs ++ [c] })

/-- DOM Standard §4.5 `importNode(node, subtree)` に `Attr` を渡したとき。 -/
def importAttr (s : DOMState) (doc : NodeId) (aid : AttrId) : Except DOMException (AttrId × DOMState) :=
  match requireDocument s.tree doc with
  | .error e => .error e
  | .ok _ =>
    match findAttr s aid with
    | none => .error .notFoundError
    | some (a, _) => .ok (cloneAttrIn s a doc)

/-- DOM Standard §4.4 `cloneNode(subtree)` を `Attr` に呼んだとき。copy の node document は元と同じ。 -/
def cloneAttr (s : DOMState) (aid : AttrId) : Except DOMException (AttrId × DOMState) :=
  match findAttr s aid with
  | none => .error .notFoundError
  | some (a, _) => .ok (cloneAttrIn s a a.ownerDocument)

/-! ## value を書く -/

/--
DOM Standard §4.9 "set an existing attribute value"。`Attr.value`・`nodeValue`・`textContent` の
setter がどれもこれを呼ぶ。element が null なら value を書き換えるだけで、そうでなければ
"change an attribute"（mutation record を積む）。Trusted Types の step は対象外である。
-/
def setAttrValue (s : DOMState) (aid : AttrId) (value : String) : Except DOMException DOMState :=
  match findAttr s aid with
  | none => .error .notFoundError
  | some (_, none) => .ok (modifyAttr s aid fun b => { b with value := value })
  | some (a, some n) =>
    match s.tree.get? n with
    | none => .error .notFoundError
    | some d =>
      if d.kind = .element then .ok (changeAttribute s n d a value) else .error .notFoundError

/-! ## 値を返すだけの method -/

/-- refs が指すものが状態にあるか。 -/
def NodeRef.exists (s : DOMState) : NodeRef → Bool
  | .node n => (s.tree.get? n).isSome
  | .attr a => (findAttr s a).isSome

/--
`compareDocumentPosition` の step 5 で、同じ木にないものの前後を一貫して決める全順序。
node どうしは `compareDocumentPosition` と同じく id の順、node は `Attr` より前に置く。
-/
def NodeRef.orderKey : NodeRef → Nat × Nat
  | .node n => (0, n.id)
  | .attr a => (1, a.id)

/-- `orderKey` の辞書式順序で `x` が `y` より前か。 -/
def NodeRef.before (x y : NodeRef) : Bool :=
  x.orderKey.1 < y.orderKey.1 || (x.orderKey.1 == y.orderKey.1 && x.orderKey.2 < y.orderKey.2)

/-- `Attr` を element に置き換える（step 3・4）。node ならそのまま。element が null なら `none`。 -/
def NodeRef.elementOf (s : DOMState) : NodeRef → Option NodeId
  | .node n => some n
  | .attr a => attrOwnerElement s a

/--
DOM Standard §4.4 `compareDocumentPosition(other)`。`this` が `node`、`other` が `other`。

step 4.2 の "equals" は attribute の `equals`（namespace・local name・value）である。
同じ element の attribute list では鍵が一意なので、同じ `Attr` のときだけ当たる。
-/
def compareDocumentPositionRef (s : DOMState) (node other : NodeRef) : Nat :=
  -- step 1
  if node = other then 0
  else
    -- step 2-4。`Attr` は element に置き換える。
    let attr1 : Option Attr := match other with
      | .attr a => (findAttr s a).map (·.1) | .node _ => none
    let attr2 : Option Attr := match node with
      | .attr a => (findAttr s a).map (·.1) | .node _ => none
    match other.elementOf s, node.elementOf s with
    | some n1, some n2 =>
      -- step 4.2：同じ element の attribute どうしは attribute list の順。
      let sameElement : Option Nat :=
        match attr1, attr2 with
        | some a1, some a2 =>
          if n1 = n2 then
            match s.tree.get? n2 with
            | none => none
            | some d =>
              (d.attributes.find? fun b => attrEquals b a1 || attrEquals b a2).map fun b =>
                if attrEquals b a1 then
                  DocumentPosition.implementationSpecific + DocumentPosition.preceding
                else DocumentPosition.implementationSpecific + DocumentPosition.following
          else none
        | _, _ => none
      match sameElement with
      | some r => r
      | none =>
        -- step 5
        if root s.tree n1 != root s.tree n2 then
          DocumentPosition.disconnected + DocumentPosition.implementationSpecific +
            (if other.before node then DocumentPosition.preceding else DocumentPosition.following)
        -- step 6
        else if (isAncestorOf s.tree n1 n2 && attr1.isNone) || (n1 == n2 && attr2.isSome) then
          DocumentPosition.contains + DocumentPosition.preceding
        -- step 7
        else if (isAncestorOf s.tree n2 n1 && attr2.isNone) || (n1 == n2 && attr1.isSome) then
          DocumentPosition.containedBy + DocumentPosition.following
        -- step 8
        else if precedes s.tree n1 n2 then DocumentPosition.preceding
        -- step 9
        else DocumentPosition.following
    -- step 5：element の無い `Attr` が絡む。
    | _, _ =>
      DocumentPosition.disconnected + DocumentPosition.implementationSpecific +
        (if other.before node then DocumentPosition.preceding else DocumentPosition.following)

/--
DOM Standard §4.4 `contains(other)`。`other` が `this` の inclusive descendant か。
`Attr` の inclusive descendant は自分だけで、`Attr` はどの node の descendant でもない。
-/
def nodeContainsRef (s : DOMState) : NodeRef → NodeRef → Bool
  | .node n, .node m => nodeContains s.tree n m
  | .attr a, .attr b => a == b
  | _, _ => false

/-- DOM Standard §4.4 `isEqualNode(otherNode)`。`Attr` どうしは namespace・local name・value。 -/
def nodeRefEquals (s : DOMState) : NodeRef → NodeRef → Bool
  | .node n, .node m => nodeEquals s.tree n m
  | .attr a, .attr b =>
    match findAttr s a, findAttr s b with
    | some (x, _), some (y, _) => attrEquals x y
    | _, _ => false
  | _, _ => false

/--
DOM Standard §4.4 "locate a namespace" の `Attr` の枝。element が null なら null、
そうでなければ element で探す。`lookupPrefix` と `isDefaultNamespace` も同じく element に委ねる。
-/
def attrLookupNamespaceURI (s : DOMState) (aid : AttrId) («prefix» : Option String) : Option String :=
  match attrOwnerElement s aid with
  | none => none
  | some e => lookupNamespaceURI s.tree e «prefix»

def attrLookupPrefix (s : DOMState) (aid : AttrId) («namespace» : Option String) : Option String :=
  match «namespace» with
  | none => none
  | some ns =>
    if ns == "" then none
    else
      match attrOwnerElement s aid with
      | none => none
      | some e => lookupPrefix s.tree e (some ns)

def attrIsDefaultNamespace (s : DOMState) (aid : AttrId) («namespace» : Option String) : Bool :=
  let ns := if «namespace» == some "" then none else «namespace»
  (match attrOwnerElement s aid with
   | none => none
   | some e => locateNamespace s.tree e none) == ns

/-! ## 子を持てない -/

/--
DOM Standard §4.4 `appendChild(node)` の引数か受け手に `Attr` があるとき。

pre-insertion validity の step 1（parent が Document・DocumentFragment・Element でない）か
step 4（node が DocumentFragment・DocumentType・Element・CharacterData でない）で
`HierarchyRequestError` になる。step 2-3 は `Attr` が木に入らないので当たらない。
どちらも node なら通常の `appendChild` である。
-/
def appendChildRef (s : DOMState) (parent node : NodeRef) : Except DOMException DOMState :=
  match parent, node with
  | .node p, .node n => appendChild s p n
  | .attr a, _ =>
    if (findAttr s a).isNone then .error .notFoundError else .error .hierarchyRequestError
  | .node p, .attr a =>
    match s.tree.get? p with
    | none => .error .notFoundError
    | some pd =>
      if (findAttr s a).isNone then .error .notFoundError
      -- step 1
      else if !(pd.kind == .document || pd.kind == .documentFragment || pd.kind == .element) then
        .error .hierarchyRequestError
      -- step 4
      else .error .hierarchyRequestError

end Dom
