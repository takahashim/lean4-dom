import Dom.Attribute.Algorithms
import Dom.Mutation.Create

/-!
# `Attr` を node として渡す API（§4.9）

`createAttribute` / `getAttributeNode` / `setAttributeNode` / `removeAttributeNode` と、
`NamedNodeMap` の `removeNamedItem`。

model の attribute は element の状態のままだが、**同一性は `AttrId` で持つ**ので、
「どの `Attr` を渡したか」「返ってきたのは同じ `Attr` か」は表せる。
`Attr` を指す引数は id で渡す。

* **どの element にも付いていない `Attr`** は `DOMState.detachedAttrs` にいる。
  `createAttribute` が作ったもの、`removeAttributeNode` が返したもの、
  `setAttributeNode` が押し出したものである。
* 名前で消した attribute（`removeAttribute`）は入らない。仕様では element を null に
  するだけで object は残るが、それを指す参照がどこにも無いので観測できない。

`setAttributeNodeNS` は仕様上 `setAttributeNode` と step が同一なので、別に置かない。
attribute の node document は model に無いので、"replace an attribute" の step 4 と
"append an attribute" の step 3 は空になる。
-/

namespace Dom

open Dom.ListUtil

/-! ## `Attr` を id で引く -/

/-- `aid` を持つ attribute がある element。無ければ `none`（detach されている）。 -/
def ownerElementOf (t : Tree) (aid : AttrId) : Option NodeId :=
  t.nodes.keys.find? fun n =>
    match t.get? n with
    | none => false
    | some d => d.attributes.any fun a => a.id == aid

/-- `aid` を持つ attribute と、その owner element（detach されていれば `none`）。 -/
def findAttr (s : DOMState) (aid : AttrId) : Option (Attr × Option NodeId) :=
  match ownerElementOf s.tree aid with
  | some n =>
    match s.tree.get? n with
    | none => none
    | some d => (d.attributes.find? fun a => a.id == aid).map fun a => (a, some n)
  | none => (s.detachedAttrs.find? fun a => a.id == aid).map fun a => (a, none)

/-- detach された list から取り除く。 -/
def removeDetached (s : DOMState) (aid : AttrId) : DOMState :=
  { s with detachedAttrs := eraseFirst (fun a => a.id == aid) s.detachedAttrs }

@[simp] theorem removeDetached_tree (s : DOMState) (aid : AttrId) :
    (removeDetached s aid).tree = s.tree := rfl

@[simp] theorem removeDetached_ranges (s : DOMState) (aid : AttrId) :
    (removeDetached s aid).ranges = s.ranges := rfl

@[simp] theorem removeDetached_iterators (s : DOMState) (aid : AttrId) :
    (removeDetached s aid).iterators = s.iterators := rfl

@[simp] theorem removeDetached_registrations (s : DOMState) (aid : AttrId) :
    (removeDetached s aid).registrations = s.registrations := rfl

@[simp] theorem removeDetached_observers (s : DOMState) (aid : AttrId) :
    (removeDetached s aid).observers = s.observers := rfl

/-! ## `Attr` を作る -/

/--
DOM Standard §4.9 "create an attribute"。

element を持たない新しい `Attr` を作る。node document は model に無い。
-/
def createAttributeIn (s : DOMState) («namespace» «prefix» : Option String) (localName : String) :
    AttrId × DOMState :=
  let a : Attr := Attr.normalized
    { id := freshStateAttrId s, «namespace» := «namespace», «prefix» := «prefix»,
      localName := localName }
  (a.id, { s with detachedAttrs := s.detachedAttrs ++ [a] })

/-- DOM Standard §4.5 `Document.createAttribute(localName)`。 -/
def createAttribute (s : DOMState) (doc : NodeId) (localName : String) :
    Except DOMException (AttrId × DOMState) :=
  match requireDocument s.tree doc with
  | .error e => .error e
  | .ok dd =>
    -- step 1
    if !isValidAttributeLocalName localName then .error .invalidCharacterError
    else
      -- step 2
      .ok (createAttributeIn s none none
        (if dd.isHTMLDocument then asciiLowercase localName else localName))

/-- DOM Standard §4.5 `Document.createAttributeNS(namespace, qualifiedName)`。 -/
def createAttributeNS (s : DOMState) (doc : NodeId) («namespace» : Option String)
    (qualifiedName : String) : Except DOMException (AttrId × DOMState) :=
  match requireDocument s.tree doc with
  | .error e => .error e
  | .ok _ =>
    match validateAndExtractAttribute «namespace» qualifiedName with
    | .error e => .error e
    | .ok (ns, pfx, ln) => .ok (createAttributeIn s ns pfx ln)

/-! ## `Element` の method -/

/-- 受け手が Element であることを確かめる。 -/
def requireElement (t : Tree) (element : NodeId) : Except DOMException NodeData :=
  match t.get? element with
  | none => .error .notFoundError
  | some d => if d.kind != .element then .error .typeError else .ok d

/-- DOM Standard §4.9 `Element.getAttributeNode(qualifiedName)`。 -/
def getAttributeNode (t : Tree) (element : NodeId) (qualifiedName : String) :
    Except DOMException (Option AttrId) :=
  match requireElement t element with
  | .error e => .error e
  | .ok d => .ok ((getAttributeByName t d qualifiedName).map (·.id))

/-- DOM Standard §4.9 `Element.getAttributeNodeNS(namespace, localName)`。 -/
def getAttributeNodeNS (t : Tree) (element : NodeId) («namespace» : Option String)
    (localName : String) : Except DOMException (Option AttrId) :=
  match requireElement t element with
  | .error e => .error e
  | .ok d => .ok ((getAttributeByKey d «namespace» localName).map (·.id))

/--
DOM Standard §4.9 "replace an attribute"。

押し出された側は element を失うので detach された attribute になる。
呼び出し側（`setAttributeNode`）がそれを返す。
-/
def replaceAttributeWith (s : DOMState) (element : NodeId) (d : NodeData) (old new : Attr) :
    DOMState :=
  let t := setAttributes s.tree element d
    (updateFirst (fun b => b.key == old.key) (fun _ => new) d.attributes)
  handleAttributeChanges { s with tree := t, detachedAttrs := s.detachedAttrs ++ [old] }
    element old (some old.value)

/--
DOM Standard §4.9 "set an attribute" と `Element.setAttributeNode(attr)`。

step 1 の Trusted Types は対象外なので、step 6 の value の書き換えは何もしない。
`setAttributeNodeNS` も同じ step を走るので、この一つで両方を表す。
-/
def setAttributeNode (s : DOMState) (element : NodeId) (aid : AttrId) :
    Except DOMException (Option AttrId × DOMState) :=
  match requireElement s.tree element with
  | .error e => .error e
  | .ok d =>
    match findAttr s aid with
    -- `Attr` でない引数。WebIDL の変換で TypeError になる。
    | none => .error .typeError
    | some (a₀, owner) =>
      -- step 2
      if owner != none && owner != some element then .error .inUseAttributeError
      else
        -- step 3。model が持てる形に整えてから引く（`Attr.normalized` は挙動を変えない）。
        match getAttributeByKey d a₀.normalized.namespace a₀.normalized.localName with
        | some old =>
          -- step 4
          if old.id == aid then .ok (some aid, s)
          -- step 7
          else .ok (some old.id,
            replaceAttributeWith (removeDetached s aid) element d old a₀.normalized)
        -- step 8
        | none => .ok (none, appendAttribute (removeDetached s aid) element d a₀.normalized)

/--
DOM Standard §4.9 "remove an attribute"。

`removeAttributeFrom`（名前で消す側）と違い、外した attribute は呼び出し側に返るので
detach された側に残す。
-/
def detachAttribute (s : DOMState) (element : NodeId) (d : NodeData) (a : Attr) : DOMState :=
  let t := setAttributes s.tree element d (eraseFirst (fun b => b.id == a.id) d.attributes)
  handleAttributeChanges { s with tree := t, detachedAttrs := s.detachedAttrs ++ [a] }
    element a (some a.value)

/--
DOM Standard §4.9 `Element.removeAttributeNode(attr)`。

step 1 は attribute list に無ければ `NotFoundError`。
-/
def removeAttributeNode (s : DOMState) (element : NodeId) (aid : AttrId) :
    Except DOMException (AttrId × DOMState) :=
  match requireElement s.tree element with
  | .error e => .error e
  | .ok d =>
    match d.attributes.find? fun a => a.id == aid with
    | none => .error .notFoundError
    | some a => .ok (aid, detachAttribute s element d a)

/--
DOM Standard §4.9 `NamedNodeMap.removeNamedItem(qualifiedName)`。

`removeAttribute` と違い、無ければ `NotFoundError` を投げ、外した `Attr` を返す。
-/
def removeNamedItem (s : DOMState) (element : NodeId) (qualifiedName : String) :
    Except DOMException (AttrId × DOMState) :=
  match requireElement s.tree element with
  | .error e => .error e
  | .ok d =>
    match getAttributeByName s.tree d qualifiedName with
    | none => .error .notFoundError
    | some a => removeAttributeNode s element a.id

end Dom
