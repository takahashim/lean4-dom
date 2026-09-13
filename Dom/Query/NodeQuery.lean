import Dom.Basic.Order
import Dom.Attribute.Name

/-!
# 値を返すだけの `Node` の method（§4.4）

木も live object も変えないので、どれも `Tree` の上の純関数である。
差分テストでは「操作の戻り値」としてだけ観測される。

## model が持たない持ち物

`equals` は DocumentType の name / public ID / system ID と
ProcessingInstruction の target を見るが、model の `NodeData` はどちらも持たない
（roadmap §13.1）。harness はどちらも固定値（`"html"` と `"pi"`）で作るので、
その二つの比較は常に真になり、判定は変わらない。
-/

namespace Dom

/-! ## `compareDocumentPosition` -/

namespace DocumentPosition

/-- DOM Standard §4.4 の mask。 -/
def disconnected : Nat := 1
def preceding : Nat := 2
def following : Nat := 4
def contains : Nat := 8
def containedBy : Nat := 16
def implementationSpecific : Nat := 32

end DocumentPosition

/--
DOM Standard §4.4 `compareDocumentPosition(other)`。

仕様の `node1` が `other`、`node2` が `this`（ここでは `node`）である。
返す mask は **`other` が `node` から見てどこにいるか** を表す。

step 6 の「同じ木にない」場合は PRECEDING と FOLLOWING のどちらでもよいが、
仕様は **一貫していること** を求める（"with the constraint that this is to be consistent"）。
model は node id の順という全順序で決める。
`compareDocumentPosition_disconnected_consistent` がその一貫性である。

attribute は node ではないので step 3-5 は model の対象外である（roadmap §13.3）。
-/
def compareDocumentPosition (t : Tree) (node other : NodeId) : Nat :=
  if node == other then 0
  -- step 6
  else if root t other != root t node then
    DocumentPosition.disconnected + DocumentPosition.implementationSpecific +
      (if other.id < node.id then DocumentPosition.preceding else DocumentPosition.following)
  -- step 7
  else if isAncestorOf t other node then
    DocumentPosition.contains + DocumentPosition.preceding
  -- step 8
  else if isAncestorOf t node other then
    DocumentPosition.containedBy + DocumentPosition.following
  -- step 9
  else if precedes t other node then DocumentPosition.preceding
  -- step 10
  else DocumentPosition.following

/-- 同じ木にないときは、node id の順で PRECEDING か FOLLOWING を決める。 -/
theorem compareDocumentPosition_disconnected {t : Tree} {a b : NodeId} (hne : a ≠ b)
    (hr : root t b ≠ root t a) :
    compareDocumentPosition t a b = if b.id < a.id then 35 else 37 := by
  unfold compareDocumentPosition
  rw [if_neg (by simp [hne]), if_pos (by simp [hr])]
  split <;> rfl

/--
**同じ木にない二つの node については、逆に呼べば逆の答えになる。**

仕様 step 6 の "consistent" がこれである。どちらを PRECEDING にするかは実装に任されるが、
一方から見て「先行する」なら、他方から見ては「後続する」でなければならない。
-/
theorem compareDocumentPosition_disconnected_consistent {t : Tree} {a b : NodeId}
    (hne : a ≠ b) (hr : root t a ≠ root t b) :
    (compareDocumentPosition t a b = 37 ∧ compareDocumentPosition t b a = 35) ∨
    (compareDocumentPosition t a b = 35 ∧ compareDocumentPosition t b a = 37) := by
  have hid : a.id ≠ b.id := fun h => hne (by cases a; cases b; simp_all)
  rw [compareDocumentPosition_disconnected hne (Ne.symm hr),
    compareDocumentPosition_disconnected (Ne.symm hne) hr]
  rcases Nat.lt_or_ge a.id b.id with h | h
  · exact Or.inl ⟨by rw [if_neg (by omega)], by rw [if_pos (by omega)]⟩
  · have h' : b.id < a.id := by omega
    exact Or.inr ⟨by rw [if_pos (by omega)], by rw [if_neg (by omega)]⟩

/-- DOM Standard §4.4 `contains(other)`。 -/
def nodeContains (t : Tree) (node other : NodeId) : Bool :=
  isInclusiveAncestorOf t node other

/--
DOM Standard §4.4 `getRootNode(options)`。

`composed` は shadow tree の話なので model の対象外（roadmap §13.4）。
-/
def getRootNode (t : Tree) (n : NodeId) : NodeId := root t n

/-! ## `isEqualNode` -/

/-- DOM Standard §4.4 の attribute の `equals`。**prefix は見ない。** -/
def attrEquals (x y : Attr) : Bool :=
  x.namespace == y.namespace && x.localName == y.localName && x.value == y.value

/--
DOM Standard §4.4 `equals` のうち、node 自身の持ち物の比較（children は別）。

kind ごとの switch をそのまま写してある。
-/
def nodeOwnPropertiesEqual (a b : NodeData) : Bool :=
  match a.kind with
  | .element =>
    a.namespace == b.namespace && a.prefix == b.prefix && a.localName == b.localName &&
      a.attributes.length == b.attributes.length &&
      a.attributes.all fun x => b.attributes.any fun y => attrEquals x y
  | .text | .cdataSection | .comment | .processingInstruction => a.data == b.data
  -- DocumentType の name / public ID / system ID は model の対象外（上の注）。
  | .documentType => true
  | .document | .documentFragment => true

/-- `equals` の本体。fuel は木の高さの上界。 -/
def nodeEqualsFuel (t : Tree) : Nat → NodeId → NodeId → Bool
  | 0, _, _ => false
  | f + 1, a, b =>
    match t.get? a, t.get? b with
    | some da, some db =>
      da.kind == db.kind && nodeOwnPropertiesEqual da db &&
        da.children.length == db.children.length &&
        (da.children.zip db.children).all fun p => nodeEqualsFuel t f p.1 p.2
    | _, _ => false

/--
DOM Standard §4.4 `isEqualNode(otherNode)`。

木にある node は深さが `t.size` 未満なので、`preorder` と同じ fuel で足りる。
-/
def nodeEquals (t : Tree) (a b : NodeId) : Bool :=
  nodeEqualsFuel t t.size a b

/-! ## `textContent` / `nodeValue` -/

/-- DOM Standard §4.4 の descendant text content。 -/
def descendantTextContent (t : Tree) (n : NodeId) : String :=
  (((preorder t n).drop 1).filterMap fun x =>
    match t.get? x with
    | none => none
    | some d => if d.kind.isText then some d.data else none).foldl (· ++ ·) ""

/-- DOM Standard §4.4 "get text content"。Document と DocumentType では null。 -/
def getTextContent (t : Tree) (n : NodeId) : Option String :=
  match t.get? n with
  | none => none
  | some d =>
    match d.kind with
    | .documentFragment | .element => some (descendantTextContent t n)
    | .text | .cdataSection | .comment | .processingInstruction => some d.data
    | .document | .documentType => none

/--
DOM Standard §4.4 `nodeValue` の getter。

CharacterData なら data、それ以外は null（Attr は model の対象外）。
-/
def getNodeValue (t : Tree) (n : NodeId) : Option String :=
  match t.get? n with
  | none => none
  | some d => if d.kind.isCharacterData then some d.data else none

/-! ## 名前空間の探索（§4.4） -/

/-- `n` の parent element。parent が element でなければ null。 -/
def parentElement (t : Tree) (n : NodeId) : Option NodeId :=
  match parentOf t n with
  | none => none
  | some p => if kindOf t p == some NodeKind.element then some p else none

/-- Document の document element（最初の element の子）。 -/
def documentElement (t : Tree) (n : NodeId) : Option NodeId :=
  (childrenOf t n).find? fun c => kindOf t c == some NodeKind.element

/--
`e` から parent element をたどれるだけたどった列。

仕様の "locate a namespace" / "locate a namespace prefix" は
parent element へ再帰するので、element でない親に当たったところで止まる。
-/
def elementChain (t : Tree) (e : NodeId) : List NodeId :=
  (e :: ancestors t e).takeWhile fun x => kindOf t x == some NodeKind.element

/-- DOM Standard §4.4 "locate a namespace" の Element の枝。 -/
def locateNamespaceIn (t : Tree) («prefix» : Option String) : List NodeId → Option String
  | [] => none
  | e :: rest =>
    -- step 1-2
    if «prefix» == some "xml" then some xmlNamespace
    else if «prefix» == some "xmlns" then some xmlnsNamespace
    else
      match t.get? e with
      | none => none
      | some d =>
        -- step 3
        if d.namespace.isSome && d.prefix == «prefix» then d.namespace
        else
          -- step 4。見つかれば値が空でも **そこで止まる**（空なら null）。
          match d.attributes.find? fun a =>
              (a.namespace == some xmlnsNamespace && a.prefix == some "xmlns" &&
                some a.localName == «prefix») ||
              («prefix».isNone && a.namespace == some xmlnsNamespace && a.prefix.isNone &&
                a.localName == "xmlns") with
          | some a => if a.value == "" then none else some a.value
          -- step 5-6
          | none => locateNamespaceIn t «prefix» rest

/-- DOM Standard §4.4 "locate a namespace"。 -/
def locateNamespace (t : Tree) (n : NodeId) («prefix» : Option String) : Option String :=
  match t.get? n with
  | none => none
  | some d =>
    match d.kind with
    | .element => locateNamespaceIn t «prefix» (elementChain t n)
    | .document =>
      match documentElement t n with
      | none => none
      | some e => locateNamespaceIn t «prefix» (elementChain t e)
    | .documentType | .documentFragment => none
    | _ =>
      match parentElement t n with
      | none => none
      | some e => locateNamespaceIn t «prefix» (elementChain t e)

/-- DOM Standard §4.4 "locate a namespace prefix"。 -/
def locateNamespacePrefixIn (t : Tree) («namespace» : String) : List NodeId → Option String
  | [] => none
  | e :: rest =>
    match t.get? e with
    | none => none
    | some d =>
      -- step 1
      if d.namespace == some «namespace» && d.prefix.isSome then d.prefix
      else
        -- step 2。`xmlns:` の prefix を持つ attribute だけを見る（namespace は見ない）。
        match d.attributes.find? fun a => a.prefix == some "xmlns" && a.value == «namespace» with
        | some a => some a.localName
        -- step 3-4
        | none => locateNamespacePrefixIn t «namespace» rest

/-- DOM Standard §4.4 `lookupNamespaceURI(prefix)`。空文字列は null と同じ。 -/
def lookupNamespaceURI (t : Tree) (n : NodeId) («prefix» : Option String) : Option String :=
  locateNamespace t n (if «prefix» == some "" then none else «prefix»)

/-- DOM Standard §4.4 `lookupPrefix(namespace)`。 -/
def lookupPrefix (t : Tree) (n : NodeId) («namespace» : Option String) : Option String :=
  match «namespace» with
  | none => none
  | some ns =>
    if ns == "" then none
    else
      match t.get? n with
      | none => none
      | some d =>
        match d.kind with
        | .element => locateNamespacePrefixIn t ns (elementChain t n)
        | .document =>
          match documentElement t n with
          | none => none
          | some e => locateNamespacePrefixIn t ns (elementChain t e)
        | .documentType | .documentFragment => none
        | _ =>
          match parentElement t n with
          | none => none
          | some e => locateNamespacePrefixIn t ns (elementChain t e)

/-- DOM Standard §4.4 `isDefaultNamespace(namespace)`。 -/
def isDefaultNamespace (t : Tree) (n : NodeId) («namespace» : Option String) : Bool :=
  let ns := if «namespace» == some "" then none else «namespace»
  locateNamespace t n none == ns

end Dom
