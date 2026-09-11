import Dom.Attribute.Name
import Dom.Observer.Record
import Dom.Util.List

/-!
# Attribute

DOM Standard §4.9 の attribute の algorithm と、`Element` の attribute 関連 method。
element の namespace と local name に依る部分（`tagName`、attribute 名の ASCII lowercase）も
ここに置く。

仕様の attribute は `Attr` node だが、本 model では element の状態として持つ
（`Dom/Basic/NodeId.lean` の `Attr` を参照）。したがって

* `Attr` node を直接渡す API（`setAttributeNode`, `attributes` の `NamedNodeMap`）
* それに伴う "set an attribute" と "replace an attribute"、`InUseAttributeError`

は扱わない。attribute の node document も持たないので、adopt の step 3.2 は空になる。

receiver が Element でない場合は WebIDL の TypeError を返す。仕様の algorithm 自体には
その検査が無い（`Element` interface の method からしか呼ばれないため）が、
model は node を kind で区別するので、IDL 由来の検査として置く。
-/

namespace Dom

open Dom.ListUtil

/-! ## attribute list の探索 -/

/--
DOM Standard §4.9 "get an attribute by namespace and local name"。

step 1 の「空文字列なら null」を含む。
-/
def getAttributeByKey (d : NodeData) («namespace» : Option String) (localName : String) :
    Option Attr :=
  let ns := normalizeNamespace «namespace»
  d.attributes.find? fun a => a.namespace == ns && a.localName == localName

/-- `d` の node document が HTML document か。 -/
def isHTMLDocumentOf (t : Tree) (d : NodeData) : Bool :=
  match t.get? d.ownerDocument with
  | none => false
  | some doc => doc.isHTMLDocument

/--
DOM Standard §4.8 `Element.tagName`。

qualified name を、HTML namespace の element が HTML document にあるときは ASCII uppercase する。
-/
def tagName (t : Tree) (element : NodeId) : Option String :=
  match t.get? element with
  | none => none
  | some d =>
    if d.kind != .element then none
    else if d.namespace == some htmlNamespace && isHTMLDocumentOf t d then
      some (asciiUppercase d.qualifiedName)
    else some d.qualifiedName

/--
DOM Standard §4.9 "get an attribute by name" step 1、および `setAttribute` step 2 と
`toggleAttribute` step 2。

HTML namespace の element が HTML document にあるなら qualified name を ASCII lowercase する。
その三箇所は同じ条件と同じ変換なので、ここにまとめる。
-/
def attrNameFor (t : Tree) (d : NodeData) (qualifiedName : String) : String :=
  if d.namespace == some htmlNamespace && isHTMLDocumentOf t d then
    asciiLowercase qualifiedName
  else qualifiedName

/--
DOM Standard §4.9 "get an attribute by name"。

step 1 で名前を正規化し、qualified name が一致する最初の attribute を返す。
-/
def getAttributeByName (t : Tree) (d : NodeData) (qualifiedName : String) : Option Attr :=
  let qn := attrNameFor t d qualifiedName
  d.attributes.find? fun a => a.qualifiedName == qn

/-- DOM Standard §4.9 "get an attribute value"。無ければ空文字列。 -/
def getAttributeValue (d : NodeData) («namespace» : Option String) (localName : String) : String :=
  match getAttributeByKey d «namespace» localName with
  | none => ""
  | some a => a.value

/-! ## attribute list を変える primitive -/

/--
element の attribute list だけを差し替える。木の他の成分は変えない。

`d` は差し替える前の node data で、`t.get? n = some d` を満たすことを呼び出し側が保証する
（`withData` と同じ形にしてある）。
-/
def setAttributes (t : Tree) (n : NodeId) (d : NodeData) (as : List Attr) : Tree :=
  { t with nodes := t.nodes.insert n { d with attributes := as } }

theorem get?_setAttributes {t : Tree} {n : NodeId} {d : NodeData} (_hd : t.get? n = some d)
    (as : List Attr) (m : NodeId) :
    (setAttributes t n d as).get? m =
      if m = n then some { d with attributes := as } else t.get? m := by
  show (t.nodes.insert n { d with attributes := as }).get? m = _
  rw [NodeStore.get?_insert]
  by_cases h : m = n
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun he => h he.symm)]
    rfl

theorem parentOf_setAttributes {t : Tree} {n : NodeId} {d : NodeData} (hd : t.get? n = some d)
    (as : List Attr) (m : NodeId) : parentOf (setAttributes t n d as) m = parentOf t m := by
  unfold parentOf
  rw [get?_setAttributes hd]
  by_cases h : m = n
  · subst h; simp [hd]
  · rw [if_neg h]

theorem childrenOf_setAttributes {t : Tree} {n : NodeId} {d : NodeData} (hd : t.get? n = some d)
    (as : List Attr) (m : NodeId) : childrenOf (setAttributes t n d as) m = childrenOf t m := by
  unfold childrenOf
  rw [get?_setAttributes hd]
  by_cases h : m = n
  · subst h; simp [hd]
  · rw [if_neg h]

theorem kindOf_setAttributes {t : Tree} {n : NodeId} {d : NodeData} (hd : t.get? n = some d)
    (as : List Attr) (m : NodeId) : kindOf (setAttributes t n d as) m = kindOf t m := by
  unfold kindOf
  rw [get?_setAttributes hd]
  by_cases h : m = n
  · subst h; simp [hd]
  · rw [if_neg h]

/--
attribute list を差し替えても、attribute 名の正規化は変わらない。

`attrNameFor` が見るのは element の namespace と node document の type だけで、
`setAttributes` はそのどちらも変えない。
-/
theorem attrNameFor_setAttributes {t : Tree} {n : NodeId} {d : NodeData} (hd : t.get? n = some d)
    (as : List Attr) (qn : String) :
    attrNameFor (setAttributes t n d as) { d with attributes := as } qn = attrNameFor t d qn := by
  unfold attrNameFor isHTMLDocumentOf
  rw [get?_setAttributes hd]
  by_cases hm : d.ownerDocument = n
  · rw [if_pos hm, hm, hd]
  · rw [if_neg hm]

/-!
## "handle attribute changes"

DOM Standard §4.9。custom element の callback reaction（step 2）と
attribute change steps（step 3）は hook の位置だけを保ち、model では空である。
-/

/--
DOM Standard §4.9 "handle attribute changes" step 1。

record の `oldValue` は "queue a mutation record" 側で
`attributeOldValue` を見て決めるので、ここでは候補として渡すだけである。
-/
def handleAttributeChanges (s : DOMState) (element : NodeId) (a : Attr)
    (oldValue : Option String) : DOMState :=
  queueMutationRecord s
    { type := .attributes, target := element,
      attributeName := some a.localName, attributeNamespace := a.namespace }
    oldValue

/--
DOM Standard §4.9 "change an attribute"。

仕様 step 1-2 は attribute node の value を書き換える。model の attribute は
element の状態なので、attribute list の中の該当要素を差し替える形になる。
`a` は変更前の attribute、`value` は新しい value である。
-/
def changeAttribute (s : DOMState) (element : NodeId) (d : NodeData) (a : Attr) (value : String) :
    DOMState :=
  let t := setAttributes s.tree element d
    (updateFirst (fun b => b.key == a.key) (fun b => { b with value := value }) d.attributes)
  handleAttributeChanges { s with tree := t } element a (some a.value)

/--
DOM Standard §4.9 "append an attribute"。

step 2-3（attribute の element と node document）は model が attribute を
element の状態として持つので自動的に満たされる。
-/
def appendAttribute (s : DOMState) (element : NodeId) (d : NodeData) (a : Attr) : DOMState :=
  let t := setAttributes s.tree element d (d.attributes ++ [a])
  handleAttributeChanges { s with tree := t } element a none

/--
DOM Standard §4.9 "remove an attribute"。

`a` は取り除く attribute。oldValue は仕様どおり attribute の value である。
-/
def removeAttributeFrom (s : DOMState) (element : NodeId) (d : NodeData) (a : Attr) : DOMState :=
  let t := setAttributes s.tree element d (eraseFirst (fun b => b.key == a.key) d.attributes)
  handleAttributeChanges { s with tree := t } element a (some a.value)

/--
DOM Standard §4.9 "set an attribute value"。

step 2 は attribute が無ければ作って append、step 3 はあれば change である。

namespace は入口で正規化する（空文字列を null にする）。仕様の本文は step 1 の正規化を
"get an attribute by namespace and local name" の中に置いていて、
新しく作る attribute には正規化前の namespace を渡すが、
呼び出し側（`setAttributeNS`）は "validate and extract" 済みの namespace しか渡さないので、
両者は一致する。
-/
def setAttributeValue (s : DOMState) (element : NodeId) (localName value : String)
    («prefix» : Option String := none) («namespace» : Option String := none) :
    Except DOMException DOMState :=
  match s.tree.get? element with
  | none => .error .notFoundError
  | some d =>
    if d.kind != .element then .error .typeError
    else
      match getAttributeByKey d «namespace» localName with
      | none =>
        .ok (appendAttribute s element d
          { «namespace» := normalizeNamespace «namespace», «prefix» := «prefix»,
            localName := localName, value := value })
      | some a => .ok (changeAttribute s element d a value)

/-! ## `Element` の method -/

/--
DOM Standard §4.9 `Element.setAttribute(qualifiedName, value)`。

model の element は HTML namespace に無いので step 2 の lowercase は走らない。
step 4 は qualified name で探す（namespace と local name ではない）ことに注意する。
-/
def setAttribute (s : DOMState) (element : NodeId) (qualifiedName value : String) :
    Except DOMException DOMState :=
  -- step 1
  if !isValidAttributeLocalName qualifiedName then .error .invalidCharacterError
  else
    match s.tree.get? element with
    | none => .error .notFoundError
    | some d =>
      if d.kind != .element then .error .typeError
      else
        match getAttributeByName s.tree d qualifiedName with
        -- step 5
        | some a => .ok (changeAttribute s element d a value)
        -- step 6-7
        | none =>
          .ok (appendAttribute s element d
            { localName := attrNameFor s.tree d qualifiedName, value := value })

/-- DOM Standard §4.9 `Element.setAttributeNS(namespace, qualifiedName, value)`。 -/
def setAttributeNS (s : DOMState) (element : NodeId) («namespace» : Option String)
    (qualifiedName value : String) : Except DOMException DOMState :=
  match validateAndExtractAttribute «namespace» qualifiedName with
  | .error e => .error e
  | .ok (ns, pfx, localName) => setAttributeValue s element localName value pfx ns

/--
DOM Standard §4.9 "remove an attribute by name" と `Element.removeAttribute(qualifiedName)`。

attribute が無ければ何もしない。
-/
def removeAttribute (s : DOMState) (element : NodeId) (qualifiedName : String) :
    Except DOMException DOMState :=
  match s.tree.get? element with
  | none => .error .notFoundError
  | some d =>
    if d.kind != .element then .error .typeError
    else
      match getAttributeByName s.tree d qualifiedName with
      | none => .ok s
      | some a => .ok (removeAttributeFrom s element d a)

/-- DOM Standard §4.9 "remove an attribute by namespace and local name" と `removeAttributeNS`。 -/
def removeAttributeNS (s : DOMState) (element : NodeId) («namespace» : Option String)
    (localName : String) : Except DOMException DOMState :=
  match s.tree.get? element with
  | none => .error .notFoundError
  | some d =>
    if d.kind != .element then .error .typeError
    else
      match getAttributeByKey d «namespace» localName with
      | none => .ok s
      | some a => .ok (removeAttributeFrom s element d a)

/--
DOM Standard §4.9 `Element.toggleAttribute(qualifiedName, force)`。

返り値の `Bool` は attribute が結果として付いているかである。
-/
def toggleAttribute (s : DOMState) (element : NodeId) (qualifiedName : String)
    (force : Option Bool) : Except DOMException (DOMState × Bool) :=
  -- step 1
  if !isValidAttributeLocalName qualifiedName then .error .invalidCharacterError
  else
    match s.tree.get? element with
    | none => .error .notFoundError
    | some d =>
      if d.kind != .element then .error .typeError
      else
        match getAttributeByName s.tree d qualifiedName with
        -- step 4
        | none =>
          if force == some false then .ok (s, false)
          else
            .ok (appendAttribute s element d
              { localName := attrNameFor s.tree d qualifiedName }, true)
        -- step 5-6
        | some a =>
          if force == some true then .ok (s, true)
          else .ok (removeAttributeFrom s element d a, false)

/-! ## 木を変えない検査 -/

/-- DOM Standard §4.9 `Element.getAttribute(qualifiedName)`。 -/
def getAttribute (t : Tree) (element : NodeId) (qualifiedName : String) : Option String :=
  match t.get? element with
  | none => none
  | some d => (getAttributeByName t d qualifiedName).map (·.value)

/-- DOM Standard §4.9 `Element.hasAttribute(qualifiedName)`。 -/
def hasAttribute (t : Tree) (element : NodeId) (qualifiedName : String) : Bool :=
  (getAttribute t element qualifiedName).isSome

/-- DOM Standard §4.9 `Element.getAttributeNames()`。attribute list の順である。 -/
def getAttributeNames (t : Tree) (element : NodeId) : List String :=
  match t.get? element with
  | none => []
  | some d => d.attributes.map Attr.qualifiedName

end Dom
