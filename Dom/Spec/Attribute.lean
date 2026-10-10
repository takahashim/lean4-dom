import Dom.Spec.Record
import Dom.Attribute.Name

/-!
# attribute の変更と record の関係意味論（§4.9・§4.3.4）

`replace` などと同じ方針。仕様本文から独立に書き写した関係を置き、
実行関数（`Dom/Attribute/Algorithms.lean`）がそれを満たすことは
`Dom/Spec/AttributeSound.lean` で証明する。

## model の範囲

* attribute は element の状態（attribute list）として持つ。同一性は `AttrId` で表す
  （`Dom/Basic/NodeId.lean`）。
* 新しく作る attribute の id は `freshStateAttrId`（状態にある attribute id の最大より一つ大きいもの）
  とする。どの id を割り当てるかは仕様が決めない model の約束なので、関係もこれを語彙として使う。
* "handle attribute changes" の step 2（custom element の callback reaction）と step 3
  （attribute change steps）は model では空である。step 1 の record だけを書く。
* receiver が木に無いか Element でなければ `NotFoundError`（model の都合）。
  Element でない receiver に対する WebIDL の TypeError は、method を呼ぶ層（`Dom/Exec/Invoke.lean`）が
  algorithm より先に返すので、この関係には現れない。
-/

namespace Dom.Spec

open Dom

/-! ## §4.3.4 attributes の record -/

/--
"queue a mutation record" の step 2.3 のうち、attributes record に効く部分。

options の attributes が true で、`attributeFilter` が無いか、あって name を含み namespace が null。
-/
def InterestedInAttribute (s : DOMState) (mo : Nat) (target : NodeId) (name : String)
    (ns : Option String) : Prop :=
  ∃ r ∈ s.registrations, r.observer = mo ∧ r.attributes = true ∧
    InclusiveAncestor s.tree r.node target ∧ (r.node = target ∨ r.subtree = true) ∧
    (r.attributeFilter = none ∨ ∃ f, r.attributeFilter = some f ∧ name ∈ f ∧ ns = none)

/-- step 2.3.3。`attributeOldValue` を持つ interested な registration があること。 -/
def AttributeOldValueWanted (s : DOMState) (mo : Nat) (target : NodeId) (name : String)
    (ns : Option String) : Prop :=
  ∃ r ∈ s.registrations, r.observer = mo ∧ r.attributes = true ∧ r.attributeOldValue = true ∧
    InclusiveAncestor s.tree r.node target ∧ (r.node = target ∨ r.subtree = true) ∧
    (r.attributeFilter = none ∨ ∃ f, r.attributeFilter = some f ∧ name ∈ f ∧ ns = none)

/-- attributes の record。 -/
def attrRecord (target : NodeId) (name : String) (ns oldValue : Option String) : MutationRecord :=
  { type := .attributes, target := target, attributeName := some name,
    attributeNamespace := ns, oldValue := oldValue }

/--
**attributes の record を一つ積む。**

interested な observer の queue の末尾に一つ積み、oldValue は `attributeOldValue` を持つ
observer にだけ載せる。observer は pending mutation observers に入り、microtask が予約される。
-/
def AttributeRecordQueued (s s' : DOMState) (target : NodeId) (name : String)
    (ns : Option String) (oldValue : Option String) : Prop :=
  s'.observers.length = s.observers.length ∧
  (∀ (mo : Nat) (o o' : ObserverState), s.observers[mo]? = some o →
    s'.observers[mo]? = some o' →
    (InterestedInAttribute s mo target name ns → AttributeOldValueWanted s mo target name ns →
      o'.records = o.records ++ [attrRecord target name ns oldValue]) ∧
    (InterestedInAttribute s mo target name ns → ¬ AttributeOldValueWanted s mo target name ns →
      o'.records = o.records ++ [attrRecord target name ns none]) ∧
    (¬ InterestedInAttribute s mo target name ns → o'.records = o.records)) ∧
  (∀ mo, InterestedInAttribute s mo target name ns → mo ∈ s'.pendingObservers) ∧
  (∀ mo ∈ s.pendingObservers, mo ∈ s'.pendingObservers) ∧
  (∀ mo ∈ s'.pendingObservers, mo ∈ s.pendingObservers ∨ InterestedInAttribute s mo target name ns) ∧
  s'.microtaskQueued = true

/-! ## attribute list の探索 -/

/-- 述語を満たす最初の attribute（無ければ null）。 -/
def FirstAttr (as : List Attr) (p : Attr → Prop) : Option Attr → Prop
  | some a => ∃ pre post, as = pre ++ a :: post ∧ p a ∧ ∀ x ∈ pre, ¬ p x
  | none => ∀ x ∈ as, ¬ p x

/-- "get an attribute by namespace and local name"。空文字列の namespace は null にする。 -/
def AttrByKey (d : NodeData) (ns : Option String) (localName : String) : Option Attr → Prop :=
  FirstAttr d.attributes fun a => a.namespace = normalizeNamespace ns ∧ a.localName = localName

/--
"get an attribute by name" の step 1。element が HTML namespace にあり、node document が
HTML document なら、qualified name を ASCII lowercase する。
-/
def AttrNameNormalized (t : Tree) (d : NodeData) (qn qn' : String) : Prop :=
  ((d.namespace = some htmlNamespace ∧ ∃ doc, t.get? d.ownerDocument = some doc ∧
      doc.isHTMLDocument = true) ∧ qn' = asciiLowercase qn) ∨
    (¬ (d.namespace = some htmlNamespace ∧ ∃ doc, t.get? d.ownerDocument = some doc ∧
      doc.isHTMLDocument = true) ∧ qn' = qn)

/-- "get an attribute by name"：正規化した qualified name に一致する最初の attribute。 -/
def AttrByName (t : Tree) (d : NodeData) (qn : String) (r : Option Attr) : Prop :=
  ∃ qn', AttrNameNormalized t d qn qn' ∧ FirstAttr d.attributes (fun a => a.qualifiedName = qn') r

/-! ## attribute list を変える -/

/-- element の attribute list だけが `as` になる。 -/
structure AttributesReplaced (t t' : Tree) (element : NodeId) (as : List Attr) : Prop where
  changed : ∀ d, t.get? element = some d → t'.get? element = some { d with attributes := as }
  others : ∀ m, m ≠ element → t'.get? m = t.get? m

/--
"handle attribute changes" の step 1：record を積む。木と live range などは変えない。
-/
def AttributeChangeHandled (s s' : DOMState) (element : NodeId) (a : Attr)
    (oldValue : Option String) : Prop :=
  AttributeRecordQueued s s' element a.localName a.namespace oldValue ∧ ObserverOnly s s'

/-- 木だけを差し替えた状態。 -/
def TreeOnly (s s₁ : DOMState) : Prop :=
  s₁.ranges = s.ranges ∧ s₁.iterators = s.iterators ∧ s₁.registrations = s.registrations ∧
    s₁.observers = s.observers ∧ s₁.pendingObservers = s.pendingObservers ∧
    s₁.microtaskQueued = s.microtaskQueued ∧ Untouched s s₁

/--
**"change an attribute"。** 1. oldValue は attribute の value。2. value を書き換える。
3. handle attribute changes。
-/
def AttributeChanged (s : DOMState) (element : NodeId) (d : NodeData) (a : Attr) (value : String)
    (s' : DOMState) : Prop :=
  ∃ (pre post : List Attr) (s₁ : DOMState),
    s.tree.get? element = some d ∧
    d.attributes = pre ++ a :: post ∧ (∀ x ∈ pre, x.key ≠ a.key) ∧
    AttributesReplaced s.tree s₁.tree element (pre ++ { a with value := value } :: post) ∧
    TreeOnly s s₁ ∧
    AttributeChangeHandled s₁ s' element a (some a.value)

/--
**"append an attribute"。** 3. attribute の node document を element のものにする。
4. list の末尾に足す。1. handle attribute changes（oldValue は null）。
-/
def AttributeAppended (s : DOMState) (element : NodeId) (d : NodeData) (a₀ : Attr)
    (s' : DOMState) : Prop :=
  ∃ s₁ : DOMState,
    s.tree.get? element = some d ∧
    AttributesReplaced s.tree s₁.tree element
      (d.attributes ++ [{ a₀ with ownerDocument := d.ownerDocument }]) ∧
    TreeOnly s s₁ ∧
    AttributeChangeHandled s₁ s' element { a₀ with ownerDocument := d.ownerDocument } none

/--
**"remove an attribute"。** list から取り除き、handle attribute changes
（oldValue は attribute の value）。
-/
def AttributeRemoved (s : DOMState) (element : NodeId) (d : NodeData) (a : Attr)
    (s' : DOMState) : Prop :=
  ∃ (pre post : List Attr) (s₁ : DOMState),
    s.tree.get? element = some d ∧
    d.attributes = pre ++ a :: post ∧ (∀ x ∈ pre, x.key ≠ a.key) ∧
    AttributesReplaced s.tree s₁.tree element (pre ++ post) ∧
    TreeOnly s s₁ ∧
    AttributeChangeHandled s₁ s' element a (some a.value)

/-! ## `Element` の method -/

/--
receiver の guard（model の都合）：木に無いか Element でなければ NotFoundError。

Element でない receiver の WebIDL の TypeError は method を呼ぶ層が先に返す。
-/
def ReceiverError (s : DOMState) (element : NodeId) (e : DOMException) : Prop :=
  (s.tree.get? element = none ∧ e = .notFoundError) ∨
    (∃ d, s.tree.get? element = some d ∧ d.kind ≠ .element ∧ e = .notFoundError)

/-- receiver が木にある Element であること。 -/
def IsElementData (s : DOMState) (element : NodeId) (d : NodeData) : Prop :=
  s.tree.get? element = some d ∧ d.kind = .element

/--
**`setAttribute(qualifiedName, value)` の、結果まで含めた関係。**

1. qualifiedName が valid attribute local name でなければ InvalidCharacterError。
3-4. get an attribute by name。
5. あれば change an attribute。
6-7. 無ければ（step 2 で正規化した名前で）attribute を作って append する。
-/
def SetAttributeResult (s : DOMState) (element : NodeId) (qn value : String) :
    Except DOMException DOMState → Prop
  | .error e => (isValidAttributeLocalName qn = false ∧ e = .invalidCharacterError) ∨
      (isValidAttributeLocalName qn = true ∧ ReceiverError s element e)
  | .ok s' => isValidAttributeLocalName qn = true ∧ ∃ d, IsElementData s element d ∧
      ((∃ a, AttrByName s.tree d qn (some a) ∧ AttributeChanged s element d a value s') ∨
        (AttrByName s.tree d qn none ∧ ∃ qn', AttrNameNormalized s.tree d qn qn' ∧
          AttributeAppended s element d
            { id := freshStateAttrId s, localName := qn', value := value,
              ownerDocument := d.ownerDocument } s'))

/--
**"set an attribute value"（`setAttributeNS` の step 2 から先）。**

2. get an attribute by namespace and local name。無ければ作って append。
3. あれば change an attribute。
-/
def SetAttributeValueResult (s : DOMState) (element : NodeId) (localName value : String)
    («prefix» ns : Option String) : Except DOMException DOMState → Prop
  | .error e => ReceiverError s element e
  | .ok s' => ∃ d, IsElementData s element d ∧
      ((∃ a, AttrByKey d ns localName (some a) ∧ AttributeChanged s element d a value s') ∨
        (AttrByKey d ns localName none ∧
          AttributeAppended s element d
            { id := freshStateAttrId s, «namespace» := normalizeNamespace ns, «prefix» := «prefix»,
              localName := localName, value := value, ownerDocument := d.ownerDocument } s'))

/-- **`removeAttribute(qualifiedName)`。** remove an attribute by name。無ければ何もしない。 -/
def RemoveAttributeResult (s : DOMState) (element : NodeId) (qn : String) :
    Except DOMException DOMState → Prop
  | .error e => ReceiverError s element e
  | .ok s' => ∃ d, IsElementData s element d ∧
      ((AttrByName s.tree d qn none ∧ s' = s) ∨
        (∃ a, AttrByName s.tree d qn (some a) ∧ AttributeRemoved s element d a s'))

/-- **`removeAttributeNS(namespace, localName)`。** -/
def RemoveAttributeNSResult (s : DOMState) (element : NodeId) (ns : Option String)
    (localName : String) : Except DOMException DOMState → Prop
  | .error e => ReceiverError s element e
  | .ok s' => ∃ d, IsElementData s element d ∧
      ((AttrByKey d ns localName none ∧ s' = s) ∨
        (∃ a, AttrByKey d ns localName (some a) ∧ AttributeRemoved s element d a s'))

/--
**`toggleAttribute(qualifiedName, force)`。**

4. attribute が無いとき、force が無いか true なら作って append し true、そうでなければ false。
5. あるとき、force が無いか false なら remove して false、そうでなければ true。
-/
def ToggleAttributeResult (s : DOMState) (element : NodeId) (qn : String) (force : Option Bool) :
    Except DOMException (DOMState × Bool) → Prop
  | .error e => (isValidAttributeLocalName qn = false ∧ e = .invalidCharacterError) ∨
      (isValidAttributeLocalName qn = true ∧ ReceiverError s element e)
  | .ok (s', b) => isValidAttributeLocalName qn = true ∧ ∃ d, IsElementData s element d ∧
      ((AttrByName s.tree d qn none ∧
          ((force = some false ∧ s' = s ∧ b = false) ∨
            (force ≠ some false ∧ b = true ∧ ∃ qn', AttrNameNormalized s.tree d qn qn' ∧
              AttributeAppended s element d
                { id := freshStateAttrId s, localName := qn', ownerDocument := d.ownerDocument }
                s'))) ∨
        (∃ a, AttrByName s.tree d qn (some a) ∧
          ((force = some true ∧ s' = s ∧ b = true) ∨
            (force ≠ some true ∧ b = false ∧ AttributeRemoved s element d a s'))))

end Dom.Spec
