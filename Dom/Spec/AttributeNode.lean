import Dom.Spec.Attribute

/-!
# `Attr` を node として渡す API の関係意味論（§4.9）

`setAttributeNode` / `removeAttributeNode` / `NamedNodeMap.removeNamedItem` と、
それらが走る "set an attribute"・"replace an attribute"・"remove an attribute"。
実行関数（`Dom/Attribute/Node.lean`）がこれを満たすことは
`Dom/Spec/AttributeNodeSound.lean` で証明する。

## model の範囲

* `Attr` の同一性は `AttrId` で表す。element を持たない `Attr` は `DOMState.detachedAttrs` にいる。
  仕様で「`Attr` の element を null にする」は「detach された list の末尾に足す」、
  「element を設定する」は「detach された list から外す」にあたる（model の約束）。
* 関係の一意性は、`Attr` の id が状態の中で一意であること（`AttrIdsUnique`）を前提にする。
  その不変条件はすべての操作が保つ（`Dom/Exec/AttrIds.lean`）。
-/

namespace Dom.Spec

open Dom

/-! ## `Attr` を id で引く -/

/-- id が `aid` の `Attr` は、どの element にも付いていない。 -/
def AttrIdUnattached (s : DOMState) (aid : AttrId) : Prop :=
  ∀ m d, s.tree.get? m = some d → ∀ b ∈ d.attributes, b.id ≠ aid

/--
id が `aid` の `Attr` と、その element（detach されていれば null）。
どこにも無ければ null（引数が `Attr` でない。WebIDL の変換で TypeError になる）。
-/
def AttrLocated (s : DOMState) (aid : AttrId) : Option (Attr × Option NodeId) → Prop
  | some (a, some m) => a.id = aid ∧ ∃ d, s.tree.get? m = some d ∧ a ∈ d.attributes
  | some (a, none) => a.id = aid ∧ a ∈ s.detachedAttrs ∧ AttrIdUnattached s aid
  | none => AttrIdUnattached s aid ∧ ∀ b ∈ s.detachedAttrs, b.id ≠ aid

/-! ## `Attr` の element を変える -/

/-- detach された `a` に element を設定する：detach された list から外す。他は変えない。 -/
def AttrTakenFromDetached (s s₀ : DOMState) (a : Attr) : Prop :=
  ∃ pre post, s.detachedAttrs = pre ++ a :: post ∧ (∀ x ∈ pre, x.id ≠ a.id) ∧
    s₀ = { s with detachedAttrs := pre ++ post }

/-- 木と detach された list（`D` になる）だけを差し替えた状態。 -/
def TreeDetachedOnly (s s₁ : DOMState) (D : List Attr) : Prop :=
  s₁.ranges = s.ranges ∧ s₁.iterators = s.iterators ∧ s₁.registrations = s.registrations ∧
    s₁.observers = s.observers ∧ s₁.pendingObservers = s.pendingObservers ∧
    s₁.microtaskQueued = s.microtaskQueued ∧ s₁.walkers = s.walkers ∧
    s₁.listeners = s.listeners ∧ s₁.detachedAttrs = D

/--
**"replace an attribute" `old` with `new`。**

2. element の attribute list で `old` を `new` に置き換える。
3-4. `new` の element と node document を element のものにする。
5. `old` の element を null にする（detach された list の末尾に足す）。
6. handle attribute changes（`old` について、oldValue は `old` の value）。
-/
def AttributeReplacedWith (s : DOMState) (element : NodeId) (d : NodeData) (old new : Attr)
    (s' : DOMState) : Prop :=
  ∃ (pre post : List Attr) (s₁ : DOMState),
    s.tree.get? element = some d ∧
    d.attributes = pre ++ old :: post ∧ (∀ x ∈ pre, x.key ≠ old.key) ∧
    AttributesReplaced s.tree s₁.tree element
      (pre ++ { new with ownerDocument := d.ownerDocument } :: post) ∧
    TreeDetachedOnly s s₁ (s.detachedAttrs ++ [old]) ∧
    AttributeChangeHandled s₁ s' element old (some old.value)

/--
**"remove an attribute" `a`（`Attr` を呼び出し側に返す場合）。**

2. element の attribute list から取り除く。3. element を null にする
（detach された list の末尾に足す）。4. handle attribute changes（oldValue は `a` の value）。
-/
def AttributeDetached (s : DOMState) (element : NodeId) (d : NodeData) (a : Attr)
    (s' : DOMState) : Prop :=
  ∃ (pre post : List Attr) (s₁ : DOMState),
    s.tree.get? element = some d ∧
    d.attributes = pre ++ a :: post ∧ (∀ x ∈ pre, x.id ≠ a.id) ∧
    AttributesReplaced s.tree s₁.tree element (pre ++ post) ∧
    TreeDetachedOnly s s₁ (s.detachedAttrs ++ [a]) ∧
    AttributeChangeHandled s₁ s' element a (some a.value)

/-! ## method -/

/--
**`setAttributeNode(attr)`（"set an attribute"）の、結果まで含めた関係。**

2. `attr` の element が null でも element でもなければ InUseAttributeError。
3. `attr` の namespace と local name で get an attribute（oldAttr）。
4. oldAttr が `attr` なら `attr` を返す（状態は変えない）。
7. oldAttr があれば replace an attribute、8. 無ければ append an attribute。9. oldAttr を返す。

`attr` の element が element なら、attribute list の鍵は一意なので step 3 で `attr` 自身が
見つかり step 4 で終わる。step 7-8 に来るのは `attr` の element が null のときだけである。
-/
def SetAttributeNodeResult (s : DOMState) (element : NodeId) (aid : AttrId) :
    Except DOMException (Option AttrId × DOMState) → Prop
  | .error e => ReceiverError s element e ∨ ∃ d, IsElementData s element d ∧
      ((AttrLocated s aid none ∧ e = .notFoundError) ∨
        (∃ a m, AttrLocated s aid (some (a, some m)) ∧ m ≠ element ∧ e = .inUseAttributeError))
  | .ok (r, s') => ∃ d, IsElementData s element d ∧ ∃ a o, AttrLocated s aid (some (a, o)) ∧
      (o = none ∨ o = some element) ∧
      ((∃ old, AttrByKey d a.namespace a.localName (some old) ∧ old.id = aid ∧
          r = some aid ∧ s' = s) ∨
        (∃ old, AttrByKey d a.namespace a.localName (some old) ∧ old.id ≠ aid ∧ o = none ∧
          r = some old.id ∧ ∃ s₀, AttrTakenFromDetached s s₀ a ∧
            AttributeReplacedWith s₀ element d old a s') ∨
        (AttrByKey d a.namespace a.localName none ∧ o = none ∧ r = none ∧
          ∃ s₀, AttrTakenFromDetached s s₀ a ∧ AttributeAppended s₀ element d a s'))

/--
**`removeAttributeNode(attr)`。**

1. element の attribute list に `attr` が無ければ NotFoundError。
2. remove an attribute。3. `attr` を返す。
-/
def RemoveAttributeNodeResult (s : DOMState) (element : NodeId) (aid : AttrId) :
    Except DOMException (AttrId × DOMState) → Prop
  | .error e => ReceiverError s element e ∨ ∃ d, IsElementData s element d ∧
      (∀ a ∈ d.attributes, a.id ≠ aid) ∧ e = .notFoundError
  | .ok (r, s') => ∃ d, IsElementData s element d ∧ ∃ a ∈ d.attributes, a.id = aid ∧
      r = aid ∧ AttributeDetached s element d a s'

/--
**`NamedNodeMap.removeNamedItem(qualifiedName)`。**

1. remove an attribute by name（get an attribute by name、あれば remove an attribute）。
2. 無ければ NotFoundError。3. 取り除いた `Attr` を返す。
-/
def RemoveNamedItemResult (s : DOMState) (element : NodeId) (qn : String) :
    Except DOMException (AttrId × DOMState) → Prop
  | .error e => ReceiverError s element e ∨ ∃ d, IsElementData s element d ∧
      AttrByName s.tree d qn none ∧ e = .notFoundError
  | .ok (r, s') => ∃ d, IsElementData s element d ∧ ∃ a, AttrByName s.tree d qn (some a) ∧
      r = a.id ∧ AttributeDetached s element d a s'

end Dom.Spec
