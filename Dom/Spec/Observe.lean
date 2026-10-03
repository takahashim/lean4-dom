import Dom.Observer.Deliver

/-!
# `MutationObserver.observe` の関係意味論（§4.3）

実行関数（`Dom/Observer/Deliver.lean` の `MutationObserver.observe`）がこの関係と
ちょうど一致する（等号）ことは `Dom/Spec/ObserveSound.lean` で証明する。

## 読み

step 1-2 の「`attributeOldValue` / `characterDataOldValue` が存在する」は、IDL の既定値が
false なので「true である」と読む（`MutationObserverInit.resolve` の注を参照）。
`attributeFilter` は存在の有無をそのまま見る。

step 7.1.1 は「node list の各 node から、source が registered の transient を取り除く」である。
model の registered observer list は一本で、transient は source の node（`source`）を持つので、
「この observer の transient で、source が target のもの」を取り除く。
-/

namespace Dom.Spec

open Dom MutationObserver

/-- step 1：`attributes` が省略され、`attributeOldValue` か `attributeFilter` があれば true にする。 -/
def AttributesResolved (o : MutationObserverInit) (b : Option Bool) : Prop :=
  (o.attributes = none ∧ (o.attributeOldValue = true ∨ o.attributeFilter ≠ none) ∧ b = some true) ∨
    (¬ (o.attributes = none ∧ (o.attributeOldValue = true ∨ o.attributeFilter ≠ none)) ∧
      b = o.attributes)

/-- step 2：`characterData` が省略され、`characterDataOldValue` があれば true にする。 -/
def CharacterDataResolved (o : MutationObserverInit) (b : Option Bool) : Prop :=
  (o.characterData = none ∧ o.characterDataOldValue = true ∧ b = some true) ∨
    (¬ (o.characterData = none ∧ o.characterDataOldValue = true) ∧ b = o.characterData)

/--
**step 3-6：TypeError になる options。**

3. childList・attributes・characterData のどれも true でない。
4. attributeOldValue が true で attributes が false。
5. attributeFilter があって attributes が false。
6. characterDataOldValue が true で characterData が false。

attributes と characterData は step 1-2 で解決した後の値で見る。
-/
def ObserveOptionsRejected (o : MutationObserverInit) : Prop :=
  ∃ a c, AttributesResolved o a ∧ CharacterDataResolved o c ∧
    ((o.childList = false ∧ a ≠ some true ∧ c ≠ some true) ∨
      (o.attributeOldValue = true ∧ a = some false) ∨
      (o.attributeFilter ≠ none ∧ a = some false) ∨
      (o.characterDataOldValue = true ∧ c = some false))

/-- step 7-8 で使う registered observer（options は解決後の値）。 -/
def registrationFor (mo : Nat) (target : NodeId) (o : MutationObserverInit) (a c : Option Bool) :
    Registration :=
  { node := target, observer := mo, subtree := o.subtree, childList := o.childList,
    attributes := decide (a = some true), attributeOldValue := o.attributeOldValue,
    attributeFilter := o.attributeFilter, characterData := decide (c = some true),
    characterDataOldValue := o.characterDataOldValue }

/-- step 7.1：source がこの registration の transient を落とし、registration の options を差し替える。 -/
def reregistered (mo : Nat) (target : NodeId) (reg r : Registration) : Option Registration :=
  if r.transient = true ∧ r.observer = mo ∧ r.source = some target then none
  else if r.observer = mo ∧ r.node = target ∧ r.transient = false then some reg
  else some r

/--
**`observe(target, options)` の、結果まで含めた関係。**

target が木に無い、または observer が無いのは model の都合で `NotFoundError`。

7. target の registered observer list にこの observer のものがあれば、
   1. source がそれである transient を取り除き、2. options を差し替える。
8. 無ければ、registered observer を足し、target を node list に足す。
-/
def ObserveResult (s : DOMState) (mo : Nat) (target : NodeId) (o : MutationObserverInit) :
    Except DOMException DOMState → Prop
  | .error e => (((s.tree.get? target = none) ∨ s.observers.length ≤ mo) ∧ e = .notFoundError) ∨
      ((∃ d, s.tree.get? target = some d) ∧ mo < s.observers.length ∧
        ObserveOptionsRejected o ∧ e = .typeError)
  | .ok s' => (∃ d, s.tree.get? target = some d) ∧ mo < s.observers.length ∧
      ¬ ObserveOptionsRejected o ∧
      ∃ a c, AttributesResolved o a ∧ CharacterDataResolved o c ∧
        -- step 7
        (((∃ r ∈ s.registrations, r.observer = mo ∧ r.node = target ∧ r.transient = false) ∧
            s' = { s with registrations :=
              s.registrations.filterMap (reregistered mo target (registrationFor mo target o a c)) }) ∨
          -- step 8
          ((¬ ∃ r ∈ s.registrations, r.observer = mo ∧ r.node = target ∧ r.transient = false) ∧
            ∃ ob, s.observers[mo]? = some ob ∧
              s' = { s with
                registrations := s.registrations ++ [registrationFor mo target o a c]
                observers := s.observers.set mo { ob with nodeList := ob.nodeList ++ [target] } }))

end Dom.Spec
