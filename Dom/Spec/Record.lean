import Dom.Basic.State
import Dom.Basic.Order

/-!
# childList の mutation record を積む step の関係意味論（§4.3.4）

`remove` の step 21 と `insert` の step 4.2 / 9 が使う。
どちらも「childList の record を一つ積む」だけなので、一つの関係にまとめてある。

childList の record は oldValue を持たないので、"queue a mutation record" の
step 2.3.2-2.3.3（同じ observer が二度出たら oldValue を上書きする）は効かない。
attributes / characterData を含む一般形はまだ無い。
-/

namespace Dom.Spec

open Dom

/--
§4.3.4 "queue a mutation record" の step 2.3 のうち、childList record に効く部分。

childList の record は oldValue を持たないので、step 2.3.2-2.3.3 の
「同じ observer が二度出たら oldValue を上書きする」は効かない。
-/
def InterestedInChildList (s : DOMState) (mo : Nat) (target : NodeId) : Prop :=
  ∃ r ∈ s.registrations, r.observer = mo ∧ r.childList = true ∧
    InclusiveAncestor s.tree r.node target ∧ (r.node = target ∨ r.subtree = true)

/--
仕様の step 21。`suppressObservers` が false なら childList の record を積む。

record は interested な observer の queue の末尾に一つだけ積まれ、
その observer は pending mutation observers に入り、microtask が予約される。
-/
def TreeRecordQueued (s s' : DOMState) (target : NodeId) (added removed : List NodeId)
    (oldPrev oldNext : Option NodeId) (suppress : Bool) : Prop :=
  if suppress then
    s'.observers.length = s.observers.length ∧
    (∀ (mo : Nat) (o o' : ObserverState), s.observers[mo]? = some o →
      s'.observers[mo]? = some o' → o'.records = o.records) ∧
    (∀ mo : Nat, mo ∈ s'.pendingObservers ↔ mo ∈ s.pendingObservers) ∧
    s'.microtaskQueued = s.microtaskQueued
  else
    let rec' : MutationRecord :=
      { type := .childList, target := target, addedNodes := added, removedNodes := removed,
        previousSibling := oldPrev, nextSibling := oldNext }
    s'.observers.length = s.observers.length ∧
    (∀ (mo : Nat) (o o' : ObserverState), s.observers[mo]? = some o →
      s'.observers[mo]? = some o' →
      (InterestedInChildList s mo target → o'.records = o.records ++ [rec']) ∧
      (¬ InterestedInChildList s mo target → o'.records = o.records)) ∧
    (∀ mo, InterestedInChildList s mo target → mo ∈ s'.pendingObservers) ∧
    (∀ mo ∈ s.pendingObservers, mo ∈ s'.pendingObservers) ∧
    (∀ mo ∈ s'.pendingObservers, mo ∈ s.pendingObservers ∨ InterestedInChildList s mo target) ∧
    s'.microtaskQueued = true
/-! ## characterData の record -/

/--
§4.3.4 "queue a mutation record" の step 2.3 のうち、characterData record に効く部分。
-/
def InterestedInCharacterData (s : DOMState) (mo : Nat) (target : NodeId) : Prop :=
  ∃ r ∈ s.registrations, r.observer = mo ∧ r.characterData = true ∧
    InclusiveAncestor s.tree r.node target ∧ (r.node = target ∨ r.subtree = true)

/--
step 2.3.3。oldValue が載るのは、`characterDataOldValue` を持つ registration が
その observer にあるときだけである。

同じ observer が二度出たときに oldValue を上書きするのは、この形に効く
（一つでも flag があれば載る）。
-/
def CharacterDataOldValueWanted (s : DOMState) (mo : Nat) (target : NodeId) : Prop :=
  ∃ r ∈ s.registrations, r.observer = mo ∧ r.characterData = true ∧
    r.characterDataOldValue = true ∧
    InclusiveAncestor s.tree r.node target ∧ (r.node = target ∨ r.subtree = true)

/-- §4.10 replace data の step 4。characterData の record を一つ積む。 -/
def CharacterDataRecordQueued (s s' : DOMState) (target : NodeId) (oldValue : String) : Prop :=
  s'.observers.length = s.observers.length ∧
  (∀ (mo : Nat) (o o' : ObserverState), s.observers[mo]? = some o →
    s'.observers[mo]? = some o' →
    (InterestedInCharacterData s mo target → CharacterDataOldValueWanted s mo target →
      o'.records = o.records ++
        [{ type := .characterData, target := target, oldValue := some oldValue }]) ∧
    (InterestedInCharacterData s mo target → ¬ CharacterDataOldValueWanted s mo target →
      o'.records = o.records ++ [{ type := .characterData, target := target }]) ∧
    (¬ InterestedInCharacterData s mo target → o'.records = o.records)) ∧
  (∀ mo, InterestedInCharacterData s mo target → mo ∈ s'.pendingObservers) ∧
  (∀ mo ∈ s.pendingObservers, mo ∈ s'.pendingObservers) ∧
  (∀ mo ∈ s'.pendingObservers, mo ∈ s.pendingObservers ∨ InterestedInCharacterData s mo target) ∧
  s'.microtaskQueued = true

end Dom.Spec
