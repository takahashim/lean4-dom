import Dom.Basic.State

/-!
# notify mutation observers・`disconnect()`・`takeRecords()` の関係意味論（§4.3）

本文は node ごとに registered observer list を持ち、notify の step 6.3（remove transient registered observers）と
`disconnect()` の step 1-2 は「observer の node list（transient node set）の各 node から」registered observer を外す。
model の registered observer list は一本の列（`DOMState.registrations`）で、各 registration が自分の node を持つので、
「observer が mo で、node が mo の node list にあるもの」を列から外す、と書く。model の node list は本文の
node list と transient node set を合わせたものである（`ObserverState.nodeList`）。

signal slots（step 4-5、7）は Shadow DOM なので扱わない。callback（step 6.4）は呼ばず、
「どの observer にどの records を渡すか」を結果の列に並べる。
-/

namespace Dom.Spec

open Dom

/--
**step 6.1-6.3：一つの observer への配送の準備。**

records は mo の record queue の clone で、record queue を空にし、mo の transient node set の各 node から
observer が mo の transient registered observer を外す。
-/
def ObserverNotified (s : DOMState) (mo : Nat) (s' : DOMState) (records : List MutationRecord) :
    Prop :=
  (∃ o, s.observers[mo]? = some o ∧ records = o.records ∧
    s' = { s with
      observers := s.observers.set mo { o with records := [] },
      registrations := s.registrations.filter fun r =>
        !(r.transient && r.observer == mo && o.nodeList.contains r.node) }) ∨
  -- model の都合：observer が無い番号。
  (s.observers[mo]? = none ∧ s' = s ∧ records = [])

/-- step 6：notify list の observer を順に。records が空でなければ callback に渡す（step 6.4）。 -/
inductive NotifiedEach : DOMState → List Nat → DOMState → List (Nat × List MutationRecord) → Prop
  | nil {s} : NotifiedEach s [] s []
  | cons {s s₁ s₂ mo rest records out} : ObserverNotified s mo s₁ records →
      NotifiedEach s₁ rest s₂ out →
      NotifiedEach s (mo :: rest) s₂ (if records = [] then out else (mo, records) :: out)

/--
**§4.3 "notify mutation observers" の関係。**

1. mutation observer microtask queued を false にする。
2. notify list は pending mutation observers を creation index の昇順に並べたもの。observer は scenario の
   初期状態でだけ作るので、creation index は `observers` の添字である。
3. pending mutation observers を空にする。
6. notify list の各 observer について step 6.1-6.4。
-/
def NotifyResult (s s' : DOMState) (out : List (Nat × List MutationRecord)) : Prop :=
  ∃ notifyList : List Nat, notifyList.Perm s.pendingObservers ∧ notifyList.Pairwise (· ≤ ·) ∧
    NotifiedEach { s with microtaskQueued := false, pendingObservers := [] } notifyList s' out

/--
**§4.3 `disconnect()` の関係。**

1-2. node list と transient node set の各 node から、observer が this の registered observer を外す。
3. node list を空にする（transient node set は step 2 で空になる）。
4. record queue を空にする。
-/
def DisconnectResult (s : DOMState) (mo : Nat) (s' : DOMState) : Prop :=
  (∃ o, s.observers[mo]? = some o ∧
    s' = { s with
      registrations := s.registrations.filter fun r =>
        !(r.observer == mo && o.nodeList.contains r.node),
      observers := s.observers.set mo { o with nodeList := [], records := [] } }) ∨
  (s.observers[mo]? = none ∧ s' = s)

/--
**§4.3 `takeRecords()` の関係。**

1. records は record queue の clone。2. record queue を空にする。3. records を返す。
-/
def TakeRecordsResult (s : DOMState) (mo : Nat) (s' : DOMState) (records : List MutationRecord) :
    Prop :=
  (∃ o, s.observers[mo]? = some o ∧ records = o.records ∧
    s' = { s with observers := s.observers.set mo { o with records := [] } }) ∨
  (s.observers[mo]? = none ∧ s' = s ∧ records = [])

end Dom.Spec
