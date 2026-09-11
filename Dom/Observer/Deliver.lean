import Dom.Observer.Record

/-!
# MutationObserver の配送

DOM Standard §4.3 の "queue a mutation observer microtask"、
"notify mutation observers"、および `observe` / `disconnect` / `takeRecords`。

callback は model の外なので、`notifyMutationObservers` は
「どの observer に何が配送されるか」を返す形にしてある。

## 仕様の読み方

"notify mutation observers" step 5.2 と `observe` step 7.1 は、
transient registered observer を **observer の node list に載っている node から** 取り除く。
一方 remove step 20 は transient を「外す node」に足すだけで node list には触れない。
本文どおりだと transient が決して掃除されないので、
remove step 20 が node list にもその node を足すと読む。
実装（ブラウザと Dommy）もそう振る舞う。
-/

namespace Dom

/-- `MutationObserverInit` のうち、本 model が扱う四つ。 -/
structure MutationObserverInit where
  childList : Bool := false
  subtree : Bool := false
  characterData : Bool := false
  characterDataOldValue : Bool := false
deriving DecidableEq, Repr, Inhabited

/-!
## `MutationObserver` の method

観測モデルの `Dom.observe`（`Dom/Observation.lean`）と名前がぶつかるので、
`MutationObserver` namespace に入れる。
-/

namespace MutationObserver


/--
DOM Standard §4.3 `MutationObserver.observe(target, options)`。

attribute は扱わないので、TypeError になるのは次の二つである。

* `childList` も `characterData` も true でない（step 3）。
* `characterDataOldValue` が true で `characterData` が false（step 6）。
-/
def observe (s : DOMState) (mo : Nat) (target : NodeId) (opts : MutationObserverInit) :
    Except DOMException DOMState :=
  -- model の都合。仕様では target は実在する node、`this` は実在する observer である。
  if (s.tree.get? target).isNone then .error .notFoundError
  else if mo ≥ s.observers.length then .error .notFoundError
  -- step 3
  else if !(opts.childList || opts.characterData) then .error .typeError
  -- step 6
  else if opts.characterDataOldValue && !opts.characterData then .error .typeError
  else
    let reg : Registration :=
      { node := target, observer := mo, subtree := opts.subtree, childList := opts.childList,
        characterData := opts.characterData,
        characterDataOldValue := opts.characterDataOldValue }
    -- step 7。既にこの observer の registration が target にあるか。
    if s.registrations.any (fun r => r.observer == mo && r.node == target && !r.transient) then
      -- step 7.1.1：この registration を source とする transient を取り除く。
      -- step 7.1.2：options を差し替える。
      .ok { s with
              registrations := s.registrations.filterMap fun r =>
                if r.transient && r.observer == mo && r.source == some target then none
                else if r.observer == mo && r.node == target && !r.transient then some reg
                else some r }
    else
      -- step 7.2：registration を足し、target を node list に足す。
      .ok { s with
              registrations := s.registrations ++ [reg]
              observers := match s.observers[mo]? with
                | none => s.observers
                | some o => s.observers.set mo { o with nodeList := o.nodeList ++ [target] } }

/--
DOM Standard §4.3 `MutationObserver.disconnect()`。

node list は空にしない（仕様もそうしている）。
-/
def disconnect (s : DOMState) (mo : Nat) : DOMState :=
  { s with
      registrations := s.registrations.filter fun r => r.observer != mo
      observers := match s.observers[mo]? with
        | none => s.observers
        | some o => s.observers.set mo { o with records := [] } }

/-- DOM Standard §4.3 `MutationObserver.takeRecords()`。 -/
def takeRecords (s : DOMState) (mo : Nat) : DOMState × List MutationRecord :=
  match s.observers[mo]? with
  | none => (s, [])
  | some o => ({ s with observers := s.observers.set mo { o with records := [] } }, o.records)

end MutationObserver

/-! ## notify -/

/-- ある observer の transient registration を全部外す。 -/
def removeTransients (s : DOMState) (mo : Nat) : DOMState :=
  { s with registrations := s.registrations.filter fun r => !(r.transient && r.observer == mo) }

/--
DOM Standard §4.3 "notify mutation observers" の step 5。

一つの observer について、record queue を空にし、transient registration を外し、
配送する record を返す。
-/
def notifyOne (s : DOMState) (mo : Nat) : DOMState × List MutationRecord :=
  let (s₁, records) := MutationObserver.takeRecords s mo
  (removeTransients s₁ mo, records)

/-- step 5 の繰り返し。 -/
def notifyEach : DOMState → List Nat → DOMState × List (Nat × List MutationRecord)
  | s, [] => (s, [])
  | s, mo :: rest =>
    let (s₁, records) := notifyOne s mo
    let (s₂, out) := notifyEach s₁ rest
    (s₂, if records.isEmpty then out else (mo, records) :: out)

/--
DOM Standard §4.3 "notify mutation observers"。

signal slots（slotchange の発火）は Shadow DOM なので扱わない。
callback の呼び出しも model の外なので、
「どの observer に何が配送されるか」を返す形にしてある。
record が空の observer は callback を呼ばないので、返り値にも出さない。
-/
def notifyMutationObservers (s : DOMState) : DOMState × List (Nat × List MutationRecord) :=
  let notifySet := s.pendingObservers
  let s₀ := { s with microtaskQueued := false, pendingObservers := [] }
  notifyEach s₀ notifySet

/-! ## 木も live object も変えないこと -/

namespace MutationObserver

@[simp] theorem observe_tree {s s' : DOMState} {mo : Nat} {target : NodeId}
    {opts : MutationObserverInit} (h : observe s mo target opts = .ok s') :
    s'.tree = s.tree := by
  unfold observe at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · split at h <;> rw [← Except.ok.inj h]

@[simp] theorem observe_ranges {s s' : DOMState} {mo : Nat} {target : NodeId}
    {opts : MutationObserverInit} (h : observe s mo target opts = .ok s') :
    s'.ranges = s.ranges := by
  unfold observe at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · split at h <;> rw [← Except.ok.inj h]

@[simp] theorem observe_iterators {s s' : DOMState} {mo : Nat} {target : NodeId}
    {opts : MutationObserverInit} (h : observe s mo target opts = .ok s') :
    s'.iterators = s.iterators := by
  unfold observe at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · split at h <;> rw [← Except.ok.inj h]

/-- `observe` は observer の数を変えない。 -/
@[simp] theorem observe_nodeList_length (s : DOMState) (mo : Nat) (target : NodeId) :
    (match s.observers[mo]? with
      | none => s.observers
      | some o => s.observers.set mo { o with nodeList := o.nodeList ++ [target] }).length
      = s.observers.length := by
  split
  · rfl
  · simp

@[simp] theorem disconnect_observers_length (s : DOMState) (mo : Nat) :
    (disconnect s mo).observers.length = s.observers.length := by
  unfold disconnect
  simp only []
  split
  · rfl
  · simp

@[simp] theorem takeRecords_observers_length (s : DOMState) (mo : Nat) :
    (takeRecords s mo).1.observers.length = s.observers.length := by
  unfold takeRecords
  split
  · rfl
  · simp

@[simp] theorem disconnect_tree (s : DOMState) (mo : Nat) : (disconnect s mo).tree = s.tree := rfl
@[simp] theorem disconnect_ranges (s : DOMState) (mo : Nat) :
    (disconnect s mo).ranges = s.ranges := rfl
@[simp] theorem disconnect_iterators (s : DOMState) (mo : Nat) :
    (disconnect s mo).iterators = s.iterators := rfl

@[simp] theorem takeRecords_tree (s : DOMState) (mo : Nat) :
    (takeRecords s mo).1.tree = s.tree := by
  unfold takeRecords; split <;> rfl
@[simp] theorem takeRecords_ranges (s : DOMState) (mo : Nat) :
    (takeRecords s mo).1.ranges = s.ranges := by
  unfold takeRecords; split <;> rfl
@[simp] theorem takeRecords_iterators (s : DOMState) (mo : Nat) :
    (takeRecords s mo).1.iterators = s.iterators := by
  unfold takeRecords; split <;> rfl

end MutationObserver

@[simp] theorem removeTransients_tree (s : DOMState) (mo : Nat) :
    (removeTransients s mo).tree = s.tree := rfl
@[simp] theorem removeTransients_ranges (s : DOMState) (mo : Nat) :
    (removeTransients s mo).ranges = s.ranges := rfl
@[simp] theorem removeTransients_iterators (s : DOMState) (mo : Nat) :
    (removeTransients s mo).iterators = s.iterators := rfl

theorem notifyEach_tree : ∀ (s : DOMState) (ms : List Nat), (notifyEach s ms).1.tree = s.tree
  | _, [] => rfl
  | s, mo :: rest => by
    show (notifyEach (notifyOne s mo).1 rest).1.tree = s.tree
    rw [notifyEach_tree _ rest]
    show (removeTransients (MutationObserver.takeRecords s mo).1 mo).tree = s.tree
    simp

theorem notifyEach_ranges : ∀ (s : DOMState) (ms : List Nat), (notifyEach s ms).1.ranges = s.ranges
  | _, [] => rfl
  | s, mo :: rest => by
    show (notifyEach (notifyOne s mo).1 rest).1.ranges = s.ranges
    rw [notifyEach_ranges _ rest]
    show (removeTransients (MutationObserver.takeRecords s mo).1 mo).ranges = s.ranges
    simp

theorem notifyEach_iterators :
    ∀ (s : DOMState) (ms : List Nat), (notifyEach s ms).1.iterators = s.iterators
  | _, [] => rfl
  | s, mo :: rest => by
    show (notifyEach (notifyOne s mo).1 rest).1.iterators = s.iterators
    rw [notifyEach_iterators _ rest]
    show (removeTransients (MutationObserver.takeRecords s mo).1 mo).iterators = s.iterators
    simp

@[simp] theorem notifyMutationObservers_tree (s : DOMState) :
    (notifyMutationObservers s).1.tree = s.tree := notifyEach_tree _ _

@[simp] theorem notifyMutationObservers_ranges (s : DOMState) :
    (notifyMutationObservers s).1.ranges = s.ranges := notifyEach_ranges _ _

@[simp] theorem notifyMutationObservers_iterators (s : DOMState) :
    (notifyMutationObservers s).1.iterators = s.iterators := notifyEach_iterators _ _

end Dom
