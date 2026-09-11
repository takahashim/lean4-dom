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

/--
DOM Standard §4.3.2 の `MutationObserverInit`。

IDL は `childList` / `subtree` / `attributeOldValue` / `characterDataOldValue` に
`false` の既定値を与えるが、`attributes` と `characterData` には与えない。
`observe` の step 1-2 が「存在するか」で分岐するので、この二つは `Option Bool` で持つ。
`attributeFilter` も同じく存在の有無に意味がある（step 5、および
"queue a mutation record" step 2.3 の三つ目の条件）。

`attributes` に対応する `Attr` node の観測は model の対象外だが、
attribute の変更そのものは §4.9 の algorithm として扱う。
-/
structure MutationObserverInit where
  childList : Bool := false
  subtree : Bool := false
  attributes : Option Bool := none
  attributeOldValue : Bool := false
  attributeFilter : Option (List String) := none
  characterData : Option Bool := none
  characterDataOldValue : Bool := false
deriving DecidableEq, Repr, Inhabited

namespace MutationObserverInit

/--
`observe` の step 1-2。省略された `attributes` / `characterData` を埋める。

step 1 は `attributeOldValue` が **存在する** ことを条件にするが、IDL の既定値が
`false` なので、model では「true である」ことで代用する。
`attributeOldValue: false` を明示した場合との差は
step 4 の TypeError の有無にしか出ず、そこでは `attributes` が
`some false` でなければならないので結論は変わらない。
`characterDataOldValue` も同様である。
-/
def resolve (o : MutationObserverInit) : MutationObserverInit :=
  let o := if o.attributes.isNone && (o.attributeOldValue || o.attributeFilter.isSome) then
      { o with attributes := some true } else o
  if o.characterData.isNone && o.characterDataOldValue then
    { o with characterData := some true } else o

end MutationObserverInit

/-!
## `MutationObserver` の method

観測モデルの `Dom.observe`（`Dom/Observation.lean`）と名前がぶつかるので、
`MutationObserver` namespace に入れる。
-/

namespace MutationObserver


/--
DOM Standard §4.3 `MutationObserver.observe(target, options)` の step 3-6。

解決後（step 1-2 の後）の options を検査する。
検査だけを切り出してあるのは、失敗の条件を単体で述べられるようにするためである。
-/
def observeOptionsError (opts₀ : MutationObserverInit) : Option DOMException :=
  let opts := opts₀.resolve
  -- step 3
  if !(opts.childList || opts.attributes == some true || opts.characterData == some true) then
    some .typeError
  -- step 4
  else if opts.attributeOldValue && opts.attributes == some false then some .typeError
  -- step 5
  else if opts.attributeFilter.isSome && opts.attributes == some false then some .typeError
  -- step 6
  else if opts.characterDataOldValue && opts.characterData == some false then some .typeError
  else none

/--
DOM Standard §4.3 `MutationObserver.observe(target, options)`。

step 1-2 は `MutationObserverInit.resolve`、step 3-6 は `observeOptionsError` が行う。
TypeError は四通りある。

* `childList` / `attributes` / `characterData` のどれも true でない（step 3）。
* `attributeOldValue` が true で `attributes` が false（step 4）。
* `attributeFilter` があって `attributes` が false（step 5）。
* `characterDataOldValue` が true で `characterData` が false（step 6）。

step 4-6 の「false である」は解決後の値なので、
省略された場合（step 1-2 で true になる）は TypeError にならない。
-/
def observe (s : DOMState) (mo : Nat) (target : NodeId) (opts₀ : MutationObserverInit) :
    Except DOMException DOMState :=
  let opts := opts₀.resolve
  -- model の都合。仕様では target は実在する node、`this` は実在する observer である。
  if (s.tree.get? target).isNone then .error .notFoundError
  else if mo ≥ s.observers.length then .error .notFoundError
  else match observeOptionsError opts₀ with
  | some e => .error e
  | none =>
    let reg : Registration :=
      { node := target, observer := mo, subtree := opts.subtree, childList := opts.childList,
        attributes := opts.attributes == some true,
        attributeOldValue := opts.attributeOldValue,
        attributeFilter := opts.attributeFilter,
        characterData := opts.characterData == some true,
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

/--
`observe` は木も live object も変えない。

失敗の分岐が多いので、三つの成分をまとめて一度に示す。
-/
theorem observe_frame {s s' : DOMState} {mo : Nat} {target : NodeId}
    {opts : MutationObserverInit} (h : observe s mo target opts = .ok s') :
    s'.tree = s.tree ∧ s'.ranges = s.ranges ∧ s'.iterators = s.iterators := by
  unfold observe at h
  repeat' split at h
  -- 成功する分岐では `h` が `... = s'` の形になる。失敗する分岐は `simp` が潰す。
  all_goals first
    | (subst h; exact ⟨rfl, rfl, rfl⟩)
    | (rw [← Except.ok.inj h]; exact ⟨rfl, rfl, rfl⟩)
    | simp at h

@[simp] theorem observe_tree {s s' : DOMState} {mo : Nat} {target : NodeId}
    {opts : MutationObserverInit} (h : observe s mo target opts = .ok s') :
    s'.tree = s.tree := (observe_frame h).1

@[simp] theorem observe_ranges {s s' : DOMState} {mo : Nat} {target : NodeId}
    {opts : MutationObserverInit} (h : observe s mo target opts = .ok s') :
    s'.ranges = s.ranges := (observe_frame h).2.1

@[simp] theorem observe_iterators {s s' : DOMState} {mo : Nat} {target : NodeId}
    {opts : MutationObserverInit} (h : observe s mo target opts = .ok s') :
    s'.iterators = s.iterators := (observe_frame h).2.2

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
