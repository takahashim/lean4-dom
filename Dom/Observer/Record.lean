import Dom.Basic.State
import Dom.Basic.Order

/-!
# MutationObserver の record

DOM Standard §4.3.4 の "queue a mutation record" と "queue a tree mutation record"、
および §4.3 "add transient registered observers"（remove step 15 と move step 17 が呼ぶ）を定義する。

配送そのもの（"notify mutation observers"）は `Dom/Observer/Deliver.lean` にある。
ここは record を積むところまでで、transient registered observer を消すのは配送の側
（"remove transient registered observers"）である。
-/

namespace Dom

/-! ## interested observers -/

/--
"queue a mutation record" step 2.3 の条件。

仕様は「次のいずれも真でないなら」という否定の形なので、ここでは肯定に直してある。
`name` と `namespace` は record の `attributeName` / `attributeNamespace` である。

attributeFilter は **存在するだけで** 絞り込みになる。
存在して、かつ「name を含まない」か「namespace が非 null」なら record を積まない。
namespace 付きの attribute は filter では拾えない、というのが仕様の読み方である。
-/
def Registration.interestedIn (r : Registration) (target : NodeId) (type : RecordType)
    (name : Option String) («namespace» : Option String) : Bool :=
  (r.node == target || r.subtree) &&
    (match type with
     | .attributes =>
       r.attributes &&
         (match r.attributeFilter with
          | none => true
          | some f =>
            (match name with
             | none => false
             | some nm => f.contains nm) && «namespace».isNone)
     | .characterData => r.characterData
     | .childList => r.childList)

/-- "queue a mutation record" step 2.3.2。observer を初出順に集め、oldValue を上書きする。 -/
def addInterested (acc : List (Nat × Option String)) (mo : Nat) (ov : Option String) :
    List (Nat × Option String) :=
  if acc.any (fun p => p.1 == mo) then
    match ov with
    | none => acc
    | some _ => acc.map fun p => if p.1 == mo then (p.1, ov) else p
  else
    acc ++ [(mo, ov)]

/--
"queue a mutation record" の step 1-2。

target の inclusive ancestor を下から上へ、各 node の registered observer list を
list の順に見て、条件を満たす observer を初出順に集める。
第二成分は record に載せる oldValue で（step 2.3.3）、
characterData かつ `characterDataOldValue`、または attributes かつ `attributeOldValue`
のときだけ非 `none` になる。
-/
def interestedObservers (s : DOMState) (rec : MutationRecord) (oldValue : Option String) :
    List (Nat × Option String) :=
  let nodes := rec.target :: ancestors s.tree rec.target
  nodes.foldl (fun acc n =>
    (s.registrations.filter fun r => r.node == n).foldl (fun acc r =>
      if r.interestedIn rec.target rec.type rec.attributeName rec.attributeNamespace then
        addInterested acc r.observer
          (if (rec.type == .characterData && r.characterDataOldValue)
              || (rec.type == .attributes && r.attributeOldValue) then oldValue else none)
      else acc) acc) []

/-! ## microtask -/

/-- DOM Standard §4.3 "queue a mutation observer microtask"。 -/
def queueMutationObserverMicrotask (s : DOMState) : DOMState :=
  if s.microtaskQueued then s else { s with microtaskQueued := true }

/-- pending mutation observers に足す。仕様の set なので重複は持たない。 -/
def addPendingObserver (s : DOMState) (mo : Nat) : DOMState :=
  if s.pendingObservers.contains mo then s
  else { s with pendingObservers := s.pendingObservers ++ [mo] }

/-! ## record を積む -/

/-- observer `mo` の record queue の末尾に `rec` を足す。 -/
def enqueueRecord (obs : List ObserverState) (mo : Nat) (rec : MutationRecord) :
    List ObserverState :=
  match obs[mo]? with
  | none => obs
  | some o => obs.set mo { o with records := o.records ++ [rec] }

/--
DOM Standard §4.3.4 "queue a mutation record"。

interested observers が空なら step 4 で返る。そうでなければ step 5 が record を積んで
pending mutation observers に足し、step 6 が microtask を予約する。
-/
def queueMutationRecord (s : DOMState) (rec : MutationRecord) (oldValue : Option String) :
    DOMState :=
  let interested := interestedObservers s rec oldValue
  if interested.isEmpty then s
  else
    let s₁ := { s with
        observers := interested.foldl
          (fun obs p => enqueueRecord obs p.1 { rec with oldValue := p.2 }) s.observers }
    let s₂ := interested.foldl (fun st p => addPendingObserver st p.1) s₁
    queueMutationObserverMicrotask s₂

/-- `queueMutationRecord` の本体を `let` を開いた形で書いたもの。 -/
theorem queueMutationRecord_eq (s : DOMState) (rec : MutationRecord) (ov : Option String) :
    queueMutationRecord s rec ov =
      if (interestedObservers s rec ov).isEmpty then s
      else queueMutationObserverMicrotask ((interestedObservers s rec ov).foldl
        (fun st p => addPendingObserver st p.1)
        { s with
            observers := (interestedObservers s rec ov).foldl
              (fun obs p => enqueueRecord obs p.1 { rec with oldValue := p.2 }) s.observers }) :=
  rfl

/--
DOM Standard §4.3.4 "queue a tree mutation record"。

仕様は addedNodes か removedNodes の一方が空でないことを assert するので、
両方空なら何もしない。
-/
def queueTreeMutationRecord (s : DOMState) (target : NodeId)
    (addedNodes removedNodes : List NodeId)
    (previousSibling nextSibling : Option NodeId) : DOMState :=
  if addedNodes.isEmpty && removedNodes.isEmpty then s
  else
    queueMutationRecord s
      { type := .childList, target := target, addedNodes := addedNodes,
        removedNodes := removedNodes, previousSibling := previousSibling,
        nextSibling := nextSibling } none

/-- DOM Standard §4.10 replace data step 4 の characterData record。 -/
def queueCharacterDataRecord (s : DOMState) (target : NodeId) (oldValue : String) : DOMState :=
  queueMutationRecord s { type := .characterData, target := target } (some oldValue)

/-! ## transient registered observer -/

/--
transient を足す一歩。observer の node list は伸びるだけで、その observer の node list には node が入る。

model の node list（`ObserverState.nodeList`）は、本文の node list と transient node set を合わせたものである。
"add transient registered observers" step 1.6 はここで transient node set に node を足す。
-/
def transientStep (node : NodeId) (obs : List ObserverState) (r : Registration) : List ObserverState :=
  match obs[r.observer]? with
  | none => obs
  | some o =>
    if o.nodeList.contains node then obs
    else obs.set r.observer { o with nodeList := o.nodeList ++ [node] }

/--
"add transient registered observers" step 1.3 の source。

transient registered observer なら その source、そうでなければ registered 自身である。
model は source を registration の node で表す（`Registration.source` の doc comment）。
-/
def Registration.sourceNode (r : Registration) : Option NodeId :=
  if r.transient then r.source else some r.node

/-- step 1.5 で足す transient registered observer。options は registered のものを写す。 -/
def Registration.transientOn (r : Registration) (node : NodeId) : Registration :=
  { r with node := node, transient := true, source := r.sourceNode }

/-- step 1.4：`regs` に、source が `r` の source である transient registered observer があるか。 -/
def hasTransientFrom (regs : List Registration) (r : Registration) : Bool :=
  regs.any fun t => t.transient && t.observer == r.observer && t.source == r.sourceNode

/--
step 1.1-1.5 を一つの registered について行う。

`existing` は node の元の registered observer list、`acc` はここまでに足した transient である。
-/
def collectTransient (node : NodeId) (existing acc : List Registration) (r : Registration) :
    List Registration :=
  if r.subtree && !hasTransientFrom (existing ++ acc) r then acc ++ [r.transientOn node] else acc

/--
step 1 の繰り返しで `node` に足す transient registered observer の列。

`parent` の inclusive ancestor を下から上へ、各 node の registered observer list を list の順に回る。
-/
def newTransients (s : DOMState) (node parent : NodeId) : List Registration :=
  ((parent :: ancestors s.tree parent).flatMap fun n =>
      s.registrations.filter fun r => r.node == n).foldl
    (collectTransient node (s.registrations.filter fun r => r.node == node)) []

/-- step 1.7-1.8：足した transient の observer を pending にし、microtask を予約する。 -/
def pendTransient (s : DOMState) (r : Registration) : DOMState :=
  queueMutationObserverMicrotask (addPendingObserver s r.observer)

/--
DOM Standard §4.3 "add transient registered observers"。remove step 15 と move step 17 が呼ぶ。

`parent` の inclusive ancestor に subtree 付きで登録されている registered observer ごとに、
`node` に transient registered observer を足す。
これがあると、subtree observer は外された部分木の中の変更も次の notify まで見続ける。

registered が transient なら、足す transient の source はその source である（step 1.3）。
すでに外れた部分木の中でさらに removal が起きても、追跡は元の registered observer から続く。
同じ source の transient が `node` にあれば足さない（step 1.4）。

足した transient の observer は pending になる（step 1.7）。record が無くても、次の notify で
transient が外れるためである。
-/
def addTransientObservers (s : DOMState) (node parent : NodeId) : DOMState :=
  let added := newTransients s node parent
  let s₁ := { s with
      registrations := s.registrations ++ added
      -- step 1.6。transient を置いた node を、その observer の transient node set（model では node list）に足す。
      observers := added.foldl (transientStep node) s.observers }
  added.foldl pendTransient s₁


/-- step 1.7-1.8 の畳み込みは、`f` が見る成分を変えない。 -/
theorem foldl_pendTransient_frame {β : Type} (f : DOMState → β)
    (hf : ∀ st r, f (pendTransient st r) = f st) :
    ∀ (l : List Registration) (st : DOMState), f (l.foldl pendTransient st) = f st
  | [], _ => rfl
  | r :: l, st => by
    rw [List.foldl_cons, foldl_pendTransient_frame f hf l, hf]

/-- `addTransientObservers` の、step 1.7-1.8 の前の状態。 -/
theorem addTransientObservers_eq (s : DOMState) (node parent : NodeId) :
    addTransientObservers s node parent =
      (newTransients s node parent).foldl pendTransient
        { s with
            registrations := s.registrations ++ newTransients s node parent
            observers := (newTransients s node parent).foldl (transientStep node) s.observers } :=
  rfl

/-- `addTransientObservers` は、`f` が見る成分のうち registration と observer 列以外を変えない。 -/
theorem addTransientObservers_frame {β : Type} (f : DOMState → β)
    (hf : ∀ st r, f (pendTransient st r) = f st)
    (hs : ∀ (st : DOMState) regs obs,
      f { st with registrations := regs, observers := obs } = f st)
    (s : DOMState) (node parent : NodeId) : f (addTransientObservers s node parent) = f s := by
  rw [addTransientObservers_eq, foldl_pendTransient_frame f hf, hs]

/-! ## walker・listener・detach された `Attr` には触れない -/

/--
record を積む段はどれも三成分を持ち越す。`Untouched`（`Dom/Basic/State.lean`）は
これを束ねたもので、関係意味論が frame 条件として持つ。
-/
@[simp] theorem queueMutationObserverMicrotask_walkers (s : DOMState) :
    (queueMutationObserverMicrotask s).walkers = s.walkers := by
  unfold queueMutationObserverMicrotask; split <;> rfl

@[simp] theorem addPendingObserver_walkers (s : DOMState) (mo : Nat) :
    (addPendingObserver s mo).walkers = s.walkers := by
  unfold addPendingObserver; split <;> rfl

theorem foldl_addPendingObserver_walkers :
    ∀ (l : List (Nat × Option String)) (s : DOMState),
      (l.foldl (fun st p => addPendingObserver st p.1) s).walkers = s.walkers
  | [], _ => rfl
  | x :: xs, s => by
    show (xs.foldl _ (addPendingObserver s x.1)).walkers = s.walkers
    rw [foldl_addPendingObserver_walkers xs, addPendingObserver_walkers]

@[simp] theorem queueMutationRecord_walkers (s : DOMState) (rec : MutationRecord)
    (ov : Option String) : (queueMutationRecord s rec ov).walkers = s.walkers := by
  rw [queueMutationRecord_eq]
  split
  · rfl
  · rw [queueMutationObserverMicrotask_walkers, foldl_addPendingObserver_walkers]

@[simp] theorem queueTreeMutationRecord_walkers (s : DOMState) (t : NodeId)
    (a r : List NodeId) (p n : Option NodeId) :
    (queueTreeMutationRecord s t a r p n).walkers = s.walkers := by
  unfold queueTreeMutationRecord
  split
  · rfl
  · simp

@[simp] theorem queueCharacterDataRecord_walkers (s : DOMState) (t : NodeId) (v : String) :
    (queueCharacterDataRecord s t v).walkers = s.walkers := by
  unfold queueCharacterDataRecord; simp

@[simp] theorem addTransientObservers_walkers (s : DOMState) (n p : NodeId) :
    (addTransientObservers s n p).walkers = s.walkers :=
  addTransientObservers_frame (·.walkers) (fun st r => by simp [pendTransient]) (fun _ _ _ => rfl) s n p

@[simp] theorem queueMutationObserverMicrotask_listeners (s : DOMState) :
    (queueMutationObserverMicrotask s).listeners = s.listeners := by
  unfold queueMutationObserverMicrotask; split <;> rfl

@[simp] theorem addPendingObserver_listeners (s : DOMState) (mo : Nat) :
    (addPendingObserver s mo).listeners = s.listeners := by
  unfold addPendingObserver; split <;> rfl

theorem foldl_addPendingObserver_listeners :
    ∀ (l : List (Nat × Option String)) (s : DOMState),
      (l.foldl (fun st p => addPendingObserver st p.1) s).listeners = s.listeners
  | [], _ => rfl
  | x :: xs, s => by
    show (xs.foldl _ (addPendingObserver s x.1)).listeners = s.listeners
    rw [foldl_addPendingObserver_listeners xs, addPendingObserver_listeners]

@[simp] theorem queueMutationRecord_listeners (s : DOMState) (rec : MutationRecord)
    (ov : Option String) : (queueMutationRecord s rec ov).listeners = s.listeners := by
  rw [queueMutationRecord_eq]
  split
  · rfl
  · rw [queueMutationObserverMicrotask_listeners, foldl_addPendingObserver_listeners]

@[simp] theorem queueTreeMutationRecord_listeners (s : DOMState) (t : NodeId)
    (a r : List NodeId) (p n : Option NodeId) :
    (queueTreeMutationRecord s t a r p n).listeners = s.listeners := by
  unfold queueTreeMutationRecord
  split
  · rfl
  · simp

@[simp] theorem queueCharacterDataRecord_listeners (s : DOMState) (t : NodeId) (v : String) :
    (queueCharacterDataRecord s t v).listeners = s.listeners := by
  unfold queueCharacterDataRecord; simp

@[simp] theorem addTransientObservers_listeners (s : DOMState) (n p : NodeId) :
    (addTransientObservers s n p).listeners = s.listeners :=
  addTransientObservers_frame (·.listeners) (fun st r => by simp [pendTransient]) (fun _ _ _ => rfl) s n p

@[simp] theorem queueMutationObserverMicrotask_detachedAttrs (s : DOMState) :
    (queueMutationObserverMicrotask s).detachedAttrs = s.detachedAttrs := by
  unfold queueMutationObserverMicrotask; split <;> rfl

@[simp] theorem addPendingObserver_detachedAttrs (s : DOMState) (mo : Nat) :
    (addPendingObserver s mo).detachedAttrs = s.detachedAttrs := by
  unfold addPendingObserver; split <;> rfl

theorem foldl_addPendingObserver_detachedAttrs :
    ∀ (l : List (Nat × Option String)) (s : DOMState),
      (l.foldl (fun st p => addPendingObserver st p.1) s).detachedAttrs = s.detachedAttrs
  | [], _ => rfl
  | x :: xs, s => by
    show (xs.foldl _ (addPendingObserver s x.1)).detachedAttrs = s.detachedAttrs
    rw [foldl_addPendingObserver_detachedAttrs xs, addPendingObserver_detachedAttrs]

@[simp] theorem queueMutationRecord_detachedAttrs (s : DOMState) (rec : MutationRecord)
    (ov : Option String) : (queueMutationRecord s rec ov).detachedAttrs = s.detachedAttrs := by
  rw [queueMutationRecord_eq]
  split
  · rfl
  · rw [queueMutationObserverMicrotask_detachedAttrs, foldl_addPendingObserver_detachedAttrs]

@[simp] theorem queueTreeMutationRecord_detachedAttrs (s : DOMState) (t : NodeId)
    (a r : List NodeId) (p n : Option NodeId) :
    (queueTreeMutationRecord s t a r p n).detachedAttrs = s.detachedAttrs := by
  unfold queueTreeMutationRecord
  split
  · rfl
  · simp

@[simp] theorem queueCharacterDataRecord_detachedAttrs (s : DOMState) (t : NodeId) (v : String) :
    (queueCharacterDataRecord s t v).detachedAttrs = s.detachedAttrs := by
  unfold queueCharacterDataRecord; simp

@[simp] theorem addTransientObservers_detachedAttrs (s : DOMState) (n p : NodeId) :
    (addTransientObservers s n p).detachedAttrs = s.detachedAttrs :=
  addTransientObservers_frame (·.detachedAttrs) (fun st r => by simp [pendTransient]) (fun _ _ _ => rfl) s n p

theorem untouched_queueMutationRecord (s : DOMState) (rec : MutationRecord)
    (oldValue : Option String) : Untouched s (queueMutationRecord s rec oldValue) :=
  ⟨by simp, by simp, by simp⟩

theorem untouched_queueTreeMutationRecord (s : DOMState) (target : NodeId)
    (added removed : List NodeId) (prev next : Option NodeId) :
    Untouched s (queueTreeMutationRecord s target added removed prev next) :=
  ⟨by simp, by simp, by simp⟩

theorem untouched_queueCharacterDataRecord (s : DOMState) (target : NodeId) (oldValue : String) :
    Untouched s (queueCharacterDataRecord s target oldValue) := ⟨by simp, by simp, by simp⟩

theorem untouched_addTransientObservers (s : DOMState) (node parent : NodeId) :
    Untouched s (addTransientObservers s node parent) := ⟨by simp, by simp, by simp⟩

/-! ## microtask と pending は他の成分を変えない -/

@[simp] theorem queueMutationObserverMicrotask_tree (s : DOMState) :
    (queueMutationObserverMicrotask s).tree = s.tree := by
  unfold queueMutationObserverMicrotask; split <;> rfl

@[simp] theorem queueMutationObserverMicrotask_ranges (s : DOMState) :
    (queueMutationObserverMicrotask s).ranges = s.ranges := by
  unfold queueMutationObserverMicrotask; split <;> rfl

@[simp] theorem queueMutationObserverMicrotask_iterators (s : DOMState) :
    (queueMutationObserverMicrotask s).iterators = s.iterators := by
  unfold queueMutationObserverMicrotask; split <;> rfl

@[simp] theorem queueMutationObserverMicrotask_registrations (s : DOMState) :
    (queueMutationObserverMicrotask s).registrations = s.registrations := by
  unfold queueMutationObserverMicrotask; split <;> rfl

@[simp] theorem queueMutationObserverMicrotask_observers (s : DOMState) :
    (queueMutationObserverMicrotask s).observers = s.observers := by
  unfold queueMutationObserverMicrotask; split <;> rfl

@[simp] theorem addPendingObserver_tree (s : DOMState) (mo : Nat) :
    (addPendingObserver s mo).tree = s.tree := by
  unfold addPendingObserver; split <;> rfl

@[simp] theorem addPendingObserver_ranges (s : DOMState) (mo : Nat) :
    (addPendingObserver s mo).ranges = s.ranges := by
  unfold addPendingObserver; split <;> rfl

@[simp] theorem addPendingObserver_iterators (s : DOMState) (mo : Nat) :
    (addPendingObserver s mo).iterators = s.iterators := by
  unfold addPendingObserver; split <;> rfl

@[simp] theorem addPendingObserver_registrations (s : DOMState) (mo : Nat) :
    (addPendingObserver s mo).registrations = s.registrations := by
  unfold addPendingObserver; split <;> rfl

@[simp] theorem addPendingObserver_observers (s : DOMState) (mo : Nat) :
    (addPendingObserver s mo).observers = s.observers := by
  unfold addPendingObserver; split <;> rfl

/-- pending observers を畳み込んでも木と live object は変わらない。 -/
theorem foldl_addPendingObserver_tree :
    ∀ (l : List (Nat × Option String)) (s : DOMState),
      (l.foldl (fun st p => addPendingObserver st p.1) s).tree = s.tree
  | [], _ => rfl
  | x :: xs, s => by
    show (xs.foldl _ (addPendingObserver s x.1)).tree = s.tree
    rw [foldl_addPendingObserver_tree xs, addPendingObserver_tree]

theorem foldl_addPendingObserver_ranges :
    ∀ (l : List (Nat × Option String)) (s : DOMState),
      (l.foldl (fun st p => addPendingObserver st p.1) s).ranges = s.ranges
  | [], _ => rfl
  | x :: xs, s => by
    show (xs.foldl _ (addPendingObserver s x.1)).ranges = s.ranges
    rw [foldl_addPendingObserver_ranges xs, addPendingObserver_ranges]

theorem foldl_addPendingObserver_iterators :
    ∀ (l : List (Nat × Option String)) (s : DOMState),
      (l.foldl (fun st p => addPendingObserver st p.1) s).iterators = s.iterators
  | [], _ => rfl
  | x :: xs, s => by
    show (xs.foldl _ (addPendingObserver s x.1)).iterators = s.iterators
    rw [foldl_addPendingObserver_iterators xs, addPendingObserver_iterators]

theorem foldl_addPendingObserver_registrations :
    ∀ (l : List (Nat × Option String)) (s : DOMState),
      (l.foldl (fun st p => addPendingObserver st p.1) s).registrations = s.registrations
  | [], _ => rfl
  | x :: xs, s => by
    show (xs.foldl _ (addPendingObserver s x.1)).registrations = s.registrations
    rw [foldl_addPendingObserver_registrations xs, addPendingObserver_registrations]

theorem foldl_addPendingObserver_observers :
    ∀ (l : List (Nat × Option String)) (s : DOMState),
      (l.foldl (fun st p => addPendingObserver st p.1) s).observers = s.observers
  | [], _ => rfl
  | x :: xs, s => by
    show (xs.foldl _ (addPendingObserver s x.1)).observers = s.observers
    rw [foldl_addPendingObserver_observers xs, addPendingObserver_observers]

/-! ## 木を変えないこと -/

@[simp] theorem queueMutationRecord_tree (s : DOMState) (rec : MutationRecord)
    (ov : Option String) : (queueMutationRecord s rec ov).tree = s.tree := by
  rw [queueMutationRecord_eq]
  split
  · rfl
  · rw [queueMutationObserverMicrotask_tree, foldl_addPendingObserver_tree]

@[simp] theorem queueMutationRecord_ranges (s : DOMState) (rec : MutationRecord)
    (ov : Option String) : (queueMutationRecord s rec ov).ranges = s.ranges := by
  rw [queueMutationRecord_eq]
  split
  · rfl
  · rw [queueMutationObserverMicrotask_ranges, foldl_addPendingObserver_ranges]

@[simp] theorem queueMutationRecord_iterators (s : DOMState) (rec : MutationRecord)
    (ov : Option String) : (queueMutationRecord s rec ov).iterators = s.iterators := by
  rw [queueMutationRecord_eq]
  split
  · rfl
  · rw [queueMutationObserverMicrotask_iterators, foldl_addPendingObserver_iterators]

@[simp] theorem queueMutationRecord_registrations (s : DOMState) (rec : MutationRecord)
    (ov : Option String) : (queueMutationRecord s rec ov).registrations = s.registrations := by
  rw [queueMutationRecord_eq]
  split
  · rfl
  · rw [queueMutationObserverMicrotask_registrations, foldl_addPendingObserver_registrations]

@[simp] theorem queueTreeMutationRecord_tree (s : DOMState) (t : NodeId)
    (a r : List NodeId) (p n : Option NodeId) :
    (queueTreeMutationRecord s t a r p n).tree = s.tree := by
  unfold queueTreeMutationRecord
  split
  · rfl
  · simp

@[simp] theorem queueTreeMutationRecord_ranges (s : DOMState) (t : NodeId)
    (a r : List NodeId) (p n : Option NodeId) :
    (queueTreeMutationRecord s t a r p n).ranges = s.ranges := by
  unfold queueTreeMutationRecord
  split
  · rfl
  · simp

@[simp] theorem queueTreeMutationRecord_iterators (s : DOMState) (t : NodeId)
    (a r : List NodeId) (p n : Option NodeId) :
    (queueTreeMutationRecord s t a r p n).iterators = s.iterators := by
  unfold queueTreeMutationRecord
  split
  · rfl
  · simp

@[simp] theorem queueCharacterDataRecord_tree (s : DOMState) (t : NodeId) (v : String) :
    (queueCharacterDataRecord s t v).tree = s.tree := by
  unfold queueCharacterDataRecord; simp

@[simp] theorem queueCharacterDataRecord_ranges (s : DOMState) (t : NodeId) (v : String) :
    (queueCharacterDataRecord s t v).ranges = s.ranges := by
  unfold queueCharacterDataRecord; simp

@[simp] theorem queueCharacterDataRecord_iterators (s : DOMState) (t : NodeId) (v : String) :
    (queueCharacterDataRecord s t v).iterators = s.iterators := by
  unfold queueCharacterDataRecord; simp

@[simp] theorem addTransientObservers_tree (s : DOMState) (n p : NodeId) :
    (addTransientObservers s n p).tree = s.tree :=
  addTransientObservers_frame (·.tree) (fun st r => by simp [pendTransient]) (fun _ _ _ => rfl) s n p

@[simp] theorem addTransientObservers_ranges (s : DOMState) (n p : NodeId) :
    (addTransientObservers s n p).ranges = s.ranges :=
  addTransientObservers_frame (·.ranges) (fun st r => by simp [pendTransient]) (fun _ _ _ => rfl) s n p

@[simp] theorem addTransientObservers_iterators (s : DOMState) (n p : NodeId) :
    (addTransientObservers s n p).iterators = s.iterators :=
  addTransientObservers_frame (·.iterators) (fun st r => by simp [pendTransient]) (fun _ _ _ => rfl) s n p

theorem transientStep_grow (node : NodeId) (obs : List ObserverState) (r : Registration)
    {i : Nat} {o : ObserverState} (h : obs[i]? = some o) :
    ∃ o', (transientStep node obs r)[i]? = some o' ∧ ∀ x ∈ o.nodeList, x ∈ o'.nodeList := by
  unfold transientStep
  split
  · exact ⟨o, h, fun _ hx => hx⟩
  · next o₀ h₀ =>
    split
    · exact ⟨o, h, fun _ hx => hx⟩
    · rw [List.getElem?_set]
      by_cases hk : r.observer = i
      · subst hk
        rw [h₀] at h
        cases h
        have hlt := (List.getElem?_eq_some_iff.mp h₀).1
        refine ⟨{ o with nodeList := o.nodeList ++ [node] }, by simp [hlt], fun x hx => ?_⟩
        simp [hx]
      · exact ⟨o, by simp [hk, h], fun _ hx => hx⟩

theorem transientStep_listed (node : NodeId) (obs : List ObserverState) (r : Registration)
    (hlt : r.observer < obs.length) :
    ∃ o', (transientStep node obs r)[r.observer]? = some o' ∧ node ∈ o'.nodeList := by
  unfold transientStep
  obtain ⟨o, ho⟩ : ∃ o, obs[r.observer]? = some o := ⟨_, List.getElem?_eq_getElem hlt⟩
  rw [ho]
  simp only []
  split
  · next hc => exact ⟨o, ho, by simpa using hc⟩
  · exact ⟨{ o with nodeList := o.nodeList ++ [node] }, by simp [hlt], by simp⟩

theorem transientStep_length (node : NodeId) (obs : List ObserverState) (r : Registration) :
    (transientStep node obs r).length = obs.length := by
  unfold transientStep
  split
  · rfl
  · split <;> simp

theorem foldl_transientStep_grow (node : NodeId) :
    ∀ (l : List Registration) (obs : List ObserverState) {i : Nat} {o : ObserverState},
      obs[i]? = some o →
      ∃ o', (l.foldl (transientStep node) obs)[i]? = some o' ∧ ∀ x ∈ o.nodeList, x ∈ o'.nodeList
  | [], obs, i, o, h => ⟨o, h, fun _ hx => hx⟩
  | r :: l, obs, i, o, h => by
    obtain ⟨o₁, h₁, hs₁⟩ := transientStep_grow node obs r h
    obtain ⟨o₂, h₂, hs₂⟩ := foldl_transientStep_grow node l (transientStep node obs r) h₁
    exact ⟨o₂, h₂, fun x hx => hs₂ x (hs₁ x hx)⟩

theorem foldl_transientStep_length (node : NodeId) :
    ∀ (l : List Registration) (obs : List ObserverState),
      (l.foldl (transientStep node) obs).length = obs.length
  | [], _ => rfl
  | r :: l, obs => by
    show (l.foldl _ (transientStep node obs r)).length = _
    rw [foldl_transientStep_length node l, transientStep_length]

theorem foldl_transientStep_listed (node : NodeId) :
    ∀ (l : List Registration) (obs : List ObserverState) (r : Registration), r ∈ l →
      r.observer < obs.length →
      ∃ o', (l.foldl (transientStep node) obs)[r.observer]? = some o' ∧ node ∈ o'.nodeList
  | [], _, _, h, _ => by cases h
  | x :: l, obs, r, h, hlt => by
    rcases List.mem_cons.mp h with rfl | hm
    · obtain ⟨o₁, h₁, hn₁⟩ := transientStep_listed node obs r hlt
      obtain ⟨o₂, h₂, hs₂⟩ := foldl_transientStep_grow node l (transientStep node obs r) h₁
      exact ⟨o₂, h₂, hs₂ node hn₁⟩
    · exact foldl_transientStep_listed node l (transientStep node obs x) r hm
        (by rw [transientStep_length]; exact hlt)

/-- `addTransientObservers` の observer 列は、元の列に `transientStep` を当てたもの。 -/
theorem addTransientObservers_observers (s : DOMState) (n p : NodeId) :
    (addTransientObservers s n p).observers =
      (newTransients s n p).foldl (transientStep n) s.observers := by
  rw [addTransientObservers_eq,
    foldl_pendTransient_frame (·.observers) (fun st r => by simp [pendTransient])]

/-- `addTransientObservers` の registration は、元の列に step 1.5 の transient を続けたもの。 -/
theorem addTransientObservers_registrations (s : DOMState) (n p : NodeId) :
    (addTransientObservers s n p).registrations = s.registrations ++ newTransients s n p := by
  rw [addTransientObservers_eq,
    foldl_pendTransient_frame (·.registrations) (fun st r => by simp [pendTransient])]

@[simp] theorem addTransientObservers_observers_length (s : DOMState) (n p : NodeId) :
    (addTransientObservers s n p).observers.length = s.observers.length := by
  rw [addTransientObservers_observers]
  exact foldl_transientStep_length _ _ _

/-- step 1.7-1.8 の畳み込みの microtask。transient を一つでも足せば予約される。 -/
theorem microtaskQueued_foldl_pendTransient :
    ∀ (l : List Registration) (st : DOMState),
      (l.foldl pendTransient st).microtaskQueued = (st.microtaskQueued || !l.isEmpty)
  | [], st => by simp
  | r :: l, st => by
    rw [List.foldl_cons, microtaskQueued_foldl_pendTransient l]
    unfold pendTransient queueMutationObserverMicrotask addPendingObserver
    split <;> split <;> simp_all

theorem addTransientObservers_microtaskQueued (s : DOMState) (n p : NodeId) :
    (addTransientObservers s n p).microtaskQueued =
      (s.microtaskQueued || !(newTransients s n p).isEmpty) := by
  rw [addTransientObservers_eq, microtaskQueued_foldl_pendTransient]

@[simp] theorem queueTreeMutationRecord_registrations (s : DOMState) (t : NodeId)
    (a r : List NodeId) (p n : Option NodeId) :
    (queueTreeMutationRecord s t a r p n).registrations = s.registrations := by
  unfold queueTreeMutationRecord
  split
  · rfl
  · simp

@[simp] theorem enqueueRecord_length (obs : List ObserverState) (mo : Nat)
    (rec : MutationRecord) : (enqueueRecord obs mo rec).length = obs.length := by
  unfold enqueueRecord
  split
  · rfl
  · simp

theorem foldl_enqueue_length :
    ∀ (l : List (Nat × Option String)) (obs : List ObserverState) (rec : MutationRecord),
      (l.foldl (fun o p => enqueueRecord o p.1 { rec with oldValue := p.2 }) obs).length
        = obs.length
  | [], _, _ => rfl
  | x :: xs, obs, rec => by
    show (xs.foldl _ (enqueueRecord obs x.1 _)).length = obs.length
    rw [foldl_enqueue_length xs, enqueueRecord_length]

@[simp] theorem queueMutationRecord_observers_length (s : DOMState) (rec : MutationRecord)
    (ov : Option String) :
    (queueMutationRecord s rec ov).observers.length = s.observers.length := by
  rw [queueMutationRecord_eq]
  split
  · rfl
  · rw [queueMutationObserverMicrotask_observers, foldl_addPendingObserver_observers]
    exact foldl_enqueue_length _ _ _

@[simp] theorem queueTreeMutationRecord_observers_length (s : DOMState) (t : NodeId)
    (a r : List NodeId) (p n : Option NodeId) :
    (queueTreeMutationRecord s t a r p n).observers.length = s.observers.length := by
  unfold queueTreeMutationRecord
  split
  · rfl
  · exact queueMutationRecord_observers_length ..

@[simp] theorem queueCharacterDataRecord_registrations (s : DOMState) (t : NodeId) (v : String) :
    (queueCharacterDataRecord s t v).registrations = s.registrations := by
  unfold queueCharacterDataRecord; simp

@[simp] theorem queueCharacterDataRecord_observers_length (s : DOMState) (t : NodeId)
    (v : String) :
    (queueCharacterDataRecord s t v).observers.length = s.observers.length :=
  queueMutationRecord_observers_length ..

/-! ## record を積んでも node list は変わらない -/

theorem enqueueRecord_nodeLists (obs : List ObserverState) (mo : Nat) (rec : MutationRecord) :
    (enqueueRecord obs mo rec).map (·.nodeList) = obs.map (·.nodeList) := by
  unfold enqueueRecord
  split
  · rfl
  · next o ho =>
    rw [List.map_set]
    apply List.ext_getElem?
    intro k
    rw [List.getElem?_set]
    by_cases hk : mo = k
    · subst hk
      obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.mp ho
      simp [hlt, he]
    · simp [hk]

theorem foldl_enqueue_nodeLists :
    ∀ (l : List (Nat × Option String)) (obs : List ObserverState) (rec : MutationRecord),
      (l.foldl (fun o p => enqueueRecord o p.1 { rec with oldValue := p.2 }) obs).map (·.nodeList)
        = obs.map (·.nodeList)
  | [], _, _ => rfl
  | x :: xs, obs, rec => by
    show (xs.foldl _ (enqueueRecord obs x.1 _)).map _ = _
    rw [foldl_enqueue_nodeLists xs, enqueueRecord_nodeLists]

@[simp] theorem queueMutationRecord_nodeLists (s : DOMState) (rec : MutationRecord)
    (ov : Option String) :
    (queueMutationRecord s rec ov).observers.map (·.nodeList) = s.observers.map (·.nodeList) := by
  rw [queueMutationRecord_eq]
  split
  · rfl
  · rw [queueMutationObserverMicrotask_observers, foldl_addPendingObserver_observers]
    exact foldl_enqueue_nodeLists _ _ _

@[simp] theorem queueTreeMutationRecord_nodeLists (s : DOMState) (t : NodeId)
    (a r : List NodeId) (p n : Option NodeId) :
    (queueTreeMutationRecord s t a r p n).observers.map (·.nodeList) =
      s.observers.map (·.nodeList) := by
  unfold queueTreeMutationRecord
  split
  · rfl
  · exact queueMutationRecord_nodeLists ..

@[simp] theorem queueCharacterDataRecord_nodeLists (s : DOMState) (t : NodeId) (v : String) :
    (queueCharacterDataRecord s t v).observers.map (·.nodeList) = s.observers.map (·.nodeList) :=
  queueMutationRecord_nodeLists ..

/-- step 1 の畳み込みが足すのは、列の中の subtree 付きの registered から作った transient だけである。 -/
theorem mem_foldl_collectTransient (node : NodeId) (ex : List Registration) :
    ∀ (l acc : List Registration) {t : Registration}, t ∈ l.foldl (collectTransient node ex) acc →
      t ∈ acc ∨ ∃ r ∈ l, r.subtree = true ∧ t = r.transientOn node
  | [], acc, t, h => Or.inl h
  | r :: l, acc, t, h => by
    rw [List.foldl_cons] at h
    rcases mem_foldl_collectTransient node ex l _ h with h | ⟨r', hr', hs, he⟩
    · unfold collectTransient at h
      split at h
      · next hc =>
        rcases List.mem_append.mp h with h | h
        · exact Or.inl h
        · refine Or.inr ⟨r, List.mem_cons_self .., ?_, List.mem_singleton.mp h⟩
          simp only [Bool.and_eq_true] at hc
          exact hc.1
      · exact Or.inl h
    · exact Or.inr ⟨r', List.mem_cons_of_mem _ hr', hs, he⟩

/-- `newTransients` の要素は、`parent` の inclusive ancestor の上の subtree 付きの registered から作る。 -/
theorem mem_newTransients {s : DOMState} {node parent : NodeId} {t : Registration}
    (h : t ∈ newTransients s node parent) :
    ∃ r ∈ s.registrations, r.node ∈ parent :: ancestors s.tree parent ∧ r.subtree = true ∧
      t = r.transientOn node := by
  rcases mem_foldl_collectTransient node _ _ [] h with h | ⟨r, hr, hs, he⟩
  · cases h
  · obtain ⟨m, hm, hr⟩ := List.mem_flatMap.mp hr
    obtain ⟨hr, hn⟩ := List.mem_filter.mp hr
    have hn : r.node = m := by simpa using hn
    exact ⟨r, hr, hn ▸ hm, hs, he⟩

/-- `newTransients` の要素はどれも `node` の上の transient である。 -/
theorem node_of_mem_newTransients {s : DOMState} {node parent : NodeId} {t : Registration}
    (h : t ∈ newTransients s node parent) : t.node = node := by
  obtain ⟨r, -, -, -, rfl⟩ := mem_newTransients h
  rfl

/-- transient registration の observer index は、元の registration から受け継ぐ。 -/
theorem addTransientObservers_observer_lt (s : DOMState) (n p : NodeId) {r : Registration}
    (h : r ∈ (addTransientObservers s n p).registrations)
    (hall : ∀ r' ∈ s.registrations, r'.observer < s.observers.length) :
    r.observer < s.observers.length := by
  rw [addTransientObservers_registrations] at h
  rcases List.mem_append.mp h with h | h
  · exact hall r h
  · obtain ⟨r₀, hr₀, -, -, rfl⟩ := mem_newTransients h
    exact hall r₀ hr₀

end Dom
