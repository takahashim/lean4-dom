import Dom.Basic.State
import Dom.Basic.Order

/-!
# MutationObserver の record

DOM Standard §4.3.4 の "queue a mutation record" と "queue a tree mutation record"、
および §4.2.3 remove step 20 の transient registered observer を定義する。

配送そのもの（"notify mutation observers"）は `Dom/Observer/Deliver.lean` にある。
ここは record を積むところまでで、transient registered observer を消すのは配送の側である。
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

step 4 が record を積んで pending mutation observers に足し、
step 5 が microtask を予約する。step 5 は interested observers が空でも走る。
-/
def queueMutationRecord (s : DOMState) (rec : MutationRecord) (oldValue : Option String) :
    DOMState :=
  let interested := interestedObservers s rec oldValue
  let s₁ := { s with
      observers := interested.foldl
        (fun obs p => enqueueRecord obs p.1 { rec with oldValue := p.2 }) s.observers }
  let s₂ := interested.foldl (fun st p => addPendingObserver st p.1) s₁
  queueMutationObserverMicrotask s₂

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
DOM Standard §4.2.3 remove step 20。

`parent` の inclusive ancestor に subtree 付きで登録されている observer を、
取り除く `node` の registered observer list に transient として足す。
これがあると、subtree observer は外された部分木の中の変更も配送まで見続ける。
-/
def addTransientObservers (s : DOMState) (node parent : NodeId) : DOMState :=
  let nodes := parent :: ancestors s.tree parent
  let added := nodes.flatMap fun n =>
    (s.registrations.filter fun r => r.node == n && r.subtree && !r.transient).map fun r =>
      { r with node := node, transient := true, source := some r.node }
  -- transient を置いた node を、その observer の node list にも足す。
  -- こうしないと "notify mutation observers" step 5.2 と `observe` step 7.1 の掃除が
  -- この node に届かない（`Dom/Observer/Deliver.lean` の doc comment を参照）。
  let observers := added.foldl (fun obs r =>
    match obs[r.observer]? with
    | none => obs
    | some o =>
      if o.nodeList.contains node then obs
      else obs.set r.observer { o with nodeList := o.nodeList ++ [node] }) s.observers
  { s with registrations := s.registrations ++ added, observers := observers }


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
  unfold queueMutationRecord
  rw [queueMutationObserverMicrotask_tree, foldl_addPendingObserver_tree]

@[simp] theorem queueMutationRecord_ranges (s : DOMState) (rec : MutationRecord)
    (ov : Option String) : (queueMutationRecord s rec ov).ranges = s.ranges := by
  unfold queueMutationRecord
  rw [queueMutationObserverMicrotask_ranges, foldl_addPendingObserver_ranges]

@[simp] theorem queueMutationRecord_iterators (s : DOMState) (rec : MutationRecord)
    (ov : Option String) : (queueMutationRecord s rec ov).iterators = s.iterators := by
  unfold queueMutationRecord
  rw [queueMutationObserverMicrotask_iterators, foldl_addPendingObserver_iterators]

@[simp] theorem queueMutationRecord_registrations (s : DOMState) (rec : MutationRecord)
    (ov : Option String) : (queueMutationRecord s rec ov).registrations = s.registrations := by
  unfold queueMutationRecord
  rw [queueMutationObserverMicrotask_registrations, foldl_addPendingObserver_registrations]

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
    (addTransientObservers s n p).tree = s.tree := rfl

@[simp] theorem addTransientObservers_ranges (s : DOMState) (n p : NodeId) :
    (addTransientObservers s n p).ranges = s.ranges := rfl

@[simp] theorem addTransientObservers_iterators (s : DOMState) (n p : NodeId) :
    (addTransientObservers s n p).iterators = s.iterators := rfl

/-- transient を足しても observer の数は変わらない。 -/
theorem foldl_transient_observers_length :
    ∀ (l : List Registration) (obs : List ObserverState) (node : NodeId),
      (l.foldl (fun obs r =>
        match obs[r.observer]? with
        | none => obs
        | some o =>
          if o.nodeList.contains node then obs
          else obs.set r.observer { o with nodeList := o.nodeList ++ [node] }) obs).length
        = obs.length
  | [], _, _ => rfl
  | x :: xs, obs, node => by
    show (xs.foldl _ (match obs[x.observer]? with
      | none => obs
      | some o =>
        if o.nodeList.contains node then obs
        else obs.set x.observer { o with nodeList := o.nodeList ++ [node] })).length = obs.length
    rw [foldl_transient_observers_length xs]
    split
    · rfl
    · split <;> simp

@[simp] theorem addTransientObservers_observers_length (s : DOMState) (n p : NodeId) :
    (addTransientObservers s n p).observers.length = s.observers.length := by
  unfold addTransientObservers
  exact foldl_transient_observers_length _ _ _

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
  unfold queueMutationRecord
  rw [queueMutationObserverMicrotask_observers, foldl_addPendingObserver_observers]
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

/-- transient registration の observer index は、元の registration から受け継ぐ。 -/
theorem addTransientObservers_observer_lt (s : DOMState) (n p : NodeId) {r : Registration}
    (h : r ∈ (addTransientObservers s n p).registrations)
    (hall : ∀ r' ∈ s.registrations, r'.observer < s.observers.length) :
    r.observer < s.observers.length := by
  unfold addTransientObservers at h
  simp only [List.mem_append] at h
  rcases h with h | h
  · exact hall r h
  · obtain ⟨x, _, hx⟩ := List.mem_flatMap.mp h
    obtain ⟨r₀, hr₀mem, hr₀⟩ := List.mem_map.mp hx
    have := hall r₀ (List.mem_filter.mp hr₀mem).1
    rw [← hr₀]
    exact this

end Dom
