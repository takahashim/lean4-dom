import Dom.Basic.State
import Dom.Basic.Order

/-!
# MutationObserver の record

DOM Standard §4.3.4 の "queue a mutation record" と "queue a tree mutation record"、
および §4.2.3 remove step 20 の transient registered observer を定義する。

配送（"queue a mutation observer microtask" と "notify mutation observers"）は
model の対象外である。record は observer ごとの queue に貯まり、
`takeRecords` で取り出すまで残る。transient registered observer を消すのは
配送の側なので、この model では登録されたまま残る。
-/

namespace Dom

/-! ## interested observers -/

/--
"queue a mutation record" step 2.3 の条件。

仕様は「次のいずれも真でないなら」という否定の形なので、ここでは肯定に直してある。
model は attribute を扱わないので、attribute に関する三つの条件は無い。
-/
def Registration.interestedIn (r : Registration) (target : NodeId) (type : RecordType) : Bool :=
  (r.node == target || r.subtree) &&
    (match type with
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
第二成分は record に載せる oldValue で、
characterData かつ `characterDataOldValue` のときだけ非 `none` になる。
-/
def interestedObservers (s : DOMState) (target : NodeId) (type : RecordType)
    (oldValue : Option String) : List (Nat × Option String) :=
  let nodes := target :: ancestors s.tree target
  nodes.foldl (fun acc n =>
    (s.registrations.filter fun r => r.node == n).foldl (fun acc r =>
      if r.interestedIn target type then
        addInterested acc r.observer
          (if type == .characterData && r.characterDataOldValue then oldValue else none)
      else acc) acc) []

/-! ## record を積む -/

/-- observer `mo` の record queue の末尾に `rec` を足す。 -/
def enqueueRecord (obs : List ObserverState) (mo : Nat) (rec : MutationRecord) :
    List ObserverState :=
  match obs[mo]? with
  | none => obs
  | some o => obs.set mo { o with records := o.records ++ [rec] }

/-- DOM Standard §4.3.4 "queue a mutation record"。 -/
def queueMutationRecord (s : DOMState) (rec : MutationRecord) (oldValue : Option String) :
    DOMState :=
  let interested := interestedObservers s rec.target rec.type oldValue
  { s with
      observers := interested.foldl
        (fun obs p => enqueueRecord obs p.1 { rec with oldValue := p.2 }) s.observers }

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
    (s.registrations.filter fun r => r.node == n && r.subtree).map fun r =>
      { r with node := node, transient := true }
  { s with registrations := s.registrations ++ added }

/-! ## 木を変えないこと -/

@[simp] theorem queueMutationRecord_tree (s : DOMState) (rec : MutationRecord)
    (ov : Option String) : (queueMutationRecord s rec ov).tree = s.tree := rfl

@[simp] theorem queueMutationRecord_ranges (s : DOMState) (rec : MutationRecord)
    (ov : Option String) : (queueMutationRecord s rec ov).ranges = s.ranges := rfl

@[simp] theorem queueMutationRecord_iterators (s : DOMState) (rec : MutationRecord)
    (ov : Option String) : (queueMutationRecord s rec ov).iterators = s.iterators := rfl

@[simp] theorem queueMutationRecord_registrations (s : DOMState) (rec : MutationRecord)
    (ov : Option String) : (queueMutationRecord s rec ov).registrations = s.registrations := rfl

@[simp] theorem queueTreeMutationRecord_tree (s : DOMState) (t : NodeId)
    (a r : List NodeId) (p n : Option NodeId) :
    (queueTreeMutationRecord s t a r p n).tree = s.tree := by
  unfold queueTreeMutationRecord; split <;> rfl

@[simp] theorem queueTreeMutationRecord_ranges (s : DOMState) (t : NodeId)
    (a r : List NodeId) (p n : Option NodeId) :
    (queueTreeMutationRecord s t a r p n).ranges = s.ranges := by
  unfold queueTreeMutationRecord; split <;> rfl

@[simp] theorem queueTreeMutationRecord_iterators (s : DOMState) (t : NodeId)
    (a r : List NodeId) (p n : Option NodeId) :
    (queueTreeMutationRecord s t a r p n).iterators = s.iterators := by
  unfold queueTreeMutationRecord; split <;> rfl

@[simp] theorem queueCharacterDataRecord_tree (s : DOMState) (t : NodeId) (v : String) :
    (queueCharacterDataRecord s t v).tree = s.tree := rfl

@[simp] theorem queueCharacterDataRecord_ranges (s : DOMState) (t : NodeId) (v : String) :
    (queueCharacterDataRecord s t v).ranges = s.ranges := rfl

@[simp] theorem queueCharacterDataRecord_iterators (s : DOMState) (t : NodeId) (v : String) :
    (queueCharacterDataRecord s t v).iterators = s.iterators := rfl

@[simp] theorem addTransientObservers_tree (s : DOMState) (n p : NodeId) :
    (addTransientObservers s n p).tree = s.tree := rfl

@[simp] theorem addTransientObservers_ranges (s : DOMState) (n p : NodeId) :
    (addTransientObservers s n p).ranges = s.ranges := rfl

@[simp] theorem addTransientObservers_iterators (s : DOMState) (n p : NodeId) :
    (addTransientObservers s n p).iterators = s.iterators := rfl

@[simp] theorem addTransientObservers_observers (s : DOMState) (n p : NodeId) :
    (addTransientObservers s n p).observers = s.observers := rfl

@[simp] theorem queueTreeMutationRecord_registrations (s : DOMState) (t : NodeId)
    (a r : List NodeId) (p n : Option NodeId) :
    (queueTreeMutationRecord s t a r p n).registrations = s.registrations := by
  unfold queueTreeMutationRecord; split <;> rfl

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
  exact foldl_enqueue_length _ _ _

@[simp] theorem queueTreeMutationRecord_observers_length (s : DOMState) (t : NodeId)
    (a r : List NodeId) (p n : Option NodeId) :
    (queueTreeMutationRecord s t a r p n).observers.length = s.observers.length := by
  unfold queueTreeMutationRecord
  split
  · rfl
  · exact queueMutationRecord_observers_length ..

@[simp] theorem queueCharacterDataRecord_registrations (s : DOMState) (t : NodeId) (v : String) :
    (queueCharacterDataRecord s t v).registrations = s.registrations := rfl

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
