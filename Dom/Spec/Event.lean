import Dom.Event.Dispatch

/-!
# event の配送の関係意味論（§2.7・§2.9）

`replace` などと同じ方針。仕様本文から独立に書き写した関係を置き、
実行関数（`Dom/Event/Dispatch.lean`）がそれとちょうど一致することは
`Dom/Spec/EventSound.lean` で証明する。

## model の範囲

`Dom/Event/Dispatch.lean` の冒頭と同じ。shadow tree も `Window` も無いので、event path は
target から get the parent を辿った列で、shadow-adjusted target を持つのは先頭の target だけである。
callback は model の外なので、scenario が宣言した副作用（`ListenerAction`）を
`CallbackRan` が仕様の言葉で書く。

## listener list

仕様の listener list は EventTarget ごとだが、model は一本の list に `target` を持たせ、
"remove an event listener" は list から取り除く代わりに `removed` を立てる
（`Dom/Basic/State.lean` の `EventListener`）。したがって「`item` の listener list」は
「target が `item` で `removed` でない listener」を list の順に並べたものである。
-/

namespace Dom.Spec

open Dom

/-! ## §2.9 dispatch step 5.4-5.10：event path -/

/--
target から get the parent を辿った列。Document の get the parent は（`Window` が無いので）null、
それ以外の node は parent である。
-/
inductive EventPathSpec (t : Tree) : NodeId → List NodeId → Prop where
  | last {n : NodeId} : parentOf t n = none → EventPathSpec t n [n]
  | cons {n p : NodeId} {ps : List NodeId} :
      parentOf t n = some p → EventPathSpec t p ps → EventPathSpec t n (n :: ps)

/-! ## §2.7 listener list の操作 -/

/-- "remove an event listener"：`removed` を立てる。 -/
def ListenerRemovedAt (s s' : DOMState) (i : Nat) : Prop :=
  (s.listeners[i]? = none ∧ s' = s) ∨
    (∃ l, s.listeners[i]? = some l ∧
      s' = { s with listeners := s.listeners.set i { l with removed := true } })

/--
"add an event listener" の step 5。
同じ target・type・callback・capture の listener がまだ list にあれば何もしない。
-/
def ListenerAdded (s s' : DOMState) (l : EventListener) : Prop :=
  ((∃ x ∈ s.listeners, x.removed = false ∧ x.target = l.target ∧ x.type = l.type ∧
      x.callback = l.callback ∧ x.capture = l.capture) ∧ s' = s) ∨
    ((¬ ∃ x ∈ s.listeners, x.removed = false ∧ x.target = l.target ∧ x.type = l.type ∧
      x.callback = l.callback ∧ x.capture = l.capture) ∧
      s' = { s with listeners := s.listeners ++ [l] })

/-- `item` の listener list（invoke の step 6 の clone）：その listener の index を list の順に並べた列。 -/
def ListenersOf (s : DOMState) (item : NodeId) (idxs : List Nat) : Prop :=
  idxs.Pairwise (· < ·) ∧
    ∀ i, i ∈ idxs ↔ ∃ l, s.listeners[i]? = some l ∧ l.target = item ∧ l.removed = false

/-! ## callback の副作用 -/

/--
listener の callback を呼んだ効果。

* `stopPropagation()` は stop propagation flag を立てる。
* `stopImmediatePropagation()` は stop propagation flag と stop immediate propagation flag を立てる。
* `preventDefault()` は cancelable なら canceled flag を立てる（passive は扱わない）。
* `removeEventListener` / `addEventListener` は §2.7 の操作。
-/
def CallbackRan (s : DOMState) (e : EventState) (l : EventListener) (s' : DOMState)
    (e' : EventState) : Prop :=
  match l.action with
  | .none => s' = s ∧ e' = e
  | .stopPropagation => s' = s ∧ e' = { e with stopPropagation := true }
  | .stopImmediatePropagation =>
    s' = s ∧ e' = { e with stopPropagation := true, stopImmediate := true }
  | .preventDefault =>
    s' = s ∧ ((e.cancelable = true ∧ e' = { e with canceled := true }) ∨
      (e.cancelable = false ∧ e' = e))
  | .removeListener k => ListenerRemovedAt s s' k ∧ e' = e
  | .addListener tgt ty src cap =>
    e' = e ∧ ((s.listeners[src]? = none ∧ s' = s) ∨
      ∃ source, s.listeners[src]? = some source ∧
        ListenerAdded s s'
          { target := ⟨tgt⟩, «type» := ty, callback := source.callback, capture := cap,
            once := false, action := source.action })

/-! ## §2.9 inner invoke -/

/--
"inner invoke"。`idxs`（clone）を順に見る。

2. removed の listener は飛ばす。
2.1. type が違えば飛ばす。
2.3-2.4. phase が capturing で capture が false、bubbling で capture が true なら飛ばす。
2.5. once なら、呼ぶ前に外す。
2.11. callback を呼ぶ。呼ばれたことを記録する。
2.14. stop immediate propagation flag が立てば終わる。
-/
inductive InnerInvoked (capturing : Bool) (cur : NodeId) :
    DOMState → EventState → List Nat → DOMState → EventState → List Invocation → Prop where
  | nil {s : DOMState} {e : EventState} : InnerInvoked capturing cur s e [] s e []
  | gone {s s' : DOMState} {e e' : EventState} {i : Nat} {rest : List Nat}
      {log : List Invocation} :
      s.listeners[i]? = none → InnerInvoked capturing cur s e rest s' e' log →
      InnerInvoked capturing cur s e (i :: rest) s' e' log
  | skip {s s' : DOMState} {e e' : EventState} {i : Nat} {rest : List Nat}
      {log : List Invocation} {l : EventListener} :
      s.listeners[i]? = some l → (l.removed = true ∨ l.type ≠ e.type ∨ l.capture ≠ capturing) →
      InnerInvoked capturing cur s e rest s' e' log →
      InnerInvoked capturing cur s e (i :: rest) s' e' log
  | call {s s₁ s₂ s' : DOMState} {e e₂ e' : EventState} {i : Nat} {rest : List Nat}
      {log : List Invocation} {l : EventListener} :
      s.listeners[i]? = some l → l.removed = false → l.type = e.type → l.capture = capturing →
      -- step 2.5
      ((l.once = true ∧ ListenerRemovedAt s s₁ i) ∨ (l.once = false ∧ s₁ = s)) →
      -- step 2.11
      CallbackRan s₁ e l s₂ e₂ →
      e₂.stopImmediate = false →
      InnerInvoked capturing cur s₂ e₂ rest s' e' log →
      InnerInvoked capturing cur s e (i :: rest) s' e'
        (⟨l.callback, cur, e.eventPhase⟩ :: log)
  /-- step 2.14：stop immediate propagation flag が立てば、残りは呼ばない。 -/
  | callStop {s s₁ s₂ : DOMState} {e e₂ : EventState} {i : Nat} {rest : List Nat}
      {l : EventListener} :
      s.listeners[i]? = some l → l.removed = false → l.type = e.type → l.capture = capturing →
      ((l.once = true ∧ ListenerRemovedAt s s₁ i) ∨ (l.once = false ∧ s₁ = s)) →
      CallbackRan s₁ e l s₂ e₂ →
      e₂.stopImmediate = true →
      InnerInvoked capturing cur s e (i :: rest) s₂ e₂ [⟨l.callback, cur, e.eventPhase⟩]

/-! ## §2.9 invoke と dispatch -/

/-- dispatch の step 5.13-5.14 が決める eventPhase。 -/
def phaseOf (capturing isTarget : Bool) : Nat :=
  if isTarget then 2 else if capturing then 1 else 3

/--
dispatch の step 5.13-5.14 の一つの item と "invoke"。

eventPhase を決めてから invoke する。invoke の step 4：stop propagation flag が立っていれば
何もしない。step 6：listener list を clone する。step 7：inner invoke。
-/
def Invoked (s : DOMState) (e : EventState) (capturing : Bool) (item : NodeId) (isTarget : Bool)
    (s' : DOMState) (e' : EventState) (log : List Invocation) : Prop :=
  (e.stopPropagation = true ∧ s' = s ∧
      e' = { e with eventPhase := phaseOf capturing isTarget } ∧ log = []) ∨
    (e.stopPropagation = false ∧ ∃ idxs, ListenersOf s item idxs ∧
      InnerInvoked capturing item s { e with eventPhase := phaseOf capturing isTarget } idxs
        s' e' log)

/--
dispatch の step 5.13（capture の周、path を逆順に）と step 5.14（bubble の周、path の順）。

bubble の周では、target 以外の item は event の bubbles が false なら飛ばす。
-/
inductive PassRan (capturing : Bool) (target : NodeId) :
    DOMState → EventState → List NodeId → DOMState → EventState → List Invocation → Prop where
  | nil {s : DOMState} {e : EventState} : PassRan capturing target s e [] s e []
  | skip {s s' : DOMState} {e e' : EventState} {item : NodeId} {rest : List NodeId}
      {log : List Invocation} :
      capturing = false → item ≠ target → e.bubbles = false →
      PassRan capturing target s e rest s' e' log →
      PassRan capturing target s e (item :: rest) s' e' log
  | invoke {s s₁ s' : DOMState} {e e₁ e' : EventState} {item : NodeId} {rest : List NodeId}
      {log₁ log₂ : List Invocation} :
      ¬ (capturing = false ∧ item ≠ target ∧ e.bubbles = false) →
      Invoked s e capturing item (decide (item = target)) s₁ e₁ log₁ →
      PassRan capturing target s₁ e₁ rest s' e' log₂ →
      PassRan capturing target s e (item :: rest) s' e' (log₁ ++ log₂)

/--
**§2.9 `dispatchEvent` の、結果まで含めた関係。**

成功すれば「最終状態」「戻り値（canceled flag が立っていなければ true）」「呼ばれた listener の列」。
target が木に無ければ（model の都合）`NotFoundError`。
-/
def DispatchResult (s : DOMState) (target : NodeId) («type» : String) (bubbles cancelable : Bool) :
    Except DOMException (DOMState × Bool × List Invocation) → Prop
  | .error e => s.tree.get? target = none ∧ e = .notFoundError
  | .ok (s', ret, log) =>
    (∃ d, s.tree.get? target = some d) ∧
      ∃ (path : List NodeId) (s₁ : DOMState) (e₁ e₂ : EventState) (log₁ log₂ : List Invocation),
        EventPathSpec s.tree target path ∧
        PassRan true target s { «type» := «type», bubbles := bubbles, cancelable := cancelable }
          path.reverse s₁ e₁ log₁ ∧
        PassRan false target s₁ e₁ path s' e₂ log₂ ∧
        log = log₁ ++ log₂ ∧ ret = !e₂.canceled

/-! ## §2.7 `addEventListener` / `removeEventListener` -/

/--
**`addEventListener(type, callback, options)` の、結果まで含めた関係。**

callback は scenario の `source` 番の listener のものを使う。target か `source` が無ければ
（model の都合）`NotFoundError`。
-/
def AddEventListenerResult (s : DOMState) (target : NodeId) («type» : String) (source : Nat)
    (capture once : Bool) : Except DOMException DOMState → Prop
  | .error e => (s.tree.get? target = none ∨ s.listeners[source]? = none) ∧ e = .notFoundError
  | .ok s' => (∃ d, s.tree.get? target = some d) ∧ ∃ src, s.listeners[source]? = some src ∧
      ListenerAdded s s'
        { target := target, «type» := «type», callback := src.callback, capture := capture,
          once := once, action := src.action }

/-- listener が target・type・callback・capture に当たること。 -/
def ListenerMatches (l : EventListener) (target : NodeId) («type» : String) (callback : Nat)
    (capture : Bool) : Prop :=
  l.removed = false ∧ l.target = target ∧ l.type = «type» ∧ l.callback = callback ∧
    l.capture = capture

/--
**`removeEventListener(type, callback, options)` の、結果まで含めた関係。**

当たる listener があれば remove an event listener する。add が重複を足さないので
当たるものは高々一つだが、関係は「list で最初のもの」と書く。
-/
def RemoveEventListenerResult (s : DOMState) (target : NodeId) («type» : String)
    (callback : Nat) (capture : Bool) : Except DOMException DOMState → Prop
  | .error e => s.tree.get? target = none ∧ e = .notFoundError
  | .ok s' => (∃ d, s.tree.get? target = some d) ∧
      (((¬ ∃ l ∈ s.listeners, ListenerMatches l target «type» callback capture) ∧ s' = s) ∨
        (∃ i l, s.listeners[i]? = some l ∧ ListenerMatches l target «type» callback capture ∧
          (∀ j l', j < i → s.listeners[j]? = some l' →
            ¬ ListenerMatches l' target «type» callback capture) ∧
          ListenerRemovedAt s s' i))

end Dom.Spec
