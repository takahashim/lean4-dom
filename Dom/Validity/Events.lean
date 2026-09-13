import Dom.Validity.State
import Dom.Event.Dispatch

/-!
# event の配送と `AdmissibleDOMState`

`listeners` は `DOMState` の成分だが、`walkers` と同じく
**`AdmissibleDOMState` には入れていない**。§2.7 の listener list は木の形とは独立で、
木を変える algorithm はこれを触らないからである
（node が木から外れても listener はその node に付いたまま、というのが仕様の挙動である）。

ここで示すのは「配送は listener list 以外を変えない」ことで、
そこから admissibility の保存が出る。
-/

namespace Dom

/-- 二つの状態が `listeners` しか違わないこと。 -/
def ListenersOnly (s s' : DOMState) : Prop :=
  { s with listeners := s'.listeners } = s'

namespace ListenersOnly

theorem refl (s : DOMState) : ListenersOnly s s := rfl

theorem trans {a b c : DOMState} (h₁ : ListenersOnly a b) (h₂ : ListenersOnly b c) :
    ListenersOnly a c := by
  unfold ListenersOnly at *
  rw [← h₂, ← h₁]

end ListenersOnly

theorem listenersOnly_removeListenerAt (s : DOMState) (i : Nat) :
    ListenersOnly s (removeListenerAt s i) := by
  unfold ListenersOnly removeListenerAt
  split <;> rfl

theorem listenersOnly_addListener (s : DOMState) (l : EventListener) :
    ListenersOnly s (addListener s l) := by
  unfold ListenersOnly addListener
  split <;> rfl

theorem listenersOnly_runAction (s : DOMState) (e : EventState) (l : EventListener) :
    ListenersOnly s (runAction s e l).1 := by
  unfold runAction
  split
  · exact ListenersOnly.refl s
  · exact ListenersOnly.refl s
  · exact ListenersOnly.refl s
  · exact ListenersOnly.refl s
  · exact listenersOnly_removeListenerAt s _
  · next src _ _ _ =>
    split
    · exact ListenersOnly.refl s
    · exact listenersOnly_addListener s _

theorem listenersOnly_invokeOne (s : DOMState) (e : EventState) (l : EventListener) (i : Nat) :
    ListenersOnly s (invokeOne s e l i).1 := by
  unfold invokeOne
  have h₁ : ListenersOnly s (if l.once then removeListenerAt s i else s) := by
    split
    · exact listenersOnly_removeListenerAt s i
    · exact ListenersOnly.refl s
  exact h₁.trans (listenersOnly_runAction _ e l)

theorem listenersOnly_innerInvoke (capturing : Bool) (cur : NodeId) :
    ∀ (idxs : List Nat) (s : DOMState) (e : EventState) (log : List Invocation),
      ListenersOnly s (innerInvoke capturing cur s e log idxs).1
  | [], s, _, _ => ListenersOnly.refl s
  | i :: rest, s, e, log => by
    rw [innerInvoke]
    split
    · exact listenersOnly_innerInvoke capturing cur rest s e log
    · next l _ =>
      split
      · exact listenersOnly_innerInvoke capturing cur rest s e log
      · split
        · exact listenersOnly_innerInvoke capturing cur rest s e log
        · dsimp only
          split
          · exact listenersOnly_invokeOne s e l i
          · exact (listenersOnly_invokeOne s e l i).trans
              (listenersOnly_innerInvoke capturing cur rest _ _ _)

theorem listenersOnly_invokeItem (s : DOMState) (e : EventState) (log : List Invocation)
    (capturing : Bool) (item : NodeId) (isTarget : Bool) :
    ListenersOnly s (invokeItem s e log capturing item isTarget).1 := by
  unfold invokeItem
  split
  · exact ListenersOnly.refl s
  · exact listenersOnly_innerInvoke _ _ _ _ _ _

theorem listenersOnly_runPass (capturing : Bool) (target : NodeId) :
    ∀ (path : List NodeId) (s : DOMState) (e : EventState) (log : List Invocation),
      ListenersOnly s (runPass capturing target s e log path).1
  | [], s, _, _ => ListenersOnly.refl s
  | item :: rest, s, e, log => by
    rw [runPass]
    dsimp only
    split
    · exact listenersOnly_runPass capturing target rest s e log
    · exact (listenersOnly_invokeItem s e log capturing item _).trans
        (listenersOnly_runPass capturing target rest _ _ _)

/-- **配送は listener list 以外を変えない。** -/
theorem listenersOnly_dispatchEvent {s s' : DOMState} {target : NodeId} {ty : String}
    {b c r : Bool} {log : List Invocation}
    (hd : dispatchEvent s target ty b c = .ok (s', r, log)) : ListenersOnly s s' := by
  unfold dispatchEvent at hd
  split at hd
  · simp at hd
  · dsimp only at hd
    have := (Prod.mk.injEq ..).mp (Except.ok.inj hd)
    rw [← this.1]
    exact (listenersOnly_runPass true target _ s _ []).trans
      (listenersOnly_runPass false target _ _ _ _)

/-- listener list を差し替えても、admissibility の七成分は変わらない。 -/
theorem admissible_withListeners {s : DOMState} {ls : List EventListener}
    (h : AdmissibleDOMState s) : AdmissibleDOMState { s with listeners := ls } :=
  ⟨h.structural, h.nodeDocuments, h.documentTrees, h.rangeEndpoints, h.iterators,
    h.observerRegistrations, h.attributes⟩

theorem admissible_of_listenersOnly {s s' : DOMState} (h : AdmissibleDOMState s)
    (hl : ListenersOnly s s') : AdmissibleDOMState s' := by
  unfold ListenersOnly at hl
  rw [← hl]
  exact admissible_withListeners h

/-- **`dispatchEvent` は admissibility を保つ。** -/
theorem admissible_dispatchEvent {s s' : DOMState} {target : NodeId} {ty : String}
    {b c r : Bool} {log : List Invocation} (h : AdmissibleDOMState s)
    (hd : dispatchEvent s target ty b c = .ok (s', r, log)) : AdmissibleDOMState s' :=
  admissible_of_listenersOnly h (listenersOnly_dispatchEvent hd)

/-- `addEventListener` は admissibility を保つ。 -/
theorem admissible_addEventListener {s s' : DOMState} {target : NodeId} {ty : String}
    {src : Nat} {cap once : Bool} (h : AdmissibleDOMState s)
    (ha : addEventListener s target ty src cap once = .ok s') : AdmissibleDOMState s' := by
  unfold addEventListener at ha
  split at ha
  · simp at ha
  · split at ha
    · simp at ha
    · rw [← Except.ok.inj ha]
      exact admissible_of_listenersOnly h (listenersOnly_addListener s _)

/-- `removeEventListener` は admissibility を保つ。 -/
theorem admissible_removeEventListener {s s' : DOMState} {target : NodeId} {ty : String}
    {cb : Nat} {cap : Bool} (h : AdmissibleDOMState s)
    (hr : removeEventListener s target ty cb cap = .ok s') : AdmissibleDOMState s' := by
  unfold removeEventListener at hr
  split at hr
  · simp at hr
  · split at hr
    · rw [← Except.ok.inj hr]; exact h
    · rw [← Except.ok.inj hr]
      exact admissible_of_listenersOnly h (listenersOnly_removeListenerAt s _)

end Dom
