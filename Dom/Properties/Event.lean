import Dom.Event.Dispatch
import Dom.Properties.Tree

/-!
# §2.9 dispatch の振る舞い

`Dom/Validity/Events.lean` は「listener 以外を変えない」「妥当性を保つ」という
不変条件を示している。ここでは仕様の **振る舞い** の側を書く。

* callback の副作用（`stopPropagation` / `stopImmediatePropagation` /
  `preventDefault` / `once`）が何を立てるか
* listener の選別（capture 周は capture listener だけ、`removed` と `type` の検査）
* 停止フラグが立った後は何も呼ばれないこと
* `bubbles` が false なら bubble の周で target 以外は呼ばれないこと
* log は伸びるだけ（呼ばれた順に後ろへ足される）
* 戻り値は canceled flag の否定で、`cancelable` が false なら必ず true
-/

namespace Dom

/-! ## `runAction` -/

theorem runAction_stopPropagation (s : DOMState) (e : EventState) (l : EventListener)
    (h : l.action = .stopPropagation) :
    runAction s e l = (s, { e with stopPropagation := true }) := by
  unfold runAction; rw [h]

theorem runAction_stopImmediate (s : DOMState) (e : EventState) (l : EventListener)
    (h : l.action = .stopImmediatePropagation) :
    runAction s e l = (s, { e with stopPropagation := true, stopImmediate := true }) := by
  unfold runAction; rw [h]

theorem runAction_preventDefault_cancelable (s : DOMState) (e : EventState) (l : EventListener)
    (h : l.action = .preventDefault) (hc : e.cancelable = true) :
    runAction s e l = (s, { e with canceled := true }) := by
  unfold runAction; rw [h]; simp [hc]

theorem runAction_preventDefault_not_cancelable (s : DOMState) (e : EventState)
    (l : EventListener) (h : l.action = .preventDefault) (hc : e.cancelable = false) :
    runAction s e l = (s, e) := by
  unfold runAction; rw [h]; simp [hc]

theorem runAction_type (s : DOMState) (e : EventState) (l : EventListener) :
    (runAction s e l).2.type = e.type := by
  unfold runAction; split <;> (try split) <;> rfl

theorem runAction_bubbles (s : DOMState) (e : EventState) (l : EventListener) :
    (runAction s e l).2.bubbles = e.bubbles := by
  unfold runAction; split <;> (try split) <;> rfl

theorem runAction_cancelable (s : DOMState) (e : EventState) (l : EventListener) :
    (runAction s e l).2.cancelable = e.cancelable := by
  unfold runAction; split <;> (try split) <;> rfl

theorem runAction_eventPhase (s : DOMState) (e : EventState) (l : EventListener) :
    (runAction s e l).2.eventPhase = e.eventPhase := by
  unfold runAction; split <;> (try split) <;> rfl

/-- **cancelable でなければ canceled は立たない。** -/
theorem runAction_canceled_of_not_cancelable (s : DOMState) (e : EventState) (l : EventListener)
    (hc : e.cancelable = false) (he : e.canceled = false) :
    (runAction s e l).2.canceled = false := by
  unfold runAction
  split <;> (try split) <;> simp_all

/-- **stop propagation flag は一度立つと落ちない。** -/
theorem runAction_stopPropagation_mono (s : DOMState) (e : EventState) (l : EventListener)
    (h : e.stopPropagation = true) : (runAction s e l).2.stopPropagation = true := by
  unfold runAction
  split <;> (try split) <;> simp_all

/-- **`innerInvoke` は log を伸ばすだけである。** -/
theorem innerInvoke_log_prefix (capturing : Bool) (cur : NodeId) :
    ∀ (idxs : List Nat) (s : DOMState) (e : EventState) (log : List Invocation),
      log <+: (innerInvoke capturing cur s e log idxs).2.2
  | [], s, e, log => by rw [innerInvoke]; exact List.prefix_refl _
  | i :: rest, s, e, log => by
    rw [innerInvoke]
    split
    · exact innerInvoke_log_prefix capturing cur rest s e log
    · split
      · exact innerInvoke_log_prefix capturing cur rest s e log
      · split
        · exact innerInvoke_log_prefix capturing cur rest s e log
        · by_cases hstop : (invokeOne s e ‹EventListener› i).2.stopImmediate = true
          · rw [if_pos hstop]
            exact List.prefix_append _ _
          · rw [if_neg hstop]
            exact List.IsPrefix.trans (List.prefix_append _ _)
              (innerInvoke_log_prefix capturing cur rest _ _ _)

/-- **`invokeItem` は log を伸ばすだけである。** -/
theorem invokeItem_log_prefix (s : DOMState) (e : EventState) (log : List Invocation)
    (capturing : Bool) (item : NodeId) (isTarget : Bool) :
    log <+: (invokeItem s e log capturing item isTarget).2.2 := by
  unfold invokeItem
  split
  · exact List.prefix_refl _
  · exact innerInvoke_log_prefix _ _ _ _ _ _

/-- **`runPass` は log を伸ばすだけである。** 呼ばれた順に後ろへ足される。 -/
theorem runPass_log_prefix (capturing : Bool) (target : NodeId) :
    ∀ (path : List NodeId) (s : DOMState) (e : EventState) (log : List Invocation),
      log <+: (runPass capturing target s e log path).2.2
  | [], s, e, log => by rw [runPass]; exact List.prefix_refl _
  | item :: rest, s, e, log => by
    rw [runPass]
    split
    · exact runPass_log_prefix capturing target rest s e log
    · exact List.IsPrefix.trans (invokeItem_log_prefix s e log capturing item (item == target))
        (runPass_log_prefix capturing target rest _ _ _)

/-- **stop propagation flag が立っていれば、その item は何もしない（invoke の step 5）。** -/
theorem invokeItem_stopPropagation (s : DOMState) (e : EventState) (log : List Invocation)
    (capturing : Bool) (item : NodeId) (isTarget : Bool) (h : e.stopPropagation = true) :
    invokeItem s e log capturing item isTarget = (s, e, log) := by
  unfold invokeItem; rw [if_pos h]

/-- **stop propagation flag が立った後は、残りの item は一つも呼ばれない。** -/
theorem runPass_stopPropagation (capturing : Bool) (target : NodeId) :
    ∀ (path : List NodeId) (s : DOMState) (e : EventState) (log : List Invocation),
      e.stopPropagation = true → runPass capturing target s e log path = (s, e, log)
  | [], s, e, log, _ => by rw [runPass]
  | item :: rest, s, e, log, h => by
    rw [runPass]
    split
    · exact runPass_stopPropagation capturing target rest s e log h
    · rw [invokeItem_stopPropagation s e log capturing item (item == target) h]
      exact runPass_stopPropagation capturing target rest s e log h

/--
**`bubbles` が false なら、bubble の周で target 以外は呼ばれない（dispatch の step 13.2.1）。**
-/
theorem runPass_no_bubbles (target : NodeId) :
    ∀ (path : List NodeId) (s : DOMState) (e : EventState) (log : List Invocation),
      e.bubbles = false → (∀ x ∈ path, x ≠ target) →
      runPass false target s e log path = (s, e, log)
  | [], s, e, log, _, _ => by rw [runPass]
  | item :: rest, s, e, log, hb, hx => by
    rw [runPass]
    have hne : item ≠ target := hx item (by simp)
    rw [if_pos (by simp [hb, hne])]
    exact runPass_no_bubbles target rest s e log hb (fun y hy => hx y (by simp [hy]))

/-! ## 返り値 -/

/-- **`dispatchEvent` の戻り値は canceled flag の否定である（§2.9 の step 15）。** -/
theorem dispatchEvent_returns (s : DOMState) (target : NodeId) (ty : String)
    (bubbles cancelable : Bool) {s' : DOMState} {r : Bool} {log : List Invocation}
    (h : dispatchEvent s target ty bubbles cancelable = .ok (s', r, log)) :
    ∃ e : EventState, r = !e.canceled := by
  unfold dispatchEvent at h
  split at h
  · simp at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨_, h.2.1.symm⟩

/-- **木に無い node への `dispatchEvent` は NotFoundError である。** -/
theorem dispatchEvent_not_found (s : DOMState) (target : NodeId) (ty : String)
    (bubbles cancelable : Bool) (h : s.tree.get? target = none) :
    dispatchEvent s target ty bubbles cancelable = .error .notFoundError := by
  unfold dispatchEvent; rw [h]

/-! ## event path -/

@[simp] theorem eventPath_eq (t : Tree) (target : NodeId) :
    eventPath t target = target :: ancestors t target := rfl

/-- **event path の先頭は target である。** capture 周は逆順なので根から始まる。 -/
theorem eventPath_head (t : Tree) (target : NodeId) :
    (eventPath t target).head? = some target := rfl

theorem invokeOne_cancelable (s : DOMState) (e : EventState) (l : EventListener) (i : Nat) :
    (invokeOne s e l i).2.cancelable = e.cancelable := by
  unfold invokeOne
  split <;> (unfold runAction; split <;> (try split) <;> rfl)

theorem invokeOne_canceled_of_not_cancelable (s : DOMState) (e : EventState) (l : EventListener)
    (i : Nat) (hc : e.cancelable = false) (he : e.canceled = false) :
    (invokeOne s e l i).2.canceled = false := by
  unfold invokeOne
  split <;> (unfold runAction; split <;> (try split) <;> simp_all)

/--
**選別条件に合う listener が一つも無ければ、`innerInvoke` は何もしない。**

capture 周では capture listener だけ、bubble 周では非 capture listener だけを呼ぶ
（invoke の step 2.3-2.4）。`removed` と `type` の検査も同じ形である。
-/
theorem innerInvoke_skip (capturing : Bool) (cur : NodeId) :
    ∀ (idxs : List Nat) (s : DOMState) (e : EventState) (log : List Invocation),
      (∀ i ∈ idxs, ∀ l, s.listeners[i]? = some l →
        l.removed = true ∨ l.type ≠ e.type ∨ l.capture ≠ capturing) →
      innerInvoke capturing cur s e log idxs = (s, e, log)
  | [], s, e, log, _ => by rw [innerInvoke]
  | i :: rest, s, e, log, h => by
    rw [innerInvoke]
    have hrest : ∀ j ∈ rest, ∀ l, s.listeners[j]? = some l →
        l.removed = true ∨ l.type ≠ e.type ∨ l.capture ≠ capturing :=
      fun j hj => h j (by simp [hj])
    split
    · exact innerInvoke_skip capturing cur rest s e log hrest
    · next l hl =>
      have hsel := h i (by simp) l hl
      split
      · exact innerInvoke_skip capturing cur rest s e log hrest
      · next hkeep =>
        have htype : l.removed = false ∧ l.type = e.type := by
          simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, bne_iff_ne, ne_eq,
            Decidable.not_not] at hkeep
          constructor
          · cases hr : l.removed with
            | false => rfl
            | true => exact absurd (Or.inl (by rw [hr])) hkeep
          · by_cases ht : l.type = e.type
            · exact ht
            · exact absurd (Or.inr ht) hkeep
        have hcap : l.capture ≠ capturing := by
          rcases hsel with hr | ht | hc
          · rw [htype.1] at hr; simp at hr
          · exact absurd htype.2 ht
          · exact hc
        rw [if_pos (by simp [Ne.symm hcap])]
        exact innerInvoke_skip capturing cur rest s e log hrest

/-- **cancelable でない event の canceled flag は立たない。** -/
theorem innerInvoke_not_canceled (capturing : Bool) (cur : NodeId) :
    ∀ (idxs : List Nat) (s : DOMState) (e : EventState) (log : List Invocation),
      e.cancelable = false → e.canceled = false →
      (innerInvoke capturing cur s e log idxs).2.1.cancelable = false ∧
        (innerInvoke capturing cur s e log idxs).2.1.canceled = false
  | [], s, e, log, hc, he => by rw [innerInvoke]; exact ⟨hc, he⟩
  | i :: rest, s, e, log, hc, he => by
    rw [innerInvoke]
    split
    · exact innerInvoke_not_canceled capturing cur rest s e log hc he
    · next l hl =>
      split
      · exact innerInvoke_not_canceled capturing cur rest s e log hc he
      · split
        · exact innerInvoke_not_canceled capturing cur rest s e log hc he
        · have hc2 : (invokeOne s e l i).2.cancelable = false := by
            rw [invokeOne_cancelable]; exact hc
          have he2 : (invokeOne s e l i).2.canceled = false :=
            invokeOne_canceled_of_not_cancelable s e l i hc he
          by_cases hstop : (invokeOne s e l i).2.stopImmediate = true
          · rw [if_pos hstop]; exact ⟨hc2, he2⟩
          · rw [if_neg hstop]
            exact innerInvoke_not_canceled capturing cur rest _ _ _ hc2 he2

theorem invokeItem_not_canceled (s : DOMState) (e : EventState) (log : List Invocation)
    (capturing : Bool) (item : NodeId) (isTarget : Bool)
    (hc : e.cancelable = false) (he : e.canceled = false) :
    (invokeItem s e log capturing item isTarget).2.1.cancelable = false ∧
      (invokeItem s e log capturing item isTarget).2.1.canceled = false := by
  unfold invokeItem
  split
  · exact ⟨hc, he⟩
  · exact innerInvoke_not_canceled _ _ _ _ _ _ hc he

theorem runPass_not_canceled (capturing : Bool) (target : NodeId) :
    ∀ (path : List NodeId) (s : DOMState) (e : EventState) (log : List Invocation),
      e.cancelable = false → e.canceled = false →
      (runPass capturing target s e log path).2.1.cancelable = false ∧
        (runPass capturing target s e log path).2.1.canceled = false
  | [], s, e, log, hc, he => by rw [runPass]; exact ⟨hc, he⟩
  | item :: rest, s, e, log, hc, he => by
    rw [runPass]
    split
    · exact runPass_not_canceled capturing target rest s e log hc he
    · obtain ⟨hc2, he2⟩ := invokeItem_not_canceled s e log capturing item (item == target) hc he
      exact runPass_not_canceled capturing target rest _ _ _ hc2 he2

/-- **`cancelable` が false なら `dispatchEvent` は必ず true を返す（§2.4）。** -/
theorem dispatchEvent_not_cancelable (s : DOMState) (target : NodeId) (ty : String)
    (bubbles : Bool) {s' : DOMState} {r : Bool} {log : List Invocation}
    (h : dispatchEvent s target ty bubbles false = .ok (s', r, log)) : r = true := by
  unfold dispatchEvent at h
  split at h
  · simp at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hc1, he1⟩ := runPass_not_canceled true target
      (eventPath s.tree target).reverse s
      ({ «type» := ty, bubbles := bubbles, cancelable := false } : EventState) [] rfl rfl
    obtain ⟨-, he2⟩ := runPass_not_canceled false target
      (eventPath s.tree target) _ _ _ hc1 he1
    rw [← h.2.1, he2]
    rfl

/-! ## `once` -/

/-- **`once` の listener は呼ぶ前に外される（invoke の step 2.5）。** -/
theorem invokeOne_once (s : DOMState) (e : EventState) (l : EventListener) (i : Nat)
    (h : l.once = true) : invokeOne s e l i = runAction (removeListenerAt s i) e l := by
  unfold invokeOne; rw [if_pos h]

/-- **外した listener には `removed` が立つ。** 以降の invoke はこれを見て飛ばす。 -/
theorem removeListenerAt_removed (s : DOMState) (i : Nat) (l : EventListener)
    (h : s.listeners[i]? = some l) :
    (removeListenerAt s i).listeners[i]? = some { l with removed := true } := by
  unfold removeListenerAt
  rw [h]
  simp only [List.getElem?_set, if_pos, if_true]
  rw [if_pos (by
    rcases Nat.lt_or_ge i s.listeners.length with hlt | hge
    · exact hlt
    · rw [List.getElem?_eq_none hge] at h; simp at h)]

end Dom
