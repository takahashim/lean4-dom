import Dom.Spec.Event
import Dom.Properties.Tree
import Dom.Util.List

/-!
# event の配送は関係とちょうど一致する

段ごとに二つの向きを示す。

* sound：実行関数の結果は関係を満たす。
* complete：関係を満たす結果は、実行関数の結果と**等しい**。

event の配送は listener list と event のフラグしか動かさないので、観測の一致（`ObsEq`）を経由せず、
等号で言える。一意性は complete から直ちに出る。
-/

namespace Dom.Spec

open Dom

/-! ## §2.7 listener list の操作 -/

theorem removeListenerAt_spec (s : DOMState) (i : Nat) :
    ListenerRemovedAt s (removeListenerAt s i) i := by
  unfold removeListenerAt ListenerRemovedAt
  cases h : s.listeners[i]? with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some l => exact Or.inr ⟨l, rfl, rfl⟩

theorem listenerRemovedAt_eq {s s' : DOMState} {i : Nat} (h : ListenerRemovedAt s s' i) :
    s' = removeListenerAt s i := by
  unfold removeListenerAt
  rcases h with ⟨hn, rfl⟩ | ⟨l, hl, rfl⟩
  · rw [hn]
  · rw [hl]

private theorem any_iff (s : DOMState) (l : EventListener) :
    (s.listeners.any fun x =>
        !x.removed && x.target == l.target && x.type == l.type &&
          x.callback == l.callback && x.capture == l.capture) = true ↔
      ∃ x ∈ s.listeners, x.removed = false ∧ x.target = l.target ∧ x.type = l.type ∧
        x.callback = l.callback ∧ x.capture = l.capture := by
  simp only [List.any_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq,
    and_assoc]

theorem addListener_spec (s : DOMState) (l : EventListener) :
    ListenerAdded s (addListener s l) l := by
  unfold addListener ListenerAdded
  by_cases h : (s.listeners.any fun x =>
      !x.removed && x.target == l.target && x.type == l.type &&
        x.callback == l.callback && x.capture == l.capture) = true
  · rw [if_pos h]; exact Or.inl ⟨(any_iff s l).mp h, rfl⟩
  · rw [if_neg h]; exact Or.inr ⟨fun h' => h ((any_iff s l).mpr h'), rfl⟩

theorem listenerAdded_eq {s s' : DOMState} {l : EventListener} (h : ListenerAdded s s' l) :
    s' = addListener s l := by
  unfold addListener
  rcases h with ⟨hx, he⟩ | ⟨hx, he⟩
  · rw [if_pos ((any_iff s l).mpr hx), he]
  · rw [if_neg (fun h' => hx ((any_iff s l).mp h')), he]

/-! ## callback の副作用 -/

theorem runAction_spec (s : DOMState) (e : EventState) (l : EventListener) :
    CallbackRan s e l (runAction s e l).1 (runAction s e l).2 := by
  unfold CallbackRan runAction
  cases l.action with
  | none => exact ⟨rfl, rfl⟩
  | stopPropagation => exact ⟨rfl, rfl⟩
  | stopImmediatePropagation => exact ⟨rfl, rfl⟩
  | preventDefault =>
    refine ⟨rfl, ?_⟩
    cases hc : e.cancelable
    · exact Or.inr ⟨rfl, by simp⟩
    · exact Or.inl ⟨rfl, by simp⟩
  | removeListener k => exact ⟨removeListenerAt_spec s k, rfl⟩
  | addListener tgt ty src cap =>
    dsimp only
    cases h : s.listeners[src]? with
    | none => exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
    | some source => exact ⟨rfl, Or.inr ⟨source, rfl, addListener_spec _ _⟩⟩

theorem callbackRan_eq {s s' : DOMState} {e e' : EventState} {l : EventListener}
    (h : CallbackRan s e l s' e') : (s', e') = runAction s e l := by
  unfold CallbackRan at h
  unfold runAction
  cases ha : l.action with
  | none => rw [ha] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | stopPropagation => rw [ha] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | stopImmediatePropagation => rw [ha] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | preventDefault =>
    rw [ha] at h
    obtain ⟨rfl, ⟨hc, rfl⟩ | ⟨hc, rfl⟩⟩ := h <;> simp [hc]
  | removeListener k =>
    rw [ha] at h
    obtain ⟨hr, rfl⟩ := h
    rw [listenerRemovedAt_eq hr]
  | addListener tgt ty src cap =>
    rw [ha] at h
    obtain ⟨rfl, ⟨hn, rfl⟩ | ⟨source, hs, hadd⟩⟩ := h
    · simp [hn]
    · simp only [hs]
      rw [listenerAdded_eq hadd]

/-! ## step 2.5（once） -/

theorem onceRemoved_spec (s : DOMState) (l : EventListener) (i : Nat) :
    (l.once = true ∧ ListenerRemovedAt s (if l.once then removeListenerAt s i else s) i) ∨
      (l.once = false ∧ (if l.once then removeListenerAt s i else s) = s) := by
  cases h : l.once
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, removeListenerAt_spec s i⟩

theorem onceRemoved_eq {s s₁ : DOMState} {l : EventListener} {i : Nat}
    (h : (l.once = true ∧ ListenerRemovedAt s s₁ i) ∨ (l.once = false ∧ s₁ = s)) :
    s₁ = if l.once then removeListenerAt s i else s := by
  rcases h with ⟨ho, hr⟩ | ⟨ho, rfl⟩
  · rw [if_pos ho, listenerRemovedAt_eq hr]
  · rw [if_neg (by simp [ho])]

/-! ## inner invoke -/

theorem innerInvoke_sound (capturing : Bool) (cur : NodeId) :
    ∀ (idxs : List Nat) (s : DOMState) (e : EventState) (log : List Invocation),
      ∃ L, InnerInvoked capturing cur s e idxs (innerInvoke capturing cur s e log idxs).1
          (innerInvoke capturing cur s e log idxs).2.1 L ∧
        (innerInvoke capturing cur s e log idxs).2.2 = log ++ L
  | [], s, e, log => ⟨[], .nil, by simp [innerInvoke]⟩
  | i :: rest, s, e, log => by
    cases hl : s.listeners[i]? with
    | none =>
      obtain ⟨L, hL, he⟩ := innerInvoke_sound capturing cur rest s e log
      refine ⟨L, ?_, ?_⟩ <;> rw [innerInvoke, hl]
      · exact .gone hl hL
      · exact he
    | some l =>
      by_cases hskip : (l.removed || l.type != e.type) = true
      · obtain ⟨L, hL, he⟩ := innerInvoke_sound capturing cur rest s e log
        have hs : l.removed = true ∨ l.type ≠ e.type ∨ l.capture ≠ capturing := by
          simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at hskip
          rcases hskip with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        refine ⟨L, ?_, ?_⟩ <;> rw [innerInvoke] <;> simp only [hl, if_pos hskip]
        · exact .skip hl hs hL
        · exact he
      · have hr : l.removed = false := by simp at hskip; exact hskip.1
        have ht : l.type = e.type := by simp at hskip; exact hskip.2
        by_cases hcap : (capturing != l.capture) = true
        · obtain ⟨L, hL, he⟩ := innerInvoke_sound capturing cur rest s e log
          have hs : l.removed = true ∨ l.type ≠ e.type ∨ l.capture ≠ capturing := by
            simp only [bne_iff_ne, ne_eq] at hcap
            exact Or.inr (Or.inr (Ne.symm hcap))
          refine ⟨L, ?_, ?_⟩ <;> rw [innerInvoke] <;> simp only [hl, if_neg hskip, if_pos hcap]
          · exact .skip hl hs hL
          · exact he
        · have hc : l.capture = capturing := by
            have h' := hcap
            simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h'
            exact h'.symm
          have hcb := runAction_spec (if l.once then removeListenerAt s i else s) e l
          by_cases hst : (invokeOne s e l i).2.stopImmediate = true
          · refine ⟨[⟨l.callback, cur, e.eventPhase⟩], ?_, ?_⟩ <;>
              simp only [innerInvoke, hl, if_neg hskip, if_neg hcap, if_pos hst]
            · exact .callStop hl hr ht hc (onceRemoved_spec s l i) hcb (by simpa [invokeOne] using hst)
          · obtain ⟨L, hL, he⟩ := innerInvoke_sound capturing cur rest
              (invokeOne s e l i).1 (invokeOne s e l i).2 (log ++ [⟨l.callback, cur, e.eventPhase⟩])
            refine ⟨⟨l.callback, cur, e.eventPhase⟩ :: L, ?_, ?_⟩ <;> rw [innerInvoke] <;>
              simp only [hl, if_neg hskip, if_neg hcap, if_neg hst]
            · exact .call hl hr ht hc (onceRemoved_spec s l i) hcb (by simpa [invokeOne] using hst) hL
            · rw [he]; simp

theorem innerInvoke_complete {capturing : Bool} {cur : NodeId} {idxs : List Nat}
    {s s' : DOMState} {e e' : EventState} {L : List Invocation}
    (h : InnerInvoked capturing cur s e idxs s' e' L) :
    ∀ log, innerInvoke capturing cur s e log idxs = (s', e', log ++ L) := by
  induction h with
  | nil => intro log; rw [innerInvoke]; simp
  | gone hl _ ih => intro log; rw [innerInvoke]; simp only [hl]; exact ih log
  | @skip s₀ s₀' e₀ e₀' i rest log₀ l hl hs _ ih =>
    intro log
    rw [innerInvoke]
    simp only [hl]
    by_cases hskip : (l.removed || l.type != e₀.type) = true
    · rw [if_pos hskip]; exact ih log
    · rw [if_neg hskip]
      have h' := hskip
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not,
        Bool.not_eq_true] at h'
      rcases hs with h | h | h
      · rw [h'.1] at h; cases h
      · exact absurd h'.2 h
      · rw [if_pos (by simpa [bne_iff_ne] using Ne.symm h)]
        exact ih log
  | @call s₀ s₁ s₂ s₀' e₀ e₂ e₀' i rest log₀ l hl hr ht hc ho hcb hst _ ih =>
    intro log
    rw [innerInvoke]
    simp only [hl, hr, ht, hc, bne_self_eq_false, Bool.or_false, Bool.false_eq_true, if_false]
    have e₁ := onceRemoved_eq ho
    subst e₁
    have e₂' := callbackRan_eq hcb
    unfold invokeOne
    rw [← e₂']
    simp only [hst, Bool.false_eq_true, if_false]
    rw [ih]
    simp
  | @callStop s₀ s₁ s₂ e₀ e₂ i rest l hl hr ht hc ho hcb hst =>
    intro log
    rw [innerInvoke]
    simp only [hl, hr, ht, hc, bne_self_eq_false, Bool.or_false, Bool.false_eq_true, if_false]
    have e₁ := onceRemoved_eq ho
    subst e₁
    have e₂' := callbackRan_eq hcb
    unfold invokeOne
    rw [← e₂']
    simp [hst]

/-! ## invoke の step 6：listener list の clone -/

private theorem pairwise_zipIdx_snd {α : Type _} :
    ∀ (l : List α) (k : Nat), (l.zipIdx k).Pairwise (fun p q => p.2 < q.2)
  | [], _ => by simp
  | a :: l, k => by
    rw [List.zipIdx_cons]
    refine List.Pairwise.cons ?_ (pairwise_zipIdx_snd l (k + 1))
    rintro ⟨x, i⟩ hp
    have := (List.mem_zipIdx hp).1
    show k < i
    omega

/-- 実行側の index の列は、`item` の listener list である。 -/
theorem listenersOf_spec (s : DOMState) (item : NodeId) :
    ListenersOf s item (s.listeners.zipIdx.filterMap fun (l, i) =>
      if l.target == item && !l.removed then some i else none) := by
  refine ⟨?_, fun i => ?_⟩
  · refine List.Pairwise.filterMap _ ?_ (pairwise_zipIdx_snd s.listeners 0)
    rintro ⟨x, a⟩ ⟨y, b⟩ hab i hi j hj
    simp only at hi hj
    split at hi <;> split at hj <;> simp_all
  · rw [List.mem_filterMap]
    constructor
    · rintro ⟨⟨x, j⟩, hm, hf⟩
      simp only at hf
      split at hf
      · next hc =>
        cases hf
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
        exact ⟨x, List.mem_zipIdx_iff_getElem?.mp hm, hc.1, hc.2⟩
      · cases hf
    · rintro ⟨x, hx, ht, hr⟩
      refine ⟨(x, i), List.mem_zipIdx_iff_getElem?.mpr hx, ?_⟩
      simp [ht, hr]

theorem listenersOf_unique {s : DOMState} {item : NodeId} {a b : List Nat}
    (h₁ : ListenersOf s item a) (h₂ : ListenersOf s item b) : a = b :=
  ListUtil.eq_of_pairwise_of_mem_iff (fun x _ h => Nat.lt_irrefl x h)
    (fun _ _ _ _ h h' => Nat.lt_asymm h h') h₁.1 h₂.1
    (fun i => (h₁.2 i).trans (h₂.2 i).symm)

/-! ## invoke -/

theorem phaseOf_eq (capturing isTarget : Bool) :
    (if isTarget then EventPhase.atTarget
      else if capturing then EventPhase.capturing else EventPhase.bubbling) =
      phaseOf capturing isTarget := rfl

theorem invokeItem_sound (s : DOMState) (e : EventState) (log : List Invocation)
    (capturing : Bool) (item : NodeId) (isTarget : Bool) :
    ∃ L, Invoked s e capturing item isTarget (invokeItem s e log capturing item isTarget).1
        (invokeItem s e log capturing item isTarget).2.1 L ∧
      (invokeItem s e log capturing item isTarget).2.2 = log ++ L := by
  unfold invokeItem
  dsimp only
  rw [phaseOf_eq]
  by_cases hst : e.stopPropagation = true
  · rw [if_pos hst]
    exact ⟨[], Or.inl ⟨hst, rfl, rfl, rfl⟩, by simp⟩
  · rw [if_neg hst]
    obtain ⟨L, hL, he⟩ := innerInvoke_sound capturing item _ s
      { e with eventPhase := phaseOf capturing isTarget } log
    exact ⟨L, Or.inr ⟨by simpa using hst, _, listenersOf_spec s item, hL⟩, he⟩

theorem invokeItem_complete {s s' : DOMState} {e e' : EventState} {capturing : Bool}
    {item : NodeId} {isTarget : Bool} {L : List Invocation}
    (h : Invoked s e capturing item isTarget s' e' L) (log : List Invocation) :
    invokeItem s e log capturing item isTarget = (s', e', log ++ L) := by
  unfold invokeItem
  dsimp only
  rw [phaseOf_eq]
  rcases h with ⟨hst, rfl, rfl, rfl⟩ | ⟨hst, idxs, hidx, hL⟩
  · rw [if_pos hst]; simp
  · rw [if_neg (by simp [hst])]
    rw [listenersOf_unique (listenersOf_spec s item) hidx]
    exact innerInvoke_complete hL log

/-! ## dispatch の二周 -/

private theorem beq_eq_decide (a b : NodeId) : (a == b) = decide (a = b) := by
  by_cases h : a = b <;> simp [h]

theorem runPass_sound (capturing : Bool) (target : NodeId) :
    ∀ (path : List NodeId) (s : DOMState) (e : EventState) (log : List Invocation),
      ∃ L, PassRan capturing target s e path (runPass capturing target s e log path).1
          (runPass capturing target s e log path).2.1 L ∧
        (runPass capturing target s e log path).2.2 = log ++ L
  | [], s, e, log => ⟨[], .nil, by simp [runPass]⟩
  | item :: rest, s, e, log => by
    by_cases hskip : (!capturing && !(item == target) && !e.bubbles) = true
    · have hskip' := hskip
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hskip'
      obtain ⟨⟨hc, hne⟩, hb⟩ := hskip'
      obtain ⟨L, hL, he⟩ := runPass_sound capturing target rest s e log
      refine ⟨L, ?_, ?_⟩ <;> rw [runPass, if_pos hskip]
      · exact .skip hc (by simpa using hne) hb hL
      · exact he
    · obtain ⟨L₁, hL₁, he₁⟩ := invokeItem_sound s e log capturing item (item == target)
      obtain ⟨L₂, hL₂, he₂⟩ := runPass_sound capturing target rest
        (invokeItem s e log capturing item (item == target)).1
        (invokeItem s e log capturing item (item == target)).2.1
        (invokeItem s e log capturing item (item == target)).2.2
      refine ⟨L₁ ++ L₂, ?_, ?_⟩ <;> rw [runPass] <;> rw [if_neg hskip]
      · refine .invoke ?_ (by rw [← beq_eq_decide]; exact hL₁) hL₂
        intro ⟨h1, h2, h3⟩
        exact hskip (by simp [h1, h2, h3])
      · rw [he₂, he₁]; simp

theorem runPass_complete {capturing : Bool} {target : NodeId} {path : List NodeId}
    {s s' : DOMState} {e e' : EventState} {L : List Invocation}
    (h : PassRan capturing target s e path s' e' L) :
    ∀ log, runPass capturing target s e log path = (s', e', log ++ L) := by
  induction h with
  | nil => intro log; simp [runPass]
  | skip hc hne hb _ ih =>
    intro log
    rw [runPass, if_pos (by simp [hc, hne, hb])]
    exact ih log
  | @invoke s₀ s₁ s₀' e₀ e₁ e₀' item rest log₁ log₂ hns hinv _ ih =>
    intro log
    rw [runPass, if_neg (by
      intro h'
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h'
      exact hns ⟨h'.1.1, by simpa using h'.1.2, h'.2⟩)]
    rw [beq_eq_decide, invokeItem_complete hinv log]
    dsimp only
    rw [ih]
    simp

/-! ## event path -/

theorem ancestors_eq_nil {t : Tree} {n : NodeId} (h : parentOf t n = none) : ancestors t n = [] := by
  unfold ancestors
  cases t.size with
  | zero => rfl
  | succ k => simp [ancestorChain, h]

theorem eventPath_spec {t : Tree} (hwf : WellFormed t) :
    ∀ (k : Nat) (n : NodeId), (ancestors t n).length ≤ k → EventPathSpec t n (eventPath t n)
  | 0, n, hk => by
    cases hp : parentOf t n with
    | none => unfold eventPath; rw [ancestors_eq_nil hp]; exact .last hp
    | some p => rw [ancestors_eq_cons hwf hp] at hk; simp at hk
  | k + 1, n, hk => by
    cases hp : parentOf t n with
    | none => unfold eventPath; rw [ancestors_eq_nil hp]; exact .last hp
    | some p =>
      have hc := ancestors_eq_cons hwf hp
      rw [hc] at hk
      simp only [List.length_cons] at hk
      have ih := eventPath_spec hwf k p (by omega)
      unfold eventPath at ih ⊢
      rw [hc]
      exact .cons hp ih

theorem eventPathSpec_eq {t : Tree} (hwf : WellFormed t) {n : NodeId} {path : List NodeId}
    (h : EventPathSpec t n path) : path = eventPath t n := by
  induction h with
  | last hp => unfold eventPath; rw [ancestors_eq_nil hp]
  | cons hp _ ih => unfold eventPath at ih ⊢; rw [ancestors_eq_cons hwf hp, ih]

/-! ## 全体 -/

/-- **`dispatchEvent` の結果は関係を満たす。** -/
theorem dispatchEvent_result_sound {s : DOMState} (hwf : WellFormed s.tree) (target : NodeId)
    («type» : String) (bubbles cancelable : Bool) :
    DispatchResult s target «type» bubbles cancelable
      (dispatchEvent s target «type» bubbles cancelable) := by
  unfold dispatchEvent
  cases hd : s.tree.get? target with
  | none => exact ⟨hd, rfl⟩
  | some d =>
    dsimp only
    obtain ⟨L₁, h₁, he₁⟩ := runPass_sound true target (eventPath s.tree target).reverse s
      { «type» := «type», bubbles := bubbles, cancelable := cancelable } []
    obtain ⟨L₂, h₂, he₂⟩ := runPass_sound false target (eventPath s.tree target)
      (runPass true target s { «type» := «type», bubbles := bubbles, cancelable := cancelable } []
        (eventPath s.tree target).reverse).1
      (runPass true target s { «type» := «type», bubbles := bubbles, cancelable := cancelable } []
        (eventPath s.tree target).reverse).2.1
      (runPass true target s { «type» := «type», bubbles := bubbles, cancelable := cancelable } []
        (eventPath s.tree target).reverse).2.2
    refine ⟨⟨d, hd⟩, _, _, _, _, L₁, L₂, eventPath_spec hwf _ target (Nat.le_refl _), h₁, h₂,
      ?_, rfl⟩
    rw [he₂, he₁]
    simp

/-- **関係を満たす結果は、`dispatchEvent` の結果と等しい。** -/
theorem dispatchEvent_result_complete {s : DOMState} (hwf : WellFormed s.tree) {target : NodeId}
    {«type» : String} {bubbles cancelable : Bool}
    {r : Except DOMException (DOMState × Bool × List Invocation)}
    (h : DispatchResult s target «type» bubbles cancelable r) :
    r = dispatchEvent s target «type» bubbles cancelable := by
  unfold dispatchEvent
  rcases r with e | ⟨s', ret, log⟩
  · obtain ⟨hn, rfl⟩ := h
    rw [hn]
  · obtain ⟨⟨d, hd⟩, path, s₁, e₁, e₂, log₁, log₂, hp, h₁, h₂, rfl, rfl⟩ := h
    rw [hd]
    dsimp only
    rw [← eventPathSpec_eq hwf hp, runPass_complete h₁ []]
    simp only [List.nil_append]
    rw [runPass_complete h₂ log₁]

/-- **関係は結果を一つに決める。** -/
theorem dispatchEvent_result_deterministic {s : DOMState} (hwf : WellFormed s.tree)
    {target : NodeId} {«type» : String} {bubbles cancelable : Bool}
    {r₁ r₂ : Except DOMException (DOMState × Bool × List Invocation)}
    (h₁ : DispatchResult s target «type» bubbles cancelable r₁)
    (h₂ : DispatchResult s target «type» bubbles cancelable r₂) : r₁ = r₂ :=
  (dispatchEvent_result_complete hwf h₁).trans (dispatchEvent_result_complete hwf h₂).symm

/-! ## `addEventListener` / `removeEventListener` -/

theorem addEventListener_result_sound (s : DOMState) (target : NodeId) («type» : String)
    (source : Nat) (capture once : Bool) :
    AddEventListenerResult s target «type» source capture once
      (addEventListener s target «type» source capture once) := by
  unfold addEventListener
  cases hd : s.tree.get? target with
  | none => exact ⟨Or.inl hd, rfl⟩
  | some d =>
    cases hs : s.listeners[source]? with
    | none => exact ⟨Or.inr hs, rfl⟩
    | some src => exact ⟨⟨d, hd⟩, src, hs, addListener_spec _ _⟩

theorem addEventListener_result_complete {s : DOMState} {target : NodeId} {«type» : String}
    {source : Nat} {capture once : Bool} {r : Except DOMException DOMState}
    (h : AddEventListenerResult s target «type» source capture once r) :
    r = addEventListener s target «type» source capture once := by
  unfold addEventListener
  rcases r with e | s'
  · obtain ⟨hn | hn, rfl⟩ := h
    · rw [hn]
    · cases hd : s.tree.get? target with
      | none => rfl
      | some d => simp only [hn]
  · obtain ⟨⟨d, hd⟩, src, hs, hadd⟩ := h
    simp only [hd, hs]
    rw [listenerAdded_eq hadd]

private theorem find?_match_iff (target : NodeId) («type» : String)
    (callback : Nat) (capture : Bool) (l : EventListener) :
    (!l.removed && l.target == target && l.type == «type» && l.callback == callback &&
        l.capture == capture) = true ↔ ListenerMatches l target «type» callback capture := by
  unfold ListenerMatches
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq, and_assoc]

/-- `zipIdx` の中で最初に当たるもの。 -/
private theorem find?_zipIdx_some {p : EventListener → Bool} :
    ∀ (L : List EventListener) (k : Nat) (x : EventListener) (i : Nat),
      (L.zipIdx k).find? (fun q => p q.1) = some (x, i) →
      k ≤ i ∧ L[i - k]? = some x ∧ p x = true ∧ ∀ j y, j < i - k → L[j]? = some y → p y = false
  | [], _, _, _, h => by simp at h
  | a :: L, k, x, i, h => by
    rw [List.zipIdx_cons] at h
    by_cases ha : p a = true
    · simp only [List.find?_cons, ha, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨Nat.le_refl _, by simp, ha, fun j y hj => by omega⟩
    · simp only [List.find?_cons, ha] at h
      obtain ⟨hk, hx, hp, hfirst⟩ := find?_zipIdx_some L (k + 1) x i h
      refine ⟨by omega, ?_, hp, fun j y hj hy => ?_⟩
      · rw [show i - k = (i - (k + 1)) + 1 by omega]; simpa using hx
      · cases j with
        | zero => simp at hy; rw [← hy]; simpa using ha
        | succ j => exact hfirst j y (by omega) (by simpa using hy)

private theorem find?_zipIdx_none {p : EventListener → Bool} :
    ∀ (L : List EventListener) (k : Nat), (L.zipIdx k).find? (fun q => p q.1) = none →
      ∀ x ∈ L, p x = false
  | [], _, _ => by simp
  | a :: L, k, h => by
    rw [List.zipIdx_cons] at h
    by_cases ha : p a = true
    · simp only [List.find?_cons, ha] at h; cases h
    · simp only [List.find?_cons, ha] at h
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simpa using ha
      · exact find?_zipIdx_none L (k + 1) h x hx

theorem removeEventListener_result_sound (s : DOMState) (target : NodeId) («type» : String)
    (callback : Nat) (capture : Bool) :
    RemoveEventListenerResult s target «type» callback capture
      (removeEventListener s target «type» callback capture) := by
  unfold removeEventListener
  cases hd : s.tree.get? target with
  | none => exact ⟨hd, rfl⟩
  | some d =>
    have hm := find?_match_iff target «type» callback capture
    cases hf : (s.listeners.zipIdx.find? fun (l, _) =>
        !l.removed && l.target == target && l.type == «type» && l.callback == callback &&
          l.capture == capture) with
    | none =>
      refine ⟨⟨d, hd⟩, Or.inl ⟨?_, rfl⟩⟩
      rintro ⟨l, hl, hml⟩
      have := find?_zipIdx_none (p := fun l => !l.removed && l.target == target &&
        l.type == «type» && l.callback == callback && l.capture == capture) s.listeners 0 hf l hl
      rw [(hm l).mpr hml] at this
      cases this
    | some pr =>
      obtain ⟨x, i⟩ := pr
      obtain ⟨-, hx, hp, hfirst⟩ := find?_zipIdx_some (p := fun l => !l.removed &&
        l.target == target && l.type == «type» && l.callback == callback && l.capture == capture)
        s.listeners 0 x i hf
      simp only [Nat.sub_zero] at hx hfirst
      refine ⟨⟨d, hd⟩, Or.inr ⟨i, x, hx, (hm x).mp hp, fun j y hj hy hmy => ?_,
        removeListenerAt_spec s i⟩⟩
      have := hfirst j y hj hy
      rw [(hm y).mpr hmy] at this
      cases this

theorem removeEventListener_result_complete {s : DOMState} {target : NodeId} {«type» : String}
    {callback : Nat} {capture : Bool} {r : Except DOMException DOMState}
    (h : RemoveEventListenerResult s target «type» callback capture r) :
    r = removeEventListener s target «type» callback capture := by
  have hs := removeEventListener_result_sound s target «type» callback capture
  rcases r with e | s'
  · obtain ⟨hn, rfl⟩ := h
    unfold removeEventListener; rw [hn]
  · cases hr : removeEventListener s target «type» callback capture with
    | error e => rw [hr] at hs; obtain ⟨hn, -⟩ := hs; obtain ⟨⟨d, hd⟩, -⟩ := h; rw [hn] at hd; cases hd
    | ok s₂ =>
      rw [hr] at hs
      obtain ⟨-, h₁⟩ := h
      obtain ⟨-, h₂⟩ := hs
      -- 最初に当たるものは一つに決まる
      congr 1
      rcases h₁ with ⟨hn₁, rfl⟩ | ⟨i, l, hl, hml, hf, hrm⟩ <;>
        rcases h₂ with ⟨hn₂, rfl⟩ | ⟨i', l', hl', hml', hf', hrm'⟩
      · rfl
      · exact absurd ⟨l', List.mem_of_getElem? hl', hml'⟩ hn₁
      · exact absurd ⟨l, List.mem_of_getElem? hl, hml⟩ hn₂
      · have hii : i = i' := by
          rcases Nat.lt_trichotomy i i' with h | h | h
          · exact absurd hml (hf' i l h hl)
          · exact h
          · exact absurd hml' (hf i' l' h hl')
        subst hii
        rw [listenerRemovedAt_eq hrm, listenerRemovedAt_eq hrm']

end Dom.Spec
