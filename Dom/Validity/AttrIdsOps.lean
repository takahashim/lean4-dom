import Dom.Validity.AttrIds
import Dom.CharacterData.Normalize
import Dom.Range.Api
import Dom.Validity.Events
import Dom.Validity.Walkers
import Dom.Observer.Deliver

/-!
# attribute の id の配置を変えない操作

normalize、Range、traversal、event、MutationObserver の操作は、attribute list にも
detach された `Attr` の list にも触れない（`AttrFrame`）。
-/

namespace Dom

/-! ## normalize -/

theorem attrFrame_normalizeMergeOne {s s' : DOMState} {survivor sib : NodeId}
    (h : normalizeMergeOne s survivor sib = .ok s') : AttrFrame s s' := by
  unfold normalizeMergeOne at h
  split at h
  · next dsurv dsib parent idx _ _ _ _ =>
    by_cases hbad : (survivor == sib || dsurv.kind != NodeKind.text ||
        dsib.kind != NodeKind.text) = true
    · simp only [hbad, if_true] at h; cases h
    · simp only [hbad, Bool.false_eq_true, if_false] at h
      have tail : ∀ s₁ s₂ : DOMState, AttrFrame s s₁ →
          s₂ = { s₁ with
            ranges := s₁.ranges.map (normalizeMergeRange survivor sib parent idx dsurv.length) } →
          remove s₂ sib = .ok s' → AttrFrame s s' := by
        intro s₁ s₂ h₁ hs₂ hr
        exact (h₁.trans (AttrFrame.of_eq (by rw [hs₂]) (by rw [hs₂]))).trans (attrFrame_remove hr)
      by_cases hemp : dsib.data.isEmpty = true
      · simp only [hemp, if_true] at h
        exact tail s _ (AttrFrame.refl _) rfl h
      · simp only [hemp, Bool.false_eq_true, if_false] at h
        cases hrd : replaceData s survivor dsurv.length 0 dsib.data with
        | error e => rw [hrd] at h; cases h
        | ok s₁ =>
          rw [hrd] at h
          exact tail s₁ _ (attrFrame_replaceData hrd) rfl h
  · cases h

theorem attrFrame_normalizeRun {survivor : NodeId} :
    ∀ (sibs : List NodeId) {s s' : DOMState}, normalizeRun s survivor sibs = .ok s' →
      AttrFrame s s'
  | [], s, s', h => by rw [normalizeRun] at h; cases h; exact AttrFrame.refl _
  | sib :: rest, s, s', h => by
    rw [normalizeRun] at h
    split at h
    · cases h
    · next s₁ hm => exact (attrFrame_normalizeMergeOne hm).trans (attrFrame_normalizeRun rest h)

theorem attrFrame_normalizeList (this : NodeId) :
    ∀ (cands : List NodeId) {s s' : DOMState}, normalizeList s this cands = .ok s' →
      AttrFrame s s'
  | [], s, s', h => by rw [normalizeList] at h; cases h; exact AttrFrame.refl _
  | n :: rest, s, s', h => by
    rw [normalizeList] at h
    split at h
    · split at h
      · exact attrFrame_normalizeList this rest h
      · split at h
        · split at h
          · cases h
          · next s₁ hr => exact (attrFrame_remove hr).trans (attrFrame_normalizeList this rest h)
        · split at h
          · cases h
          · next s₁ hr =>
            exact (attrFrame_normalizeRun _ hr).trans (attrFrame_normalizeList this rest h)
    · exact attrFrame_normalizeList this rest h

theorem attrFrame_normalize {s s' : DOMState} {n : NodeId} (h : normalize s n = .ok s') :
    AttrFrame s s' := by
  unfold normalize at h
  split at h
  · cases h
  · exact attrFrame_normalizeList _ _ h

/-! ## Range -/

theorem attrFrame_withRange (s : DOMState) (i : Nat) (r : RangeState) :
    AttrFrame s (withRange s i r) := AttrFrame.of_eq rfl rfl

/-- 木と detach された list を変えない形の結果。 -/
private theorem frame_tac {s s' : DOMState} (ht : s'.tree = s.tree)
    (hd : s'.detachedAttrs = s.detachedAttrs) : AttrFrame s s' := AttrFrame.of_eq ht hd

theorem attrFrame_rangeSetStart {s s' : DOMState} {i : Nat} {bp : BoundaryPoint}
    (h : rangeSetStart s i bp = .ok s') : AttrFrame s s' := by
  unfold rangeSetStart at h
  repeat' split at h
  all_goals first | (cases h; exact attrFrame_withRange ..) | (cases h; done)

theorem attrFrame_rangeSetEnd {s s' : DOMState} {i : Nat} {bp : BoundaryPoint}
    (h : rangeSetEnd s i bp = .ok s') : AttrFrame s s' := by
  unfold rangeSetEnd at h
  repeat' split at h
  all_goals first | (cases h; exact attrFrame_withRange ..) | (cases h; done)

theorem attrFrame_rangeSetStartSibling {s s' : DOMState} {i : Nat} {n : NodeId} {a : Bool}
    (h : rangeSetStartSibling s i n a = .ok s') : AttrFrame s s' := by
  unfold rangeSetStartSibling at h
  split at h
  · cases h
  · exact attrFrame_rangeSetStart h

theorem attrFrame_rangeSetEndSibling {s s' : DOMState} {i : Nat} {n : NodeId} {a : Bool}
    (h : rangeSetEndSibling s i n a = .ok s') : AttrFrame s s' := by
  unfold rangeSetEndSibling at h
  split at h
  · cases h
  · exact attrFrame_rangeSetEnd h

theorem attrFrame_rangeCollapse {s s' : DOMState} {i : Nat} {b : Bool}
    (h : rangeCollapse s i b = .ok s') : AttrFrame s s' := by
  unfold rangeCollapse at h
  repeat' split at h
  all_goals first | (cases h; exact attrFrame_withRange ..) | (cases h; done)

theorem attrFrame_rangeSelectNode {s s' : DOMState} {i : Nat} {n : NodeId}
    (h : rangeSelectNode s i n = .ok s') : AttrFrame s s' := by
  unfold rangeSelectNode at h
  repeat' split at h
  all_goals first | (cases h; exact attrFrame_withRange ..) | (cases h; done)

theorem attrFrame_rangeSelectNodeContents {s s' : DOMState} {i : Nat} {n : NodeId}
    (h : rangeSelectNodeContents s i n = .ok s') : AttrFrame s s' := by
  unfold rangeSelectNodeContents at h
  repeat' split at h
  all_goals first | (cases h; exact attrFrame_withRange ..) | (cases h; done)

theorem attrFrame_rangeDeleteContents {s s' : DOMState} {i : Nat}
    (h : rangeDeleteContents s i = .ok s') : AttrFrame s s' := by
  unfold rangeDeleteContents at h
  split at h
  · cases h
  · split at h
    · cases h; exact AttrFrame.refl _
    · split at h
      · split at h
        · exact attrFrame_replaceData h
        · split at h
          · cases h
          · next s₁ hs₁ =>
            have h₁ : AttrFrame s s₁ := by
              split at hs₁
              · exact attrFrame_replaceData hs₁
              · cases hs₁; exact AttrFrame.refl _
            dsimp only at h
            cases hs₂ : removeEach s₁ (nodesToRemove s.tree _) with
            | error e => rw [hs₂] at h; cases h
            | ok s₂ =>
              rw [hs₂] at h
              dsimp only at h
              have h₂ := h₁.trans (attrFrame_removeEach _ hs₂)
              split at h
              · cases h
              · next s₃ hs₃ =>
                have h₃ : AttrFrame s s₃ := by
                  split at hs₃
                  · exact h₂.trans (attrFrame_replaceData hs₃)
                  · cases hs₃; exact h₂
                split at h
                · cases h
                · cases h; exact h₃.trans (attrFrame_withRange ..)
      · cases h

theorem attrFrame_rangeInsertNode {s s' : DOMState} {i : Nat} {n : NodeId}
    (h : rangeInsertNode s i n = .ok s') : AttrFrame s s' := by
  unfold rangeInsertNode at h
  split at h
  · cases h
  · next r hr =>
    split at h
    · cases h
    · next ds hds =>
      split at h
      · cases h
      · split at h
        · repeat' split at h
          all_goals cases h
        · simp only [] at h
          cases hv : ensurePreInsertionValidity s.tree n r.start.node ds.children[r.start.offset]? []
            with
          | error e => rw [hv] at h; simp at h
          | ok u =>
            rw [hv] at h
            simp only [] at h
            cases hrm : (if (parentOf s.tree n).isSome = true then remove s n else Except.ok s) with
            | error e => rw [hrm] at h; simp at h
            | ok s₁ =>
              rw [hrm] at h
              have h₁ : AttrFrame s s₁ := by
                split at hrm
                · exact attrFrame_remove hrm
                · cases hrm; exact AttrFrame.refl _
              simp only [] at h
              split at h
              · simp at h
              · next s₂ hp =>
                have h₂ := h₁.trans (attrFrame_preInsert hp)
                repeat' split at h
                all_goals first
                  | (cases h; exact h₂.trans (attrFrame_withRange ..))
                  | (cases h; exact h₂)
                  | (cases h; done)

/-! ## 木を変えない操作 -/

theorem attrFrame_of_listenersOnly {s s' : DOMState} (h : ListenersOnly s s') : AttrFrame s s' := by
  unfold ListenersOnly at h
  rw [← h]
  exact AttrFrame.of_eq rfl rfl

theorem attrFrame_observe {s s' : DOMState} {mo : Nat} {target : NodeId}
    {opts : MutationObserverInit} (h : MutationObserver.observe s mo target opts = .ok s') :
    AttrFrame s s' := by
  unfold MutationObserver.observe at h
  repeat' split at h
  all_goals first
    | (subst h; exact AttrFrame.of_eq rfl rfl)
    | (rw [← Except.ok.inj h]; exact AttrFrame.of_eq rfl rfl)
    | simp at h

theorem attrFrame_disconnect (s : DOMState) (mo : Nat) :
    AttrFrame s (MutationObserver.disconnect s mo) := AttrFrame.of_eq rfl rfl

theorem attrFrame_takeRecords (s : DOMState) (mo : Nat) :
    AttrFrame s (MutationObserver.takeRecords s mo).1 := by
  unfold MutationObserver.takeRecords
  split <;> exact AttrFrame.of_eq rfl rfl

theorem attrFrame_notifyEach : ∀ (l : List Nat) (s : DOMState), AttrFrame s (notifyEach s l).1
  | [], s => AttrFrame.refl s
  | mo :: rest, s => by
    unfold notifyEach notifyOne
    have h₁ : AttrFrame s (removeTransients (MutationObserver.takeRecords s mo).1 mo) :=
      (attrFrame_takeRecords s mo).trans (AttrFrame.of_eq rfl rfl)
    exact h₁.trans (attrFrame_notifyEach rest _)

theorem attrFrame_notifyMutationObservers (s : DOMState) :
    AttrFrame s (notifyMutationObservers s).1 := by
  show AttrFrame s (notifyEach { s with microtaskQueued := false, pendingObservers := [] }
    s.pendingObservers).1
  exact (AttrFrame.of_eq (s := s) (s' := { s with microtaskQueued := false, pendingObservers := [] })
    rfl rfl).trans (attrFrame_notifyEach _ _)

theorem attrFrame_walkerStep {s s' : DOMState} {i : Nat} {m : WalkerMethod} {r : Option NodeId}
    (h : walkerStep s i m = .ok (r, s')) : AttrFrame s s' := by
  unfold walkerStep walkerRun at h
  repeat' split at h
  all_goals first
    | (cases h; exact AttrFrame.refl _)
    | (cases h; exact AttrFrame.of_eq rfl rfl)
    | (cases h; done)

theorem attrFrame_addEventListener {s s' : DOMState} {target : NodeId} {ty : String} {src : Nat}
    {cap : Bool} {passive : Option Bool} {once : Bool}
    (h : addEventListener s target ty src cap passive once = .ok s') : AttrFrame s s' := by
  unfold addEventListener at h
  repeat' split at h
  all_goals first
    | (cases h; exact attrFrame_of_listenersOnly (listenersOnly_addListener s _))
    | (cases h; done)

theorem attrFrame_removeEventListener {s s' : DOMState} {target : NodeId} {ty : String} {cb : Nat}
    {cap : Bool} (h : removeEventListener s target ty cb cap = .ok s') : AttrFrame s s' := by
  unfold removeEventListener at h
  repeat' split at h
  all_goals first
    | (cases h; exact AttrFrame.refl _)
    | (cases h; exact attrFrame_of_listenersOnly (listenersOnly_removeListenerAt s _))
    | (cases h; done)

theorem attrFrame_dispatchEvent {s s' : DOMState} {target : NodeId} {ty : String}
    {b c r : Bool} {log : List Invocation}
    (h : dispatchEvent s target ty b c = .ok (s', r, log)) : AttrFrame s s' :=
  attrFrame_of_listenersOnly (listenersOnly_dispatchEvent h)

end Dom
