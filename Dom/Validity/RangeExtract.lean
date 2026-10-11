import Dom.Range.Extract
import Dom.Validity.Variadic
import Dom.Validity.Clone
import Dom.Validity.SplitText
import Dom.Validity.AttrIdsOps

/-!
# `insertNode`・extract・clone the contents・`surroundContents()` は妥当性を保つ

どれも既に保存を示した部品（`splitText`、`append`、`replaceData`、clone、`withRange`、
`replaceAll`、`selectNode`、`discard`）の合成である。証明は部品で閉じた性質 `P`（`RangeClosed`）について
一度だけ行い、admissibility と、admissibility と attribute の id の一意性の組（`Good`）に当てる。
-/

namespace Dom

/-! ## 部品で閉じた性質 -/

/-- extract と clone the contents の部品で閉じた性質。 -/
structure ContentsClosed (P : DOMState → Prop) : Prop where
  append : ∀ {s s' : DOMState} {n p : NodeId}, P s → append s n p = .ok s' → P s'
  replaceData : ∀ {s s' : DOMState} {n : NodeId} {o c : Nat} {d : String}, P s →
    replaceData s n o c d = .ok s' → P s'
  withRange : ∀ {s : DOMState} {i : Nat} {r : RangeState}, P s → EndpointsValid s.tree r →
    P (withRange s i r)
  cloneSingleData : ∀ {s : DOMState} {n : NodeId} {d : NodeData} (x : String), P s →
    s.tree.get? n = some d → P (cloneSingle s { d with data := x } d.ownerDocument).2
  cloneNodeIn : ∀ {s s' : DOMState} {n c : NodeId} {d : NodeData}, P s → s.tree.get? n = some d →
    cloneNodeIn s n d.ownerDocument true = .ok (c, s') → P s'

/-- extract・clone the contents・`insertNode`・`surroundContents()` の部品で閉じた性質。 -/
structure RangeClosed (P : DOMState → Prop) : Prop extends ContentsClosed P where
  discard : ∀ {s : DOMState} (n : NodeId), P s → P (discard s n)
  fragment : ∀ {s s' : DOMState} {r : RangeState} {frag : NodeId}, P s →
    rangeFragment s r = .ok (frag, s') → P s'
  splitText : ∀ {s s' : DOMState} {n t : NodeId} {o : Nat}, P s → splitText s n o = .ok (t, s') → P s'
  insertTail : ∀ {s s' : DOMState} {i : Nat} {p n : NodeId} {ref : Option NodeId}, P s →
    rangeInsertNodeTail s i p n ref = .ok s' → P s'
  replaceAllNone : ∀ {s s' : DOMState} {p : NodeId}, P s → replaceAll s none p = .ok s' → P s'
  selectNode : ∀ {s s' : DOMState} {i : Nat} {n : NodeId}, P s → rangeSelectNode s i n = .ok s' → P s'

/-- `failWith` は成功の値を変えない。 -/
@[simp] theorem failWith_ok {α : Type} {s : DOMState} {r : Except DOMException α} {a : α} :
    failWith s r = .ok a ↔ r = .ok a := by
  cases r <;> simp [failWith]

theorem ok_of_discardFragmentOnError {α : Type} {base frag : NodeId}
    {r : Except (DOMException × DOMState) α} {a : α} (h : discardFragmentOnError base frag r = .ok a) :
    r = .ok a := by
  unfold discardFragmentOnError at h
  split at h
  · simp at h
  · exact h

theorem ok_of_discardOnError {α : Type} {frag : NodeId} {r : Except (DOMException × DOMState) α}
    {a : α} (h : discardOnError frag r = .ok a) : r = .ok a := by
  unfold discardOnError at h
  split at h
  · simp at h
  · exact h

/-- 再帰が `P` を保つこと。 -/
def RecurClosed (P : DOMState → Prop) (recur : Recur) : Prop :=
  ∀ s r c s', P s → recur s r c = .ok s' → P s'

section
variable {P : DOMState → Prop} (hC : ContentsClosed P)
include hC

/-! ## extract と clone the contents -/

theorem closed_appendDataClone {s s' : DOMState} {n into : NodeId} {d : NodeData} {x : String}
    (h : P s) (hd : s.tree.get? n = some d) (hr : appendDataClone s d x into = .ok s') :
    P s' := by
  unfold appendDataClone at hr
  rcases hcs : cloneSingle s { d with data := x } d.ownerDocument with ⟨c, s₁⟩
  have h₁ : P s₁ := by have := hC.cloneSingleData x h hd; rw [hcs] at this; exact this
  simp only [hcs] at hr
  split at hr
  · simp at hr
  · next s₂ ha => cases hr; exact hC.append h₁ ha

theorem closed_appendShallowClone {s s' : DOMState} {n c into : NodeId} {d : NodeData}
    (h : P s) (hd : s.tree.get? n = some d) (hr : appendShallowClone s d into = .ok (c, s')) :
    P s' := by
  unfold appendShallowClone at hr
  rcases hcs : cloneSingle s d d.ownerDocument with ⟨c₀, s₁⟩
  have h₁ : P s₁ := by
    have := hC.cloneSingleData d.data h hd
    rw [show ({ d with data := d.data } : NodeData) = d from rfl, hcs] at this
    exact this
  simp only [hcs] at hr
  split at hr
  · simp at hr
  · next s₂ ha => cases hr; exact hC.append h₁ ha

theorem closed_dataPart {s s' : DOMState} {cut : Bool} {n into : NodeId} {o c : Nat}
    (h : P s) (hr : dataPart cut s n o c into = .ok s') : P s' := by
  unfold dataPart at hr
  split at hr
  · simp at hr
  · next d hd =>
    split at hr
    · simp at hr
    split at hr
    · simp at hr
    · split at hr
      · simp at hr
      · next s₁ ha =>
        have h₁ := closed_appendDataClone hC h hd ha
        split at hr
        · exact hC.replaceData h₁ (failWith_ok.mp hr)
        · cases hr; exact h₁

theorem closed_appendEach {into : NodeId} :
    ∀ (cs : List NodeId) {s s' : DOMState}, P s → appendEach s into cs = .ok s' → P s'
  | [], s, s', h, hr => by cases hr; exact h
  | c :: cs, s, s', h, hr => by
    unfold appendEach at hr
    split at hr
    · simp at hr
    · next s₁ ha => exact closed_appendEach cs (hC.append h ha) hr

theorem closed_cloneEach {into : NodeId} :
    ∀ (cs : List NodeId) {s s' : DOMState}, P s → cloneEach s into cs = .ok s' → P s'
  | [], s, s', h, hr => by cases hr; exact h
  | c :: cs, s, s', h, hr => by
    unfold cloneEach at hr
    split at hr
    · simp at hr
    · next cd hcd =>
      split at hr
      · simp at hr
      · next copy s₁ hc =>
        split at hr
        · simp at hr
        · next s₂ ha => exact closed_cloneEach cs (hC.append (hC.cloneNodeIn h hcd hc) ha) hr

theorem closed_setSelf {s s' : DOMState} {self : Option Nat} {bp : BoundaryPoint} (h : P s)
    (hr : setSelf s self bp = .ok s') : P s' := by
  unfold setSelf at hr
  split at hr
  · cases hr; exact h
  · split at hr
    · next hv =>
      cases hr
      have := (checkValidBoundaryPoint_iff _ _).mp hv
      exact hC.withRange h ⟨this, this⟩
    · simp at hr

theorem closed_partialFirst {cut : Bool} {recur : Recur} {s s' : DOMState} {r : RangeState}
    {fp : Option NodeId} {into : NodeId} (hrec : RecurClosed P recur) (h : P s)
    (hr : partialFirst cut recur s r fp into = .ok s') : P s' := by
  unfold partialFirst at hr
  split at hr
  · cases hr; exact h
  · split at hr
    · simp at hr
    · next fd hfd =>
      split at hr
      · exact closed_dataPart hC h hr
      · split at hr
        · simp at hr
        · next c s₁ ha => exact hrec _ _ _ _ (closed_appendShallowClone hC h hfd ha) hr

theorem closed_partialLast {cut : Bool} {recur : Recur} {s s' : DOMState} {r : RangeState}
    {lp : Option NodeId} {into : NodeId} (hrec : RecurClosed P recur) (h : P s)
    (hr : partialLast cut recur s r lp into = .ok s') : P s' := by
  unfold partialLast at hr
  split at hr
  · cases hr; exact h
  · split at hr
    · simp at hr
    · next ld hld =>
      split at hr
      · exact closed_dataPart hC h hr
      · split at hr
        · simp at hr
        · next c s₁ ha => exact hrec _ _ _ _ (closed_appendShallowClone hC h hld ha) hr

/-- **extract と clone the contents は妥当性を保つ。** -/
theorem closed_contentsInto (cut : Bool) :
    ∀ (fuel : Nat) {s s' : DOMState} {r : RangeState} {self : Option Nat} {into : NodeId},
      P s → contentsInto cut fuel s r self into = .ok s' → P s'
  | 0, s, s', r, self, into, h, hr => by simp [contentsInto] at hr
  | fuel + 1, s, s', r, self, into, h, hr => by
    have hrec : RecurClosed P (fun s' r' c => contentsInto cut fuel s' r' none c) :=
      fun _ _ _ _ hg hc => closed_contentsInto cut fuel hg hc
    unfold contentsInto at hr
    split at hr
    · cases hr; exact h
    · split at hr
      · simp at hr
      · split at hr
        · exact closed_dataPart hC h hr
        · split at hr
          · simp at hr
          · dsimp only at hr
            split at hr
            · simp at hr
            · split at hr
              · simp at hr
              · next s₁ hs₁ =>
                have h₁ := closed_setSelf hC h hs₁
                split at hr
                · simp at hr
                · next s₂ hs₂ =>
                  have h₂ := closed_partialFirst hC hrec h₁ hs₂
                  split at hr
                  · simp at hr
                  · next s₃ hs₃ =>
                    have h₃ : P s₃ := by
                      split at hs₃
                      · exact closed_appendEach hC _ h₂ hs₃
                      · exact closed_cloneEach hC _ h₂ hs₃
                    exact closed_partialLast hC hrec h₃ hr

end

section
variable {P : DOMState → Prop} (hP : RangeClosed P)
include hP

/-! ## `insertNode` -/

/-- **`insertNode` は妥当性を保つ。** step 7 の split が node を作るので、一意性も一緒に運ぶ。 -/
theorem closed_rangeInsertNode {s s' : DOMState} {i : Nat} {n : NodeId}
    (h : P s) (hr : rangeInsertNode s i n = .ok s') : P s' := by
  unfold rangeInsertNode at hr
  split at hr
  · simp at hr
  · split at hr
    · simp at hr
    · split at hr
      · simp at hr
      · split at hr
        · split at hr
          · simp at hr
          · split at hr
            · simp at hr
            · split at hr
              · simp at hr
              · next newText s₀ hsp =>
                exact hP.insertTail (hP.splitText h hsp) hr
        · dsimp only at hr
          split at hr
          · simp at hr
          · exact hP.insertTail h hr

/-- **`extractContents()` は妥当性を保つ。** -/
theorem closed_rangeExtractContents {s s' : DOMState} {i : Nat} {frag : NodeId} (h : P s)
    (hr : rangeExtractContents s i = .ok (frag, s')) : P s' := by
  unfold rangeExtractContents at hr
  split at hr
  · simp at hr
  · split at hr
    · simp at hr
    · next frag₀ s₁ hf =>
      have h₁ := hP.fragment h hf
      have hr' := ok_of_discardOnError hr
      cases hc : contentsInto true (s₁.tree.size + 1) s₁ _ (some i) frag₀ with
      | error p => rw [hc] at hr'; simp [Except.map] at hr'
      | ok s₂ =>
        rw [hc] at hr'
        simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at hr'
        obtain ⟨-, rfl⟩ := hr'
        exact closed_contentsInto hP.toContentsClosed true _ h₁ hc

/-- **`cloneContents()` は妥当性を保つ。** -/
theorem closed_rangeCloneContents {s s' : DOMState} {i : Nat} {frag : NodeId} (h : P s)
    (hr : rangeCloneContents s i = .ok (frag, s')) : P s' := by
  unfold rangeCloneContents at hr
  split at hr
  · simp at hr
  · split at hr
    · simp at hr
    · next frag₀ s₁ hf =>
      have h₁ := hP.fragment h hf
      have hr' := ok_of_discardOnError hr
      cases hc : contentsInto false (s₁.tree.size + 1) s₁ _ none frag₀ with
      | error p => rw [hc] at hr'; simp [Except.map] at hr'
      | ok s₂ =>
        rw [hc] at hr'
        simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at hr'
        obtain ⟨-, rfl⟩ := hr'
        exact closed_contentsInto hP.toContentsClosed false _ h₁ hc

/-- **`surroundContents()` は妥当性を保つ。** -/
theorem closed_rangeSurroundContents {s s' : DOMState} {i : Nat} {np : NodeId} (h : P s)
    (hr : rangeSurroundContents s i np = .ok s') : P s' := by
  unfold rangeSurroundContents at hr
  split at hr
  · simp at hr
  · split at hr
    · simp at hr
    · split at hr
      · simp at hr
      · split at hr
        · simp at hr
        · split at hr
          · simp at hr
          · next frag s₁ hx =>
            have h₁ := closed_rangeExtractContents hP h hx
            have hr' := ok_of_discardFragmentOnError hr
            simp only [bind, Except.bind, pure, Except.pure] at hr'
            split at hr'
            · simp at hr'
            · next s₂ hs₂ =>
              have h₂ : P s₂ := by
                rw [failWith_ok] at hs₂
                split at hs₂
                · cases hs₂; exact h₁
                · exact hP.replaceAllNone h₁ hs₂
              split at hr'
              · simp at hr'
              · next s₃ hs₃ =>
                have h₃ := closed_rangeInsertNode hP h₂ (failWith_ok.mp hs₃)
                split at hr'
                · simp at hr'
                · next s₄ hs₄ =>
                  have h₄ := hP.append h₃ (failWith_ok.mp hs₄)
                  split at hr'
                  · simp at hr'
                  · next s₅ hs₅ =>
                    cases hr'
                    have hsel := failWith_ok.mp hs₅
                    exact hP.discard frag (hP.selectNode h₄ hsel)

end

/-! ## admissibility と `Good` -/

theorem admissible_cloneSingle_data {s : DOMState} {n : NodeId} {d : NodeData} (x : String)
    (h : AdmissibleDOMState s) (hd : s.tree.get? n = some d) :
    AdmissibleDOMState (cloneSingle s { d with data := x } d.ownerDocument).2 := by
  have hf := freshNodeData_cloneData h hd (h.wellFormed.ownerDocument_is_document n d hd)
  exact admissible_createsNode h (createsNode_withFresh ⟨hf.parent, hf.children, hf.onlyElements,
    hf.keysNodup, hf.prefixHasNamespace, hf.ownerDocument⟩)

theorem unique_cloneSingle_data {s : DOMState} {n : NodeId} {d : NodeData} (x : String)
    (h : AttrIdsUnique s) (hd : s.tree.get? n = some d) :
    AttrIdsUnique (cloneSingle s { d with data := x } d.ownerDocument).2 := by
  unfold cloneSingle
  refine unique_withFresh h _ ?_ ?_ ?_
  · rw [cloneData_attributes, List.map_map]
    exact (zipIdx_ids (stateMaxAttrId s + 1) d.attributes 0).1
  · intro a ha
    rw [cloneData_attributes] at ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    show stateMaxAttrId s < stateMaxAttrId s + 1 + p.2
    omega
  · intro a ha
    rw [cloneData_attributes] at ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    show normalizeNamespace p.1.namespace = p.1.namespace
    exact h.normalized_of_mem hd (mem_of_mem_zipIdx' (x := p.1) (i := p.2) hp)

private theorem admissible_rangeFragment {s s' : DOMState} {r : RangeState} {frag : NodeId}
    (h : AdmissibleDOMState s) (hr : rangeFragment s r = .ok (frag, s')) : AdmissibleDOMState s' := by
  unfold rangeFragment at hr
  split at hr
  · simp at hr
  · exact admissible_createDocumentFragment h hr

private theorem unique_rangeFragment {s s' : DOMState} {r : RangeState} {frag : NodeId}
    (h : AttrIdsUnique s) (hr : rangeFragment s r = .ok (frag, s')) : AttrIdsUnique s' := by
  unfold rangeFragment at hr
  split at hr
  · simp at hr
  · exact unique_createDocumentFragment h hr

private theorem admissible_replaceAllNone {s s' : DOMState} {p : NodeId}
    (h : AdmissibleDOMState s) (hr : replaceAll s none p = .ok s') : AdmissibleDOMState s' :=
  admissible_replaceAll h (fun n hn => absurd hn (by simp)) (fun n hn => absurd hn (by simp))
    (fun n hn => absurd hn (by simp)) (fun _ n hn => absurd hn (by simp)) hr

theorem admissible_rangeClosed : RangeClosed AdmissibleDOMState where
  append h ha := admissible_append h ha
  replaceData h hr := admissible_replaceData h hr
  discard n h := admissible_discard h n
  withRange h hr := admissible_withRange h hr
  cloneSingleData x h hd := admissible_cloneSingle_data x h hd
  cloneNodeIn h hd hc := admissible_cloneNodeIn h (h.wellFormed.ownerDocument_is_document _ _ hd) hc
  fragment h hr := admissible_rangeFragment h hr
  splitText h hr := admissible_splitText h hr
  insertTail h hr := admissible_rangeInsertNodeTail h hr
  replaceAllNone h hr := admissible_replaceAllNone h hr
  selectNode h hr := admissible_rangeSelectNode h hr

theorem good_rangeClosed : RangeClosed Good where
  append h ha := ⟨admissible_append h.1 ha, (attrFrame_preInsert ha).unique h.2⟩
  replaceData h hr := ⟨admissible_replaceData h.1 hr, (attrFrame_replaceData hr).unique h.2⟩
  discard n h := good_variadicClosed.discard n h
  withRange h hr := ⟨admissible_withRange h.1 hr, (attrFrame_withRange ..).unique h.2⟩
  cloneSingleData x h hd := ⟨admissible_cloneSingle_data x h.1 hd, unique_cloneSingle_data x h.2 hd⟩
  cloneNodeIn h hd hc :=
    ⟨admissible_cloneNodeIn h.1 (h.1.wellFormed.ownerDocument_is_document _ _ hd) hc,
      unique_cloneNodeIn h.2 hc⟩
  fragment h hr := ⟨admissible_rangeFragment h.1 hr, unique_rangeFragment h.2 hr⟩
  splitText h hr := ⟨admissible_splitText h.1 hr, unique_splitText h.2 hr⟩
  insertTail h hr :=
    ⟨admissible_rangeInsertNodeTail h.1 hr, (attrFrame_rangeInsertNodeTail hr).unique h.2⟩
  replaceAllNone h hr := ⟨admissible_replaceAllNone h.1 hr, (attrFrame_replaceAll hr).unique h.2⟩
  selectNode h hr := ⟨admissible_rangeSelectNode h.1 hr, (attrFrame_rangeSelectNode hr).unique h.2⟩

/-! ## 当てはめ -/

theorem admissible_rangeInsertNode {s s' : DOMState} {i : Nat} {n : NodeId}
    (h : AdmissibleDOMState s) (hr : rangeInsertNode s i n = .ok s') : AdmissibleDOMState s' :=
  closed_rangeInsertNode admissible_rangeClosed h hr

end Dom
