import Dom.Spec.RangeExtract
import Dom.Spec.RangeDeleteSound
import Dom.Spec.RangeInsertSound
import Dom.Range.Extract
import Dom.Validity.RangeExtract
import Dom.Properties.CloneOk

/-!
# extract・clone the contents・`surroundContents()` は関係を満たす

実行関数の失敗は、その時点の状態を持つ（`Except (DOMException × DOMState)`）。関係は例外の種類だけを
述べるので、状態を落として比べる（`dropErr`）。

実行関数が `outsideModel` を返す所は、関係の外である。次の三つがある。

* 木の深さで足りるはずの fuel が尽きたとき（足りることは証明していない）。
* 端点が別の木にあって common ancestor が無いとき、step 15 の点が妥当でないとき。
  live range として妥当な range では起きない。
* range の start が end より後にあり、CharacterData でない node の data を求めるとき（本文が結果を定めない）。

surrogate pair を割る切り出しの `outsideModel` は、関係の `SubstringResult` が含んでいる。
定理はどれも「結果が `outsideModel` でなければ」を仮定に置く。
-/

namespace Dom.Spec

open Dom

variable {t : Tree} {r : RangeState}

/-! ## common ancestor -/

theorem ancestors_of_parent_none {x : NodeId} (h : parentOf t x = none) : ancestors t x = [] := by
  unfold ancestors
  cases t.size with
  | zero => rfl
  | succ f => exact ancestorChain_succ_none h

/-- start node から上る列で、end node の inclusive ancestor である最初のものは common ancestor である。 -/
theorem find_common (hwf : WellFormed t) {en : NodeId} :
    ∀ (k : Nat) (x ca : NodeId), (ancestors t x).length ≤ k →
      (x :: ancestors t x).find? (fun y => isInclusiveAncestorOf t y en) = some ca →
      InclusiveAncestor t ca x ∧ InclusiveAncestor t ca en ∧
        ∀ y, InclusiveAncestor t y x → Ancestor t ca y → ¬ InclusiveAncestor t y en := by
  intro k
  induction k with
  | zero =>
    intro x ca hlen hf
    by_cases hx : isInclusiveAncestorOf t x en = true
    · simp only [List.find?_cons, hx] at hf
      cases hf
      refine ⟨Or.inl rfl, (isInclusiveAncestorOf_iff hwf _ _).mp hx, ?_⟩
      intro y hy hay
      rcases hy with rfl | hy
      · exact absurd hay (ancestor_irrefl hwf y)
      · exact absurd (ancestor_asymm hwf hay hy) id
    · simp only [List.find?_cons, hx] at hf
      have hnil : ancestors t x = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [hnil] at hf
      simp at hf
  | succ k ih =>
    intro x ca hlen hf
    by_cases hx : isInclusiveAncestorOf t x en = true
    · simp only [List.find?_cons, hx] at hf
      cases hf
      refine ⟨Or.inl rfl, (isInclusiveAncestorOf_iff hwf _ _).mp hx, ?_⟩
      intro y hy hay
      rcases hy with rfl | hy
      · exact absurd hay (ancestor_irrefl hwf y)
      · exact absurd (ancestor_asymm hwf hay hy) id
    · simp only [List.find?_cons, hx] at hf
      have hxn : ¬ InclusiveAncestor t x en := fun h' => hx ((isInclusiveAncestorOf_iff hwf _ _).mpr h')
      cases hp : parentOf t x with
      | none => rw [ancestors_of_parent_none hp] at hf; simp at hf
      | some p =>
        rw [ancestors_eq_cons hwf hp] at hf hlen
        simp only [List.length_cons] at hlen
        obtain ⟨h1, h2, h3⟩ := ih p ca (by omega) hf
        refine ⟨Or.inr (Ancestor.of_parent_inclusive hp h1), h2, ?_⟩
        intro y hy hay
        rcases hy with rfl | hy
        · exact hxn
        · exact h3 y (inclusiveAncestor_of_ancestor_parent hy hp) hay

/-- **実行側の `commonAncestor` は "get the common ancestor" の関係を満たす。** -/
theorem commonAncestor_spec (hwf : WellFormed t) {ca : NodeId} (h : commonAncestor t r = some ca) :
    CommonAncestor t r ca :=
  find_common hwf _ r.start.node ca (Nat.le_refl _) h

/-- common ancestor があれば、start node と end node は同じ木にある。 -/
theorem root_eq_of_commonAncestor (hwf : WellFormed t) {ca : NodeId} (h : CommonAncestor t r ca) :
    root t r.start.node = root t r.«end».node := by
  have e : ∀ n, InclusiveAncestor t ca n → root t n = root t ca := by
    intro n hn
    rcases hn with rfl | hn
    · rfl
    · exact root_eq_of_ancestor hwf hn
  rw [e _ h.1, e _ h.2.1]

/-! ## partially contained と contained -/

theorem partiallyContained_iff (hwf : WellFormed t) (n : NodeId) :
    partiallyContained t r n = true ↔ PartiallyContained t r n := by
  unfold partiallyContained PartiallyContained
  rw [← isInclusiveAncestorOf_iff hwf, ← isInclusiveAncestorOf_iff hwf]
  cases isInclusiveAncestorOf t n r.start.node <;> cases isInclusiveAncestorOf t n r.«end».node <;>
    simp

theorem firstPartial_spec (hwf : WellFormed t) (ca : NodeId) :
    FirstPartial t r ca (firstPartiallyContainedChild t r ca) := by
  unfold firstPartiallyContainedChild
  by_cases h : isInclusiveAncestorOf t r.start.node r.«end».node = true
  · rw [if_pos h]
    exact Or.inl ((isInclusiveAncestorOf_iff hwf _ _).mp h)
  · rw [if_neg h]
    have hn : ¬ InclusiveAncestor t r.start.node r.«end».node :=
      fun h' => h ((isInclusiveAncestorOf_iff hwf _ _).mpr h')
    cases hf : (childrenOf t ca).find? (partiallyContained t r) with
    | none =>
      refine Or.inr fun c hc hpc => ?_
      exact List.find?_eq_none.mp hf c hc ((partiallyContained_iff hwf c).mpr hpc)
    | some c =>
      obtain ⟨hpc, A, B, hl, hA⟩ := List.find?_eq_some_iff_append.mp hf
      refine ⟨hn, A, B, hl, (partiallyContained_iff hwf c).mp hpc, fun x hx hpx => ?_⟩
      have := hA x hx
      rw [(partiallyContained_iff hwf x).mpr hpx] at this
      simp at this

theorem lastPartial_spec (hwf : WellFormed t) (ca : NodeId) :
    LastPartial t r ca (lastPartiallyContainedChild t r ca) := by
  unfold lastPartiallyContainedChild
  by_cases h : isInclusiveAncestorOf t r.«end».node r.start.node = true
  · rw [if_pos h]
    exact Or.inl ((isInclusiveAncestorOf_iff hwf _ _).mp h)
  · rw [if_neg h]
    have hn : ¬ InclusiveAncestor t r.«end».node r.start.node :=
      fun h' => h ((isInclusiveAncestorOf_iff hwf _ _).mpr h')
    cases hf : (childrenOf t ca).reverse.find? (partiallyContained t r) with
    | none =>
      refine Or.inr fun c hc hpc => ?_
      exact List.find?_eq_none.mp hf c (List.mem_reverse.mpr hc)
        ((partiallyContained_iff hwf c).mpr hpc)
    | some c =>
      obtain ⟨hpc, A, B, hl, hA⟩ := List.find?_eq_some_iff_append.mp hf
      refine ⟨hn, B.reverse, A.reverse, ?_, (partiallyContained_iff hwf c).mp hpc, ?_⟩
      · rw [← List.reverse_reverse (childrenOf t ca), hl]
        simp
      · intro x hx hpx
        have := hA x (List.mem_reverse.mp hx)
        rw [(partiallyContained_iff hwf x).mpr hpx] at this
        simp at this

theorem containedChildren_spec (hwf : WellFormed t) {sd ed : NodeData}
    (hs : t.get? r.start.node = some sd) (he : t.get? r.«end».node = some ed)
    (hroot : root t r.start.node = root t r.«end».node) (ca : NodeId) :
    ContainedChildren t r ca (containedChildren t r ca) := by
  refine ⟨List.filter_sublist, fun c _ => ?_⟩
  unfold containedChildren
  rw [List.mem_filter, containedInRange_iff hwf hs he hroot]
  simp_all

/-! ## 木にあった node は残る -/

/-- 状態が admissible で、`s₀` の木にあった node がどれも同じ kind で残っていること。 -/
def Keeps (s₀ s : DOMState) : Prop :=
  AdmissibleDOMState s ∧
    ∀ m d, s₀.tree.get? m = some d → ∃ d', s.tree.get? m = some d' ∧ d'.kind = d.kind

theorem keeps_of_shapePreserving {t t' : Tree} (h : ShapePreserving t t') {m : NodeId} {d : NodeData}
    (hm : t.get? m = some d) : ∃ d', t'.get? m = some d' ∧ d'.kind = d.kind := by
  have := h m
  rw [hm] at this
  cases h1 : t'.get? m with
  | none => rw [h1] at this; cases this
  | some d' =>
    rw [h1] at this
    simp only [Option.map_some, Option.some.injEq] at this
    exact ⟨d', rfl, by rw [← NodeData.shape_kind d', this, NodeData.shape_kind]⟩

theorem keeps_contentsClosed (s₀ : DOMState) : ContentsClosed (Keeps s₀) where
  append h ha := ⟨admissible_append h.1 ha, fun m d hm => by
    obtain ⟨d', hd', hk⟩ := h.2 m d hm
    obtain ⟨d'', hd'', hk'⟩ := keeps_of_shapePreserving (shapePreserving_append ha) hd'
    exact ⟨d'', hd'', hk'.trans hk⟩⟩
  replaceData h hr := ⟨admissible_replaceData h.1 hr, fun m d hm => by
    obtain ⟨d', hd', hk⟩ := h.2 m d hm
    obtain ⟨d'', hd'', hk'⟩ := keeps_of_shapePreserving (shapePreserving_replaceData hr) hd'
    exact ⟨d'', hd'', hk'.trans hk⟩⟩
  withRange h hr := ⟨admissible_withRange h.1 hr, h.2⟩
  cloneSingleData x h hd := ⟨admissible_cloneSingle_data x h.1 hd, fun m d hm => by
    obtain ⟨d', hd', hk⟩ := h.2 m d hm
    exact ⟨d', by unfold cloneSingle; exact withFresh_get?_of_some hd' _, hk⟩⟩
  cloneNodeIn h hd hc := by
    have hdoc := h.1.wellFormed.ownerDocument_is_document _ _ hd
    refine ⟨admissible_cloneNodeIn h.1 hdoc hc, fun m d hm => ?_⟩
    obtain ⟨-, -, hkeep, -⟩ := cloneNodeIn_deep_spec h.1 hdoc hc
    obtain ⟨d', hd', hk⟩ := h.2 m d hm
    exact ⟨d', hkeep m d' hd', hk⟩

theorem keeps_refl {s : DOMState} (h : AdmissibleDOMState s) : Keeps s s :=
  ⟨h, fun _ d hm => ⟨d, hm, rfl⟩⟩

theorem Keeps.trans {s₀ s₁ s₂ : DOMState} (h₁ : Keeps s₀ s₁) (h₂ : Keeps s₁ s₂) : Keeps s₀ s₂ :=
  ⟨h₂.1, fun m d hm => by
    obtain ⟨d', hd', hk⟩ := h₁.2 m d hm
    obtain ⟨d'', hd'', hk'⟩ := h₂.2 m d' hd'
    exact ⟨d'', hd'', hk'.trans hk⟩⟩

theorem Keeps.inTree {s₀ s : DOMState} (h : Keeps s₀ s) {m : NodeId} (hm : InTree s₀.tree m) :
    InTree s.tree m := by
  obtain ⟨md, hmd⟩ := hm
  obtain ⟨d', hd', -⟩ := h.2 m md hmd
  exact ⟨d', hd'⟩

/-! ## clone -/

/-- n の clone の data を x にしたものは、`SingleClone` を満たす（n は Document でない）。 -/
theorem singleClone_spec {s : DOMState} {n : NodeId} {d : NodeData} (h : AdmissibleDOMState s)
    (hd : s.tree.get? n = some d) (hnd : d.kind ≠ .document) (x : String) :
    SingleClone s n x (cloneSingle s { d with data := x } d.ownerDocument).1
      (cloneSingle s { d with data := x } d.ownerDocument).2 := by
  have hf := freshNodeData_cloneData h hd (h.wellFormed.ownerDocument_is_document n d hd)
  refine ⟨d, _, hd, createsNode_withFresh ⟨hf.parent, hf.children, hf.onlyElements, hf.keysNodup,
    hf.prefixHasNamespace, hf.ownerDocument⟩, ?_, ?_, ?_⟩
  · rw [cloneData_shapeAnon]
    rfl
  · rfl
  · simp [cloneDocumentOf, hnd]

/-- 木の中で parent を持つ node は Document でない。 -/
theorem not_document_of_parent {s : DOMState} (h : AdmissibleDOMState s) {n p : NodeId}
    {d : NodeData} (hd : s.tree.get? n = some d) (hp : parentOf s.tree n = some p) :
    d.kind ≠ .document := by
  intro hk
  have := h.structural.documentHasNoParent n d hd hk
  rw [parentOf_of_get? hd, this] at hp
  cases hp

/-! ## 部品 -/

theorem dataPart_sound {cut : Bool} {s : DOMState} {n into : NodeId} {offset count : Nat}
    (h : AdmissibleDOMState s) (hn : InTree s.tree n)
    (hne : dropErr (dataPart cut s n offset count into) ≠ .error .outsideModel) :
    DataPartResult cut s n offset count into (dropErr (dataPart cut s n offset count into)) := by
  obtain ⟨d, hd⟩ := hn
  unfold dataPart at hne ⊢
  rw [hd] at hne ⊢
  simp only [] at hne ⊢
  cases hk : d.kind.isCharacterData with
  | false => simp [hk] at hne
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, if_false] at hne ⊢
  have hsub := substringData_result_sound hd hk offset count
  cases hs : substringData s.tree n offset count with
  | error e => rw [hs] at hsub; exact Or.inl ⟨e, hsub, by simp [failWith]⟩
  | ok x =>
  rw [hs] at hsub
  simp only [failWith] at hne ⊢
  have hnd : d.kind ≠ .document := by
    intro he; rw [he] at hk; simp [NodeKind.isCharacterData] at hk
  have hcl := singleClone_spec h hd hnd x
  refine Or.inr ⟨x, _, _, hsub, hcl, ?_⟩
  have h₁ := admissible_cloneSingle_data x h hd
  have hpr := preInsert_result_sound h₁.wellFormed
    (cloneSingle s { d with data := x } d.ownerDocument).1 into none
  unfold appendDataClone at hne ⊢
  simp only [] at hne ⊢
  unfold append
  cases hpi : preInsert (cloneSingle s { d with data := x } d.ownerDocument).2
      (cloneSingle s { d with data := x } d.ownerDocument).1 into none with
  | error e => rw [hpi] at hpr; exact Or.inl ⟨e, hpr, rfl⟩
  | ok s₂ =>
    rw [hpi] at hpr
    refine Or.inr ⟨s₂, hpr, ?_⟩
    have h₂ := admissible_preInsert h₁ hpi
    cases cut with
    | false => exact Or.inr ⟨rfl, rfl⟩
    | true =>
      refine Or.inl ⟨rfl, ?_⟩
      have hrr := replaceData_result_sound h₂.wellFormed n offset count ""
      simp only [if_true]
      cases hrd : replaceData s₂ n offset count "" with
      | error e => rw [hrd] at hrr; exact hrr
      | ok s₃ => rw [hrd] at hrr; exact hrr

theorem appendEach_sound {into : NodeId} :
    ∀ (cs : List NodeId) {s : DOMState}, AdmissibleDOMState s →
      AppendEachResult into s cs (dropErr (appendEach s into cs))
  | [], s, _ => rfl
  | c :: cs, s, h => by
    unfold appendEach AppendEachResult
    have hpr := preInsert_result_sound h.wellFormed c into none
    unfold append
    cases hpi : preInsert s c into none with
    | error e => rw [hpi] at hpr; exact Or.inl ⟨e, hpr, rfl⟩
    | ok s₁ =>
      rw [hpi] at hpr
      exact Or.inr ⟨s₁, hpr, appendEach_sound cs (admissible_preInsert h hpi)⟩

theorem cloneEach_sound {into : NodeId} :
    ∀ (cs : List NodeId) {s : DOMState}, AdmissibleDOMState s → (∀ c ∈ cs, InTree s.tree c) →
      dropErr (cloneEach s into cs) ≠ .error .outsideModel →
      CloneEachResult into s cs (dropErr (cloneEach s into cs))
  | [], s, _, _, _ => rfl
  | c :: cs, s, h, hin, hne => by
    obtain ⟨cd, hcd⟩ := hin c (by simp)
    unfold cloneEach at hne ⊢
    rw [hcd] at hne ⊢
    simp only [] at hne ⊢
    have hdoc := h.wellFormed.ownerDocument_is_document c cd hcd
    obtain ⟨copy, s₁, hc⟩ := cloneNodeIn_isOk (subtree := true) h hdoc hcd
    rw [hc] at hne ⊢
    simp only [] at hne ⊢
    obtain ⟨d₀, hd₀, hkeep, hfresh, hclone, hranges, -⟩ := cloneNodeIn_deep_spec h hdoc hc
    have h₁ := admissible_cloneNodeIn h hdoc hc
    refine ⟨copy, s₁, ⟨hkeep, hfresh, hclone, hranges⟩, ?_⟩
    have hpr := preInsert_result_sound h₁.wellFormed copy into none
    unfold append at hne ⊢
    cases hpi : preInsert s₁ copy into none with
    | error e => rw [hpi] at hpr; exact Or.inl ⟨e, hpr, rfl⟩
    | ok s₂ =>
      rw [hpi] at hpr hne
      have h₂ := admissible_preInsert h₁ hpi
      refine Or.inr ⟨s₂, hpr, cloneEach_sound cs h₂ ?_ hne⟩
      intro m hm
      obtain ⟨md, hmd⟩ := hin m (by simp [hm])
      obtain ⟨d', hd', -⟩ := keeps_of_shapePreserving (shapePreserving_preInsert hpi) (hkeep m md hmd)
      exact ⟨d', hd'⟩

theorem setSelf_spec {s s₁ : DOMState} {self : Option Nat} {bp : BoundaryPoint}
    (h : setSelf s self bp = .ok s₁) : SelfSet s self bp s₁ := by
  unfold setSelf at h
  split at h
  · cases h; exact Or.inl ⟨rfl, rfl⟩
  · next i =>
    split at h
    · cases h; exact Or.inr ⟨i, rfl, rfl⟩
    · cases h

/-! ## partially contained child -/

/-- 再帰した extract（clone the contents）が関係を満たすこと。 -/
def RecurSound (cut : Bool) (recur : Recur) : Prop :=
  ∀ s' r' c, AdmissibleDOMState s' → InTree s'.tree r'.start.node → InTree s'.tree r'.«end».node →
    dropErr (recur s' r' c) ≠ .error .outsideModel →
    ContentsInto cut s' r' none c (dropErr (recur s' r' c))

/-- partially contained child の clone。child は parent を持つ（Document でない）。 -/
private theorem shallow_cases {s : DOMState} {x into : NodeId} {fd : NodeData}
    (h : AdmissibleDOMState s) (hfd : s.tree.get? x = some fd) (hnd : fd.kind ≠ .document) :
    let c := (cloneSingle s fd fd.ownerDocument).1
    let s₁ := (cloneSingle s fd fd.ownerDocument).2
    SingleClone s x fd.data c s₁ ∧ AdmissibleDOMState s₁ ∧
      PreInsertResult s₁ c into none (preInsert s₁ c into none) := by
  have hcl := singleClone_spec h hfd hnd fd.data
  have h₁ := admissible_cloneSingle_data fd.data h hfd
  exact ⟨hcl, h₁, preInsert_result_sound h₁.wellFormed _ into none⟩

theorem partialFirst_sound {cut : Bool} {recur : Recur} {s : DOMState} {r : RangeState}
    {fp : Option NodeId} {into : NodeId} (hrec : RecurSound cut recur) (h : AdmissibleDOMState s)
    (hstart : InTree s.tree r.start.node)
    (hfp : ∀ x, fp = some x → ∃ xd, s.tree.get? x = some xd ∧ xd.kind ≠ .document)
    (hne : dropErr (partialFirst cut recur s r fp into) ≠ .error .outsideModel) :
    PartialFirst cut s r fp into (dropErr (partialFirst cut recur s r fp into)) := by
  unfold partialFirst at hne ⊢
  cases fp with
  | none => exact .none
  | some x =>
  simp only [] at hne ⊢
  obtain ⟨fd, hfd, hfnd⟩ := hfp x rfl
  rw [hfd] at hne ⊢
  simp only [] at hne ⊢
  by_cases hcd : fd.kind.isCharacterData = true
  · rw [if_pos hcd] at hne ⊢
    exact .data ⟨fd, hfd, hcd⟩ (dataPart_sound h hstart hne)
  rw [if_neg hcd] at hne ⊢
  have hncd : ¬ IsCharacterData s.tree x := by
    rintro ⟨d', hd', hk'⟩; rw [hfd] at hd'; cases hd'; exact hcd hk'
  obtain ⟨hcl, h₁, hpr⟩ := shallow_cases (into := into) h hfd hfnd
  unfold appendShallowClone at hne ⊢
  unfold append at hne ⊢
  simp only [] at hne ⊢
  cases hpi : preInsert (cloneSingle s fd fd.ownerDocument).2 (cloneSingle s fd fd.ownerDocument).1
      into none with
  | error e =>
    rw [hpi] at hpr
    exact .cloneError ⟨fd, hfd⟩ hncd ⟨fd, hfd, hcl⟩ hpr
  | ok s₂ =>
    rw [hpi] at hpr hne
    simp only [] at hne ⊢
    have hk : Keeps s s₂ := by
      refine closed_appendShallowClone (keeps_contentsClosed s) (c := (cloneSingle s fd fd.ownerDocument).1)
        (into := into) (keeps_refl h) hfd ?_
      unfold appendShallowClone append
      simp only [hpi]
    exact .recurse ⟨fd, hfd⟩ hncd ⟨fd, hfd, hcl⟩ hpr
      (hrec _ _ _ hk.1 (hk.inTree hstart) (hk.inTree ⟨fd, hfd⟩) hne)

theorem partialLast_sound {cut : Bool} {recur : Recur} {s : DOMState} {r : RangeState}
    {lp : Option NodeId} {into : NodeId} (hrec : RecurSound cut recur)
    (h : AdmissibleDOMState s)
    (hend : InTree s.tree r.«end».node)
    (hlp : ∀ x, lp = some x → ∃ xd, s.tree.get? x = some xd ∧ xd.kind ≠ .document)
    (hne : dropErr (partialLast cut recur s r lp into) ≠ .error .outsideModel) :
    PartialLast cut s r lp into (dropErr (partialLast cut recur s r lp into)) := by
  unfold partialLast at hne ⊢
  cases lp with
  | none => exact .none
  | some x =>
  simp only [] at hne ⊢
  obtain ⟨ld, hld, hlnd⟩ := hlp x rfl
  rw [hld] at hne ⊢
  simp only [] at hne ⊢
  by_cases hcd : ld.kind.isCharacterData = true
  · rw [if_pos hcd] at hne ⊢
    exact .data ⟨ld, hld, hcd⟩ (dataPart_sound h hend hne)
  rw [if_neg hcd] at hne ⊢
  have hncd : ¬ IsCharacterData s.tree x := by
    rintro ⟨d', hd', hk'⟩; rw [hld] at hd'; cases hd'; exact hcd hk'
  obtain ⟨hcl, h₁, hpr⟩ := shallow_cases (into := into) h hld hlnd
  unfold appendShallowClone at hne ⊢
  unfold append at hne ⊢
  simp only [] at hne ⊢
  cases hpi : preInsert (cloneSingle s ld ld.ownerDocument).2 (cloneSingle s ld ld.ownerDocument).1
      into none with
  | error e =>
    rw [hpi] at hpr
    exact .cloneError ⟨ld, hld⟩ hncd ⟨ld, hld, hcl⟩ hpr
  | ok s₂ =>
    rw [hpi] at hpr hne
    simp only [] at hne ⊢
    have hk : Keeps s s₂ := by
      refine closed_appendShallowClone (keeps_contentsClosed s) (c := (cloneSingle s ld ld.ownerDocument).1)
        (into := into) (keeps_refl h) hld ?_
      unfold appendShallowClone append
      simp only [hpi]
    exact .recurse ⟨ld, hld⟩ hncd ⟨ld, hld, hcl⟩ hpr
      (hrec _ _ _ hk.1 (hk.inTree ⟨ld, hld⟩) (hk.inTree hend) hne)

/-! ## 全体 -/

/-- partially contained child は木にあって Document でない（parent を持つので）。 -/
private theorem child_not_document {s : DOMState} (h : AdmissibleDOMState s) {ca x : NodeId}
    (hx : x ∈ childrenOf s.tree ca) : ∃ xd, s.tree.get? x = some xd ∧ xd.kind ≠ .document := by
  have hp := (mem_childrenOf_iff h.wellFormed x ca).mpr hx
  obtain ⟨xd, hxd, -⟩ := parentOf_eq_some hp
  exact ⟨xd, hxd, not_document_of_parent h hxd hp⟩

theorem firstPartial_mem {t : Tree} {r : RangeState} {ca : NodeId} :
    ∀ {fp}, FirstPartial t r ca fp → ∀ x, fp = some x → x ∈ childrenOf t ca
  | none, _, _, hx => by cases hx
  | some c, ⟨_, A, B, hl, _, _⟩, x, hx => by cases hx; rw [hl]; simp

theorem lastPartial_mem {t : Tree} {r : RangeState} {ca : NodeId} :
    ∀ {lp}, LastPartial t r ca lp → ∀ x, lp = some x → x ∈ childrenOf t ca
  | none, _, _, hx => by cases hx
  | some c, ⟨_, A, B, hl, _, _⟩, x, hx => by cases hx; rw [hl]; simp

/--
**extract と clone the contents の、step 1 の後の部分は関係を満たす。**

結果が `outsideModel` でなければ。start node と end node は木にある。
-/
theorem contentsInto_sound (cut : Bool) :
    ∀ (fuel : Nat) {s : DOMState} {r : RangeState} {self : Option Nat} {into : NodeId},
      AdmissibleDOMState s → InTree s.tree r.start.node → InTree s.tree r.«end».node →
      dropErr (contentsInto cut fuel s r self into) ≠ .error .outsideModel →
      ContentsInto cut s r self into (dropErr (contentsInto cut fuel s r self into))
  | 0, s, r, self, into, h, hs, he, hne => by simp [contentsInto] at hne
  | fuel + 1, s, r, self, into, h, hs, he, hne => by
    have hwf := h.wellFormed
    have hrec : RecurSound cut (fun s' r' c => contentsInto cut fuel s' r' none c) :=
      fun s' r' c h' hs' he' hne' => contentsInto_sound cut fuel h' hs' he' hne'
    have hrk : ∀ s₀, RecurClosed (Keeps s₀) (fun s' r' c => contentsInto cut fuel s' r' none c) :=
      fun s₀ _ _ _ _ hk hc => closed_contentsInto (keeps_contentsClosed s₀) cut fuel hk hc
    unfold contentsInto at hne ⊢
    -- step 2
    by_cases hcol : r.start = r.«end»
    · rw [if_pos (by simp [hcol])]
      exact .collapsed hcol
    rw [if_neg (by simpa using hcol)] at hne ⊢
    obtain ⟨sd, hsd⟩ := hs
    rw [hsd] at hne ⊢
    simp only [] at hne ⊢
    -- step 4
    by_cases hsingle : (r.start.node == r.«end».node && sd.kind.isCharacterData) = true
    · rw [if_pos hsingle] at hne ⊢
      simp only [Bool.and_eq_true, beq_iff_eq] at hsingle
      exact .single hcol hsingle.1 ⟨sd, hsd, hsingle.2⟩ (dataPart_sound h ⟨sd, hsd⟩ hne)
    rw [if_neg hsingle] at hne ⊢
    have hgen : General s.tree r := by
      refine ⟨hcol, fun ⟨heq, d', hd', hk'⟩ => hsingle ?_⟩
      rw [hsd] at hd'; cases hd'
      simp [heq, hk']
    -- step 5
    cases hca : commonAncestor s.tree r with
    | none => rw [hca] at hne; simp at hne
    | some ca =>
    rw [hca] at hne
    simp only [] at hne ⊢
    have hCA := commonAncestor_spec hwf hca
    have hroot := root_eq_of_commonAncestor hwf hCA
    obtain ⟨ed, hed⟩ := he
    have hsetup : Setup s.tree r ca (firstPartiallyContainedChild s.tree r ca)
        (lastPartiallyContainedChild s.tree r ca) (containedChildren s.tree r ca) :=
      ⟨hCA, firstPartial_spec hwf ca, lastPartial_spec hwf ca,
        containedChildren_spec hwf hsd hed hroot ca⟩
    -- step 11
    by_cases hdt : ((containedChildren s.tree r ca).any
        fun c => kindOf s.tree c == some .documentType) = true
    · rw [if_pos hdt]
      obtain ⟨c, hc, hck⟩ := List.any_eq_true.mp hdt
      refine .doctype hgen hsetup ⟨c, hc, ?_⟩
      cases hkc : s.tree.get? c with
      | none => simp [kindOf, hkc] at hck
      | some cd => simp [kindOf, hkc] at hck; exact ⟨cd, hkc, hck⟩
    rw [if_neg hdt] at hne ⊢
    have hnodt : ∀ c ∈ containedChildren s.tree r ca, ¬ KindIs s.tree c .documentType := by
      intro c hc ⟨cd, hcd, hck⟩
      exact hdt (List.any_eq_true.mpr ⟨c, hc, by simp [kindOf, hcd, hck]⟩)
    have hbp := deleteContentsNewBP_spec hwf hroot
    -- step 12-15
    cases hss : setSelf s self (deleteContentsNewBP s.tree r) with
    | error p =>
      exfalso
      rw [hss] at hne
      unfold setSelf at hss
      split at hss
      · cases hss
      · split at hss
        · cases hss
        · cases hss; exact hne rfl
    | ok s₁ =>
    rw [hss] at hne
    simp only [] at hne ⊢
    have hself := setSelf_spec hss
    have hk₁ : Keeps s s₁ := closed_setSelf (keeps_contentsClosed s) (keeps_refl h) hss
    have htree₁ : s₁.tree = s.tree := by
      rcases hself with ⟨-, rfl⟩ | ⟨i, -, rfl⟩ <;> rfl
    -- step 16-17
    have hfpar : ∀ x, firstPartiallyContainedChild s.tree r ca = some x →
        ∃ xd, s₁.tree.get? x = some xd ∧ xd.kind ≠ .document := by
      intro x hx
      rw [htree₁]
      exact child_not_document h (firstPartial_mem hsetup.first x hx)
    cases hpf : partialFirst cut (fun s' r' c => contentsInto cut fuel s' r' none c) s₁ r
        (firstPartiallyContainedChild s.tree r ca) into with
    | error p =>
      obtain ⟨e, s'⟩ := p
      rw [hpf] at hne
      have := partialFirst_sound hrec hk₁.1 (hk₁.inTree ⟨sd, hsd⟩)
        hfpar (by rw [hpf]; exact hne)
      rw [hpf] at this
      exact .firstError hgen hsetup hnodt hbp hself this
    | ok s₂ =>
    rw [hpf] at hne
    simp only [] at hne ⊢
    have hpf' := partialFirst_sound hrec hk₁.1 (hk₁.inTree ⟨sd, hsd⟩)
      hfpar (by rw [hpf]; simp)
    rw [hpf] at hpf'
    have hk₂ : Keeps s s₂ := hk₁.trans
      (closed_partialFirst (keeps_contentsClosed s₁) (hrk s₁) (keeps_refl hk₁.1) hpf)
    -- step 18（clone the contents の step 14）
    have hcin : ∀ c ∈ containedChildren s.tree r ca, InTree s₂.tree c := by
      intro c hc
      have hmem : c ∈ childrenOf s.tree ca := hsetup.contained.1.subset hc
      obtain ⟨cd, hcd, -⟩ := parentOf_eq_some ((mem_childrenOf_iff hwf c ca).mpr hmem)
      exact hk₂.inTree ⟨cd, hcd⟩
    have hcs : ∀ res, (if cut then appendEach s₂ into (containedChildren s.tree r ca)
        else cloneEach s₂ into (containedChildren s.tree r ca)) = res →
        dropErr res ≠ .error .outsideModel →
        ContainedStep cut s₂ into (containedChildren s.tree r ca) (dropErr res) := by
      intro res hres hne'
      cases cut with
      | true =>
        simp only [if_true] at hres
        subst hres
        exact Or.inl ⟨rfl, appendEach_sound _ hk₂.1⟩
      | false =>
        simp only [Bool.false_eq_true, if_false] at hres
        subst hres
        exact Or.inr ⟨rfl, cloneEach_sound _ hk₂.1 hcin hne'⟩
    cases hcr : (if cut then appendEach s₂ into (containedChildren s.tree r ca)
        else cloneEach s₂ into (containedChildren s.tree r ca)) with
    | error p =>
      obtain ⟨e, s'⟩ := p
      rw [hcr] at hne
      have := hcs _ hcr (by simpa using hne)
      exact .containedError hgen hsetup hnodt hbp hself hpf' this
    | ok s₃ =>
    rw [hcr] at hne
    simp only [] at hne ⊢
    have hcs' := hcs _ hcr (by simp)
    have hk₃ : Keeps s s₃ := by
      refine hk₂.trans ?_
      cases cut with
      | true =>
        simp only [if_true] at hcr
        exact closed_appendEach (keeps_contentsClosed s₂) _ (keeps_refl hk₂.1) hcr
      | false =>
        simp only [Bool.false_eq_true, if_false] at hcr
        exact closed_cloneEach (keeps_contentsClosed s₂) _ (keeps_refl hk₂.1) hcr
    -- step 19-20
    have hlast := partialLast_sound hrec hk₃.1 (hk₃.inTree ⟨ed, hed⟩)
      (fun x hx => by
        obtain ⟨xd, hxd, hxk⟩ := child_not_document h (lastPartial_mem hsetup.last x hx)
        obtain ⟨xd', hxd', hk'⟩ := hk₃.2 x xd hxd
        exact ⟨xd', hxd', by rw [hk']; exact hxk⟩) hne
    exact .last hgen hsetup hnodt hbp hself hpf' hcs' hlast

/-! ## live range の数 -/

/-- 状態が admissible で、live range の数が `s₀` と同じであること。 -/
def LenKeep (s₀ s : DOMState) : Prop := AdmissibleDOMState s ∧ s.ranges.length = s₀.ranges.length

theorem preInsert_ranges_length {s s' : DOMState} {n p : NodeId} {c : Option NodeId}
    (hwf : WellFormed s.tree) (h : preInsert s n p c = .ok s') : s'.ranges.length = s.ranges.length :=
  insertSpec_ranges_length (insert_sound hwf (preInsert_cases h).2)

theorem replaceData_ranges_length {s s' : DOMState} {n : NodeId} {o c : Nat} {d : String}
    (hwf : WellFormed s.tree) (h : replaceData s n o c d = .ok s') : s'.ranges.length = s.ranges.length := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlen, -⟩ := replaceData_sound hwf h
  exact hlen

theorem remove_ranges_length {s s' : DOMState} {n : NodeId} {b : Bool}
    (h : remove s n b = .ok s') : s'.ranges.length = s.ranges.length := by
  obtain ⟨p, -, hp, -, -⟩ := remove_cases h
  rw [remove_ranges hp h, List.length_map]

theorem splitText_ranges_length {s s' : DOMState} {n t : NodeId} {o : Nat}
    (h₀ : AdmissibleDOMState s) (h : splitText s n o = .ok (t, s')) : s'.ranges.length = s.ranges.length := by
  unfold splitText at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · next nn s₁ hc =>
            have hcr := (createTextNode_creates hc).2.2.1
            have h₁ := admissible_createTextNode h₀ hc
            split at h
            · split at h
              · cases h
              · next s₄ hrep =>
                cases h
                rw [replaceData_ranges_length h₁.wellFormed hrep, hcr]
            · split at h
              · cases h
              · next s₂ hpre =>
                have h₂ := admissible_preInsert h₁ hpre
                split at h
                · cases h
                · next s₄ hrep =>
                  cases h
                  rw [replaceData_ranges_length (show WellFormed (splitTextAdjust s₂ _ _ _ _).tree
                    from h₂.wellFormed) hrep]
                  simp only [splitTextAdjust, List.length_map]
                  rw [preInsert_ranges_length h₁.wellFormed hpre, hcr]

theorem rangeInsertNodeTail_ranges_length {s s' : DOMState} {i : Nat} {p n : NodeId}
    {ref : Option NodeId} (h₀ : AdmissibleDOMState s) (h : rangeInsertNodeTail s i p n ref = .ok s') :
    s'.ranges.length = s.ranges.length := by
  unfold rangeInsertNodeTail at h
  cases hrm : (if (parentOf s.tree n).isSome then remove s n else Except.ok s) with
  | error e => rw [hrm] at h; simp at h
  | ok s₁ =>
    rw [hrm] at h
    simp only [] at h
    have hl₁ : s₁.ranges.length = s.ranges.length := by
      split at hrm
      · exact remove_ranges_length hrm
      · cases hrm; rfl
    have h₁ : AdmissibleDOMState s₁ := by
      split at hrm
      · exact admissible_remove h₀ hrm
      · cases hrm; exact h₀
    split at h
    · cases h
    · next s₂ hpi =>
      have hl₂ := preInsert_ranges_length h₁.wellFormed hpi
      repeat' split at h
      all_goals first
        | (cases h; done)
        | (cases h; simp only [withRange, List.length_set]; rw [hl₂, hl₁])
        | (cases h; rw [hl₂, hl₁])

theorem lenKeep_rangeClosed (s₀ : DOMState) : RangeClosed (LenKeep s₀) where
  append h ha := ⟨admissible_append h.1 ha, by rw [preInsert_ranges_length h.1.wellFormed ha, h.2]⟩
  replaceData h hr := ⟨admissible_replaceData h.1 hr, by rw [replaceData_ranges_length h.1.wellFormed hr, h.2]⟩
  withRange h hr := ⟨admissible_withRange h.1 hr, by simp only [withRange, List.length_set]; exact h.2⟩
  cloneSingleData x h hd := ⟨admissible_cloneSingle_data x h.1 hd, h.2⟩
  cloneNodeIn h hd hc := by
    have hdoc := h.1.wellFormed.ownerDocument_is_document _ _ hd
    obtain ⟨-, -, -, -, -, hranges, -⟩ := cloneNodeIn_deep_spec h.1 hdoc hc
    exact ⟨admissible_cloneNodeIn h.1 hdoc hc, by rw [hranges, h.2]⟩
  discard n h := ⟨admissible_discard h.1 n, by unfold discard; split <;> exact h.2⟩
  fragment h hr := by
    unfold rangeFragment at hr
    split at hr
    · simp at hr
    · exact ⟨admissible_createDocumentFragment h.1 hr,
        by rw [(createDocumentFragment_creates hr).2.2.1, h.2]⟩
  splitText h hr := ⟨admissible_splitText h.1 hr, by rw [splitText_ranges_length h.1 hr, h.2]⟩
  insertTail h hr := ⟨admissible_rangeInsertNodeTail h.1 hr,
    by rw [rangeInsertNodeTail_ranges_length h.1 hr, h.2]⟩
  replaceAllNone h hr := by
    refine ⟨admissible_rangeClosed.replaceAllNone h.1 hr, ?_⟩
    obtain ⟨s₁, s₂, hre, hstep, hs⟩ := replaceAll_cases hr
    rcases hstep with ⟨-, rfl⟩ | ⟨n, hn, -⟩
    · rw [hs]
      unfold queueTreeMutationRecord
      split
      · rw [removeEach_ranges_length _ hre, h.2]
      · simp only [queueMutationRecord_ranges]; rw [removeEach_ranges_length _ hre, h.2]
    · cases hn
  selectNode h hr := by
    refine ⟨admissible_rangeSelectNode h.1 hr, ?_⟩
    unfold rangeSelectNode at hr
    repeat' split at hr
    all_goals first
      | (cases hr; done)
      | (cases hr; simp only [withRange, List.length_set]; exact h.2)

/-! ## extractContents と cloneContents -/

@[simp] theorem dropErr_discardOnError {α : Type} (frag : NodeId)
    (x : Except (DOMException × DOMState) α) : dropErr (discardOnError frag x) = dropErr x := by
  cases x with
  | error p => obtain ⟨e, s⟩ := p; rfl
  | ok a => rfl

@[simp] theorem dropErr_discardFragmentOnError {α : Type} (base frag : NodeId)
    (x : Except (DOMException × DOMState) α) :
    dropErr (discardFragmentOnError base frag x) = dropErr x := by
  cases x with
  | error p => obtain ⟨e, s⟩ := p; rfl
  | ok a => rfl

/-- extract と clone the contents に共通の、step 1 から後。 -/
theorem contentsResult_sound (cut : Bool) {s : DOMState} {i : Nat} {r : RangeState}
    {self : Option Nat} (h : AdmissibleDOMState s) (hr : s.ranges[i]? = some r)
    (hne : dropErr ((match rangeFragment s r with
        | .error e => .error (e, s)
        | .ok (frag, s₁) =>
          discardOnError frag ((contentsInto cut (s₁.tree.size + 1) s₁ r self frag).map (frag, ·))) :
        Except (DOMException × DOMState) (NodeId × DOMState)) ≠ .error .outsideModel) :
    ContentsResult cut s r self (dropErr ((match rangeFragment s r with
        | .error e => .error (e, s)
        | .ok (frag, s₁) =>
          discardOnError frag ((contentsInto cut (s₁.tree.size + 1) s₁ r self frag).map (frag, ·))) :
        Except (DOMException × DOMState) (NodeId × DOMState))) := by
  have hv := h.rangeEndpoints r (List.mem_of_getElem? hr)
  obtain ⟨sd, hsd, -⟩ := hv.1
  obtain ⟨ed, hed, -⟩ := hv.2
  have hdoc : IsDocumentIn s sd.ownerDocument := h.wellFormed.ownerDocument_is_document _ sd hsd
  have hfr : rangeFragment s r =
      .ok (withFresh s { kind := .documentFragment, ownerDocument := sd.ownerDocument }) := by
    unfold rangeFragment
    rw [hsd]
    exact createDocumentFragment_of_isDocumentIn hdoc
  rw [hfr] at hne ⊢
  cases hw : withFresh s { kind := .documentFragment, ownerDocument := sd.ownerDocument } with
  | mk frag s₁ =>
  rw [hw] at hfr hne
  simp only [dropErr_discardOnError] at hne ⊢
  have hcr : CreatesNode s frag s₁ { kind := .documentFragment, ownerDocument := sd.ownerDocument } := by
    have := createsNode_withFresh (s := s) (d := { kind := .documentFragment, ownerDocument := sd.ownerDocument })
      (by
        have := (createDocumentFragment_creates
          (createDocumentFragment_of_isDocumentIn hdoc)).2.1
        exact this)
    rw [hw] at this
    exact this
  have h₁ : AdmissibleDOMState s₁ := admissible_createsNode h hcr
  have hget : ∀ m md, s.tree.get? m = some md → s₁.tree.get? m = some md := by
    intro m md hm
    have hne' : m ≠ frag := by intro he; rw [he, hcr.1.fresh] at hm; cases hm
    rw [hcr.1.others m hne']; exact hm
  refine ⟨sd, frag, s₁, hsd, hcr, ?_⟩
  cases hc : contentsInto cut (s₁.tree.size + 1) s₁ r self frag with
  | error p =>
    obtain ⟨e, s'⟩ := p
    rw [hc] at hne
    have := contentsInto_sound cut _ h₁ ⟨sd, hget _ _ hsd⟩ ⟨ed, hget _ _ hed⟩
      (by rw [hc]; simpa [Except.map, dropErr] using hne)
    rw [hc] at this
    exact Or.inl ⟨e, this, by simp [Except.map, dropErr]⟩
  | ok s₂ =>
    have := contentsInto_sound cut _ h₁ ⟨sd, hget _ _ hsd⟩ ⟨ed, hget _ _ hed⟩ (by rw [hc]; simp)
    rw [hc] at this
    exact Or.inr ⟨s₂, this, by simp [Except.map, dropErr]⟩

/--
**`extractContents()` の結果は関係を満たす**（結果が `outsideModel` でなければ）。

失敗に付いた状態は落として比べる。
-/
theorem rangeExtractContents_result_sound {s : DOMState} {i : Nat} {r : RangeState}
    (h : AdmissibleDOMState s) (hr : s.ranges[i]? = some r)
    (hne : dropErr (rangeExtractContents s i) ≠ .error .outsideModel) :
    ContentsResult true s r (some i) (dropErr (rangeExtractContents s i)) := by
  unfold rangeExtractContents at hne ⊢
  rw [hr] at hne ⊢
  exact contentsResult_sound true h hr hne

/-- **`cloneContents()` の結果は関係を満たす**（結果が `outsideModel` でなければ）。 -/
theorem rangeCloneContents_result_sound {s : DOMState} {i : Nat} {r : RangeState}
    (h : AdmissibleDOMState s) (hr : s.ranges[i]? = some r)
    (hne : dropErr (rangeCloneContents s i) ≠ .error .outsideModel) :
    ContentsResult false s r none (dropErr (rangeCloneContents s i)) := by
  unfold rangeCloneContents at hne ⊢
  rw [hr] at hne ⊢
  exact contentsResult_sound false h hr hne

/-! ## surroundContents -/

theorem inTree_of_inclusiveAncestor (hwf : WellFormed t) {a n : NodeId} (hn : InTree t n)
    (h : InclusiveAncestor t a n) : InTree t a := by
  rcases h with rfl | h
  · exact hn
  · exact exists_data_of_ancestor hwf h

theorem mem_inclusiveAncestors_iff (hwf : WellFormed t) (n a : NodeId) :
    a ∈ n :: ancestors t n ↔ InclusiveAncestor t a n := by
  rw [List.mem_cons, mem_ancestors_iff hwf]

/-- step 1 の判定。 -/
theorem partiallyContainsNonText_iff (hwf : WellFormed t) (hs : InTree t r.start.node)
    (he : InTree t r.«end».node) :
    partiallyContainsNonText t r = true ↔
      ∃ n, PartiallyContained t r n ∧ InTree t n ∧ ¬ IsText t n := by
  unfold partiallyContainsNonText
  rw [List.any_eq_true]
  constructor
  · rintro ⟨n, hm, hp⟩
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    have hpc := (partiallyContained_iff hwf n).mp hp.1
    have hin : InTree t n := by
      rcases List.mem_append.mp hm with hm | hm
      · exact inTree_of_inclusiveAncestor hwf hs ((mem_inclusiveAncestors_iff hwf _ _).mp hm)
      · exact inTree_of_inclusiveAncestor hwf he ((mem_inclusiveAncestors_iff hwf _ _).mp hm)
    refine ⟨n, hpc, hin, ?_⟩
    rintro ⟨d, hd, hk⟩
    simp [kindOf, hd, hk] at hp
  · rintro ⟨n, hpc, ⟨d, hd⟩, hnt⟩
    refine ⟨n, ?_, ?_⟩
    · rcases hpc with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact List.mem_append_left _ ((mem_inclusiveAncestors_iff hwf _ _).mpr h1)
      · exact List.mem_append_right _ ((mem_inclusiveAncestors_iff hwf _ _).mpr h2)
    · have hk : d.kind.isText = false := by
        cases hk : d.kind.isText with
        | false => rfl
        | true => exact absurd ⟨d, hd, hk⟩ hnt
      simp [(partiallyContained_iff hwf n).mpr hpc, kindOf, hd, hk]

/--
**`surroundContents()` の結果は関係を満たす**（結果が `outsideModel` でなければ）。

実行関数は、成功したとき step 6 で空になった fragment を状態から消す（`discard`。どこからも辿れない node を
消す model の約束で、本文の step ではない）。だから成功の状態は、関係の状態からその fragment を消したものである。
失敗に付いた状態は落として比べる。
-/
theorem rangeSurroundContents_result_sound {s : DOMState} {i : Nat} {r : RangeState} {np : NodeId}
    (h : AdmissibleDOMState s) (hr : s.ranges[i]? = some r) (hnp : InTree s.tree np)
    (hne : dropErr (rangeSurroundContents s i np) ≠ .error .outsideModel) :
    ∃ res, SurroundResult s i r np res ∧
      ((∃ e, res = .error e ∧ dropErr (rangeSurroundContents s i np) = .error e) ∨
        (∃ s₅ frag, res = .ok s₅ ∧ rangeSurroundContents s i np = .ok (discard s₅ frag))) := by
  have hwf := h.wellFormed
  have hv := h.rangeEndpoints r (List.mem_of_getElem? hr)
  obtain ⟨sd, hsd, -⟩ := hv.1
  obtain ⟨ed, hed, -⟩ := hv.2
  obtain ⟨npd, hnpd⟩ := hnp
  have hi : i < s.ranges.length := (List.getElem?_eq_some_iff.mp hr).1
  unfold rangeSurroundContents at hne ⊢
  rw [hr] at hne ⊢
  simp only [] at hne ⊢
  rw [hnpd] at hne ⊢
  simp only [] at hne ⊢
  -- step 1
  by_cases h1 : partiallyContainsNonText s.tree r = true
  · rw [if_pos h1]
    exact ⟨_, Or.inl ⟨(partiallyContainsNonText_iff hwf ⟨sd, hsd⟩ ⟨ed, hed⟩).mp h1, rfl⟩,
      Or.inl ⟨_, rfl, rfl⟩⟩
  rw [if_neg h1] at hne ⊢
  have hn1 : ∀ n, PartiallyContained s.tree r n → InTree s.tree n → IsText s.tree n := by
    intro n hpc hin
    exact Classical.byContradiction fun hnt =>
      h1 ((partiallyContainsNonText_iff hwf ⟨sd, hsd⟩ ⟨ed, hed⟩).mpr ⟨n, hpc, hin, hnt⟩)
  -- step 2
  have hkind : (KindIs s.tree np .document ∨ KindIs s.tree np .documentType ∨
      KindIs s.tree np .documentFragment) ↔
      (npd.kind == .document || npd.kind == .documentType || npd.kind == .documentFragment) = true := by
    simp only [KindIs, hnpd, Option.some.injEq, exists_eq_left', Bool.or_eq_true, beq_iff_eq, or_assoc]
  by_cases h2 : (npd.kind == .document || npd.kind == .documentType ||
      npd.kind == .documentFragment) = true
  · rw [if_pos h2]
    exact ⟨_, Or.inr ⟨hn1, Or.inl ⟨hkind.mpr h2, rfl⟩⟩, Or.inl ⟨_, rfl, rfl⟩⟩
  rw [if_neg h2] at hne ⊢
  have hk2 : ¬ (KindIs s.tree np .document ∨ KindIs s.tree np .documentType ∨
      KindIs s.tree np .documentFragment) := fun h' => h2 (hkind.mp h')
  -- step 3
  cases hxe : rangeExtractContents s i with
  | error p =>
    obtain ⟨e, s'⟩ := p
    rw [hxe] at hne
    have hx := rangeExtractContents_result_sound h hr (by rw [hxe]; simpa using hne)
    rw [hxe] at hx
    exact ⟨_, Or.inr ⟨hn1, Or.inr ⟨hk2, Or.inl ⟨e, hx, rfl⟩⟩⟩, Or.inl ⟨e, rfl, rfl⟩⟩
  | ok res =>
  obtain ⟨frag, s₁⟩ := res
  rw [hxe] at hne
  simp only [dropErr_discardFragmentOnError] at hne
  have hx := rangeExtractContents_result_sound h hr (by rw [hxe]; simp)
  rw [hxe] at hx
  have hk₁ : LenKeep s s₁ := closed_rangeExtractContents (lenKeep_rangeClosed s) ⟨h, rfl⟩ hxe
  -- step 4
  have step4 : ∃ s₂, ((childrenOf s₁.tree np = [] ∧ s₂ = s₁) ∨
      (childrenOf s₁.tree np ≠ [] ∧ ReplaceAllSpec s₁ none np s₂)) ∧
      (if (childrenOf s₁.tree np).isEmpty then (Except.ok s₁ : Except DOMException DOMState)
        else replaceAll s₁ none np) = .ok s₂ ∧ LenKeep s s₂ := by
    by_cases hemp : (childrenOf s₁.tree np).isEmpty = true
    · exact ⟨s₁, Or.inl ⟨List.isEmpty_iff.mp hemp, rfl⟩, by rw [if_pos hemp], hk₁⟩
    · obtain ⟨s₂, hra⟩ := replaceAll_isOk (node := none) (parent := np) hk₁.1.wellFormed
        (fun n hn => by cases hn)
      exact ⟨s₂, Or.inr ⟨fun he => hemp (List.isEmpty_iff.mpr he),
        replaceAll_sound hk₁.1.wellFormed hra⟩, by rw [if_neg hemp, hra],
        (lenKeep_rangeClosed s).replaceAllNone hk₁ hra⟩
  obtain ⟨s₂, hrel4, hex4, hk₂⟩ := step4
  have hr₂ : ∃ r₂, s₂.ranges[i]? = some r₂ :=
    ⟨_, List.getElem?_eq_getElem (by rw [hk₂.2]; exact hi)⟩
  obtain ⟨r₂, hr₂⟩ := hr₂
  -- step 5
  have hins := rangeInsertNode_result_sound_of_admissible np hk₂.1 hr₂
  simp only [bind, Except.bind, failWith, hex4, pure, Except.pure] at hne ⊢
  cases hin : rangeInsertNode s₂ i np with
  | error e =>
    rw [hin] at hins hne
    refine ⟨.error e, Or.inr ⟨hn1, Or.inr ⟨hk2, Or.inr ⟨frag, s₁, hx, s₂, hrel4,
      Or.inl ⟨e, ⟨r₂, hr₂, hins⟩, rfl⟩⟩⟩⟩, Or.inl ⟨e, rfl, rfl⟩⟩
  | ok s₃ =>
  rw [hin] at hins hne
  simp only [] at hne ⊢
  have hk₃ : LenKeep s s₃ := closed_rangeInsertNode (lenKeep_rangeClosed s) hk₂ hin
  -- step 6
  have hpr := preInsert_result_sound hk₃.1.wellFormed frag np none
  unfold append at hne ⊢
  cases hap : preInsert s₃ frag np none with
  | error e =>
    rw [hap] at hpr hne
    refine ⟨.error e, Or.inr ⟨hn1, Or.inr ⟨hk2, Or.inr ⟨frag, s₁, hx, s₂, hrel4,
      Or.inr ⟨s₃, ⟨r₂, hr₂, hins⟩, Or.inl ⟨e, hpr, rfl⟩⟩⟩⟩⟩, Or.inl ⟨e, rfl, rfl⟩⟩
  | ok s₄ =>
  rw [hap] at hpr hne
  simp only [] at hne ⊢
  have hk₄ : LenKeep s s₄ := (lenKeep_rangeClosed s).append hk₃ hap
  -- step 7
  obtain ⟨r₄, hr₄⟩ : ∃ r₄, s₄.ranges[i]? = some r₄ :=
    ⟨_, List.getElem?_eq_getElem (by rw [hk₄.2]; exact hi)⟩
  have hsel := (rangeSelectNode_result_complete hk₄.1.wellFormed hr₄ (n := np)).mpr rfl
  cases hse : rangeSelectNode s₄ i np with
  | error e =>
    rw [hse] at hsel
    refine ⟨.error e, Or.inr ⟨hn1, Or.inr ⟨hk2, Or.inr ⟨frag, s₁, hx, s₂, hrel4,
      Or.inr ⟨s₃, ⟨r₂, hr₂, hins⟩, Or.inr ⟨s₄, hpr, r₄, hr₄, hsel⟩⟩⟩⟩⟩, Or.inl ⟨e, rfl, ?_⟩⟩
    simp [discardFragmentOnError, dropErr]
  | ok s₅ =>
    rw [hse] at hsel
    refine ⟨.ok s₅, Or.inr ⟨hn1, Or.inr ⟨hk2, Or.inr ⟨frag, s₁, hx, s₂, hrel4,
      Or.inr ⟨s₃, ⟨r₂, hr₂, hins⟩, Or.inr ⟨s₄, hpr, r₄, hr₄, hsel⟩⟩⟩⟩⟩, Or.inr ⟨s₅, frag, rfl, ?_⟩⟩
    simp [discardFragmentOnError]

end Dom.Spec
