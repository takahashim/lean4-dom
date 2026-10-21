import Dom.Spec.RangeExtractFuel
import Dom.Spec.RangeDeleteCongr
import Dom.Spec.RangeInsertCongr

/-!
# extract・clone the contents の関係は結果を一つに決める（completeness）

本文は新しい node の id を決めないので、本文の関係（`Alloc.spec`）は結果を id の付け替えを除いてしか決めない。
ここでは model の割り当て（`Alloc.model`）で id を決めた関係について、関係を満たす結果が実行関数の結果と
観測の上で等しいことを示す。

model の割り当ては、clone の id と attribute の id を `freshId` と `stateMaxAttrId` から振る。どちらも木の
`get?` と detach された `Attr` だけで決まるので、観測の等しい状態どうしで割り当ては揃う（`freshId_congr`・
`stateMaxAttrId_congr`）。

証明は実行関数の fuel について帰納する。関係の導出の各段を、観測の等しい admissible な状態で走る実行関数の段と
比べる。実行関数の段は関係の段を満たし（soundness）、関係の段は観測の等しい入力から観測の等しい結果を出す
（`preInsertResult_congr` ほか）。
-/

namespace Dom.Spec

open Dom

/-! ## 割り当ては観測で決まる -/

theorem find?_ne_none_of_mem :
    ∀ (l : List (NodeId × NodeData)) {k : NodeId}, k ∈ l.map Prod.fst → Store.find? l k ≠ none
  | [], _, h => absurd h (by simp)
  | (a, v) :: rest, k, h => by
    unfold Store.find?
    by_cases hak : a = k
    · simp [hak]
    · rw [if_neg hak]
      rcases List.mem_cons.mp h with he | hrest
      · exact absurd he.symm hak
      · exact find?_ne_none_of_mem rest hrest

theorem get?_ne_none_of_mem_keys {s : NodeStore} {k : NodeId} (h : k ∈ s.keys) : s.get? k ≠ none :=
  find?_ne_none_of_mem s.entries h

/-- `foldl` で最大を取るとき、列の要素がどれも上界以下なら結果も上界以下である。 -/
theorem foldl_le_of_forall {α : Type} (f : Nat → α → Nat) (hf : ∀ m a, m ≤ f m a)
    (hmono : ∀ m m' a, m ≤ m' → f m a ≤ f m' a) (b : Nat) :
    ∀ (l : List α) (init : Nat), init ≤ b → (∀ a ∈ l, f b a ≤ b) → l.foldl f init ≤ b
  | [], _, hi, _ => hi
  | a :: rest, init, hi, hl => by
    refine foldl_le_of_forall f hf hmono b rest _ ?_ (fun x hx => hl x (by simp [hx]))
    exact Nat.le_trans (hmono _ _ a hi) (hl a (by simp))

theorem max_le_max_left' {m m' x : Nat} (h : m ≤ m') : max m x ≤ max m' x :=
  Nat.max_le.mpr ⟨Nat.le_trans h (Nat.le_max_left _ _), Nat.le_max_right _ _⟩

theorem foldl_max_le {l : List NodeId} {init b : Nat} (hi : init ≤ b) (hl : ∀ k ∈ l, k.id ≤ b) :
    l.foldl (fun m k => max m k.id) init ≤ b :=
  foldl_le_of_forall (fun m k => max m k.id) (fun _ _ => Nat.le_max_left _ _)
    (fun _ _ _ h => max_le_max_left' h) b l init hi
    (fun k hk => Nat.max_le.mpr ⟨Nat.le_refl _, hl k hk⟩)

theorem foldl_attrMax_mono :
    ∀ (l : List Attr) {m m' : Nat}, m ≤ m' →
      l.foldl (fun m a => max m a.id.id) m ≤ l.foldl (fun m a => max m a.id.id) m'
  | [], _, _, h => h
  | _ :: rest, _, _, h => foldl_attrMax_mono rest (max_le_max_left' h)

/-- `maxId` は `get?` で決まる。 -/
theorem maxId_congr {t t' : Tree} (h : TreeObsEq t t') : maxId t' = maxId t := by
  have key : ∀ {u u' : Tree}, TreeObsEq u u' → maxId u' ≤ maxId u := by
    intro u u' hu
    refine foldl_max_le (Nat.zero_le _) fun k hk => ?_
    have hne : u'.get? k ≠ none := get?_ne_none_of_mem_keys hk
    rw [hu k] at hne
    cases hd : u.get? k with
    | none => exact absurd hd hne
    | some d => exact id_le_maxId hd
  exact Nat.le_antisymm (key h) (key h.symm)

theorem freshId_congr {t t' : Tree} (h : TreeObsEq t t') : freshId t' = freshId t := by
  unfold freshId; rw [maxId_congr h]

theorem attrMaxAt_le {t : Tree} {m b : Nat} {k : NodeId} (hm : m ≤ b)
    (hk : ∀ d, t.get? k = some d → ∀ a ∈ d.attributes, a.id.id ≤ b) : attrMaxAt t m k ≤ b := by
  unfold attrMaxAt
  split
  · exact hm
  · next d hd =>
    have : ∀ (l : List Attr) (init : Nat), init ≤ b → (∀ a ∈ l, a.id.id ≤ b) →
        l.foldl (fun m a => max m a.id.id) init ≤ b := by
      intro l init hi hl
      refine foldl_le_of_forall (fun m a => max m a.id.id) (fun _ _ => Nat.le_max_left _ _)
        (fun _ _ _ h => max_le_max_left' h) b l init hi
        (fun a ha => Nat.max_le.mpr ⟨Nat.le_refl _, hl a ha⟩)
    exact this _ _ hm (hk d hd)

/-- `maxAttrId` は `get?` で決まる。 -/
theorem maxAttrId_congr {t t' : Tree} (h : TreeObsEq t t') : maxAttrId t' = maxAttrId t := by
  have key : ∀ {u u' : Tree}, TreeObsEq u u' → maxAttrId u' ≤ maxAttrId u := by
    intro u u' hu
    unfold maxAttrId
    refine foldl_le_of_forall (attrMaxAt u') (le_attrMaxAt u') ?_ _ _ 0 (Nat.zero_le _) ?_
    · intro m m' k hmm
      unfold attrMaxAt
      split
      · exact hmm
      · exact foldl_attrMax_mono _ hmm
    · intro k _
      refine attrMaxAt_le (Nat.le_refl _) fun d hd a ha => ?_
      rw [hu k] at hd
      exact attrId_le_maxAttrId hd ha
  exact Nat.le_antisymm (key h) (key h.symm)

theorem stateMaxAttrId_congr {s sb : DOMState} (h : ObsEq s sb) :
    stateMaxAttrId sb = stateMaxAttrId s := by
  unfold stateMaxAttrId
  rw [maxAttrId_congr h.tree, h.detachedAttrs]

/-! ## node を作る段の congruence -/

theorem ObsEq.withTree {s sb : DOMState} (h : ObsEq s sb) {t t' : Tree} (ht : TreeObsEq t t') :
    ObsEq (s.withTree t) (sb.withTree t') :=
  ⟨⟨ht, h.ranges, h.iterators, h.registrations, h.records, h.pendingObservers, h.microtaskQueued,
    h.walkers, h.listeners, h.detachedAttrs⟩, h.registrationOrder, h.pendingOrder⟩

theorem TreeObsEq.insertNode {t t' : Tree} (h : TreeObsEq t t') (n : NodeId) (d : NodeData) :
    TreeObsEq (t.insertNode n d) (t'.insertNode n d) := fun m => by
  by_cases hm : m = n
  · subst hm; rw [get?_insertNode_self, get?_insertNode_self]
  · rw [get?_insertNode_ne _ hm, get?_insertNode_ne _ hm]; exact h m

/-- 観測の等しい状態に同じ node を作ると、id が揃い、結果の観測も等しい。 -/
theorem withFresh_congr {s sb : DOMState} (h : ObsEq s sb) (d : NodeData) :
    (withFresh sb d).1 = (withFresh s d).1 ∧ ObsEq (withFresh s d).2 (withFresh sb d).2 := by
  have hf := freshId_congr h.tree
  refine ⟨hf, ?_⟩
  show ObsEq (s.withTree (s.tree.insertNode (freshId s.tree) d))
    (sb.withTree (sb.tree.insertNode (freshId sb.tree) d))
  rw [hf]
  exact h.withTree (h.tree.insertNode _ d)

theorem cloneSingle_congr {s sb : DOMState} (h : ObsEq s sb) (d : NodeData) (doc : NodeId) :
    (cloneSingle sb d doc).1 = (cloneSingle s d doc).1 ∧
      ObsEq (cloneSingle s d doc).2 (cloneSingle sb d doc).2 := by
  unfold cloneSingle
  rw [freshId_congr h.tree, stateMaxAttrId_congr h]
  exact withFresh_congr h _

/-- 観測の等しい状態での `append` は、成否と例外が揃い、成功なら結果の観測も等しい。 -/
theorem append_congr {s sb : DOMState} (hwf : WellFormed s.tree) (h : ObsEq s sb) (c p : NodeId) :
    ResultObsEq (append s c p) (append sb c p) :=
  preInsertResult_congr hwf h (preInsert_result_sound hwf c p none)
    (preInsert_result_sound (h.tree.wellFormed hwf) c p none)

theorem cloneAppend_congr {s sb : DOMState} (hwf : WellFormed s.tree) (h : ObsEq s sb) (c : NodeId)
    (par : Option NodeId) : ResultObsEq (cloneAppend s c par) (cloneAppend sb c par) := by
  cases par with
  | none => exact h
  | some p => exact append_congr hwf h c p

theorem ok_ok_of_resultObsEq {r₁ r₂ : Except DOMException DOMState} {a b : DOMState}
    (h : ResultObsEq r₁ r₂) (h₁ : r₁ = .ok a) (h₂ : r₂ = .ok b) : ObsEq a b := by
  subst h₁ h₂; exact h

/-- **deep な clone は観測の等しい状態で同じ id を振り、観測の等しい結果を返す。** -/
theorem cloneMany_congr : ∀ (f₁ f₂ : Nat) {s sb : DOMState} {l : List NodeId} {doc : NodeId}
    {par : Option NodeId} {k₁ k₂ : List NodeId} {s₁ s₂ : DOMState},
    AdmissibleDOMState s → IsDocument s.tree doc → ObsEq s sb →
    cloneMany f₁ s l doc par = .ok (k₁, s₁) → cloneMany f₂ sb l doc par = .ok (k₂, s₂) →
    k₁ = k₂ ∧ ObsEq s₁ s₂
  | _, _, s, sb, [], doc, par, k₁, k₂, s₁, s₂, _, _, h, h₁, h₂ => by
    simp only [cloneMany, Except.ok.injEq, Prod.mk.injEq] at h₁ h₂
    obtain ⟨rfl, rfl⟩ := h₁
    obtain ⟨rfl, rfl⟩ := h₂
    exact ⟨rfl, h⟩
  | 0, _, _, _, _ :: _, _, _, _, _, _, _, _, _, _, h₁, _ => by simp [cloneMany] at h₁
  | _ + 1, 0, _, _, _ :: _, _, _, _, _, _, _, _, _, _, _, h₂ => by simp [cloneMany] at h₂
  | f₁ + 1, f₂ + 1, s, sb, n :: rest, doc, par, k₁, k₂, s₁, s₂, hv, hdoc, h, h₁, h₂ => by
    simp only [cloneMany] at h₁ h₂
    rw [show sb.tree.get? n = s.tree.get? n from h.tree n] at h₂
    split at h₁
    · simp at h₁
    · next d hd =>
      rw [hd] at h₂
      simp only [] at h₂
      obtain ⟨hcid, hcobs⟩ := cloneSingle_congr h d doc
      rw [hcid] at h₂
      have hcreate := createsNode_withFresh (freshNodeData_cloneData hv hd hdoc)
      have hv₁ : AdmissibleDOMState (cloneSingle s d doc).2 := admissible_createsNode hv hcreate
      have hdoc₁ : IsDocument (cloneSingle s d doc).2.tree doc := by
        obtain ⟨dd, hdd, hk⟩ := hdoc
        exact ⟨dd, (withFresh_addsNode s _).get?_of hdd, hk⟩
      have happ := cloneAppend_congr hv₁.wellFormed hcobs (cloneSingle s d doc).1 par
      split at h₁
      · simp at h₁
      · next s₃ ha₁ =>
        split at h₂
        · next e ha₂ => rw [ha₁, ha₂] at happ; exact happ.elim
        · next s₃' ha₂ =>
          have hobs₃ := ok_ok_of_resultObsEq happ ha₁ ha₂
          obtain ⟨hv₃, hsp⟩ := admissible_cloneAppend hv₁ ha₁
          have hdoc₃ : IsDocument s₃.tree doc := hdoc₁.map hsp
          split at h₁
          · simp at h₁
          · next kids₀ s₄ hk₁ =>
            split at h₂
            · simp at h₂
            · next kids₀' s₄' hk₂ =>
              obtain ⟨-, hobs₄⟩ := cloneMany_congr f₁ f₂ hv₃ hdoc₃ hobs₃ hk₁ hk₂
              obtain ⟨hv₄, hdoc₄⟩ := admissible_cloneMany f₁ _ _ _ _ _ _ hv₃ hdoc₃ hk₁
              split at h₁
              · simp at h₁
              · next sib s₅ hs₁ =>
                split at h₂
                · simp at h₂
                · next sib' s₅' hs₂ =>
                  obtain ⟨hsib, hobs₅⟩ := cloneMany_congr f₁ f₂ hv₄ hdoc₄ hobs₄ hs₁ hs₂
                  simp only [Except.ok.injEq, Prod.mk.injEq] at h₁ h₂
                  obtain ⟨rfl, rfl⟩ := h₁
                  obtain ⟨rfl, rfl⟩ := h₂
                  exact ⟨by rw [hsib], hobs₅⟩

/-- 観測の等しい状態での deep な clone は、同じ copy を作り、観測の等しい結果を返す。 -/
theorem cloneNodeIn_congr {s sb s₁ s₂ : DOMState} {n doc c₁ c₂ : NodeId} (hv : AdmissibleDOMState s)
    (hdoc : IsDocument s.tree doc) (h : ObsEq s sb)
    (h₁ : cloneNodeIn s n doc true = .ok (c₁, s₁)) (h₂ : cloneNodeIn sb n doc true = .ok (c₂, s₂)) :
    c₁ = c₂ ∧ ObsEq s₁ s₂ := by
  unfold cloneNodeIn at h₁ h₂
  rw [show sb.tree.get? n = s.tree.get? n from h.tree n] at h₂
  split at h₁
  · simp at h₁
  · next d hd =>
    rw [hd] at h₂
    simp only [if_true] at h₁ h₂
    split at h₁
    · simp at h₁
    · next c rest s' hm₁ =>
      split at h₂
      · simp at h₂
      · next c' rest' s'' hm₂ =>
        obtain ⟨hk, hobs⟩ := cloneMany_congr _ _ hv hdoc h hm₁ hm₂
        simp only [Except.ok.injEq, Prod.mk.injEq] at h₁ h₂
        obtain ⟨rfl, rfl⟩ := h₁
        obtain ⟨rfl, rfl⟩ := h₂
        exact ⟨(List.cons.inj hk).1, hobs⟩
      · simp at h₂
    · simp at h₁

/-! ## model の割り当て -/

/--
**model の割り当て。** clone の id と attribute の id を `cloneSingle`（`freshId` と `stateMaxAttrId`）で、
step 1 と subfragment の DocumentFragment の id を `freshId` で、deep な clone を `cloneNodeIn` で決める。
状態は観測の上で決める。
-/
def Alloc.model : Alloc where
  single s n x c s' := ∃ d, s.tree.get? n = some d ∧
    c = (cloneSingle s { d with data := x } d.ownerDocument).1 ∧
    ObsEq (cloneSingle s { d with data := x } d.ownerDocument).2 s'
  fragment s doc sub s' :=
    sub = (withFresh s { kind := .documentFragment, ownerDocument := doc }).1 ∧
    ObsEq (withFresh s { kind := .documentFragment, ownerDocument := doc }).2 s'
  deep s n c s' := ∃ d s'', s.tree.get? n = some d ∧ cloneNodeIn s n d.ownerDocument true = .ok (c, s'') ∧
    ObsEq s'' s'

theorem allocSound_model : AllocSound Alloc.model where
  single {_ _ d} _ hd _ _ := ⟨d, hd, rfl, ObsEq.refl _⟩
  fragment _ := ⟨rfl, ObsEq.refl _⟩
  deep {_ s' _ _ d} _ hd hc := ⟨d, s', hd, hc, ObsEq.refl _⟩

/-! ## 木の観測で決まる述語 -/

section Transport

variable {t t' : Tree} (h : TreeObsEq t t') {r : RangeState}
include h

theorem commonAncestor_congr {ca : NodeId} : CommonAncestor t' r ca ↔ CommonAncestor t r ca := by
  unfold CommonAncestor
  simp only [h.inclusiveAncestor_iff, h.ancestor_iff]

theorem partiallyContained_congr {n : NodeId} : PartiallyContained t' r n ↔ PartiallyContained t r n := by
  unfold PartiallyContained
  simp only [h.inclusiveAncestor_iff]

theorem firstPartial_congr {ca : NodeId} {fp : Option NodeId} :
    FirstPartial t' r ca fp ↔ FirstPartial t r ca fp := by
  cases fp <;> simp only [FirstPartial, h.inclusiveAncestor_iff, h.childrenOf,
    partiallyContained_congr h]

theorem lastPartial_congr {ca : NodeId} {lp : Option NodeId} :
    LastPartial t' r ca lp ↔ LastPartial t r ca lp := by
  cases lp <;> simp only [LastPartial, h.inclusiveAncestor_iff, h.childrenOf,
    partiallyContained_congr h]

theorem bpBefore_congr {a b : BoundaryPoint} : BPBefore t' a b ↔ BPBefore t a b := by
  unfold BPBefore
  simp only [h.parentOf, h.index, h.inclusiveAncestor_iff]

theorem contained_congr (hwf : WellFormed t) (hwf' : WellFormed t') {n : NodeId} :
    Contained t' r n ↔ Contained t r n := by
  unfold Contained
  simp only [h n, h.root hwf hwf', h.lengthOf, bpBefore_congr h]

theorem containedChildren_congr (hwf : WellFormed t) (hwf' : WellFormed t') {ca : NodeId}
    {cs : List NodeId} : ContainedChildren t' r ca cs ↔ ContainedChildren t r ca cs := by
  unfold ContainedChildren
  simp only [h.childrenOf, contained_congr h hwf hwf']

theorem setup_congr (hwf : WellFormed t) (hwf' : WellFormed t') {ca : NodeId} {fp lp : Option NodeId}
    {cs : List NodeId} : Setup t' r ca fp lp cs ↔ Setup t r ca fp lp cs :=
  ⟨fun hs => ⟨(commonAncestor_congr h).mp hs.common, (firstPartial_congr h).mp hs.first,
      (lastPartial_congr h).mp hs.last, (containedChildren_congr h hwf hwf').mp hs.contained⟩,
    fun hs => ⟨(commonAncestor_congr h).mpr hs.common, (firstPartial_congr h).mpr hs.first,
      (lastPartial_congr h).mpr hs.last, (containedChildren_congr h hwf hwf').mpr hs.contained⟩⟩

theorem isCharacterData_tree_congr {n : NodeId} : IsCharacterData t' n ↔ IsCharacterData t n := by
  unfold IsCharacterData; rw [h n]

theorem kindIs_congr {n : NodeId} {k : NodeKind} : KindIs t' n k ↔ KindIs t n k := by
  unfold KindIs; rw [h n]

theorem general_congr : General t' r ↔ General t r := by
  unfold General; rw [isCharacterData_tree_congr h]

theorem deleteNewBP_congr {bp : BoundaryPoint} : DeleteNewBP t' r bp ↔ DeleteNewBP t r bp := by
  unfold DeleteNewBP
  simp only [h.inclusiveAncestor_iff, h.parentOf, h.index]

theorem substringResult_congr {n : NodeId} {o c : Nat} {res : Except DOMException String} :
    SubstringResult t' n o c res ↔ SubstringResult t n o c res := by
  unfold SubstringResult; rw [h n]

end Transport

/-! ## 一つの木で一つに決まる -/

/-- 述語を満たす最初の要素は一つに決まる。 -/
theorem first_split_unique {P : NodeId → Prop} :
    ∀ {A B A' B' : List NodeId} {c c' : NodeId}, A ++ c :: B = A' ++ c' :: B' → P c → P c' →
      (∀ x ∈ A, ¬ P x) → (∀ x ∈ A', ¬ P x) → c = c'
  | [], _, [], _, _, _, he, _, _, _, _ => (List.cons.inj he).1
  | [], _, y :: A', _, _, _, he, hc, _, _, hA' => by
    have := (List.cons.inj he).1; subst this; exact absurd hc (hA' _ (by simp))
  | x :: A, _, [], _, _, _, he, _, hc', hA, _ => by
    have := (List.cons.inj he).1; subst this; exact absurd hc' (hA _ (by simp))
  | x :: A, B, y :: A', B', c, c', he, hc, hc', hA, hA' => by
    have := (List.cons.inj he).2
    exact first_split_unique this hc hc' (fun z hz => hA z (by simp [hz]))
      (fun z hz => hA' z (by simp [hz]))

theorem firstPartial_unique {t : Tree} {r : RangeState} {ca : NodeId} {fp₁ fp₂ : Option NodeId}
    (h₁ : FirstPartial t r ca fp₁) (h₂ : FirstPartial t r ca fp₂) : fp₁ = fp₂ := by
  cases fp₁ with
  | none =>
    cases fp₂ with
    | none => rfl
    | some c =>
      obtain ⟨hn, A, B, hl, hpc, -⟩ := h₂
      rcases h₁ with h | h
      · exact absurd h hn
      · exact absurd hpc (h c (by rw [hl]; simp))
  | some c =>
    cases fp₂ with
    | none =>
      obtain ⟨hn, A, B, hl, hpc, -⟩ := h₁
      rcases h₂ with h | h
      · exact absurd h hn
      · exact absurd hpc (h c (by rw [hl]; simp))
    | some c' =>
      obtain ⟨-, A, B, hl, hpc, hA⟩ := h₁
      obtain ⟨-, A', B', hl', hpc', hA'⟩ := h₂
      rw [first_split_unique (hl.symm.trans hl') hpc hpc' hA hA']

theorem lastPartial_unique {t : Tree} {r : RangeState} {ca : NodeId} {lp₁ lp₂ : Option NodeId}
    (h₁ : LastPartial t r ca lp₁) (h₂ : LastPartial t r ca lp₂) : lp₁ = lp₂ := by
  cases lp₁ with
  | none =>
    cases lp₂ with
    | none => rfl
    | some c =>
      obtain ⟨hn, A, B, hl, hpc, -⟩ := h₂
      rcases h₁ with h | h
      · exact absurd h hn
      · exact absurd hpc (h c (by rw [hl]; simp))
  | some c =>
    cases lp₂ with
    | none =>
      obtain ⟨hn, A, B, hl, hpc, -⟩ := h₁
      rcases h₂ with h | h
      · exact absurd h hn
      · exact absurd hpc (h c (by rw [hl]; simp))
    | some c' =>
      obtain ⟨-, A, B, hl, hpc, hB⟩ := h₁
      obtain ⟨-, A', B', hl', hpc', hB'⟩ := h₂
      have he : B.reverse ++ c :: A.reverse = B'.reverse ++ c' :: A'.reverse := by
        have := congrArg List.reverse (hl.symm.trans hl')
        simpa using this
      rw [first_split_unique he hpc hpc' (fun x hx => hB x (List.mem_reverse.mp hx))
        (fun x hx => hB' x (List.mem_reverse.mp hx))]

/-- 重複の無い列の部分列は、どの要素を含むかで決まる。 -/
theorem sublist_eq_of_mem_iff :
    ∀ {L l₁ l₂ : List NodeId}, L.Nodup → l₁.Sublist L → l₂.Sublist L →
      (∀ x ∈ L, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], l₁, l₂, _, h₁, h₂, _ => by rw [List.sublist_nil.mp h₁, List.sublist_nil.mp h₂]
  | a :: L, l₁, l₂, hnd, h₁, h₂, hm => by
    have hnd' := List.nodup_cons.mp hnd
    have hm' : ∀ x ∈ L, x ∈ l₁ ↔ x ∈ l₂ := fun x hx => hm x (by simp [hx])
    cases h₁ with
    | cons _ s₁ =>
      cases h₂ with
      | cons _ s₂ => exact sublist_eq_of_mem_iff hnd'.2 s₁ s₂ hm'
      | cons_cons _ s₂ =>
        exact absurd ((hm a (by simp)).mpr (by simp)) (fun ha => hnd'.1 (s₁.subset ha))
    | cons_cons _ s₁ =>
      cases h₂ with
      | cons _ s₂ =>
        exact absurd ((hm a (by simp)).mp (by simp)) (fun ha => hnd'.1 (s₂.subset ha))
      | cons_cons _ s₂ =>
        rename_i l₁' l₂'
        have hm'' : ∀ x ∈ L, x ∈ l₁' ↔ x ∈ l₂' := by
          intro x hx
          have hxa : x ≠ a := fun he => hnd'.1 (he ▸ hx)
          have := hm' x hx
          simp only [List.mem_cons, hxa, false_or] at this
          exact this
        rw [sublist_eq_of_mem_iff hnd'.2 s₁ s₂ hm'']

theorem containedChildren_unique {t : Tree} (hwf : WellFormed t) {r : RangeState} {ca : NodeId}
    {cs₁ cs₂ : List NodeId} (h₁ : ContainedChildren t r ca cs₁) (h₂ : ContainedChildren t r ca cs₂) :
    cs₁ = cs₂ := by
  have hnd : (childrenOf t ca).Nodup := by
    cases hc : t.get? ca with
    | none => rw [childrenOf_eq_nil_of_get?_eq_none hc]; exact List.nodup_nil
    | some d => rw [childrenOf_eq hc]; exact hwf.children_nodup ca d hc
  exact sublist_eq_of_mem_iff hnd h₁.1 h₂.1 fun x hx => (h₁.2 x hx).trans (h₂.2 x hx).symm

theorem setup_unique {t : Tree} (hwf : WellFormed t) {r : RangeState} {ca₁ ca₂ : NodeId}
    {fp₁ fp₂ lp₁ lp₂ : Option NodeId} {cs₁ cs₂ : List NodeId}
    (h₁ : Setup t r ca₁ fp₁ lp₁ cs₁) (h₂ : Setup t r ca₂ fp₂ lp₂ cs₂) :
    ca₁ = ca₂ ∧ fp₁ = fp₂ ∧ lp₁ = lp₂ ∧ cs₁ = cs₂ := by
  have hca := commonAncestor_unique h₁.common h₂.common
  subst hca
  exact ⟨rfl, firstPartial_unique h₁.first h₂.first, lastPartial_unique h₁.last h₂.last,
    containedChildren_unique hwf h₁.contained h₂.contained⟩

/-- substring data の関係を満たす結果は、実行関数の結果である。 -/
theorem substringResult_eq {t : Tree} {n : NodeId} {o c : Nat} {res : Except DOMException String}
    (h : SubstringResult t n o c res) : res = substringData t n o c := by
  obtain ⟨d, hd, hk, hcase⟩ := h
  have hs := substringData_result_sound hd hk o c
  obtain ⟨d', hd', -, hcase'⟩ := hs
  rw [hd] at hd'; cases hd'
  rcases hcase with ⟨hlt, rfl⟩ | ⟨hge, cc, hcc, hres⟩ <;>
    rcases hcase' with ⟨hlt', he'⟩ | ⟨hge', cc', hcc', hres'⟩
  · exact he'.symm
  · omega
  · omega
  · have hce := clampedCount_unique hcc hcc'
    subst hce
    rcases hres with ⟨pre, mid, post, hsp, hpre, hmid, rfl⟩ | ⟨hno, rfl⟩ <;>
      rcases hres' with ⟨pre', mid', post', hsp', hpre', hmid', he'⟩ | ⟨hno', he'⟩
    · rw [he']
      have h1 := Utf16.splitAt?_of_split pre (mid ++ post)
      have h1' := Utf16.splitAt?_of_split pre' (mid' ++ post')
      rw [hpre, ← List.append_assoc, ← hsp] at h1
      rw [hpre', ← List.append_assoc, ← hsp'] at h1'
      rw [h1] at h1'
      simp only [Option.some.injEq, Prod.mk.injEq] at h1'
      obtain ⟨rfl, hrest⟩ := h1'
      have h2 := Utf16.splitAt?_of_split mid post
      have h2' := Utf16.splitAt?_of_split mid' post'
      rw [hmid, hrest] at h2
      rw [hmid', h2] at h2'
      simp only [Option.some.injEq, Prod.mk.injEq] at h2'
      rw [h2'.1]
    · exact absurd ⟨pre, mid, post, hsp, hpre, hmid⟩ hno'
    · exact absurd ⟨pre', mid', post', hsp', hpre', hmid'⟩ hno
    · exact he'.symm

theorem substringResult_unique {t t' : Tree} (h : TreeObsEq t t') {n : NodeId} {o c : Nat}
    {r₁ r₂ : Except DOMException String} (h₁ : SubstringResult t n o c r₁)
    (h₂ : SubstringResult t' n o c r₂) : r₁ = r₂ :=
  (substringResult_eq h₁).trans (substringResult_eq ((substringResult_congr h).mp h₂)).symm

/-! ## 段ごとの completeness

どれも、admissible な状態 `s` で走る実行関数の結果と、観測の等しい状態 `sb` で関係を満たす結果を比べる。
-/

/-- CharacterData の一部を写す段の関係は、観測の等しい入力から観測の等しい結果を出す。 -/
theorem dataPartResult_congr {cut : Bool} {s sb : DOMState} {n into : NodeId} {o c : Nat}
    {r₁ r₂ : Except DOMException DOMState} (hv : AdmissibleDOMState s) (h : ObsEq s sb)
    (h₁ : DataPartResult .model cut s n o c into r₁) (h₂ : DataPartResult .model cut sb n o c into r₂) :
    ResultObsEq r₁ r₂ := by
  rcases h₁ with ⟨e₁, hs₁, rfl⟩ | ⟨x₁, c₁, s₁, hs₁, ⟨d₁, hd₁, rfl, hobs₁⟩, ht₁⟩ <;>
    rcases h₂ with ⟨e₂, hs₂, rfl⟩ | ⟨x₂, c₂, s₂, hs₂, ⟨d₂, hd₂, rfl, hobs₂⟩, ht₂⟩
  · cases substringResult_unique h.tree hs₁ hs₂; rfl
  · cases substringResult_unique h.tree hs₁ hs₂
  · cases substringResult_unique h.tree hs₁ hs₂
  · cases substringResult_unique h.tree hs₁ hs₂
    rw [h.tree n, hd₁] at hd₂
    cases hd₂
    obtain ⟨hcid, hcobs⟩ := cloneSingle_congr h { d₁ with data := x₁ } d₁.ownerDocument
    rw [hcid] at ht₂
    have hobs : ObsEq s₁ s₂ := (hobs₁.symm.trans hcobs).trans hobs₂
    have hwf₁ : WellFormed s₁.tree :=
      hobs₁.tree.wellFormed (admissible_cloneSingle_data x₁ hv hd₁).wellFormed
    refine andThen_congr (fun _ _ ha hb => preInsertResult_congr hwf₁ hobs ha hb) ?_ ht₁ ht₂
    intro u u' _ hu q₁ q₂ hq₁ hq₂
    rcases hq₁ with ⟨hc₁, hr₁⟩ | ⟨hc₁, rfl⟩ <;> rcases hq₂ with ⟨hc₂, hr₂⟩ | ⟨hc₂, rfl⟩
    · exact replaceDataResult_congr hu hr₁ hr₂
    · rw [hc₁] at hc₂; cases hc₂
    · rw [hc₁] at hc₂; cases hc₂
    · exact hu

/-- CharacterData の一部を写す段。 -/
theorem dataPart_complete {cut : Bool} {s sb : DOMState} {n into : NodeId} {o c : Nat}
    {res : Except DOMException DOMState} (hv : AdmissibleDOMState s) (h : ObsEq s sb)
    (hrel : DataPartResult .model cut sb n o c into res)
    (hne : dropErr (dataPart cut s n o c into) ≠ .error .outsideModel) :
    ResultObsEq (dropErr (dataPart cut s n o c into)) res := by
  have hn : InTree s.tree n := by
    rcases hrel with ⟨_, ⟨d, hd, -⟩, -⟩ | ⟨_, _, _, ⟨d, hd, -⟩, -⟩ <;>
      exact ⟨d, by rw [← h.tree n]; exact hd⟩
  exact dataPartResult_congr hv h (dataPart_sound allocSound_model hv hn hne) hrel

/-- 実行関数の pre-insert と、観測の等しい状態での関係の pre-insert を比べる。 -/
theorem preInsert_complete {s sb : DOMState} (hv : AdmissibleDOMState s) (h : ObsEq s sb)
    {c p : NodeId} {res : Except DOMException DOMState} (hrel : PreInsertResult sb c p none res) :
    ResultObsEq (preInsert s c p none) res :=
  preInsertResult_congr hv.wellFormed h (preInsert_result_sound hv.wellFormed c p none) hrel

/-- contained children を順に append する段（extract の step 18）。 -/
theorem appendEach_complete {into : NodeId} :
    ∀ (cs : List NodeId) {s sb : DOMState} {res : Except DOMException DOMState},
      AdmissibleDOMState s → ObsEq s sb → AppendEachResult into sb cs res →
      ResultObsEq (dropErr (appendEach s into cs)) res
  | [], s, sb, res, _, h, hrel => by cases hrel; exact h
  | c :: cs, s, sb, res, hv, h, hrel => by
    unfold appendEach
    unfold append
    rcases hrel with ⟨e', he', rfl⟩ | ⟨s₁', hs₁', hrest⟩
    · have := preInsert_complete hv h he'
      cases hpi : preInsert s c into none with
      | error e => rw [hpi] at this; exact this
      | ok s₁ => rw [hpi] at this; exact this.elim
    · have := preInsert_complete hv h hs₁'
      cases hpi : preInsert s c into none with
      | error e => rw [hpi] at this; exact this.elim
      | ok s₁ =>
        rw [hpi] at this
        exact appendEach_complete cs (admissible_preInsert hv hpi) this hrest

/-- contained children を subtree ごと clone して append する段（clone the contents の step 14）。 -/
theorem cloneEach_complete {into : NodeId} :
    ∀ (cs : List NodeId) {s sb : DOMState} {res : Except DOMException DOMState},
      AdmissibleDOMState s → ObsEq s sb → CloneEachResult .model into sb cs res →
      ResultObsEq (dropErr (cloneEach s into cs)) res
  | [], s, sb, res, _, h, hrel => by cases hrel; exact h
  | c :: cs, s, sb, res, hv, h, hrel => by
    obtain ⟨copy, s₁', ⟨d, s'', hd, hc'', hobs''⟩, hthen⟩ := hrel
    have hd' : s.tree.get? c = some d := by rw [← h.tree c]; exact hd
    have hdoc := hv.wellFormed.ownerDocument_is_document c d hd'
    obtain ⟨copy₀, s₁, hc⟩ := cloneNodeIn_isOk (subtree := true) hv hdoc hd'
    obtain ⟨hcopy, hobs₁⟩ := cloneNodeIn_congr hv hdoc h hc hc''
    subst hcopy
    have hobs : ObsEq s₁ s₁' := hobs₁.trans hobs''
    have hv₁ := admissible_cloneNodeIn hv hdoc hc
    unfold cloneEach
    rw [hd']
    simp only []
    rw [hc]
    simp only []
    unfold append
    rcases hthen with ⟨e', he', rfl⟩ | ⟨s₂', hs₂', hrest⟩
    · have := preInsert_complete hv₁ hobs he'
      cases hpi : preInsert s₁ copy₀ into none with
      | error e => rw [hpi] at this; exact this
      | ok s₂ => rw [hpi] at this; exact this.elim
    · have := preInsert_complete hv₁ hobs hs₂'
      cases hpi : preInsert s₁ copy₀ into none with
      | error e => rw [hpi] at this; exact this.elim
      | ok s₂ =>
        rw [hpi] at this
        exact cloneEach_complete cs (admissible_preInsert hv₁ hpi) this hrest

/-- 再帰した extract（clone the contents）の completeness。 -/
def RecurComplete (cut : Bool) (recur : Recur) : Prop :=
  ∀ s sb r c res, AdmissibleDOMState s → InTree s.tree r.start.node → InTree s.tree r.«end».node →
    ObsEq s sb → ContentsInto .model cut sb r none c res →
    dropErr (recur s r c) ≠ .error .outsideModel → ResultObsEq (dropErr (recur s r c)) res

/-- subrange を subfragment へ extract し、clone に append する段。 -/
theorem subContents_complete {cut : Bool} {recur : Recur} {s sb : DOMState} {r : RangeState} {c : NodeId}
    {res : Except DOMException DOMState} (hrec : RecurComplete cut recur)
    (hrk : ∀ s₀, RecurClosed (Keeps s₀) recur) (hv : AdmissibleDOMState s)
    (hs : InTree s.tree r.start.node) (he : InTree s.tree r.«end».node) (h : ObsEq s sb)
    (hrel : SubContents .model cut sb r c res)
    (hne : dropErr (subContents recur s r c) ≠ .error .outsideModel) :
    ResultObsEq (dropErr (subContents recur s r c)) res := by
  obtain ⟨sd, hsd⟩ := hs
  have hdoc : IsDocumentIn s sd.ownerDocument := hv.wellFormed.ownerDocument_is_document _ sd hsd
  have hfr : rangeFragment s r =
      .ok (withFresh s { kind := .documentFragment, ownerDocument := sd.ownerDocument }) := by
    unfold rangeFragment
    rw [hsd]
    exact createDocumentFragment_of_isDocumentIn hdoc
  have hcr : CreatesNode s
      (withFresh s { kind := .documentFragment, ownerDocument := sd.ownerDocument }).1
      (withFresh s { kind := .documentFragment, ownerDocument := sd.ownerDocument }).2
      { kind := .documentFragment, ownerDocument := sd.ownerDocument } :=
    createDocumentFragment_creates (createDocumentFragment_of_isDocumentIn hdoc)
  obtain ⟨hwid, hwobs⟩ := withFresh_congr h { kind := .documentFragment, ownerDocument := sd.ownerDocument }
  unfold subContents at hne ⊢
  rw [hfr] at hne ⊢
  cases hw : withFresh s { kind := .documentFragment, ownerDocument := sd.ownerDocument } with
  | mk sub s₁ =>
  rw [hw] at hcr hwid hwobs hne hfr
  simp only [] at hne hcr hwid hwobs ⊢
  have h₁ : AdmissibleDOMState s₁ := admissible_createsNode hv hcr
  have hk₁ : Keeps s s₁ := ⟨h₁, fun m d hm => ⟨d, rangeFragment_get? hfr hm, rfl⟩⟩
  -- 関係の subfragment は同じ id で、状態は観測が等しい
  have hfrag : ∀ {sd' sub' s₁'}, sb.tree.get? r.start.node = some sd' →
      Alloc.model.fragment sb sd'.ownerDocument sub' s₁' → sub' = sub ∧ ObsEq s₁ s₁' := by
    intro sd' sub' s₁' hsd' haf
    rw [show sb.tree.get? r.start.node = s.tree.get? r.start.node from h.tree _, hsd] at hsd'
    cases hsd'
    obtain ⟨rfl, hobs⟩ := haf
    exact ⟨hwid, hwobs.trans hobs⟩
  cases hrel with
  | error hsd' haf hci =>
    obtain ⟨hsub, hobs⟩ := hfrag hsd' haf
    rw [hsub] at hci
    cases hc : recur s₁ r sub with
    | error p =>
      obtain ⟨e', s'⟩ := p
      rw [hc] at hne
      have := hrec s₁ _ r sub _ h₁ (hk₁.inTree ⟨sd, hsd⟩) (hk₁.inTree he) hobs hci
        (by rw [hc]; simpa using hne)
      rw [hc] at this
      exact this
    | ok s₂ =>
      have := hrec s₁ _ r sub _ h₁ (hk₁.inTree ⟨sd, hsd⟩) (hk₁.inTree he) hobs hci (by rw [hc]; simp)
      rw [hc] at this
      exact this.elim
  | append hsd' haf hci hpr =>
    obtain ⟨hsub, hobs⟩ := hfrag hsd' haf
    rw [hsub] at hci hpr
    cases hc : recur s₁ r sub with
    | error p =>
      obtain ⟨e', s'⟩ := p
      rw [hc] at hne
      have := hrec s₁ _ r sub _ h₁ (hk₁.inTree ⟨sd, hsd⟩) (hk₁.inTree he) hobs hci
        (by rw [hc]; simpa using hne)
      rw [hc] at this
      exact this.elim
    | ok s₂ =>
      have := hrec s₁ _ r sub _ h₁ (hk₁.inTree ⟨sd, hsd⟩) (hk₁.inTree he) hobs hci (by rw [hc]; simp)
      rw [hc] at this
      have h₂ : AdmissibleDOMState s₂ := (hrk s₁ _ _ _ _ (keeps_refl h₁) hc).1
      simp only [dropErr_failWith]
      exact preInsert_complete h₂ this hpr

/-- partially contained child の clone を append する所。関係の clone は実行関数の clone と同じ id で、観測が等しい。 -/
theorem single_clone_congr {s sb : DOMState} (h : ObsEq s sb) {x c : NodeId} {fd fd' : NodeData}
    {s₁' : DOMState} (hfd : s.tree.get? x = some fd) (hfd' : sb.tree.get? x = some fd')
    (hs : Alloc.model.single sb x fd'.data c s₁') :
    c = (cloneSingle s fd fd.ownerDocument).1 ∧ ObsEq (cloneSingle s fd fd.ownerDocument).2 s₁' := by
  have hfe : fd' = fd := by
    rw [← h.tree x, hfd'] at hfd; exact Option.some.inj hfd
  rw [hfe] at hs hfd'
  obtain ⟨d, hd, rfl, hobs⟩ := hs
  rw [hfd'] at hd
  have hde : fd = d := Option.some.inj hd
  rw [← hde] at hobs ⊢
  obtain ⟨hcid, hcobs⟩ := cloneSingle_congr h { fd with data := fd.data } fd.ownerDocument
  exact ⟨hcid, hcobs.trans hobs⟩

/-- first partially contained child の段。 -/
theorem partialFirst_complete {cut : Bool} {recur : Recur} {s sb : DOMState} {r : RangeState}
    {fp : Option NodeId} {into : NodeId} {res : Except DOMException DOMState}
    (hrec : RecurComplete cut recur) (hrk : ∀ s₀, RecurClosed (Keeps s₀) recur)
    (hv : AdmissibleDOMState s) (hstart : InTree s.tree r.start.node) (h : ObsEq s sb)
    (hfp : ∀ x, fp = some x → ∃ xd, s.tree.get? x = some xd ∧ xd.kind ≠ .document)
    (hrel : PartialFirst .model cut sb r fp into res)
    (hne : dropErr (partialFirst cut recur s r fp into) ≠ .error .outsideModel) :
    ResultObsEq (dropErr (partialFirst cut recur s r fp into)) res := by
  unfold partialFirst at hne ⊢
  cases hrel with
  | none => exact h
  | @data _ _ x _ _ hcd hdp =>
    obtain ⟨fd, hfd, -⟩ := hfp x rfl
    have hk : fd.kind.isCharacterData = true := by
      obtain ⟨d, hd, hk⟩ := (isCharacterData_tree_congr h.tree).mp hcd
      rw [hfd] at hd; cases hd; exact hk
    simp only [hfd, hk, if_true] at hne ⊢
    rw [show lengthOf sb.tree r.start.node = lengthOf s.tree r.start.node from h.tree.lengthOf _] at hdp
    exact dataPart_complete hv h hdp hne
  | @cloneError _ _ x _ c s₁' e hin hncd hcl hpr =>
    obtain ⟨fd, hfd, hfnd⟩ := hfp x rfl
    obtain ⟨fd', hfd', hsingle⟩ := hcl
    have hk : fd.kind.isCharacterData = false := by
      cases hk : fd.kind.isCharacterData with
      | false => rfl
      | true => exact absurd ((isCharacterData_tree_congr h.tree).mpr ⟨fd, hfd, hk⟩) hncd
    obtain ⟨hcid, hcobs⟩ := single_clone_congr h hfd hfd' hsingle
    subst hcid
    simp only [hfd, hk, Bool.false_eq_true, if_false] at hne ⊢
    have hv₁ : AdmissibleDOMState (cloneSingle s fd fd.ownerDocument).2 :=
      admissible_cloneSingle_data fd.data hv hfd
    have := preInsert_complete hv₁ hcobs hpr
    unfold appendShallowClone at hne ⊢
    simp only [] at hne ⊢
    unfold append at hne ⊢
    cases hpi : preInsert (cloneSingle s fd fd.ownerDocument).2 (cloneSingle s fd fd.ownerDocument).1
        into none with
    | error e' => rw [hpi] at this; exact this
    | ok s₂ => rw [hpi] at this; exact this.elim
  | @recurse _ _ x _ c s₁' s₂' _ hin hncd hcl hpr hsub =>
    obtain ⟨fd, hfd, hfnd⟩ := hfp x rfl
    obtain ⟨fd', hfd', hsingle⟩ := hcl
    have hk : fd.kind.isCharacterData = false := by
      cases hk : fd.kind.isCharacterData with
      | false => rfl
      | true => exact absurd ((isCharacterData_tree_congr h.tree).mpr ⟨fd, hfd, hk⟩) hncd
    obtain ⟨hcid, hcobs⟩ := single_clone_congr h hfd hfd' hsingle
    subst hcid
    simp only [hfd, hk, Bool.false_eq_true, if_false] at hne ⊢
    have hv₁ : AdmissibleDOMState (cloneSingle s fd fd.ownerDocument).2 :=
      admissible_cloneSingle_data fd.data hv hfd
    have hpre := preInsert_complete hv₁ hcobs hpr
    have hkeep₁ : Keeps s (cloneSingle s fd fd.ownerDocument).2 :=
      (keeps_contentsClosed s).cloneSingleData fd.data (keeps_refl hv) hfd
    unfold appendShallowClone at hne ⊢
    simp only [] at hne ⊢
    unfold append at hne ⊢
    cases hpi : preInsert (cloneSingle s fd fd.ownerDocument).2 (cloneSingle s fd fd.ownerDocument).1
        into none with
    | error e' => rw [hpi] at hpre; exact hpre.elim
    | ok s₂ =>
      rw [hpi] at hpre hne
      simp only [] at hne ⊢
      have hk₂ : Keeps s s₂ := hkeep₁.trans ⟨admissible_preInsert hkeep₁.1 hpi, fun m d hm => by
        exact keeps_of_shapePreserving (shapePreserving_preInsert hpi) hm⟩
      rw [show lengthOf s₂'.tree x = lengthOf s₂.tree x from hpre.tree.lengthOf _] at hsub
      exact subContents_complete hrec hrk hk₂.1 (hk₂.inTree hstart) (hk₂.inTree ⟨fd, hfd⟩) hpre hsub hne

/-- last partially contained child の段。 -/
theorem partialLast_complete {cut : Bool} {recur : Recur} {s sb : DOMState} {r : RangeState}
    {lp : Option NodeId} {into : NodeId} {res : Except DOMException DOMState}
    (hrec : RecurComplete cut recur) (hrk : ∀ s₀, RecurClosed (Keeps s₀) recur)
    (hv : AdmissibleDOMState s) (hend : InTree s.tree r.«end».node) (h : ObsEq s sb)
    (hlp : ∀ x, lp = some x → ∃ xd, s.tree.get? x = some xd ∧ xd.kind ≠ .document)
    (hrel : PartialLast .model cut sb r lp into res)
    (hne : dropErr (partialLast cut recur s r lp into) ≠ .error .outsideModel) :
    ResultObsEq (dropErr (partialLast cut recur s r lp into)) res := by
  unfold partialLast at hne ⊢
  cases hrel with
  | none => exact h
  | @data _ _ x _ _ hcd hdp =>
    obtain ⟨ld, hld, -⟩ := hlp x rfl
    have hk : ld.kind.isCharacterData = true := by
      obtain ⟨d, hd, hk⟩ := (isCharacterData_tree_congr h.tree).mp hcd
      rw [hld] at hd; cases hd; exact hk
    simp only [hld, hk, if_true] at hne ⊢
    exact dataPart_complete hv h hdp hne
  | @cloneError _ _ x _ c s₁' e hin hncd hcl hpr =>
    obtain ⟨ld, hld, hlnd⟩ := hlp x rfl
    obtain ⟨ld', hld', hsingle⟩ := hcl
    have hk : ld.kind.isCharacterData = false := by
      cases hk : ld.kind.isCharacterData with
      | false => rfl
      | true => exact absurd ((isCharacterData_tree_congr h.tree).mpr ⟨ld, hld, hk⟩) hncd
    obtain ⟨hcid, hcobs⟩ := single_clone_congr h hld hld' hsingle
    subst hcid
    simp only [hld, hk, Bool.false_eq_true, if_false] at hne ⊢
    have hv₁ : AdmissibleDOMState (cloneSingle s ld ld.ownerDocument).2 :=
      admissible_cloneSingle_data ld.data hv hld
    have := preInsert_complete hv₁ hcobs hpr
    unfold appendShallowClone at hne ⊢
    simp only [] at hne ⊢
    unfold append at hne ⊢
    cases hpi : preInsert (cloneSingle s ld ld.ownerDocument).2 (cloneSingle s ld ld.ownerDocument).1
        into none with
    | error e' => rw [hpi] at this; exact this
    | ok s₂ => rw [hpi] at this; exact this.elim
  | @recurse _ _ x _ c s₁' s₂' _ hin hncd hcl hpr hsub =>
    obtain ⟨ld, hld, hlnd⟩ := hlp x rfl
    obtain ⟨ld', hld', hsingle⟩ := hcl
    have hk : ld.kind.isCharacterData = false := by
      cases hk : ld.kind.isCharacterData with
      | false => rfl
      | true => exact absurd ((isCharacterData_tree_congr h.tree).mpr ⟨ld, hld, hk⟩) hncd
    obtain ⟨hcid, hcobs⟩ := single_clone_congr h hld hld' hsingle
    subst hcid
    simp only [hld, hk, Bool.false_eq_true, if_false] at hne ⊢
    have hv₁ : AdmissibleDOMState (cloneSingle s ld ld.ownerDocument).2 :=
      admissible_cloneSingle_data ld.data hv hld
    have hpre := preInsert_complete hv₁ hcobs hpr
    have hkeep₁ : Keeps s (cloneSingle s ld ld.ownerDocument).2 :=
      (keeps_contentsClosed s).cloneSingleData ld.data (keeps_refl hv) hld
    unfold appendShallowClone at hne ⊢
    simp only [] at hne ⊢
    unfold append at hne ⊢
    cases hpi : preInsert (cloneSingle s ld ld.ownerDocument).2 (cloneSingle s ld ld.ownerDocument).1
        into none with
    | error e' => rw [hpi] at hpre; exact hpre.elim
    | ok s₂ =>
      rw [hpi] at hpre hne
      simp only [] at hne ⊢
      have hk₂ : Keeps s s₂ := hkeep₁.trans ⟨admissible_preInsert hkeep₁.1 hpi, fun m d hm => by
        exact keeps_of_shapePreserving (shapePreserving_preInsert hpi) hm⟩
      exact subContents_complete hrec hrk hk₂.1 (hk₂.inTree ⟨ld, hld⟩) (hk₂.inTree hend) hpre hsub hne

theorem selfSet_congr {s sb s₁ s₁' : DOMState} {self : Option Nat} {bp : BoundaryPoint}
    (h : ObsEq s sb) (h₁ : SelfSet s self bp s₁) (h₂ : SelfSet sb self bp s₁') : ObsEq s₁ s₁' := by
  rcases h₁ with ⟨hn, rfl⟩ | ⟨i, hi, rfl⟩ <;> rcases h₂ with ⟨hn', rfl⟩ | ⟨i', hi', rfl⟩
  · exact h
  · rw [hn] at hi'; cases hi'
  · rw [hi] at hn'; cases hn'
  · rw [hi] at hi'
    cases hi'
    have hr : sb.ranges = s.ranges := h.ranges
    exact ⟨⟨h.tree, by simp [hr], h.iterators, h.registrations, h.records, h.pendingObservers,
      h.microtaskQueued, h.walkers, h.listeners, h.detachedAttrs⟩, h.registrationOrder, h.pendingOrder⟩

/--
**extract と clone the contents の、step 1 の後の部分の completeness。** model の割り当ての関係を満たす結果は、
観測の等しい admissible な状態で走る実行関数の結果と、観測の上で等しい（実行関数が `outsideModel` でなければ）。
-/
theorem contentsInto_complete (cut : Bool) :
    ∀ (f : Nat) {s sb : DOMState} {r : RangeState} {self : Option Nat} {into : NodeId}
      {res : Except DOMException DOMState},
      AdmissibleDOMState s → InTree s.tree r.start.node → InTree s.tree r.«end».node → ObsEq s sb →
      ContentsInto .model cut sb r self into res →
      dropErr (contentsInto cut f s r self into) ≠ .error .outsideModel →
      ResultObsEq (dropErr (contentsInto cut f s r self into)) res
  | 0, s, sb, r, self, into, res, _, _, _, _, _, hne => by simp [contentsInto] at hne
  | f + 1, s, sb, r, self, into, res, hv, hs, he, h, hrel, hne => by
    have hwf := hv.wellFormed
    have hwfb : WellFormed sb.tree := h.tree.wellFormed hwf
    have hrec : RecurComplete cut (fun s' r' c => contentsInto cut f s' r' none c) :=
      fun _ _ _ _ _ h' hs' he' hobs' hrel' hne' => contentsInto_complete cut f h' hs' he' hobs' hrel' hne'
    have hrk : ∀ s₀, RecurClosed (Keeps s₀) (fun s' r' c => contentsInto cut f s' r' none c) :=
      fun s₀ _ _ _ _ hk hc => closed_contentsInto (keeps_contentsClosed s₀) cut f hk hc
    have hcharE : ∀ n, IsCharacterData sb.tree n ↔ IsCharacterData s.tree n :=
      fun _ => isCharacterData_tree_congr h.tree
    unfold contentsInto at hne ⊢
    -- step 2
    by_cases hcol : r.start = r.«end»
    · rw [if_pos (by simp [hcol])]
      cases hrel with
      | collapsed _ => exact h
      | single hc => exact absurd hcol hc
      | doctype hg => exact absurd hcol hg.1
      | firstError hg => exact absurd hcol hg.1
      | containedError hg => exact absurd hcol hg.1
      | last hg => exact absurd hcol hg.1
    rw [if_neg (by simpa using hcol)] at hne ⊢
    obtain ⟨sd, hsd⟩ := hs
    rw [hsd] at hne ⊢
    simp only [] at hne ⊢
    -- step 4
    by_cases hsingle : (r.start.node == r.«end».node && sd.kind.isCharacterData) = true
    · rw [if_pos hsingle] at hne ⊢
      simp only [Bool.and_eq_true, beq_iff_eq] at hsingle
      have hgen : ¬ General sb.tree r := fun hg =>
        hg.2 ⟨hsingle.1, (hcharE _).mpr ⟨sd, hsd, hsingle.2⟩⟩
      cases hrel with
      | collapsed hc => exact absurd hc hcol
      | single _ _ _ hdp => exact dataPart_complete hv h hdp hne
      | doctype hg => exact absurd hg hgen
      | firstError hg => exact absurd hg hgen
      | containedError hg => exact absurd hg hgen
      | last hg => exact absurd hg hgen
    rw [if_neg hsingle] at hne ⊢
    have hnotsingle : ∀ {res'}, ¬ (r.start.node = r.«end».node ∧ IsCharacterData sb.tree r.start.node ∧
        DataPartResult .model cut sb r.start.node r.start.offset (r.«end».offset - r.start.offset) into res') := by
      rintro res' ⟨heq, hcd, -⟩
      obtain ⟨d, hd, hk⟩ := (hcharE _).mp hcd
      rw [hsd] at hd; cases hd
      exact hsingle (by simp [heq, hk])
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
    have hsame : ∀ {ca' fp lp cs}, Setup sb.tree r ca' fp lp cs →
        ca' = ca ∧ fp = firstPartiallyContainedChild s.tree r ca ∧
          lp = lastPartiallyContainedChild s.tree r ca ∧ cs = containedChildren s.tree r ca :=
      fun hS => setup_unique hwf ((setup_congr h.tree hwf hwfb).mp hS) hsetup
    -- step 11
    by_cases hdt : ((containedChildren s.tree r ca).any
        fun c => kindOf s.tree c == some .documentType) = true
    · rw [if_pos hdt]
      have hdt' : ∃ c ∈ containedChildren s.tree r ca, KindIs s.tree c .documentType := by
        obtain ⟨c, hc, hck⟩ := List.any_eq_true.mp hdt
        refine ⟨c, hc, ?_⟩
        cases hkc : s.tree.get? c with
        | none => simp [kindOf, hkc] at hck
        | some cd => simp [kindOf, hkc] at hck; exact ⟨cd, hkc, hck⟩
      have hno : ∀ {cs}, Setup sb.tree r ca (firstPartiallyContainedChild s.tree r ca)
          (lastPartiallyContainedChild s.tree r ca) cs →
          (∀ c ∈ cs, ¬ KindIs sb.tree c .documentType) → False := by
        intro cs hS hn
        obtain ⟨-, -, -, rfl⟩ := hsame hS
        obtain ⟨c, hc, hk⟩ := hdt'
        exact hn c hc ((kindIs_congr h.tree).mpr hk)
      cases hrel with
      | collapsed hc => exact absurd hc hcol
      | single hc heq hcd hdp => exact (hnotsingle ⟨heq, hcd, hdp⟩).elim
      | doctype => rfl
      | firstError _ hS hn =>
        obtain ⟨rfl, rfl, rfl, -⟩ := hsame hS; exact (hno hS hn).elim
      | containedError _ hS hn =>
        obtain ⟨rfl, rfl, rfl, -⟩ := hsame hS; exact (hno hS hn).elim
      | last _ hS hn =>
        obtain ⟨rfl, rfl, rfl, -⟩ := hsame hS; exact (hno hS hn).elim
    rw [if_neg hdt] at hne ⊢
    have hnodt : ∀ c ∈ containedChildren s.tree r ca, ¬ KindIs s.tree c .documentType := by
      intro c hc ⟨cd, hcd, hck⟩
      exact hdt (List.any_eq_true.mpr ⟨c, hc, by simp [kindOf, hcd, hck]⟩)
    have hbp := deleteContentsNewBP_spec hwf hroot
    have hbpE : ∀ {bp}, DeleteNewBP sb.tree r bp → bp = deleteContentsNewBP s.tree r :=
      fun hb => deleteNewBP_unique ((deleteNewBP_congr h.tree).mp hb) hbp
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
    have hk₁ : Keeps s s₁ := closed_setSelf (keeps_contentsClosed s) (keeps_refl hv) hss
    have hfpar : ∀ x, firstPartiallyContainedChild s.tree r ca = some x →
        ∃ xd, s₁.tree.get? x = some xd ∧ xd.kind ≠ .document := by
      intro x hx
      have htree₁ : s₁.tree = s.tree := by rcases hself with ⟨-, rfl⟩ | ⟨i, -, rfl⟩ <;> rfl
      rw [htree₁]
      exact childOf_not_document hv (firstPartial_mem hsetup.first x hx)
    have hobs₁ : ∀ {s₁'}, SelfSet sb self (deleteContentsNewBP s.tree r) s₁' → ObsEq s₁ s₁' :=
      fun h₂ => selfSet_congr h hself h₂
    -- step 16-17
    cases hpf : partialFirst cut (fun s' r' c => contentsInto cut f s' r' none c) s₁ r
        (firstPartiallyContainedChild s.tree r ca) into with
    | error p =>
      obtain ⟨e, s'⟩ := p
      rw [hpf] at hne
      have hcmp : ∀ {s₁' res'}, SelfSet sb self (deleteContentsNewBP s.tree r) s₁' →
          PartialFirst .model cut s₁' r (firstPartiallyContainedChild s.tree r ca) into res' →
          ResultObsEq (.error e) res' := by
        intro s₁' res' hS hP
        have := partialFirst_complete hrec hrk hk₁.1 (hk₁.inTree ⟨sd, hsd⟩) (hobs₁ hS) hfpar hP
          (by rw [hpf]; simpa using hne)
        rw [hpf] at this
        exact this
      cases hrel with
      | collapsed hc => exact absurd hc hcol
      | single hc heq hcd hdp => exact (hnotsingle ⟨heq, hcd, hdp⟩).elim
      | doctype _ hS hd =>
        obtain ⟨rfl, -, -, rfl⟩ := hsame hS
        obtain ⟨c, hc, hk⟩ := hd
        exact (hnodt c hc ((kindIs_congr h.tree).mp hk)).elim
      | firstError _ hS _ hb hS₁ hP =>
        obtain ⟨rfl, rfl, -, -⟩ := hsame hS
        rw [hbpE hb] at hS₁
        exact hcmp hS₁ hP
      | containedError _ hS _ hb hS₁ hP =>
        obtain ⟨rfl, rfl, -, -⟩ := hsame hS
        rw [hbpE hb] at hS₁
        exact (hcmp hS₁ hP).elim
      | last _ hS _ hb hS₁ hP =>
        obtain ⟨rfl, rfl, -, -⟩ := hsame hS
        rw [hbpE hb] at hS₁
        exact (hcmp hS₁ hP).elim
    | ok s₂ =>
    rw [hpf] at hne
    simp only [] at hne ⊢
    have hk₂ : Keeps s s₂ := hk₁.trans
      (closed_partialFirst (keeps_contentsClosed s₁) (hrk s₁) (keeps_refl hk₁.1) hpf)
    have hobs₂ : ∀ {s₁' s₂'}, SelfSet sb self (deleteContentsNewBP s.tree r) s₁' →
        PartialFirst .model cut s₁' r (firstPartiallyContainedChild s.tree r ca) into (.ok s₂') →
        ObsEq s₂ s₂' := by
      intro s₁' s₂' hS hP
      have := partialFirst_complete hrec hrk hk₁.1 (hk₁.inTree ⟨sd, hsd⟩) (hobs₁ hS) hfpar hP
        (by rw [hpf]; simp)
      rw [hpf] at this
      exact this
    have hnoerr : ∀ {s₁' e}, SelfSet sb self (deleteContentsNewBP s.tree r) s₁' →
        ¬ PartialFirst .model cut s₁' r (firstPartiallyContainedChild s.tree r ca) into (.error e) := by
      intro s₁' e hS hP
      have := partialFirst_complete hrec hrk hk₁.1 (hk₁.inTree ⟨sd, hsd⟩) (hobs₁ hS) hfpar hP
        (by rw [hpf]; simp)
      rw [hpf] at this
      exact this
    -- step 18
    have hcs : ∀ {s₂' res'}, ObsEq s₂ s₂' →
        ContainedStep .model cut s₂' into (containedChildren s.tree r ca) res' →
        ResultObsEq (dropErr (if cut then appendEach s₂ into (containedChildren s.tree r ca)
          else cloneEach s₂ into (containedChildren s.tree r ca))) res' := by
      intro s₂' res' hobs hC
      rcases hC with ⟨rfl, hA⟩ | ⟨rfl, hB⟩
      · exact appendEach_complete _ hk₂.1 hobs hA
      · exact cloneEach_complete _ hk₂.1 hobs hB
    cases hcr : (if cut then appendEach s₂ into (containedChildren s.tree r ca)
        else cloneEach s₂ into (containedChildren s.tree r ca)) with
    | error p =>
      obtain ⟨e, s'⟩ := p
      rw [hcr] at hne hcs
      cases hrel with
      | collapsed hc => exact absurd hc hcol
      | single hc heq hcd hdp => exact (hnotsingle ⟨heq, hcd, hdp⟩).elim
      | doctype _ hS hd =>
        obtain ⟨rfl, -, -, rfl⟩ := hsame hS
        obtain ⟨c, hc, hk⟩ := hd
        exact (hnodt c hc ((kindIs_congr h.tree).mp hk)).elim
      | firstError _ hS _ hb hS₁ hP =>
        obtain ⟨rfl, rfl, -, -⟩ := hsame hS
        rw [hbpE hb] at hS₁
        exact (hnoerr hS₁ hP).elim
      | containedError _ hS _ hb hS₁ hP hC =>
        obtain ⟨rfl, rfl, -, rfl⟩ := hsame hS
        rw [hbpE hb] at hS₁
        exact hcs (hobs₂ hS₁ hP) hC
      | last _ hS _ hb hS₁ hP hC =>
        obtain ⟨rfl, rfl, -, rfl⟩ := hsame hS
        rw [hbpE hb] at hS₁
        exact (hcs (hobs₂ hS₁ hP) hC).elim
    | ok s₃ =>
    rw [hcr] at hne hcs
    simp only [] at hne ⊢
    have hk₃ : Keeps s s₃ := by
      refine hk₂.trans ?_
      cases cut with
      | true =>
        simp only [if_true] at hcr
        exact closed_appendEach (keeps_contentsClosed s₂) _ (keeps_refl hk₂.1) hcr
      | false =>
        simp only [Bool.false_eq_true, if_false] at hcr
        exact closed_cloneEach (keeps_contentsClosed s₂) _ (keeps_refl hk₂.1) hcr
    have hlpar : ∀ x, lastPartiallyContainedChild s.tree r ca = some x →
        ∃ xd, s₃.tree.get? x = some xd ∧ xd.kind ≠ .document := by
      intro x hx
      obtain ⟨xd, hxd, hxk⟩ := childOf_not_document hv (lastPartial_mem hsetup.last x hx)
      obtain ⟨xd', hxd', hk'⟩ := hk₃.2 x xd hxd
      exact ⟨xd', hxd', by rw [hk']; exact hxk⟩
    -- step 19-20
    cases hrel with
    | collapsed hc => exact absurd hc hcol
    | single hc heq hcd hdp => exact (hnotsingle ⟨heq, hcd, hdp⟩).elim
    | doctype _ hS hd =>
      obtain ⟨rfl, -, -, rfl⟩ := hsame hS
      obtain ⟨c, hc, hk⟩ := hd
      exact (hnodt c hc ((kindIs_congr h.tree).mp hk)).elim
    | firstError _ hS _ hb hS₁ hP =>
      obtain ⟨rfl, rfl, -, -⟩ := hsame hS
      rw [hbpE hb] at hS₁
      exact (hnoerr hS₁ hP).elim
    | containedError _ hS _ hb hS₁ hP hC =>
      obtain ⟨rfl, rfl, -, rfl⟩ := hsame hS
      rw [hbpE hb] at hS₁
      exact (hcs (hobs₂ hS₁ hP) hC).elim
    | last _ hS _ hb hS₁ hP hC hL =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hsame hS
      rw [hbpE hb] at hS₁
      have hobs₃ := hcs (hobs₂ hS₁ hP) hC
      exact partialLast_complete hrec hrk hk₃.1 (hk₃.inTree ⟨ed, hed⟩) hobs₃ hlpar hL hne

/-- 結果まで含めた関係を満たす結果と、実行関数の結果の対応（状態は観測の上で比べる）。 -/
def PairObsEq : Except DOMException (NodeId × DOMState) → Except DOMException (NodeId × DOMState) → Prop
  | .error e, .error e' => e = e'
  | .ok (a, s), .ok (b, s') => a = b ∧ ObsEq s s'
  | _, _ => False

/-- extract と clone the contents に共通の、step 1 から後の completeness。 -/
theorem contentsResult_complete (cut : Bool) {s : DOMState} {i : Nat} {r : RangeState}
    {self : Option Nat} (hv : AdmissibleDOMState s) (hr : s.ranges[i]? = some r)
    {res : Except DOMException (NodeId × DOMState)} (hres : ContentsResult .model cut s r self res)
    (hne : dropErr ((match rangeFragment s r with
        | .error e => .error (e, s)
        | .ok (frag, s₁) =>
          discardOnError frag ((contentsInto cut (s₁.tree.size + 1) s₁ r self frag).map (frag, ·))) :
        Except (DOMException × DOMState) (NodeId × DOMState)) ≠ .error .outsideModel) :
    PairObsEq res (dropErr ((match rangeFragment s r with
        | .error e => .error (e, s)
        | .ok (frag, s₁) =>
          discardOnError frag ((contentsInto cut (s₁.tree.size + 1) s₁ r self frag).map (frag, ·))) :
        Except (DOMException × DOMState) (NodeId × DOMState))) := by
  have hev := hv.rangeEndpoints r (List.mem_of_getElem? hr)
  obtain ⟨sd, hsd, -⟩ := hev.1
  obtain ⟨ed, hed, -⟩ := hev.2
  have hdoc : IsDocumentIn s sd.ownerDocument := hv.wellFormed.ownerDocument_is_document _ sd hsd
  have hfr : rangeFragment s r =
      .ok (withFresh s { kind := .documentFragment, ownerDocument := sd.ownerDocument }) := by
    unfold rangeFragment
    rw [hsd]
    exact createDocumentFragment_of_isDocumentIn hdoc
  have hcr : CreatesNode s
      (withFresh s { kind := .documentFragment, ownerDocument := sd.ownerDocument }).1
      (withFresh s { kind := .documentFragment, ownerDocument := sd.ownerDocument }).2
      { kind := .documentFragment, ownerDocument := sd.ownerDocument } :=
    createDocumentFragment_creates (createDocumentFragment_of_isDocumentIn hdoc)
  obtain ⟨sd', frag', s₁', hsd', ⟨hfid, hfobs⟩, hcase⟩ := hres
  rw [hsd] at hsd'
  cases hsd'
  rw [hfr] at hne ⊢
  cases hw : withFresh s { kind := .documentFragment, ownerDocument := sd.ownerDocument } with
  | mk frag s₁ =>
  rw [hw] at hcr hfid hfobs hfr hne
  simp only [] at hne hcr hfid hfobs ⊢
  rw [hfid] at hcase
  simp only [dropErr_discardOnError] at hne ⊢
  have h₁ : AdmissibleDOMState s₁ := admissible_createsNode hv hcr
  have hget : ∀ m md, s.tree.get? m = some md → s₁.tree.get? m = some md :=
    fun m md hm => rangeFragment_get? hfr hm
  rcases hcase with ⟨e, hci, rfl⟩ | ⟨s₂, hci, rfl⟩
  · have := contentsInto_complete cut _ h₁ ⟨sd, hget _ _ hsd⟩ ⟨ed, hget _ _ hed⟩ hfobs hci
      (by intro hx; apply hne; cases hc : contentsInto cut (s₁.tree.size + 1) s₁ r self frag with
        | error p => obtain ⟨e', s'⟩ := p; rw [hc] at hx; simpa [Except.map, dropErr] using hx
        | ok s₂ => rw [hc] at hx; simp [dropErr] at hx)
    cases hc : contentsInto cut (s₁.tree.size + 1) s₁ r self frag with
    | error p =>
      obtain ⟨e', s'⟩ := p
      rw [hc] at this
      simp only [dropErr, ResultObsEq] at this
      simp [Except.map, dropErr, PairObsEq, this]
    | ok s₂ => rw [hc] at this; exact this.elim
  · have := contentsInto_complete cut _ h₁ ⟨sd, hget _ _ hsd⟩ ⟨ed, hget _ _ hed⟩ hfobs hci
      (by intro hx; apply hne; cases hc : contentsInto cut (s₁.tree.size + 1) s₁ r self frag with
        | error p => obtain ⟨e', s'⟩ := p; rw [hc] at hx; simpa [Except.map, dropErr] using hx
        | ok s₂ => rw [hc] at hx; simp [dropErr] at hx)
    cases hc : contentsInto cut (s₁.tree.size + 1) s₁ r self frag with
    | error p => obtain ⟨e', s'⟩ := p; rw [hc] at this; exact this.elim
    | ok s₃ =>
      rw [hc] at this
      simp only [Except.map, dropErr]
      exact ⟨rfl, this.symm⟩

theorem PairObsEq.symm {x y : Except DOMException (NodeId × DOMState)} (h : PairObsEq x y) :
    PairObsEq y x := by
  rcases x with e | ⟨a, sa⟩ <;> rcases y with e' | ⟨b, sb⟩ <;> simp only [PairObsEq] at h ⊢
  · exact h.symm
  · exact ⟨h.1.symm, ObsEq.symm h.2⟩

theorem PairObsEq.trans {x y z : Except DOMException (NodeId × DOMState)} (h : PairObsEq x y)
    (h' : PairObsEq y z) : PairObsEq x z := by
  rcases x with e | ⟨a, sa⟩ <;> rcases y with e' | ⟨b, sb⟩ <;> rcases z with e'' | ⟨c, sc⟩ <;>
    simp only [PairObsEq] at h h' ⊢
  · exact h.trans h'
  · exact ⟨h.1.trans h'.1, ObsEq.trans h.2 h'.2⟩

/-- `extractContents()` の、subfragment を消す前の部分の completeness。 -/
theorem rangeExtractInto_result_complete {s : DOMState} {i : Nat} {r : RangeState}
    (hv : AdmissibleDOMState s) (hr : s.ranges[i]? = some r)
    {res : Except DOMException (NodeId × DOMState)} (hres : ContentsResult .model true s r (some i) res)
    (hne : dropErr (rangeExtractInto s i) ≠ .error .outsideModel) :
    PairObsEq res (dropErr (rangeExtractInto s i)) := by
  unfold rangeExtractInto at hne ⊢
  rw [hr] at hne ⊢
  exact contentsResult_complete true hv hr hres hne

theorem rangeCloneInto_result_complete {s : DOMState} {i : Nat} {r : RangeState}
    (hv : AdmissibleDOMState s) (hr : s.ranges[i]? = some r)
    {res : Except DOMException (NodeId × DOMState)} (hres : ContentsResult .model false s r none res)
    (hne : dropErr (rangeCloneInto s i) ≠ .error .outsideModel) :
    PairObsEq res (dropErr (rangeCloneInto s i)) := by
  unfold rangeCloneInto at hne ⊢
  rw [hr] at hne ⊢
  exact contentsResult_complete false hv hr hres hne

/-- `discardCreated` の前の結果との対応から、後の結果との対応を出す。 -/
theorem discardCreated_complete {res : Except DOMException (NodeId × DOMState)} (base : NodeId)
    {x : Except (DOMException × DOMState) (NodeId × DOMState)} (hx : PairObsEq res (dropErr x)) :
    (∃ e, res = .error e ∧ dropErr (discardCreated base x) = .error e) ∨
      (∃ frag s₂ s₂', res = .ok (frag, s₂) ∧ ObsEq s₂ s₂' ∧
        discardCreated base x = .ok (frag, discardAfter base s₂')) := by
  cases x with
  | error p =>
    obtain ⟨e, s'⟩ := p
    cases res with
    | error e' =>
      simp only [dropErr, PairObsEq] at hx
      exact Or.inl ⟨e', rfl, by simp [discardCreated, dropErr, hx]⟩
    | ok v => obtain ⟨a, sa⟩ := v; exact hx.elim
  | ok v =>
    obtain ⟨frag, s₂'⟩ := v
    cases res with
    | error e' => exact hx.elim
    | ok v' =>
      obtain ⟨frag₀, s₂⟩ := v'
      obtain ⟨rfl, hobs⟩ := hx
      exact Or.inr ⟨frag₀, s₂, s₂', rfl, hobs, rfl⟩

/--
**`extractContents()` の completeness。** model の割り当ての関係を満たす結果は、実行関数の結果と観測の上で
等しい（実行関数が `outsideModel` でなければ）。実行関数は最後に使い終えた subfragment を消すので、成功の状態は
関係の状態と観測の等しい状態からそれを消したものである。
-/
theorem rangeExtractContents_result_complete {s : DOMState} {i : Nat} {r : RangeState}
    (hv : AdmissibleDOMState s) (hr : s.ranges[i]? = some r)
    {res : Except DOMException (NodeId × DOMState)} (hres : ContentsResult .model true s r (some i) res)
    (hne : dropErr (rangeExtractContents s i) ≠ .error .outsideModel) :
    (∃ e, res = .error e ∧ dropErr (rangeExtractContents s i) = .error e) ∨
      (∃ frag s₂ s₂', res = .ok (frag, s₂) ∧ ObsEq s₂ s₂' ∧
        rangeExtractContents s i = .ok (frag, discardAfter (freshId s.tree) s₂')) := by
  unfold rangeExtractContents at hne ⊢
  exact discardCreated_complete _ (rangeExtractInto_result_complete hv hr hres
    fun he => hne ((dropErr_discardCreated _ _).mpr he))

/-- **`cloneContents()` の completeness。** -/
theorem rangeCloneContents_result_complete {s : DOMState} {i : Nat} {r : RangeState}
    (hv : AdmissibleDOMState s) (hr : s.ranges[i]? = some r)
    {res : Except DOMException (NodeId × DOMState)} (hres : ContentsResult .model false s r none res)
    (hne : dropErr (rangeCloneContents s i) ≠ .error .outsideModel) :
    (∃ e, res = .error e ∧ dropErr (rangeCloneContents s i) = .error e) ∨
      (∃ frag s₂ s₂', res = .ok (frag, s₂) ∧ ObsEq s₂ s₂' ∧
        rangeCloneContents s i = .ok (frag, discardAfter (freshId s.tree) s₂')) := by
  unfold rangeCloneContents at hne ⊢
  exact discardCreated_complete _ (rangeCloneInto_result_complete hv hr hres
    fun he => hne ((dropErr_discardCreated _ _).mpr he))

/--
**extract と clone the contents の関係は結果を一つに決める。** model の割り当ての関係を満たす二つの結果は、
例外が等しいか、同じ fragment で状態の観測が等しい（実行関数が `outsideModel` でなければ）。
-/
theorem contentsResult_deterministic {s : DOMState} {i : Nat} {r : RangeState}
    (hv : AdmissibleDOMState s) (hr : s.ranges[i]? = some r)
    {res₁ res₂ : Except DOMException (NodeId × DOMState)}
    (h₁ : ContentsResult .model true s r (some i) res₁) (h₂ : ContentsResult .model true s r (some i) res₂)
    (hne : dropErr (rangeExtractInto s i) ≠ .error .outsideModel) : PairObsEq res₁ res₂ :=
  (rangeExtractInto_result_complete hv hr h₁ hne).trans (rangeExtractInto_result_complete hv hr h₂ hne).symm

theorem cloneResult_deterministic {s : DOMState} {i : Nat} {r : RangeState}
    (hv : AdmissibleDOMState s) (hr : s.ranges[i]? = some r)
    {res₁ res₂ : Except DOMException (NodeId × DOMState)}
    (h₁ : ContentsResult .model false s r none res₁) (h₂ : ContentsResult .model false s r none res₂)
    (hne : dropErr (rangeCloneInto s i) ≠ .error .outsideModel) : PairObsEq res₁ res₂ :=
  (rangeCloneInto_result_complete hv hr h₁ hne).trans (rangeCloneInto_result_complete hv hr h₂ hne).symm

end Dom.Spec