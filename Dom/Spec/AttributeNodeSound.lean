import Dom.Spec.AttributeNode
import Dom.Spec.AttributeCongr
import Dom.Validity.AttrIdsAttr

/-!
# `Attr` を node として渡す API は関係を満たし、関係は結果を一つに決める

健全性・一意性・完全性をまとめて置く。どれも `Attr` の id が一意であること
（`AttrIdsUnique`）を前提にする。id で `Attr` を引く以上、同じ id の `Attr` が二つあれば
どちらを引くかが決まらないからである。
-/

namespace Dom.Spec

open Dom Dom.ListUtil

/-! ## 健全性：部品 -/

theorem attrIdUnattached_of_ownerElementOf {t : Tree} {s : DOMState} (ht : s.tree = t)
    {aid : AttrId} (h : ownerElementOf t aid = none) : AttrIdUnattached s aid := by
  intro m d hd b hb he
  rw [ht] at hd
  unfold ownerElementOf at h
  rw [List.find?_eq_none] at h
  have := h m (NodeStore.mem_keys_of_get?_eq_some hd)
  rw [show t.get? m = some d from hd] at this
  simp only [List.any_eq_true, beq_iff_eq, not_exists, not_and] at this
  exact this b hb he

/-- **`findAttr` は `AttrLocated` を満たす。** -/
theorem findAttr_spec (s : DOMState) (aid : AttrId) : AttrLocated s aid (findAttr s aid) := by
  cases hf : findAttr s aid with
  | some p =>
    obtain ⟨a, o⟩ := p
    cases o with
    | some n =>
      obtain ⟨d, hd, ha, hid⟩ := findAttr_attached hf
      exact ⟨hid, d, hd, ha⟩
    | none =>
      obtain ⟨ha, hid⟩ := findAttr_detached hf
      refine ⟨hid, ha, ?_⟩
      unfold findAttr at hf
      split at hf
      · split at hf
        · cases hf
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hf
          obtain ⟨_, _, _, h⟩ := hf
          cases h
      · next hown => exact attrIdUnattached_of_ownerElementOf rfl hown
  | none =>
    unfold findAttr at hf
    split at hf
    · next n hown =>
      have hsome := List.find?_some hown
      split at hsome
      · cases hsome
      · next d hd =>
        rw [hd] at hf
        simp only [Option.map_eq_none_iff, List.find?_eq_none] at hf
        simp only [List.any_eq_true] at hsome
        obtain ⟨b, hb, he⟩ := hsome
        exact absurd he (hf b hb)
    · next hown =>
      refine ⟨attrIdUnattached_of_ownerElementOf rfl hown, fun b hb he => ?_⟩
      simp only [Option.map_eq_none_iff, List.find?_eq_none] at hf
      exact hf b hb (by simp [he])

theorem receiverError_of_requireElement {s : DOMState} {element : NodeId} {e : DOMException}
    (h : requireElement s.tree element = .error e) : ReceiverError s element e := by
  unfold requireElement at h
  split at h
  · next hn => cases h; exact Or.inl ⟨hn, rfl⟩
  · next d hd =>
    split at h
    · next hk => cases h; exact Or.inr ⟨d, hd, by simpa using hk, rfl⟩
    · cases h

theorem removeDetached_taken {s : DOMState} (hu : AttrIdsUnique s) {a : Attr}
    (ha : a ∈ s.detachedAttrs) : AttrTakenFromDetached s (removeDetached s a.id) a := by
  obtain ⟨pre, post, hsplit, hpre⟩ := split_of_mem_id ha hu.detached
  refine ⟨pre, post, hsplit, hpre, ?_⟩
  unfold removeDetached
  rw [hsplit, eraseFirst_split pre post (fun x hx => by simpa using hpre x hx) (by simp)]

theorem replaceAttributeWith_spec {s : DOMState} (hwf : WellFormed s.tree) {element : NodeId}
    {d : NodeData} (hd : s.tree.get? element = some d) {old : Attr} (hmem : old ∈ d.attributes)
    (hnd : (d.attributes.map Attr.key).Nodup) (new : Attr) :
    AttributeReplacedWith s element d old new (replaceAttributeWith s element d old new) := by
  obtain ⟨pre, post, hsplit, hpre⟩ := split_of_mem hmem hnd
  have hlist : updateFirst (fun b => b.key == old.key)
      (fun _ => { new with ownerDocument := d.ownerDocument }) d.attributes =
      pre ++ { new with ownerDocument := d.ownerDocument } :: post := by
    rw [hsplit]
    exact updateFirst_split pre post (fun x hx => by simpa using hpre x hx) (by simp)
  unfold replaceAttributeWith
  let T := setAttributes s.tree element d (updateFirst (fun b => b.key == old.key)
    (fun _ => { new with ownerDocument := d.ownerDocument }) d.attributes)
  refine ⟨pre, post, { s with tree := T, detachedAttrs := s.detachedAttrs ++ [old] }, hd, hsplit,
    hpre, ?_, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · rw [← hlist]; exact attributesReplaced_setAttributes hd _
  · exact handleAttributeChanges_spec
      (wellFormed_of_attributesOnly (attributesOnly_setAttributes hd _) hwf) element old _

theorem detachAttribute_spec {s : DOMState} (hwf : WellFormed s.tree) {element : NodeId}
    {d : NodeData} (hd : s.tree.get? element = some d) {a : Attr} (hmem : a ∈ d.attributes)
    (hnd : (d.attributes.map (·.id)).Nodup) :
    AttributeDetached s element d a (detachAttribute s element d a) := by
  obtain ⟨pre, post, hsplit, hpre⟩ := split_of_mem_id hmem hnd
  have hlist : eraseFirst (fun b => b.id == a.id) d.attributes = pre ++ post := by
    rw [hsplit]
    exact eraseFirst_split pre post (fun x hx => by simpa using hpre x hx) (by simp)
  unfold detachAttribute
  let T := setAttributes s.tree element d (eraseFirst (fun b => b.id == a.id) d.attributes)
  refine ⟨pre, post, { s with tree := T, detachedAttrs := s.detachedAttrs ++ [a] }, hd, hsplit,
    hpre, ?_, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · rw [← hlist]; exact attributesReplaced_setAttributes hd _
  · exact handleAttributeChanges_spec
      (wellFormed_of_attributesOnly (attributesOnly_setAttributes hd _) hwf) element a _

/-! ## 健全性：method -/

section Sound

variable {s : DOMState} (hwf : WellFormed s.tree) (hav : AttributesValid s.tree)
  (hu : AttrIdsUnique s)
include hwf hav hu

theorem setAttributeNode_result_sound (element : NodeId) (aid : AttrId) :
    SetAttributeNodeResult s element aid (setAttributeNode s element aid) := by
  unfold setAttributeNode
  cases hreq : requireElement s.tree element with
  | error e => exact Or.inl (receiverError_of_requireElement hreq)
  | ok d =>
    obtain ⟨hd, hk⟩ := requireElement_ok hreq
    have hed : IsElementData s element d := ⟨hd, hk⟩
    have hkeys := hav.keysNodup element d hd
    have hloc := findAttr_spec s aid
    cases hf : findAttr s aid with
    | none => rw [hf] at hloc; exact Or.inr ⟨d, hed, Or.inl ⟨hloc, rfl⟩⟩
    | some p =>
      obtain ⟨a₀, owner⟩ := p
      rw [hf] at hloc
      have hnorm := normalized_eq_of_normalForm (hu.normalForm_findAttr hav hf)
      simp only [hnorm]
      by_cases hown : (owner != none && owner != some element) = true
      · rw [if_pos hown]
        cases owner with
        | none => simp at hown
        | some m => exact Or.inr ⟨d, hed, Or.inr ⟨a₀, m, hloc, by simpa using hown, rfl⟩⟩
      · rw [if_neg hown]
        have howner : owner = none ∨ owner = some element := by
          cases owner with
          | none => exact Or.inl rfl
          | some n =>
            right
            by_cases hne : n = element
            · rw [hne]
            · exact absurd (by simp [hne]) hown
        -- 付いている側なら、引き直した結果は自分自身である
        have hself : owner = some element →
            getAttributeByKey d a₀.namespace a₀.localName = some a₀ ∧ a₀.id = aid := by
          intro ho
          rw [ho] at hf
          obtain ⟨d', hd', ha₀, hid⟩ := findAttr_attached hf
          rw [hd] at hd'; cases hd'
          have := getAttributeByKey_self hkeys ha₀ (hu.normalized_of_mem hd ha₀)
          rw [hnorm] at this
          exact ⟨this, hid⟩
        have hspec := getAttributeByKey_spec d a₀.namespace a₀.localName
        cases hg : getAttributeByKey d a₀.namespace a₀.localName with
        | some old =>
          rw [hg] at hspec
          by_cases hid : old.id = aid
          · dsimp only; rw [if_pos (by simp [hid])]
            exact ⟨d, hed, a₀, owner, hloc, howner, Or.inl ⟨old, hspec, hid, rfl, rfl⟩⟩
          · dsimp only; rw [if_neg (by simpa using hid)]
            have ho : owner = none := by
              rcases howner with ho | ho
              · exact ho
              · obtain ⟨hg', hid'⟩ := hself ho
                rw [hg'] at hg; cases hg; exact absurd hid' hid
            subst ho
            obtain ⟨ha₀, hid₀⟩ := findAttr_detached hf
            subst hid₀
            exact ⟨d, hed, a₀, none, hloc, howner, Or.inr (Or.inl ⟨old, hspec, hid, rfl, rfl,
              _, removeDetached_taken hu ha₀,
              replaceAttributeWith_spec (s := removeDetached s a₀.id) hwf hd
                (mem_of_firstAttr hspec) hkeys a₀⟩)⟩
        | none =>
          rw [hg] at hspec
          have ho : owner = none := by
            rcases howner with ho | ho
            · exact ho
            · obtain ⟨hg', -⟩ := hself ho
              rw [hg'] at hg; cases hg
          subst ho
          obtain ⟨ha₀, hid₀⟩ := findAttr_detached hf
          subst hid₀
          exact ⟨d, hed, a₀, none, hloc, howner, Or.inr (Or.inr ⟨hspec, rfl, rfl,
            _, removeDetached_taken hu ha₀,
            appendAttribute_spec (s := removeDetached s a₀.id) hwf hd a₀⟩)⟩

omit hav in
theorem removeAttributeNode_result_sound (element : NodeId) (aid : AttrId) :
    RemoveAttributeNodeResult s element aid (removeAttributeNode s element aid) := by
  unfold removeAttributeNode
  cases hreq : requireElement s.tree element with
  | error e => exact Or.inl (receiverError_of_requireElement hreq)
  | ok d =>
    obtain ⟨hd, hk⟩ := requireElement_ok hreq
    have hnd := hu.within element
    rw [attrIdsAt_of_get? hd] at hnd
    dsimp only
    cases hf : d.attributes.find? (fun a => a.id == aid) with
    | none =>
      rw [List.find?_eq_none] at hf
      exact Or.inr ⟨d, ⟨hd, hk⟩, fun a ha he => hf a ha (by simp [he]), rfl⟩
    | some a =>
      have hid : a.id = aid := by simpa using List.find?_some hf
      exact ⟨d, ⟨hd, hk⟩, a, List.mem_of_find?_eq_some hf, hid, rfl,
        detachAttribute_spec hwf hd (List.mem_of_find?_eq_some hf) hnd⟩

omit hav in
theorem removeNamedItem_result_sound (element : NodeId) (qn : String) :
    RemoveNamedItemResult s element qn (removeNamedItem s element qn) := by
  unfold removeNamedItem
  cases hreq : requireElement s.tree element with
  | error e => exact Or.inl (receiverError_of_requireElement hreq)
  | ok d =>
    obtain ⟨hd, hk⟩ := requireElement_ok hreq
    have hnd := hu.within element
    rw [attrIdsAt_of_get? hd] at hnd
    have hspec := getAttributeByName_spec s.tree d qn
    cases hg : getAttributeByName s.tree d qn with
    | none => rw [hg] at hspec; dsimp only; rw [hg]; exact Or.inr ⟨d, ⟨hd, hk⟩, hspec, rfl⟩
    | some a =>
      rw [hg] at hspec
      have hmem := mem_of_firstAttr hspec.choose_spec.2
      have hfind : d.attributes.find? (fun b => b.id == a.id) = some a := by
        cases hf : d.attributes.find? (fun b => b.id == a.id) with
        | none => rw [List.find?_eq_none] at hf; exact absurd (by simp) (hf a hmem)
        | some b =>
          have hid : b.id = a.id := by simpa using List.find?_some hf
          rw [eq_of_key_eq hnd (List.mem_of_find?_eq_some hf) hmem hid]
      dsimp only
      rw [hg]
      dsimp only
      unfold removeAttributeNode
      rw [hreq]
      dsimp only
      rw [hfind]
      exact ⟨d, ⟨hd, hk⟩, a, hspec, rfl, detachAttribute_spec hwf hd hmem hnd⟩

end Sound

/-! ## 一意性 -/

/-- 戻り値と状態の組の結果が一致する（戻り値は等しく、状態は観測が一致する）。 -/
def AttrResultObsEq {α : Type} :
    Except DOMException (α × DOMState) → Except DOMException (α × DOMState) → Prop
  | .ok (r, a), .ok (r', b) => r = r' ∧ ObsEq a b
  | .error e, .error e' => e = e'
  | _, _ => False

theorem attrTaken_unique {s s₀ s₀' : DOMState} {a : Attr} (h₁ : AttrTakenFromDetached s s₀ a)
    (h₂ : AttrTakenFromDetached s s₀' a) : s₀ = s₀' := by
  obtain ⟨p₁, q₁, hs₁, hp₁, rfl⟩ := h₁
  obtain ⟨p₂, q₂, hs₂, hp₂, rfl⟩ := h₂
  obtain ⟨rfl, rfl⟩ := attrList_split_unique (hs₁.symm.trans hs₂)
    (fun hm => hp₁ a hm rfl) (fun hm => hp₂ a hm rfl)
  rfl

theorem attributeReplacedWith_deterministic {s o₁ o₂ : DOMState} {element : NodeId}
    {d : NodeData} {old new : Attr} (h₁ : AttributeReplacedWith s element d old new o₁)
    (h₂ : AttributeReplacedWith s element d old new o₂) : ObsEq o₁ o₂ := by
  obtain ⟨pre₁, post₁, s₁, hd, hs₁, hk₁, hr₁, ht₁, hh₁⟩ := h₁
  obtain ⟨pre₂, post₂, s₂, -, hs₂, hk₂, hr₂, ht₂, hh₂⟩ := h₂
  obtain ⟨rfl, rfl⟩ := attrList_split_unique (hs₁.symm.trans hs₂)
    (fun hm => hk₁ old hm rfl) (fun hm => hk₂ old hm rfl)
  exact attributeChangeHandled_congr (obsEq_of_treeDetached hd hr₁ hr₂ ht₁ ht₂) hh₁ hh₂

theorem attributeDetached_deterministic {s o₁ o₂ : DOMState} {element : NodeId}
    {d : NodeData} {a : Attr} (h₁ : AttributeDetached s element d a o₁)
    (h₂ : AttributeDetached s element d a o₂) : ObsEq o₁ o₂ := by
  obtain ⟨pre₁, post₁, s₁, hd, hs₁, hk₁, hr₁, ht₁, hh₁⟩ := h₁
  obtain ⟨pre₂, post₂, s₂, -, hs₂, hk₂, hr₂, ht₂, hh₂⟩ := h₂
  obtain ⟨rfl, rfl⟩ := attrList_split_unique (hs₁.symm.trans hs₂)
    (fun hm => hk₁ a hm rfl) (fun hm => hk₂ a hm rfl)
  exact attributeChangeHandled_congr (obsEq_of_treeDetached hd hr₁ hr₂ ht₁ ht₂) hh₁ hh₂

section Unique

variable {s : DOMState} (hu : AttrIdsUnique s)
include hu

theorem attr_eq_of_id {m : NodeId} {d : NodeData} (hd : s.tree.get? m = some d) {a₁ a₂ : Attr}
    (h₁ : a₁ ∈ d.attributes) (h₂ : a₂ ∈ d.attributes) (he : a₁.id = a₂.id) : a₁ = a₂ := by
  have hnd := hu.within m
  rw [attrIdsAt_of_get? hd] at hnd
  exact eq_of_key_eq hnd h₁ h₂ he

theorem attrLocated_unique {aid : AttrId} {r₁ r₂ : Option (Attr × Option NodeId)}
    (h₁ : AttrLocated s aid r₁) (h₂ : AttrLocated s aid r₂) : r₁ = r₂ := by
  rcases r₁ with _ | ⟨a₁, _ | m₁⟩ <;> rcases r₂ with _ | ⟨a₂, _ | m₂⟩
  · rfl
  · exact absurd h₂.1 (h₁.2 a₂ h₂.2.1)
  · obtain ⟨hid, d, hd, ha⟩ := h₂; exact absurd hid (h₁.1 m₂ d hd a₂ ha)
  · exact absurd h₁.1 (h₂.2 a₁ h₁.2.1)
  · rw [eq_of_key_eq hu.detached h₁.2.1 h₂.2.1 (h₁.1.trans h₂.1.symm)]
  · obtain ⟨hid, d, hd, ha⟩ := h₂; exact absurd hid (h₁.2.2 m₂ d hd a₂ ha)
  · obtain ⟨hid, d, hd, ha⟩ := h₁; exact absurd hid (h₂.1 m₁ d hd a₁ ha)
  · obtain ⟨hid, d, hd, ha⟩ := h₁; exact absurd hid (h₂.2.2 m₁ d hd a₁ ha)
  · obtain ⟨hid₁, d₁, hd₁, ha₁⟩ := h₁
    obtain ⟨hid₂, d₂, hd₂, ha₂⟩ := h₂
    have hm : m₁ = m₂ := by
      by_cases hm : m₁ = m₂
      · exact hm
      · refine absurd ?_ (hu.across m₁ m₂ hm aid ?_)
        · rw [attrIdsAt_of_get? hd₂, ← hid₂]; exact List.mem_map_of_mem ha₂
        · rw [attrIdsAt_of_get? hd₁, ← hid₁]; exact List.mem_map_of_mem ha₁
    subst hm
    rw [hd₁] at hd₂; cases hd₂
    rw [attr_eq_of_id hu hd₁ ha₁ ha₂ (hid₁.trans hid₂.symm)]

theorem setAttributeNode_result_deterministic {element : NodeId} {aid : AttrId}
    {r₁ r₂ : Except DOMException (Option AttrId × DOMState)}
    (h₁ : SetAttributeNodeResult s element aid r₁) (h₂ : SetAttributeNodeResult s element aid r₂) :
    AttrResultObsEq r₁ r₂ := by
  rcases r₁ with e₁ | ⟨v₁, o₁⟩ <;> rcases r₂ with e₂ | ⟨v₂, o₂⟩
  · show e₁ = e₂
    rcases h₁ with hr₁ | ⟨d₁, hd₁, hx₁⟩ <;> rcases h₂ with hr₂ | ⟨d₂, hd₂, hx₂⟩
    · exact receiverError_unique hr₁ hr₂
    · exact (not_receiverError hd₂ hr₁).elim
    · exact (not_receiverError hd₁ hr₂).elim
    · rcases hx₁ with ⟨hl₁, rfl⟩ | ⟨a₁, m₁, hl₁, -, rfl⟩ <;>
        rcases hx₂ with ⟨hl₂, rfl⟩ | ⟨a₂, m₂, hl₂, -, rfl⟩
      · rfl
      · cases attrLocated_unique hu hl₁ hl₂
      · cases attrLocated_unique hu hl₁ hl₂
      · rfl
  · exfalso
    obtain ⟨d₂, hd₂, a₂, ow₂, hl₂, how₂, -⟩ := h₂
    rcases h₁ with hr₁ | ⟨d₁, hd₁, ⟨hl₁, -⟩ | ⟨a₁, m₁, hl₁, hne₁, -⟩⟩
    · exact not_receiverError hd₂ hr₁
    · cases attrLocated_unique hu hl₁ hl₂
    · have he := attrLocated_unique hu hl₁ hl₂
      simp only [Option.some.injEq, Prod.mk.injEq] at he
      rcases how₂ with h | h <;> rw [← he.2] at h
      · cases h
      · exact hne₁ (Option.some.inj h)
  · exfalso
    obtain ⟨d₁, hd₁, a₁, ow₁, hl₁, how₁, -⟩ := h₁
    rcases h₂ with hr₂ | ⟨d₂, hd₂, ⟨hl₂, -⟩ | ⟨a₂, m₂, hl₂, hne₂, -⟩⟩
    · exact not_receiverError hd₁ hr₂
    · cases attrLocated_unique hu hl₁ hl₂
    · have he := attrLocated_unique hu hl₁ hl₂
      simp only [Option.some.injEq, Prod.mk.injEq] at he
      rcases how₁ with h | h <;> rw [he.2] at h
      · cases h
      · exact hne₂ (Option.some.inj h)
  · obtain ⟨d₁, hd₁, a₁, ow₁, hl₁, -, hx₁⟩ := h₁
    obtain ⟨d₂, hd₂, a₂, ow₂, hl₂, -, hx₂⟩ := h₂
    cases isElementData_unique hd₁ hd₂
    have he := attrLocated_unique hu hl₁ hl₂
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rcases hx₁ with ⟨old₁, hk₁, hid₁, rfl, rfl⟩ | ⟨old₁, hk₁, hid₁, -, rfl, t₁, ht₁, hr₁⟩ |
        ⟨hk₁, -, rfl, t₁, ht₁, ha₁⟩ <;>
      rcases hx₂ with ⟨old₂, hk₂, hid₂, rfl, rfl⟩ | ⟨old₂, hk₂, hid₂, -, rfl, t₂, ht₂, hr₂⟩ |
        ⟨hk₂, -, rfl, t₂, ht₂, ha₂⟩
    · exact ⟨rfl, ObsEq.refl _⟩
    · cases attrByKey_unique hk₁ hk₂; exact absurd hid₁ hid₂
    · cases attrByKey_unique hk₁ hk₂
    · cases attrByKey_unique hk₁ hk₂; exact absurd hid₂ hid₁
    · cases attrByKey_unique hk₁ hk₂
      cases attrTaken_unique ht₁ ht₂
      exact ⟨rfl, attributeReplacedWith_deterministic hr₁ hr₂⟩
    · cases attrByKey_unique hk₁ hk₂
    · cases attrByKey_unique hk₁ hk₂
    · cases attrByKey_unique hk₁ hk₂
    · cases attrTaken_unique ht₁ ht₂
      exact ⟨rfl, attributeAppended_deterministic ha₁ ha₂⟩

theorem removeAttributeNode_result_deterministic {element : NodeId} {aid : AttrId}
    {r₁ r₂ : Except DOMException (AttrId × DOMState)}
    (h₁ : RemoveAttributeNodeResult s element aid r₁)
    (h₂ : RemoveAttributeNodeResult s element aid r₂) : AttrResultObsEq r₁ r₂ := by
  rcases r₁ with e₁ | ⟨v₁, o₁⟩ <;> rcases r₂ with e₂ | ⟨v₂, o₂⟩
  · show e₁ = e₂
    rcases h₁ with hr₁ | ⟨d₁, hd₁, -, rfl⟩ <;> rcases h₂ with hr₂ | ⟨d₂, hd₂, -, rfl⟩
    · exact receiverError_unique hr₁ hr₂
    · exact (not_receiverError hd₂ hr₁).elim
    · exact (not_receiverError hd₁ hr₂).elim
    · rfl
  · exfalso
    obtain ⟨d₂, hd₂, a₂, ha₂, hid₂, -⟩ := h₂
    rcases h₁ with hr₁ | ⟨d₁, hd₁, hno, -⟩
    · exact not_receiverError hd₂ hr₁
    · cases isElementData_unique hd₁ hd₂; exact hno a₂ ha₂ hid₂
  · exfalso
    obtain ⟨d₁, hd₁, a₁, ha₁, hid₁, -⟩ := h₁
    rcases h₂ with hr₂ | ⟨d₂, hd₂, hno, -⟩
    · exact not_receiverError hd₁ hr₂
    · cases isElementData_unique hd₁ hd₂; exact hno a₁ ha₁ hid₁
  · obtain ⟨d₁, hd₁, a₁, ha₁, hid₁, rfl, hx₁⟩ := h₁
    obtain ⟨d₂, hd₂, a₂, ha₂, hid₂, rfl, hx₂⟩ := h₂
    cases isElementData_unique hd₁ hd₂
    cases attr_eq_of_id hu hd₁.1 ha₁ ha₂ (hid₁.trans hid₂.symm)
    exact ⟨rfl, attributeDetached_deterministic hx₁ hx₂⟩

omit hu in
theorem removeNamedItem_result_deterministic {element : NodeId} {qn : String}
    {r₁ r₂ : Except DOMException (AttrId × DOMState)}
    (h₁ : RemoveNamedItemResult s element qn r₁) (h₂ : RemoveNamedItemResult s element qn r₂) :
    AttrResultObsEq r₁ r₂ := by
  rcases r₁ with e₁ | ⟨v₁, o₁⟩ <;> rcases r₂ with e₂ | ⟨v₂, o₂⟩
  · show e₁ = e₂
    rcases h₁ with hr₁ | ⟨d₁, hd₁, -, rfl⟩ <;> rcases h₂ with hr₂ | ⟨d₂, hd₂, -, rfl⟩
    · exact receiverError_unique hr₁ hr₂
    · exact (not_receiverError hd₂ hr₁).elim
    · exact (not_receiverError hd₁ hr₂).elim
    · rfl
  · exfalso
    obtain ⟨d₂, hd₂, a₂, hn₂, -⟩ := h₂
    rcases h₁ with hr₁ | ⟨d₁, hd₁, hn₁, -⟩
    · exact not_receiverError hd₂ hr₁
    · cases isElementData_unique hd₁ hd₂; cases attrByName_unique hn₁ hn₂
  · exfalso
    obtain ⟨d₁, hd₁, a₁, hn₁, -⟩ := h₁
    rcases h₂ with hr₂ | ⟨d₂, hd₂, hn₂, -⟩
    · exact not_receiverError hd₁ hr₂
    · cases isElementData_unique hd₁ hd₂; cases attrByName_unique hn₁ hn₂
  · obtain ⟨d₁, hd₁, a₁, hn₁, rfl, hx₁⟩ := h₁
    obtain ⟨d₂, hd₂, a₂, hn₂, rfl, hx₂⟩ := h₂
    cases isElementData_unique hd₁ hd₂
    cases attrByName_unique hn₁ hn₂
    exact ⟨rfl, attributeDetached_deterministic hx₁ hx₂⟩

end Unique

/-! ## 完全性 -/

section Complete

variable {s : DOMState} (hwf : WellFormed s.tree) (hav : AttributesValid s.tree)
  (hu : AttrIdsUnique s)
include hwf hav hu

theorem setAttributeNode_result_complete {element : NodeId} {aid : AttrId}
    {r : Except DOMException (Option AttrId × DOMState)}
    (h : SetAttributeNodeResult s element aid r) : AttrResultObsEq r (setAttributeNode s element aid) :=
  setAttributeNode_result_deterministic hu h (setAttributeNode_result_sound hwf hav hu element aid)

omit hav in
theorem removeAttributeNode_result_complete {element : NodeId} {aid : AttrId}
    {r : Except DOMException (AttrId × DOMState)} (h : RemoveAttributeNodeResult s element aid r) :
    AttrResultObsEq r (removeAttributeNode s element aid) :=
  removeAttributeNode_result_deterministic hu h (removeAttributeNode_result_sound hwf hu element aid)

omit hav in
theorem removeNamedItem_result_complete {element : NodeId} {qn : String}
    {r : Except DOMException (AttrId × DOMState)} (h : RemoveNamedItemResult s element qn r) :
    AttrResultObsEq r (removeNamedItem s element qn) :=
  removeNamedItem_result_deterministic h (removeNamedItem_result_sound hwf hu element qn)

end Complete

end Dom.Spec
