import Dom.Spec.Attribute
import Dom.Spec.RecordSound
import Dom.Attribute.Algorithms
import Dom.Validity.Attributes

/-!
# attribute の変更は関係を満たす

record を積む段（`handleAttributeChanges`）から始め、change / append / remove、
`Element` の method へと順に移す。
-/

namespace Dom.Spec

open Dom

/-! ## attributes の record -/

section Record

variable {s : DOMState} (hwf : WellFormed s.tree) (target : NodeId) (name : String)
  (ns : Option String)
include hwf

private abbrev arec : MutationRecord :=
  { type := .attributes, target := target, attributeName := some name, attributeNamespace := ns }

omit hwf in
private theorem cond_iff (r : Registration) :
    Registration.interestedIn r target RecordType.attributes (some name) ns = true ↔
      (r.node = target ∨ r.subtree = true) ∧ r.attributes = true ∧
        (r.attributeFilter = none ∨ ∃ f, r.attributeFilter = some f ∧ name ∈ f ∧ ns = none) := by
  unfold Registration.interestedIn
  cases hf : r.attributeFilter with
  | none => simp
  | some f =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem,
      Option.isNone_iff_eq_none, Option.some.injEq, reduceCtorEq, false_or, exists_eq_left']


omit hwf in
private theorem flag_iff (r : Registration) :
    (((RecordType.attributes == RecordType.characterData && r.characterDataOldValue)
      || (RecordType.attributes == RecordType.attributes && r.attributeOldValue)) = true) ↔
      r.attributeOldValue = true := by
  simp

theorem mem_interested_iff_attribute (ov : Option String) (mo : Nat) :
    mo ∈ ((interestedObservers s (arec target name ns) ov).map (·.1)) ↔
      InterestedInAttribute s mo target name ns := by
  rw [mem_interestedObservers]
  constructor
  · rintro ⟨r, hrmem, hnode, hc, rfl⟩
    obtain ⟨hsub, hat, hfil⟩ := (cond_iff target name ns r).mp hc
    refine ⟨r, hrmem, rfl, hat, ?_, hsub, hfil⟩
    rcases List.mem_cons.mp hnode with he | hm
    · exact Or.inl he
    · exact Or.inr ((mem_ancestors_iff hwf target r.node).mp hm)
  · rintro ⟨r, hrmem, rfl, hat, hanc, hsub, hfil⟩
    refine ⟨r, hrmem, ?_, (cond_iff target name ns r).mpr ⟨hsub, hat, hfil⟩, rfl⟩
    rcases hanc with he | ha
    · exact List.mem_cons.mpr (Or.inl he)
    · exact List.mem_cons_of_mem _ ((mem_ancestors_iff hwf target r.node).mpr ha)

theorem mem_pair_iff_attributeOldValue (old : String) (mo : Nat) :
    ((mo, some old) ∈ interestedObservers s (arec target name ns) (some old)) ↔
      AttributeOldValueWanted s mo target name ns := by
  rw [mem_pair_interestedObservers s _ (some old) (by simp) mo]
  constructor
  · rintro ⟨r, hrmem, hnode, hc, hf, rfl⟩
    obtain ⟨hsub, hat, hfil⟩ := (cond_iff target name ns r).mp hc
    refine ⟨r, hrmem, rfl, hat, (flag_iff r).mp hf, ?_, hsub, hfil⟩
    rcases List.mem_cons.mp hnode with he | hm
    · exact Or.inl he
    · exact Or.inr ((mem_ancestors_iff hwf target r.node).mp hm)
  · rintro ⟨r, hrmem, rfl, hat, hov, hanc, hsub, hfil⟩
    refine ⟨r, hrmem, ?_, (cond_iff target name ns r).mpr ⟨hsub, hat, hfil⟩,
      (flag_iff r).mpr hov, rfl⟩
    rcases hanc with he | ha
    · exact List.mem_cons.mpr (Or.inl he)
    · exact List.mem_cons_of_mem _ ((mem_ancestors_iff hwf target r.node).mpr ha)

/-- **attributes の record を積む段は `AttributeRecordQueued` を満たす。** -/
theorem attributeRecordQueued_of_queue (oldValue : Option String) :
    AttributeRecordQueued s (queueMutationRecord s (arec target name ns) oldValue)
      target name ns oldValue := by
  have hmem := mem_interested_iff_attribute hwf target name ns oldValue
  have hrec : ∀ v : Option String,
      ({ arec target name ns with oldValue := v } : MutationRecord) = attrRecord target name ns v :=
    fun _ => rfl
  refine ⟨queueMutationRecord_observers_length .., ?_, ?_, ?_, ?_,
    microtaskQueued_queueMutationRecord ..⟩
  · intro mo o o' ho ho'
    rw [observers_queueMutationRecord] at ho'
    have hfold := records_foldl_enqueue (arec target name ns) _ s.observers mo o o' ho ho'
    -- interested なら、その observer の値は oldValue か none のどちらか一つ
    have single : ∀ v, (mo, v) ∈ interestedObservers s (arec target name ns) oldValue →
        o'.records = o.records ++ [attrRecord target name ns v] := by
      intro v hv
      rw [hfold, filterMap_eq_single (fun r : Nat × Option String =>
        ({ arec target name ns with oldValue := r.2 } : MutationRecord)) mo v _
        (nodup_interestedObservers ..) hv]
      rfl
    have pick : InterestedInAttribute s mo target name ns →
        ∃ v, (mo, v) ∈ interestedObservers s (arec target name ns) oldValue ∧
          (v = oldValue ∨ v = none) := by
      intro hint
      obtain ⟨q, hqmem, hq1⟩ := List.mem_map.mp ((hmem mo).mpr hint)
      refine ⟨q.2, ?_, value_mem_interestedObservers s _ oldValue q hqmem⟩
      cases q with
      | mk a b => simp only at hq1; rw [← hq1]; exact hqmem
    refine ⟨fun hint hwant => ?_, fun hint hwant => ?_, fun hint => ?_⟩
    · obtain ⟨v, hv, hvv⟩ := pick hint
      cases oldValue with
      | none =>
        have : v = none := by rcases hvv with h | h <;> exact h
        rw [this] at hv
        exact single none hv
      | some old =>
        exact single (some old) ((mem_pair_iff_attributeOldValue hwf target name ns old mo).mpr hwant)
    · obtain ⟨v, hv, hvv⟩ := pick hint
      cases oldValue with
      | none =>
        have : v = none := by rcases hvv with h | h <;> exact h
        rw [this] at hv
        exact single none hv
      | some old =>
        rcases hvv with hv1 | hv1
        · rw [hv1] at hv
          exact absurd ((mem_pair_iff_attributeOldValue hwf target name ns old mo).mp hv) hwant
        · rw [hv1] at hv; exact single none hv
    · rw [hfold, filterMap_eq_nil_of_not_mem (fun r : Nat × Option String =>
        ({ arec target name ns with oldValue := r.2 } : MutationRecord)) mo _
        (fun hm => hint ((hmem mo).mp hm))]
      simp
  · intro mo hint
    exact (mem_pendingObservers_queueMutationRecord _ _ _ mo).mpr (Or.inr ((hmem mo).mpr hint))
  · intro mo hmo
    exact (mem_pendingObservers_queueMutationRecord _ _ _ mo).mpr (Or.inl hmo)
  · intro mo hmo
    rcases (mem_pendingObservers_queueMutationRecord _ _ _ mo).mp hmo with hm | hm
    · exact Or.inl hm
    · exact Or.inr ((hmem mo).mp hm)

end Record

/-- **`handleAttributeChanges` は関係を満たす。** -/
theorem handleAttributeChanges_spec {s : DOMState} (hwf : WellFormed s.tree) (element : NodeId)
    (a : Attr) (oldValue : Option String) :
    AttributeChangeHandled s (handleAttributeChanges s element a oldValue) element a oldValue :=
  ⟨attributeRecordQueued_of_queue hwf element a.localName a.namespace oldValue,
    ⟨by simp [handleAttributeChanges], by simp [handleAttributeChanges],
      by simp [handleAttributeChanges], by simp [handleAttributeChanges],
      untouched_queueMutationRecord ..⟩⟩

/-! ## 列の補題 -/

theorem updateFirst_split {α : Type _} {p : α → Bool} {f : α → α} {a : α} :
    ∀ (pre post : List α), (∀ x ∈ pre, p x = false) → p a = true →
      ListUtil.updateFirst p f (pre ++ a :: post) = pre ++ f a :: post
  | [], post, _, ha => by simp [ListUtil.updateFirst, ha]
  | x :: pre, post, hpre, ha => by
    simp only [List.cons_append, ListUtil.updateFirst, hpre x (by simp), Bool.false_eq_true,
      if_false]
    rw [updateFirst_split pre post (fun y hy => hpre y (by simp [hy])) ha]

theorem eraseFirst_split {α : Type _} {p : α → Bool} {a : α} :
    ∀ (pre post : List α), (∀ x ∈ pre, p x = false) → p a = true →
      ListUtil.eraseFirst p (pre ++ a :: post) = pre ++ post
  | [], post, _, ha => by simp [ListUtil.eraseFirst, ha]
  | x :: pre, post, hpre, ha => by
    simp only [List.cons_append, ListUtil.eraseFirst, hpre x (by simp), Bool.false_eq_true,
      if_false]
    rw [eraseFirst_split pre post (fun y hy => hpre y (by simp [hy])) ha]

/-- 鍵に重複の無い list の中の attribute は、その鍵の最初の位置で切れる。 -/
theorem split_of_mem {as : List Attr} {a : Attr} (hmem : a ∈ as) (hnd : (as.map Attr.key).Nodup) :
    ∃ pre post, as = pre ++ a :: post ∧ ∀ x ∈ pre, x.key ≠ a.key := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hmem
  refine ⟨pre, post, rfl, fun x hx he => ?_⟩
  rw [List.map_append, List.map_cons] at hnd
  exact (List.nodup_append.mp hnd).2.2 x.key (List.mem_map_of_mem hx) a.key (by simp) he

theorem firstAttr_of_find? {as : List Attr} {p : Attr → Bool} {r : Option Attr}
    (h : as.find? p = r) : FirstAttr as (fun a => p a = true) r := by
  cases r with
  | none =>
    intro x hx hpx
    rw [List.find?_eq_none] at h
    exact h x hx hpx
  | some a =>
    obtain ⟨hpa, pre, post, rfl, hpre⟩ := List.find?_eq_some_iff_append.mp h
    exact ⟨pre, post, rfl, hpa, fun x hx hpx => by simpa [hpx] using hpre x hx⟩

/-! ## 探索の語彙 -/

theorem attrNameFor_spec (t : Tree) (d : NodeData) (qn : String) :
    AttrNameNormalized t d qn (attrNameFor t d qn) := by
  unfold attrNameFor AttrNameNormalized isHTMLDocumentOf
  cases hdoc : t.get? d.ownerDocument with
  | none =>
    refine Or.inr ⟨fun ⟨_, doc, hd, _⟩ => (by cases hd), by simp⟩
  | some doc =>
    by_cases h : (d.namespace == some htmlNamespace && doc.isHTMLDocument) = true
    · rw [if_pos h]
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact Or.inl ⟨⟨h.1, doc, rfl, h.2⟩, rfl⟩
    · rw [if_neg h]
      refine Or.inr ⟨fun ⟨hns, doc', hd', hh⟩ => h ?_, rfl⟩
      cases hd'
      simp [hns, hh]

theorem getAttributeByName_spec (t : Tree) (d : NodeData) (qn : String) :
    AttrByName t d qn (getAttributeByName t d qn) :=
  ⟨_, attrNameFor_spec t d qn, by
    have := firstAttr_of_find? (as := d.attributes)
      (p := fun a => a.qualifiedName == attrNameFor t d qn) rfl
    unfold getAttributeByName
    cases h : d.attributes.find? (fun a => a.qualifiedName == attrNameFor t d qn) with
    | none => rw [h] at this; intro x hx hq; exact this x hx (by simpa using hq)
    | some a =>
      rw [h] at this
      obtain ⟨pre, post, he, hp, hpre⟩ := this
      exact ⟨pre, post, he, by simpa using hp, fun x hx hq => hpre x hx (by simpa using hq)⟩⟩

theorem getAttributeByKey_spec (d : NodeData) (ns : Option String) (ln : String) :
    AttrByKey d ns ln (getAttributeByKey d ns ln) := by
  unfold getAttributeByKey AttrByKey
  have := firstAttr_of_find? (as := d.attributes)
    (p := fun a => a.namespace == normalizeNamespace ns && a.localName == ln) rfl
  cases h : d.attributes.find? (fun a => a.namespace == normalizeNamespace ns && a.localName == ln) with
  | none => rw [h] at this; intro x hx hq; exact this x hx (by simpa using hq)
  | some a =>
    rw [h] at this
    obtain ⟨pre, post, he, hp, hpre⟩ := this
    exact ⟨pre, post, he, by simpa using hp, fun x hx hq => hpre x hx (by simpa using hq)⟩

theorem mem_of_firstAttr {as : List Attr} {p : Attr → Prop} {a : Attr}
    (h : FirstAttr as p (some a)) : a ∈ as := by
  obtain ⟨pre, post, rfl, -, -⟩ := h
  simp

/-! ## change / append / remove -/

theorem attributesReplaced_setAttributes {t : Tree} {n : NodeId} {d : NodeData}
    (hd : t.get? n = some d) (as : List Attr) : AttributesReplaced t (setAttributes t n d as) n as :=
  ⟨fun d' hd' => by rw [hd] at hd'; cases hd'; rw [get?_setAttributes hd, if_pos rfl],
    fun m hm => by rw [get?_setAttributes hd, if_neg hm]⟩

private theorem treeOnly_withTree (s : DOMState) (t : Tree) : TreeOnly s { s with tree := t } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩⟩

theorem changeAttribute_spec {s : DOMState} (hwf : WellFormed s.tree) {element : NodeId}
    {d : NodeData} (hd : s.tree.get? element = some d) {a : Attr} (hmem : a ∈ d.attributes)
    (hnd : (d.attributes.map Attr.key).Nodup) (value : String) :
    AttributeChanged s element d a value (changeAttribute s element d a value) := by
  obtain ⟨pre, post, hsplit, hpre⟩ := split_of_mem hmem hnd
  have hlist : ListUtil.updateFirst (fun b => b.key == a.key) (fun b => { b with value := value })
      d.attributes = pre ++ { a with value := value } :: post := by
    rw [hsplit]
    exact updateFirst_split pre post (fun x hx => by simpa using hpre x hx) (by simp)
  unfold changeAttribute
  let T := setAttributes s.tree element d
    (ListUtil.updateFirst (fun b => b.key == a.key) (fun b => { b with value := value }) d.attributes)
  refine ⟨pre, post, { s with tree := T }, hd, hsplit, hpre, ?_, treeOnly_withTree _ _, ?_⟩
  · rw [← hlist]; exact attributesReplaced_setAttributes hd _
  · exact handleAttributeChanges_spec
      (wellFormed_of_attributesOnly (attributesOnly_setAttributes hd _) hwf) element a _

theorem appendAttribute_spec {s : DOMState} (hwf : WellFormed s.tree) {element : NodeId}
    {d : NodeData} (hd : s.tree.get? element = some d) (a₀ : Attr) :
    AttributeAppended s element d a₀ (appendAttribute s element d a₀) :=
  ⟨_, hd, attributesReplaced_setAttributes hd _, treeOnly_withTree _ _,
    handleAttributeChanges_spec
      (wellFormed_of_attributesOnly (attributesOnly_setAttributes hd _) hwf) element _ none⟩

theorem removeAttributeFrom_spec {s : DOMState} (hwf : WellFormed s.tree) {element : NodeId}
    {d : NodeData} (hd : s.tree.get? element = some d) {a : Attr} (hmem : a ∈ d.attributes)
    (hnd : (d.attributes.map Attr.key).Nodup) :
    AttributeRemoved s element d a (removeAttributeFrom s element d a) := by
  obtain ⟨pre, post, hsplit, hpre⟩ := split_of_mem hmem hnd
  have hlist : ListUtil.eraseFirst (fun b => b.key == a.key) d.attributes = pre ++ post := by
    rw [hsplit]
    exact eraseFirst_split pre post (fun x hx => by simpa using hpre x hx) (by simp)
  have hfind : d.attributes.find? (fun b => b.key == a.key) = some a :=
    List.find?_eq_some_iff_append.mpr ⟨by simp, pre, post, hsplit, fun x hx => by simpa using hpre x hx⟩
  unfold removeAttributeFrom
  simp only [hfind, Option.toList]
  let T := setAttributes s.tree element d (ListUtil.eraseFirst (fun b => b.key == a.key) d.attributes)
  refine ⟨pre, post, { s with tree := T, detachedAttrs := s.detachedAttrs ++ [a] }, hd, hsplit, hpre, ?_,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · rw [← hlist]; exact attributesReplaced_setAttributes hd _
  · exact handleAttributeChanges_spec
      (wellFormed_of_attributesOnly (attributesOnly_setAttributes hd _) hwf) element a _

/-! ## `Element` の method -/

section Methods

variable {s : DOMState} (hwf : WellFormed s.tree) (hav : AttributesValid s.tree)
include hwf hav

theorem setAttribute_result_sound (element : NodeId) (qn value : String) :
    SetAttributeResult s element qn value (setAttribute s element qn value) := by
  unfold setAttribute
  by_cases hv : isValidAttributeLocalName qn = true
  · rw [if_neg (by simp [hv])]
    cases hd : s.tree.get? element with
    | none => exact Or.inr ⟨hv, Or.inl ⟨hd, rfl⟩⟩
    | some d =>
      dsimp only
      by_cases hk : d.kind = .element
      · rw [if_neg (by simp [hk])]
        have hspec := getAttributeByName_spec s.tree d qn
        cases hg : getAttributeByName s.tree d qn with
        | some a =>
          rw [hg] at hspec
          exact ⟨hv, d, ⟨hd, hk⟩, Or.inl ⟨a, hspec, changeAttribute_spec hwf hd
            (mem_of_firstAttr hspec.choose_spec.2) (hav.keysNodup element d hd) value⟩⟩
        | none =>
          rw [hg] at hspec
          exact ⟨hv, d, ⟨hd, hk⟩, Or.inr ⟨hspec, _, attrNameFor_spec s.tree d qn,
            appendAttribute_spec hwf hd _⟩⟩
      · rw [if_pos (by simp [hk])]
        exact Or.inr ⟨hv, Or.inr ⟨d, hd, hk, rfl⟩⟩
  · rw [if_pos (by simpa using hv)]
    exact Or.inl ⟨by simpa using hv, rfl⟩

theorem setAttributeValue_result_sound (element : NodeId) (localName value : String)
    («prefix» ns : Option String) :
    SetAttributeValueResult s element localName value «prefix» ns
      (setAttributeValue s element localName value «prefix» ns) := by
  unfold setAttributeValue
  cases hd : s.tree.get? element with
  | none => exact Or.inl ⟨hd, rfl⟩
  | some d =>
    dsimp only
    by_cases hk : d.kind = .element
    · rw [if_neg (by simp [hk])]
      have hspec := getAttributeByKey_spec d ns localName
      cases hg : getAttributeByKey d ns localName with
      | some a =>
        rw [hg] at hspec
        exact ⟨d, ⟨hd, hk⟩, Or.inl ⟨a, hspec, changeAttribute_spec hwf hd
          (mem_of_firstAttr hspec) (hav.keysNodup element d hd) value⟩⟩
      | none =>
        rw [hg] at hspec
        exact ⟨d, ⟨hd, hk⟩, Or.inr ⟨hspec, appendAttribute_spec hwf hd _⟩⟩
    · rw [if_pos (by simp [hk])]
      exact Or.inr ⟨d, hd, hk, rfl⟩

theorem removeAttribute_result_sound (element : NodeId) (qn : String) :
    RemoveAttributeResult s element qn (removeAttribute s element qn) := by
  unfold removeAttribute
  cases hd : s.tree.get? element with
  | none => exact Or.inl ⟨hd, rfl⟩
  | some d =>
    dsimp only
    by_cases hk : d.kind = .element
    · rw [if_neg (by simp [hk])]
      have hspec := getAttributeByName_spec s.tree d qn
      cases hg : getAttributeByName s.tree d qn with
      | none => rw [hg] at hspec; exact ⟨d, ⟨hd, hk⟩, Or.inl ⟨hspec, rfl⟩⟩
      | some a =>
        rw [hg] at hspec
        exact ⟨d, ⟨hd, hk⟩, Or.inr ⟨a, hspec, removeAttributeFrom_spec hwf hd
          (mem_of_firstAttr hspec.choose_spec.2) (hav.keysNodup element d hd)⟩⟩
    · rw [if_pos (by simp [hk])]
      exact Or.inr ⟨d, hd, hk, rfl⟩

theorem removeAttributeNS_result_sound (element : NodeId) (ns : Option String) (ln : String) :
    RemoveAttributeNSResult s element ns ln (removeAttributeNS s element ns ln) := by
  unfold removeAttributeNS
  cases hd : s.tree.get? element with
  | none => exact Or.inl ⟨hd, rfl⟩
  | some d =>
    dsimp only
    by_cases hk : d.kind = .element
    · rw [if_neg (by simp [hk])]
      have hspec := getAttributeByKey_spec d ns ln
      cases hg : getAttributeByKey d ns ln with
      | none => rw [hg] at hspec; exact ⟨d, ⟨hd, hk⟩, Or.inl ⟨hspec, rfl⟩⟩
      | some a =>
        rw [hg] at hspec
        exact ⟨d, ⟨hd, hk⟩, Or.inr ⟨a, hspec, removeAttributeFrom_spec hwf hd
          (mem_of_firstAttr hspec) (hav.keysNodup element d hd)⟩⟩
    · rw [if_pos (by simp [hk])]
      exact Or.inr ⟨d, hd, hk, rfl⟩

theorem toggleAttribute_result_sound (element : NodeId) (qn : String) (force : Option Bool) :
    ToggleAttributeResult s element qn force (toggleAttribute s element qn force) := by
  unfold toggleAttribute
  by_cases hv : isValidAttributeLocalName qn = true
  · rw [if_neg (by simp [hv])]
    cases hd : s.tree.get? element with
    | none => exact Or.inr ⟨hv, Or.inl ⟨hd, rfl⟩⟩
    | some d =>
      dsimp only
      by_cases hk : d.kind = .element
      · rw [if_neg (by simp [hk])]
        have hspec := getAttributeByName_spec s.tree d qn
        cases hg : getAttributeByName s.tree d qn with
        | none =>
          rw [hg] at hspec
          dsimp only
          by_cases hf : force = some false
          · rw [if_pos (by simp [hf])]
            exact ⟨hv, d, ⟨hd, hk⟩, Or.inl ⟨hspec, Or.inl ⟨hf, rfl, rfl⟩⟩⟩
          · rw [if_neg (by simpa using hf)]
            exact ⟨hv, d, ⟨hd, hk⟩, Or.inl ⟨hspec, Or.inr ⟨hf, rfl, _,
              attrNameFor_spec s.tree d qn, appendAttribute_spec hwf hd _⟩⟩⟩
        | some a =>
          rw [hg] at hspec
          dsimp only
          by_cases hf : force = some true
          · rw [if_pos (by simp [hf])]
            exact ⟨hv, d, ⟨hd, hk⟩, Or.inr ⟨a, hspec, Or.inl ⟨hf, rfl, rfl⟩⟩⟩
          · rw [if_neg (by simpa using hf)]
            exact ⟨hv, d, ⟨hd, hk⟩, Or.inr ⟨a, hspec, Or.inr ⟨hf, rfl,
              removeAttributeFrom_spec hwf hd (mem_of_firstAttr hspec.choose_spec.2)
                (hav.keysNodup element d hd)⟩⟩⟩
      · rw [if_pos (by simp [hk])]
        exact Or.inr ⟨hv, Or.inr ⟨d, hd, hk, rfl⟩⟩
  · rw [if_pos (by simpa using hv)]
    exact Or.inl ⟨by simpa using hv, rfl⟩

end Methods

end Dom.Spec
