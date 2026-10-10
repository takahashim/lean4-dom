import Dom.Spec.AttributeSound
import Dom.Spec.ReplaceDataCongr

/-!
# attribute の関係の一意性と完全性

木は `get?` でしか決まらないので、結論は観測の一致（`ObsEq`）である。
record を積む段は、木を差し替えた後の状態から走るので、congruence の形で示す。
-/

namespace Dom.Spec

open Dom

/-! ## 探索 -/

open Classical in
theorem firstAttr_eq_find? {as : List Attr} {p : Attr → Prop} {r : Option Attr}
    (h : FirstAttr as p r) : r = as.find? (fun a => decide (p a)) := by
  cases r with
  | none =>
    symm
    rw [List.find?_eq_none]
    intro x hx
    simpa using h x hx
  | some a =>
    obtain ⟨pre, post, rfl, hp, hpre⟩ := h
    symm
    rw [List.find?_eq_some_iff_append]
    exact ⟨by simpa using hp, pre, post, rfl, fun x hx => by simpa using hpre x hx⟩

theorem firstAttr_unique {as : List Attr} {p : Attr → Prop} {r₁ r₂ : Option Attr}
    (h₁ : FirstAttr as p r₁) (h₂ : FirstAttr as p r₂) : r₁ = r₂ :=
  (firstAttr_eq_find? h₁).trans (firstAttr_eq_find? h₂).symm

theorem attrNameNormalized_unique {t : Tree} {d : NodeData} {qn a b : String}
    (h₁ : AttrNameNormalized t d qn a) (h₂ : AttrNameNormalized t d qn b) : a = b := by
  rcases h₁ with ⟨hc₁, rfl⟩ | ⟨hc₁, rfl⟩ <;> rcases h₂ with ⟨hc₂, rfl⟩ | ⟨hc₂, rfl⟩
  · rfl
  · exact absurd hc₁ hc₂
  · exact absurd hc₂ hc₁
  · rfl

theorem attrByName_unique {t : Tree} {d : NodeData} {qn : String} {r₁ r₂ : Option Attr}
    (h₁ : AttrByName t d qn r₁) (h₂ : AttrByName t d qn r₂) : r₁ = r₂ := by
  obtain ⟨q₁, hn₁, hf₁⟩ := h₁
  obtain ⟨q₂, hn₂, hf₂⟩ := h₂
  rw [attrNameNormalized_unique hn₁ hn₂] at hf₁
  exact firstAttr_unique hf₁ hf₂

theorem attrByKey_unique {d : NodeData} {ns : Option String} {ln : String} {r₁ r₂ : Option Attr}
    (h₁ : AttrByKey d ns ln r₁) (h₂ : AttrByKey d ns ln r₂) : r₁ = r₂ :=
  firstAttr_unique h₁ h₂

/-! ## record -/

variable {s sb : DOMState}

theorem interestedInAttribute_congr (h : ObsEq s sb) (mo : Nat) (target : NodeId) (name : String)
    (ns : Option String) :
    InterestedInAttribute sb mo target name ns ↔ InterestedInAttribute s mo target name ns := by
  unfold InterestedInAttribute
  constructor
  · rintro ⟨r, hr, h1, h2, h3, h4, h5⟩
    exact ⟨r, (h.registrations r).mp hr, h1, h2, h.tree.inclusiveAncestor_iff.mp h3, h4, h5⟩
  · rintro ⟨r, hr, h1, h2, h3, h4, h5⟩
    exact ⟨r, (h.registrations r).mpr hr, h1, h2, h.tree.inclusiveAncestor_iff.mpr h3, h4, h5⟩

theorem attributeOldValueWanted_congr (h : ObsEq s sb) (mo : Nat) (target : NodeId)
    (name : String) (ns : Option String) :
    AttributeOldValueWanted sb mo target name ns ↔ AttributeOldValueWanted s mo target name ns := by
  unfold AttributeOldValueWanted
  constructor
  · rintro ⟨r, hr, h1, h2, h3, h4, h5, h6⟩
    exact ⟨r, (h.registrations r).mp hr, h1, h2, h3, h.tree.inclusiveAncestor_iff.mp h4, h5, h6⟩
  · rintro ⟨r, hr, h1, h2, h3, h4, h5, h6⟩
    exact ⟨r, (h.registrations r).mpr hr, h1, h2, h3, h.tree.inclusiveAncestor_iff.mpr h4, h5, h6⟩

/-- **attributes の record を積む段の congruence。** -/
theorem attributeChangeHandled_congr (h : ObsEq s sb) {o₁ o₂ : DOMState} {element : NodeId}
    {a : Attr} {ov : Option String}
    (h₁ : AttributeChangeHandled s o₁ element a ov) (h₂ : AttributeChangeHandled sb o₂ element a ov) :
    ObsEq o₁ o₂ := by
  obtain ⟨⟨hl₁, hr₁, hin₁, hkeep₁, hout₁, hm₁⟩, hoo₁⟩ := h₁
  obtain ⟨⟨hl₂, hr₂, hin₂, hkeep₂, hout₂, hm₂⟩, hoo₂⟩ := h₂
  have hint := fun mo => interestedInAttribute_congr h mo element a.localName a.namespace
  have hold := fun mo => attributeOldValueWanted_congr h mo element a.localName a.namespace
  refine ⟨?_, by rw [hoo₂.ranges, hoo₁.ranges, h.ranges],
    by rw [hoo₂.iterators, hoo₁.iterators, h.iterators],
    fun r => by rw [hoo₂.registrations, hoo₁.registrations]; exact h.registrations r,
    ?_, ?_, by rw [hm₁, hm₂],
    by rw [hoo₂.untouched.walkers, hoo₁.untouched.walkers, h.walkers],
    by rw [hoo₂.untouched.listeners, hoo₁.untouched.listeners, h.listeners],
    by rw [hoo₂.untouched.detachedAttrs, hoo₁.untouched.detachedAttrs, h.detachedAttrs]⟩
  · intro m; rw [hoo₂.tree, hoo₁.tree]; exact h.tree m
  · intro mo
    refine (records_map_congr_obs h hl₁ hl₂ (fun mo o oa ob ob' ho hoa hob hob' => ?_) mo).symm
    have hre : ob.records = o.records := h.records_of ho hob
    by_cases hi : InterestedInAttribute s mo element a.localName a.namespace
    · by_cases hw : AttributeOldValueWanted s mo element a.localName a.namespace
      · rw [(hr₁ mo o oa ho hoa).1 hi hw,
          (hr₂ mo ob ob' hob hob').1 ((hint mo).mpr hi) ((hold mo).mpr hw), hre]
      · rw [(hr₁ mo o oa ho hoa).2.1 hi hw,
          (hr₂ mo ob ob' hob hob').2.1 ((hint mo).mpr hi) (fun hw' => hw ((hold mo).mp hw')), hre]
    · rw [(hr₁ mo o oa ho hoa).2.2 hi,
        (hr₂ mo ob ob' hob hob').2.2 (fun hi' => hi ((hint mo).mp hi')), hre]
  · intro mo
    constructor
    · intro hm
      rcases hout₂ mo hm with hp | hi
      · exact hkeep₁ mo ((h.pendingObservers mo).mp hp)
      · exact hin₁ mo ((hint mo).mp hi)
    · intro hm
      rcases hout₁ mo hm with hp | hi
      · exact hkeep₂ mo ((h.pendingObservers mo).mpr hp)
      · exact hin₂ mo ((hint mo).mpr hi)

/-! ## change / append / remove -/

/-- 同じ list の二つの分け方は、`a` が前半に無ければ一致する。 -/
theorem attrList_split_unique {α : Type _} {a : α} :
    ∀ {pre₁ post₁ pre₂ post₂ : List α}, pre₁ ++ a :: post₁ = pre₂ ++ a :: post₂ →
      a ∉ pre₁ → a ∉ pre₂ → pre₁ = pre₂ ∧ post₁ = post₂
  | [], _, [], _, h, _, _ => ⟨rfl, by simpa using h⟩
  | [], _, b :: _, _, h, _, h₂ => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (by rw [h.1]; simp) h₂
  | b :: _, _, [], _, h, h₁, _ => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (by rw [← h.1]; simp) h₁
  | b :: pre₁, post₁, c :: pre₂, post₂, h, h₁, h₂ => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨hp, hq⟩ := attrList_split_unique h (fun hm => h₁ (by simp [hm])) (fun hm => h₂ (by simp [hm]))
    exact ⟨by rw [hp], hq⟩

private theorem not_mem_of_keys {pre : List Attr} {a : Attr} (h : ∀ x ∈ pre, x.key ≠ a.key) :
    a ∉ pre := fun hm => h a hm rfl

/-- 同じ木から同じ list に差し替え、他を変えない状態どうしは観測が一致する。 -/
theorem obsEq_of_replaced {t : Tree} {s₁ s₁' : DOMState} {element : NodeId} {as : List Attr}
    {d : NodeData} (hd : t.get? element = some d)
    (h₁ : AttributesReplaced t s₁.tree element as) (h₂ : AttributesReplaced t s₁'.tree element as)
    (ho₁ : TreeOnly s s₁) (ho₂ : TreeOnly s s₁') : ObsEq s₁ s₁' := by
  obtain ⟨r₁, i₁, g₁, b₁, p₁, m₁, u₁⟩ := ho₁
  obtain ⟨r₂, i₂, g₂, b₂, p₂, m₂, u₂⟩ := ho₂
  refine ⟨fun m => ?_, by rw [r₁, r₂], by rw [i₁, i₂], fun r => by rw [g₁, g₂],
    fun mo => by rw [b₁, b₂], fun mo => by rw [p₁, p₂], by rw [m₁, m₂],
    by rw [u₁.walkers, u₂.walkers], by rw [u₁.listeners, u₂.listeners],
    by rw [u₁.detachedAttrs, u₂.detachedAttrs]⟩
  by_cases hm : m = element
  · subst hm; rw [h₁.changed d hd, h₂.changed d hd]
  · rw [h₁.others m hm, h₂.others m hm]

theorem attributeChanged_deterministic {s o₁ o₂ : DOMState} {element : NodeId} {d : NodeData}
    {a : Attr} {value : String}
    (h₁ : AttributeChanged s element d a value o₁) (h₂ : AttributeChanged s element d a value o₂) :
    ObsEq o₁ o₂ := by
  obtain ⟨pre₁, post₁, s₁, hd, hs₁, hk₁, hr₁, ht₁, hh₁⟩ := h₁
  obtain ⟨pre₂, post₂, s₂, -, hs₂, hk₂, hr₂, ht₂, hh₂⟩ := h₂
  obtain ⟨rfl, rfl⟩ := attrList_split_unique (hs₁.symm.trans hs₂) (not_mem_of_keys hk₁) (not_mem_of_keys hk₂)
  exact attributeChangeHandled_congr (obsEq_of_replaced hd hr₁ hr₂ ht₁ ht₂) hh₁ hh₂

theorem attributeAppended_deterministic {s o₁ o₂ : DOMState} {element : NodeId} {d : NodeData}
    {a : Attr} (h₁ : AttributeAppended s element d a o₁) (h₂ : AttributeAppended s element d a o₂) :
    ObsEq o₁ o₂ := by
  obtain ⟨s₁, hd, hr₁, ht₁, hh₁⟩ := h₁
  obtain ⟨s₂, -, hr₂, ht₂, hh₂⟩ := h₂
  exact attributeChangeHandled_congr (obsEq_of_replaced hd hr₁ hr₂ ht₁ ht₂) hh₁ hh₂

/-- 同じ木から同じ list に差し替え、detach された list も同じにした状態どうしは観測が一致する。 -/
theorem obsEq_of_treeDetached {s : DOMState} {t : Tree} {s₁ s₁' : DOMState} {element : NodeId}
    {as : List Attr} {d : NodeData} {D : List Attr} (hd : t.get? element = some d)
    (h₁ : AttributesReplaced t s₁.tree element as) (h₂ : AttributesReplaced t s₁'.tree element as)
    (ho₁ : TreeDetachedOnly s s₁ D) (ho₂ : TreeDetachedOnly s s₁' D) : ObsEq s₁ s₁' := by
  obtain ⟨r₁, i₁, g₁, b₁, p₁, m₁, w₁, l₁, d₁⟩ := ho₁
  obtain ⟨r₂, i₂, g₂, b₂, p₂, m₂, w₂, l₂, d₂⟩ := ho₂
  refine ⟨fun m => ?_, by rw [r₁, r₂], by rw [i₁, i₂], fun r => by rw [g₁, g₂],
    fun mo => by rw [b₁, b₂], fun mo => by rw [p₁, p₂], by rw [m₁, m₂],
    by rw [w₁, w₂], by rw [l₁, l₂], by rw [d₁, d₂]⟩
  by_cases hm : m = element
  · subst hm; rw [h₁.changed d hd, h₂.changed d hd]
  · rw [h₁.others m hm, h₂.others m hm]

theorem attributeRemoved_deterministic {s o₁ o₂ : DOMState} {element : NodeId} {d : NodeData}
    {a : Attr} (h₁ : AttributeRemoved s element d a o₁) (h₂ : AttributeRemoved s element d a o₂) :
    ObsEq o₁ o₂ := by
  obtain ⟨pre₁, post₁, s₁, hd, hs₁, hk₁, hr₁, ht₁, hh₁⟩ := h₁
  obtain ⟨pre₂, post₂, s₂, -, hs₂, hk₂, hr₂, ht₂, hh₂⟩ := h₂
  obtain ⟨rfl, rfl⟩ := attrList_split_unique (hs₁.symm.trans hs₂) (not_mem_of_keys hk₁) (not_mem_of_keys hk₂)
  exact attributeChangeHandled_congr (obsEq_of_treeDetached hd hr₁ hr₂ ht₁ ht₂) hh₁ hh₂

/-! ## `Element` の method -/

theorem receiverError_unique {s : DOMState} {element : NodeId} {e₁ e₂ : DOMException}
    (h₁ : ReceiverError s element e₁) (h₂ : ReceiverError s element e₂) : e₁ = e₂ := by
  rcases h₁ with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ <;> rcases h₂ with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ <;> rfl

theorem not_receiverError {s : DOMState} {element : NodeId} {d : NodeData} {e : DOMException}
    (hd : IsElementData s element d) (h : ReceiverError s element e) : False := by
  rcases h with ⟨hn, -⟩ | ⟨d', hd', hk, -⟩
  · rw [hd.1] at hn; cases hn
  · rw [hd.1] at hd'; cases hd'; exact hk hd.2

theorem isElementData_unique {s : DOMState} {element : NodeId} {d₁ d₂ : NodeData}
    (h₁ : IsElementData s element d₁) (h₂ : IsElementData s element d₂) : d₁ = d₂ := by
  have := h₂.1
  rw [h₁.1] at this
  exact Option.some.inj this

theorem setAttribute_result_deterministic {s : DOMState} {element : NodeId} {qn value : String}
    {r₁ r₂ : Except DOMException DOMState}
    (h₁ : SetAttributeResult s element qn value r₁) (h₂ : SetAttributeResult s element qn value r₂) :
    ResultObsEq r₁ r₂ := by
  cases r₁ with
  | error e₁ =>
    cases r₂ with
    | error e₂ =>
      show e₁ = e₂
      rcases h₁ with ⟨hv₁, rfl⟩ | ⟨hv₁, hr₁⟩ <;> rcases h₂ with ⟨hv₂, rfl⟩ | ⟨hv₂, hr₂⟩
      · rfl
      · rw [hv₁] at hv₂; cases hv₂
      · rw [hv₁] at hv₂; cases hv₂
      · exact receiverError_unique hr₁ hr₂
    | ok o₂ =>
      obtain ⟨hv, d, hd, -⟩ := h₂
      rcases h₁ with ⟨hv₁, -⟩ | ⟨-, hr₁⟩
      · rw [hv] at hv₁; cases hv₁
      · exact (not_receiverError hd hr₁).elim
  | ok o₁ =>
    cases r₂ with
    | error e₂ =>
      obtain ⟨hv, d, hd, -⟩ := h₁
      rcases h₂ with ⟨hv₂, -⟩ | ⟨-, hr₂⟩
      · rw [hv] at hv₂; cases hv₂
      · exact (not_receiverError hd hr₂).elim
    | ok o₂ =>
      obtain ⟨-, d₁, hd₁, hc₁⟩ := h₁
      obtain ⟨-, d₂, hd₂, hc₂⟩ := h₂
      have := isElementData_unique hd₁ hd₂
      subst this
      rcases hc₁ with ⟨a₁, ha₁, hch₁⟩ | ⟨hn₁, q₁, hq₁, hap₁⟩ <;>
        rcases hc₂ with ⟨a₂, ha₂, hch₂⟩ | ⟨hn₂, q₂, hq₂, hap₂⟩
      · cases attrByName_unique ha₁ ha₂; exact attributeChanged_deterministic hch₁ hch₂
      · cases attrByName_unique ha₁ hn₂
      · cases attrByName_unique hn₁ ha₂
      · cases attrNameNormalized_unique hq₁ hq₂; exact attributeAppended_deterministic hap₁ hap₂

theorem setAttributeValue_result_deterministic {s : DOMState} {element : NodeId}
    {localName value : String} {«prefix» ns : Option String} {r₁ r₂ : Except DOMException DOMState}
    (h₁ : SetAttributeValueResult s element localName value «prefix» ns r₁)
    (h₂ : SetAttributeValueResult s element localName value «prefix» ns r₂) :
    ResultObsEq r₁ r₂ := by
  cases r₁ with
  | error e₁ =>
    cases r₂ with
    | error e₂ => exact receiverError_unique h₁ h₂
    | ok o₂ => obtain ⟨d, hd, -⟩ := h₂; exact (not_receiverError hd h₁).elim
  | ok o₁ =>
    cases r₂ with
    | error e₂ => obtain ⟨d, hd, -⟩ := h₁; exact (not_receiverError hd h₂).elim
    | ok o₂ =>
      obtain ⟨d₁, hd₁, hc₁⟩ := h₁
      obtain ⟨d₂, hd₂, hc₂⟩ := h₂
      have := isElementData_unique hd₁ hd₂
      subst this
      rcases hc₁ with ⟨a₁, ha₁, hch₁⟩ | ⟨hn₁, hap₁⟩ <;> rcases hc₂ with ⟨a₂, ha₂, hch₂⟩ | ⟨hn₂, hap₂⟩
      · cases attrByKey_unique ha₁ ha₂; exact attributeChanged_deterministic hch₁ hch₂
      · cases attrByKey_unique ha₁ hn₂
      · cases attrByKey_unique hn₁ ha₂
      · exact attributeAppended_deterministic hap₁ hap₂

theorem removeAttribute_result_deterministic {s : DOMState} {element : NodeId} {qn : String}
    {r₁ r₂ : Except DOMException DOMState}
    (h₁ : RemoveAttributeResult s element qn r₁) (h₂ : RemoveAttributeResult s element qn r₂) :
    ResultObsEq r₁ r₂ := by
  cases r₁ with
  | error e₁ =>
    cases r₂ with
    | error e₂ => exact receiverError_unique h₁ h₂
    | ok o₂ => obtain ⟨d, hd, -⟩ := h₂; exact (not_receiverError hd h₁).elim
  | ok o₁ =>
    cases r₂ with
    | error e₂ => obtain ⟨d, hd, -⟩ := h₁; exact (not_receiverError hd h₂).elim
    | ok o₂ =>
      obtain ⟨d₁, hd₁, hc₁⟩ := h₁
      obtain ⟨d₂, hd₂, hc₂⟩ := h₂
      have := isElementData_unique hd₁ hd₂
      subst this
      rcases hc₁ with ⟨hn₁, rfl⟩ | ⟨a₁, ha₁, hrm₁⟩ <;> rcases hc₂ with ⟨hn₂, rfl⟩ | ⟨a₂, ha₂, hrm₂⟩
      · exact ObsEq.refl _
      · cases attrByName_unique hn₁ ha₂
      · cases attrByName_unique ha₁ hn₂
      · cases attrByName_unique ha₁ ha₂; exact attributeRemoved_deterministic hrm₁ hrm₂

theorem removeAttributeNS_result_deterministic {s : DOMState} {element : NodeId}
    {ns : Option String} {ln : String} {r₁ r₂ : Except DOMException DOMState}
    (h₁ : RemoveAttributeNSResult s element ns ln r₁) (h₂ : RemoveAttributeNSResult s element ns ln r₂) :
    ResultObsEq r₁ r₂ := by
  cases r₁ with
  | error e₁ =>
    cases r₂ with
    | error e₂ => exact receiverError_unique h₁ h₂
    | ok o₂ => obtain ⟨d, hd, -⟩ := h₂; exact (not_receiverError hd h₁).elim
  | ok o₁ =>
    cases r₂ with
    | error e₂ => obtain ⟨d, hd, -⟩ := h₁; exact (not_receiverError hd h₂).elim
    | ok o₂ =>
      obtain ⟨d₁, hd₁, hc₁⟩ := h₁
      obtain ⟨d₂, hd₂, hc₂⟩ := h₂
      have := isElementData_unique hd₁ hd₂
      subst this
      rcases hc₁ with ⟨hn₁, rfl⟩ | ⟨a₁, ha₁, hrm₁⟩ <;> rcases hc₂ with ⟨hn₂, rfl⟩ | ⟨a₂, ha₂, hrm₂⟩
      · exact ObsEq.refl _
      · cases attrByKey_unique hn₁ ha₂
      · cases attrByKey_unique ha₁ hn₂
      · cases attrByKey_unique ha₁ ha₂; exact attributeRemoved_deterministic hrm₁ hrm₂

/-- `toggleAttribute` の結果の一致：状態は観測で、返り値は等号で。 -/
def ToggleResultObsEq : Except DOMException (DOMState × Bool) →
    Except DOMException (DOMState × Bool) → Prop
  | .ok (a, b), .ok (a', b') => ObsEq a a' ∧ b = b'
  | .error e, .error e' => e = e'
  | _, _ => False

theorem toggleAttribute_result_deterministic {s : DOMState} {element : NodeId} {qn : String}
    {force : Option Bool} {r₁ r₂ : Except DOMException (DOMState × Bool)}
    (h₁ : ToggleAttributeResult s element qn force r₁)
    (h₂ : ToggleAttributeResult s element qn force r₂) : ToggleResultObsEq r₁ r₂ := by
  rcases r₁ with e₁ | ⟨o₁, b₁⟩ <;> rcases r₂ with e₂ | ⟨o₂, b₂⟩
  · show e₁ = e₂
    rcases h₁ with ⟨hv₁, rfl⟩ | ⟨hv₁, hr₁⟩ <;> rcases h₂ with ⟨hv₂, rfl⟩ | ⟨hv₂, hr₂⟩
    · rfl
    · rw [hv₁] at hv₂; cases hv₂
    · rw [hv₁] at hv₂; cases hv₂
    · exact receiverError_unique hr₁ hr₂
  · obtain ⟨hv, d, hd, -⟩ := h₂
    rcases h₁ with ⟨hv₁, -⟩ | ⟨-, hr₁⟩
    · rw [hv] at hv₁; cases hv₁
    · exact (not_receiverError hd hr₁).elim
  · obtain ⟨hv, d, hd, -⟩ := h₁
    rcases h₂ with ⟨hv₂, -⟩ | ⟨-, hr₂⟩
    · rw [hv] at hv₂; cases hv₂
    · exact (not_receiverError hd hr₂).elim
  · obtain ⟨-, d₁, hd₁, hc₁⟩ := h₁
    obtain ⟨-, d₂, hd₂, hc₂⟩ := h₂
    have := isElementData_unique hd₁ hd₂
    subst this
    rcases hc₁ with ⟨hn₁, hx₁⟩ | ⟨a₁, ha₁, hx₁⟩ <;> rcases hc₂ with ⟨hn₂, hx₂⟩ | ⟨a₂, ha₂, hx₂⟩
    · rcases hx₁ with ⟨hf₁, rfl, rfl⟩ | ⟨hf₁, rfl, q₁, hq₁, hap₁⟩ <;>
        rcases hx₂ with ⟨hf₂, rfl, rfl⟩ | ⟨hf₂, rfl, q₂, hq₂, hap₂⟩
      · exact ⟨ObsEq.refl _, rfl⟩
      · exact absurd hf₁ hf₂
      · exact absurd hf₂ hf₁
      · cases attrNameNormalized_unique hq₁ hq₂; exact ⟨attributeAppended_deterministic hap₁ hap₂, rfl⟩
    · cases attrByName_unique hn₁ ha₂
    · cases attrByName_unique ha₁ hn₂
    · cases attrByName_unique ha₁ ha₂
      rcases hx₁ with ⟨hf₁, rfl, rfl⟩ | ⟨hf₁, rfl, hrm₁⟩ <;>
        rcases hx₂ with ⟨hf₂, rfl, rfl⟩ | ⟨hf₂, rfl, hrm₂⟩
      · exact ⟨ObsEq.refl _, rfl⟩
      · exact absurd hf₁ hf₂
      · exact absurd hf₂ hf₁
      · exact ⟨attributeRemoved_deterministic hrm₁ hrm₂, rfl⟩

/-! ## 完全性 -/

section Complete

variable {s : DOMState} (hwf : WellFormed s.tree) (hav : AttributesValid s.tree)
include hwf hav

theorem setAttribute_result_complete {element : NodeId} {qn value : String}
    {r : Except DOMException DOMState} (h : SetAttributeResult s element qn value r) :
    ResultObsEq r (setAttribute s element qn value) :=
  setAttribute_result_deterministic h (setAttribute_result_sound hwf hav element qn value)

theorem setAttributeValue_result_complete {element : NodeId} {localName value : String}
    {«prefix» ns : Option String} {r : Except DOMException DOMState}
    (h : SetAttributeValueResult s element localName value «prefix» ns r) :
    ResultObsEq r (setAttributeValue s element localName value «prefix» ns) :=
  setAttributeValue_result_deterministic h
    (setAttributeValue_result_sound hwf hav element localName value «prefix» ns)

theorem removeAttribute_result_complete {element : NodeId} {qn : String}
    {r : Except DOMException DOMState} (h : RemoveAttributeResult s element qn r) :
    ResultObsEq r (removeAttribute s element qn) :=
  removeAttribute_result_deterministic h (removeAttribute_result_sound hwf hav element qn)

theorem removeAttributeNS_result_complete {element : NodeId} {ns : Option String} {ln : String}
    {r : Except DOMException DOMState} (h : RemoveAttributeNSResult s element ns ln r) :
    ResultObsEq r (removeAttributeNS s element ns ln) :=
  removeAttributeNS_result_deterministic h (removeAttributeNS_result_sound hwf hav element ns ln)

theorem toggleAttribute_result_complete {element : NodeId} {qn : String} {force : Option Bool}
    {r : Except DOMException (DOMState × Bool)} (h : ToggleAttributeResult s element qn force r) :
    ToggleResultObsEq r (toggleAttribute s element qn force) :=
  toggleAttribute_result_deterministic h (toggleAttribute_result_sound hwf hav element qn force)

end Complete

end Dom.Spec
