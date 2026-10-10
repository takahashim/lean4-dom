import Dom.Spec.RangeDeleteSound

/-!
# `deleteContents` の関係の一意性と完全性

step 4 の列は「membership と tree order」で、step 5-6 の boundary point は
「start node の inclusive ancestor が一列に並ぶこと」で一つに決まる。
step 7-9 は `replace data` と `remove` の関係を観測の上で繋ぐ。
-/

namespace Dom.Spec

open Dom
open Dom.ListUtil (eq_of_pairwise_of_mem_iff)

variable {t : Tree} {r : RangeState}

/-! ## step 4 -/

theorem precedesIn_self_of_nodup : ∀ {l : List NodeId} {a : NodeId}, l.Nodup →
    precedesIn l a a = false
  | [], _, _ => rfl
  | x :: rest, a, hnd => by
    by_cases hx : x = a
    · subst hx
      simp [precedesIn, (List.nodup_cons.mp hnd).1]
    · simp only [precedesIn, if_neg hx]
      exact precedesIn_self_of_nodup (List.nodup_cons.mp hnd).2

/-- **step 4 の列は一つに決まる。** -/
theorem nodesToRemove_unique (hwf : WellFormed t) {sd : NodeData}
    (hs : t.get? r.start.node = some sd) {l₁ l₂ : List NodeId}
    (h₁ : NodesToRemove t r l₁) (h₂ : NodesToRemove t r l₂) : l₁ = l₂ := by
  obtain ⟨rd, hrd⟩ := exists_data_root hwf hs
  have hmem : ∀ x ∈ l₁, x ∈ preorder t (root t r.start.node) := by
    intro x hx
    obtain ⟨⟨-, hr, -, -⟩, -⟩ := (h₁.1 x).mp hx
    refine (mem_preorder_iff hwf hrd x).mpr ?_
    rw [← hr]
    exact root_inclusive_ancestor t x
  have hnd := preorder_nodup hwf (root t r.start.node)
  have hdesc : ∀ x ∈ l₁, InclusiveDescendant t x (root t r.start.node) :=
    fun x hx => (mem_preorder_iff hwf hrd x).mp (hmem x hx)
  have hirr : ∀ x ∈ l₁, ¬ PrecedesStruct t x x := by
    intro x hx hp
    have := precedesIn_preorder_of_struct hwf hrd (hdesc x hx) (hdesc x hx) hp
    rw [precedesIn_self_of_nodup hnd] at this
    cases this
  refine eq_of_pairwise_of_mem_iff hirr ?_ h₁.2 h₂.2 (fun x => (h₁.1 x).trans (h₂.1 x).symm)
  intro x hx y hy hxy hyx
  have hne : x ≠ y := fun he => hirr x hx (he ▸ hxy)
  have e₁ := precedesIn_preorder_of_struct hwf hrd (hdesc x hx) (hdesc y hy) hxy
  have e₂ := precedesIn_preorder_of_struct hwf hrd (hdesc y hy) (hdesc x hx) hyx
  rw [precedesIn_asymm hne (hmem x hx) (hmem y hy) e₁] at e₂
  cases e₂

/-! ## step 5-6 -/

/-- **step 5-6 の boundary point は一つに決まる。** -/
theorem deleteNewBP_unique {bp₁ bp₂ : BoundaryPoint}
    (h₁ : DeleteNewBP t r bp₁) (h₂ : DeleteNewBP t r bp₂) : bp₁ = bp₂ := by
  rcases h₁ with ⟨ha₁, rfl⟩ | ⟨hn₁, ref₁, p₁, i₁, hrs₁, hre₁, hp₁, hpe₁, hi₁, rfl⟩ <;>
    rcases h₂ with ⟨ha₂, rfl⟩ | ⟨hn₂, ref₂, p₂, i₂, hrs₂, hre₂, hp₂, hpe₂, hi₂, rfl⟩
  · rfl
  · exact absurd ha₁ hn₂
  · exact absurd ha₂ hn₁
  · -- start node の inclusive ancestor は一列に並ぶので、止まる所は一つである
    have key : ∀ {a b pa pb : NodeId}, Ancestor t a b → parentOf t b = some pb →
        InclusiveAncestor t pb r.«end».node → ¬ InclusiveAncestor t a r.«end».node → False := by
      intro a b pa pb hab hpb hpbe hae
      obtain ⟨q, hq, hqa⟩ := hab.cases_parent
      rw [hpb] at hq
      cases hq
      exact hae ((show InclusiveAncestor t a pb from hqa).trans_inclusive hpbe)
    have hre : ref₁ = ref₂ := by
      rcases inclusive_ancestor_linear hrs₁ hrs₂ with h | h
      · rcases h with h | h
        · exact h
        · exact (key (pa := ref₁) h hp₂ hpe₂ hre₁).elim
      · rcases h with h | h
        · exact h.symm
        · exact (key (pa := ref₂) h hp₁ hpe₁ hre₂).elim
    subst hre
    rw [hp₁] at hp₂
    cases hp₂
    rw [hi₁] at hi₂
    cases hi₂
    rfl

/-! ## step 7・9 -/

/-- replace data の失敗の条件は木の観測だけで決まる。 -/
theorem replaceDataResult_error_congr {s sb : DOMState} (h : ObsEq s sb) {n : NodeId}
    {offset count : Nat} {data : String} {e : DOMException} :
    ReplaceDataResult sb n offset count data (.error e) ↔
      ReplaceDataResult s n offset count data (.error e) := by
  show (_ ∨ _) ↔ (_ ∨ _)
  rw [h.tree n]

/-- **replace data の結果の関係の congruence。** -/
theorem replaceDataResult_congr {s sb : DOMState} (h : ObsEq s sb) {n : NodeId}
    {offset count : Nat} {data : String} {r₁ r₂ : Except DOMException DOMState}
    (h₁ : ReplaceDataResult s n offset count data r₁)
    (h₂ : ReplaceDataResult sb n offset count data r₂) : ResultObsEq r₁ r₂ := by
  cases r₁ with
  | ok o₁ =>
    cases r₂ with
    | ok o₂ => exact replaceDataSpec_congr h h₁ h₂
    | error e₂ => exact replaceData_result_deterministic h₁ ((replaceDataResult_error_congr h).mp h₂)
  | error e₁ =>
    cases r₂ with
    | ok o₂ => exact replaceData_result_deterministic ((replaceDataResult_error_congr h).mpr h₁) h₂
    | error e₂ => exact replaceData_result_deterministic h₁ ((replaceDataResult_error_congr h).mp h₂)

theorem isCharacterData_congr {s sb : DOMState} (h : ObsEq s sb) (n : NodeId) :
    IsCharacterData sb.tree n ↔ IsCharacterData s.tree n := by
  unfold IsCharacterData
  rw [h.tree n]

theorem replaceDataIfCharacterData_congr {s sb : DOMState} (h : ObsEq s sb) {n : NodeId}
    {offset count : Nat} {r₁ r₂ : Except DOMException DOMState}
    (h₁ : ReplaceDataIfCharacterData s n offset count r₁)
    (h₂ : ReplaceDataIfCharacterData sb n offset count r₂) : ResultObsEq r₁ r₂ := by
  rcases h₁ with ⟨hc₁, rfl⟩ | ⟨hc₁, hr₁⟩ <;> rcases h₂ with ⟨hc₂, rfl⟩ | ⟨hc₂, hr₂⟩
  · exact h
  · exact absurd ((isCharacterData_congr h n).mp hc₂) hc₁
  · exact absurd ((isCharacterData_congr h n).mpr hc₁) hc₂
  · exact replaceDataResult_congr h hr₁ hr₂

/-- step 7・9 の成功側からは well-formedness が残る。 -/
theorem replaceDataIfCharacterData_wellFormed {s s₁ : DOMState} {n : NodeId} {offset count : Nat}
    (hwf : WellFormed s.tree) (h : ReplaceDataIfCharacterData s n offset count (.ok s₁)) :
    WellFormed s₁.tree := by
  rcases h with ⟨-, he⟩ | ⟨-, hr⟩
  · cases he; exact hwf
  · exact replaceDataSpec_wellFormed hwf hr

/-! ## 繋ぎ -/

/-- `AndThen` の congruence。前段の結果が観測として一致し、後段が観測を保てば一致する。 -/
theorem andThen_congr {A A' : Except DOMException DOMState → Prop}
    {next next' : DOMState → Except DOMException DOMState → Prop}
    {res₁ res₂ : Except DOMException DOMState}
    (hA : ∀ r₁ r₂, A r₁ → A' r₂ → ResultObsEq r₁ r₂)
    (hnext : ∀ s₁ s₁', A (.ok s₁) → ObsEq s₁ s₁' → ∀ q₁ q₂, next s₁ q₁ → next' s₁' q₂ →
      ResultObsEq q₁ q₂)
    (h₁ : AndThen A next res₁) (h₂ : AndThen A' next' res₂) : ResultObsEq res₁ res₂ := by
  rcases h₁ with ⟨e₁, ha₁, rfl⟩ | ⟨s₁, ha₁, hn₁⟩ <;>
    rcases h₂ with ⟨e₂, ha₂, rfl⟩ | ⟨s₂, ha₂, hn₂⟩
  · exact hA _ _ ha₁ ha₂
  · exact (hA _ _ ha₁ ha₂).elim
  · exact (hA _ _ ha₁ ha₂).elim
  · exact hnext s₁ s₂ ha₁ (hA _ _ ha₁ ha₂) _ _ hn₁ hn₂

/-! ## 全体 -/

/-- **`deleteContents` の関係は結果を一つに決める。** -/
theorem deleteContents_result_deterministic {s : DOMState} {i : Nat}
    (hwf : WellFormed s.tree) {sd : NodeData} (hs : s.tree.get? r.start.node = some sd)
    {res₁ res₂ : Except DOMException DOMState}
    (h₁ : DeleteContentsResult s i r res₁) (h₂ : DeleteContentsResult s i r res₂) :
    ResultObsEq res₁ res₂ := by
  rcases h₁ with ⟨hc₁, rfl⟩ | ⟨hc₁, heq₁, hch₁, hr₁⟩ | ⟨hc₁, hn₁, l₁, bp₁, hl₁, hbp₁, hch₁⟩ <;>
    rcases h₂ with ⟨hc₂, rfl⟩ | ⟨hc₂, heq₂, hch₂, hr₂⟩ | ⟨hc₂, hn₂, l₂, bp₂, hl₂, hbp₂, hch₂⟩
  · exact ResultObsEq.refl _
  · exact absurd hc₁ hc₂
  · exact absurd hc₁ hc₂
  · exact absurd hc₂ hc₁
  · exact replaceData_result_deterministic hr₁ hr₂
  · exact absurd ⟨heq₁, hch₁⟩ hn₂
  · exact absurd hc₂ hc₁
  · exact absurd ⟨heq₂, hch₂⟩ hn₁
  · have hle := nodesToRemove_unique hwf hs hl₁ hl₂
    subst hle
    have hbe := deleteNewBP_unique hbp₁ hbp₂
    subst hbe
    refine andThen_congr (fun _ _ ha hb => replaceDataIfCharacterData_congr (ObsEq.refl _) ha hb)
      ?_ hch₁ hch₂
    intro s₁ s₁' ha₁ hobs₁ q₁ q₂ ⟨s₂, hre₂, hq₁⟩ ⟨s₂', hre₂', hq₂⟩
    have hwf₁ := replaceDataIfCharacterData_wellFormed (s := { s with ranges := s.ranges.set i _ })
      hwf ha₁
    have hobs₂ := removeEachSpec_congr hwf₁ hobs₁ hre₂ hre₂'
    refine andThen_congr (fun _ _ ha hb => replaceDataIfCharacterData_congr hobs₂ ha hb)
      ?_ hq₁ hq₂
    intro s₃ s₃' _ hobs₃ q₃ q₄ hq₃ hq₄
    subst hq₃ hq₄
    exact hobs₃

/-- **`deleteContents` の完全性。** -/
theorem rangeDeleteContents_result_complete {s : DOMState} {i : Nat}
    (h : AdmissibleDOMState s) (hr : s.ranges[i]? = some r) (hrv : RangeValid s.tree r)
    {res : Except DOMException DOMState} (hres : DeleteContentsResult s i r res) :
    ResultObsEq res (rangeDeleteContents s i) := by
  obtain ⟨⟨sd, hs, -⟩, -⟩ := id hrv
  exact deleteContents_result_deterministic h.wellFormed hs hres
    (rangeDeleteContents_result_sound h hr hrv)

end Dom.Spec
