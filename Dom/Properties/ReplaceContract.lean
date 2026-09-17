import Dom.Properties.InsertContract

/-!
# 契約：`replaceChild` の成功条件

`replace` が落ちうるのは四箇所である。

* step 1 の pre-insertion validity
* step 6 の `adopt`
* step 7 の `remove`（`child` に parent があるときだけ走る）
* step 9 の `insert`

後ろの三つが落ちないことを言えば、**`replaceChild` が返す例外は step 1 のものだけ**になる。

step 9 だけが厄介である。`insert` が走るのは validity を通った状態そのものではなく、
adopt と removal を通った後の状態だからである。そこで `insert_isOk_of_facts`
（validity ではなく四つの事実で受ける版）に、事実を運んでいく。

運ぶ道具は `Dom/Properties/InsertOk.lean` にある。
`parentOf_adopt_ne` / `ancestor_of_adopt`（adopt は adopt する node 以外の parent を
動かさず、祖先関係を増やさない）と、`parentOf_detach` / `ancestor_of_detach`
（removal も同じ）である。
-/

namespace Dom

/--
step 2-3 の reference child は `parent` の子で、`node` でも `child` でもない。

`node` でないのは step 2-3 がそれを避けるためで、`child` でないのは
children に重複が無いからである（`nextSibling_ne_self` と
`nextSibling_nextSibling_ne`）。
-/
theorem replaceReferenceChild_facts {t : Tree} (hwf : WellFormed t)
    {child node parent : NodeId} (hcp : parentOf t child = some parent) :
    ∀ c, replaceReferenceChild t child node = some c →
      parentOf t c = some parent ∧ c ≠ node ∧ c ≠ child := by
  intro c hc
  rw [replaceReferenceChild_eq] at hc
  by_cases hq : nextSibling t child = some node
  · rw [if_pos hq] at hc
    have hnp : parentOf t node = some parent := parentOf_nextSibling hwf hcp hq
    exact ⟨parentOf_nextSibling hwf hnp hc, fun he => nextSibling_ne_self hwf node (by rw [hc, he]),
      nextSibling_nextSibling_ne hwf hcp hq hc⟩
  · rw [if_neg hq] at hc
    exact ⟨parentOf_nextSibling hwf hcp hc, fun he => hq (by rw [hc, he]),
      fun he => nextSibling_ne_self hwf child (by rw [hc, he])⟩

/--
**`replace` が成功するのは、step 1 の validity を通るときちょうどである。**

つまり `replaceChild` が返す例外は pre-insertion validity のものだけである。
-/
theorem replace_succeeds_iff {s : DOMState} (hwf : WellFormed s.tree)
    {child node parent : NodeId} :
    (∃ s', replace s child node parent = .ok s') ↔
      ensurePreInsertionValidity s.tree node parent (some child) [child] = .ok () := by
  constructor
  · rintro ⟨s', h⟩
    obtain ⟨-, -, -, -, hv, -⟩ := replace_cases h
    exact hv
  · intro hv
    obtain ⟨⟨pd, hpd⟩, ⟨nd, hnd⟩, hanc, hchild⟩ := ensurePreInsertionValidity_ok hv
    have hcp : parentOf s.tree child = some parent := hchild child rfl
    have hnotanc : ¬ InclusiveAncestor s.tree node parent := by
      intro hq
      rw [(isInclusiveAncestorOf_iff hwf node parent).mpr hq] at hanc
      exact Bool.noConfusion hanc
    obtain ⟨href, hrne, hrnc⟩ :
        (∀ c, replaceReferenceChild s.tree child node = some c →
          parentOf s.tree c = some parent) ∧
        (∀ c, replaceReferenceChild s.tree child node = some c → c ≠ node) ∧
        (∀ c, replaceReferenceChild s.tree child node = some c → c ≠ child) :=
      ⟨fun c hc => (replaceReferenceChild_facts hwf hcp c hc).1,
        fun c hc => (replaceReferenceChild_facts hwf hcp c hc).2.1,
        fun c hc => (replaceReferenceChild_facts hwf hcp c hc).2.2⟩
    -- step 6：adopt は落ちない
    obtain ⟨s₁, ha⟩ := adopt_isOk (doc := pd.ownerDocument) hwf hnd
    have hwf₁ : WellFormed s₁.tree :=
      adopt_preserves_wellformed hwf (isDocument_ownerDocument hwf hpd) ha
    have hsp₁ : ShapePreserving s.tree s₁.tree := shapePreserving_adopt ha
    -- step 9：`insert` の四つの事実を、adopt と removal を跨いで運ぶ
    have key : ∀ s₂ : DOMState, WellFormed s₂.tree → ShapePreserving s₁.tree s₂.tree →
        (∀ a x, Ancestor s₂.tree a x → Ancestor s₁.tree a x) →
        (∀ m, m ≠ child → parentOf s₂.tree m = parentOf s₁.tree m) →
        ∃ o, insert s₂ node parent (replaceReferenceChild s.tree child node) true = .ok o := by
      intro s₂ hwf₂ hsp₂ hanc₂ hpar₂
      obtain ⟨pd₁, hpd₁⟩ := exists_get?_of_kindPreserving hsp₁ hpd
      obtain ⟨pd₂, hpd₂⟩ := exists_get?_of_kindPreserving hsp₂ hpd₁
      obtain ⟨nd₁, hnd₁⟩ := exists_get?_of_kindPreserving hsp₁ hnd
      obtain ⟨nd₂, hnd₂⟩ := exists_get?_of_kindPreserving hsp₂ hnd₁
      refine insert_isOk_of_facts (b := true) hwf₂ hpd₂ hnd₂ ?_ ?_ hrne
      · intro hq
        refine hnotanc ?_
        rcases hq with he | hx
        · exact Or.inl he
        · exact Or.inr (ancestor_of_adopt ha (hanc₂ _ _ hx))
      · intro c hc
        rw [hpar₂ c (hrnc c hc), parentOf_adopt_ne ha (hrne c hc)]
        exact href c hc
    -- step 7：`child` に parent があれば外す。どちらの枝でも落ちない。
    unfold replace
    simp only [hv, hpd, ha]
    cases hq : parentOf s₁.tree child with
    | none =>
      obtain ⟨o, ho⟩ := key s₁ hwf₁ (ShapePreserving.refl _) (fun _ _ h => h) (fun _ _ => rfl)
      simp only [ho]
      exact ⟨_, rfl⟩
    | some q =>
      obtain ⟨s₂, hr⟩ := (remove_succeeds_iff hwf₁ (n := child) (b := true)).mpr (by rw [hq]; rfl)
      obtain ⟨o, ho⟩ := key s₂ (remove_preserves_wellformed hwf₁ hr) (shapePreserving_remove hr)
        (fun _ _ h => ancestor_of_detach (remove_ok hr).2 h)
        (fun m hm => by rw [parentOf_detach (remove_ok hr).2, if_neg hm])
      simp only [hr, ho]
      exact ⟨_, rfl⟩

/-- **`replace` が失敗するのは validity で落ちるときちょうどで、例外はそれである。** -/
theorem replace_error_iff {s : DOMState} (hwf : WellFormed s.tree)
    {child node parent : NodeId} {e : DOMException} :
    replace s child node parent = .error e ↔
      ensurePreInsertionValidity s.tree node parent (some child) [child] = .error e := by
  constructor
  · intro h
    cases hx : ensurePreInsertionValidity s.tree node parent (some child) [child] with
    | error e' =>
      rw [replace_of_validity_error hx] at h
      have he : e' = e := Except.error.inj h
      subst he
      rfl
    | ok u =>
      exfalso
      obtain ⟨s', hs'⟩ := (replace_succeeds_iff hwf).mpr (by cases u; exact hx)
      rw [hs'] at h
      simp at h
  · exact replace_of_validity_error

end Dom
