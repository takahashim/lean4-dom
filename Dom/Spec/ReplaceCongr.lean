import Dom.Spec.Replace
import Dom.Spec.InsertCongr

/-!
# `replace` の congruence

`Dom/Spec/InsertCongr.lean` と同じ形で、`ReplaceSpec` について
「入力の観測が等しければ出力の観測も等しい」を示す。

`replace` の step 1（ensure pre-insertion validity）は関係に含めていないので、
そこが保証する事実は仮定として受け取る。

* `node` は `parent` ではない（step 2）
* `child` の parent は `parent` である（step 3）
* 入れる node は `parent` の inclusive ancestor でない（step 2）

どれも `insert` の congruence が pre-insertion validity を仮定するのと同じ扱いである。
-/

namespace Dom.Spec

open Dom

variable {s sb : DOMState} {child node parent : NodeId}

/-! ## step 2-3：reference child -/

theorem referenceChild_unique {t tb : Tree} (h : TreeObsEq t tb) {r₁ r₂ : Option NodeId}
    (h₁ : ReferenceChild t child node r₁) (h₂ : ReferenceChild tb child node r₂) : r₁ = r₂ := by
  rcases h₁ with ⟨ha₁, he₁⟩ | ⟨ha₁, he₁⟩ <;> rcases h₂ with ⟨ha₂, he₂⟩ | ⟨ha₂, he₂⟩
  · rw [he₁, he₂, h.nextSibling]
  · exact absurd (by rw [h.nextSibling]; exact ha₁) ha₂
  · exact absurd (by rw [← h.nextSibling]; exact ha₂) ha₁
  · rw [he₁, he₂, h.nextSibling]

/-! ## step 7：`child` を外す -/

/-- step 7 が一つの derivation について保証すること。 -/
theorem childRemoved_facts {s₁ s₂ : DOMState} {removed : List NodeId}
    (hwf : WellFormed s₁.tree) (h : ChildRemoved s₁ s₂ child removed) :
    WellFormed s₂.tree ∧ ∀ a m : NodeId, Ancestor s₂.tree a m → Ancestor s₁.tree a m := by
  rcases h with ⟨-, -, rfl⟩ | ⟨-, -, hr⟩
  · exact ⟨hwf, fun _ _ ha => ha⟩
  · exact ⟨removeSpec_wellFormed hwf hr, fun _ _ ha => removeSpec_ancestor hr ha⟩

/-- **step 7 の congruence。** -/
theorem childRemoved_congr {s₁ s₁' s₂ s₂' : DOMState} {r₁ r₂ : List NodeId}
    (hwf : WellFormed s₁.tree) (h : ObsEq s₁ s₁')
    (h₁ : ChildRemoved s₁ s₂ child r₁) (h₂ : ChildRemoved s₁' s₂' child r₂) :
    ObsEq s₂ s₂' ∧ r₁ = r₂ := by
  rcases h₁ with ⟨hp₁, hr₁, rfl⟩ | ⟨⟨p₁, hp₁⟩, hr₁, hrm₁⟩
  · rcases h₂ with ⟨-, hr₂, rfl⟩ | ⟨⟨p₂, hp₂⟩, -, -⟩
    · exact ⟨h, by rw [hr₁, hr₂]⟩
    · exact absurd (by rw [h.tree.parentOf, hp₁] at hp₂; exact hp₂) (by simp)
  · rcases h₂ with ⟨hp₂, -, -⟩ | ⟨-, hr₂, hrm₂⟩
    · exact absurd (by rw [h.tree.parentOf, hp₁] at hp₂; exact hp₂) (by simp)
    · exact ⟨removeSpec_congr hwf h hrm₁ hrm₂, by rw [hr₁, hr₂]⟩

/-! ## 全体 -/

/--
**`ReplaceSpec` の congruence。**

step ごとに観測を持ち上げる。`node` の kind と children は adopt も removal も跨いで
残るので、step 8 の `nodes` は step 1 の時点の木から決まる。
-/
theorem replaceSpec_congr {o₁ o₂ : DOMState} (hwf : WellFormed s.tree) (h : ObsEq s sb)
    (hnep : node ≠ parent) (hcp : parentOf s.tree child = some parent)
    (hacyc : ∀ ns : List NodeId, NodesToInsert s.tree node ns →
      ∀ m ∈ ns, ¬ InclusiveAncestor s.tree m parent)
    (h₁ : ReplaceSpec s child node parent o₁) (h₂ : ReplaceSpec sb child node parent o₂) :
    ObsEq o₁ o₂ := by
  obtain ⟨ref, prev, nodes, removed, pd, s₁, s₂, s₃,
    href₁, hprev₁, hpd₁, ha₁, hcr₁, hni₁, hi₁, -, hrec₁, hfr₁⟩ := h₁
  obtain ⟨ref', prev', nodes', removed', pd', s₁', s₂', s₃',
    href₂, hprev₂, hpd₂, ha₂, hcr₂, hni₂, hi₂, -, hrec₂, hfr₂⟩ := h₂
  -- step 2-4 の位置は入力の観測から決まる。
  have hre : ref' = ref := (referenceChild_unique h.tree href₁ href₂).symm
  subst hre
  have hpe : prev' = prev := by rw [hprev₁, hprev₂, h.tree.previousSibling]
  subst hpe
  have hpde : pd' = pd := by
    rw [h.tree] at hpd₂
    have he := hpd₁
    rw [hpd₂] at he
    exact Option.some.inj he
  subst hpde
  -- step 6
  have hdoc : IsDocument s.tree pd'.ownerDocument :=
    isDocument_ownerDocument (m := parent) hwf hpd₁
  have hobs₁ : ObsEq s₁ s₁' := adoptSpec_congr hwf h ha₁ ha₂
  have hwf₁ : WellFormed s₁.tree := adoptSpec_wellFormed hwf hdoc ha₁
  -- step 7
  obtain ⟨hobs₂, hreme⟩ := childRemoved_congr hwf₁ hobs₁ hcr₁ hcr₂
  subst hreme
  obtain ⟨hwf₂, hanc₂⟩ := childRemoved_facts hwf₁ hcr₁
  -- step 8
  have hnse : nodes' = nodes := (nodesToInsert_unique hobs₂.tree hni₁ hni₂).symm
  subst hnse
  -- step 9。validity が `s` について言うことを `s₂` へ移す。
  have hacyc₂ : ∀ ns : List NodeId, NodesToInsert s₂.tree node ns →
      ∀ m ∈ ns, ¬ InclusiveAncestor s₂.tree m parent := by
    -- `node` の kind と children は adopt も removal も跨いで残るので、
    -- `s₂` で読んだ列は `s` で読んだものと同じである。
    have hb : ∀ ns, NodesToInsert s₂.tree node ns → NodesToInsert s.tree node ns := by
      obtain ⟨od, hod, -⟩ := (id ha₁ : AdoptSpec _ _ _ _)
      obtain ⟨nd, hnd⟩ := exists_data_of_ownerDocumentOf hod
      obtain ⟨nd₁, hnd₁, hk₁, hch₁⟩ := adoptSpec_selfData hwf ha₁ hnd
      have hside : ∀ q, parentOf s₁.tree child = some q → node ≠ q := by
        intro q hq
        by_cases hcn : child = node
        · exfalso
          rw [hcn, adoptSpec_detached ha₁] at hq
          simp at hq
        · rw [adoptSpec_parentOf ha₁ hcn, hcp] at hq
          rw [← Option.some.inj hq]
          exact hnep
      obtain ⟨nd₂, hnd₂, hk₂, hch₂⟩ :
          ∃ nd₂, s₂.tree.get? node = some nd₂ ∧ nd₂.kind = nd.kind ∧
            nd₂.children = nd.children := by
        rcases hcr₁ with ⟨-, -, rfl⟩ | ⟨-, -, hrm⟩
        · exact ⟨nd₁, hnd₁, hk₁, hch₁⟩
        · obtain ⟨nd₂, hnd₂, hk₂', hch₂'⟩ := removeSpec_data hrm hnd₁ hside
          exact ⟨nd₂, hnd₂, by rw [hk₂', hk₁], by rw [hch₂', hch₁]⟩
      intro ns hns
      obtain ⟨nd₂', hnd₂', hcase⟩ := hns
      rw [hnd₂] at hnd₂'
      cases hnd₂'
      refine ⟨nd, hnd, ?_⟩
      rcases hcase with ⟨hk, hns'⟩ | ⟨hk, hns'⟩
      · exact Or.inl ⟨by rw [← hk₂]; exact hk, by rw [hns', hch₂]⟩
      · exact Or.inr ⟨by rw [← hk₂]; exact hk, hns'⟩
    intro ns hns m hm hc
    refine hacyc ns (hb ns hns) m hm ?_
    rcases hc with he | hanc
    · exact Or.inl he
    · exact Or.inr (adoptSpec_ancestor ha₁ (hanc₂ m parent hanc))
  have hobs₃ : ObsEq s₃ s₃' := insertSpec_congr hwf₂ hobs₂ hacyc₂ hi₁ hi₂
  -- step 10
  exact treeRecordQueued_congr hobs₃ hrec₁ hrec₂ hfr₁ hfr₂

/-- **`ReplaceSpec` は観測を一つに決める。** -/
theorem replaceSpec_deterministic {o₁ o₂ : DOMState} (hwf : WellFormed s.tree)
    (hnep : node ≠ parent) (hcp : parentOf s.tree child = some parent)
    (hacyc : ∀ ns : List NodeId, NodesToInsert s.tree node ns →
      ∀ m ∈ ns, ¬ InclusiveAncestor s.tree m parent)
    (h₁ : ReplaceSpec s child node parent o₁) (h₂ : ReplaceSpec s child node parent o₂) :
    ObsEq o₁ o₂ :=
  replaceSpec_congr hwf (ObsEq.refl s) hnep hcp hacyc h₁ h₂

end Dom.Spec
