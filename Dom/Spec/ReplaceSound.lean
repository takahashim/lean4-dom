import Dom.Spec.Replace
import Dom.Validity.Structural
import Dom.Spec.AdoptSound
import Dom.Spec.InsertSound
import Dom.Spec.RemoveCongr
import Dom.Spec.AdoptCongr

/-!
# `replace` は `ReplaceSpec` を満たす

`Dom/Spec/InsertSound.lean` と同じ形。step ごとに実行側の結果を関係に移す。

`nodes` の読む位置だけは実行側と関係でずれている。実行関数は step 1 の直後に
`s.tree` から読み、関係は step 8 のとおり removal の後の木から読む。
`child` は `node` の子ではありえない（step 1 の validity が
「`node` は `parent` の inclusive ancestor でない」を保証し、`child` の parent は
`parent` である）ので、どちらでも同じ列になる。その一致をここで示す。
-/

namespace Dom.Spec

open Dom

/--
`replace` の step 1 が通れば、`node` は `parent` ではない。

`node` が `child` と同じことはありうる（子を自分自身で置き換える呼び出し）。
仕様の step 3 が reference child をずらすのはそのためである。
-/
theorem replace_node_ne_parent {t : Tree} (hwf : WellFormed t) {node parent child : NodeId}
    (hv : ensurePreInsertionValidity t node parent (some child) [child] = .ok ()) :
    node ≠ parent := by
  obtain ⟨-, -, hanc, -⟩ := ensurePreInsertionValidity_ok hv
  intro he
  rw [(isInclusiveAncestorOf_iff hwf node parent).mpr (Or.inl he)] at hanc
  exact Bool.noConfusion hanc

/--
`child` は `node` の子ではない。

`child` の parent は `parent` で（step 1 の validity）、`node` は `parent` ではないからである。
これで `node` の children は step 7 の removal を跨いで変わらない。
-/
theorem replace_child_not_child_of_node {t : Tree} (hwf : WellFormed t)
    {node parent child : NodeId}
    (hv : ensurePreInsertionValidity t node parent (some child) [child] = .ok ()) :
    ∀ p, parentOf t child = some p → node ≠ p := by
  obtain ⟨-, -, -, hchild⟩ := ensurePreInsertionValidity_ok hv
  intro p hp
  rw [hchild child rfl] at hp
  rw [← Option.some.inj hp]
  exact replace_node_ne_parent hwf hv


/-! ## 全体 -/

/--
**`replace` は `ReplaceSpec` を満たす。**

`StructurallyValid` まで要るのは step 10 の assertion（addedNodes と removedNodes の
どちらかは空でない）のためである。それが破れるのは
「`node` が `child` と同じ空の DocumentFragment」のときだけで、
`fragmentHasNoParent` がその状態を禁じている。
-/
theorem replace_sound {s s' : DOMState} {child node parent : NodeId}
    (hsv : StructurallyValid s.tree)
    (h : replace s child node parent = .ok s') : ReplaceSpec s child node parent s' := by
  have hwf : WellFormed s.tree := hsv.wellFormed
  unfold replace at h
  split at h
  · simp at h
  · next hv =>
    split at h
    · simp at h
    · next pd hpd =>
      simp only at h
      obtain ⟨-, ⟨nd, hnd⟩, -, hchild⟩ := ensurePreInsertionValidity_ok hv
      have hcp : parentOf s.tree child = some parent := hchild child rfl
      have hnep : node ≠ parent := replace_node_ne_parent hwf hv
      simp only [hnd] at h
      split at h
      · simp at h
      · next s₁ ha =>
        have hwf₁ := adopt_preserves_wellformed hwf (isDocument_ownerDocument hwf hpd) ha
        -- adopt が動かす parent は `node` だけである。
        have hpa : parentOf s₁.tree child =
            if child = node then none else parentOf s.tree child := parentOf_adopt ha child
        split at h
        · simp at h
        · next s₂ hr =>
          have hwf₂ : WellFormed s₂.tree := by
            revert hr; split
            · intro hr; rw [← Except.ok.inj hr]; exact hwf₁
            · intro hr; exact remove_preserves_wellformed hwf₁ (by simpa using hr)
          -- step 7 の関係と、そこで外れる node が `node` でないこと。
          have hnotnode : ∀ q, parentOf s₁.tree child = some q → node ≠ q := by
            intro q hq
            rw [hpa] at hq
            by_cases hcn : child = node
            · rw [if_pos hcn] at hq; exact absurd hq (by simp)
            · rw [if_neg hcn, hcp] at hq
              rw [← Option.some.inj hq]
              exact hnep
          have hcr : ChildRemoved s₁ s₂ child
              (if (parentOf s₁.tree child).isSome then [child] else []) := by
            revert hr
            split
            · next hp =>
              intro hr
              rw [hp]
              exact Or.inl ⟨hp, by simp, (Except.ok.inj hr).symm⟩
            · next p hp =>
              intro hr
              rw [hp]
              exact Or.inr ⟨⟨p, hp⟩, by simp, remove_sound hwf₁ (by simpa using hr)⟩
          -- step 8。`node` の kind と children は adopt も removal も跨いで残る。
          obtain ⟨nd₂, hnd₂, hk₂, hch₂⟩ :
              ∃ nd₂, s₂.tree.get? node = some nd₂ ∧ nd₂.kind = nd.kind ∧
                nd₂.children = nd.children := by
            obtain ⟨nd₁, hnd₁, hk₁, hch₁⟩ := adoptSpec_selfData hwf (adopt_sound hwf ha) hnd
            revert hr
            split
            · intro hr
              rw [← Except.ok.inj hr]
              exact ⟨nd₁, hnd₁, hk₁, hch₁⟩
            · next p hp =>
              intro hr
              obtain ⟨nd₂, hnd₂, hk₂', hch₂'⟩ :=
                removeSpec_data (remove_sound hwf₁ (by simpa using hr)) hnd₁ hnotnode
              exact ⟨nd₂, hnd₂, by rw [hk₂', hk₁], by rw [hch₂', hch₁]⟩
          have hni : NodesToInsert s₂.tree node
              (if nd.kind == NodeKind.documentFragment then nd.children else [node]) := by
            refine ⟨nd₂, hnd₂, ?_⟩
            by_cases hk : nd.kind = NodeKind.documentFragment
            · exact Or.inl ⟨by rw [hk₂, hk], by rw [if_pos (by simp [hk]), hch₂]⟩
            · exact Or.inr ⟨by rw [hk₂]; exact hk, by rw [if_neg (by simp [hk])]⟩
          split at h
          · simp at h
          · next s₃ hi =>
            have hwf₃ : WellFormed s₃.tree := insert_preserves_wellformed hwf₂ hi
            -- step 2-3
            have href : ReferenceChild s.tree child node
                (if nextSibling s.tree child = some node then nextSibling s.tree node
                 else nextSibling s.tree child) := by
              by_cases hc : nextSibling s.tree child = some node
              · exact Or.inl ⟨hc, by rw [if_pos hc]⟩
              · exact Or.inr ⟨hc, by rw [if_neg hc]⟩
            -- step 10 の assertion
            have hassert :
                (if nd.kind == NodeKind.documentFragment then nd.children else [node]) ≠ [] ∨
                (if (parentOf s₁.tree child).isSome then [child] else []) ≠ [] := by
              by_cases hsome : (parentOf s₁.tree child).isSome
              · exact Or.inr (by rw [if_pos hsome]; simp)
              · refine Or.inl ?_
                -- child が外れているのは `child = node` のときだけである。
                have hcn : child = node := by
                  by_cases hc : child = node
                  · exact hc
                  · exfalso
                    rw [hpa, if_neg hc, hcp] at hsome
                    simp at hsome
                by_cases hk : nd.kind = NodeKind.documentFragment
                · exfalso
                  have hnp : nd.parent = none := hsv.fragmentHasNoParent node nd hnd hk
                  rw [hcn, parentOf, hnd] at hcp
                  simp [hnp] at hcp
                · rw [if_neg (by simp [hk])]
                  simp
            have hguard :
                ¬((if nd.kind == NodeKind.documentFragment then nd.children else [node]).isEmpty &&
                  (if (parentOf s₁.tree child).isSome then [child] else []).isEmpty) := by
              rcases hassert with hA | hB
              · cases hx : (if nd.kind == NodeKind.documentFragment then nd.children
                            else [node]) with
                | nil => exact absurd hx hA
                | cons a as => simp [hx]
              · cases hy : (if (parentOf s₁.tree child).isSome then [child] else []) with
                | nil => exact absurd hy hB
                | cons a as => simp [hy]
            rw [← Except.ok.inj h]
            exact ⟨_, _, _, _, pd, s₁, s₂, s₃, href, rfl, hpd, adopt_sound hwf ha, hcr, hni,
              insert_sound hwf₂ hi, hassert,
              treeRecordQueued_of_queue s₃ hwf₃ parent _ _ _ _ hguard,
              ⟨by simp, by simp, by simp, by simp⟩⟩

end Dom.Spec
