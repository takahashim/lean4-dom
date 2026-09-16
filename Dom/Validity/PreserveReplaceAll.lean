import Dom.Validity.PreserveReplaceDocument

/-!
# `replace all` による保存
-/

namespace Dom

/-! ## replace all -/

/-- `removeEach` は children を減らすだけで、外した node はどこの children にも残らない。 -/
theorem removeEach_childrenOf_sub :
    ∀ (ms : List NodeId) {s s' : DOMState} {b : Bool}, WellFormed s.tree →
      removeEach s ms b = .ok s' →
      ∀ p, (childrenOf s'.tree p).Sublist (childrenOf s.tree p) ∧
        (∀ m ∈ ms, m ∉ childrenOf s'.tree p)
  | [], _, _, _, _, hr, p => by
    rw [← Except.ok.inj hr]
    exact ⟨List.Sublist.refl _, fun m hm => absurd hm (by simp)⟩
  | n :: ms, s, s', b, hwf, hr, p => by
    simp only [removeEach] at hr
    split at hr
    · simp at hr
    · next s₁ h₁ =>
      have hch : childrenOf s₁.tree p = ListUtil.removeAll (childrenOf s.tree p) n :=
        detach_childrenOf_removeAll hwf (remove_ok h₁).2 p
      have hwf₁ := remove_preserves_wellformed hwf h₁
      obtain ⟨hsub, hnot⟩ := removeEach_childrenOf_sub ms hwf₁ hr p
      have hsub' : (childrenOf s₁.tree p).Sublist (childrenOf s.tree p) := by
        rw [hch]; exact ListUtil.removeAll_sublist _ _
      refine ⟨hsub.trans hsub', fun m hm => ?_⟩
      rcases List.mem_cons.mp hm with rfl | hm'
      · intro hmem
        have hx₁ := hsub.subset hmem
        rw [hch] at hx₁
        exact ((ListUtil.mem_removeAll _ _ _).mp hx₁).1 rfl
      · exact hnot m hm'

/-- §4.2.3 replace all step 4 の後、parent の children は空になる。 -/
theorem removeEach_childrenOf_nil {s s' : DOMState} {parent : NodeId} {b : Bool}
    (hwf : WellFormed s.tree) (hr : removeEach s (childrenOf s.tree parent) b = .ok s') :
    childrenOf s'.tree parent = [] := by
  obtain ⟨hsub, hnot⟩ := removeEach_childrenOf_sub _ hwf hr parent
  cases hl : childrenOf s'.tree parent with
  | nil => rfl
  | cons y l =>
    exfalso
    have hy : y ∈ childrenOf s'.tree parent := by rw [hl]; simp
    exact hnot y (hsub.subset hy) hy

/--
`replace all` は node tree の制約を自分では検査しない。

したがって `insert` に必要な kind の事実は仮定として受け取る。
呼び出し側（`replaceChildren` など）が `ensure pre-insertion validity` で確立する。
-/
theorem structurallyValid_replaceAll {s s' : DOMState} {node : Option NodeId} {parent : NodeId}
    (h : StructurallyValid s.tree)
    (hpk : ∀ n, node = some n → ∀ pd, s.tree.get? parent = some pd →
      pd.kind.canHaveChildren = true)
    (hnk : ∀ n, node = some n → ∀ nd, s.tree.get? n = some nd → nd.kind ≠ NodeKind.document)
    (hdtf : ∀ n, node = some n → ∀ nd, s.tree.get? n = some nd →
      nd.kind = NodeKind.documentType →
      ∀ pd, s.tree.get? parent = some pd → pd.kind = NodeKind.document)
    (hr : replaceAll s node parent = .ok s') : StructurallyValid s'.tree := by
  obtain ⟨s₁, s₂, hre, hstep, hsx⟩ := replaceAll_cases hr
  have h₁ : StructurallyValid s₁.tree := structurallyValid_removeEach _ h hre
  have hkp : ShapePreserving s.tree s₁.tree := shapePreserving_removeEach _ hre
  have h₂ : StructurallyValid s₂.tree := by
    rcases hstep with ⟨-, rfl⟩ | ⟨m, hm, hins⟩
    · exact h₁
    · refine structurallyValid_insert_of_facts h₁ ?_ ?_ ?_ hins
      · exact kindFact_of_kindPreserving hkp (P := fun k => k.canHaveChildren = true)
          (hpk m hm)
      · exact kindFact_of_kindPreserving hkp (P := fun k => k ≠ NodeKind.document)
          (hnk m hm)
      · exact doctypeFact_of_kindPreserving hkp (hdtf m hm)
  rw [hsx]
  simpa using h₂

theorem nodeDocumentsValid_replaceAll {s s' : DOMState} {node : Option NodeId} {parent : NodeId}
    (hs : StructurallyValid s.tree) (h : NodeDocumentsValid s.tree)
    (hpk : ∀ n, node = some n → ∀ pd, s.tree.get? parent = some pd →
      pd.kind.canHaveChildren = true)
    (hnk : ∀ n, node = some n → ∀ nd, s.tree.get? n = some nd → nd.kind ≠ NodeKind.document)
    (hdtf : ∀ n, node = some n → ∀ nd, s.tree.get? n = some nd →
      nd.kind = NodeKind.documentType →
      ∀ pd, s.tree.get? parent = some pd → pd.kind = NodeKind.document)
    (hr : replaceAll s node parent = .ok s') : NodeDocumentsValid s'.tree := by
  obtain ⟨s₁, s₂, hre, hstep, hsx⟩ := replaceAll_cases hr
  have hs₁ : StructurallyValid s₁.tree := structurallyValid_removeEach _ hs hre
  have h₁ : NodeDocumentsValid s₁.tree := nodeDocumentsValid_removeEach _ hs h hre
  have hkp : ShapePreserving s.tree s₁.tree := shapePreserving_removeEach _ hre
  have h₂ : NodeDocumentsValid s₂.tree := by
    rcases hstep with ⟨-, rfl⟩ | ⟨m, hm, hins⟩
    · exact h₁
    · refine nodeDocumentsValid_insert_of_facts hs₁ h₁ ?_ ?_ ?_ hins
      · exact kindFact_of_kindPreserving hkp (P := fun k => k.canHaveChildren = true)
          (hpk m hm)
      · exact kindFact_of_kindPreserving hkp (P := fun k => k ≠ NodeKind.document)
          (hnk m hm)
      · exact doctypeFact_of_kindPreserving hkp (hdtf m hm)
  rw [hsx]
  simpa using h₂

/--
`replace all` は parent の children を空にしてから入れるので、
Document の制約には「入れる node の側」の条件しか要らない。
-/
theorem documentTreesValid_replaceAll {s s' : DOMState} {node : Option NodeId} {parent : NodeId}
    (hwf : WellFormed s.tree) (h : DocumentTreesValid s.tree)
    (hok : kindOf s.tree parent = some NodeKind.document →
      ∀ n, node = some n → ∀ nd, s.tree.get? n = some nd →
      (∀ m ∈ (if nd.kind = NodeKind.documentFragment then nd.children else [n]),
        ∀ k, kindOf s.tree m = some k → k.isText = false) ∧
      (((if nd.kind = NodeKind.documentFragment then nd.children else [n]).filter fun m =>
          kindOf s.tree m == some NodeKind.element).length +
        ((if nd.kind = NodeKind.documentFragment then nd.children else [n]).filter fun m =>
          kindOf s.tree m == some NodeKind.documentType).length ≤ 1))
    (hr : replaceAll s node parent = .ok s') : DocumentTreesValid s'.tree := by
  obtain ⟨s₁, s₂, hre, hstep, hsx⟩ := replaceAll_cases hr
  have hwf₁ : WellFormed s₁.tree := removeEach_preserves_wellformed _ hwf hre
  have h₁ : DocumentTreesValid s₁.tree := documentTreesValid_removeEach _ hwf h hre
  have hkp : ShapePreserving s.tree s₁.tree := shapePreserving_removeEach _ hre
  have hnil : childrenOf s₁.tree parent = [] := removeEach_childrenOf_nil hwf hre
  have helemnil : elementChildren s₁.tree parent = [] := by
    unfold elementChildren; rw [hnil]; rfl
  have hdtnil : doctypeChildren s₁.tree parent = [] := by
    unfold doctypeChildren; rw [hnil]; rfl
  have h₂ : DocumentTreesValid s₂.tree := by
    rcases hstep with ⟨-, rfl⟩ | ⟨m, hm, hins⟩
    · exact h₁
    · refine documentTreesValid_insert_of_seqOk hwf₁ h₁ ?_ hins
      intro nd hnd
      obtain ⟨nd₀, hnd₀, hkd⟩ := shapePreserving_get? hkp hnd
      intro hdocparent
      have hdoc0 : kindOf s.tree parent = some NodeKind.document := by
        have hkk : kindOf s₁.tree parent = kindOf s.tree parent := hkp.kind parent
        rw [← hkk]
        exact hdocparent
      obtain ⟨g1, g2⟩ := hok hdoc0 m hm nd₀ hnd₀
      have hkind : ∀ x, kindOf s₁.tree x = kindOf s.tree x := hkp.kind
      -- 入れる node の列は `removeEach` で縮むだけである。
      have hsl : ((if nd.kind = NodeKind.documentFragment then nd.children
            else [m])).Sublist
          (if nd₀.kind = NodeKind.documentFragment then nd₀.children else [m]) := by
        by_cases hk : nd.kind = NodeKind.documentFragment
        · rw [if_pos hk, if_pos (by rw [hkd]; exact hk)]
          have hs := (removeEach_childrenOf_sub _ hwf hre m).1
          rw [childrenOf_eq hnd, childrenOf_eq hnd₀] at hs
          exact hs
        · rw [if_neg hk, if_neg (by rw [hkd]; exact hk)]
          exact List.Sublist.refl _
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro x hx k hk
        exact g1 x (hsl.subset hx) k (by rw [← hkind x]; exact hk)
      · simp only [hkind]
        exact Nat.le_trans (Nat.add_le_add (hsl.filter _).length_le
          (hsl.filter _).length_le) g2
      · rw [helemnil]
        simp only [hkind, List.length_nil, Nat.zero_add]
        exact Nat.le_trans (Nat.le_trans (hsl.filter _).length_le (Nat.le_add_right _ _)) g2
      · rw [hdtnil]
        simp only [hkind, List.length_nil, Nat.zero_add]
        exact Nat.le_trans (Nat.le_trans (hsl.filter _).length_le (Nat.le_add_left _ _)) g2
      · intro _ _ _ c hc
        exact absurd hc (by simp)
      · intro _ _ _
        exact ⟨fun c hc => absurd hc (by simp), fun _ => helemnil⟩
  rw [hsx]
  simpa using h₂

end Dom
