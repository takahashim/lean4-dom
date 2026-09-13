import Dom.Validity.Admissible
import Dom.CharacterData.Normalize

/-!
# `normalize()` が `AdmissibleDOMState` を保つこと

`Dom/CharacterData/Normalize.lean` の算法は `replaceData` と `remove` の合成に
boundary point の引き渡しを挟んだものなので、保存もその三つに分かれる。

引き渡しの側だけが新しい。消える兄弟の中を指していた boundary point は
survivor の継ぎ目より後ろへ移るが、その時点で survivor の長さは
継ぎ目 + 兄弟の長さまで伸びているので、端点は木の中に収まったままである。
-/

namespace Dom

/-- boundary point の引き渡しは、端点の妥当性を保つ。 -/
theorem endpointsValid_normalizeMerge {s : DOMState} {survivor sib parent : NodeId}
    {idx len : Nat} {dsurv dsib : NodeData}
    (hsurv : s.tree.get? survivor = some dsurv) (hsib : s.tree.get? sib = some dsib)
    (hlen : len + dsib.length ≤ dsurv.length)
    (h : RangeEndpointsValid s) :
    RangeEndpointsValid
      { s with ranges := s.ranges.map (normalizeMergeRange survivor sib parent idx len) } := by
  have hbp : ∀ bp : BoundaryPoint, ValidBoundaryPoint s.tree bp →
      ValidBoundaryPoint s.tree (normalizeMergeBP survivor sib parent idx len bp) := by
    intro bp hv
    unfold normalizeMergeBP
    split
    · next he =>
      refine ⟨dsurv, hsurv, ?_⟩
      obtain ⟨d, hd, hoff⟩ := hv
      rw [he, hsib] at hd
      cases hd
      simp only
      omega
    · split
      · exact ⟨dsurv, hsurv, by simp only; omega⟩
      · exact hv
  intro r hr
  simp only [List.mem_map] at hr
  obtain ⟨r₀, hr₀, rfl⟩ := hr
  exact ⟨hbp _ (h r₀ hr₀).1, hbp _ (h r₀ hr₀).2⟩

/-- 兄弟を一つ畳む step は admissibility を保つ。 -/
theorem admissible_normalizeMergeOne {s s' : DOMState} {survivor sib : NodeId}
    (h : AdmissibleDOMState s) (hm : normalizeMergeOne s survivor sib = .ok s') :
    AdmissibleDOMState s' := by
  unfold normalizeMergeOne at hm
  split at hm
  · next dsurv dsib parent idx hsurv hsib hpar hidx =>
    split at hm
    · simp at hm
    · next hkind =>
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not,
        beq_iff_eq] at hkind
      obtain ⟨⟨hne, hks⟩, hkb⟩ := hkind
      have hchar : dsurv.kind.isCharacterData = true := by rw [hks]; rfl
      have hcharb : dsib.kind.isCharacterData = true := by rw [hkb]; rfl
      split at hm
      · -- 空の兄弟。data は変わらないので、そのまま引き渡して外す。
        next hempty =>
        have hzero : dsib.length = 0 := by
          simp only [NodeData.length, hcharb, if_pos]
          rw [String.isEmpty_iff.mp hempty]
          rfl
        refine admissible_remove ?_ hm
        exact ⟨h.structural, h.nodeDocuments, h.documentTrees,
          endpointsValid_normalizeMerge hsurv hsib (by omega) h.rangeEndpoints,
          h.iterators, h.observerRegistrations, h.attributes⟩
      · next hempty =>
        dsimp only at hm
        split at hm
        · simp at hm
        · next s₁ hs₁ =>
          obtain ⟨d, spliced, hd, -, hoff, hsplice, htree, -, -⟩ := replaceData_ok hs₁
          rw [hsurv] at hd
          cases hd
          have h₁ := admissible_replaceData h hs₁
          have hd₁ : s₁.tree.get? survivor = some { dsurv with data := spliced } := by
            rw [htree, get?_withData hsurv]
            simp
          have hsib₁ : s₁.tree.get? sib = some dsib := by
            rw [htree, get?_withData hsurv]
            rw [if_neg (fun he => hne he.symm)]
            exact hsib
          have hlen : dsurv.length + dsib.length
              ≤ ({ dsurv with data := spliced } : NodeData).length := by
            have hl := length_spliceData? hsplice
            have hzero : adjustedCount dsurv.length dsurv.length 0 = 0 := by
              simp only [adjustedCount]
              split <;> omega
            rw [hzero] at hl
            simp only [NodeData.length, hchar, hcharb, if_pos]
            omega
          refine admissible_remove ?_ hm
          exact ⟨h₁.structural, h₁.nodeDocuments, h₁.documentTrees,
            endpointsValid_normalizeMerge hd₁ hsib₁ hlen h₁.rangeEndpoints,
            h₁.iterators, h₁.observerRegistrations, h₁.attributes⟩
  · simp at hm

/-- run を畳む step も admissibility を保つ。 -/
theorem admissible_normalizeRun : ∀ (cands : List NodeId) {s s' : DOMState} {survivor : NodeId}
    {k : Nat}, AdmissibleDOMState s → normalizeRun s survivor cands = .ok (s', k) →
    AdmissibleDOMState s'
  | [], s, s', survivor, k, h, hr => by
    rw [normalizeRun] at hr
    simp only [Except.ok.injEq, Prod.mk.injEq] at hr
    rw [← hr.1]
    exact h
  | sib :: rest, s, s', survivor, k, h, hr => by
    rw [normalizeRun] at hr
    split at hr
    · cases hm : normalizeMergeOne s survivor sib with
      | error e => rw [hm] at hr; simp at hr
      | ok s₁ =>
        rw [hm] at hr
        dsimp only at hr
        cases hp : normalizeRun s₁ survivor rest with
        | error e => rw [hp] at hr; simp at hr
        | ok pair =>
          rw [hp] at hr
          obtain ⟨s₂, k₂⟩ := pair
          dsimp only at hr
          simp only [Except.ok.injEq, Prod.mk.injEq] at hr
          rw [← hr.1]
          exact admissible_normalizeRun rest (admissible_normalizeMergeOne h hm) hp
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hr
      rw [← hr.1]
      exact h

/-- 候補列の処理も admissibility を保つ。 -/
theorem admissible_normalizeList : ∀ (cands : List NodeId) {s s' : DOMState},
    AdmissibleDOMState s → normalizeList s cands = .ok s' → AdmissibleDOMState s'
  | [], s, s', h, hl => by
    rw [normalizeList] at hl
    rw [← Except.ok.inj hl]
    exact h
  | n :: rest, s, s', h, hl => by
    rw [normalizeList] at hl
    split at hl
    · split at hl
      · cases hs : remove s n with
        | error e => rw [hs] at hl; simp at hl
        | ok s₁ =>
          rw [hs] at hl
          dsimp only at hl
          exact admissible_normalizeList rest (admissible_remove h hs) hl
      · cases hp : normalizeRun s n rest with
        | error e => rw [hp] at hl; simp at hl
        | ok pair =>
          rw [hp] at hl
          obtain ⟨s₁, k⟩ := pair
          dsimp only at hl
          exact admissible_normalizeList (rest.drop k) (admissible_normalizeRun rest h hp) hl
    · exact admissible_normalizeList rest h hl
termination_by cands => cands.length
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (simp only [List.length_drop]; omega)

/-- **`normalize()` は admissibility を保つ。** -/
theorem admissible_normalize {s s' : DOMState} {node : NodeId}
    (h : AdmissibleDOMState s) (hn : normalize s node = .ok s') : AdmissibleDOMState s' := by
  unfold normalize at hn
  split at hn
  · simp at hn
  · exact admissible_normalizeList _ h hn

end Dom
