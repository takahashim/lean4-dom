import Dom.Spec.Normalize
import Dom.Spec.ReplaceDataSound
import Dom.Spec.RemoveSound
import Dom.CharacterData.Normalize
import Dom.Properties.CharacterData
import Dom.Properties.Mutation

/-!
# `normalize` は `NormalizeSpec` を満たす

`Dom/Spec/InsertSound.lean` と同じ形。段ごとに実行側の結果を関係に移す。
-/

namespace Dom.Spec

open Dom

/-! ## 語彙の対応 -/

theorem isExclusiveText_iff {t : Tree} {n : NodeId} :
    isExclusiveText t n = true ↔ ExclusiveText t n := by
  unfold isExclusiveText ExclusiveText
  cases t.get? n with
  | none => simp
  | some d => simp

private theorem mem_takeWhile_imp {α : Type _} {f : α → Bool} :
    ∀ {l : List α} {x : α}, x ∈ l.takeWhile f → f x = true
  | [], x, h => by simp at h
  | a :: l, x, h => by
    by_cases ha : f a = true
    · rw [List.takeWhile_cons_of_pos ha] at h
      rcases List.mem_cons.mp h with rfl | hm
      · exact ha
      · exact mem_takeWhile_imp hm
    · rw [List.takeWhile_cons_of_neg ha] at h
      simp at h

private theorem head?_dropWhile {α : Type _} (f : α → Bool) :
    ∀ (l : List α) (x : α), (l.dropWhile f).head? = some x → f x = false
  | [], x, h => by simp at h
  | a :: l, x, h => by
    by_cases ha : f a = true
    · rw [List.dropWhile_cons_of_pos ha] at h
      exact head?_dropWhile f l x h
    · rw [List.dropWhile_cons_of_neg ha] at h
      simp only [List.head?_cons, Option.some.injEq] at h
      rw [← h]
      simpa using ha

/-- 実行側の `followingTexts` は関係を満たす。 -/
theorem followingTexts_spec {t : Tree} (hwf : WellFormed t) {n p : NodeId}
    (hp : parentOf t n = some p) : FollowingContiguousTexts t n (followingTexts t n) := by
  have hmem := mem_childrenOf_of_parentOf hwf hp
  obtain ⟨⟨pre, after⟩, hsp⟩ :=
    Option.isSome_iff_exists.mp (ListUtil.splitAt?_isSome_of_mem hmem)
  have hc := ListUtil.splitAt?_eq_some hsp
  unfold followingTexts
  rw [hp]
  simp only []
  rw [hsp]
  simp only []
  refine ⟨p, pre, after.dropWhile (isExclusiveText t), hp, ?_, ?_, ?_⟩
  · rw [List.takeWhile_append_dropWhile]; exact hc
  · intro x hx
    exact isExclusiveText_iff.mp (mem_takeWhile_imp hx)
  · intro x hx hex
    have := head?_dropWhile _ _ x hx
    rw [isExclusiveText_iff.mpr hex] at this
    cases this

/-! ## 兄弟を一つ畳む -/

theorem bpHandedOff_normalizeMergeBP (survivor sib parent : NodeId) (idx len : Nat)
    (bp : BoundaryPoint) :
    BPHandedOff survivor sib parent idx len bp (normalizeMergeBP survivor sib parent idx len bp) := by
  unfold normalizeMergeBP
  by_cases h₁ : bp.node = sib
  · rw [if_pos h₁]; exact Or.inl ⟨h₁, rfl⟩
  · rw [if_neg h₁]
    by_cases h₂ : bp.node = parent ∧ bp.offset = idx
    · rw [if_pos h₂]; exact Or.inr (Or.inl ⟨h₂.1, h₂.2, rfl⟩)
    · rw [if_neg h₂]; exact Or.inr (Or.inr ⟨h₁, h₂, rfl⟩)

theorem rangesHandedOff_map (s : DOMState) (survivor sib parent : NodeId) (idx len : Nat) :
    RangesHandedOff s
      { s with ranges := s.ranges.map (normalizeMergeRange survivor sib parent idx len) }
      survivor sib parent idx len := by
  refine ⟨_, rfl, by simp, ?_⟩
  intro i r r' hr hr'
  rw [List.getElem?_map, hr] at hr'
  simp only [Option.map_some, Option.some.injEq] at hr'
  subst hr'
  exact ⟨bpHandedOff_normalizeMergeBP .., bpHandedOff_normalizeMergeBP ..⟩

/-- step 6-7 の後半。range を渡した状態から `remove` が成功すれば、関係の後半が立つ。 -/
private theorem merge_tail {s₁ s₂ s' : DOMState} {survivor sib parent : NodeId} {idx len : Nat}
    (hwf₁ : WellFormed s₁.tree)
    (hs₂ : s₂ = { s₁ with ranges := s₁.ranges.map (normalizeMergeRange survivor sib parent idx len) })
    (h : remove s₂ sib = .ok s') :
    RangesHandedOff s₁ s₂ survivor sib parent idx len ∧ RemoveSpec s₂ sib false s' ∧
      WellFormed s'.tree := by
  have hwf₂ : WellFormed s₂.tree := by rw [hs₂]; exact hwf₁
  exact ⟨hs₂ ▸ rangesHandedOff_map .., remove_sound hwf₂ h, remove_preserves_wellformed hwf₂ h⟩

/-- **兄弟を一つ畳む段の soundness。** well-formedness も運ぶ。 -/
theorem normalizeMergeOne_sound {s s' : DOMState} {survivor sib : NodeId}
    (hwf : WellFormed s.tree) (h : normalizeMergeOne s survivor sib = .ok s') :
    SiblingMerged s survivor sib s' ∧ WellFormed s'.tree := by
  unfold normalizeMergeOne at h
  split at h
  · next dsurv dsib parent idx hsurv hsib hp hidx =>
    obtain ⟨pre, post, hc, hlen, -⟩ := (index_eq_some_iff_split hp).mp hidx
    subst hlen
    by_cases hbad : (survivor == sib || dsurv.kind != NodeKind.text ||
        dsib.kind != NodeKind.text) = true
    · simp only [hbad, if_true] at h
      cases h
    · simp only [hbad, Bool.false_eq_true, if_false] at h
      by_cases hemp : dsib.data.isEmpty = true
      · simp only [hemp, if_true] at h
        obtain ⟨hro, hrm, hwf'⟩ := merge_tail hwf rfl h
        exact ⟨⟨dsurv, dsib, parent, pre, post, s, _, hsurv, hsib, hp, hc,
          Or.inl ⟨by simpa using hemp, rfl⟩, hro, hrm⟩, hwf'⟩
      · simp only [hemp, Bool.false_eq_true, if_false] at h
        cases hrd : replaceData s survivor dsurv.length 0 dsib.data with
        | error e => rw [hrd] at h; cases h
        | ok s₁ =>
          rw [hrd] at h
          obtain ⟨hro, hrm, hwf'⟩ := merge_tail (replaceData_preserves_wellformed hwf hrd) rfl h
          exact ⟨⟨dsurv, dsib, parent, pre, post, s₁, _, hsurv, hsib, hp, hc,
            Or.inr ⟨by simpa using hemp, replaceData_sound hwf hrd⟩, hro, hrm⟩, hwf'⟩
  · cases h

/-- **run を畳む段の soundness。** -/
theorem normalizeRun_sound {survivor : NodeId} : ∀ (sibs : List NodeId) {s s' : DOMState},
    WellFormed s.tree → normalizeRun s survivor sibs = .ok s' →
    RunMerged s survivor sibs s' ∧ WellFormed s'.tree
  | [], s, s', hwf, h => by
    rw [normalizeRun] at h
    cases h
    exact ⟨.nil, hwf⟩
  | sib :: rest, s, s', hwf, h => by
    rw [normalizeRun] at h
    split at h
    · cases h
    · next s₁ hm =>
      obtain ⟨hsm, hwf₁⟩ := normalizeMergeOne_sound hwf hm
      obtain ⟨hrun, hwf'⟩ := normalizeRun_sound rest hwf₁ h
      exact ⟨.cons hsm hrun, hwf'⟩

/-- **候補列の処理の soundness。** -/
theorem normalizeList_sound (this : NodeId) : ∀ (cands : List NodeId) {s s' : DOMState},
    WellFormed s.tree → normalizeList s this cands = .ok s' → NormalizedEach this s cands s'
  | [], s, s', _, h => by
    rw [normalizeList] at h
    cases h
    exact .nil
  | n :: rest, s, s', hwf, h => by
    rw [normalizeList] at h
    split at h
    · next hanc =>
      have hanc' : Ancestor s.tree this n := (isAncestorOf_iff hwf this n).mp hanc
      obtain ⟨p, hp⟩ := hanc'.parent_isSome
      split at h
      · next hn =>
        exfalso
        rw [parentOf_eq, hn] at hp
        cases hp
      · next d hd =>
        split at h
        · next hlen =>
          split at h
          · cases h
          · next s₁ hr =>
            exact .empty hanc' hd hlen (remove_sound hwf hr)
              (normalizeList_sound this rest (remove_preserves_wellformed hwf hr) h)
        · next hlen =>
          split at h
          · cases h
          · next s₁ hr =>
            obtain ⟨hrun, hwf₁⟩ := normalizeRun_sound _ hwf hr
            exact .run hanc' hd hlen (followingTexts_spec hwf hp) hrun
              (normalizeList_sound this rest hwf₁ h)
    · next hanc =>
      refine .skip (fun ha => hanc ((isAncestorOf_iff hwf this n).mpr ha)) ?_
      exact normalizeList_sound this rest hwf h

/-- **`normalize` は `NormalizeSpec` を満たす。** -/
theorem normalize_sound {s s' : DOMState} {this : NodeId} (hwf : WellFormed s.tree)
    (h : normalize s this = .ok s') : NormalizeSpec s this s' := by
  unfold normalize at h
  split at h
  · cases h
  · next d hd =>
    refine ⟨⟨d, hd⟩, ?_⟩
    have hf : ((preorder s.tree this).drop 1).filter (isExclusiveText s.tree) =
        DescendantExclusiveTexts s.tree this := by
      unfold DescendantExclusiveTexts
      congr 1
      funext n
      unfold isExclusiveText
      cases s.tree.get? n <;> rfl
    rw [hf] at h
    exact normalizeList_sound this _ hwf h

end Dom.Spec
