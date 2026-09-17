import Dom.Spec.ReplaceData
import Dom.Spec.RecordSound
import Dom.CharacterData.ReplaceData

/-!
# `replace data` は関係意味論を満たす

`Dom/Spec/ReplaceData.lean` の `ReplaceDataSpec` を、実行関数 `replaceData` が満たすことを示す。
-/

namespace Dom.Spec

open Dom

/-- 実行側の切り詰めは step 3 のとおりである。 -/
theorem clampedCount_adjustedCount (length offset count : Nat) :
    ClampedCount length offset count (adjustedCount length offset count) := by
  unfold ClampedCount adjustedCount
  split
  · next h => exact Or.inl ⟨h, rfl⟩
  · next h => exact Or.inr ⟨h, rfl⟩

/-- 実行側の splice は step 5-7 のとおりである。 -/
theorem dataSpliced_of_spliceData? {old data new : String} {offset count : Nat}
    (h : spliceData? old offset count data = some new) :
    DataSpliced old offset count data new := by
  unfold spliceData? at h
  split at h
  · simp at h
  · next pre rest hpre =>
    split at h
    · simp at h
    · next mid post hmid =>
      obtain ⟨hpre₁, hpre₂⟩ := Utf16.splitAt?_spec hpre
      obtain ⟨hmid₁, hmid₂⟩ := Utf16.splitAt?_spec hmid
      refine ⟨pre, mid, post, ?_, hpre₂, hmid₂, ?_⟩
      · rw [← hpre₁, ← hmid₁]
        simp
      · rw [← Option.some.inj h, String.toList_ofList]

/-- 実行側の boundary point 調整は step 8-11 のとおりである。 -/
theorem dataAdjusted_replaceDataAdjustBP (node : NodeId) (offset count newLen : Nat)
    (bp : BoundaryPoint) :
    DataAdjusted node offset count newLen bp
      (replaceDataAdjustBP node offset count newLen bp) := by
  unfold DataAdjusted replaceDataAdjustBP
  split
  · next hne => exact Or.inl ⟨hne, rfl⟩
  · next hne =>
    have hn : bp.node = node := by simpa using hne
    split
    · next hin => exact Or.inr (Or.inl ⟨hn, hin.1, hin.2, by rw [hn]⟩)
    · next hin =>
      split
      · next hafter => exact Or.inr (Or.inr (Or.inl ⟨hn, hafter, by rw [hn]⟩))
      · next hafter => exact Or.inr (Or.inr (Or.inr ⟨hn, hin, hafter, rfl⟩))

/-- **`replaceData` は `ReplaceDataSpec` を満たす。** -/
theorem replaceData_sound {s s' : DOMState} {node : NodeId} {offset count : Nat} {data : String}
    (hwf : WellFormed s.tree) (h : replaceData s node offset count data = .ok s') :
    ReplaceDataSpec s node offset count data s' := by
  unfold replaceData at h
  split at h
  · simp at h
  · next d hd =>
    split at h
    · simp at h
    · next hkind =>
      split at h
      · simp at h
      · next hlen =>
        split at h
        · simp at h
        · next spliced hsp =>
          refine ⟨d, adjustedCount d.length offset count, spliced,
            queueCharacterDataRecord s node d.data, hd, by simpa using hkind, by omega,
            clampedCount_adjustedCount .., dataSpliced_of_spliceData? hsp,
            characterDataRecordQueued_of_queue s hwf node d.data,
            ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · -- step 5-7：木の効果
            rw [← Except.ok.inj h]
            refine ⟨?_, ?_⟩
            · intro d₀ hd₀
              rw [hd] at hd₀
              cases hd₀
              show (s.tree.nodes.insert node { d with data := spliced }).get? node = _
              rw [NodeStore.get?_insert_self]
            · intro m hm
              show (s.tree.nodes.insert node { d with data := spliced }).get? m = _
              rw [NodeStore.get?_insert_ne _ (fun he => hm he.symm)]
              rfl
          · rw [← Except.ok.inj h]
            show (s.ranges.map _).length = _
            exact List.length_map ..
          · intro i r r' hr hr'
            rw [← Except.ok.inj h] at hr'
            rw [List.getElem?_map, hr] at hr'
            simp only [Option.map_some, Option.some.injEq] at hr'
            rw [← hr']
            exact ⟨dataAdjusted_replaceDataAdjustBP .., dataAdjusted_replaceDataAdjustBP ..⟩
          · rw [← Except.ok.inj h]
          · rw [← Except.ok.inj h]
          · rw [← Except.ok.inj h]
          · rw [← Except.ok.inj h]
            show (queueCharacterDataRecord s node d.data).registrations = _
            unfold queueCharacterDataRecord
            exact queueMutationRecord_registrations ..
          · rw [← Except.ok.inj h]
            show (queueCharacterDataRecord s node d.data).iterators = _
            unfold queueCharacterDataRecord
            exact queueMutationRecord_iterators ..
          · rw [← Except.ok.inj h]
            exact (untouched_queueCharacterDataRecord s node d.data).trans ⟨rfl, rfl, rfl⟩

end Dom.Spec
