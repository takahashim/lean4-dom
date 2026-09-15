import Dom.Spec.Record
import Dom.Properties.Record

/-!
# record を積む step は関係意味論を満たす

`queueTreeMutationRecord` が `TreeRecordQueued` を満たすことを示す。
`remove` の step 21 と `insert` の step 4.2 / 9 が共有する。
-/

namespace Dom.Spec

open Dom

/-- `suppressObservers` が true なら、record の step は何もしない。 -/
theorem treeRecordQueued_of_suppress (s : DOMState) (target : NodeId)
    (added removed : List NodeId) (prev next : Option NodeId) :
    TreeRecordQueued s s target added removed prev next true := by
  unfold TreeRecordQueued
  rw [if_pos rfl]
  exact ⟨rfl, fun mo o o' ho ho' => by rw [ho] at ho'; cases ho'; rfl,
    fun _ => Iff.rfl, rfl⟩

/-- 一つの observer が受け取る record は、interested なら一つ、そうでなければ無い。 -/
theorem records_after_tree_queue {s : DOMState} {rec : MutationRecord} {mo : Nat}
    {o o' : ObserverState} (hov : rec.oldValue = none)
    (ho : s.observers[mo]? = some o)
    (ho' : (queueMutationRecord s rec none).observers[mo]? = some o') :
    (mo ∈ ((interestedObservers s rec none).map (·.1)) → o'.records = o.records ++ [rec]) ∧
      (mo ∉ ((interestedObservers s rec none).map (·.1)) → o'.records = o.records) := by
  rw [observers_queueMutationRecord] at ho'
  have hfold := records_foldl_enqueue rec _ s.observers mo o o' ho ho'
  constructor
  · intro hmem
    obtain ⟨q, hq', hq1⟩ := List.mem_map.mp hmem
    have hq2 : q.2 = none := oldValue_none_of_childList s rec q hq'
    have hqe : q = (mo, none) := by
      cases q with
      | mk a bb => simp only at hq1 hq2; rw [hq1, hq2]
    rw [hfold, filterMap_eq_single
      (fun r : Nat × Option String => ({ rec with oldValue := r.2 } : MutationRecord)) mo none _
      (nodup_interestedObservers s rec none) (by rw [← hqe]; exact hq')]
    have : ({ rec with oldValue := (none : Option String) } : MutationRecord) = rec := by rw [← hov]
    rw [this]
  · intro hmem
    rw [hfold, filterMap_eq_nil_of_not_mem
      (fun r : Nat × Option String => ({ rec with oldValue := r.2 } : MutationRecord)) mo _ hmem]
    simp

/-- interested observer の集まりは、関係の側の条件と一致する。 -/
theorem mem_interested_iff_childList {s : DOMState} (hwf : WellFormed s.tree) {rec : MutationRecord}
    (hty : rec.type = RecordType.childList) (hna : rec.attributeName = none)
    (hns : rec.attributeNamespace = none) (mo : Nat) :
    mo ∈ ((interestedObservers s rec none).map (·.1)) ↔ InterestedInChildList s mo rec.target := by
  rw [mem_interestedObservers]
  have hcond : ∀ r : Registration,
      Registration.interestedIn r rec.target rec.type rec.attributeName rec.attributeNamespace
        = ((r.node == rec.target || r.subtree) && r.childList) := by
    intro r
    rw [hty, hna, hns]
    rfl
  constructor
  · rintro ⟨r, hrmem, hnode, hc, rfl⟩
    rw [hcond] at hc
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
    refine ⟨r, hrmem, rfl, hc.2, ?_, hc.1⟩
    rcases List.mem_cons.mp hnode with he | hm
    · exact Or.inl he
    · exact Or.inr ((mem_ancestors_iff hwf rec.target r.node).mp hm)
  · rintro ⟨r, hrmem, rfl, hchild, hanc, hsub⟩
    refine ⟨r, hrmem, ?_, ?_, rfl⟩
    · rcases hanc with he | ha
      · exact List.mem_cons.mpr (Or.inl he)
      · exact List.mem_cons_of_mem _ ((mem_ancestors_iff hwf rec.target r.node).mpr ha)
    · rw [hcond]
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
      exact ⟨hsub, hchild⟩

/-- **`queueTreeMutationRecord` は `TreeRecordQueued` を満たす。** -/
theorem treeRecordQueued_of_queue (s : DOMState) (hwf : WellFormed s.tree) (target : NodeId)
    (added removed : List NodeId) (prev next : Option NodeId)
    (hne : ¬(added.isEmpty && removed.isEmpty)) :
    TreeRecordQueued s (queueTreeMutationRecord s target added removed prev next)
      target added removed prev next false := by
  have hq : queueTreeMutationRecord s target added removed prev next =
      queueMutationRecord s
        { type := .childList, target := target, addedNodes := added, removedNodes := removed,
          previousSibling := prev, nextSibling := next } none := by
    unfold queueTreeMutationRecord
    rw [if_neg (by simpa using hne)]
  have hbridge := fun mo => mem_interested_iff_childList (s := s) hwf
    (rec := ({ type := .childList, target := target, addedNodes := added, removedNodes := removed,
               previousSibling := prev, nextSibling := next } : MutationRecord)) rfl rfl rfl mo
  unfold TreeRecordQueued
  rw [if_neg (by simp), hq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact queueMutationRecord_observers_length ..
  · intro mo o o' ho ho'
    have hr := records_after_tree_queue (mo := mo) rfl ho ho'
    exact ⟨fun hint => hr.1 ((hbridge mo).mpr hint),
      fun hint => hr.2 (fun hm => hint ((hbridge mo).mp hm))⟩
  · intro mo hint
    exact (mem_pendingObservers_queueMutationRecord _ _ _ mo).mpr (Or.inr ((hbridge mo).mpr hint))
  · intro mo hmo
    exact (mem_pendingObservers_queueMutationRecord _ _ _ mo).mpr (Or.inl hmo)
  · intro mo hmo
    rcases (mem_pendingObservers_queueMutationRecord _ _ _ mo).mp hmo with hm | hm
    · exact Or.inl hm
    · exact Or.inr ((hbridge mo).mp hm)
  · exact microtaskQueued_queueMutationRecord ..

/-! ## characterData の record -/

/-- interested な observer の集まりは、関係の側の条件と一致する（characterData）。 -/
theorem mem_interested_iff_characterData {s : DOMState} (hwf : WellFormed s.tree)
    {rec : MutationRecord} (hty : rec.type = RecordType.characterData) (ov : Option String)
    (mo : Nat) :
    mo ∈ ((interestedObservers s rec ov).map (·.1)) ↔
      InterestedInCharacterData s mo rec.target := by
  rw [mem_interestedObservers]
  have hcond : ∀ r : Registration,
      Registration.interestedIn r rec.target rec.type rec.attributeName rec.attributeNamespace
        = ((r.node == rec.target || r.subtree) && r.characterData) := by
    intro r
    rw [hty]
    rfl
  constructor
  · rintro ⟨r, hrmem, hnode, hc, rfl⟩
    rw [hcond] at hc
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
    refine ⟨r, hrmem, rfl, hc.2, ?_, hc.1⟩
    rcases List.mem_cons.mp hnode with he | hm
    · exact Or.inl he
    · exact Or.inr ((mem_ancestors_iff hwf rec.target r.node).mp hm)
  · rintro ⟨r, hrmem, rfl, hcd, hanc, hsub⟩
    refine ⟨r, hrmem, ?_, ?_, rfl⟩
    · rcases hanc with he | ha
      · exact List.mem_cons.mpr (Or.inl he)
      · exact List.mem_cons_of_mem _ ((mem_ancestors_iff hwf rec.target r.node).mpr ha)
    · rw [hcond]
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
      exact ⟨hsub, hcd⟩

/-- oldValue が載る observer も、関係の側の条件と一致する。 -/
theorem mem_pair_iff_characterDataOldValue {s : DOMState} (hwf : WellFormed s.tree)
    {rec : MutationRecord} (hty : rec.type = RecordType.characterData) (old : String) (mo : Nat) :
    ((mo, some old) ∈ interestedObservers s rec (some old)) ↔
      CharacterDataOldValueWanted s mo rec.target := by
  rw [mem_pair_interestedObservers s rec (some old) (by simp) mo]
  have hcond : ∀ r : Registration,
      Registration.interestedIn r rec.target rec.type rec.attributeName rec.attributeNamespace
        = ((r.node == rec.target || r.subtree) && r.characterData) := by
    intro r
    rw [hty]
    rfl
  have hflag : ∀ r : Registration,
      (((rec.type == RecordType.characterData && r.characterDataOldValue)
        || (rec.type == RecordType.attributes && r.attributeOldValue)) = true) ↔
        r.characterDataOldValue = true := by
    intro r
    rw [hty]
    simp
  constructor
  · rintro ⟨r, hrmem, hnode, hc, hf, rfl⟩
    rw [hcond] at hc
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
    refine ⟨r, hrmem, rfl, hc.2, (hflag r).mp hf, ?_, hc.1⟩
    rcases List.mem_cons.mp hnode with he | hm
    · exact Or.inl he
    · exact Or.inr ((mem_ancestors_iff hwf rec.target r.node).mp hm)
  · rintro ⟨r, hrmem, rfl, hcd, hov, hanc, hsub⟩
    refine ⟨r, hrmem, ?_, ?_, (hflag r).mpr hov, rfl⟩
    · rcases hanc with he | ha
      · exact List.mem_cons.mpr (Or.inl he)
      · exact List.mem_cons_of_mem _ ((mem_ancestors_iff hwf rec.target r.node).mpr ha)
    · rw [hcond]
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
      exact ⟨hsub, hcd⟩

/-- **`queueCharacterDataRecord` は `CharacterDataRecordQueued` を満たす。** -/
theorem characterDataRecordQueued_of_queue (s : DOMState) (hwf : WellFormed s.tree)
    (target : NodeId) (old : String) :
    CharacterDataRecordQueued s (queueCharacterDataRecord s target old) target old := by
  have hmem := fun mo => mem_interested_iff_characterData (s := s) hwf
    (rec := ({ type := .characterData, target := target } : MutationRecord)) rfl (some old) mo
  have hpair := fun mo => mem_pair_iff_characterDataOldValue (s := s) hwf
    (rec := ({ type := .characterData, target := target } : MutationRecord)) rfl old mo
  unfold queueCharacterDataRecord
  refine ⟨queueMutationRecord_observers_length .., ?_, ?_, ?_, ?_,
    microtaskQueued_queueMutationRecord ..⟩
  · intro mo o o' ho ho'
    rw [observers_queueMutationRecord] at ho'
    have hfold := records_foldl_enqueue
      ({ type := .characterData, target := target } : MutationRecord) _ s.observers mo o o' ho ho'
    refine ⟨?_, ?_, ?_⟩
    · intro hint hwant
      have hq : (mo, some old) ∈ interestedObservers s
          ({ type := .characterData, target := target } : MutationRecord) (some old) :=
        (hpair mo).mpr hwant
      rw [hfold, filterMap_eq_single
        (fun r : Nat × Option String =>
          ({ type := .characterData, target := target, oldValue := r.2 } : MutationRecord))
        mo (some old) _ (nodup_interestedObservers ..) hq]
    · intro hint hwant
      -- interested だが flag が無いなら、値は `none` である。
      obtain ⟨q, hqmem, hq1⟩ := List.mem_map.mp ((hmem mo).mpr hint)
      have hval : q.2 = some old ∨ q.2 = none :=
        value_mem_interestedObservers s _ (some old) q hqmem
      have hqnone : q.2 = none := by
        rcases hval with hv | hv
        · exfalso
          refine hwant ((hpair mo).mp ?_)
          have : q = (mo, some old) := by
            cases q with
            | mk a bb => simp only at hq1 hv; rw [hq1, hv]
          rw [← this]
          exact hqmem
        · exact hv
      have hq : (mo, none) ∈ interestedObservers s
          ({ type := .characterData, target := target } : MutationRecord) (some old) := by
        have : q = (mo, none) := by
          cases q with
          | mk a bb => simp only at hq1 hqnone; rw [hq1, hqnone]
        rw [← this]
        exact hqmem
      rw [hfold, filterMap_eq_single
        (fun r : Nat × Option String =>
          ({ type := .characterData, target := target, oldValue := r.2 } : MutationRecord))
        mo none _ (nodup_interestedObservers ..) hq]
    · intro hint
      rw [hfold, filterMap_eq_nil_of_not_mem
        (fun r : Nat × Option String =>
          ({ type := .characterData, target := target, oldValue := r.2 } : MutationRecord))
        mo _ (fun hm => hint ((hmem mo).mp hm))]
      simp
  · intro mo hint
    exact (mem_pendingObservers_queueMutationRecord _ _ _ mo).mpr (Or.inr ((hmem mo).mpr hint))
  · intro mo hmo
    exact (mem_pendingObservers_queueMutationRecord _ _ _ mo).mpr (Or.inl hmo)
  · intro mo hmo
    rcases (mem_pendingObservers_queueMutationRecord _ _ _ mo).mp hmo with hm | hm
    · exact Or.inl hm
    · exact Or.inr ((hmem mo).mp hm)

end Dom.Spec
