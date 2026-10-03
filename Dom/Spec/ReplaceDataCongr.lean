import Dom.Spec.ReplaceDataDeterministic
import Dom.Spec.ObsEq

/-!
# `replace data` の congruence

`replaceDataSpec_deterministic` は入力の状態が同じときの一意性である。
normalize のように replace data を他の段と繋ぐときは、途中の状態が観測としてしか
一致しないので、「入力の観測が等しければ出力の観測も等しい」（`_congr`）が要る。
-/

namespace Dom.Spec

open Dom

variable {s sb : DOMState}

/-- record を積むかどうかは registration の所属と祖先関係だけで決まる。 -/
theorem interestedInCharacterData_congr (h : ObsEq s sb) (mo : Nat) (target : NodeId) :
    InterestedInCharacterData sb mo target ↔ InterestedInCharacterData s mo target := by
  unfold InterestedInCharacterData
  constructor
  · rintro ⟨r, hr, h1, h2, h3, h4⟩
    exact ⟨r, (h.registrations r).mp hr, h1, h2, h.tree.inclusiveAncestor_iff.mp h3, h4⟩
  · rintro ⟨r, hr, h1, h2, h3, h4⟩
    exact ⟨r, (h.registrations r).mpr hr, h1, h2, h.tree.inclusiveAncestor_iff.mpr h3, h4⟩

theorem characterDataOldValueWanted_congr (h : ObsEq s sb) (mo : Nat) (target : NodeId) :
    CharacterDataOldValueWanted sb mo target ↔ CharacterDataOldValueWanted s mo target := by
  unfold CharacterDataOldValueWanted
  constructor
  · rintro ⟨r, hr, h1, h2, h3, h4, h5⟩
    exact ⟨r, (h.registrations r).mp hr, h1, h2, h3, h.tree.inclusiveAncestor_iff.mp h4, h5⟩
  · rintro ⟨r, hr, h1, h2, h3, h4, h5⟩
    exact ⟨r, (h.registrations r).mpr hr, h1, h2, h3, h.tree.inclusiveAncestor_iff.mpr h4, h5⟩

/-- `records_map_congr` の、入力が観測として等しい二つの状態である版。 -/
theorem records_map_congr_obs (h : ObsEq s sb) {sa sb' : DOMState}
    (hla : sa.observers.length = s.observers.length)
    (hlb : sb'.observers.length = sb.observers.length)
    (hrec : ∀ (mo : Nat) (o oa ob ob' : ObserverState), s.observers[mo]? = some o →
      sa.observers[mo]? = some oa → sb.observers[mo]? = some ob →
      sb'.observers[mo]? = some ob' → oa.records = ob'.records) :
    ∀ mo : Nat, (sa.observers[mo]?).map (·.records) = (sb'.observers[mo]?).map (·.records) := by
  refine records_map_congr hla (by rw [hlb, h.observers_length]) ?_
  intro mo o oa ho hoa ob' hob'
  obtain ⟨ob, hob, -⟩ := h.exists_observer ho
  exact hrec mo o oa ob ob' ho hoa hob hob'

/-- **characterData の record を積む段の congruence。** -/
theorem characterDataRecordQueued_congr (h : ObsEq s sb) {s₁ s₂ : DOMState} {target : NodeId}
    {oldValue : String}
    (h₁ : CharacterDataRecordQueued s s₁ target oldValue)
    (h₂ : CharacterDataRecordQueued sb s₂ target oldValue) :
    (∀ mo : Nat, (s₁.observers[mo]?).map (·.records) = (s₂.observers[mo]?).map (·.records)) ∧
      (∀ mo : Nat, mo ∈ s₁.pendingObservers ↔ mo ∈ s₂.pendingObservers) ∧
      s₁.microtaskQueued = s₂.microtaskQueued := by
  obtain ⟨hl₁, hr₁, hin₁, hkeep₁, hout₁, hm₁⟩ := h₁
  obtain ⟨hl₂, hr₂, hin₂, hkeep₂, hout₂, hm₂⟩ := h₂
  have hint := fun mo => interestedInCharacterData_congr h mo target
  have hold := fun mo => characterDataOldValueWanted_congr h mo target
  refine ⟨records_map_congr_obs h hl₁ hl₂ (fun mo o oa ob ob' ho hoa hob hob' => ?_), ?_,
    by rw [hm₁, hm₂]⟩
  · have hre : ob.records = o.records := h.records_of ho hob
    by_cases hi : InterestedInCharacterData s mo target
    · by_cases hw : CharacterDataOldValueWanted s mo target
      · rw [(hr₁ mo o oa ho hoa).1 hi hw,
          (hr₂ mo ob ob' hob hob').1 ((hint mo).mpr hi) ((hold mo).mpr hw), hre]
      · rw [(hr₁ mo o oa ho hoa).2.1 hi hw,
          (hr₂ mo ob ob' hob hob').2.1 ((hint mo).mpr hi) (fun hw' => hw ((hold mo).mp hw')), hre]
    · rw [(hr₁ mo o oa ho hoa).2.2 hi,
        (hr₂ mo ob ob' hob hob').2.2 (fun hi' => hi ((hint mo).mp hi')), hre]
  · intro mo
    constructor
    · intro hm
      rcases hout₁ mo hm with hp | hi
      · exact hkeep₂ mo ((h.pendingObservers mo).mpr hp)
      · exact hin₂ mo ((hint mo).mpr hi)
    · intro hm
      rcases hout₂ mo hm with hp | hi
      · exact hkeep₁ mo ((h.pendingObservers mo).mp hp)
      · exact hin₁ mo ((hint mo).mp hi)

/--
**`ReplaceDataSpec` の congruence。**

`replaceDataSpec_deterministic` と同じ組み立てで、入力側の一致を `ObsEq` から取る。
-/
theorem replaceDataSpec_congr (h : ObsEq s sb) {o₁ o₂ : DOMState} {node : NodeId}
    {offset count : Nat} {data : String}
    (h₁ : ReplaceDataSpec s node offset count data o₁)
    (h₂ : ReplaceDataSpec sb node offset count data o₂) : ObsEq o₁ o₂ := by
  obtain ⟨d₁, c₁, new₁, sa, hd₁, -, -, hcc₁, hds₁, hcr₁, hdr₁, hlen₁, hadj₁,
    hob₁, hpe₁, hmt₁, hreg₁, hit₁, hun₁⟩ := h₁
  obtain ⟨d₂, c₂, new₂, sc, hd₂, -, -, hcc₂, hds₂, hcr₂, hdr₂, hlen₂, hadj₂,
    hob₂, hpe₂, hmt₂, hreg₂, hit₂, hun₂⟩ := h₂
  have hde : d₂ = d₁ := Option.some.inj (by rw [← hd₁, ← h.tree node, ← hd₂])
  subst hde
  have hce : c₂ = c₁ := clampedCount_unique hcc₂ hcc₁
  subst hce
  have hne : new₂ = new₁ := dataSpliced_unique hds₂ hds₁
  subst hne
  obtain ⟨hrecu, hpendu, hmtu⟩ := characterDataRecordQueued_congr h hcr₁ hcr₂
  have hsr : sb.ranges = s.ranges := h.ranges
  refine ⟨?_, ?_, by rw [hit₂, hit₁, h.iterators], ?_, ?_, ?_, ?_,
    by rw [hun₂.walkers, hun₁.walkers, h.walkers],
    by rw [hun₂.listeners, hun₁.listeners, h.listeners],
    by rw [hun₂.detachedAttrs, hun₁.detachedAttrs, h.detachedAttrs]⟩
  · intro m
    by_cases hm : m = node
    · subst hm
      rw [hdr₁.changed d₂ hd₁, hdr₂.changed d₂ hd₂]
    · rw [hdr₁.others m hm, hdr₂.others m hm, h.tree m]
  · -- range は index ごとに決まる
    rw [hsr] at hlen₂ hadj₂
    refine List.ext_getElem (by rw [hlen₂, hlen₁]) (fun i hi₂ hi₁ => ?_)
    have hs : i < s.ranges.length := by omega
    obtain ⟨r, hr⟩ : ∃ r, s.ranges[i]? = some r := ⟨s.ranges[i], by simp [hs]⟩
    have e₁ := hadj₁ i r o₁.ranges[i] hr (by simp [hi₁])
    have e₂ := hadj₂ i r o₂.ranges[i] hr (by simp [hi₂])
    have hst := dataAdjusted_unique e₂.1 e₁.1
    have hen := dataAdjusted_unique e₂.2 e₁.2
    show o₂.ranges[i] = o₁.ranges[i]
    rw [show o₂.ranges[i] = ⟨(o₂.ranges[i]).start, (o₂.ranges[i]).«end»⟩ from rfl,
      show o₁.ranges[i] = ⟨(o₁.ranges[i]).start, (o₁.ranges[i]).«end»⟩ from rfl, hst, hen]
  · intro r; rw [hreg₂, hreg₁]; exact h.registrations r
  · intro mo; rw [hob₂, hob₁]; exact (hrecu mo).symm
  · intro mo; rw [hpe₂, hpe₁]; exact (hpendu mo).symm
  · rw [hmt₂, hmt₁, hmtu]

end Dom.Spec
