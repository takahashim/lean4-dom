import Dom.Spec.ReplaceDataSound
import Dom.Spec.ObsEq

/-!
# `replace data` の一意性と完全性（§4.10）

`Dom/Spec/ReplaceDataSound.lean` は soundness（実行関数の結果が関係を満たすこと）だけで、
逆向きが無かった。ここで

* **一意性**（`replaceDataSpec_deterministic`）：関係を満たす状態の観測は一つに決まる
* **完全性**（`replaceData_complete`）：関係を満たす状態があるなら実行関数は成功し、
  その観測は関係が決めたものと等しい

を入れる。`remove` / `adopt` / `insert` と同じ水準になる。

段ごとの一意性はどれも「関係が関数の graph である」ことに帰着する。
splice は `spliceData?` が、boundary point の調整は step 8-11 の場合分けが、
record は `records_map_congr` が与える。
-/

namespace Dom.Spec

open Dom

/-! ## step 3：切り詰めた count -/

theorem clampedCount_unique {length offset count c₁ c₂ : Nat}
    (h₁ : ClampedCount length offset count c₁) (h₂ : ClampedCount length offset count c₂) :
    c₁ = c₂ := by
  rcases h₁ with ⟨hlt₁, rfl⟩ | ⟨hge₁, rfl⟩ <;> rcases h₂ with ⟨hlt₂, rfl⟩ | ⟨hge₂, rfl⟩
  · rfl
  · exact absurd hlt₁ hge₂
  · exact absurd hlt₂ hge₁
  · rfl

/-! ## step 5-7：splice -/

/--
**scalar 境界で切れる分け方があるなら、`spliceData?` はそれを返す。**

`DataSpliced` は「そう切れる」という存在の形で書いてあるので、
実行関数の成功をここから取り出す。`Utf16.splitAt?_of_split` がその芯である。
-/
theorem spliceData?_of_dataSpliced {old data new : String} {offset count : Nat}
    (h : DataSpliced old offset count data new) :
    spliceData? old offset count data = some new := by
  obtain ⟨pre, mid, post, hsplit, hpre, hmid, hnew⟩ := h
  unfold spliceData?
  rw [show old.toList = pre ++ (mid ++ post) from by rw [hsplit]; simp]
  rw [← hpre, Utf16.splitAt?_of_split pre (mid ++ post)]
  simp only []
  rw [← hmid, Utf16.splitAt?_of_split mid post]
  simp only []
  rw [← hnew, String.ofList_toList]

/-- したがって splice の結果は一つに決まる。 -/
theorem dataSpliced_unique {old data new₁ new₂ : String} {offset count : Nat}
    (h₁ : DataSpliced old offset count data new₁)
    (h₂ : DataSpliced old offset count data new₂) : new₁ = new₂ :=
  Option.some.inj ((spliceData?_of_dataSpliced h₁).symm.trans (spliceData?_of_dataSpliced h₂))

/-! ## step 5-7：木の効果 -/

/-- `DataReplaced` は `get?` を決める。 -/
theorem dataReplaced_unique {t t₁ t₂ : Tree} {node : NodeId} {new : String} {d : NodeData}
    (hd : t.get? node = some d)
    (h₁ : DataReplaced t t₁ node new) (h₂ : DataReplaced t t₂ node new) :
    ∀ m, t₂.get? m = t₁.get? m := by
  intro m
  by_cases hm : m = node
  · subst hm
    rw [h₁.changed d hd, h₂.changed d hd]
  · rw [h₁.others m hm, h₂.others m hm]

/-! ## step 8-11：boundary point -/

/-- step 8-11 の四つの枝は互いに排他なので、調整後の boundary point は一つに決まる。 -/
theorem dataAdjusted_unique {node : NodeId} {offset count newLen : Nat}
    {bp b₁ b₂ : BoundaryPoint}
    (h₁ : DataAdjusted node offset count newLen bp b₁)
    (h₂ : DataAdjusted node offset count newLen bp b₂) : b₁ = b₂ := by
  unfold DataAdjusted at h₁ h₂
  rcases h₁ with ⟨hn₁, rfl⟩ | ⟨hn₁, hlo₁, hhi₁, rfl⟩ | ⟨hn₁, hgt₁, rfl⟩ | ⟨hn₁, hna₁, hnb₁, rfl⟩ <;>
    rcases h₂ with ⟨hn₂, rfl⟩ | ⟨hn₂, hlo₂, hhi₂, rfl⟩ | ⟨hn₂, hgt₂, rfl⟩ |
      ⟨hn₂, hna₂, hnb₂, rfl⟩ <;>
    simp_all <;> omega

/-! ## step 4：record -/

/-- **characterData の record を積む段は観測を一つに決める。** -/
theorem characterDataRecordQueued_unique {s s₁ s₂ : DOMState} {target : NodeId}
    {oldValue : String}
    (h₁ : CharacterDataRecordQueued s s₁ target oldValue)
    (h₂ : CharacterDataRecordQueued s s₂ target oldValue) :
    (∀ mo : Nat, (s₁.observers[mo]?).map (·.records) = (s₂.observers[mo]?).map (·.records)) ∧
      (∀ mo : Nat, mo ∈ s₁.pendingObservers ↔ mo ∈ s₂.pendingObservers) ∧
      s₁.microtaskQueued = s₂.microtaskQueued := by
  obtain ⟨hl₁, hr₁, hin₁, hkeep₁, hout₁, hm₁⟩ := h₁
  obtain ⟨hl₂, hr₂, hin₂, hkeep₂, hout₂, hm₂⟩ := h₂
  refine ⟨records_map_congr hl₁ hl₂ (fun mo o oa ho hoa ob hob => ?_), ?_, by rw [hm₁, hm₂]⟩
  · by_cases hint : InterestedInCharacterData s mo target
    · by_cases hold : CharacterDataOldValueWanted s mo target
      · rw [(hr₁ mo o oa ho hoa).1 hint hold, (hr₂ mo o ob ho hob).1 hint hold]
      · rw [(hr₁ mo o oa ho hoa).2.1 hint hold, (hr₂ mo o ob ho hob).2.1 hint hold]
    · rw [(hr₁ mo o oa ho hoa).2.2 hint, (hr₂ mo o ob ho hob).2.2 hint]
  · intro mo
    constructor
    · intro hm
      rcases hout₁ mo hm with hold | hint
      · exact hkeep₂ mo hold
      · exact hin₂ mo hint
    · intro hm
      rcases hout₂ mo hm with hold | hint
      · exact hkeep₁ mo hold
      · exact hin₁ mo hint

/-! ## 全体 -/

/--
**`ReplaceDataSpec` は観測を一つに決める。**

木は `get?` で、range は index ごとに、record は観測できる queue の像で一致する。
`iterators` と `registrations` は関係がそのまま「変わらない」と言っている。
-/
theorem replaceDataSpec_deterministic {s o₁ o₂ : DOMState} {node : NodeId}
    {offset count : Nat} {data : String}
    (h₁ : ReplaceDataSpec s node offset count data o₁)
    (h₂ : ReplaceDataSpec s node offset count data o₂) : ObsEq o₁ o₂ := by
  obtain ⟨d₁, c₁, new₁, sa, hd₁, -, -, hcc₁, hds₁, hcr₁, hdr₁, hlen₁, hadj₁,
    hob₁, hpe₁, hmt₁, hreg₁, hit₁, hun₁⟩ := h₁
  obtain ⟨d₂, c₂, new₂, sb, hd₂, -, -, hcc₂, hds₂, hcr₂, hdr₂, hlen₂, hadj₂,
    hob₂, hpe₂, hmt₂, hreg₂, hit₂, hun₂⟩ := h₂
  have hde : d₂ = d₁ := Option.some.inj (by rw [← hd₁, ← hd₂])
  subst hde
  have hce : c₂ = c₁ := clampedCount_unique hcc₂ hcc₁
  subst hce
  have hne : new₂ = new₁ := dataSpliced_unique hds₂ hds₁
  subst hne
  obtain ⟨hrecu, hpendu, hmtu⟩ := characterDataRecordQueued_unique hcr₁ hcr₂
  refine ⟨dataReplaced_unique hd₁ hdr₁ hdr₂, ?_, by rw [hit₂, hit₁], ?_, ?_, ?_, ?_,
    hun₂.walkers.trans hun₁.walkers.symm,
    hun₂.listeners.trans hun₁.listeners.symm,
    hun₂.detachedAttrs.trans hun₁.detachedAttrs.symm⟩
  · -- range は index ごとに決まる
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
  · intro r; rw [hreg₂, hreg₁]
  · intro mo; rw [hob₂, hob₁]; exact (hrecu mo).symm
  · intro mo; rw [hpe₂, hpe₁]; exact (hpendu mo).symm
  · rw [hmt₂, hmt₁, hmtu]

/-- **`replaceData` は関係を満たす状態があるなら成功する。** -/
theorem replaceData_isOk_of_spec {s s' : DOMState} {node : NodeId} {offset count : Nat}
    {data : String} (h : ReplaceDataSpec s node offset count data s') :
    ∃ out, replaceData s node offset count data = .ok out := by
  obtain ⟨d, c, new, -, hd, hk, hle, hcc, hds, -, -, -, -, -, -, -, -, -⟩ := h
  unfold replaceData
  simp only [hd]
  rw [if_neg (by simp [hk])]
  rw [if_neg (by simp; omega)]
  have hcc' : adjustedCount d.length offset count = c := by
    unfold adjustedCount
    rcases hcc with ⟨hlt, rfl⟩ | ⟨hge, rfl⟩
    · rw [if_pos (by omega)]
    · rw [if_neg (by omega)]
  rw [show spliceData? d.data offset (adjustedCount d.length offset count) data = some new from by
    rw [hcc']; exact spliceData?_of_dataSpliced hds]
  exact ⟨_, rfl⟩

/--
**`replaceData` の完全性。**

関係を満たす状態があるなら実行関数は成功し、その観測は関係が決めたものと等しい。
成功することは `replaceData_isOk_of_spec`、観測が等しいことは soundness と
`replaceDataSpec_deterministic` を繋いだものである。
-/
theorem replaceData_complete {s s' : DOMState} {node : NodeId} {offset count : Nat}
    {data : String} (hwf : WellFormed s.tree)
    (h : ReplaceDataSpec s node offset count data s') :
    ∃ out, replaceData s node offset count data = .ok out ∧ ObsEq s' out := by
  obtain ⟨out, hok⟩ := replaceData_isOk_of_spec h
  exact ⟨out, hok, replaceDataSpec_deterministic h (replaceData_sound hwf hok)⟩

end Dom.Spec
