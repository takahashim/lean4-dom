import Dom.Spec.Result
import Dom.Spec.ReplaceDataSound
import Dom.Spec.ReplaceDataDeterministic

/-!
# replace data と `CharacterData` の method の、結果まで含めた関係

`ReplaceDataSpec`（`Dom/Spec/ReplaceData.lean`）は成功したときの状態遷移だけを述べる。
ここでは失敗する場合も含めた関係 `ReplaceDataResult` を置き、
`appendData` / `insertData` / `deleteData` / `setData` を、それぞれ仕様が書くとおり
replace data への委譲として結果まで結ぶ。

失敗は四通りある。仕様の algorithm 自身が持つのは step 2 の `IndexSizeError` だけで、
残りは model の都合である。

* node が木に無い（`NotFoundError`）。IDL の受け手は必ず存在するので仕様には現れない。
* node が CharacterData でない（`InvalidNodeTypeError`）。`CharacterData` の method からしか
  呼ばれないので仕様には現れない。
* `offset` か `offset + count` が surrogate pair の途中（`__outsideModel__`）。仕様は定義しているが、
  model の文字列（`Char` の列）では表せない。
-/

namespace Dom.Spec

open Dom

/--
**§4.10 replace data の、結果まで含めた関係。**

成功なら `ReplaceDataSpec`。失敗は上の四通りで、どれに当たるかで例外が決まる。
-/
def ReplaceDataResult (s : DOMState) (node : NodeId) (offset count : Nat) (data : String) :
    Except DOMException DOMState → Prop
  | .ok s' => ReplaceDataSpec s node offset count data s'
  | .error e =>
    (s.tree.get? node = none ∧ e = .notFoundError) ∨
    (∃ d, s.tree.get? node = some d ∧ d.kind.isCharacterData = false ∧
      e = .invalidNodeTypeError) ∨
    -- step 1-2
    (∃ d, s.tree.get? node = some d ∧ d.kind.isCharacterData = true ∧ d.length < offset ∧
      e = .indexSizeError) ∨
    -- step 3 の後、step 5-7 の切り出しが surrogate pair を割る
    (∃ d c, s.tree.get? node = some d ∧ d.kind.isCharacterData = true ∧ offset ≤ d.length ∧
      ClampedCount d.length offset count c ∧ (∀ new, ¬ DataSpliced d.data offset c data new) ∧
      e = .outsideModel)

/-- **`replaceData` の結果は、成否によらず関係を満たす。** -/
theorem replaceData_result_sound {s : DOMState} (hwf : WellFormed s.tree) (node : NodeId)
    (offset count : Nat) (data : String) :
    ReplaceDataResult s node offset count data (replaceData s node offset count data) := by
  cases h : replaceData s node offset count data with
  | ok s' => exact replaceData_sound hwf h
  | error e =>
    unfold replaceData at h
    split at h
    · next hn => exact Or.inl ⟨hn, (Except.error.inj h).symm⟩
    · next d hd =>
      split at h
      · next hk =>
        exact Or.inr (Or.inl ⟨d, hd, by simpa using hk, (Except.error.inj h).symm⟩)
      · next hk =>
        have hk' : d.kind.isCharacterData = true := by simpa using hk
        split at h
        · next hlt => exact Or.inr (Or.inr (Or.inl ⟨d, hd, hk', hlt, (Except.error.inj h).symm⟩))
        · next hlt =>
          split at h
          · next hsp =>
            refine Or.inr (Or.inr (Or.inr ⟨d, adjustedCount d.length offset count, hd, hk',
              by omega, clampedCount_adjustedCount _ _ _, ?_, (Except.error.inj h).symm⟩))
            intro new hds
            rw [spliceData?_of_dataSpliced hds] at hsp
            cases hsp
          · simp at h

/-- 関係を満たす結果が成功なら、node は CharacterData で、`offset` は長さ以下で、切り出せる。 -/
theorem replaceDataResult_ok_facts {s s' : DOMState} {node : NodeId} {offset count : Nat}
    {data : String} (h : ReplaceDataResult s node offset count data (.ok s')) :
    ∃ d c new, s.tree.get? node = some d ∧ d.kind.isCharacterData = true ∧ offset ≤ d.length ∧
      ClampedCount d.length offset count c ∧ DataSpliced d.data offset c data new := by
  obtain ⟨d, c, new, -, hd, hk, hle, hcc, hds, -⟩ := h
  exact ⟨d, c, new, hd, hk, hle, hcc, hds⟩

/--
**関係は結果を一つに決める。**

成功するかどうかも、成功したときの観測も、失敗したときの例外も決まる。
-/
theorem replaceData_result_deterministic {s : DOMState} {node : NodeId} {offset count : Nat}
    {data : String} {r₁ r₂ : Except DOMException DOMState}
    (h₁ : ReplaceDataResult s node offset count data r₁)
    (h₂ : ReplaceDataResult s node offset count data r₂) : ResultObsEq r₁ r₂ := by
  -- 失敗の四通りは互いに排他で、成功とも排他である。
  have hok_err : ∀ {s' : DOMState} {e : DOMException},
      ReplaceDataResult s node offset count data (.ok s') →
      ReplaceDataResult s node offset count data (.error e) → False := by
    intro s' e hok herr
    obtain ⟨d, c, new, hd, hk, hle, hcc, hds⟩ := replaceDataResult_ok_facts hok
    rcases herr with ⟨hn, -⟩ | ⟨d', hd', hk', -⟩ | ⟨d', hd', -, hlt, -⟩ |
      ⟨d', c', hd', -, -, hcc', hno, -⟩
    · rw [hn] at hd; cases hd
    · rw [hd] at hd'; cases hd'; rw [hk] at hk'; cases hk'
    · rw [hd] at hd'; cases hd'; omega
    · rw [hd] at hd'; cases hd'
      rw [clampedCount_unique hcc hcc'] at hds
      exact hno new hds
  cases r₁ with
  | ok s₁ =>
    cases r₂ with
    | ok s₂ => exact replaceDataSpec_deterministic h₁ h₂
    | error e₂ => exact (hok_err h₁ h₂).elim
  | error e₁ =>
    cases r₂ with
    | ok s₂ => exact (hok_err h₂ h₁).elim
    | error e₂ =>
      show e₁ = e₂
      rcases h₁ with ⟨hn₁, rfl⟩ | ⟨d₁, hd₁, hk₁, rfl⟩ | ⟨d₁, hd₁, hk₁, hlt₁, rfl⟩ |
        ⟨d₁, c₁, hd₁, hk₁, hle₁, -, -, rfl⟩ <;>
      rcases h₂ with ⟨hn₂, rfl⟩ | ⟨d₂, hd₂, hk₂, rfl⟩ | ⟨d₂, hd₂, hk₂, hlt₂, rfl⟩ |
        ⟨d₂, c₂, hd₂, hk₂, hle₂, -, -, rfl⟩ <;>
      first
        | rfl
        | (exfalso; simp_all; done)
        | (exfalso; simp_all; omega)

/-- **完全性も結果の水準で言える。** -/
theorem replaceData_result_complete {s : DOMState} (hwf : WellFormed s.tree) {node : NodeId}
    {offset count : Nat} {data : String} {r : Except DOMException DOMState}
    (h : ReplaceDataResult s node offset count data r) :
    ResultObsEq r (replaceData s node offset count data) :=
  replaceData_result_deterministic h (replaceData_result_sound hwf node offset count data)

/-! ## `CharacterData` の method

どれも仕様が replace data への委譲として書いている。`appendData` と `setData` は
「this の length」を引数に取るので、node が木に無ければそこで `NotFoundError` になる。
-/

/-- `appendData(data)`：「replace data with this, this's length, 0, and data」。 -/
def AppendDataResult (s : DOMState) (node : NodeId) (data : String) :
    Except DOMException DOMState → Prop
  | r => (s.tree.get? node = none ∧ r = .error .notFoundError) ∨
    (∃ d, s.tree.get? node = some d ∧ ReplaceDataResult s node d.length 0 data r)

/-- `setData`（`data` の setter）：「replace data with this, 0, this's length, and the given value」。 -/
def SetDataResult (s : DOMState) (node : NodeId) (data : String) :
    Except DOMException DOMState → Prop
  | r => (s.tree.get? node = none ∧ r = .error .notFoundError) ∨
    (∃ d, s.tree.get? node = some d ∧ ReplaceDataResult s node 0 d.length data r)

theorem appendData_result_sound {s : DOMState} (hwf : WellFormed s.tree) (node : NodeId)
    (data : String) : AppendDataResult s node data (appendData s node data) := by
  unfold appendData
  split
  · next hn => exact Or.inl ⟨hn, rfl⟩
  · next d hd => exact Or.inr ⟨d, hd, replaceData_result_sound hwf node d.length 0 data⟩

theorem appendData_result_complete {s : DOMState} (hwf : WellFormed s.tree) {node : NodeId}
    {data : String} {r : Except DOMException DOMState} (h : AppendDataResult s node data r) :
    ResultObsEq r (appendData s node data) := by
  unfold appendData
  rcases h with ⟨hn, rfl⟩ | ⟨d, hd, hr⟩
  · rw [hn]; rfl
  · rw [hd]; exact replaceData_result_complete hwf hr

theorem setData_result_sound {s : DOMState} (hwf : WellFormed s.tree) (node : NodeId)
    (data : String) : SetDataResult s node data (setData s node data) := by
  unfold setData
  split
  · next hn => exact Or.inl ⟨hn, rfl⟩
  · next d hd => exact Or.inr ⟨d, hd, replaceData_result_sound hwf node 0 d.length data⟩

theorem setData_result_complete {s : DOMState} (hwf : WellFormed s.tree) {node : NodeId}
    {data : String} {r : Except DOMException DOMState} (h : SetDataResult s node data r) :
    ResultObsEq r (setData s node data) := by
  unfold setData
  rcases h with ⟨hn, rfl⟩ | ⟨d, hd, hr⟩
  · rw [hn]; rfl
  · rw [hd]; exact replaceData_result_complete hwf hr

/-- `insertData(offset, data)`：「replace data with this, offset, 0, and data」。 -/
theorem insertData_result_sound {s : DOMState} (hwf : WellFormed s.tree) (node : NodeId)
    (offset : Nat) (data : String) :
    ReplaceDataResult s node offset 0 data (insertData s node offset data) :=
  replaceData_result_sound hwf node offset 0 data

theorem insertData_result_complete {s : DOMState} (hwf : WellFormed s.tree) {node : NodeId}
    {offset : Nat} {data : String} {r : Except DOMException DOMState}
    (h : ReplaceDataResult s node offset 0 data r) : ResultObsEq r (insertData s node offset data) :=
  replaceData_result_complete hwf h

/-- `deleteData(offset, count)`：「replace data with this, offset, count, and the empty string」。 -/
theorem deleteData_result_sound {s : DOMState} (hwf : WellFormed s.tree) (node : NodeId)
    (offset count : Nat) :
    ReplaceDataResult s node offset count "" (deleteData s node offset count) :=
  replaceData_result_sound hwf node offset count ""

theorem deleteData_result_complete {s : DOMState} (hwf : WellFormed s.tree) {node : NodeId}
    {offset count : Nat} {r : Except DOMException DOMState}
    (h : ReplaceDataResult s node offset count "" r) :
    ResultObsEq r (deleteData s node offset count) :=
  replaceData_result_complete hwf h

end Dom.Spec
