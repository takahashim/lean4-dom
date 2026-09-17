import Dom.Properties.InsertOk
import Dom.Properties.Contract

/-!
# 契約：`insertBefore` と `appendChild` の成功条件

`Dom/Properties/Contract.lean` の success に当たる部分のうち挿入側である。
`Dom/Properties/InsertOk.lean` の `insert_isOk_of_validity`（validity を通れば
`insert` は落ちない）と、`preInsert` の step 1 についての interface を繋ぐ。

`Dom/Properties/Contract.lean` に置かないのは import の向きの都合である
（`adopt_isOk` が `remove_succeeds_iff` を使うので `CloneOk` が `Contract` を見る）。
-/

namespace Dom

/--
**`preInsert` が成功するのは、step 1 の validity を通るときちょうどである。**

つまり `insertBefore` が返す例外は **pre-insertion validity のものだけ**である。
step 4 の `insert` は落ちない（`insert_isOk_of_validity`）。

`child` が `node` 自身の場合は除いてある。そのとき step 2-3 は reference child を
`node` の次の兄弟に取り替えるので、validity を取り替えた側で読み直す必要があり、
`ensurePreInsertionValidity_child_congr` の前提（element と doctype の検査が移ること）を
別に示さなければならない。`appendChild`（`child = none`）はこの場合に当たらない。
-/
theorem preInsert_succeeds_iff {s : DOMState} (hwf : WellFormed s.tree)
    {node parent : NodeId} {child : Option NodeId} (hcn : child ≠ some node) :
    (∃ s', preInsert s node parent child = .ok s') ↔
      ensurePreInsertionValidity s.tree node parent child [] = .ok () := by
  constructor
  · rintro ⟨s', h⟩
    exact (preInsert_cases h).1
  · intro hv
    rw [preInsert_of_validity hv, preInsertReferenceChild_eq, if_neg hcn]
    exact insert_isOk_of_validity hwf hv (fun c hc he => hcn (by rw [hc, he]))

/-- **`preInsert` が失敗するのは validity で落ちるときちょうどで、例外はそれである。** -/
theorem preInsert_error_iff {s : DOMState} (hwf : WellFormed s.tree)
    {node parent : NodeId} {child : Option NodeId} {e : DOMException} (hcn : child ≠ some node) :
    preInsert s node parent child = .error e ↔
      ensurePreInsertionValidity s.tree node parent child [] = .error e := by
  constructor
  · intro h
    cases hx : ensurePreInsertionValidity s.tree node parent child [] with
    | error e' =>
      rw [preInsert_of_validity_error hx] at h
      have he : e' = e := Except.error.inj h
      subst he
      rfl
    | ok u =>
      exfalso
      obtain ⟨s', hs'⟩ := (preInsert_succeeds_iff hwf hcn).mpr (by cases u; exact hx)
      rw [hs'] at h
      simp at h
  · exact preInsert_of_validity_error

/-- **`appendChild` の契約。** `child` が無いので上の除外に当たらない。 -/
theorem append_succeeds_iff {s : DOMState} (hwf : WellFormed s.tree) {node parent : NodeId} :
    (∃ s', append s node parent = .ok s') ↔
      ensurePreInsertionValidity s.tree node parent none [] = .ok () := by
  rw [append]
  exact preInsert_succeeds_iff hwf (by simp)


end Dom
