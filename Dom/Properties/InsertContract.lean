import Dom.Properties.InsertOk
import Dom.Properties.Contract
import Dom.Validity.Admissible

/-!
# 契約：`insertBefore` と `appendChild` の成功条件

`Dom/Properties/Contract.lean` の success に当たる部分のうち挿入側である。
`Dom/Properties/InsertOk.lean` の `insert_isOk_of_validity`（validity を通れば
`insert` は落ちない）と、`preInsert` の step 1 についての interface を繋ぐ。

`Dom/Properties/Contract.lean` に置かないのは import の向きの都合である
（`adopt_isOk` が `remove_succeeds_iff` を使うので `CloneOk` が `Contract` を見る）。
-/

namespace Dom

/-- node は自分自身の次の兄弟ではない。children に重複が無いからである。 -/
theorem nextSibling_ne_self {t : Tree} (hwf : WellFormed t) (n : NodeId) :
    nextSibling t n ≠ some n := by
  intro he
  cases hp : parentOf t n with
  | none => rw [nextSibling, hp] at he; simp at he
  | some p =>
    obtain ⟨A, B, hs⟩ := ListUtil.exists_splitAt?_of_mem ((mem_childrenOf_iff hwf n p).mp hp)
    have hL : childrenOf t p = A ++ n :: B := ListUtil.splitAt?_eq_some hs
    rw [nextSibling_of_split hwf hp hL] at he
    have hmem : n ∈ B := by
      cases hb : B with
      | nil => rw [hb] at he; simp at he
      | cons x xs => rw [hb] at he; simp at he; simp [← he]
    have hnd : (childrenOf t p).Nodup := childrenOf_nodup hwf p
    rw [hL] at hnd
    have hnn : n ∉ B := by
      have := (List.nodup_append.mp hnd).2.1
      simpa using (List.nodup_cons.mp this).1
    exact hnn hmem

/-- 次の兄弟は同じ parent を持つ。 -/
theorem parentOf_nextSibling {t : Tree} (hwf : WellFormed t) {n m p : NodeId}
    (hp : parentOf t n = some p) (hn : nextSibling t n = some m) : parentOf t m = some p := by
  obtain ⟨A, B, hs⟩ := ListUtil.exists_splitAt?_of_mem ((mem_childrenOf_iff hwf n p).mp hp)
  have hL : childrenOf t p = A ++ n :: B := ListUtil.splitAt?_eq_some hs
  rw [nextSibling_of_split hwf hp hL] at hn
  have hmem : m ∈ B := by
    cases hb : B with
    | nil => rw [hb] at hn; simp at hn
    | cons x xs => rw [hb] at hn; simp at hn; simp [← hn]
  exact (mem_childrenOf_iff hwf m p).mpr (by rw [hL]; simp [hmem])

/--
次の兄弟の次の兄弟は、元の node ではない。

`replace` の step 2-3 が `child` の次を飛ばして `node` の次を取るとき、
その結果が `child` に戻らないことを言う。children に重複が無いからである。
-/
theorem nextSibling_nextSibling_ne {t : Tree} (hwf : WellFormed t) {n m k p : NodeId}
    (hp : parentOf t n = some p) (hn : nextSibling t n = some m)
    (hm : nextSibling t m = some k) : k ≠ n := by
  obtain ⟨A, B, hs⟩ := ListUtil.exists_splitAt?_of_mem ((mem_childrenOf_iff hwf n p).mp hp)
  have hL : childrenOf t p = A ++ n :: B := ListUtil.splitAt?_eq_some hs
  have hB := nextSibling_of_split hwf hp hL
  rw [hB] at hn
  cases hb : B with
  | nil => rw [hb] at hn; simp at hn
  | cons x B' =>
    rw [hb] at hn
    simp only [List.head?_cons, Option.some.injEq] at hn
    subst hn
    have hpm : parentOf t x = some p := parentOf_nextSibling hwf hp (by rw [hB, hb]; simp)
    have hL' : childrenOf t p = (A ++ [n]) ++ x :: B' := by rw [hL, hb]; simp
    rw [nextSibling_of_split hwf hpm hL'] at hm
    have hkm : k ∈ B' := by
      cases hc : B' with
      | nil => rw [hc] at hm; simp at hm
      | cons y ys => rw [hc] at hm; simp at hm; simp [← hm]
    intro he
    have hnd : (childrenOf t p).Nodup := childrenOf_nodup hwf p
    rw [hL, hb] at hnd
    have hnn : n ∉ x :: B' := (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1
    exact hnn (by simp [← he, hkm])

/--
**`preInsert` が成功するのは、step 1 の validity を通るときちょうどである。**

つまり `insertBefore` が返す例外は **pre-insertion validity のものだけ**である。
step 4 の `insert` は落ちない（`insert_isOk_of_validity`）。

`child` が `node` 自身の場合は step 2-3 が reference child を `node` の次の兄弟に
取り替えるが、validity はその取り替えを跨ぐ（`ensurePreInsertionValidity_shift`）。
取り替えた先が `node` になることも無い（`nextSibling_ne_self`）ので、除外は要らない。
-/
theorem preInsert_succeeds_iff {s : DOMState} (hwf : WellFormed s.tree)
    {node parent : NodeId} {child : Option NodeId} :
    (∃ s', preInsert s node parent child = .ok s') ↔
      ensurePreInsertionValidity s.tree node parent child [] = .ok () := by
  constructor
  · rintro ⟨s', h⟩
    exact (preInsert_cases h).1
  · intro hv
    rw [preInsert_of_validity hv]
    refine insert_isOk_of_validity hwf ?_ ?_
    · rw [preInsertReferenceChild_eq]
      exact ensurePreInsertionValidity_shift hwf hv
    · intro c hc he
      rw [preInsertReferenceChild_eq] at hc
      by_cases hq : child = some node
      · rw [if_pos hq] at hc
        exact nextSibling_ne_self hwf node (by rw [hc, he])
      · rw [if_neg hq] at hc
        exact hq (by rw [hc, he])

/-- **`preInsert` が失敗するのは validity で落ちるときちょうどで、例外はそれである。** -/
theorem preInsert_error_iff {s : DOMState} (hwf : WellFormed s.tree)
    {node parent : NodeId} {child : Option NodeId} {e : DOMException} :
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
      obtain ⟨s', hs'⟩ := (preInsert_succeeds_iff hwf).mpr (by cases u; exact hx)
      rw [hs'] at h
      simp at h
  · exact preInsert_of_validity_error

/-- **`appendChild` の契約。** -/
theorem append_succeeds_iff {s : DOMState} (hwf : WellFormed s.tree) {node parent : NodeId} :
    (∃ s', append s node parent = .ok s') ↔
      ensurePreInsertionValidity s.tree node parent none [] = .ok () := by
  rw [append]
  exact preInsert_succeeds_iff hwf


end Dom
