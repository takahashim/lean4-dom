import Url.SearchParams

/-!
# `URLSearchParams.sort` の正しさ（§6.2）

§6.2 の `sort()` は「名前の code unit 順で並べ替え、名前が等しい組どうしの相対順序を保つ」と言う。
ここでは `Params.sort` がその三つを満たし、しかもそれを満たす list は一つしかないことを示す。

* **並べ替えである。** `sort_perm`。
* **code unit 順に並ぶ。** `sort_sorted`。前の組の名前は後ろの組の名前より大きくない。
* **安定である。** `filter_sort`。名前ごとに取り出すと、組の並びは元の list と同じ。
* **一意である。** `sort_unique`。並んでいて名前ごとの並びが元と同じ list は `sort` の結果に限る。

一意性には「違う名前はどちらかが小さい」が要る。code unit 列への変換が単射であること
（`Infra.utf16Units_inj`）から出る。
-/

namespace Url.Params

open Infra

/-- 名前の code unit 順で並んでいる。前の組の名前が後ろの組の名前より大きいことはない。 -/
def Sorted (l : Params) : Prop := l.Pairwise (fun a b => strLt b.1 a.1 = false)

/-! ## 並べ替えである -/

theorem perm_insert (p : String × String) : ∀ s : Params, (insert p s).Perm (p :: s)
  | [] => .refl _
  | q :: rest => by
    rw [insert]
    split
    · exact ((perm_insert p rest).cons q).trans (.swap p q rest)
    · exact .refl _

/-- **`sort` は並べ替えである。** 組を落とさず、増やさない。 -/
theorem sort_perm : ∀ l : Params, (sort l).Perm l
  | [] => .refl _
  | p :: rest => (perm_insert p (sort rest)).trans ((sort_perm rest).cons p)

/-! ## code unit 順に並ぶ -/

theorem sorted_insert (p : String × String) : ∀ s : Params, Sorted s → Sorted (insert p s)
  | [] , _ => List.pairwise_singleton _ _
  | q :: rest, hs => by
    have hs' := List.pairwise_cons.mp hs
    rw [insert]
    split
    · next hqp =>
      refine List.pairwise_cons.mpr ⟨fun x hx => ?_, sorted_insert p rest hs'.2⟩
      rcases List.mem_cons.mp ((perm_insert p rest).mem_iff.mp hx) with rfl | hx
      · exact strLt_asymm hqp
      · exact hs'.1 x hx
    · next hqp =>
      have hqp : strLt q.1 p.1 = false := by simpa using hqp
      refine List.pairwise_cons.mpr ⟨fun x hx => ?_, hs⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hqp
      · exact strLe_trans hqp (hs'.1 x hx)

/-- **`sort` の結果は名前の code unit 順に並ぶ。** -/
theorem sort_sorted : ∀ l : Params, Sorted (sort l)
  | [] => List.Pairwise.nil
  | p :: rest => sorted_insert p (sort rest) (sort_sorted rest)

/-! ## 安定である -/

theorem filter_insert (p : String × String) (k : String) : ∀ s : Params,
    (insert p s).filter (fun x => x.1 == k) = (p :: s).filter (fun x => x.1 == k)
  | [] => rfl
  | q :: rest => by
    rw [insert]
    split
    · next hqp =>
      have hne := ne_of_strLt hqp
      rw [List.filter_cons, filter_insert p k rest]
      by_cases hq : q.1 = k <;> by_cases hp : p.1 = k
      · exact absurd (hq.trans hp.symm) hne
      · simp [hq, hp]
      · simp [hq, hp]
      · simp [hq, hp]
    · rfl

/--
**`sort` は安定である。** 名前ごとに取り出した組の並びは元の list と同じである。

値だけを見た形が `getAll_sort`（`Url/SearchParams.lean`）である。
-/
theorem filter_sort (k : String) : ∀ l : Params,
    (sort l).filter (fun x => x.1 == k) = l.filter (fun x => x.1 == k)
  | [] => rfl
  | p :: rest => by
    show (insert p (sort rest)).filter _ = _
    rw [filter_insert, List.filter_cons, List.filter_cons, filter_sort k rest]

/-! ## 一意である -/

/-- 並んでいる二つの list は、名前ごとの並びが同じなら等しい。 -/
theorem sorted_eq : ∀ {s s' : Params}, Sorted s → Sorted s' →
    (∀ k, s.filter (fun x => x.1 == k) = s'.filter (fun x => x.1 == k)) → s = s'
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => by
    have := h b.1
    simp at this
  | a :: _, [], _, _, h => by
    have := h a.1
    simp at this
  | a :: r, b :: r', hs, hs', h => by
    have hsc := List.pairwise_cons.mp hs
    have hsc' := List.pairwise_cons.mp hs'
    -- `a` は `s'` にもある（`b` も `s` にある）
    have hmem : ∀ k (x : String × String), x.1 = k →
        (x ∈ a :: r ↔ x ∈ b :: r') := by
      intro k x hx
      have := h k
      constructor
      · intro hm
        have : x ∈ (a :: r).filter (fun x => x.1 == k) := List.mem_filter.mpr ⟨hm, by simp [hx]⟩
        rw [h k] at this
        exact (List.mem_filter.mp this).1
      · intro hm
        have : x ∈ (b :: r').filter (fun x => x.1 == k) := List.mem_filter.mpr ⟨hm, by simp [hx]⟩
        rw [← h k] at this
        exact (List.mem_filter.mp this).1
    by_cases hab : a.1 = b.1
    · have hk := h a.1
      simp only [List.filter_cons, beq_self_eq_true, if_true, hab] at hk
      obtain ⟨rfl, -⟩ := List.cons.inj hk
      have hr : ∀ k, r.filter (fun x => x.1 == k) = r'.filter (fun x => x.1 == k) := by
        intro k
        have := h k
        simp only [List.filter_cons] at this
        split at this
        · exact (List.cons.inj this).2
        · exact this
      rw [sorted_eq hsc.2 hsc'.2 hr]
    · exfalso
      rcases strLt_total hab with hlt | hlt
      · -- `a` は `s'` の中で `b` の後ろにあるはずだが、`b` より小さい
        have ha := (hmem a.1 a rfl).mp (by simp)
        rcases List.mem_cons.mp ha with he | ha
        · exact hab (by rw [he])
        · rw [hsc'.1 a ha] at hlt; cases hlt
      · have hb := (hmem b.1 b rfl).mpr (by simp)
        rcases List.mem_cons.mp hb with he | hb
        · exact hab (by rw [he])
        · rw [hsc.1 b hb] at hlt; cases hlt

/--
**`sort` の結果は、仕様の言う並べ替えとして一つに決まる。**

名前の code unit 順に並び、名前ごとの組の並びが元の list と同じ list は `sort l` だけである。
-/
theorem sort_unique {l s : Params} (hs : Sorted s)
    (hf : ∀ k, s.filter (fun x => x.1 == k) = l.filter (fun x => x.1 == k)) : s = sort l :=
  sorted_eq hs (sort_sorted l) (fun k => (hf k).trans (filter_sort k l).symm)

end Url.Params
