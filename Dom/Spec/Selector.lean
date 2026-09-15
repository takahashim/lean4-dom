import Dom.Selector.Match
import Dom.Properties.Tree
import Dom.Properties.Mutation

/-!
# selector の照合の関係意味論（部分）

`Dom/Spec/Remove.lean` と同じ趣旨である。実行関数そのものを意味論にすると、
仕様の翻訳を誤ってもその誤った関数についての定理は証明できてしまう。
そこで仕様本文から独立に書き写した関係を置き、実行関数がそれを満たすことを示す。

照合全体ではなく、**翻訳を誤りやすく、差分テストが薄いところ**に絞ってある。

| 対象 | 仕様 | なぜここか |
| --- | --- | --- |
| `<a-n-plus-b>` が表す index | CSS Syntax §9 | `A` が負の場合を生成器が一度も作っていない |
| combinator が結ぶ element | Selectors §16 | `+` と `~` の候補を list 操作で書いており、off-by-one が入りうる |

## 書き方の制約

**この module は照合の実行関数を呼ばない。** 使ってよいのは `parentOf` /
`childrenOf` / `index` / `Ancestor` のような観測の語彙と、
仕様が言う「element だけを見る」という条件だけである。
-/

namespace Dom.Spec

open Dom Selectors

/-! ## `<a-n-plus-b>`（CSS Syntax Level 3 §9） -/

/--
仕様が言う「`An+B` が表す index」。

> The `An+B` notation ... represents any index `i = An + B` for any
> **non-negative integer** `n`.

`n` が非負に限ることが効く。`A` が負なら表す index は有限個になり、
`:nth-child(-n+3)` が「先頭から三つ」を指す。
-/
def AnBIndex (ab : AnB) (i : Nat) : Prop := ∃ n : Nat, ab.a * (n : Int) + ab.b = (i : Int)

/-- 正の係数のときの、非負の倍数であることの言い換え。 -/
theorem exists_nat_mul_iff {a d : Int} (ha : 0 < a) :
    (∃ n : Nat, a * (n : Int) = d) ↔ (0 ≤ d ∧ d % a = 0) := by
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨Int.mul_nonneg (Int.le_of_lt ha) (Int.natCast_nonneg n), Int.mul_emod_right a n⟩
  · rintro ⟨hd, hz⟩
    refine ⟨(d / a).toNat, ?_⟩
    rw [Int.toNat_of_nonneg (Int.ediv_nonneg hd (Int.le_of_lt ha))]
    exact Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hz)

/-- **`anbMatches` は仕様の言う index の集合をちょうど表す。** -/
theorem anbMatches_iff (ab : AnB) (i : Nat) : anbMatches ab i = true ↔ AnBIndex ab i := by
  have hshift : AnBIndex ab i ↔ ∃ n : Nat, ab.a * (n : Int) = (i : Int) - ab.b := by
    constructor <;> rintro ⟨n, hn⟩ <;> exact ⟨n, by omega⟩
  rw [hshift]
  unfold anbMatches
  by_cases ha : ab.a = 0
  · simp only [ha, beq_self_eq_true, if_pos, Int.zero_mul]
    constructor
    · intro h; exact ⟨0, by simpa using (by simpa using h : (i : Int) - ab.b = 0).symm⟩
    · rintro ⟨n, hn⟩; simpa using hn.symm
  · rw [if_neg (by simpa using ha)]
    by_cases hp : 0 < ab.a
    · rw [if_pos (by simpa using hp)]
      rw [exists_nat_mul_iff hp]
      simp
    · rw [if_neg (by simpa using hp)]
      have hn : 0 < -ab.a := by omega
      have hneg : (∃ n : Nat, ab.a * (n : Int) = (i : Int) - ab.b)
          ↔ ∃ n : Nat, (-ab.a) * (n : Int) = -((i : Int) - ab.b) := by
        constructor
        · rintro ⟨n, hn⟩
          exact ⟨n, by rw [Int.neg_mul, hn]⟩
        · rintro ⟨n, hn⟩
          rw [Int.neg_mul] at hn
          exact ⟨n, by omega⟩
      rw [hneg, exists_nat_mul_iff hn]
      simp

/--
**`:nth-child(-n+B)` は「先頭から B 個」である。**

`A` が負のときに `n` が非負に限ることの帰結で、生成器が作らない形である。
-/
theorem anbMatches_neg_one (b : Int) (i : Nat) :
    anbMatches ⟨-1, b⟩ i = true ↔ (i : Int) ≤ b := by
  rw [anbMatches_iff]
  constructor
  · rintro ⟨n, hn⟩
    have : (0 : Int) ≤ (n : Int) := Int.natCast_nonneg n
    simp only at hn
    omega
  · intro h
    refine ⟨(b - (i : Int)).toNat, ?_⟩
    rw [Int.toNat_of_nonneg (by omega)]
    simp only
    omega

/-- `odd` は奇数の index をちょうど表す。 -/
theorem anbMatches_odd (i : Nat) : anbMatches ⟨2, 1⟩ i = true ↔ i % 2 = 1 := by
  rw [anbMatches_iff]
  constructor
  · rintro ⟨n, hn⟩; simp only at hn; omega
  · intro h; exact ⟨i / 2, by simp only; omega⟩

/-- `even` は偶数の index をちょうど表す。 -/
theorem anbMatches_even (i : Nat) : anbMatches ⟨2, 0⟩ i = true ↔ i % 2 = 0 := by
  rw [anbMatches_iff]
  constructor
  · rintro ⟨n, hn⟩; simp only at hn; omega
  · intro h; exact ⟨i / 2, by simp only; omega⟩

/-! ## combinator が結ぶ element（Selectors Level 4 §16）

仕様は combinator を「`E` と `F` の間の関係」として定める。

| combinator | 仕様 |
| --- | --- |
| `E F` | `F` は `E` の descendant |
| `E > F` | `F` は `E` の child |
| `E ~ F` | 同じ parent を持ち、`E` が `F` より前にある |
| `E + F` | 同じ parent を持ち、`E` が `F` の**すぐ**前にある |

selector は element しか見ないので、sibling の並びは element だけの列である。
その列そのものは `elementChildrenOf` を共有するが、**位置の表し方は
実行側と独立**にしてある。実行側は `takeWhile` と `getLast?` で書いており、
向き（前か後か）と一つずれが入りうるのはそこだからである。
-/

/-- `E ~ F`。同じ parent の element の並びで、`e` が `f` より前にある。 -/
def ElementSiblingBefore (t : Tree) (e f : NodeId) : Prop :=
  ∃ p pre mid post, elementChildrenOf t p = pre ++ e :: mid ++ f :: post

/-- `E + F`。同じ parent の element の並びで、`e` が `f` のすぐ前にある。 -/
def ElementSiblingImmediatelyBefore (t : Tree) (e f : NodeId) : Prop :=
  ∃ p pre post, elementChildrenOf t p = pre ++ e :: f :: post

theorem takeWhile_ne_append (n : NodeId) : ∀ (pre post : List NodeId), n ∉ pre →
    (pre ++ n :: post).takeWhile (fun m => m != n) = pre
  | [], _, _ => by simp
  | c :: rest, post, h => by
    have hc : ¬ c = n := fun heq => h (by simp [heq])
    simp only [List.cons_append, List.takeWhile_cons, bne_iff_ne, ne_eq, hc, not_false_eq_true,
      if_true, List.cons.injEq, true_and]
    exact takeWhile_ne_append n rest post (fun hm => h (List.mem_cons_of_mem c hm))

theorem elementChildrenOf_nodup {t : Tree} (hwf : WellFormed t) (p : NodeId) :
    (elementChildrenOf t p).Nodup :=
  List.Sublist.nodup List.filter_sublist (childrenOf_nodup hwf p)

theorem mem_elementChildrenOf {t : Tree} (hwf : WellFormed t) {n p : NodeId}
    (hp : parentOf t n = some p) (hel : isElementNode t n = true) :
    n ∈ elementChildrenOf t p := by
  simp only [elementChildrenOf, List.mem_filter]
  exact ⟨(mem_childrenOf_iff hwf n p).mp hp, hel⟩

/-- element の並びで `n` の手前にあるものは、`takeWhile` が切り出すものである。 -/
theorem takeWhile_eq_of_split {t : Tree} (hwf : WellFormed t) {n p : NodeId}
    {a b : List NodeId} (hs : elementChildrenOf t p = a ++ n :: b) :
    (elementChildrenOf t p).takeWhile (fun m => m != n) = a := by
  have hnd : (elementChildrenOf t p).Nodup := elementChildrenOf_nodup hwf p
  rw [hs] at hnd
  have hnot : n ∉ a := fun hm => by
    rw [List.nodup_append] at hnd
    exact hnd.2.2 n hm n (List.mem_cons_self ..) rfl
  rw [hs, takeWhile_ne_append n a b hnot]

/-- **`E F` の候補はちょうど ancestor である。** -/
theorem mem_combCandidates_descendant {t : Tree} (hwf : WellFormed t) (e n : NodeId) :
    e ∈ combCandidates t .descendant n ↔ Ancestor t e n := by
  simp only [combCandidates]
  exact mem_ancestors_iff hwf n e

/-- **`E > F` の候補はちょうど parent である。** -/
theorem mem_combCandidates_child {t : Tree} (e n : NodeId) :
    e ∈ combCandidates t .child n ↔ parentOf t n = some e := by
  simp only [combCandidates]
  cases hp : parentOf t n with
  | none => simp
  | some p => simp [eq_comm]

/-- **`E ~ F` の候補はちょうど、前にある element の sibling である。** -/
theorem mem_combCandidates_subsequentSibling {t : Tree} (hwf : WellFormed t) {n p : NodeId}
    (hp : parentOf t n = some p) (hn : isElementNode t n = true) (e : NodeId) :
    e ∈ combCandidates t .subsequentSibling n ↔ ElementSiblingBefore t e n := by
  obtain ⟨pre, post, hsplit, hnotin⟩ :=
    List.eq_append_cons_of_mem (mem_elementChildrenOf hwf hp hn)
  have hcand : combCandidates t .subsequentSibling n = pre := by
    simp only [combCandidates, hp]
    exact takeWhile_eq_of_split hwf hsplit
  rw [hcand]
  constructor
  · intro he
    obtain ⟨a, b, hab, _⟩ := List.eq_append_cons_of_mem he
    exact ⟨p, a, b, post, by simp [hsplit, hab]⟩
  · rintro ⟨q, a, mid, post', hq⟩
    have hqp : q = p := by
      have hmem : n ∈ elementChildrenOf t q := by rw [hq]; simp
      rw [elementChildrenOf, List.mem_filter] at hmem
      have := parentOf_of_mem_childrenOf hwf hmem.1
      rw [hp] at this
      exact (Option.some.inj this).symm
    subst hqp
    have hsp : elementChildrenOf t q = (a ++ e :: mid) ++ n :: post' := by rw [hq]
    have : (elementChildrenOf t q).takeWhile (fun m => m != n) = a ++ e :: mid :=
      takeWhile_eq_of_split hwf hsp
    rw [← takeWhile_eq_of_split hwf hsplit, this]
    simp

/-- **`E + F` の候補はちょうど、すぐ前にある element の sibling である。** -/
theorem mem_combCandidates_nextSibling {t : Tree} (hwf : WellFormed t) {n p : NodeId}
    (hp : parentOf t n = some p) (hn : isElementNode t n = true) (e : NodeId) :
    e ∈ combCandidates t .nextSibling n ↔ ElementSiblingImmediatelyBefore t e n := by
  obtain ⟨pre, post, hsplit, hnotin⟩ :=
    List.eq_append_cons_of_mem (mem_elementChildrenOf hwf hp hn)
  have hpre : (elementChildrenOf t p).takeWhile (fun m => m != n) = pre :=
    takeWhile_eq_of_split hwf hsplit
  have hcand : ∀ x, x ∈ combCandidates t .nextSibling n ↔ pre.getLast? = some x := by
    intro x
    simp only [combCandidates, hp, hpre]
    cases hg : pre.getLast? with
    | none => simp
    | some m => simp [eq_comm]
  rw [hcand e, List.getLast?_eq_some_iff]
  constructor
  · rintro ⟨ys, hys⟩
    exact ⟨p, ys, post, by simp [hsplit, hys]⟩
  · rintro ⟨q, a, post', hq⟩
    have hqp : q = p := by
      have hmem : n ∈ elementChildrenOf t q := by rw [hq]; simp
      rw [elementChildrenOf, List.mem_filter] at hmem
      have := parentOf_of_mem_childrenOf hwf hmem.1
      rw [hp] at this
      exact (Option.some.inj this).symm
    subst hqp
    have hsp : elementChildrenOf t q = (a ++ [e]) ++ n :: post' := by rw [hq]; simp
    have : (elementChildrenOf t q).takeWhile (fun m => m != n) = a ++ [e] :=
      takeWhile_eq_of_split hwf hsp
    exact ⟨a, by rw [← hpre, this]⟩

end Dom.Spec
