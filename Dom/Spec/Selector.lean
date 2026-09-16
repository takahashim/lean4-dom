import Dom.Selector.Match
import Dom.Properties.Tree
import Dom.Properties.Mutation
import Dom.Properties.TreeOrder

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

/-! ## attribute selector の値の照合（Selectors Level 4 §6.3）

仕様は六つの演算子を「値 `v` と selector の値 `w` の関係」として定める。
実行側は `hasPrefixL` / `hasSuffixL` / `hasInfixL` と空白での分割で書いており、
**前後を取り違える・空文字列の除外を落とす**のが誤りやすいところである。

`~=` の「空白で区切った語のどれか」だけは、語の切り出しの帰納法が重いので
定理にしていない。仕様が明記する二つの但し書き（値が空、値が空白を含む）は
定理にしてあり、語境界そのものは固定 scenario
`attribute-includes-needs-a-whole-word` が見ている。
-/

def NoWhitespace (w : List Char) : Prop := ∀ c ∈ w, isAsciiWhitespace c = false

/-- `w` が `v` の中に空白で区切られた語として現れる。 -/
def WordIn (v w : List Char) : Prop :=
  ∃ pre post, v = pre ++ (w ++ post) ∧
    (∀ c, pre.getLast? = some c → isAsciiWhitespace c = true) ∧
    (∀ c, post.head? = some c → isAsciiWhitespace c = true)

private theorem getLast?_append_ne {u l : List Char} (h : l ≠ []) :
    (u ++ l).getLast? = l.getLast? := by
  rw [List.getLast?_append]
  cases hl : l.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp hl) h
  | some c => rfl

theorem wordIn_of_no_ws {u w : List Char} (hu : ∀ c ∈ u, isAsciiWhitespace c = false) :
    WordIn u w ↔ u = w := by
  constructor
  · rintro ⟨pre, post, hv, hpre, hpost⟩
    have hpn : pre = [] := by
      cases hp : pre with
      | nil => rfl
      | cons a as =>
        exfalso
        obtain ⟨c, hc⟩ : ∃ c, (a :: as).getLast? = some c := by
          cases h2 : (a :: as).getLast? with
          | none => exact absurd h2 (by simp)
          | some c => exact ⟨c, rfl⟩
        have hcw := hpre c (by rw [hp]; exact hc)
        have hcmem : c ∈ (a :: as) := List.mem_of_getLast? hc
        have hcm : c ∈ u := by
          rw [hv, hp]
          simp only [List.cons_append, List.mem_cons, List.mem_append]
          rcases List.mem_cons.mp hcmem with rfl | hx
          · exact Or.inl rfl
          · exact Or.inr (Or.inl hx)
        rw [hu c hcm] at hcw
        simp at hcw
    have hqn : post = [] := by
      cases hp : post with
      | nil => rfl
      | cons a as =>
        exfalso
        have hcw := hpost a (by rw [hp]; rfl)
        have hcm : a ∈ u := by rw [hv, hp]; simp
        rw [hu a hcm] at hcw
        simp at hcw
    rw [hv, hpn, hqn]
    simp
  · intro h
    exact ⟨[], [], by rw [h]; simp, by simp, by simp⟩

theorem wordIn_append_ws {u : List Char} (hu : ∀ c ∈ u, isAsciiWhitespace c = false)
    {ws : Char} (hws : isAsciiWhitespace ws = true) {rest w : List Char}
    (hne : w ≠ []) (hnw : NoWhitespace w) :
    WordIn (u ++ (ws :: rest)) w ↔ ((u ≠ [] ∧ u = w) ∨ WordIn rest w) := by
  constructor
  · rintro ⟨pre, post, hv, hpre, hpost⟩
    rcases List.append_eq_append_iff.mp hv with ⟨as, hpe, hxs⟩ | ⟨bs, hue, hzs⟩
    · -- pre = u ++ as, ws :: rest = as ++ (w ++ post)
      cases as with
      | nil =>
        exfalso
        simp only [List.nil_append] at hxs
        cases w with
        | nil => exact hne rfl
        | cons a w' =>
          rw [List.cons_append] at hxs
          injection hxs with h1 _
          have := hnw ws (by rw [h1]; simp)
          rw [hws] at this
          simp at this
      | cons a as' =>
        rw [List.cons_append] at hxs
        injection hxs with h1 h2
        refine Or.inr ⟨as', post, h2, ?_, hpost⟩
        intro c hc
        refine hpre c ?_
        rw [hpe]
        cases has : as' with
        | nil => rw [has] at hc; simp at hc
        | cons b bs' =>
          rw [getLast?_append_ne (l := a :: b :: bs') (by simp)]
          rw [has] at hc
          simpa using hc
    · -- u = pre ++ bs, w ++ post = bs ++ (ws :: rest)
      have hpn : pre = [] := by
        cases hp : pre with
        | nil => rfl
        | cons a as =>
          exfalso
          obtain ⟨c, hc⟩ : ∃ c, (a :: as).getLast? = some c := by
            cases h2 : (a :: as).getLast? with
            | none => exact absurd h2 (by simp)
            | some c => exact ⟨c, rfl⟩
          have hcw := hpre c (by rw [hp]; exact hc)
          have hcmem : c ∈ (a :: as) := List.mem_of_getLast? hc
          have hcm : c ∈ u := by rw [hue, hp]; exact List.mem_append.mpr (Or.inl hcmem)
          rw [hu c hcm] at hcw
          simp at hcw
      subst hpn
      simp only [List.nil_append] at hue hzs
      subst hue
      rcases List.append_eq_append_iff.mp hzs with ⟨as, hue2, hpost2⟩ | ⟨bs', hwe, hzs2⟩
      · -- u = w ++ as, post = as ++ (ws :: rest)
        cases as with
        | nil =>
          refine Or.inl ⟨?_, ?_⟩
          · rw [hue2]; simpa using hne
          · rw [hue2]; simp
        | cons b bs'' =>
          exfalso
          have hb : b ∈ u := by rw [hue2]; exact List.mem_append.mpr (Or.inr (by simp))
          have hh := hpost b (by rw [hpost2]; rfl)
          rw [hu b hb] at hh
          simp at hh
      · -- w = u ++ bs', ws :: rest = bs' ++ post
        cases bs' with
        | nil =>
          rw [List.append_nil] at hwe
          exact Or.inl ⟨by rw [← hwe]; exact hne, hwe.symm⟩
        | cons b bs'' =>
          exfalso
          rw [List.cons_append] at hzs2
          injection hzs2 with h1 _
          have : ws ∈ w := by rw [hwe, ← h1]; exact List.mem_append.mpr (Or.inr (by simp))
          have h3 := hnw ws this
          rw [hws] at h3
          simp at h3
  · rintro (⟨hune, rfl⟩ | ⟨pre', post', hr, hpre', hpost'⟩)
    · exact ⟨[], ws :: rest, by simp, by simp, by simp [hws]⟩
    · refine ⟨u ++ (ws :: pre'), post', by rw [hr]; simp, ?_, hpost'⟩
      intro c hc
      cases hp : pre' with
      | nil =>
        rw [hp] at hc
        rw [getLast?_append_ne (l := [ws]) (by simp)] at hc
        simp only [List.getLast?_singleton, Option.some.injEq] at hc
        rw [← hc]; exact hws
      | cons b bs =>
        rw [hp] at hc
        rw [getLast?_append_ne (l := ws :: b :: bs) (by simp)] at hc
        refine hpre' c ?_
        rw [hp]
        simpa using hc


/-- 六つの演算子が表す、値どうしの関係。 -/
def AttrOpHolds : AttrOp -> List Char -> List Char -> Prop
  | .exact, v, w => v = w
  | .includes, v, w => w ≠ [] ∧ NoWhitespace w ∧ WordIn v w
  | .dashMatch, v, w => v = w ∨ ∃ rest, v = w ++ Char.ofNat 0x2D :: rest
  | .prefixMatch, v, w => w ≠ [] ∧ ∃ rest, v = w ++ rest
  | .suffixMatch, v, w => w ≠ [] ∧ ∃ pre, v = pre ++ w
  | .substring, v, w => w ≠ [] ∧ ∃ pre post, v = pre ++ w ++ post

theorem hasPrefixL_iff : ∀ (p l : List Char), hasPrefixL p l = true ↔ ∃ rest, l = p ++ rest
  | [], l => by simp [hasPrefixL]
  | _ :: _, [] => by simp [hasPrefixL]
  | a :: as, b :: bs => by
    rw [hasPrefixL, Bool.and_eq_true, beq_iff_eq, hasPrefixL_iff as bs]
    constructor
    · rintro ⟨rfl, rest, rfl⟩
      exact ⟨rest, rfl⟩
    · rintro ⟨rest, h⟩
      rw [List.cons_append, List.cons.injEq] at h
      exact ⟨h.1.symm, rest, h.2⟩

theorem hasSuffixL_iff (p l : List Char) : hasSuffixL p l = true ↔ ∃ pre, l = pre ++ p := by
  rw [hasSuffixL, hasPrefixL_iff]
  constructor
  · rintro ⟨rest, h⟩
    refine ⟨rest.reverse, ?_⟩
    have := congrArg List.reverse h
    simpa using this
  · rintro ⟨pre, rfl⟩
    exact ⟨pre.reverse, by simp⟩

theorem hasInfixL_iff (p : List Char) : ∀ (l : List Char),
    hasInfixL p l = true ↔ ∃ pre post, l = pre ++ p ++ post
  | [] => by
    rw [hasInfixL, hasPrefixL_iff]
    constructor
    · rintro ⟨rest, h⟩
      exact ⟨[], rest, by simpa using h⟩
    · rintro ⟨pre, post, h⟩
      refine ⟨[], ?_⟩
      have hp : p = [] := by
        have h' := h.symm
        simp only [List.append_eq_nil_iff] at h'
        exact h'.1.2
      simp [hp]
  | c :: t => by
    rw [hasInfixL, Bool.or_eq_true, hasPrefixL_iff, hasInfixL_iff p t]
    constructor
    · rintro (⟨rest, h⟩ | ⟨pre, post, h⟩)
      · exact ⟨[], rest, by simpa using h⟩
      · exact ⟨c :: pre, post, by simp [h]⟩
    · rintro ⟨pre, post, h⟩
      cases pre with
      | nil => exact Or.inl ⟨post, by simpa using h⟩
      | cons a as =>
        refine Or.inr ⟨as, post, ?_⟩
        rw [List.cons_append, List.cons_append, List.cons.injEq] at h
        exact h.2

/-! ### 空白区切りの語列（`splitWsAux` の特徴付け） -/

end Dom.Spec

namespace Dom
open Dom.Spec Infra

/-- accumulator は「まだ出していない語の逆順」なので、先頭に戻してよい。 -/
theorem splitWsAux_no_ws : ∀ (l acc : List Char), (∀ c ∈ l, isAsciiWhitespace c = false) →
    splitWsAux acc l = (if (acc.reverse ++ l).isEmpty then [] else [acc.reverse ++ l])
  | [], acc, _ => by
    show (if acc.isEmpty then [] else [acc.reverse]) = _
    by_cases h : acc.isEmpty = true
    · rw [if_pos h]
      have : acc = [] := List.isEmpty_iff.mp h
      subst this; simp
    · rw [if_neg h]
      have : acc ≠ [] := fun hc => h (by rw [hc]; rfl)
      simp [this]
  | a :: as, acc, h => by
    have ha : isAsciiWhitespace a = false := h a (by simp)
    show (if isAsciiWhitespace a then _ else splitWsAux (a :: acc) as) = _
    rw [if_neg (by rw [ha]; simp),
      splitWsAux_no_ws as (a :: acc) (fun c hc => h c (by simp [hc]))]
    simp

theorem splitWsAux_split : ∀ (word acc : List Char), (∀ c ∈ word, isAsciiWhitespace c = false) →
    ∀ (ws : Char), isAsciiWhitespace ws = true → ∀ (tail : List Char),
    splitWsAux acc (word ++ ws :: tail) =
      (if (acc.reverse ++ word).isEmpty then [] else [acc.reverse ++ word]) ++ splitWsAux [] tail
  | [], acc, _, ws, hws, tail => by
    show (if isAsciiWhitespace ws then
        (if acc.isEmpty then [] else [acc.reverse]) ++ splitWsAux [] tail else _) = _
    rw [if_pos (by rw [hws])]
    by_cases h : acc.isEmpty = true
    · have : acc = [] := List.isEmpty_iff.mp h
      subst this; simp
    · have hne : acc ≠ [] := fun hc => h (by rw [hc]; rfl)
      rw [if_neg h, if_neg (by simp [hne])]
      simp
  | a :: rest, acc, h, ws, hws, tail => by
    have ha : isAsciiWhitespace a = false := h a (by simp)
    show (if isAsciiWhitespace a then _ else splitWsAux (a :: acc) (rest ++ ws :: tail)) = _
    rw [if_neg (by rw [ha]; simp),
      splitWsAux_split rest (a :: acc) (fun c hc => h c (by simp [hc])) ws hws tail]
    simp

/-- 最初の whitespace で切る。 -/
theorem exists_first_ws : ∀ (v : List Char),
    (∀ c ∈ v, isAsciiWhitespace c = false) ∨
    ∃ word ws tail, v = word ++ ws :: tail ∧ (∀ c ∈ word, isAsciiWhitespace c = false) ∧
      isAsciiWhitespace ws = true
  | [] => Or.inl (by simp)
  | a :: rest => by
    by_cases ha : isAsciiWhitespace a = true
    · exact Or.inr ⟨[], a, rest, rfl, by simp, ha⟩
    · rcases exists_first_ws rest with h | ⟨word, ws, tail, hv, hw, hws⟩
      · refine Or.inl fun c hc => ?_
        rcases List.mem_cons.mp hc with rfl | hc'
        · simpa using ha
        · exact h c hc'
      · refine Or.inr ⟨a :: word, ws, tail, by rw [hv]; simp, fun c hc => ?_, hws⟩
        rcases List.mem_cons.mp hc with rfl | hc'
        · simpa using ha
        · exact hw c hc'

/-- **`splitWsAux [] v` は `v` の空白区切りの語をちょうど並べる。** -/
theorem mem_splitWs_iff : ∀ (n : Nat) (v : List Char), v.length ≤ n → ∀ (w : List Char),
    w ≠ [] → NoWhitespace w → (w ∈ splitWsAux [] v ↔ WordIn v w)
  | 0, v, hlen, w, hne, hnw => by
    have : v = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    constructor
    · intro h; simp [splitWsAux] at h
    · rintro ⟨pre, post, hv, -, -⟩
      exfalso
      have := congrArg List.length hv
      simp at this
      exact hne (List.eq_nil_of_length_eq_zero (by omega))
  | n + 1, v, hlen, w, hne, hnw => by
    rcases exists_first_ws v with hno | ⟨word, ws, tail, rfl, hword, hws⟩
    · rw [splitWsAux_no_ws v [] hno, wordIn_of_no_ws hno]
      split
      · next h =>
        have hvn : v = [] := by
          have := List.isEmpty_iff.mp h
          simpa using this
        constructor
        · intro hm; simp at hm
        · intro hm; rw [hvn] at hm; exact absurd hm.symm hne
      · next h =>
        simp only [List.reverse_nil, List.nil_append, List.mem_singleton]
        exact ⟨fun hm => hm.symm, fun hm => hm.symm⟩
    · rw [splitWsAux_split word [] hword ws hws tail]
      have hlt : tail.length ≤ n := by simp at hlen; omega
      rw [wordIn_append_ws hword hws hne hnw]
      rw [List.mem_append]
      rw [mem_splitWs_iff n tail hlt w hne hnw]
      have hsplit : (w ∈ (if ([].reverse ++ word).isEmpty = true then []
          else [([].reverse ++ word)])) ↔ (word ≠ [] ∧ word = w) := by
        split
        · next h =>
          have hwn : word = [] := by
            have := List.isEmpty_iff.mp h
            simpa using this
          constructor
          · intro hm; simp at hm
          · rintro ⟨hne2, -⟩; exact absurd hwn hne2
        · next h =>
          simp only [List.reverse_nil, List.nil_append, List.mem_singleton]
          have hwne : word ≠ [] := by
            intro hc
            rw [hc] at h
            simp at h
          exact ⟨fun hm => ⟨hwne, hm.symm⟩, fun hm => hm.2.symm⟩
      rw [hsplit]

end Dom

namespace Dom.Spec

open Dom Selectors

/-- **六つの演算子は仕様の関係をちょうど表す。** -/
theorem attrTestHolds_iff (test : AttrTest) (value : String) :
    attrTestHolds test value = true ↔
      AttrOpHolds test.op (caseFold test.case value.toList)
        (caseFold test.case test.value.toList) := by
  unfold attrTestHolds
  cases hop : test.op with
  | exact => simp [AttrOpHolds]
  | includes =>
    simp only [AttrOpHolds, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      List.isEmpty_eq_false_iff, List.any_eq_false, List.any_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨⟨hne, hnw⟩, hmem⟩
      obtain ⟨x, hx, rfl⟩ := hmem
      refine ⟨hne, fun c hc => ?_, ?_⟩
      · have := hnw c hc
        simpa using this
      · exact (mem_splitWs_iff (caseFold test.case value.toList).length
          (caseFold test.case value.toList) (Nat.le_refl _) _ hne
          (fun c hc => by simpa using hnw c hc)).mp hx
    · rintro ⟨hne, hnw, hword⟩
      refine ⟨⟨hne, fun c hc => by simpa using hnw c hc⟩, ?_⟩
      exact ⟨_, (mem_splitWs_iff (caseFold test.case value.toList).length
        (caseFold test.case value.toList) (Nat.le_refl _) _ hne hnw).mpr hword, rfl⟩
  | dashMatch =>
    simp only [AttrOpHolds, Bool.or_eq_true, beq_iff_eq, hasPrefixL_iff]
    constructor
    · rintro (h1 | ⟨rest, h1⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨rest, by simpa using h1⟩
    · rintro (h1 | ⟨rest, h1⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨rest, by simpa using h1⟩
  | prefixMatch =>
    simp only [AttrOpHolds, Bool.and_eq_true, hasPrefixL_iff, Bool.not_eq_true',
      List.isEmpty_eq_false_iff]
  | suffixMatch =>
    simp only [AttrOpHolds, Bool.and_eq_true, hasSuffixL_iff, Bool.not_eq_true',
      List.isEmpty_eq_false_iff]
  | substring =>
    simp only [AttrOpHolds, Bool.and_eq_true, hasInfixL_iff, Bool.not_eq_true',
      List.isEmpty_eq_false_iff]

/-- **`[att~=""]` は何にも当たらない。** 仕様が明記する但し書きの一つ。 -/
theorem includes_empty_never (c : AttrCase) (value : String) :
    attrTestHolds ⟨.includes, "", c⟩ value = false := by
  cases c <;> simp [attrTestHolds, caseFold]

/--
**`caseFold` は whitespace を含むかどうかを変えない。**

`i` flag の ASCII lowercase は A-Z しか動かさないので、whitespace には触れない。
-/
theorem any_isAsciiWhitespace_caseFold (case : AttrCase) (l : List Char) :
    (caseFold case l).any isAsciiWhitespace = l.any isAsciiWhitespace := by
  cases case with
  | insensitive =>
    show (l.map Infra.asciiLowerChar).any isAsciiWhitespace = _
    rw [List.any_map]
    refine congrArg _ ?_
    funext c
    exact Infra.isAsciiWhitespace_asciiLowerChar c
  | _ => rfl

/--
**値が空白を含む `~=` は何にも当たらない。** もう一つの但し書き。

`i` flag が付いていても同じである（`any_isAsciiWhitespace_caseFold`）。
-/
theorem includes_whitespace_never (test : AttrTest) (value : String)
    (hop : test.op = .includes)
    (hw : ∃ c ∈ test.value.toList, isAsciiWhitespace c = true) :
    attrTestHolds test value = false := by
  obtain ⟨c, hcmem, hcws⟩ := hw
  unfold attrTestHolds
  simp only [hop, Bool.and_eq_false_iff]
  refine Or.inl (Or.inr ?_)
  simp only [Bool.not_eq_eq_eq_not, Bool.not_false]
  rw [any_isAsciiWhitespace_caseFold]
  exact List.any_eq_true.mpr ⟨c, hcmem, hcws⟩

/-! ## `:nth-*()` が数える列（Selectors Level 4 §14.3-14.7）

仕様は

> elements that are among `An+B`-th elements from the list composed of their
> **inclusive siblings** that match the selector list `S`

と言う。効くのは三つである。

* 数える列は **inclusive sibling**（`:nth-of-type()` では同じ type のもの）だけ
* index は **1 始まり**
* `:nth-last-*()` は **末尾から**数える

実行側は `elementSiblings` / `filter` / `reverse` / `indexOfNode` で書いてあり、
数え始めと向きを取り違えうるのはそこである。
-/

/-- §3.1 の inclusive sibling のうち element。parent が無ければ自分だけである。 -/
def InclusiveElementSibling (t : Tree) (m n : NodeId) : Prop :=
  isElementNode t m = true ∧ (m = n ∨ ∃ p, parentOf t n = some p ∧ parentOf t m = some p)

/-- §14.5 の「同じ type」。namespace と local name が一致すること。 -/
def SameType (t : Tree) (d : NodeData) (m : NodeId) : Prop :=
  ∃ e, t.get? m = some e ∧ e.namespace = d.namespace ∧ e.localName = d.localName

/-- **`elementSiblings` はちょうど inclusive element sibling を並べる。** -/
theorem mem_elementSiblings_iff {t : Tree} (hwf : WellFormed t) {n : NodeId}
    (hn : isElementNode t n = true) (m : NodeId) :
    m ∈ elementSiblings t n ↔ InclusiveElementSibling t m n := by
  unfold elementSiblings InclusiveElementSibling
  cases hp : parentOf t n with
  | none =>
    constructor
    · intro h
      have : m = n := by simpa using h
      exact ⟨this ▸ hn, Or.inl this⟩
    · rintro ⟨_, hm | ⟨p, hpp, _⟩⟩
      · simp [hm]
      · exact absurd hpp (by simp)
  | some p =>
    simp only [elementChildrenOf, List.mem_filter]
    constructor
    · rintro ⟨hmem, hel⟩
      exact ⟨hel, Or.inr ⟨p, rfl, (mem_childrenOf_iff hwf m p).mpr hmem⟩⟩
    · rintro ⟨hel, hm | ⟨q, hq, hmq⟩⟩
      · subst hm
        exact ⟨(mem_childrenOf_iff hwf m p).mp hp, hel⟩
      · rw [← Option.some.inj hq] at hmq
        exact ⟨(mem_childrenOf_iff hwf m p).mp hmq, hel⟩

/-- **`sameTypeAs` はちょうど「同じ type」である。** -/
theorem sameTypeAs_iff (t : Tree) (d : NodeData) (m : NodeId) :
    sameTypeAs t d m = true ↔ SameType t d m := by
  unfold sameTypeAs SameType
  cases hm : t.get? m with
  | none => simp
  | some e => simp

/-! ### index の数え方 -/

theorem indexOfNode_of_split : ∀ (pre post : List NodeId) (n : NodeId), n ∉ pre →
    indexOfNode (pre ++ n :: post) n = some pre.length
  | [], _, _, _ => by simp [indexOfNode, List.findIdx?_cons]
  | c :: rest, post, n, h => by
    have hc : ¬ c = n := fun heq => h (by simp [heq])
    simp only [indexOfNode, List.cons_append, List.findIdx?_cons, beq_iff_eq, hc, if_false,
      List.length_cons]
    rw [show List.findIdx? (fun m => m == n) (rest ++ n :: post) = some rest.length from
      indexOfNode_of_split rest post n (fun hm => h (List.mem_cons_of_mem c hm))]
    simp

theorem indexOfNode_eq_some : ∀ (l : List NodeId) (n : NodeId) (i : Nat),
    indexOfNode l n = some i → ∃ pre post, l = pre ++ n :: post ∧ pre.length = i
  | [], _, _, h => by simp [indexOfNode] at h
  | c :: rest, n, i, h => by
    simp only [indexOfNode, List.findIdx?_cons, beq_iff_eq] at h
    by_cases hc : c = n
    · rw [if_pos hc] at h
      exact ⟨[], rest, by simp [hc], by simpa using Option.some.inj h⟩
    · rw [if_neg hc] at h
      cases hj : List.findIdx? (fun m => m == n) rest with
      | none => rw [hj] at h; simp at h
      | some j =>
        rw [hj] at h
        obtain ⟨pre, post, hs, hl⟩ := indexOfNode_eq_some rest n j hj
        refine ⟨c :: pre, post, by simp [hs], ?_⟩
        simp only [List.length_cons, hl]
        simpa using Option.some.inj h

theorem indexOfNode_eq_none {l : List NodeId} {n : NodeId} (h : indexOfNode l n = none) :
    n ∉ l := by
  intro hm
  rw [indexOfNode, List.findIdx?_eq_none_iff] at h
  simpa using h n hm

/-! ### `:nth-*()` の照合 -/

/-- `:nth-*()` が数える列。 -/
def nthPoolOf (ctx : MatchCtx) (d : NodeData) (kind : NthKind)
    (ofSel : Option (List Complex)) (n : NodeId) : List NodeId :=
  match kind with
  | .child | .lastChild =>
    match ofSel with
    | none => elementSiblings ctx.tree n
    | some l => (elementSiblings ctx.tree n).filter (fun m => matchSelList ctx l m)
  | .ofType | .lastOfType => (elementSiblings ctx.tree n).filter (sameTypeAs ctx.tree d)

/--
`:nth-*()` が数える列の**中身**を、仕様の語彙で言ったもの。

`nthPoolOf` は実行側の `pool` をそのまま写したものなので、それだけでは
「何を数えるか」を仕様から独立に固定したことにならない。この述語と
`mem_nthPoolOf_iff` を挟むことで、中身の側は inclusive element sibling と
same type という仕様の語彙で決まる。並びの側は `matchSimple_nth_iff` が
`pre ++ n :: post` の形で押さえている。
-/
def NthPoolMember (ctx : MatchCtx) (d : NodeData) (kind : NthKind)
    (ofSel : Option (List Complex)) (n m : NodeId) : Prop :=
  InclusiveElementSibling ctx.tree m n ∧
    match kind with
    | .ofType | .lastOfType => SameType ctx.tree d m
    | _ =>
      match ofSel with
      | none => True
      | some l => matchSelList ctx l m = true

/-- `:nth-last-child()` と `:nth-last-of-type()` は末尾から数える。 -/
def countsFromEnd : NthKind -> Bool
  | .lastChild | .lastOfType => true
  | _ => false

/-- 数える列と向きを与えたときの、位置の条件。これが `:nth-*()` の中身である。 -/
theorem nth_index_iff {pool : List NodeId} {n : NodeId} {ab : AnB} (hnd : pool.Nodup)
    (fromEnd : Bool) :
    (match indexOfNode (if fromEnd then pool.reverse else pool) n with
      | none => false
      | some i => anbMatches ab (i + 1)) = true ↔
      ∃ pre post, pool = pre ++ n :: post ∧
        AnBIndex ab (if fromEnd then post.length + 1 else pre.length + 1) := by
  cases fromEnd with
  | false =>
    simp only [if_false, Bool.false_eq_true]
    cases hi : indexOfNode pool n with
    | none =>
      simp only [Bool.false_eq_true, false_iff]
      rintro ⟨pre, post, hs, _⟩
      exact absurd (hs ▸ List.mem_append_right pre List.mem_cons_self) (indexOfNode_eq_none hi)
    | some i =>
      rw [anbMatches_iff]
      constructor
      · intro hab
        obtain ⟨pre, post, hs, hlen⟩ := indexOfNode_eq_some pool n i hi
        exact ⟨pre, post, hs, by simpa [hlen] using hab⟩
      · rintro ⟨pre, post, hs, hab⟩
        have hnp : n ∉ pre := by
          rw [hs, List.nodup_append] at hnd
          exact fun hm => hnd.2.2 n hm n List.mem_cons_self rfl
        rw [hs, indexOfNode_of_split pre post n hnp] at hi
        simpa [← Option.some.inj hi] using hab
  | true =>
    simp only [if_true]
    cases hi : indexOfNode pool.reverse n with
    | none =>
      simp only [Bool.false_eq_true, false_iff]
      rintro ⟨pre, post, hs, _⟩
      refine absurd ?_ (indexOfNode_eq_none hi)
      rw [hs]
      simp
    | some i =>
      rw [anbMatches_iff]
      constructor
      · intro hab
        obtain ⟨pre, post, hs, hlen⟩ := indexOfNode_eq_some pool.reverse n i hi
        refine ⟨post.reverse, pre.reverse, ?_, ?_⟩
        · have := congrArg List.reverse hs
          simpa using this
        · simpa [hlen] using hab
      · rintro ⟨pre, post, hs, hab⟩
        have hrev : pool.reverse = post.reverse ++ n :: pre.reverse := by rw [hs]; simp
        have hnp : n ∉ post.reverse := by
          rw [hs, List.nodup_append] at hnd
          have hd2 := hnd.2.1
          rw [List.nodup_cons] at hd2
          simpa using hd2.1
        rw [hrev, indexOfNode_of_split post.reverse pre.reverse n hnp] at hi
        simpa [← Option.some.inj hi] using hab

/-- **数える列に入るのはちょうど、仕様が言う「inclusive sibling で S に当たるもの」である。** -/
theorem mem_nthPoolOf_iff {t : Tree} (hwf : WellFormed t) {ctx : MatchCtx}
    (hctx : ctx.tree = t) {n : NodeId} (hn : isElementNode t n = true) (d : NodeData)
    (kind : NthKind) (ofSel : Option (List Complex)) (m : NodeId) :
    m ∈ nthPoolOf ctx d kind ofSel n ↔ NthPoolMember ctx d kind ofSel n m := by
  subst hctx
  unfold nthPoolOf NthPoolMember
  cases kind with
  | child =>
    cases ofSel with
    | none => simpa using (mem_elementSiblings_iff hwf hn m)
    | some l => rw [List.mem_filter, mem_elementSiblings_iff hwf hn m]
  | lastChild =>
    cases ofSel with
    | none => simpa using (mem_elementSiblings_iff hwf hn m)
    | some l => rw [List.mem_filter, mem_elementSiblings_iff hwf hn m]
  | ofType =>
    rw [List.mem_filter, mem_elementSiblings_iff hwf hn m, sameTypeAs_iff]
  | lastOfType =>
    rw [List.mem_filter, mem_elementSiblings_iff hwf hn m, sameTypeAs_iff]

/--
**`:nth-*()` は、数える列の中での 1 始まりの位置が `An+B` に当たることと同値である。**

`:nth-last-*()` では末尾からの位置になる。
-/
theorem matchSimple_nth_iff {ctx : MatchCtx} {n : NodeId} {d : NodeData}
    {kind : NthKind} {ab : AnB} {ofSel : Option (List Complex)}
    (hd : ctx.tree.get? n = some d) (hel : d.kind = NodeKind.element)
    (hnd : (nthPoolOf ctx d kind ofSel n).Nodup) :
    matchSimple ctx (.nth kind ab ofSel) n = true ↔
      ∃ pre post, nthPoolOf ctx d kind ofSel n = pre ++ n :: post ∧
        AnBIndex ab (if countsFromEnd kind then post.length + 1 else pre.length + 1) := by
  have hne : (d.kind != NodeKind.element) = false := by simp [hel]
  rw [matchSimple, hd]
  simp only [hne, Bool.false_eq_true, if_false]
  cases kind with
  | child => exact nth_index_iff hnd false
  | lastChild => exact nth_index_iff hnd true
  | ofType => exact nth_index_iff hnd false
  | lastOfType => exact nth_index_iff hnd true

/-! ## type selector・`:root`・`:empty`

Selectors §6.1 は、名前の照合を既定で "identical to"（大文字小文字を区別する）とし、
host language が別に定めたときだけ違う、とする。HTML は HTML namespace の element に
ついて別に定めるが、それは **selector の側を ASCII lowercase して local name と比べる**
規則であって、対称な case-insensitive ではない。仕様自身が「ほぼ同じ」と註記しており、
script で作った大文字の local name は selector で当たらない。

§6.1 の white space は SPACE / TAB / LF / CR / FF で、`Infra.isAsciiWhitespace` と同じである。
-/

/-- HTML の規則が効く条件。HTML namespace の element が HTML document にあること。 -/
def HtmlElementInHtmlDocument (t : Tree) (d : NodeData) : Prop :=
  d.namespace = some htmlNamespace ∧
    ∃ doc, t.get? d.ownerDocument = some doc ∧ doc.isHTMLDocument = true

/-- §6.1 の type selector。 -/
def TypeSelectorMatches (t : Tree) (d : NodeData) (name : String) : Prop :=
  (HtmlElementInHtmlDocument t d ∧ asciiLowercase name = d.localName) ∨
    (¬ HtmlElementInHtmlDocument t d ∧ name = d.localName)

/-- **type selector は仕様どおり、HTML の element だけ selector 側を lowercase して比べる。** -/
theorem typeHolds_iff (t : Tree) (d : NodeData) (name : String) :
    typeHolds t d name = true ↔ TypeSelectorMatches t d name := by
  unfold typeHolds TypeSelectorMatches HtmlElementInHtmlDocument isHTMLDocumentOf
  by_cases hns : d.namespace = some htmlNamespace
  · cases hdoc : t.get? d.ownerDocument with
    | none => simp [hns]
    | some doc =>
      by_cases hh : doc.isHTMLDocument = true
      · simp [hns, hh]
      · simp [hns, hh]
  · simp [hns]

/-- §14.1 の `:root`。document の root、すなわち parent が Document である element。 -/
def IsDocumentRoot (t : Tree) (n : NodeId) : Prop :=
  ∃ p, parentOf t n = some p ∧ kindOf t p = some NodeKind.document

/-- **`:root` は parent が Document である element にちょうど当たる。** -/
theorem matchSimple_root_iff {ctx : MatchCtx} {n : NodeId} {d : NodeData}
    (hd : ctx.tree.get? n = some d) (hel : d.kind = NodeKind.element) :
    matchSimple ctx .root n = true ↔ IsDocumentRoot ctx.tree n := by
  have hne : (d.kind != NodeKind.element) = false := by simp [hel]
  rw [matchSimple, hd]
  simp only [hne, Bool.false_eq_true, if_false]
  unfold IsDocumentRoot
  cases hp : parentOf ctx.tree n with
  | none => simp
  | some p => simp

/--
§14.2 の `:empty` を壊さない子。

> an element that has no children except, optionally, document white space characters

同じ節の後段は「data の長さが 0 でない content node は emptiness に影響する」と書いており、
前段の「空白だけなら影響しない」と食い違う。model は**前段**に従う。
実装はどちらも後段に留まっている（`docs/status.md` の findings 19）。
-/
def EmptyIgnorable (t : Tree) (c : NodeId) : Prop :=
  ∀ d, t.get? c = some d →
    d.kind = NodeKind.comment ∨ d.kind = NodeKind.processingInstruction ∨
      ((d.kind = NodeKind.text ∨ d.kind = NodeKind.cdataSection) ∧
        ∀ ch ∈ d.data.toList, isAsciiWhitespace ch = true)

theorem emptyOk_iff (t : Tree) (c : NodeId) : emptyOk t c = true ↔ EmptyIgnorable t c := by
  unfold emptyOk EmptyIgnorable
  cases hc : t.get? c with
  | none => simp
  | some d => cases hk : d.kind <;> simp [hk]

/-- **`:empty` は、どの子も emptiness を壊さないことにちょうど当たる。** -/
theorem matchSimple_empty_iff {ctx : MatchCtx} {n : NodeId} {d : NodeData}
    (hd : ctx.tree.get? n = some d) (hel : d.kind = NodeKind.element) :
    matchSimple ctx .empty n = true ↔
      ∀ c ∈ childrenOf ctx.tree n, EmptyIgnorable ctx.tree c := by
  have hne : (d.kind != NodeKind.element) = false := by simp [hel]
  rw [matchSimple, hd]
  simp only [hne, Bool.false_eq_true, if_false, List.all_eq_true]
  constructor
  · intro h c hc
    exact (emptyOk_iff ctx.tree c).mp (h c hc)
  · intro h c hc
    exact (emptyOk_iff ctx.tree c).mpr (h c hc)

/-! ## `:has()` の候補と attribute の namespace

`:has()` の引数は relative selector で、anchor は `:has()` を付けた element である。
combinator は `>` だけでなく `+` や `~` も書けるので、**候補は anchor の部分木に
限らない**。同じ木のどの element でもよい。

attribute の namespace は §6.3 が定める。`[att]` は namespace を持たない attribute
だけに当たり、`[*|att]` は問わない。class と id も namespace を持たない attribute である
（§6.5・§6.6）。名前の大文字小文字は type selector と同じ非対称の規則に従う。
-/

theorem get?_root {t : Tree} (hwf : WellFormed t) {n : NodeId} {d : NodeData}
    (hd : t.get? n = some d) : ∃ r, t.get? (root t n) = some r := by
  rcases root_inclusive_ancestor t n with h | h
  · exact ⟨d, by rw [h]; exact hd⟩
  · exact exists_data_of_ancestor' hwf h

/-- **`:has()` の候補は同じ木の element すべてである。部分木には限らない。** -/
theorem matchSimple_has_iff {ctx : MatchCtx} (hwf : WellFormed ctx.tree) {n : NodeId}
    {d : NodeData} (hd : ctx.tree.get? n = some d) (hel : d.kind = NodeKind.element)
    (l : List Complex) :
    matchSimple ctx (.has l) n = true ↔
      ∃ c, InclusiveDescendant ctx.tree c (root ctx.tree n) ∧
        matchSelList { ctx with anchor := some n } l c = true := by
  have hne : (d.kind != NodeKind.element) = false := by simp [hel]
  rw [matchSimple, hd]
  simp only [hne, Bool.false_eq_true, if_false, List.any_eq_true]
  obtain ⟨r, hr⟩ := get?_root hwf hd
  constructor
  · rintro ⟨c, hc, hm⟩
    exact ⟨c, (mem_preorder_iff hwf hr c).mp hc, hm⟩
  · rintro ⟨c, hc, hm⟩
    exact ⟨c, (mem_preorder_iff hwf hr c).mpr hc, hm⟩

/-- §6.3 の attribute 名の照合。type selector と同じ非対称の規則である。 -/
def AttrNameMatches (t : Tree) (d : NodeData) (name : String) (a : Attr) : Prop :=
  (HtmlElementInHtmlDocument t d ∧ a.localName = asciiLowercase name) ∨
    (¬ HtmlElementInHtmlDocument t d ∧ a.localName = name)

/-- `[att]` は namespace を持たない attribute だけ、`[*|att]` は問わない。 -/
def SelectorAttrMatches (t : Tree) (d : NodeData) (anyNs : Bool) (name : String) (a : Attr) :
    Prop :=
  AttrNameMatches t d name a ∧ (anyNs = true ∨ a.namespace = none)

theorem attrNameInSelector_spec (t : Tree) (d : NodeData) (name : String) (a : Attr) :
    (a.localName == attrNameInSelector t d name) = true ↔ AttrNameMatches t d name a := by
  unfold attrNameInSelector AttrNameMatches HtmlElementInHtmlDocument isHTMLDocumentOf
  by_cases hns : d.namespace = some htmlNamespace
  · cases hdoc : t.get? d.ownerDocument with
    | none => simp [hns]
    | some doc =>
      by_cases hh : doc.isHTMLDocument = true
      · simp [hns, hh]
      · simp [hns, hh]
  · simp [hns]

/-- **`[att]` が返すのは、仕様の条件を満たす attribute である。** -/
theorem selectorAttr_some {t : Tree} {d : NodeData} {anyNs : Bool} {name : String} {a : Attr}
    (h : selectorAttr t d anyNs name = some a) :
    a ∈ d.attributes ∧ SelectorAttrMatches t d anyNs name a := by
  unfold selectorAttr at h
  obtain ⟨hp, _⟩ := List.find?_eq_some_iff_append.mp h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Option.isNone_iff_eq_none] at hp
  exact ⟨List.mem_of_find?_eq_some h,
    (attrNameInSelector_spec t d name a).mp hp.1, hp.2⟩

/-- **`[att]` が何も返さないなら、条件を満たす attribute は無い。** -/
theorem selectorAttr_none {t : Tree} {d : NodeData} {anyNs : Bool} {name : String}
    (h : selectorAttr t d anyNs name = none) :
    ∀ a ∈ d.attributes, ¬ SelectorAttrMatches t d anyNs name a := by
  unfold selectorAttr at h
  intro a ha hmatch
  have := List.find?_eq_none.mp h a ha
  simp only [Bool.and_eq_true, Bool.or_eq_true, Option.isNone_iff_eq_none, not_and] at this
  exact this ((attrNameInSelector_spec t d name a).mpr hmatch.1) hmatch.2

/-- **class と id は namespace を持たない attribute を見る。** -/
theorem plainAttr_some {d : NodeData} {name v : String} (h : plainAttr d name = some v) :
    ∃ a ∈ d.attributes, a.localName = name ∧ a.namespace = none ∧ a.value = v := by
  unfold plainAttr at h
  cases hf : d.attributes.find? (fun a => a.localName == name && a.namespace.isNone) with
  | none => rw [hf] at h; simp at h
  | some a =>
    rw [hf] at h
    obtain ⟨hp, _⟩ := List.find?_eq_some_iff_append.mp hf
    simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at hp
    exact ⟨a, List.mem_of_find?_eq_some hf, hp.1, hp.2, by simpa using h⟩

theorem plainAttr_none {d : NodeData} {name : String} (h : plainAttr d name = none) :
    ∀ a ∈ d.attributes, ¬ (a.localName = name ∧ a.namespace = none) := by
  unfold plainAttr at h
  cases hf : d.attributes.find? (fun a => a.localName == name && a.namespace.isNone) with
  | some a => rw [hf] at h; simp at h
  | none =>
    intro a ha hm
    have := List.find?_eq_none.mp hf a ha
    simp only [Bool.and_eq_true, not_and, beq_iff_eq, Option.isNone_iff_eq_none] at this
    exact this hm.1 hm.2

/-! ### 存在との同値（利用側のためのまとめ） -/

/--
**`[att]` が当たる attribute があることと、`selectorAttr` が返すことは同値である。**

健全性（`selectorAttr_some`）と不在（`selectorAttr_none`）を一つにしたもの。
使う側はこちらだけで済む。
-/
theorem selectorAttr_isSome_iff {t : Tree} {d : NodeData} {anyNs : Bool} {name : String} :
    (selectorAttr t d anyNs name).isSome = true ↔
      ∃ a ∈ d.attributes, SelectorAttrMatches t d anyNs name a := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨hmem, hmatch⟩ := selectorAttr_some ha
    exact ⟨a, hmem, hmatch⟩
  · rintro ⟨a, hmem, hmatch⟩
    cases hs : selectorAttr t d anyNs name with
    | none => exact absurd hmatch (selectorAttr_none hs a hmem)
    | some b => simp

/-- **class / id も同じ形でまとめる。** -/
theorem plainAttr_isSome_iff {d : NodeData} {name : String} :
    (plainAttr d name).isSome = true ↔
      ∃ a ∈ d.attributes, a.localName = name ∧ a.namespace = none := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨a, hmem, hn, hns, -⟩ := plainAttr_some hv
    exact ⟨a, hmem, hn, hns⟩
  · rintro ⟨a, hmem, hn, hns⟩
    cases hs : plainAttr d name with
    | none => exact absurd ⟨hn, hns⟩ (plainAttr_none hs a hmem)
    | some v => simp

end Dom.Spec
