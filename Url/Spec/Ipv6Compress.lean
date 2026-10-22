import Url.Ipv6

/-!
# IPv6 の圧縮位置（§3.5）

§3.5 IPv6 serializer は「find the IPv6 address compressed piece index」の結果の位置を `::` で省く。
本文はこれを algorithm として書いている。四つの変数（いちばん長い並びの位置と長さ、いま数えている並びの
位置と長さ）を持って左から一度だけ走り、長さの初期値を 1 にして「より長い」ときだけ置き換える。
実装の `ipv6CompressIndex`（`Url/Ipv6.lean`）はその写しである。

その algorithm が何を求めているかは、本文には例しか無い。ここでは RFC 5952 §4.2.2-4.2.3 の言い方で書く。
`zeroRun a j` は添字 `j` から始まる 0 の並びの長さで、

* 圧縮位置は、`zeroRun` が最大で 2 以上になる添字のうち最初のもの（`CompressAt`）。
  一番長い並びを省き、同じ長さなら最初の並びを省く（RFC 5952 §4.2.3）。
* そういう添字が無い（どの `zeroRun` も 1 以下）なら null。0 が一つだけなら `::` にしない（§4.2.2）。

`ipv6CompressIndex_iff` と `ipv6CompressIndex_none_iff` が、本文の algorithm はこれを計算すると言う。
address の長さは仮定しない。
-/

namespace Url.Spec

open Url

/-- 添字 `j` から始まる 0 の並びの長さ。 -/
def zeroRun (a : Ipv6) (j : Nat) : Nat := ((a.drop j).takeWhile (· == 0)).length

/-- **§3.5 の圧縮位置。** 0 の並びが最も長く（2 以上で）始まる添字のうち、最初のもの。 -/
def CompressAt (a : Ipv6) (c : Nat) : Prop :=
  2 ≤ zeroRun a c ∧ (∀ j, zeroRun a j ≤ zeroRun a c) ∧ ∀ j < c, zeroRun a j < zeroRun a c

/-- 圧縮位置は一つしかない。 -/
theorem CompressAt.unique {a : Ipv6} {c c' : Nat} (h : CompressAt a c) (h' : CompressAt a c') :
    c = c' := by
  rcases Nat.lt_trichotomy c c' with hlt | heq | hgt
  · have := h'.2.2 c hlt; have := h.2.1 c'; omega
  · exact heq
  · have := h.2.2 c' hgt; have := h'.2.1 c; omega

/-! ## `zeroRun` の再帰 -/

theorem zeroRun_eq (a : Ipv6) (j : Nat) :
    zeroRun a j = if a[j]? = some 0 then zeroRun a (j + 1) + 1 else 0 := by
  unfold zeroRun
  by_cases hj : j < a.length
  · rw [List.drop_eq_getElem_cons hj, List.getElem?_eq_getElem hj]
    by_cases h0 : a[j] = 0
    · simp only [List.takeWhile_cons, h0, beq_self_eq_true, if_true, List.length_cons]
    · simp only [List.takeWhile_cons, h0, Option.some.injEq, if_false]
      rw [if_neg (by simpa using h0)]; rfl
  · rw [List.drop_eq_nil_of_le (by omega), List.getElem?_eq_none (by omega)]
    simp

theorem zeroRun_of_ne {a : Ipv6} {j : Nat} (h : a[j]? ≠ some 0) : zeroRun a j = 0 := by
  rw [zeroRun_eq, if_neg h]

/-- 0 が続く区間では、`zeroRun` は区間の終わりまでの距離だけ長い。 -/
theorem zeroRun_block {a : Ipv6} {s k : Nat} (hz : ∀ j, s ≤ j → j < k → a[j]? = some 0) :
    ∀ d j, j + d = k → s ≤ j → zeroRun a j = d + zeroRun a k
  | 0, j, h, _ => by subst h; simp
  | d + 1, j, h, hs => by
    rw [zeroRun_eq, if_pos (hz j hs (by omega)), zeroRun_block hz d (j + 1) (by omega) (by omega)]
    omega

/-! ## 畳み込みの不変条件 -/

/-- 実装の畳み込みの一歩。 -/
def compressStep (st : Option Nat × Nat × Option Nat × Nat) (pi : Nat × Nat) :
    Option Nat × Nat × Option Nat × Nat :=
  let (longestIndex, longestSize, foundIndex, foundSize) := st
  if pi.1 != 0 then
    if foundSize > longestSize then (foundIndex, foundSize, none, 0)
    else (longestIndex, longestSize, none, 0)
  else
    (longestIndex, longestSize,
      (match foundIndex with | none => some pi.2 | some i => some i), foundSize + 1)

theorem compressStep_ne {li fi : Option Nat} {ls fs p k : Nat} (h : p ≠ 0) :
    compressStep (li, ls, fi, fs) (p, k)
      = if fs > ls then (fi, fs, none, 0) else (li, ls, none, 0) := by
  simp [compressStep, h]

theorem compressStep_zero (li fi : Option Nat) (ls fs k : Nat) :
    compressStep (li, ls, fi, fs) (0, k) = (li, ls, some (fi.getD k), fs + 1) := by
  cases fi <;> simp [compressStep]

theorem ipv6CompressIndex_eq (a : Ipv6) :
    ipv6CompressIndex a =
      let final := a.zipIdx.foldl compressStep (none, 1, none, 0)
      if final.2.2.2 > final.2.1 then final.2.2.1 else final.1 := by
  unfold ipv6CompressIndex
  rfl

/-- 添字 `s` より前で、いちばん長い並びが `li`（長さ `ls`）である。2 以上の並びが無ければ `none` で `ls = 1`。 -/
def CompressBest (a : Ipv6) (s : Nat) (li : Option Nat) (ls : Nat) : Prop :=
  (li = none ∧ ls = 1 ∧ ∀ j < s, zeroRun a j ≤ 1) ∨
  (∃ c, li = some c ∧ c < s ∧ zeroRun a c = ls ∧ 2 ≤ ls ∧
    (∀ j < s, zeroRun a j ≤ ls) ∧ ∀ j < c, zeroRun a j < ls)

/-- 添字 `k` まで読んだときの状態。数えている並びは `k - fs` から `k` の手前までである。 -/
def CompressInv (a : Ipv6) (k : Nat) (st : Option Nat × Nat × Option Nat × Nat) : Prop :=
  st.2.2.2 ≤ k ∧ (∀ j, k - st.2.2.2 ≤ j → j < k → a[j]? = some 0) ∧
  st.2.2.1 = (if st.2.2.2 = 0 then none else some (k - st.2.2.2)) ∧
  CompressBest a (k - st.2.2.2) st.1 st.2.1

/-- 0 の並びが閉じたとき、その並びの中の添字の `zeroRun` は並びの先頭が最大である。 -/
theorem closed_block {a : Ipv6} {s k : Nat} (_hsk : s ≤ k)
    (hz : ∀ j, s ≤ j → j < k → a[j]? = some 0) (hend : zeroRun a k = 0) :
    ∀ j, s ≤ j → j ≤ k → zeroRun a j = k - j := by
  intro j hs hk
  rw [zeroRun_block hz (k - j) j (by omega) hs, hend]
  omega

theorem inv_step {a : Ipv6} {k : Nat} {st : Option Nat × Nat × Option Nat × Nat} (hk : k < a.length)
    (h : CompressInv a k st) : CompressInv a (k + 1) (compressStep st (a[k], k)) := by
  obtain ⟨li, ls, fi, fs⟩ := st
  obtain ⟨hfs, hz, hfi, hb⟩ := h
  simp only at hfs hz hfi hb
  by_cases h0 : a[k] = 0
  · rw [h0, compressStep_zero]
    refine ⟨by dsimp only; omega, ?_, ?_, ?_⟩
    · intro j h1 h2
      dsimp only at h1
      by_cases hjk : j = k
      · subst hjk; simp [List.getElem?_eq_getElem hk, h0]
      · exact hz j (by omega) (by omega)
    · dsimp only
      rw [if_neg (by omega)]
      cases fi with
      | none =>
        have : fs = 0 := by
          by_cases hc : fs = 0
          · exact hc
          · rw [if_neg hc] at hfi; cases hfi
        subst this
        simp
      | some i =>
        have hne : fs ≠ 0 := by intro hc; rw [if_pos hc] at hfi; cases hfi
        rw [if_neg hne] at hfi
        simp only [Option.some.injEq, Option.getD_some] at hfi ⊢; omega
    · dsimp only
      rw [show k + 1 - (fs + 1) = k - fs by omega]
      exact hb
  · rw [compressStep_ne h0]
    -- 並び `k - fs .. k` が閉じる
    have hend : zeroRun a k = 0 := zeroRun_of_ne (by simp [List.getElem?_eq_getElem hk, h0])
    have hcl := closed_block (s := k - fs) (by omega) hz hend
    have hrun : ∀ j, k - fs ≤ j → j < k + 1 → zeroRun a j ≤ fs := by
      intro j h1 h2; rw [hcl j h1 (by omega)]; omega
    by_cases hgt : fs > ls
    · rw [if_pos hgt]
      refine ⟨by simp, fun j h1 h2 => by simp at h1; omega, by simp, ?_⟩
      dsimp only
      simp only [Nat.sub_zero]
      have hls1 : 1 ≤ ls := by
        rcases hb with ⟨_, h1, _⟩ | ⟨_, _, _, _, h2, _⟩ <;> omega
      have hlt : ∀ j < k - fs, zeroRun a j < fs := by
        intro j hj
        rcases hb with ⟨_, h1, hall⟩ | ⟨_, _, _, _, _, hall, _⟩
        · have := hall j hj; omega
        · have := hall j hj; omega
      right
      refine ⟨k - fs, ?_, by omega, ?_, by omega, ?_, hlt⟩
      · rw [if_neg (by omega)] at hfi; exact hfi
      · rw [hcl (k - fs) (by omega) (by omega)]; omega
      · intro j hj
        by_cases hjs : j < k - fs
        · exact Nat.le_of_lt (hlt j hjs)
        · exact hrun j (by omega) hj
    · rw [if_neg hgt]
      refine ⟨by simp, fun j h1 h2 => by simp at h1; omega, by simp, ?_⟩
      dsimp only
      simp only [Nat.sub_zero]
      rcases hb with ⟨h1, h2, hall⟩ | ⟨c, h1, h2, h3, h4, hall, h5⟩
      · left
        refine ⟨h1, h2, fun j hj => ?_⟩
        by_cases hjs : j < k - fs
        · exact hall j hjs
        · have := hrun j (by omega) hj; omega
      · right
        refine ⟨c, h1, by omega, h3, h4, fun j hj => ?_, h5⟩
        by_cases hjs : j < k - fs
        · exact hall j hjs
        · have := hrun j (by omega) hj; omega

theorem inv_fold (a : Ipv6) : ∀ (m k : Nat) (st : Option Nat × Nat × Option Nat × Nat),
    k + m = a.length → CompressInv a k st →
    CompressInv a a.length (((a.drop k).zipIdx k).foldl compressStep st)
  | 0, k, st, hm, h => by
    rw [List.drop_eq_nil_of_le (by omega)]
    simp only [List.zipIdx_nil, List.foldl_nil]
    rw [← show k = a.length by omega]; exact h
  | m + 1, k, st, hm, h => by
    have hk : k < a.length := by omega
    rw [List.drop_eq_getElem_cons hk, List.zipIdx_cons, List.foldl_cons]
    exact inv_fold a m (k + 1) _ (by omega) (inv_step hk h)

/-! ## 実装は本文を計算する -/

theorem ipv6CompressIndex_spec (a : Ipv6) :
    (∀ c, ipv6CompressIndex a = some c → CompressAt a c) ∧
    (ipv6CompressIndex a = none → ∀ j, zeroRun a j ≤ 1) := by
  have h0 : CompressInv a 0 (none, 1, none, 0) :=
    ⟨by simp, fun j h1 h2 => by simp at h2, by simp, Or.inl ⟨rfl, rfl, fun j hj => by simp at hj⟩⟩
  have hinv := inv_fold a a.length 0 _ (by omega) h0
  rw [List.drop_zero] at hinv
  have hz : (a.zipIdx 0) = a.zipIdx := rfl
  rw [hz] at hinv
  rw [ipv6CompressIndex_eq]
  generalize a.zipIdx.foldl compressStep (none, 1, none, 0) = st at hinv ⊢
  obtain ⟨li, ls, fi, fs⟩ := st
  obtain ⟨hfs, hzr, hfi, hb⟩ := hinv
  simp only at hfs hzr hfi hb ⊢
  -- 最後の並び `n - fs .. n` は末尾で閉じる
  have hend : zeroRun a a.length = 0 := zeroRun_of_ne (by simp)
  have hcl := closed_block (s := a.length - fs) (by omega) hzr hend
  have hrun : ∀ j, a.length - fs ≤ j → zeroRun a j ≤ fs := by
    intro j h1
    by_cases hj : j ≤ a.length
    · rw [hcl j h1 hj]; omega
    · rw [zeroRun_of_ne (by rw [List.getElem?_eq_none (by omega)]; simp)]; omega
  have hls1 : 1 ≤ ls := by
    rcases hb with ⟨_, h1, _⟩ | ⟨_, _, _, _, h2, _⟩ <;> omega
  by_cases hgt : fs > ls
  · rw [if_pos hgt]
    rw [if_neg (by omega)] at hfi
    rw [hfi]
    refine ⟨fun c hc => ?_, fun h => by cases h⟩
    cases hc
    have hlt : ∀ j < a.length - fs, zeroRun a j < fs := by
      intro j hj
      rcases hb with ⟨_, _, hall⟩ | ⟨_, _, _, _, _, hall, _⟩
      · have := hall j hj; omega
      · have := hall j hj; omega
    have hs : zeroRun a (a.length - fs) = fs := by
      rw [hcl (a.length - fs) (by omega) (by omega)]; omega
    refine ⟨by omega, fun j => ?_, fun j hj => by rw [hs]; exact hlt j hj⟩
    rw [hs]
    by_cases hjs : j < a.length - fs
    · exact Nat.le_of_lt (hlt j hjs)
    · exact hrun j (by omega)
  · rw [if_neg hgt]
    rcases hb with ⟨h1, h2, hall⟩ | ⟨c, h1, h2, h3, h4, hall, h5⟩
    · rw [h1]
      refine ⟨fun c hc => (nomatch hc), fun _ j => ?_⟩
      by_cases hjs : j < a.length - fs
      · exact hall j hjs
      · have := hrun j (by omega); omega
    · rw [h1]
      refine ⟨fun c' hc' => ?_, fun h => by cases h⟩
      cases hc'
      refine ⟨by omega, fun j => ?_, fun j hj => by rw [h3]; exact h5 j hj⟩
      rw [h3]
      by_cases hjs : j < a.length - fs
      · exact hall j hjs
      · have := hrun j (by omega); omega

/-- **本文の algorithm が返す位置は、一番長い 0 の並び（長さ 2 以上）のうち最初のものの先頭である。** -/
theorem ipv6CompressIndex_iff (a : Ipv6) (c : Nat) :
    ipv6CompressIndex a = some c ↔ CompressAt a c := by
  obtain ⟨hs, hn⟩ := ipv6CompressIndex_spec a
  constructor
  · exact hs c
  · intro hc
    cases h : ipv6CompressIndex a with
    | none => have := hn h c; have := hc.1; omega
    | some c' => rw [(hs c' h).unique hc]

/-- **null を返すのは、長さ 2 以上の 0 の並びが無いときである。** -/
theorem ipv6CompressIndex_none_iff (a : Ipv6) :
    ipv6CompressIndex a = none ↔ ∀ j, zeroRun a j ≤ 1 := by
  obtain ⟨hs, hn⟩ := ipv6CompressIndex_spec a
  constructor
  · exact hn
  · intro hall
    cases h : ipv6CompressIndex a with
    | none => rfl
    | some c => have := (hs c h).1; have := hall c; omega

/-- 本文の例。`0:f:0:0:f:f:0:0` では二つ目の 0（添字 2）を指す。長さ 2 の並びが二つあり、最初のほうである。 -/
example : ipv6CompressIndex [0, 0xf, 0, 0, 0xf, 0xf, 0, 0] = some 2 := by decide

example : CompressAt [0, 0xf, 0, 0, 0xf, 0xf, 0, 0] 2 :=
  (ipv6CompressIndex_iff _ _).mp (by decide)

end Url.Spec
