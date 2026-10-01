import Infra.Spec.Utf8Decode
import Infra.Bits

/-!
# `utf8Decode` は関係仕様を満たす

`Infra/Spec/Utf8Decode.lean` の `Decodes` を、実行関数 `utf8Decode` が満たすことを示す。

復元規則を述べた `Chunk` の各規則が、`utf8Decode` の `match` の枝に一対一で対応する。
-/

namespace Infra.Spec

open Infra

/-! ## 仕様側の continuation byte 条件と実装関数の対応 -/

theorem continuationBits_some_iff (b : UInt8) (v : Nat) :
    continuationBits b = some v ↔ IsContinuation b ∧ ContinuationValue b = v := by
  have hlt := b.toNat_lt
  unfold continuationBits IsContinuation ContinuationValue
  rw [and_C0, and_3F, Nat.and_two_pow_sub_one_eq_mod _ 2]
  split <;> simp_all <;> omega

theorem continuationBits_none_iff (b : UInt8) :
    continuationBits b = none ↔ ¬ IsContinuation b := by
  have hlt := b.toNat_lt
  unfold continuationBits IsContinuation
  rw [and_C0, Nat.and_two_pow_sub_one_eq_mod _ 2]
  split <;> simp_all <;> omega

/-! ## 先頭 byte の形と Bool 条件の対応 -/

theorem isLead2_iff (b : UInt8) :
    IsLead2 b ↔ (decide (194 ≤ b.toNat) && decide (b.toNat ≤ 223)) = true := by
  simp [IsLead2, Bool.and_eq_true, decide_eq_true_eq]

theorem isLead3_iff (b : UInt8) :
    IsLead3 b ↔ (decide (224 ≤ b.toNat) && decide (b.toNat ≤ 239)) = true := by
  simp [IsLead3, Bool.and_eq_true, decide_eq_true_eq]

theorem isLead4_iff (b : UInt8) :
    IsLead4 b ↔ (decide (240 ≤ b.toNat) && decide (b.toNat ≤ 244)) = true := by
  simp [IsLead4, Bool.and_eq_true, decide_eq_true_eq]

/-- decoder の境界判定を使って表した `FirstCont3`。 -/
def FirstCont3B (n b1 : Nat) : Bool :=
  withinBoundary (if n == 0xE0 then 0xA0 else 0x80)
    (if n == 0xED then 0x9F else 0xBF) b1

/-- `FirstCont4` の Bool 版。 -/
def FirstCont4B (n b1 : Nat) : Bool :=
  withinBoundary (if n == 0xF0 then 0x90 else 0x80)
    (if n == 0xF4 then 0x8F else 0xBF) b1

theorem firstCont3_iff (n b1 : Nat) : FirstCont3 n b1 ↔ FirstCont3B n b1 = true := by
  simp [FirstCont3, FirstCont3B, withinBoundary, Bool.and_eq_true, decide_eq_true_eq]

theorem firstCont4_iff (n b1 : Nat) : FirstCont4 n b1 ↔ FirstCont4B n b1 = true := by
  simp [FirstCont4, FirstCont4B, withinBoundary, Bool.and_eq_true, decide_eq_true_eq]

/-! ## 組み立てた code point

decoder は bit 演算で code point を組み立てて `charOfScalar` に渡す。仕様は同じ値を
算術で書いている。両者が一致し、しかも組み立てた値が必ず Unicode scalar value である
（`charOfScalar` の fallback に落ちない）ことをここで示す。
-/

theorem charOfScalar_toNat_of {n : Nat} (h : isScalarValue n = true) :
    (charOfScalar n).toNat = n := by
  unfold charOfScalar
  rw [if_pos h]
  unfold isScalarValue at h
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h
  have hv : n.isValidChar := h
  simp [Char.ofNat, hv, Char.ofNatAux, Char.toNat]

theorem assemble2 {b : UInt8} {v1 : Nat} (h : IsLead2 b) (hv : v1 < 64) :
    (charOfScalar (((b.toNat &&& 0x1F) <<< 6) ||| v1)).toNat = (b.toNat - 0xC0) * 64 + v1 := by
  unfold IsLead2 at h
  rw [and_1F, Nat.shiftLeft_eq, lor_add (k := 6) hv, charOfScalar_toNat_of] <;>
    simp [isScalarValue] <;> omega

theorem assemble3 {b b1 : UInt8} {v2 : Nat} (h : IsLead3 b) (hb : FirstCont3 b.toNat b1.toNat)
    (hv : v2 < 64) :
    (charOfScalar (((b.toNat &&& 0x0F) <<< 12) ||| ((b1.toNat &&& 0x3F) <<< 6) ||| v2)).toNat
      = (b.toNat - 0xE0) * 4096 + (b1.toNat - 0x80) * 64 + v2 := by
  unfold IsLead3 at h
  unfold FirstCont3 at hb
  rw [and_0F, and_3F, Nat.shiftLeft_eq, Nat.shiftLeft_eq, lor3 (by omega) hv, charOfScalar_toNat_of] <;>
    by_cases h0 : b.toNat = 224 <;> by_cases h1 : b.toNat = 237 <;>
    simp_all [isScalarValue] <;> omega

theorem assemble4 {b b1 : UInt8} {v2 v3 : Nat} (h : IsLead4 b) (hb : FirstCont4 b.toNat b1.toNat)
    (hv2 : v2 < 64) (hv3 : v3 < 64) :
    (charOfScalar (((b.toNat &&& 0x07) <<< 18) ||| ((b1.toNat &&& 0x3F) <<< 12)
        ||| (v2 <<< 6) ||| v3)).toNat
      = (b.toNat - 0xF0) * 262144 + (b1.toNat - 0x80) * 4096 + v2 * 64 + v3 := by
  unfold IsLead4 at h
  unfold FirstCont4 at hb
  rw [and_07, and_3F, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq,
    lor4 (by omega) hv2 hv3, charOfScalar_toNat_of] <;>
    by_cases h0 : b.toNat = 240 <;> by_cases h1 : b.toNat = 244 <;>
    simp_all [isScalarValue] <;> omega

/-! ## 一歩分の復号 -/

/-- 非空入力では、decoder の先頭一歩が `Chunk` ひとつに対応する。 -/
theorem utf8Decode_head_spec (bs : Bytes) (hne : bs ≠ []) :
    ∃ c rest, utf8Decode bs = c :: utf8Decode rest ∧ Chunk bs c rest := by
  induction bs using utf8Decode.induct with
  | case1 =>
      contradiction
  | case2 b rest n hn ih =>
      rw [utf8Decode.eq_def]; dsimp only at *
      rw [if_pos hn]
      exact ⟨_, _, rfl, Chunk.ascii hn
        (charOfScalar_toNat_of (by simp [isScalarValue]; omega))⟩
  | case3 b n hlt hlead2 b1 rest' v1 hcb ih =>
      rw [utf8Decode.eq_def]; dsimp only at *
      rw [if_neg hlt, if_pos hlead2, hcb]
      obtain ⟨hcont, hv⟩ := (continuationBits_some_iff b1 v1).mp hcb
      have hl := (isLead2_iff b).mpr hlead2
      exact ⟨_, _, rfl, Chunk.lead2 v1 hl hcont hv
        (assemble2 hl (by unfold IsContinuation ContinuationValue at *; omega))⟩
  | case4 b n hlt hlead2 b1 rest' hcb ih =>
      rw [utf8Decode.eq_def]; dsimp only at *
      rw [if_neg hlt, if_pos hlead2, hcb]
      exact ⟨_, _, rfl, Chunk.lead2_cont_none ((isLead2_iff b).mpr hlead2)
        ((continuationBits_none_iff b1).mp hcb)⟩
  | case5 b n hlt hlead2 =>
      rw [utf8Decode.eq_def]; dsimp only at *
      rw [if_neg hlt, if_pos hlead2]
      exact ⟨_, _, by simp [utf8Decode], Chunk.lead2_eof ((isLead2_iff b).mpr hlead2)⟩
  | case6 b n hlt hnot2 hlead3 lo hi b1 b2 rest' hbc v2 hcb ih =>
      rw [utf8Decode.eq_def]; dsimp only at *
      simp only [n, lo, hi, dite_eq_ite] at hbc
      rw [if_neg hlt, if_neg hnot2, if_pos hlead3, if_pos hbc, hcb]
      obtain ⟨hcont, hv⟩ := (continuationBits_some_iff b2 v2).mp hcb
      have hl := (isLead3_iff b).mpr hlead3
      have hb := (firstCont3_iff b.toNat b1.toNat).mpr hbc
      exact ⟨_, _, rfl, Chunk.lead3 v2 hl hb hcont hv
        (assemble3 hl hb (by unfold IsContinuation ContinuationValue at *; omega))⟩
  | case7 b n hlt hnot2 hlead3 lo hi b1 b2 rest' hbc hcb ih =>
      rw [utf8Decode.eq_def]; dsimp only at *
      simp only [n, lo, hi, dite_eq_ite] at hbc
      rw [if_neg hlt, if_neg hnot2, if_pos hlead3, if_pos hbc, hcb]
      exact ⟨_, _, rfl, Chunk.lead3_b2_bad ((isLead3_iff b).mpr hlead3)
        ((firstCont3_iff b.toNat b1.toNat).mpr hbc)
        ((continuationBits_none_iff b2).mp hcb)⟩
  | case8 b n hlt hnot2 hlead3 lo hi b1 b2 rest' hbc ih =>
      rw [utf8Decode.eq_def]; dsimp only at *
      simp only [n, lo, hi, dite_eq_ite] at hbc
      rw [if_neg hlt, if_neg hnot2, if_pos hlead3, if_neg hbc]
      exact ⟨_, _, rfl, Chunk.lead3_b1_bad ((isLead3_iff b).mpr hlead3)
        (fun hc => hbc ((firstCont3_iff b.toNat b1.toNat).mp hc))⟩
  | case9 b n hlt hnot2 hlead3 lo hi b1 hbc =>
      rw [utf8Decode.eq_def]; dsimp only at *
      simp only [n, lo, hi, dite_eq_ite] at hbc
      rw [if_neg hlt, if_neg hnot2, if_pos hlead3, if_pos hbc]
      exact ⟨_, _, by simp [utf8Decode], Chunk.lead3_eof_b1_ok ((isLead3_iff b).mpr hlead3)
        ((firstCont3_iff b.toNat b1.toNat).mpr hbc)⟩
  | case10 b n hlt hnot2 hlead3 lo hi b1 hbc ih =>
      rw [utf8Decode.eq_def]; dsimp only at *
      simp only [n, lo, hi, dite_eq_ite] at hbc
      rw [if_neg hlt, if_neg hnot2, if_pos hlead3, if_neg hbc]
      exact ⟨_, _, rfl, Chunk.lead3_eof_b1_bad ((isLead3_iff b).mpr hlead3)
        (fun hc => hbc ((firstCont3_iff b.toNat b1.toNat).mp hc))⟩
  | case11 b n hlt hnot2 hlead3 =>
      rw [utf8Decode.eq_def]; dsimp only at *
      rw [if_neg hlt, if_neg hnot2, if_pos hlead3]
      exact ⟨_, _, by simp [utf8Decode], Chunk.lead3_eof ((isLead3_iff b).mpr hlead3)⟩
  | case12 b n hlt hnot2 hnot3 hlead4 lo hi b1 b2 b3 rest' hbc v2 v3 h3cb h2cb ih =>
      rw [utf8Decode.eq_def]; dsimp only at *
      simp only [n, lo, hi, dite_eq_ite] at hbc
      rw [if_neg hlt, if_neg hnot2, if_neg hnot3, if_pos hlead4, if_pos hbc, h2cb, h3cb]
      obtain ⟨hcont2, hv2⟩ := (continuationBits_some_iff b2 v2).mp h2cb
      obtain ⟨hcont3, hv3⟩ := (continuationBits_some_iff b3 v3).mp h3cb
      have hl := (isLead4_iff b).mpr hlead4
      have hb := (firstCont4_iff b.toNat b1.toNat).mpr hbc
      exact ⟨_, _, rfl, Chunk.lead4 v2 v3 hl hb hcont2 hv2 hcont3 hv3
        (assemble4 hl hb (by unfold IsContinuation ContinuationValue at *; omega)
          (by unfold IsContinuation ContinuationValue at *; omega))⟩
  | case13 b n hlt hnot2 hnot3 hlead4 lo hi b1 b2 b3 rest' hbc val h3cb h2cb ih =>
      rw [utf8Decode.eq_def]; dsimp only at *
      simp only [n, lo, hi, dite_eq_ite] at hbc
      rw [if_neg hlt, if_neg hnot2, if_neg hnot3, if_pos hlead4, if_pos hbc, h2cb, h3cb]
      obtain ⟨hcont2, hv2⟩ := (continuationBits_some_iff b2 val).mp h2cb
      exact ⟨_, _, rfl, Chunk.lead4_b3_bad val ((isLead4_iff b).mpr hlead4)
        ((firstCont4_iff b.toNat b1.toNat).mpr hbc) hcont2 hv2
        ((continuationBits_none_iff b3).mp h3cb)⟩
  | case14 b n hlt hnot2 hnot3 hlead4 lo hi b1 b2 b3 rest' hbc h2cb ih =>
      rw [utf8Decode.eq_def]; dsimp only at *
      simp only [n, lo, hi, dite_eq_ite] at hbc
      rw [if_neg hlt, if_neg hnot2, if_neg hnot3, if_pos hlead4, if_pos hbc, h2cb]
      exact ⟨_, _, rfl, Chunk.lead4_b2_bad ((isLead4_iff b).mpr hlead4)
        ((firstCont4_iff b.toNat b1.toNat).mpr hbc)
        ((continuationBits_none_iff b2).mp h2cb)⟩
  | case15 b n hlt hnot2 hnot3 hlead4 lo hi b1 b2 b3 rest' hbc ih =>
      rw [utf8Decode.eq_def]; dsimp only at *
      simp only [n, lo, hi, dite_eq_ite] at hbc
      rw [if_neg hlt, if_neg hnot2, if_neg hnot3, if_pos hlead4, if_neg hbc]
      exact ⟨_, _, rfl, Chunk.lead4_b1_bad ((isLead4_iff b).mpr hlead4)
        (fun hc => hbc ((firstCont4_iff b.toNat b1.toNat).mp hc))⟩
  | case16 b n hlt hnot2 hnot3 hlead4 lo hi b1 b2 hbc v1 h2cb =>
      rw [utf8Decode.eq_def]; dsimp only at *
      simp only [n, lo, hi, dite_eq_ite] at hbc
      rw [if_neg hlt, if_neg hnot2, if_neg hnot3, if_pos hlead4, if_pos hbc, h2cb]
      obtain ⟨hcont, hv⟩ := (continuationBits_some_iff b2 v1).mp h2cb
      exact ⟨_, _, by simp [utf8Decode], Chunk.lead4_eof_b1_ok2 v1 ((isLead4_iff b).mpr hlead4)
        ((firstCont4_iff b.toNat b1.toNat).mpr hbc) hcont hv⟩
  | case17 b n hlt hnot2 hnot3 hlead4 lo hi b1 b2 hbc h2cb ih =>
      rw [utf8Decode.eq_def]; dsimp only at *
      simp only [n, lo, hi, dite_eq_ite] at hbc
      rw [if_neg hlt, if_neg hnot2, if_neg hnot3, if_pos hlead4, if_pos hbc, h2cb]
      exact ⟨_, _, rfl, Chunk.lead4_eof_b2_bad ((isLead4_iff b).mpr hlead4)
        ((firstCont4_iff b.toNat b1.toNat).mpr hbc)
        ((continuationBits_none_iff b2).mp h2cb)⟩
  | case18 b n hlt hnot2 hnot3 hlead4 lo hi b1 b2 hbc ih =>
      rw [utf8Decode.eq_def]; dsimp only at *
      simp only [n, lo, hi, dite_eq_ite] at hbc
      rw [if_neg hlt, if_neg hnot2, if_neg hnot3, if_pos hlead4, if_neg hbc]
      exact ⟨_, _, rfl, Chunk.lead4_eof_b1_bad2 ((isLead4_iff b).mpr hlead4)
        (fun hc => hbc ((firstCont4_iff b.toNat b1.toNat).mp hc))⟩
  | case19 b n hlt hnot2 hnot3 hlead4 lo hi b1 hbc =>
      rw [utf8Decode.eq_def]; dsimp only at *
      simp only [n, lo, hi, dite_eq_ite] at hbc
      rw [if_neg hlt, if_neg hnot2, if_neg hnot3, if_pos hlead4, if_pos hbc]
      exact ⟨_, _, by simp [utf8Decode], Chunk.lead4_eof_b1_ok ((isLead4_iff b).mpr hlead4)
        ((firstCont4_iff b.toNat b1.toNat).mpr hbc)⟩
  | case20 b n hlt hnot2 hnot3 hlead4 lo hi b1 hbc ih =>
      rw [utf8Decode.eq_def]; dsimp only at *
      simp only [n, lo, hi, dite_eq_ite] at hbc
      rw [if_neg hlt, if_neg hnot2, if_neg hnot3, if_pos hlead4, if_neg hbc]
      exact ⟨_, _, rfl, Chunk.lead4_eof_b1_bad ((isLead4_iff b).mpr hlead4)
        (fun hc => hbc ((firstCont4_iff b.toNat b1.toNat).mp hc))⟩
  | case21 b n hlt hnot2 hnot3 hlead4 =>
      rw [utf8Decode.eq_def]; dsimp only at *
      rw [if_neg hlt, if_neg hnot2, if_neg hnot3, if_pos hlead4]
      exact ⟨_, _, by simp [utf8Decode], Chunk.lead4_eof ((isLead4_iff b).mpr hlead4)⟩
  | case22 b rest n hlt hnot2 hnot3 hnot4 ih =>
      rw [utf8Decode.eq_def]; dsimp only at *
      rw [if_neg hlt, if_neg hnot2, if_neg hnot3, if_neg hnot4]
      refine ⟨replacementChar, rest, ?_, Chunk.invalid rest ?_⟩
      · rfl
      rintro (hc | hc | hc | hc)
      · exact hlt hc
      · exact hnot2 ((isLead2_iff b).mp hc)
      · exact hnot3 ((isLead3_iff b).mp hc)
      · exact hnot4 ((isLead4_iff b).mp hc)

/-! ## 全体の復号 -/

/-- `Chunk` は少なくとも 1 byte を消費する。 -/
theorem Chunk.rest_length_lt {bs bs' : Bytes} {c : Char} (h : Chunk bs c bs') :
    bs'.length < bs.length := by
  cases h <;> simp <;> omega

/-- **`utf8Decode` は `Decodes` を満たす。** 一歩分の補題を長さについて帰納する。 -/
theorem utf8Decode_spec (bs : Bytes) : Decodes bs (utf8Decode bs) := by
  suffices aux : ∀ n, ∀ bs : Bytes, bs.length = n → Decodes bs (utf8Decode bs) by
    exact aux bs.length bs rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro bs hlen
      cases bs with
      | nil =>
          simpa [utf8Decode] using Decodes.nil
      | cons b rest =>
          obtain ⟨c, tail, hstep, hchunk⟩ := utf8Decode_head_spec (b :: rest) (by simp)
          rw [hstep]
          have htail : tail.length < n := by
            rw [← hlen]
            exact Chunk.rest_length_lt hchunk
          exact Decodes.cons hchunk (ih tail.length htail tail rfl)

end Infra.Spec
