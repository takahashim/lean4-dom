import Selectors.Parser

/-!
# `An+B` の関係仕様（CSS Syntax §9）

`Selectors/Parser.lean` の `An+B` の部品 `signlessInt` / `digitsAfter` /
`parseB` / `identAnB` と、`parseAnB` / `parseAnBFull` を関係として書く。

関係は parser の関数を呼ばない。符号なし整数と「接頭辞の後ろの数字列」は
`SignlessInt` / `DigitsAfter` として入力の形で書き、`signlessInt_spec` /
`digitsAfter_spec` で実行関数と結ぶ。例外は先頭の空白を飛ばす `dropWs` で、
これは `dropWs_spec`（空白 token をいくつか剥がしたもの）で特徴づけたうえで使う。
-/

namespace Selectors.Spec

open Selectors
open Infra

/-! ## 空白・符号なし整数・数字列 -/

/-- **`dropWs` は先頭の空白 token をすべて剥がす。** 残りは空白で始まらない。 -/
theorem dropWs_spec (l l' : List Component) :
    dropWs l = l' ↔
      ∃ k, l = List.replicate k (Component.tok Token.whitespace) ++ l' ∧
        ∀ rest, l' ≠ Component.tok Token.whitespace :: rest := by
  induction l with
  | nil =>
    simp only [dropWs]
    constructor
    · rintro rfl; exact ⟨0, rfl, fun _ h => nomatch h⟩
    · rintro ⟨k, hk, _⟩
      cases k <;> simp_all
  | cons c rest ih =>
    by_cases hc : c = Component.tok Token.whitespace
    · subst hc
      simp only [dropWs]
      rw [ih]
      constructor
      · rintro ⟨k, hk, hn⟩; exact ⟨k + 1, by simp [hk, List.replicate_succ], hn⟩
      · rintro ⟨k, hk, hn⟩
        cases k with
        | zero => simp at hk; exact absurd hk.symm (hn rest)
        | succ k => exact ⟨k, by simpa [List.replicate_succ] using hk, hn⟩
    · have hd : dropWs (c :: rest) = c :: rest := by
        unfold dropWs; split
        · next h => exact absurd (List.cons.inj h).1 hc
        · rfl
      rw [hd]
      constructor
      · rintro rfl; exact ⟨0, rfl, fun r h => hc (List.cons.inj h).1⟩
      · rintro ⟨k, hk, hn⟩
        cases k with
        | zero => simpa using hk
        | succ k => exact absurd (List.cons.inj hk).1 hc

/-- 符号の無い整数 token がちょうど一つ。 -/
def SignlessInt (l : List Component) (v : Nat) (r : List Component) : Prop :=
  ∃ n : Num, l = Component.tok (Token.number n) :: r ∧ n.isInteger = true ∧
    n.sign = none ∧ 0 ≤ n.value ∧ v = n.value.toNat

/-- 文字列 `s` が接頭辞 `pre` と、空でない ASCII 数字列 `d`（値 `v`）からなる。 -/
def DigitsAfter (pre s : String) (v : Nat) : Prop :=
  ∃ d : List Char, s.toList = pre.toList ++ d ∧ d ≠ [] ∧
    (∀ c ∈ d, isAsciiDigit c = true) ∧ v = digitsToNat d

/-- **`signlessInt` は符号なし整数 token をちょうど読む。** -/
theorem signlessInt_spec (l : List Component) (v : Nat) (r : List Component) :
    signlessInt l = some (v, r) ↔ SignlessInt l v r := by
  unfold SignlessInt
  constructor
  · intro h
    unfold signlessInt at h
    split at h
    · next n rest =>
      split at h
      · next hc =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hv, hr⟩ := h
        subst hv; subst hr
        rw [Bool.and_eq_true, Bool.and_eq_true] at hc
        obtain ⟨⟨hi, hsn⟩, hge⟩ := hc
        rw [decide_eq_true_eq] at hge
        rw [Option.isNone_iff_eq_none] at hsn
        exact ⟨n, rfl, hi, hsn, hge, rfl⟩
      · simp at h
    · simp at h
  · rintro ⟨n, rfl, hi, hs, hge, rfl⟩
    simp only [signlessInt]
    simp [hi, hs, hge]

/-- **`digitsAfter` は接頭辞の後ろの数字列をちょうど読む。** -/
theorem digitsAfter_spec (pre s : String) (v : Nat) :
    digitsAfter pre s = some v ↔ DigitsAfter pre s v := by
  unfold DigitsAfter
  constructor
  · intro h
    unfold digitsAfter at h
    dsimp only at h
    split at h
    · next hpre =>
      split at h
      · next hnot => simp_all
      · next hd =>
        have hd' : ((s.toList.drop pre.toList.length).isEmpty ||
            !(s.toList.drop pre.toList.length).all isAsciiDigit) = false := by simpa using hd
        rw [Bool.or_eq_false_iff] at hd'
        obtain ⟨he, ha⟩ := hd'
        have hdne : (s.toList.drop pre.toList.length) ≠ [] := List.isEmpty_eq_false_iff.mp he
        have hdall : ∀ c ∈ s.toList.drop pre.toList.length, isAsciiDigit c = true :=
          List.all_eq_true.mp (by simpa using ha)
        refine ⟨s.toList.drop pre.toList.length, ?_, hdne, hdall, (Option.some.inj h).symm⟩
        conv => lhs; rw [show s.toList = List.take pre.toList.length s.toList ++
          List.drop pre.toList.length s.toList from
          (List.take_append_drop pre.toList.length s.toList).symm]
        rw [beq_iff_eq.mp hpre]
    · next hnot => simp_all
  · rintro ⟨d, hs, hdne, hdall, hv⟩
    subst hv
    unfold digitsAfter
    dsimp only
    have hempty : d.isEmpty = false := List.isEmpty_eq_false_iff.mpr hdne
    have hall : d.all isAsciiDigit = true := List.all_eq_true.mpr hdall
    simp only [hs, List.take_left, List.drop_left, hempty, hall, Bool.not_true, Bool.or_false,
      beq_self_eq_true, Bool.false_eq_true, if_true, if_false]

/-! ## `parseB` -/

/-- `parseB a l` が返す `B` と残り。 -/
inductive BRel (a : Int) : List Component → Int → List Component → Prop where
  | signed {l : List Component} {n : Num} {rest : List Component}
      (hd : dropWs l = Component.tok (Token.number n) :: rest)
      (hi : n.isInteger = true) (hs : n.sign.isSome = true) :
      BRel a l n.value rest
  | zeroNum {l : List Component} {n : Num} {rest : List Component}
      (hd : dropWs l = Component.tok (Token.number n) :: rest)
      (h : ¬(n.isInteger = true ∧ n.sign.isSome = true)) :
      BRel a l 0 l
  | zeroDelim {l : List Component} {d : Char} {rest : List Component}
      (hd : dropWs l = Component.tok (Token.delim d) :: rest)
      (h1 : d ≠ CH_PLUS) (h2 : d ≠ CH_HYPHEN) :
      BRel a l 0 l
  | zeroOther {l : List Component}
      (hn : ∀ (n : Num) (rest : List Component),
        dropWs l = Component.tok (Token.number n) :: rest → False)
      (hd : ∀ (d : Char) (rest : List Component),
        dropWs l = Component.tok (Token.delim d) :: rest → False) :
      BRel a l 0 l
  | plus {l : List Component} {d : Char} {rest : List Component} {v : Nat} {r : List Component}
      (hd : dropWs l = Component.tok (Token.delim d) :: rest) (hd1 : d = CH_PLUS)
      (hs : SignlessInt (dropWs rest) v r) :
      BRel a l (v : Int) r
  | minus {l : List Component} {d : Char} {rest : List Component} {v : Nat} {r : List Component}
      (hd : dropWs l = Component.tok (Token.delim d) :: rest) (hd1 : d = CH_HYPHEN)
      (hs : SignlessInt (dropWs rest) v r) :
      BRel a l (-(v : Int)) r

/-- **`parseB` は `BRel` をちょうど表す。** -/
theorem parseB_spec (a : Int) (l : List Component) (ab : AnB) (r : List Component) :
    parseB a l = some (ab, r) ↔ ab.a = a ∧ BRel a l ab.b r := by
  constructor
  · intro h
    unfold parseB at h
    split at h
    · next n rest hd =>
      split at h
      · next hc =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hab, hr⟩ := h
        subst hr
        rw [← hab]
        rw [Bool.and_eq_true] at hc
        exact ⟨rfl, .signed hd hc.1 hc.2⟩
      · next hnc =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hab, hr⟩ := h
        subst hr
        rw [← hab]
        exact ⟨rfl, .zeroNum hd (by simpa [Bool.and_eq_true] using hnc)⟩
    · next d rest hd =>
      split at h
      · next hc =>
        split at h
        · next v r2 hs =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hab, hr⟩ := h
          subst hr
          rw [← hab]
          rw [Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at hc
          rcases hc with hplus | hminus
          · subst hplus
            have hne : (CH_PLUS == CH_HYPHEN) = false := by decide
            simp only [hne, Bool.false_eq_true, if_false]
            exact ⟨trivial, .plus hd rfl ((signlessInt_spec _ _ _).mp hs)⟩
          · subst hminus
            have hha : (CH_HYPHEN == CH_HYPHEN) = true := by decide
            simp only [hha, if_true]
            exact ⟨trivial, .minus hd rfl ((signlessInt_spec _ _ _).mp hs)⟩
        · next hn => simp at h
      · next hnc =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hab, hr⟩ := h
        subst hr
        rw [← hab]
        have hnc' : (d == CH_PLUS || d == CH_HYPHEN) = false := by simpa using hnc
        rw [Bool.or_eq_false_iff] at hnc'
        exact ⟨rfl, .zeroDelim hd (by simpa using hnc'.1) (by simpa using hnc'.2)⟩
    · next hn hd2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hab, hr⟩ := h
      subst hr
      rw [← hab]
      exact ⟨rfl, .zeroOther hn hd2⟩
  · rintro ⟨ha, hb⟩
    cases ab with
    | mk a' b' =>
      subst ha
      cases hb with
      | signed hd hi hs =>
        unfold parseB
        rw [hd]
        simp [hi, hs]
      | zeroNum hd h =>
        rename_i n rest
        unfold parseB
        rw [hd]
        have hf : (n.isInteger && n.sign.isSome) = false := by
          cases hi : n.isInteger <;> cases hs : n.sign.isSome <;> simp_all
        simp [hf]
      | zeroDelim hd h1 h2 =>
        unfold parseB
        rw [hd]
        simp [h1, h2]
      | zeroOther hn hd =>
        unfold parseB
        split
        · next n rest heq => exact absurd heq (hn n rest)
        · next d rest heq => exact absurd heq (hd d rest)
        · rfl
      | plus hd hd1 hs =>
        replace hs := (signlessInt_spec _ _ _).mpr hs
        unfold parseB
        rw [hd, hd1]
        have hne : (CH_PLUS == CH_HYPHEN) = false := by decide
        simp [hs, hne]
      | minus hd hd1 hs =>
        replace hs := (signlessInt_spec _ _ _).mpr hs
        unfold parseB
        rw [hd, hd1]
        have hpf : (CH_HYPHEN == CH_PLUS) = false := by decide
        simp [hs, hpf]
        rfl



/-! ## `identAnB` -/

/-- `identAnB` が読む ident 形の関係。 -/
inductive IdentRel (kw : Bool) (s : String) : List Component → Int → Int → List Component → Prop where
  | odd {rest : List Component} (h : kw = true) (hs : asciiLowercase s == "odd") :
      IdentRel kw s rest 2 1 rest
  | even {rest : List Component} (h : kw = true) (hs : asciiLowercase s == "even") :
      IdentRel kw s rest 2 0 rest
  | n {rest : List Component} {b : Int} {r : List Component}
      (hs : asciiLowercase s == "n") (hb : BRel 1 rest b r) :
      IdentRel kw s rest 1 b r
  | negn {rest : List Component} {b : Int} {r : List Component}
      (hs : asciiLowercase s == "-n") (hb : BRel (-1) rest b r) :
      IdentRel kw s rest (-1) b r
  | nDash {rest : List Component} {v : Nat} {r : List Component}
      (hs : asciiLowercase s == "n-") (h : SignlessInt (dropWs rest) v r) :
      IdentRel kw s rest 1 (-(v : Int)) r
  | negnDash {rest : List Component} {v : Nat} {r : List Component}
      (hs : asciiLowercase s == "-n-") (h : SignlessInt (dropWs rest) v r) :
      IdentRel kw s rest (-1) (-(v : Int)) r
  | nDigits {rest : List Component} {v : Nat}
      (hs : DigitsAfter "n-" (asciiLowercase s) v) :
      IdentRel kw s rest 1 (-(v : Int)) rest
  | negnDigits {rest : List Component} {v : Nat}
      (hs : DigitsAfter "-n-" (asciiLowercase s) v) :
      IdentRel kw s rest (-1) (-(v : Int)) rest

/-- **`identAnB` は `IdentRel` をちょうど表す。** -/
theorem identAnB_spec (kw : Bool) (s : String) (rest : List Component) (ab : AnB)
    (r : List Component) :
    identAnB kw s rest = some (ab, r) ↔ IdentRel kw s rest ab.a ab.b r := by
  constructor
  · intro h
    unfold identAnB at h
    dsimp only at h
    split at h
    · next hc =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hab, hr⟩ := h; subst hr; rw [← hab]
      rw [Bool.and_eq_true] at hc
      exact .odd hc.1 hc.2
    · split at h
      · next hc =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hab, hr⟩ := h; subst hr; rw [← hab]
        rw [Bool.and_eq_true] at hc
        exact .even hc.1 hc.2
      · split at h
        · next hc =>
          obtain ⟨ha, hb⟩ := (parseB_spec 1 rest ab r).mp h
          rw [ha]
          exact .n hc hb
        · split at h
          · next hc =>
            obtain ⟨ha, hb⟩ := (parseB_spec (-1) rest ab r).mp h
            rw [ha]
            exact .negn hc hb
          · split at h
            · next hc =>
              split at h
              · next v r2 hs =>
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨hab, hr⟩ := h; subst hr; rw [← hab]
                exact .nDash hc ((signlessInt_spec _ _ _).mp hs)
              · next hn => simp at h
            · split at h
              · next hc =>
                split at h
                · next v r2 hs =>
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨hab, hr⟩ := h; subst hr; rw [← hab]
                  exact .negnDash hc ((signlessInt_spec _ _ _).mp hs)
                · next hn => simp at h
              · split at h
                · next v hs =>
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨hab, hr⟩ := h; subst hr; rw [← hab]
                  exact .negnDigits ((digitsAfter_spec _ _ _).mp hs)
                · next hnone =>
                  split at h
                  · next v hs =>
                    simp only [Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨hab, hr⟩ := h; subst hr; rw [← hab]
                    exact .nDigits ((digitsAfter_spec _ _ _).mp hs)
                  · simp at h
  · intro hb
    cases ab with
    | mk a' b' =>
      cases hb with
      | odd h hs =>
        unfold identAnB
        dsimp only
        rw [h]
        simp [hs]
      | even h hs =>
        unfold identAnB
        dsimp only
        rw [h]
        have hne : ¬ (asciiLowercase s == "odd") = true := by
          intro hc; rw [beq_iff_eq] at hc; rw [hc] at hs; simp at hs
        simp [hs, hne]
      | n hs hb =>
        unfold identAnB
        dsimp only
        have hne : (kw && (asciiLowercase s == "odd")) = false := by
          rw [beq_iff_eq] at hs; rw [hs]; simp
        have hne2 : (kw && (asciiLowercase s == "even")) = false := by
          rw [beq_iff_eq] at hs; rw [hs]; simp
        rw [hne, hne2]
        rw [beq_iff_eq] at hs
        simp only [hs, beq_self_eq_true, if_true]
        exact (parseB_spec 1 rest ⟨1, b'⟩ r).mpr ⟨rfl, hb⟩
      | negn hs hb =>
        unfold identAnB
        dsimp only
        have hne : ¬ (asciiLowercase s == "n") = true := by
          intro hc; rw [beq_iff_eq] at hc; rw [beq_iff_eq] at hs; rw [hs] at hc; simp at hc
        have hne0 : (kw && (asciiLowercase s == "odd")) = false := by
          rw [beq_iff_eq] at hs; rw [hs]; simp
        have hne1 : (kw && (asciiLowercase s == "even")) = false := by
          rw [beq_iff_eq] at hs; rw [hs]; simp
        rw [hne0, hne1, if_neg hne]
        rw [beq_iff_eq] at hs
        simp only [hs, beq_self_eq_true, if_true]
        exact (parseB_spec (-1) rest ⟨-1, b'⟩ r).mpr ⟨rfl, hb⟩
      | nDash hs h =>
        replace h := (signlessInt_spec _ _ _).mpr h
        unfold identAnB
        dsimp only
        have hodd : (kw && (asciiLowercase s == "odd")) = false := by
          rw [beq_iff_eq] at hs; rw [hs]; simp
        have heven : (kw && (asciiLowercase s == "even")) = false := by
          rw [beq_iff_eq] at hs; rw [hs]; simp
        have hn : ¬ (asciiLowercase s == "n") = true := by
          intro hc; rw [beq_iff_eq] at hs hc; rw [hs] at hc; simp at hc
        have hneg : ¬ (asciiLowercase s == "-n") = true := by
          intro hc; rw [beq_iff_eq] at hs hc; rw [hs] at hc; simp at hc
        rw [hodd, heven, if_neg hn, if_neg hneg]
        rw [beq_iff_eq] at hs
        simp only [hs, beq_self_eq_true, Bool.false_eq_true, if_false, if_true, h]
        rfl
      | negnDash hs h =>
        replace h := (signlessInt_spec _ _ _).mpr h
        unfold identAnB
        dsimp only
        have hodd : (kw && (asciiLowercase s == "odd")) = false := by
          rw [beq_iff_eq] at hs; rw [hs]; simp
        have heven : (kw && (asciiLowercase s == "even")) = false := by
          rw [beq_iff_eq] at hs; rw [hs]; simp
        have hn : ¬ (asciiLowercase s == "n") = true := by
          intro hc; rw [beq_iff_eq] at hs hc; rw [hs] at hc; simp at hc
        have hneg : ¬ (asciiLowercase s == "-n") = true := by
          intro hc; rw [beq_iff_eq] at hs hc; rw [hs] at hc; simp at hc
        have hnd : ¬ (asciiLowercase s == "n-") = true := by
          intro hc; rw [beq_iff_eq] at hs hc; rw [hs] at hc; simp at hc
        rw [hodd, heven, if_neg hn, if_neg hneg, if_neg hnd]
        rw [beq_iff_eq] at hs
        simp only [hs, beq_self_eq_true, Bool.false_eq_true, if_false, if_true, h]
        rfl
      | nDigits hs =>
        obtain ⟨d, hd, hdne, _, _⟩ := id hs
        -- `-n-` で始まる文字列は `n-` で始まらないので、実装の試す順序は効かない。
        have hnegd : digitsAfter "-n-" (asciiLowercase s) = none := by
          cases h' : digitsAfter "-n-" (asciiLowercase s) with
          | none => rfl
          | some v' =>
            obtain ⟨d', hd', _⟩ := (digitsAfter_spec _ _ _).mp h'
            rw [hd] at hd'; simp at hd'
        replace hs := (digitsAfter_spec _ _ _).mpr hs
        unfold identAnB
        dsimp only
        have hodd : ¬ (kw && (asciiLowercase s == "odd")) = true := by
          intro hc; rw [Bool.and_eq_true] at hc; rw [beq_iff_eq] at hc
          rw [hc.2] at hd; simp_all
        have heven : ¬ (kw && (asciiLowercase s == "even")) = true := by
          intro hc; rw [Bool.and_eq_true] at hc; rw [beq_iff_eq] at hc
          rw [hc.2] at hd; simp_all
        have hn : ¬ (asciiLowercase s == "n") = true := by
          intro hc; rw [beq_iff_eq] at hc; rw [hc] at hd; simp_all
        have hneg : ¬ (asciiLowercase s == "-n") = true := by
          intro hc; rw [beq_iff_eq] at hc; rw [hc] at hd; simp_all
        have hnd : ¬ (asciiLowercase s == "n-") = true := by
          intro hc; rw [beq_iff_eq] at hc; rw [hc] at hd; simp_all
        have hnegnd : ¬ (asciiLowercase s == "-n-") = true := by
          intro hc; rw [beq_iff_eq] at hc; rw [hc] at hd; simp_all
        rw [if_neg hodd, if_neg heven, if_neg hn, if_neg hneg, if_neg hnd, if_neg hnegnd]
        simp only [hnegd, hs]
        rfl
      | negnDigits hs =>
        obtain ⟨d, hd, hdne, _, _⟩ := id hs
        replace hs := (digitsAfter_spec _ _ _).mpr hs
        unfold identAnB
        dsimp only
        have hodd : ¬ (kw && (asciiLowercase s == "odd")) = true := by
          intro hc; rw [Bool.and_eq_true] at hc; rw [beq_iff_eq] at hc
          rw [hc.2] at hd; simp_all
        have heven : ¬ (kw && (asciiLowercase s == "even")) = true := by
          intro hc; rw [Bool.and_eq_true] at hc; rw [beq_iff_eq] at hc
          rw [hc.2] at hd; simp_all
        have hn : ¬ (asciiLowercase s == "n") = true := by
          intro hc; rw [beq_iff_eq] at hc; rw [hc] at hd; simp_all
        have hneg : ¬ (asciiLowercase s == "-n") = true := by
          intro hc; rw [beq_iff_eq] at hc; rw [hc] at hd; simp_all
        have hnd : ¬ (asciiLowercase s == "n-") = true := by
          intro hc; rw [beq_iff_eq] at hc; rw [hc] at hd; simp_all
        have hnegnd : ¬ (asciiLowercase s == "-n-") = true := by
          intro hc; rw [beq_iff_eq] at hc; rw [hc] at hd; simp_all
        rw [if_neg hodd, if_neg heven, if_neg hn, if_neg hneg, if_neg hnd, if_neg hnegnd]
        simp only [hs]
        rfl

/-! ## `parseAnB` / `parseAnBFull` -/

/-- `parseAnB` が読むトップレベルの形。 -/
inductive AnBSyntax : List Component → AnB → List Component → Prop where
  | ident (l : List Component) (s : String) (rest : List Component) (a b : Int)
      (r : List Component) (hd : dropWs l = Component.tok (Token.ident s) :: rest)
      (hi : IdentRel true s rest a b r) : AnBSyntax l ⟨a, b⟩ r
  | number (l : List Component) (n : Num) (rest : List Component)
      (hd : dropWs l = Component.tok (Token.number n) :: rest) (hi : n.isInteger = true) :
      AnBSyntax l ⟨0, n.value⟩ rest
  | dimN (l : List Component) (n : Num) (u : String) (rest : List Component) (b : Int)
      (r : List Component) (hd : dropWs l = Component.tok (Token.dimension n u) :: rest)
      (hi : n.isInteger = true) (hu : asciiLowercase u == "n") (hb : BRel n.value rest b r) :
      AnBSyntax l ⟨n.value, b⟩ r
  | dimNDash (l : List Component) (n : Num) (u : String) (rest : List Component) (v : Nat)
      (r : List Component) (hd : dropWs l = Component.tok (Token.dimension n u) :: rest)
      (hi : n.isInteger = true) (hu : asciiLowercase u == "n-")
      (hs : SignlessInt (dropWs rest) v r) :
      AnBSyntax l ⟨n.value, -(v : Int)⟩ r
  | dimDigits (l : List Component) (n : Num) (u : String) (rest : List Component) (v : Nat)
      (hd : dropWs l = Component.tok (Token.dimension n u) :: rest)
      (hi : n.isInteger = true) (hu : DigitsAfter "n-" (asciiLowercase u) v) :
      AnBSyntax l ⟨n.value, -(v : Int)⟩ rest
  | plusIdent (l : List Component) (d : Char) (s : String) (rest : List Component) (a b : Int)
      (r : List Component)
      (hd : dropWs l = Component.tok (Token.delim d) :: Component.tok (Token.ident s) :: rest)
      (hd1 : (d == CH_PLUS) = true) (hi : IdentRel false s rest a b r) :
      AnBSyntax l ⟨a, b⟩ r

/-- **`parseAnB` は `AnBSyntax` をちょうど表す。** -/
theorem parseAnB_spec (l : List Component) (ab : AnB) (r : List Component) :
    parseAnB l = some (ab, r) ↔ AnBSyntax l ab r := by
  constructor
  · intro h
    unfold parseAnB at h
    split at h
    · next s rest hd =>
      exact .ident l s rest ab.a ab.b r hd ((identAnB_spec true s rest ab r).mp h)
    · next n rest hd =>
      split at h
      · next hi =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hab, hr⟩ := h; subst hr; rw [← hab]
        exact .number l n rest hd hi
      · simp at h
    · next n u rest hd =>
      split at h
      · simp at h
      · next hnc =>
        have hi : n.isInteger = true := by simpa using hnc
        dsimp only at h
        split at h
        · next hu =>
          obtain ⟨ha, hb⟩ := (parseB_spec n.value rest ab r).mp h
          rw [show ab = ⟨n.value, ab.b⟩ from by cases ab; simp_all]
          exact .dimN l n u rest ab.b r hd hi hu hb
        · split at h
          · next hu =>
            split at h
            · next v r2 hs =>
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨hab, hr⟩ := h; subst hr; rw [← hab]
              exact .dimNDash l n u rest v _ hd hi hu ((signlessInt_spec _ _ _).mp hs)
            · simp at h
          · split at h
            · next v hu =>
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨hab, hr⟩ := h; subst hr; rw [← hab]
              exact .dimDigits l n u rest v hd hi ((digitsAfter_spec _ _ _).mp hu)
            · simp at h
    · next d s rest hd =>
      split at h
      · next hc =>
        exact .plusIdent l d s rest ab.a ab.b r hd hc ((identAnB_spec false s rest ab r).mp h)
      · simp at h
    · simp at h
  · intro hb
    cases hb with
    | ident s rest a b r hd hi =>
      unfold parseAnB
      rw [hd]
      exact (identAnB_spec true s rest ⟨a, b⟩ r).mpr hi
    | number n rest hd hi =>
      unfold parseAnB
      rw [hd]
      simp [hi]
    | dimN n u rest b r hd hi hu hb =>
      unfold parseAnB
      rw [hd]
      simp only [hi, Bool.not_true, Bool.false_eq_true, if_false]
      simp [hu]
      exact (parseB_spec n.value rest ⟨n.value, b⟩ r).mpr ⟨rfl, hb⟩
    | dimNDash n u rest v r hd hi hu hs =>
      replace hs := (signlessInt_spec _ _ _).mpr hs
      unfold parseAnB
      rw [hd]
      simp only [hi, Bool.not_true, Bool.false_eq_true, if_false]
      have hu' : ¬ (asciiLowercase u == "n") = true := by
        intro hc; rw [beq_iff_eq] at hu hc; rw [hu] at hc; simp at hc
      rw [if_neg hu']
      simp [hu, hs]
    | dimDigits n u rest v hd hi hu =>
      unfold parseAnB
      rw [hd]
      simp only [hi, Bool.not_true, Bool.false_eq_true, if_false]
      obtain ⟨d, hd2, hdne, _, _⟩ := id hu
      replace hu := (digitsAfter_spec _ _ _).mpr hu
      have hu' : ¬ (asciiLowercase u == "n") = true := by
        intro hc; rw [beq_iff_eq] at hc; rw [hc] at hd2; simp_all
      have hu'' : ¬ (asciiLowercase u == "n-") = true := by
        intro hc; rw [beq_iff_eq] at hc; rw [hc] at hd2; simp_all
      rw [if_neg hu', if_neg hu'']
      simp only [hu]
    | plusIdent d s rest a b r hd hd1 hi =>
      unfold parseAnB
      rw [hd]
      dsimp only
      rw [if_pos hd1]
      exact (identAnB_spec false s rest ⟨a, b⟩ r).mpr hi

/-- **`parseAnBFull` は `AnBSyntax` と「残りが空白だけ」でちょうど表す。** -/
theorem parseAnBFull_spec (l : List Component) (ab : AnB) :
    parseAnBFull l = some ab ↔ ∃ r : List Component, AnBSyntax l ab r ∧ dropWs r = [] := by
  constructor
  · intro h
    unfold parseAnBFull at h
    split at h
    · next ab' r hrs =>
      by_cases hempty : (dropWs r).isEmpty = true
      · have hr : dropWs r = [] := by simpa using hempty
        rw [if_pos hempty] at h
        have hab : ab' = ab := Option.some.inj h
        refine ⟨r, ?_, hr⟩
        rw [← hab]
        exact (parseAnB_spec l ab' r).mp hrs
      · rw [if_neg hempty] at h
        simp at h
    · simp at h
  · rintro ⟨r, hb, hr⟩
    unfold parseAnBFull
    rw [(parseAnB_spec l ab r).mpr hb]
    dsimp only
    have : (dropWs r).isEmpty = true := by rw [hr]; rfl
    rw [this]
    simp

end Selectors.Spec
