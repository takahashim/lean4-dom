import Url.Spec.Ipv4
import Url.Ipv6

/-!
# IPv6 の関係仕様（§3.3 IPv6 parser）

実装の `ipv6Parser` は pointer を進める loop を、残りの入力についての再帰（`ipv6Loop`）と
IPv4-in-IPv6 の部分（`ipv4InIpv6`）で書いている。ここでは同じものを、RFC 4291 §2.2 と同じ形の
文法として書く（`Ipv6Text`）。

* piece は 1-4 個の ASCII hex digit（`H16`）。
* piece を `:` で区切って並べる（`Groups`）。最後に dotted decimal の IPv4 を置ける（`Tail`）。IPv4 は 2 piece ぶん。
* 省略しない形は 8 piece ちょうど。`::` は一度だけ使えて、その前後の piece が合わせて 7 個以下。
  `::` が埋める 0 の個数は残りである。
* dotted decimal の各数は `0` か、`0` で始まらない 10 進で、255 以下（`DecOctet`）。

`ipv6Parser_iff` が、実装はこの関係を計算すると言う。
-/

namespace Url.Spec

open Infra Url

/-! ## 10 進の数 -/

theorem digitValue_eq (c : Char) :
    digitValue c = if IsDecDigit c then some (digitVal c) else none := by
  unfold digitValue digitVal
  by_cases h : IsDecDigit c
  · rw [if_pos h]
    unfold IsDecDigit at h
    rw [if_pos (by simp; omega), if_pos (by omega)]
  · rw [if_neg h]
    unfold IsDecDigit at h
    rw [if_neg (by simp; omega)]

theorem isAsciiDigit_eq (c : Char) : isAsciiDigit c = decide (IsDecDigit c) := by
  unfold isAsciiDigit IsDecDigit
  by_cases h1 : 48 ≤ c.toNat <;> by_cases h2 : c.toNat ≤ 57 <;> simp [h1, h2]

/-- **`takeDec` は先頭の ASCII digit の並びを桁の重みで読み、残りを返す。** 入力に条件は無い。 -/
theorem takeDec_eq : ∀ (s : List Char) (acc len : Nat),
    takeDec s acc len
      = (acc * 10 ^ (s.takeWhile isAsciiDigit).length + radixValue 10 (s.takeWhile isAsciiDigit),
         len + (s.takeWhile isAsciiDigit).length, s.dropWhile isAsciiDigit)
  | [], acc, len => by simp [takeDec, radixValue]
  | c :: s, acc, len => by
    simp only [takeDec, digitValue_eq]
    by_cases hc : IsDecDigit c
    · rw [if_pos hc]
      simp only
      rw [takeDec_eq s (acc * 10 + digitVal c) (len + 1)]
      have hd : isAsciiDigit c = true := by rw [isAsciiDigit_eq]; simpa using hc
      simp only [List.takeWhile_cons, hd, if_true, List.dropWhile_cons, List.length_cons,
        radixValue, Prod.mk.injEq]
      refine ⟨?_, by omega, trivial⟩
      rw [Nat.pow_succ, Nat.add_mul, Nat.add_assoc, Nat.mul_assoc, Nat.mul_comm 10]
    · rw [if_neg hc]
      have hd : isAsciiDigit c = false := by rw [isAsciiDigit_eq]; simpa using hc
      simp [hd, radixValue]

/--
dotted decimal の一つの数。空でない ASCII digit の並びで、二桁以上なら `0` で始まらず、255 以下。

IPv6 parser 5.5.5.4 の「ipv4Piece が 0 のときに digit が続けば失敗」は、二桁以上で `0` で始まることと同じである。
-/
def DecOctet (d : List Char) : Prop :=
  d ≠ [] ∧ (∀ c ∈ d, IsDecDigit c) ∧ (d.length > 1 → d.head? ≠ some '0') ∧ radixValue 10 d ≤ 255

instance (d : List Char) : Decidable (DecOctet d) := by unfold DecOctet; infer_instance

/-- 一つの数を読んだ後の続き。 -/
def octetNext (fuel : Nat) (s : List Char) (addr : Ipv6) (p ns : Nat) : Option Ipv6 :=
  if DecOctet (s.takeWhile isAsciiDigit) then
    ipv4InIpv6 fuel (s.dropWhile isAsciiDigit)
      (addr.set (p + ns / 2)
        (addr.getD (p + ns / 2) 0 * 0x100 + radixValue 10 (s.takeWhile isAsciiDigit)))
      p (ns + 1)
  else none

/-- IPv4-in-IPv6 の最初の数（区切りの `.` は要らない）。 -/
theorem ipv4InIpv6_first (fuel : Nat) (input : List Char) (addr : Ipv6) (p : Nat) :
    ipv4InIpv6 (fuel + 1) input addr p 0 = octetNext fuel input addr p 0 := by
  let ns := 0
  have hafter : ∀ s : List Char,
      (match s with
        | [] => none
        | c :: _ =>
          if (!isAsciiDigit c) = true then none
          else
            if (takeDec s 0 0).fst > 255 then none
            else
              if (decide ((takeDec s 0 0).2.fst > 1) && s.head? == some '0') = true then none
              else
                ipv4InIpv6 fuel (takeDec s 0 0).2.snd
                  (List.set addr (p + ns / 2) (List.getD addr (p + ns / 2) 0 * 256 + (takeDec s 0 0).fst))
                  p (ns + 1))
      = octetNext fuel s addr p ns := by
    unfold octetNext
    intro s
    cases s with
    | nil => simp [DecOctet]
    | cons c t =>
      simp only [takeDec_eq, Nat.zero_mul, Nat.zero_add, List.head?_cons]
      by_cases hc : isAsciiDigit c = true
      · rw [if_neg (by simp [hc])]
        have hne : (c :: t).takeWhile isAsciiDigit ≠ [] := by simp [hc]
        have hall : ∀ x ∈ (c :: t).takeWhile isAsciiDigit, IsDecDigit x := by
          intro x hx
          have := List.all_eq_true.mp List.all_takeWhile x hx
          rw [isAsciiDigit_eq] at this; simpa using this
        have hhead : ((c :: t).takeWhile isAsciiDigit).head? = some c := by
          simp [hc]
        split
        · next hv => rw [if_neg (show ¬DecOctet _ from fun h => by unfold DecOctet at h; omega)]
        · next hv =>
          split
          · next hz =>
            simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Option.some.injEq] at hz
            rw [if_neg (show ¬DecOctet _ from fun h => h.2.2.1 hz.1 (by rw [hhead, hz.2]))]
          · next hz =>
            simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Option.some.injEq,
              not_and] at hz
            rw [if_pos (show DecOctet _ from ⟨hne, hall, fun hl => by
              rw [hhead]; intro h; exact hz hl (by simpa using h), by omega⟩)]
      · have hc' : isAsciiDigit c = false := by simpa using hc
        simp [hc', DecOctet]
  cases input with
  | nil => simp [ipv4InIpv6, octetNext, DecOctet]
  | cons c t =>
    simp only [ipv4InIpv6, Nat.lt_irrefl, if_false]
    exact hafter (c :: t)

/-- 二つ目以降の数は `.` の後に読む。 -/
theorem ipv4InIpv6_dot (fuel : Nat) (t : List Char) (addr : Ipv6) (p ns : Nat) (h0 : 0 < ns)
    (h4 : ns < 4) :
    ipv4InIpv6 (fuel + 1) ('.' :: t) addr p ns = octetNext fuel t addr p ns := by
  have hafter : ∀ s : List Char,
      (match s with
        | [] => none
        | c :: _ =>
          if (!isAsciiDigit c) = true then none
          else
            if (takeDec s 0 0).fst > 255 then none
            else
              if (decide ((takeDec s 0 0).2.fst > 1) && s.head? == some '0') = true then none
              else
                ipv4InIpv6 fuel (takeDec s 0 0).2.snd
                  (List.set addr (p + ns / 2) (List.getD addr (p + ns / 2) 0 * 256 + (takeDec s 0 0).fst))
                  p (ns + 1))
      = octetNext fuel s addr p ns := by
    unfold octetNext
    intro s
    cases s with
    | nil => simp [DecOctet]
    | cons c t =>
      simp only [takeDec_eq, Nat.zero_mul, Nat.zero_add, List.head?_cons]
      by_cases hc : isAsciiDigit c = true
      · rw [if_neg (by simp [hc])]
        have hne : (c :: t).takeWhile isAsciiDigit ≠ [] := by simp [hc]
        have hall : ∀ x ∈ (c :: t).takeWhile isAsciiDigit, IsDecDigit x := by
          intro x hx
          have := List.all_eq_true.mp List.all_takeWhile x hx
          rw [isAsciiDigit_eq] at this; simpa using this
        have hhead : ((c :: t).takeWhile isAsciiDigit).head? = some c := by
          simp [hc]
        split
        · next hv => rw [if_neg (show ¬DecOctet _ from fun h => by unfold DecOctet at h; omega)]
        · next hv =>
          split
          · next hz =>
            simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Option.some.injEq] at hz
            rw [if_neg (show ¬DecOctet _ from fun h => h.2.2.1 hz.1 (by rw [hhead, hz.2]))]
          · next hz =>
            simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Option.some.injEq,
              not_and] at hz
            rw [if_pos (show DecOctet _ from ⟨hne, hall, fun hl => by
              rw [hhead]; intro h; exact hz hl (by simpa using h), by omega⟩)]
      · have hc' : isAsciiDigit c = false := by simpa using hc
        simp [hc', DecOctet]
  simp only [ipv4InIpv6, h0, h4, if_true]
  exact hafter t

/-- 二つ目以降の数の前に `.` が無ければ失敗する。 -/
theorem ipv4InIpv6_nodot (fuel : Nat) (input : List Char) (addr : Ipv6) (p ns : Nat) (h0 : 0 < ns)
    (h4 : ns < 4) (hd : ∀ t, input ≠ '.' :: t) :
    ipv4InIpv6 (fuel + 1) input addr p ns = none := by
  cases input with
  | nil => simp [ipv4InIpv6]; try omega
  | cons c t =>
    have hc : c ≠ '.' := fun e => hd t (by rw [e])
    simp only [ipv4InIpv6, h0, if_true]

/-- 数え終わり。入力が尽きていれば成功する。 -/
theorem ipv4InIpv6_zero (input : List Char) (addr : Ipv6) (p : Nat) :
    ipv4InIpv6 0 input addr p 4 = if input = [] then some addr else none := by
  cases input <;> simp [ipv4InIpv6]

/-- dotted decimal の IPv4。四つの数を `.` で区切り、二つずつ 16 bit の piece にする。 -/
def Ipv4Text (l : List Char) (x y : Nat) : Prop :=
  ∃ d1 d2 d3 d4, l = d1 ++ '.' :: (d2 ++ '.' :: (d3 ++ '.' :: d4)) ∧
    DecOctet d1 ∧ DecOctet d2 ∧ DecOctet d3 ∧ DecOctet d4 ∧
    x = radixValue 10 d1 * 256 + radixValue 10 d2 ∧ y = radixValue 10 d3 * 256 + radixValue 10 d4

/-- digit の並びの後に digit でないものが続けば、takeWhile と dropWhile はそこで分ける。 -/
theorem takeDrop_digits {d rest : List Char} (hd : ∀ c ∈ d, IsDecDigit c)
    (hr : ∀ c r, rest = c :: r → isAsciiDigit c = false) :
    (d ++ rest).takeWhile isAsciiDigit = d ∧ (d ++ rest).dropWhile isAsciiDigit = rest := by
  induction d with
  | nil =>
    cases rest with
    | nil => simp
    | cons c r => simp [hr c r rfl]
  | cons c d ih =>
    have hc : isAsciiDigit c = true := by rw [isAsciiDigit_eq]; simpa using hd c (by simp)
    obtain ⟨h1, h2⟩ := ih (fun x hx => hd x (by simp [hx]))
    simp [hc, h1, h2]

theorem dot_not_digit : isAsciiDigit '.' = false := by decide

/-- 一つの数を読んで成功したなら、その数は `DecOctet` で、続きも成功している。 -/
theorem octetNext_inv {fuel : Nat} {s : List Char} {addr : Ipv6} {p ns : Nat} {a' : Ipv6}
    (h : octetNext fuel s addr p ns = some a') :
    DecOctet (s.takeWhile isAsciiDigit) ∧
      ipv4InIpv6 fuel (s.dropWhile isAsciiDigit)
        (addr.set (p + ns / 2)
          (addr.getD (p + ns / 2) 0 * 0x100 + radixValue 10 (s.takeWhile isAsciiDigit)))
        p (ns + 1) = some a' := by
  unfold octetNext at h
  split at h
  · exact ⟨by assumption, h⟩
  · simp at h

/-- 二つ目以降の数で成功したなら、入力は `.` で始まる。 -/
theorem ipv4InIpv6_dot_inv {fuel : Nat} {input : List Char} {addr : Ipv6} {p ns : Nat} {a' : Ipv6}
    (h0 : 0 < ns) (h4 : ns < 4) (h : ipv4InIpv6 (fuel + 1) input addr p ns = some a') :
    ∃ s, input = '.' :: s ∧ octetNext fuel s addr p ns = some a' := by
  by_cases hd : ∃ s, input = '.' :: s
  · obtain ⟨s, rfl⟩ := hd
    exact ⟨s, rfl, by rw [← ipv4InIpv6_dot fuel s addr p ns h0 h4]; exact h⟩
  · rw [ipv4InIpv6_nodot fuel input addr p ns h0 h4 (fun t he => hd ⟨t, he⟩)] at h
    simp at h

/-- **IPv4-in-IPv6 は dotted decimal の関係 `Ipv4Text` を読み、二つの piece に書く。** -/
theorem ipv4InIpv6_iff (input : List Char) (addr : Ipv6) (p : Nat) (hlen : p + 1 < addr.length)
    (h0 : addr.getD p 0 = 0) (h1 : addr.getD (p + 1) 0 = 0) (addr' : Ipv6) :
    ipv4InIpv6 4 input addr p 0 = some addr'
      ↔ ∃ x y, Ipv4Text input x y ∧ addr' = (addr.set p x).set (p + 1) y := by
  have hp : p < addr.length := by omega
  constructor
  · intro h
    rw [ipv4InIpv6_first] at h
    obtain ⟨hd1, h⟩ := octetNext_inv h
    obtain ⟨s2, hs2, h⟩ := ipv4InIpv6_dot_inv (by omega) (by omega) h
    obtain ⟨hd2, h⟩ := octetNext_inv h
    obtain ⟨s3, hs3, h⟩ := ipv4InIpv6_dot_inv (by omega) (by omega) h
    obtain ⟨hd3, h⟩ := octetNext_inv h
    obtain ⟨s4, hs4, h⟩ := ipv4InIpv6_dot_inv (by omega) (by omega) h
    obtain ⟨hd4, h⟩ := octetNext_inv h
    rw [ipv4InIpv6_zero] at h
    split at h
    · next he =>
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨_, _, ⟨input.takeWhile isAsciiDigit, s2.takeWhile isAsciiDigit,
        s3.takeWhile isAsciiDigit, s4.takeWhile isAsciiDigit, ?_, hd1, hd2, hd3, hd4, rfl, rfl⟩, ?_⟩
      · have e1 := (List.takeWhile_append_dropWhile (p := isAsciiDigit) (l := input)).symm
        have e2 := (List.takeWhile_append_dropWhile (p := isAsciiDigit) (l := s2)).symm
        have e3 := (List.takeWhile_append_dropWhile (p := isAsciiDigit) (l := s3)).symm
        have e4 := (List.takeWhile_append_dropWhile (p := isAsciiDigit) (l := s4)).symm
        rw [hs2] at e1; rw [hs3] at e2; rw [hs4] at e3; rw [he, List.append_nil] at e4
        refine e1.trans ?_; congr 2
        refine e2.trans ?_; congr 2
        refine e3.trans ?_; congr 2
      · simp only [Nat.reduceAdd, Nat.reduceDiv, Nat.add_zero, Nat.zero_div]
        rw [h0, getD_set_self _ _ _ _ hp, getD_set_other _ _ _ _ _ (by omega),
          getD_set_other _ _ _ _ _ (by omega), h1, List.set_set]
        rw [getD_set_self _ _ _ _ (by simp; omega), List.set_set]
        simp
    · simp at h
  · rintro ⟨x, y, ⟨d1, d2, d3, d4, rfl, hd1, hd2, hd3, hd4, rfl, rfl⟩, rfl⟩
    have nd : ∀ r, ∀ c r', ('.' :: r) = c :: r' → isAsciiDigit c = false := by
      intro r c r' he; simp at he; rw [← he.1]; exact dot_not_digit
    have nil : ∀ c r', ([] : List Char) = c :: r' → isAsciiDigit c = false := by
      intro c r' he; cases he
    obtain ⟨t1, r1⟩ := takeDrop_digits hd1.2.1 (nd _)
    obtain ⟨t2, r2⟩ := takeDrop_digits hd2.2.1 (nd _)
    obtain ⟨t3, r3⟩ := takeDrop_digits hd3.2.1 (nd _)
    obtain ⟨t4, r4⟩ := takeDrop_digits (rest := []) hd4.2.1 nil
    simp only [List.append_nil] at t4 r4
    rw [ipv4InIpv6_first]
    unfold octetNext
    rw [t1, if_pos hd1, r1, ipv4InIpv6_dot _ _ _ _ _ (by omega) (by omega)]
    unfold octetNext
    rw [t2, if_pos hd2, r2, ipv4InIpv6_dot _ _ _ _ _ (by omega) (by omega)]
    unfold octetNext
    rw [t3, if_pos hd3, r3, ipv4InIpv6_dot _ _ _ _ _ (by omega) (by omega)]
    unfold octetNext
    rw [t4, if_pos hd4, r4, ipv4InIpv6_zero, if_pos rfl]
    simp only [Nat.reduceAdd, Nat.reduceDiv, Nat.add_zero, Nat.zero_div, Option.some.injEq]
    rw [h0, getD_set_self _ _ _ _ hp, getD_set_other _ _ _ _ _ (by omega),
      getD_set_other _ _ _ _ _ (by omega), h1, List.set_set]
    rw [getD_set_self _ _ _ _ (by simp; omega), List.set_set]
    simp

/-! ## 16 進の piece -/

/-- ASCII hex digit かどうかの判定（`Infra.hexValue` が値を返すこと）。 -/
def isHexB (c : Char) : Bool := (hexValue c).isSome

theorem isHexB_iff (c : Char) : isHexB c = true ↔ IsHexDigit c := by
  unfold isHexB; rw [hexValue_eq]; split <;> simp_all

/-- **`takeHex n` は先頭の hex digit を高々 `n` 個読み、桁の重みで読んだ値と個数と残りを返す。** -/
theorem takeHex_eq : ∀ (n : Nat) (l : List Char),
    takeHex n l = (radixValue 16 ((l.takeWhile isHexB).take n), ((l.takeWhile isHexB).take n).length,
                   l.drop ((l.takeWhile isHexB).take n).length)
  | 0, l => by simp [takeHex, radixValue]
  | n + 1, [] => by simp [takeHex, radixValue]
  | n + 1, c :: rest => by
    simp only [takeHex, hexValue_eq]
    by_cases hc : IsHexDigit c
    · rw [if_pos hc]
      simp only
      rw [takeHex_eq n rest]
      have hb : isHexB c = true := (isHexB_iff c).mpr hc
      simp [hb, radixValue]
    · rw [if_neg hc]
      have hb : isHexB c = false := by
        cases h : isHexB c
        · rfl
        · exact absurd ((isHexB_iff c).mp h) hc
      simp [hb, radixValue]

/-- 1-4 個の ASCII hex digit。 -/
def H16 (g : List Char) : Prop := g ≠ [] ∧ g.length ≤ 4 ∧ ∀ c ∈ g, IsHexDigit c

/-- piece の後に hex digit でないものが続けば、`takeHex 4` はちょうどその piece を読む。 -/
theorem takeHex_h16 {g rest : List Char} (hg : H16 g)
    (hr : ∀ c r, rest = c :: r → isHexB c = false) :
    takeHex 4 (g ++ rest) = (radixValue 16 g, g.length, rest) := by
  rw [takeHex_eq]
  have htw : (g ++ rest).takeWhile isHexB = g := by
    rw [List.takeWhile_append_of_pos (fun c hc => (isHexB_iff c).mpr (hg.2.2 c hc))]
    cases rest with
    | nil => simp
    | cons c r => simp [hr c r rfl]
  rw [htw, List.take_of_length_le hg.2.1]
  simp

/-! ## loop の遷移

実装の `ipv6Loop` が成功するときの遷移を、そのまま構成子にした関係（`LoopRun`）。
文法との対応は次の節で示す。ここでは loop が `LoopRun` をちょうど計算することだけを言う。
-/

/-- `ipv6Loop` の成功した走行。結果は (address, pieceIndex, compress)。 -/
inductive LoopRun : List Char → Ipv6 → Nat → Option Nat → Ipv6 × Nat × Option Nat → Prop
  /-- 入力の終わり。 -/
  | eof {a : Ipv6} {p : Nat} {c : Option Nat} : LoopRun [] a p c (a, p, c)
  /-- step 5.2：piece の読み始めの `:` は `::` の二つ目。一度だけ。 -/
  | compress {rest : List Char} {a : Ipv6} {p : Nat} {r : Ipv6 × Nat × Option Nat} :
      p ≠ 8 → LoopRun rest a (p + 1) (some (p + 1)) r → LoopRun (':' :: rest) a p none r
  /-- step 5.3-5.6：piece と区切りの `:`。区切りの後が入力の終わりなら失敗なので、続きは空でない。 -/
  | piece {g rest : List Char} {a : Ipv6} {p : Nat} {c : Option Nat} {r : Ipv6 × Nat × Option Nat} :
      p ≠ 8 → H16 g → rest ≠ [] → LoopRun rest (a.set p (radixValue 16 g)) (p + 1) c r →
      LoopRun (g ++ ':' :: rest) a p c r
  /-- step 5.3-5.7：最後の piece。 -/
  | last {g : List Char} {a : Ipv6} {p : Nat} {c : Option Nat} :
      p ≠ 8 → H16 g → LoopRun g a p c (a.set p (radixValue 16 g), p + 1, c)
  /-- step 5.5：IPv4-in-IPv6。2 piece を埋めて終わる。 -/
  | ipv4 {l : List Char} {a : Ipv6} {p : Nat} {c : Option Nat} {x y : Nat} :
      p ≤ 6 → Ipv4Text l x y → LoopRun l a p c ((a.set p x).set (p + 1) y, p + 2, c)

/-- loop の不変条件。address は 8 piece で、pieceIndex 以降はまだ 0。 -/
def LoopInv (a : Ipv6) (p : Nat) : Prop := a.length = 8 ∧ p ≤ 8 ∧ ∀ j, p ≤ j → a.getD j 0 = 0

theorem LoopInv.set {a : Ipv6} {p v : Nat} (h : LoopInv a p) (hp : p ≠ 8) :
    LoopInv (a.set p v) (p + 1) := by
  refine ⟨by simp [h.1], by have := h.2.1; omega, fun j hj => ?_⟩
  rw [getD_set_other _ _ _ _ _ (by omega)]
  exact h.2.2 j (by omega)

theorem LoopInv.succ {a : Ipv6} {p : Nat} (h : LoopInv a p) (hp : p ≠ 8) : LoopInv a (p + 1) :=
  ⟨h.1, by have := h.2.1; omega, fun j hj => h.2.2 j (by omega)⟩

/-- 読んだ hex digit の並びは、高々 4 個の hex digit。 -/
theorem hexPrefix_h16 {l : List Char} (hne : (l.takeWhile isHexB).take 4 ≠ []) :
    H16 ((l.takeWhile isHexB).take 4) := by
  refine ⟨hne, by simp [Nat.min_le_left], fun c hc => ?_⟩
  have := List.all_eq_true.mp List.all_takeWhile c (List.mem_of_mem_take hc)
  exact (isHexB_iff c).mp this

/-- 前置きは取り出した部分と残りに戻る。 -/
theorem take_append_drop_prefix (l : List Char) :
    l = (l.takeWhile isHexB).take 4 ++ l.drop ((l.takeWhile isHexB).take 4).length := by
  have hpre : (l.takeWhile isHexB).take 4 = l.take ((l.takeWhile isHexB).take 4).length := by
    have h1 : (l.takeWhile isHexB).take 4 <+: l :=
      (List.take_prefix 4 _).trans (List.takeWhile_prefix _)
    exact (List.prefix_iff_eq_take.mp h1)
  conv => lhs; rw [← List.take_append_drop ((l.takeWhile isHexB).take 4).length l]
  rw [← hpre]

/-- **loop が成功したなら、その走行は `LoopRun` である。** -/
theorem loopRun_of_loop : ∀ (fuel : Nat) (l : List Char) (a : Ipv6) (p : Nat) (c : Option Nat)
    (r : Ipv6 × Nat × Option Nat), LoopInv a p → ipv6Loop fuel l a p c = some r → LoopRun l a p c r
  | 0, _, _, _, _, _, _, h => by simp [ipv6Loop] at h
  | _ + 1, [], a, p, c, r, _, h => by
    simp only [ipv6Loop, Option.some.injEq] at h
    subst h; exact .eof
  | f + 1, c0 :: t, a, p, c, r, hinv, h => by
    simp only [ipv6Loop] at h
    split at h
    · simp at h
    · next hp8 =>
      have hp : p ≠ 8 := by simpa using hp8
      split at h
      · next _ rest he =>
        simp only [List.cons.injEq] at he
        obtain ⟨rfl, hrt⟩ := he
        subst hrt
        split at h
        · simp at h
        · next hc =>
          have hc' : c = none := by simpa using hc
          subst hc'
          exact .compress hp (loopRun_of_loop f t a (p + 1) (some (p + 1)) r (hinv.succ hp) h)
      · next _ hnc =>
        have hc0 : c0 ≠ ':' := fun e => hnc t (by rw [e])
        rw [takeHex_eq] at h
        simp only at h
        have hdec := take_append_drop_prefix (c0 :: t)
        generalize hg : ((c0 :: t).takeWhile isHexB).take 4 = g at h hdec
        generalize hd : (c0 :: t).drop g.length = rest at h hdec
        have hgh : g ≠ [] → H16 g := fun hne => by rw [← hg] at hne ⊢; exact hexPrefix_h16 hne
        split at h
        · -- IPv4-in-IPv6
          split at h
          · simp at h
          · next hl0 =>
            split at h
            · simp at h
            · next hp6 =>
              have hp6' : p ≤ 6 := by omega
              split at h
              · simp at h
              · next addr' hip =>
                simp only [Option.some.injEq] at h
                subst h
                obtain ⟨x, y, htext, rfl⟩ := (ipv4InIpv6_iff (c0 :: t) a p
                  (by rw [hinv.1]; omega) (hinv.2.2 p (Nat.le_refl _))
                  (hinv.2.2 (p + 1) (by omega)) addr').mp hip
                exact .ipv4 hp6' htext
        · -- piece と区切り
          next rest' =>
          split at h
          · simp at h
          · next hne =>
            have hgne : g ≠ [] := by
              rintro rfl
              simp at hdec
              exact hc0 hdec.1
            rw [hdec]
            exact .piece hp (hgh hgne) (by simpa using hne)
              (loopRun_of_loop f rest' _ (p + 1) c r (hinv.set hp) h)
        · -- 最後の piece
          simp only [Option.some.injEq] at h
          subst h
          have hgne : g ≠ [] := by rintro rfl; simp at hdec
          rw [hdec, List.append_nil]
          exact .last hp (hgh hgne)
        · simp at h

theorem hex_of_dec {c : Char} (h : IsDecDigit c) : IsHexDigit c := Or.inl h

/-- 255 以下で、二桁以上なら `0` で始まらない数は、高々三桁である。 -/
theorem DecOctet.length_le {d : List Char} (h : DecOctet d) : d.length ≤ 3 := by
  obtain ⟨hne, hall, hz, hv⟩ := h
  refine Classical.byContradiction fun hl => ?_
  obtain ⟨c, t, rfl⟩ : ∃ c t, d = c :: t := by
    cases d with
    | nil => exact absurd rfl hne
    | cons c t => exact ⟨c, t, rfl⟩
  have hc0 : c ≠ '0' := fun e => hz (by simp at hl ⊢; omega) (by simp [e])
  have hcd := hall c (by simp)
  have hpos : 1 ≤ digitVal c := by
    unfold digitVal IsDecDigit at *
    have : c.toNat ≠ 48 := fun e => hc0 (by rw [← Char.ofNat_toNat c, e])
    split <;> omega
  have : 1000 ≤ radixValue 10 (c :: t) := by
    simp only [radixValue]
    have h3 : 3 ≤ t.length := by simp at hl; omega
    have : 10 ^ 3 ≤ 10 ^ t.length := Nat.pow_le_pow_right (by omega) h3
    have : 1 * 10 ^ 3 ≤ digitVal c * 10 ^ t.length := Nat.mul_le_mul hpos this
    omega
  omega

/-- IPv4-in-IPv6 の入力は、`takeHex 4` で見ると最初の数を読んだところで `.` に当たる。 -/
theorem takeHex_ipv4 {l : List Char} {x y : Nat} (h : Ipv4Text l x y) :
    ∃ v len tail, takeHex 4 l = (v, len, '.' :: tail) ∧ len ≠ 0 := by
  obtain ⟨d1, d2, d3, d4, rfl, hd1, -, -, -, -, -⟩ := h
  have h16 : H16 d1 := ⟨hd1.1, by have := hd1.length_le; omega, fun c hc => hex_of_dec (hd1.2.1 c hc)⟩
  refine ⟨_, _, _, takeHex_h16 h16 (fun c r he => by simp at he; rw [← he.1]; decide), ?_⟩
  intro h0; exact hd1.1 (List.length_eq_zero_iff.mp h0)

/-- **`LoopRun` の走行は、fuel が足りれば loop が実際にたどる。** -/
theorem loop_of_loopRun {l : List Char} {a : Ipv6} {p : Nat} {c : Option Nat}
    {r : Ipv6 × Nat × Option Nat} (h : LoopRun l a p c r) :
    ∀ fuel, 9 - p ≤ fuel → LoopInv a p → ipv6Loop fuel l a p c = some r := by
  induction h with
  | eof =>
    intro fuel hf hinv
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by have := hinv.2.1; omega⟩
    simp [ipv6Loop]
  | @compress rest a p r hp _ ih =>
    intro fuel hf hinv
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by have := hinv.2.1; omega⟩
    simp only [ipv6Loop, beq_iff_eq, hp, if_false, Option.isSome_none, Bool.false_eq_true]
    exact ih f (by omega) (hinv.succ hp)
  | @piece g rest a p c r hp hg hne _ ih =>
    intro fuel hf hinv
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by have := hinv.2.1; omega⟩
    obtain ⟨c0, g', rfl⟩ : ∃ c0 g', g = c0 :: g' := by
      cases g with
      | nil => exact absurd rfl hg.1
      | cons c0 g' => exact ⟨c0, g', rfl⟩
    have hc0 : c0 ≠ ':' := fun e => by
      have := hg.2.2 c0 (by simp); rw [e] at this; revert this; decide
    have ht := takeHex_h16 (rest := ':' :: rest) hg (fun c r he => by simp at he; rw [← he.1]; decide)
    simp only [List.cons_append] at ht ⊢
    simp only [ipv6Loop, beq_iff_eq, hp, if_false]
    split
    · next _ _ he => simp at he; exact absurd he.1 hc0
    · rw [ht]
      simp only [List.isEmpty_iff, hne, if_false]
      exact ih f (by omega) (hinv.set hp)
  | @last g a p c hp hg =>
    intro fuel hf hinv
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by have := hinv.2.1; omega⟩
    obtain ⟨c0, g', rfl⟩ : ∃ c0 g', g = c0 :: g' := by
      cases g with
      | nil => exact absurd rfl hg.1
      | cons c0 g' => exact ⟨c0, g', rfl⟩
    have hc0 : c0 ≠ ':' := fun e => by
      have := hg.2.2 c0 (by simp); rw [e] at this; revert this; decide
    have ht := takeHex_h16 (rest := []) hg (fun c r he => by cases he)
    simp only [List.append_nil] at ht
    simp only [ipv6Loop, beq_iff_eq, hp, if_false]
    split
    · next _ _ he => simp at he; exact absurd he.1 hc0
    · rw [ht]
  | @ipv4 l a p c x y hp6 htext =>
    intro fuel hf hinv
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by have := hinv.2.1; omega⟩
    obtain ⟨v, len, tail, ht, hlen⟩ := takeHex_ipv4 htext
    have hip := (ipv4InIpv6_iff l a p (by rw [hinv.1]; omega) (hinv.2.2 p (Nat.le_refl _))
      (hinv.2.2 (p + 1) (by omega)) _).mpr ⟨x, y, htext, rfl⟩
    obtain ⟨d1, d2, d3, d4, rfl, hd1, -⟩ := htext
    obtain ⟨c0, d1', rfl⟩ : ∃ c0 d1', d1 = c0 :: d1' := by
      cases d1 with
      | nil => exact absurd rfl hd1.1
      | cons c0 d1' => exact ⟨c0, d1', rfl⟩
    have hc0 : c0 ≠ ':' := fun e => by
      have := hd1.2.1 c0 (by simp); rw [e] at this; revert this; decide
    simp only [List.cons_append] at ht hip ⊢
    simp only [ipv6Loop, beq_iff_eq, show p ≠ 8 by omega, if_false]
    split
    · next _ _ he => simp at he; exact absurd he.1 hc0
    · rw [ht]
      simp only [hlen, if_false, show ¬p > 6 by omega, hip]

/-! ## 文法 -/

/-- piece を `:` で区切って並べたもの。値の列を返す。 -/
inductive Groups : List Char → List Nat → Prop
  | one {g : List Char} : H16 g → Groups g [radixValue 16 g]
  | cons {g r : List Char} {vs : List Nat} : H16 g → Groups r vs →
      Groups (g ++ ':' :: r) (radixValue 16 g :: vs)

/-- 省略の後ろ（または省略しない全体）。piece の並びか、その後に dotted decimal の IPv4（2 piece ぶん）。 -/
inductive Tail : List Char → List Nat → Prop
  | groups {l : List Char} {vs : List Nat} : Groups l vs → Tail l vs
  | ipv4 {l : List Char} {x y : Nat} : Ipv4Text l x y → Tail l [x, y]
  | groupsIpv4 {g t : List Char} {vs : List Nat} {x y : Nat} : Groups g vs → Ipv4Text t x y →
      Tail (g ++ ':' :: t) (vs ++ [x, y])

/--
§3.3 IPv6 parser が受け付ける文字列（RFC 4291 §2.2 の形）。

* 省略しない形：8 piece ちょうど。
* `::` を一度だけ使う形：前と後ろの piece は合わせて 7 個以下で、`::` は残りを 0 で埋める。
-/
inductive Ipv6Text : List Char → Ipv6 → Prop
  | full {l : List Char} {vs : List Nat} : Tail l vs → vs.length = 8 → Ipv6Text l vs
  | compress {L R : List Char} {ls rs : List Nat} : (L = [] ∧ ls = [] ∨ Groups L ls) →
      (R = [] ∧ rs = [] ∨ Tail R rs) → ls.length + rs.length ≤ 7 →
      Ipv6Text (L ++ ':' :: ':' :: R) (ls ++ List.replicate (8 - ls.length - rs.length) 0 ++ rs)

/-! ## loop の走行と文法 -/

/-- address の `p` 番目から値を順に書く。 -/
def setMany : Ipv6 → Nat → List Nat → Ipv6
  | a, _, [] => a
  | a, p, v :: vs => setMany (a.set p v) (p + 1) vs

/-- 区切りの `:` を後ろに付けた piece の並び（`::` の前の部分）。 -/
inductive GroupsSep : List Char → List Nat → Prop
  | nil : GroupsSep [] []
  | cons {g r : List Char} {vs : List Nat} : H16 g → GroupsSep r vs →
      GroupsSep (g ++ ':' :: r) (radixValue 16 g :: vs)

/-- loop の走行の形。何も読まない、省略なしの piece の並び、省略を一度含む、の三通り。 -/
def LoopShape (input : List Char) (a : Ipv6) (p : Nat) (c : Option Nat)
    (r : Ipv6 × Nat × Option Nat) : Prop :=
  (input = [] ∧ r = (a, p, c)) ∨
  (∃ vs, Tail input vs ∧ p + vs.length ≤ 8 ∧ r = (setMany a p vs, p + vs.length, c)) ∨
  (c = none ∧ ∃ Lsep ls R rs, GroupsSep Lsep ls ∧ input = Lsep ++ ':' :: R ∧
    (R = [] ∧ rs = [] ∨ Tail R rs) ∧ p + ls.length + 1 + rs.length ≤ 8 ∧
    r = (setMany (setMany a p ls) (p + ls.length + 1) rs, p + ls.length + 1 + rs.length,
         some (p + ls.length + 1)))

/-- piece を一つ前に足しても `Tail` のまま。 -/
theorem Tail.cons {g rest : List Char} {vs : List Nat} (hg : H16 g) (ht : Tail rest vs) :
    Tail (g ++ ':' :: rest) (radixValue 16 g :: vs) := by
  cases ht with
  | groups h => exact .groups (.cons hg h)
  | ipv4 h => exact .groupsIpv4 (vs := [radixValue 16 g]) (.one hg) h
  | @groupsIpv4 g2 t vs2 x y hg2 hi =>
    have := Tail.groupsIpv4 (Groups.cons hg hg2) hi
    simpa [List.append_assoc] using this

/-- **loop の走行は三つの形のどれかである。** -/
theorem LoopRun.shape {input : List Char} {a : Ipv6} {p : Nat} {c : Option Nat}
    {r : Ipv6 × Nat × Option Nat} (h : LoopRun input a p c r) (hp : p ≤ 8) :
    LoopShape input a p c r := by
  induction h with
  | eof => exact .inl ⟨rfl, rfl⟩
  | @compress rest a p r hp8 _ ih =>
    rcases ih (by omega) with ⟨rfl, rfl⟩ | ⟨rs, ht, hb, rfl⟩ | ⟨hc, -⟩
    · exact .inr (.inr ⟨rfl, [], [], [], [], .nil, rfl, .inl ⟨rfl, rfl⟩, by simp; omega,
        by simp [setMany]⟩)
    · exact .inr (.inr ⟨rfl, [], [], rest, rs, .nil, rfl, .inr ht, by simp; omega,
        by simp [setMany]⟩)
    · cases hc
  | @piece g rest a p c r hp8 hg hne _ ih =>
    rcases ih (by omega) with ⟨rfl, -⟩ | ⟨vs, ht, hb, rfl⟩ | ⟨rfl, Lsep, ls, R, rs, hl, rfl, hR, hb, rfl⟩
    · exact absurd rfl hne
    · exact .inr (.inl ⟨_, ht.cons hg, by simp; omega, by simp [setMany]; omega⟩)
    · refine .inr (.inr ⟨rfl, g ++ ':' :: Lsep, radixValue 16 g :: ls, R, rs, .cons hg hl,
        by simp [List.append_assoc], hR, by simp; omega, ?_⟩)
      simp only [setMany, List.length_cons]
      rw [show p + (ls.length + 1) + 1 = p + 1 + ls.length + 1 by omega]
  | @last g a p c hp8 hg =>
    exact .inr (.inl ⟨_, .groups (.one hg), by simp; omega, by simp [setMany]⟩)
  | @ipv4 l a p c x y hp6 ht =>
    exact .inr (.inl ⟨_, .ipv4 ht, by simp; omega, by simp [setMany]⟩)

theorem Groups.ne_nil {l : List Char} {vs : List Nat} (h : Groups l vs) : l ≠ [] := by
  cases h with
  | one hg => exact hg.1
  | cons hg _ => simp

theorem Groups.length_pos {l : List Char} {vs : List Nat} (h : Groups l vs) : 0 < vs.length := by
  cases h <;> simp

/-- **piece の並びは、最後まで読めば値を順に書く。** -/
theorem loopRun_groups {l : List Char} {vs : List Nat} (h : Groups l vs) :
    ∀ (a : Ipv6) (p : Nat) (c : Option Nat), p + vs.length ≤ 8 →
      LoopRun l a p c (setMany a p vs, p + vs.length, c) := by
  induction h with
  | one hg =>
    intro a p c hb
    simp only [List.length_singleton] at hb ⊢
    exact .last (by omega) hg
  | @cons g r vs hg hr ih =>
    intro a p c hb
    simp only [List.length_cons] at hb ⊢
    have := ih (a.set p (radixValue 16 g)) (p + 1) c (by omega)
    rw [show p + 1 + vs.length = p + (vs.length + 1) by omega] at this
    exact .piece (by omega) hg hr.ne_nil this

/-- piece の並びの後に区切りの `:` と続きがあれば、値を書いてから続きを読む。 -/
theorem loopRun_groupsThen {g : List Char} {vs : List Nat} (h : Groups g vs) :
    ∀ (X : List Char) (a : Ipv6) (p : Nat) (c : Option Nat) (r : Ipv6 × Nat × Option Nat),
      X ≠ [] → p + vs.length ≤ 8 → LoopRun X (setMany a p vs) (p + vs.length) c r →
      LoopRun (g ++ ':' :: X) a p c r := by
  induction h with
  | one hg =>
    intro X a p c r hX hb hr
    simp only [List.length_singleton, setMany] at hb hr
    exact .piece (by omega) hg hX hr
  | @cons g0 r0 vs hg hr0 ih =>
    intro X a p c r hX hb hr
    simp only [List.length_cons, setMany] at hb hr
    rw [List.append_assoc, List.cons_append]
    refine .piece (by omega) hg (by simp) (ih X _ (p + 1) c r hX (by omega) ?_)
    rwa [show p + 1 + vs.length = p + (vs.length + 1) by omega]

/-- **省略の後ろ（または全体）は、最後まで読めば値を順に書く。** -/
theorem loopRun_tail {l : List Char} {vs : List Nat} (h : Tail l vs) (a : Ipv6) (p : Nat)
    (c : Option Nat) (hb : p + vs.length ≤ 8) :
    LoopRun l a p c (setMany a p vs, p + vs.length, c) := by
  cases h with
  | groups hg => exact loopRun_groups hg a p c hb
  | ipv4 hi =>
    simp only [List.length_cons, List.length_nil] at hb ⊢
    exact .ipv4 (by omega) hi
  | @groupsIpv4 g t vs x y hg hi =>
    simp only [List.length_append, List.length_cons, List.length_nil] at hb ⊢
    refine loopRun_groupsThen hg t a p c _ ?_ (by omega) ?_
    · obtain ⟨d1, -, -, -, rfl, hd1, -⟩ := hi
      cases d1 with
      | nil => exact absurd rfl hd1.1
      | cons _ _ => simp
    · have hset : setMany a p (vs ++ [x, y]) = (setMany a p vs |>.set (p + vs.length) x).set
          (p + vs.length + 1) y := by
        clear hg hi hb
        induction vs generalizing a p with
        | nil => simp [setMany]
        | cons v vs ih =>
          simp only [List.cons_append, setMany, List.length_cons]
          rw [ih]
          rw [show p + 1 + vs.length = p + (vs.length + 1) by omega]
      rw [hset, show p + (vs.length + 2) = p + vs.length + 2 by omega]
      exact .ipv4 (by omega) hi

/-- `::` の前の部分（区切りの `:` 込み）を読み、続きへ渡す。 -/
theorem loopRun_sep {Lsep : List Char} {ls : List Nat} (h : GroupsSep Lsep ls) :
    ∀ (X : List Char) (a : Ipv6) (p : Nat) (c : Option Nat) (r : Ipv6 × Nat × Option Nat),
      X ≠ [] → p + ls.length ≤ 8 → LoopRun X (setMany a p ls) (p + ls.length) c r →
      LoopRun (Lsep ++ X) a p c r := by
  induction h with
  | nil => intro X a p c r _ _ hr; simpa [setMany] using hr
  | @cons g r0 vs hg _ ih =>
    intro X a p c r hX hb hr
    simp only [List.length_cons, setMany] at hb hr
    rw [List.append_assoc, List.cons_append]
    refine .piece (by omega) hg (by intro he; exact hX (List.append_eq_nil_iff.mp he).2)
      (ih X _ (p + 1) c r hX (by omega) ?_)
    rwa [show p + 1 + vs.length = p + (vs.length + 1) by omega]

theorem Groups.sep {L : List Char} {ls : List Nat} (h : Groups L ls) :
    GroupsSep (L ++ [':']) ls := by
  induction h with
  | one hg => exact .cons hg .nil
  | cons hg _ ih => simpa [List.append_assoc] using GroupsSep.cons hg ih

theorem GroupsSep.groups {Lsep : List Char} {ls : List Nat} (h : GroupsSep Lsep ls)
    (hne : Lsep ≠ []) : ∃ L, Lsep = L ++ [':'] ∧ Groups L ls := by
  induction h with
  | nil => exact absurd rfl hne
  | @cons g r vs hg hr ih =>
    by_cases hr0 : r = []
    · subst hr0
      have hvs : vs = [] := by
        generalize hL : ([] : List Char) = L at hr
        cases hr with
        | nil => rfl
        | cons _ _ => simp at hL
      subst hvs
      exact ⟨g, rfl, .one hg⟩
    · obtain ⟨L, rfl, hL⟩ := ih hr0
      exact ⟨g ++ ':' :: L, by simp, .cons hg hL⟩

/-! ## address の計算 -/

theorem setMany_eq : ∀ (vs : List Nat) (a : List Nat) (p : Nat), p + vs.length ≤ a.length →
    setMany a p vs = a.take p ++ vs ++ a.drop (p + vs.length)
  | [], a, p, _ => by simp [setMany]
  | v :: vs, a, p, h => by
    simp only [List.length_cons] at h
    simp only [setMany]
    rw [setMany_eq vs (a.set p v) (p + 1) (by simp; omega)]
    rw [List.set_eq_take_append_cons_drop, if_pos (by omega)]
    have hl : (a.take p).length = p := by simp; omega
    simp only [List.length_cons]
    rw [List.take_append, hl, show p + 1 - p = 1 by omega]
    rw [List.take_of_length_le (by omega), List.drop_append, hl]
    simp only [show p + 1 + vs.length - p = vs.length + 1 by omega,
      List.drop_eq_nil_of_le (show (a.take p).length ≤ p + 1 + vs.length by omega),
      List.nil_append, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_drop]
    rw [show p + 1 + vs.length = vs.length + (p + 1) by omega]
    simp [List.append_assoc, show p + (vs.length + 1) = vs.length + (p + 1) by omega]

theorem ipv6Zero_eq : ipv6Zero = List.replicate 8 0 := rfl

theorem loopInv_zero {p : Nat} (hp : p ≤ 8) : LoopInv ipv6Zero p :=
  ⟨rfl, hp, fun j _ => ipv6Zero_getD j⟩

/-- 省略なしで 8 piece を書けば、address はその列そのものである。 -/
theorem setMany_zero_full {vs : List Nat} (h : vs.length = 8) : setMany ipv6Zero 0 vs = vs := by
  rw [setMany_eq vs ipv6Zero 0 (by simp [ipv6Zero_eq, h])]
  simp [ipv6Zero_eq, h]

/-- **`::` の展開。** 前の piece、残りの 0、後ろの piece の順に並ぶ。 -/
theorem expand_eq (ls rs : List Nat) (hb : ls.length + rs.length ≤ 7) :
    ipv6Expand (setMany (setMany ipv6Zero 0 ls) (ls.length + 1) rs) (ls.length + 1 + rs.length)
        (ls.length + 1)
      = ls ++ List.replicate (8 - ls.length - rs.length) 0 ++ rs := by
  have h1 : setMany ipv6Zero 0 ls = ls ++ List.replicate (8 - ls.length) 0 := by
    rw [setMany_eq ls ipv6Zero 0 (by simp [ipv6Zero_eq]; omega)]
    simp only [ipv6Zero_eq, List.take_zero, List.nil_append, Nat.zero_add, List.drop_replicate]
  have hrep : List.replicate (8 - ls.length) 0
      = 0 :: List.replicate (7 - ls.length) 0 := by
    rw [show 8 - ls.length = (7 - ls.length) + 1 by omega, List.replicate_succ]
  rw [h1, hrep]
  have hk : (ls ++ 0 :: List.replicate (7 - ls.length) 0).take (ls.length + 1) = ls ++ [0] := by
    simp [List.take_append, List.take_of_length_le (show ls.length ≤ ls.length + 1 by omega)]
  have hd : (ls ++ 0 :: List.replicate (7 - ls.length) 0).drop (ls.length + 1 + rs.length)
      = List.replicate (7 - ls.length - rs.length) 0 := by
    rw [List.drop_append, show ls.length + 1 + rs.length - ls.length = rs.length + 1 by omega]
    simp [List.drop_replicate]
    omega
  rw [setMany_eq rs _ (ls.length + 1) (by simp; omega), hk, hd]
  unfold ipv6Expand
  simp only [Nat.add_sub_cancel_left]
  have e1 : (ls ++ [0] ++ rs ++ List.replicate (7 - ls.length - rs.length) 0).take (ls.length + 1)
      = ls ++ [0] := by
    rw [List.append_assoc, List.append_assoc, List.take_append]
    simp [List.take_of_length_le (show ls.length ≤ ls.length + 1 by omega)]
  have e2 : ((ls ++ [0] ++ rs ++ List.replicate (7 - ls.length - rs.length) 0).drop
      (ls.length + 1)).take rs.length = rs := by
    rw [show ls ++ [0] ++ rs ++ List.replicate (7 - ls.length - rs.length) 0
        = (ls ++ [0]) ++ (rs ++ List.replicate (7 - ls.length - rs.length) 0) by simp,
      List.drop_left' (by simp)]
    simp
  rw [e1, e2]
  have e3 : List.replicate (8 - (ls.length + 1) - rs.length) 0 = List.replicate (7 - ls.length - rs.length) 0 := by
    congr 1; omega
  rw [e3, show 8 - ls.length - rs.length = (7 - ls.length - rs.length) + 1 by omega,
    List.replicate_succ]
  simp

/-! ## IPv6 parser -/

theorem colon_not_hex : ¬ IsHexDigit ':' := by decide

theorem H16.head {g : List Char} (h : H16 g) : ∃ c t, g = c :: t ∧ c ≠ ':' := by
  obtain ⟨c, t, rfl⟩ : ∃ c t, g = c :: t := by
    cases g with
    | nil => exact absurd rfl h.1
    | cons c t => exact ⟨c, t, rfl⟩
  exact ⟨c, t, rfl, fun e => colon_not_hex (e ▸ h.2.2 c (by simp))⟩

theorem Groups.head {l : List Char} {vs : List Nat} (h : Groups l vs) :
    ∃ c t, l = c :: t ∧ c ≠ ':' := by
  cases h with
  | one hg => exact hg.head
  | cons hg _ =>
    obtain ⟨c, t, rfl, hc⟩ := hg.head
    exact ⟨c, _, rfl, hc⟩

theorem Ipv4Text.head {l : List Char} {x y : Nat} (h : Ipv4Text l x y) :
    ∃ c t, l = c :: t ∧ c ≠ ':' := by
  obtain ⟨d1, d2, d3, d4, rfl, hd1, -⟩ := h
  obtain ⟨c, t, rfl⟩ : ∃ c t, d1 = c :: t := by
    cases d1 with
    | nil => exact absurd rfl hd1.1
    | cons c t => exact ⟨c, t, rfl⟩
  refine ⟨c, _, rfl, fun e => ?_⟩
  have := hd1.2.1 c (by simp); rw [e] at this; revert this; decide

theorem Tail.head {l : List Char} {vs : List Nat} (h : Tail l vs) : ∃ c t, l = c :: t ∧ c ≠ ':' := by
  cases h with
  | groups hg => exact hg.head
  | ipv4 hi => exact hi.head
  | groupsIpv4 hg _ =>
    obtain ⟨c, t, rfl, hc⟩ := hg.head
    exact ⟨c, _, rfl, hc⟩

/-- 先頭が `:` でない入力は、loop を先頭から走らせる。 -/
theorem ipv6Parser_plain {input : List Char} (h : ∀ t, input ≠ ':' :: t) :
    ipv6Parser input = (match ipv6Loop 9 input ipv6Zero 0 none with
      | none => none
      | some (address, pieceIndex, compress) => ipv6Parser.ipv6Finish address pieceIndex compress) := by
  unfold ipv6Parser
  split
  · next rest => exact absurd rfl (h (':' :: rest))
  · next t _ => exact absurd rfl (h t)
  · rfl

/-- **IPv6 parser は関係 `Ipv6Text` を計算する。** 入力に制限は無い。 -/
theorem ipv6Parser_iff (input : List Char) (a : Ipv6) :
    ipv6Parser input = some a ↔ Ipv6Text input a := by
  constructor
  · intro h
    by_cases h1 : ∃ rest, input = ':' :: ':' :: rest
    · obtain ⟨rest, rfl⟩ := h1
      simp only [ipv6Parser] at h
      split at h
      · simp at h
      · next a' p' c' hloop =>
        have hrun := loopRun_of_loop 9 rest ipv6Zero 1 (some 1) _ (loopInv_zero (by omega)) hloop
        rcases hrun.shape (by omega) with ⟨rfl, he⟩ | ⟨rs, ht, hb, he⟩ | ⟨hc, -⟩
        · simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl, rfl⟩ := he
          simp only [ipv6Parser.ipv6Finish, Option.some.injEq] at h
          subst h
          have := expand_eq [] [] (by simp)
          simp only [setMany, List.length_nil, Nat.zero_add] at this
          rw [this]
          exact Ipv6Text.compress (L := []) (R := []) (.inl ⟨rfl, rfl⟩) (.inl ⟨rfl, rfl⟩) (by simp)
        · simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl, rfl⟩ := he
          simp only [ipv6Parser.ipv6Finish, Option.some.injEq] at h
          subst h
          have := expand_eq [] rs (by simp; omega)
          simp only [setMany, List.length_nil, Nat.zero_add] at this
          rw [this]
          exact Ipv6Text.compress (L := []) (.inl ⟨rfl, rfl⟩) (.inr ht) (by simp; omega)
        · cases hc
    · by_cases h2 : ∃ x, input = ':' :: x
      · obtain ⟨x, rfl⟩ := h2
        have hx : ∀ rest, x ≠ ':' :: rest := fun rest he => h1 ⟨rest, by rw [he]⟩
        simp only [ipv6Parser] at h
        first
          | simp at h
          | (split at h
             · next rest he => simp at he; exact absurd he (hx rest)
             · simp at h
             · next hn _ => exact absurd rfl (hn x))
      · have h2' : ∀ t, input ≠ ':' :: t := fun t he => h2 ⟨t, he⟩
        rw [ipv6Parser_plain h2'] at h
        split at h
        · simp at h
        · next a' p' c' hloop =>
          have hrun := loopRun_of_loop 9 input ipv6Zero 0 none _ (loopInv_zero (by omega)) hloop
          rcases hrun.shape (by omega) with ⟨rfl, he⟩ | ⟨vs, ht, hb, he⟩ |
              ⟨-, Lsep, ls, R, rs, hl, rfl, hR, hb, he⟩
          · simp only [Prod.mk.injEq] at he
            obtain ⟨rfl, rfl, rfl⟩ := he
            simp [ipv6Parser.ipv6Finish] at h
          · simp only [Prod.mk.injEq] at he
            obtain ⟨rfl, rfl, rfl⟩ := he
            simp only [ipv6Parser.ipv6Finish, Nat.zero_add] at h
            split at h
            · next h8 =>
              simp only [beq_iff_eq] at h8
              simp only [Option.some.injEq] at h
              subst h
              rw [setMany_zero_full h8]
              exact .full ht h8
            · simp at h
          · simp only [Prod.mk.injEq] at he
            obtain ⟨rfl, rfl, rfl⟩ := he
            have hLne : Lsep ≠ [] := by
              rintro rfl
              exact h2 ⟨R, rfl⟩
            obtain ⟨L, rfl, hL⟩ := hl.groups hLne
            simp only [ipv6Parser.ipv6Finish, Nat.zero_add, Option.some.injEq] at h
            subst h
            rw [expand_eq ls rs (by omega)]
            have := Ipv6Text.compress (.inr hL) hR (by omega)
            simpa [List.append_assoc] using this
  · intro h
    cases h with
    | @full l vs ht h8 =>
      obtain ⟨c, t, rfl, hc⟩ := ht.head
      rw [ipv6Parser_plain (fun t' he => hc (List.cons.inj he).1)]
      have hrun := loopRun_tail ht ipv6Zero 0 none (by omega)
      rw [loop_of_loopRun hrun 9 (by omega) (loopInv_zero (by omega))]
      simp [ipv6Parser.ipv6Finish, h8, setMany_zero_full h8]
    | @compress L R ls rs hL hR hb =>
      have hrunR : ∀ q, q + 1 + rs.length ≤ 8 → ∀ a0 : Ipv6,
          LoopRun R a0 (q + 1) (some (q + 1))
            (setMany a0 (q + 1) rs, q + 1 + rs.length, some (q + 1)) := by
        intro q hq a0
        rcases hR with ⟨rfl, rfl⟩ | ht
        · simpa [setMany] using (LoopRun.eof : LoopRun [] a0 (q + 1) (some (q + 1)) _)
        · exact loopRun_tail ht a0 (q + 1) (some (q + 1)) hq
      rcases hL with ⟨rfl, rfl⟩ | hL
      · simp only [List.nil_append, ipv6Parser]
        rw [loop_of_loopRun (hrunR 0 (by simp; omega) ipv6Zero) 9 (by omega)
          (loopInv_zero (by omega))]
        simp only [ipv6Parser.ipv6Finish, Option.some.injEq]
        have := expand_eq [] rs (by simp; omega)
        simp only [setMany, List.length_nil, Nat.zero_add] at this
        simpa using this
      · obtain ⟨c, t, he, hc⟩ := hL.head
        rw [ipv6Parser_plain (fun t' h' => by rw [he] at h'; exact hc (List.cons.inj h').1)]
        have hrun : LoopRun (L ++ ':' :: ':' :: R) ipv6Zero 0 none
            (setMany (setMany ipv6Zero 0 ls) (ls.length + 1) rs, ls.length + 1 + rs.length,
              some (ls.length + 1)) := by
          refine loopRun_groupsThen hL (':' :: R) ipv6Zero 0 none _ (by simp) (by omega) ?_
          simp only [Nat.zero_add]
          exact .compress (by omega) (hrunR ls.length (by omega) _)
        rw [loop_of_loopRun hrun 9 (by omega) (loopInv_zero (by omega))]
        simp only [ipv6Parser.ipv6Finish, Option.some.injEq]
        rw [expand_eq ls rs (by omega)]

/-! ## 証人

関係の側で書いた結果を、実装を `decide` で計算して確かめる。
-/

/-- `1::2` は前に 1 piece、後ろに 1 piece で、`::` が 6 piece の 0 を埋める。 -/
example : Ipv6Text "1::2".toList [1, 0, 0, 0, 0, 0, 0, 2] := (ipv6Parser_iff _ _).mp (by decide)

/-- dotted decimal の IPv4 は最後の 2 piece になる。 -/
example : Ipv6Text "::ffff:1.2.3.4".toList [0, 0, 0, 0, 0, 0xffff, 0x0102, 0x0304] :=
  (ipv6Parser_iff _ _).mp (by decide)

/-- `::` は一度だけ。 -/
example (a : Ipv6) : ¬ Ipv6Text "1:::2".toList a := fun h => by
  have h' := (ipv6Parser_iff _ _).mpr h
  rw [show ipv6Parser "1:::2".toList = none by decide] at h'
  cases h'

/-- dotted decimal の数は `0` で始まれない（`04`）。 -/
example (a : Ipv6) : ¬ Ipv6Text "::1.2.3.04".toList a := fun h => by
  have h' := (ipv6Parser_iff _ _).mpr h
  rw [show ipv6Parser "::1.2.3.04".toList = none by decide] at h'
  cases h'

end Url.Spec
