import Url.Spec.Path
import Url.Ipv4

/-!
# IPv4 の関係仕様（§3.3 IPv4 number parser、IPv4 parser、ends in a number checker）

`Url/Ipv4.lean` の実装は、基数を `Option` の左畳み込みで読み、part を `strictSplit` で分け、
part の値を `256 * acc + n` で畳み込んで最後に `256^(5 - size)` を掛ける。
ここでは同じものを、本文の言い回しのまま書く。

* 値は桁の重みで書く（`radixValue`。「represented by input in radix-R notation」）。
* 基数の決め方は本文の三つの場合をそのまま構成子にする（`Ipv4Number`）。
* part は `.` での strict split（`SplitBy`）で、最後の空の part は part が 2 個以上のときだけ落とす。
* アドレスは「最後の数に、残りの数を `256^(3 - counter)` 倍して足す」（`ipv4Sum`）。

digit の範囲は本文の範囲で直に書き、`Infra.hexValue` も `radixDigit` も呼ばない。
-/

namespace Url.Spec

open Infra Url

/-! ## 基数 -/

/-- ASCII digit（0x30-0x39）。 -/
def IsDecDigit (c : Char) : Prop := 0x30 ≤ c.toNat ∧ c.toNat ≤ 0x39

/-- 8 進の digit（0x30-0x37）。 -/
def IsOctDigit (c : Char) : Prop := 0x30 ≤ c.toNat ∧ c.toNat ≤ 0x37

/-- ASCII hex digit（0x30-0x39、0x41-0x46、0x61-0x66）。 -/
def IsHexDigit (c : Char) : Prop :=
  (0x30 ≤ c.toNat ∧ c.toNat ≤ 0x39) ∨ (0x41 ≤ c.toNat ∧ c.toNat ≤ 0x46) ∨
    (0x61 ≤ c.toNat ∧ c.toNat ≤ 0x66)

instance (c : Char) : Decidable (IsDecDigit c) := by unfold IsDecDigit; infer_instance
instance (c : Char) : Decidable (IsOctDigit c) := by unfold IsOctDigit; infer_instance
instance (c : Char) : Decidable (IsHexDigit c) := by unfold IsHexDigit; infer_instance

/-- digit の値。ASCII hex digit の値 0 から 15。 -/
def digitVal (c : Char) : Nat :=
  if c.toNat ≤ 0x39 then c.toNat - 0x30
  else if c.toNat ≤ 0x46 then c.toNat - 0x41 + 10
  else c.toNat - 0x61 + 10

/-- 基数 `R` の表記が表す値。桁の重みで書く。 -/
def radixValue (R : Nat) : List Char → Nat
  | [] => 0
  | c :: rest => digitVal c * R ^ rest.length + radixValue R rest

/--
§3.3 IPv4 number parser。`Ipv4Number input n v` は「`input` を読むと `(n, v)`」。

* step 4：二文字以上で `0x` か `0X` で始まれば、残りを 16 進で読み、validation error。残りが空なら 0（step 6）。
* step 5：二文字以上で `0` で始まれば（`0x` でなければ）、残りを 8 進で読み、validation error。
* それ以外：空でなければ 10 進で読む。
-/
inductive Ipv4Number : List Char → Nat → Bool → Prop
  | hex {x : Char} {t : List Char} : (x = 'x' ∨ x = 'X') → (∀ c ∈ t, IsHexDigit c) →
      Ipv4Number ('0' :: x :: t) (radixValue 16 t) true
  | octal {x : Char} {t : List Char} : x ≠ 'x' → x ≠ 'X' → (∀ c ∈ x :: t, IsOctDigit c) →
      Ipv4Number ('0' :: x :: t) (radixValue 8 (x :: t)) true
  | decimal {l : List Char} : l ≠ [] → (∀ x t, l ≠ '0' :: x :: t) → (∀ c ∈ l, IsDecDigit c) →
      Ipv4Number l (radixValue 10 l) false

/-! ## 実装との対応 -/

/-- `Infra.hexValue` は本文の範囲と値に一致する。 -/
theorem hexValue_eq (c : Char) :
    hexValue c = if IsHexDigit c then some (digitVal c) else none := by
  unfold hexValue digitVal
  by_cases hh : IsHexDigit c
  · rw [if_pos hh]
    unfold IsHexDigit at hh
    repeat' split
    all_goals first
      | rfl
      | (exfalso; simp only [Bool.and_eq_true, decide_eq_true_eq] at *; omega)
      | (simp only [Bool.and_eq_true, decide_eq_true_eq, Option.some.injEq] at *; omega)
  · rw [if_neg hh]
    unfold IsHexDigit at hh
    repeat' split
    all_goals first
      | rfl
      | (exfalso; simp only [Bool.and_eq_true, decide_eq_true_eq] at *; omega)

/-- 基数 `R`（8・10・16）の digit。 -/
def IsRadixDigit (R : Nat) (c : Char) : Prop :=
  (R = 16 ∧ IsHexDigit c) ∨ (R = 10 ∧ IsDecDigit c) ∨ (R = 8 ∧ IsOctDigit c)

instance (R : Nat) (c : Char) : Decidable (IsRadixDigit R c) := by
  unfold IsRadixDigit; infer_instance

/-- 実装の `radixDigit` は、基数が 8・10・16 なら本文の範囲と値に一致する。 -/
theorem radixDigit_eq (R : Nat) (hR : R = 8 ∨ R = 10 ∨ R = 16) (c : Char) :
    radixDigit R c = if IsRadixDigit R c then some (digitVal c) else none := by
  unfold radixDigit
  rw [hexValue_eq]
  by_cases hh : IsHexDigit c
  · rw [if_pos hh]
    simp only
    have hv : digitVal c < 16 := by
      unfold digitVal IsHexDigit at *; (repeat' split) <;> omega
    rcases hR with rfl | rfl | rfl
    · by_cases ho : IsOctDigit c
      · rw [if_pos (by unfold digitVal IsOctDigit at *; (repeat' split) <;> omega),
          if_pos (show IsRadixDigit 8 c from Or.inr (Or.inr ⟨rfl, ho⟩))]
      · rw [if_neg (by unfold digitVal IsOctDigit IsHexDigit at *; (repeat' split) <;> omega),
          if_neg (show ¬IsRadixDigit 8 c by rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩) <;> first | (simp at h) | exact ho h)]
    · by_cases hd : IsDecDigit c
      · rw [if_pos (by unfold digitVal IsDecDigit at *; (repeat' split) <;> omega),
          if_pos (show IsRadixDigit 10 c from Or.inr (Or.inl ⟨rfl, hd⟩))]
      · rw [if_neg (by unfold digitVal IsDecDigit IsHexDigit at *; (repeat' split) <;> omega),
          if_neg (show ¬IsRadixDigit 10 c by rintro (⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩) <;> first | (simp at h) | exact hd h)]
    · rw [if_pos hv, if_pos (show IsRadixDigit 16 c from Or.inl ⟨rfl, hh⟩)]
  · rw [if_neg hh, if_neg (show ¬IsRadixDigit R c from ?_)]
    rintro (⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩)
    · exact hh h
    · exact hh (Or.inl h)
    · exact hh (Or.inl ⟨h.1, by unfold IsOctDigit at h; omega⟩)

private theorem fold_none (R : Nat) : ∀ l : List Char,
    l.foldl (fun acc c => match acc, radixDigit R c with
      | some a, some v => some (a * R + v)
      | _, _ => none) none = none
  | [] => rfl
  | _ :: l => by simp only [List.foldl_cons]; exact fold_none R l

private theorem fold_some (R : Nat) (hR : R = 8 ∨ R = 10 ∨ R = 16) : ∀ (l : List Char) (a : Nat),
    l.foldl (fun acc c => match acc, radixDigit R c with
      | some a, some v => some (a * R + v)
      | _, _ => none) (some a)
      = if ∀ c ∈ l, IsRadixDigit R c then some (a * R ^ l.length + radixValue R l) else none
  | [], a => by simp [radixValue]
  | c :: l, a => by
    simp only [List.foldl_cons]
    rw [radixDigit_eq R hR c]
    by_cases hc : IsRadixDigit R c
    · rw [if_pos hc]
      simp only
      rw [fold_some R hR l]
      by_cases hl : ∀ x ∈ l, IsRadixDigit R x
      · rw [if_pos hl, if_pos (by intro x hx; rcases List.mem_cons.mp hx with rfl | hx <;> simp_all)]
        simp only [radixValue, List.length_cons, Nat.pow_succ, Option.some.injEq, Nat.add_mul,
          Nat.add_assoc]
        rw [Nat.mul_assoc a R, Nat.mul_comm R (R ^ l.length), ← Nat.mul_assoc]
      · rw [if_neg hl, if_neg (fun h => hl (fun x hx => h x (by simp [hx])))]
    · rw [if_neg hc]
      simp only
      rw [fold_none, if_neg (fun h => hc (h c (by simp)))]

/-- **実装の `parseRadix` は、空でなく全部が digit なら桁の重みで読んだ値を返す。** -/
theorem parseRadix_eq (R : Nat) (hR : R = 8 ∨ R = 10 ∨ R = 16) (l : List Char) :
    parseRadix R l = if l ≠ [] ∧ ∀ c ∈ l, IsRadixDigit R c then some (radixValue R l) else none := by
  cases l with
  | nil => simp [parseRadix]
  | cons c t =>
    simp only [parseRadix]
    refine (fold_some R hR (c :: t) 0).trans ?_
    simp

/-- `0x` / `0X` で始まる入力。 -/
theorem ipv4NumberParser_hex {x : Char} (hx : x = 'x' ∨ x = 'X') (t : List Char) :
    ipv4NumberParser ('0' :: x :: t)
      = if t = [] then some (0, true) else (parseRadix 16 t).map (·, true) := by
  rcases hx with rfl | rfl <;>
  · cases t with
    | nil => rfl
    | cons d t' =>
      simp only [ipv4NumberParser, List.isEmpty_cons, Bool.false_eq_true, if_false]
      cases parseRadix 16 (d :: t') <;> simp

/-- `0` と `x` / `X` 以外で始まる二文字以上の入力。 -/
theorem ipv4NumberParser_oct {x : Char} (hx1 : x ≠ 'x') (hx2 : x ≠ 'X') (t : List Char) :
    ipv4NumberParser ('0' :: x :: t) = (parseRadix 8 (x :: t)).map (·, true) := by
  simp only [ipv4NumberParser]
  split
  · next he => simp at he; exact absurd he.1 hx2
  · next he => simp at he; exact absurd he.1 hx1
  · next t' he =>
    simp only [List.cons.injEq, true_and] at he
    subst he
    simp only [List.isEmpty_cons, Bool.false_eq_true, if_false]
    cases parseRadix 8 (x :: t) <;> simp
  · next _ _ hn => exact (hn (x :: t) rfl).elim

/-- `0` で始まる二文字以上でない、空でない入力。 -/
theorem ipv4NumberParser_dec {l : List Char} (hne : l ≠ []) (h0 : ∀ x t, l ≠ '0' :: x :: t) :
    ipv4NumberParser l = (parseRadix 10 l).map (·, false) := by
  cases l with
  | nil => exact absurd rfl hne
  | cons c t =>
    by_cases hc : c = '0'
    · subst hc
      cases t with
      | nil => rfl
      | cons x t' => exact absurd rfl (h0 x t')
    · simp only [ipv4NumberParser]
      split
      · next he => simp at he; exact absurd he.1 hc
      · next he => simp at he; exact absurd he.1 hc
      · next t' he => simp at he; exact absurd he.1 hc
      · simp only [List.isEmpty_cons, Bool.false_eq_true, if_false]
        cases parseRadix 10 (c :: t) <;> simp

/-- **IPv4 number parser は関係 `Ipv4Number` を計算する。** 入力に制限は無い。 -/
theorem ipv4NumberParser_iff (input : List Char) (n : Nat) (v : Bool) :
    ipv4NumberParser input = some (n, v) ↔ Ipv4Number input n v := by
  constructor
  · intro h
    by_cases h0 : ∃ x t, input = '0' :: x :: t
    · obtain ⟨x, t, rfl⟩ := h0
      by_cases hx : x = 'x' ∨ x = 'X'
      · rw [ipv4NumberParser_hex hx] at h
        by_cases ht : t = []
        · subst ht
          simp at h
          obtain ⟨rfl, rfl⟩ := h
          exact .hex hx (by simp)
        · rw [if_neg ht, parseRadix_eq 16 (by decide)] at h
          split at h
          · next hc =>
            simp at h
            obtain ⟨rfl, rfl⟩ := h
            exact .hex hx (fun c hc' => by
              rcases hc.2 c hc' with ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
              · exact h
              · simp at h
              · simp at h)
          · simp at h
      · have hx1 : x ≠ 'x' := fun e => hx (Or.inl e)
        have hx2 : x ≠ 'X' := fun e => hx (Or.inr e)
        rw [ipv4NumberParser_oct hx1 hx2, parseRadix_eq 8 (by decide)] at h
        split at h
        · next hc =>
          simp at h
          obtain ⟨rfl, rfl⟩ := h
          exact .octal hx1 hx2 (fun c hc' => by
            rcases hc.2 c hc' with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
            · simp at h
            · simp at h
            · exact h)
        · simp at h
    · have h0' : ∀ x t, input ≠ '0' :: x :: t := fun x t he => h0 ⟨x, t, he⟩
      have hne : input ≠ [] := by rintro rfl; simp [ipv4NumberParser] at h
      rw [ipv4NumberParser_dec hne h0', parseRadix_eq 10 (by decide)] at h
      split at h
      · next hc =>
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        exact .decimal hne h0' (fun c hc' => by
          rcases hc.2 c hc' with ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩
          · simp at h
          · exact h
          · simp at h)
      · simp at h
  · intro h
    cases h with
    | @hex x t hx ht =>
      rw [ipv4NumberParser_hex hx]
      by_cases he : t = []
      · subst he; simp [radixValue]
      · rw [if_neg he, parseRadix_eq 16 (by decide),
          if_pos ⟨he, fun c hc => Or.inl ⟨rfl, ht c hc⟩⟩]
        rfl
    | @octal x t hx1 hx2 ht =>
      rw [ipv4NumberParser_oct hx1 hx2, parseRadix_eq 8 (by decide),
        if_pos ⟨by simp, fun c hc => Or.inr (Or.inr ⟨rfl, ht c hc⟩)⟩]
      rfl
    | @decimal l hne h0 hd =>
      rw [ipv4NumberParser_dec hne h0, parseRadix_eq 10 (by decide),
        if_pos ⟨hne, fun c hc => Or.inr (Or.inl ⟨rfl, hd c hc⟩)⟩]
      rfl

/-! ## IPv4 parser -/

/-- IPv4 parser step 2：最後の part が空なら、part が 2 個以上のときだけ落とす。 -/
def trimLastPart (parts : List (List Char)) : List (List Char) :=
  if parts.getLast? = some [] ∧ parts.length > 1 then parts.dropLast else parts

/-- step 6：part を一つずつ IPv4 number として読んだ数の列。 -/
inductive PartsNumbers : List (List Char) → List Nat → Prop
  | nil : PartsNumbers [] []
  | cons {p : List Char} {ps : List (List Char)} {n : Nat} {ns : List Nat} {v : Bool} :
      Ipv4Number p n v → PartsNumbers ps ns → PartsNumbers (p :: ps) (n :: ns)

/-- step 11-12：`counter` 番目の数に `256^(3 - counter)` を掛けて足す。 -/
def counterSum : Nat → List Nat → Nat
  | _, [] => 0
  | k, n :: ns => n * 256 ^ (3 - k) + counterSum (k + 1) ns

/--
§3.3 IPv4 parser。`Ipv4Parses input addr` は「`input` を読むと IPv4 address `addr`」。

* step 1-2：`.` で strict split し、最後の空の part を（2 個以上なら）落とす。
* step 4：part は 4 個まで。
* step 6：どの part も IPv4 number として読める。
* step 8：最後以外の数は 255 以下。
* step 9：最後の数は `256^(5 - size)` 未満。
* step 10-14：最後の数に、残りを `256^(3 - counter)` 倍して足したもの。
-/
def Ipv4Parses (input : List Char) (addr : Nat) : Prop :=
  ∃ raw nums last, SplitBy (· == '.') input raw ∧ PartsNumbers (trimLastPart raw) nums ∧
    nums.length ≤ 4 ∧ (∀ n ∈ nums.dropLast, n ≤ 255) ∧ nums.getLast? = some last ∧
    last < 256 ^ (5 - nums.length) ∧ addr = last + counterSum 0 nums.dropLast

/-- 実装の `strictSplit` は `splitBy` である。 -/
theorem strictSplit_go_eq (sep : Char) : ∀ (l acc : List Char),
    strictSplit.go sep l acc = (splitBy (· == sep) l).modifyHead (acc.reverse ++ ·)
  | [], acc => by simp [strictSplit.go, splitBy]
  | c :: l, acc => by
    simp only [strictSplit.go]
    by_cases hc : (c == sep) = true
    · rw [if_pos hc, strictSplit_go_eq sep l []]
      simp [splitBy, hc]
      cases splitBy (fun x => x == sep) l <;> rfl
    · rw [if_neg hc, strictSplit_go_eq sep l (c :: acc)]
      rw [splitBy_cons_nosep (by simpa using hc)]
      cases h : splitBy (· == sep) l with
      | nil => exact absurd h (splitBy_ne_nil _ l)
      | cons x r => simp

theorem strictSplit_eq (l : List Char) (sep : Char) : strictSplit l sep = splitBy (· == sep) l := by
  unfold strictSplit
  rw [strictSplit_go_eq]
  exact modifyHead_nil_append _

theorem ipv4Parts_eq (l : List Char) : ipv4Parts l = trimLastPart (splitBy (· == '.') l) := by
  unfold ipv4Parts trimLastPart
  rw [strictSplit_eq]
  dsimp only
  generalize splitBy (· == '.') l = parts
  cases h : parts.getLast? with
  | none => simp
  | some x => cases x <;> simp

/-- 実装の `mapM` は `PartsNumbers` を計算する。 -/
theorem mapM_numbers_iff : ∀ (ps : List (List Char)) (ns : List Nat),
    ps.mapM (fun p => (ipv4NumberParser p).map Prod.fst) = some ns ↔ PartsNumbers ps ns
  | [], ns => by
    cases ns <;> simp [PartsNumbers.nil]
    intro h; cases h
  | p :: ps, ns => by
    simp only [List.mapM_cons]
    constructor
    · intro h
      cases hp : ipv4NumberParser p with
      | none => simp [hp] at h
      | some nv =>
        obtain ⟨n, v⟩ := nv
        cases hps : ps.mapM (fun p => (ipv4NumberParser p).map Prod.fst) with
        | none => simp [hp, hps] at h
        | some ns' =>
          simp [hp, hps] at h
          subst h
          exact .cons ((ipv4NumberParser_iff p n v).mp hp) ((mapM_numbers_iff ps ns').mp hps)
    · intro h
      cases h with
      | @cons _ _ n ns' v hn hns =>
        rw [(ipv4NumberParser_iff p n v).mpr hn, (mapM_numbers_iff ps ns').mpr hns]
        rfl

private theorem fold256_acc : ∀ (ns : List Nat) (a : Nat),
    ns.foldl (fun acc n => acc * 256 + n) a = a * 256 ^ ns.length + ns.foldl (fun acc n => acc * 256 + n) 0
  | [], a => by simp
  | n :: ns, a => by
    simp only [List.foldl_cons]
    rw [fold256_acc ns (a * 256 + n), fold256_acc ns (0 * 256 + n)]
    simp only [List.length_cons, Nat.pow_succ, Nat.zero_mul, Nat.zero_add, Nat.add_mul, Nat.add_assoc]
    rw [Nat.mul_assoc a 256, Nat.mul_comm 256 (256 ^ ns.length), ← Nat.mul_assoc]

/-- counter の重みで足すのは、256 進で畳み込んで残りの桁だけずらすのと同じである。 -/
theorem counterSum_eq : ∀ (ns : List Nat) (k : Nat), k + ns.length ≤ 4 →
    counterSum k ns = ns.foldl (fun acc n => acc * 256 + n) 0 * 256 ^ (4 - k - ns.length)
  | [], k, _ => by simp [counterSum]
  | n :: ns, k, h => by
    simp only [List.length_cons] at h
    simp only [counterSum, List.foldl_cons, Nat.zero_mul, Nat.zero_add]
    rw [counterSum_eq ns (k + 1) (by omega), fold256_acc ns n, Nat.add_mul, Nat.mul_assoc,
      ← Nat.pow_add]
    simp only [List.length_cons]
    rw [show ns.length + (4 - k - (ns.length + 1)) = 3 - k by omega,
      show 4 - (k + 1) - ns.length = 4 - k - (ns.length + 1) by omega]

/-- **IPv4 parser は関係 `Ipv4Parses` を計算する。** 入力に制限は無い。 -/
theorem ipv4Parser_iff (input : List Char) (addr : Nat) :
    ipv4Parser input = some addr ↔ Ipv4Parses input addr := by
  unfold ipv4Parser
  rw [ipv4Parts_eq]
  constructor
  · intro h
    split at h
    · simp at h
    · next nums hm =>
      have hpn := (mapM_numbers_iff _ nums).mp hm
      split at h
      · simp at h
      · next hlen =>
        split at h
        · simp at h
        · next hdl =>
          split at h
          · simp at h
          · next last hl =>
            split at h
            · simp at h
            · next hb =>
              simp only [Option.some.injEq] at h
              simp only [Bool.or_eq_true, decide_eq_true_eq, List.isEmpty_iff, not_or,
                Nat.not_lt] at hlen
              simp only [List.any_eq_true, decide_eq_true_eq, not_exists, not_and, Nat.not_lt] at hdl
              have hpos : 0 < nums.length := List.length_pos_iff.mpr hlen.2
              refine ⟨_, nums, last, splitBy_spec _ input, hpn, hlen.1, hdl, hl, by omega, ?_⟩
              rw [← h, counterSum_eq _ 0 (by simp; omega)]
              simp only [List.length_dropLast]
              rw [show 4 - 0 - (nums.length - 1) = 5 - nums.length by omega]
              omega
  · rintro ⟨raw, nums, last, hsp, hpn, hlen, hdl, hl, hb, rfl⟩
    rw [← hsp.eq_splitBy, (mapM_numbers_iff _ nums).mpr hpn]
    have hne : nums ≠ [] := by intro he; rw [he] at hl; simp at hl
    have hpos : 0 < nums.length := List.length_pos_iff.mpr hne
    simp only
    rw [if_neg (by simp [hne]; omega), if_neg (by simp; exact hdl), hl]
    simp only
    rw [if_neg (by omega)]
    rw [counterSum_eq _ 0 (by simp; omega)]
    simp only [List.length_dropLast, Option.some.injEq]
    rw [show 4 - 0 - (nums.length - 1) = 5 - nums.length by omega]
    omega

/-! ## ends in a number checker -/

/-- ends in a number checker step 3：最後の part が空なら落とす（こちらは part の個数を見ない）。 -/
def trimEmptyLast (parts : List (List Char)) : List (List Char) :=
  if parts.getLast? = some [] then parts.dropLast else parts

/--
§3.3 ends in a number checker。

最後の part（空なら落とした後の最後）が、空でない ASCII digit の列か、IPv4 number として読めるもの。
-/
def EndsInNumber (input : List Char) : Prop :=
  ∃ raw last, SplitBy (· == '.') input raw ∧ (trimEmptyLast raw).getLast? = some last ∧
    ((last ≠ [] ∧ ∀ c ∈ last, IsDecDigit c) ∨ ∃ n v, Ipv4Number last n v)

theorem isAsciiDigit_iff (c : Char) : isAsciiDigit c = true ↔ IsDecDigit c := by
  simp [isAsciiDigit, IsDecDigit]

/-- 空でない入力なら、part を一つしか持たないのはそれが空でないとき。二つの落とし方は一致する。 -/
theorem trimLastPart_eq {input : List Char} (hne : input ≠ []) :
    trimLastPart (splitBy (· == '.') input) = trimEmptyLast (splitBy (· == '.') input) := by
  unfold trimLastPart trimEmptyLast
  by_cases hl : (splitBy (· == '.') input).getLast? = some []
  · have hlen : (splitBy (· == '.') input).length > 1 := by
      refine Classical.byContradiction fun hle => ?_
      have h1 : (splitBy (· == '.') input).length = 1 := by
        have := splitBy_ne_nil (· == '.') input
        have : 0 < (splitBy (· == '.') input).length := List.length_pos_iff.mpr this
        omega
      obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp h1
      rw [hx] at hl
      simp at hl
      subst hl
      have hs := splitBy_spec (· == '.') input
      rw [hx] at hs
      cases hs with
      | last _ => exact hne rfl
      | sep _ _ hr => exact absurd hr (by intro h; cases h)
    rw [if_pos ⟨hl, hlen⟩, if_pos hl]
  · rw [if_neg (fun h => hl h.1), if_neg hl]

/-- **ends in a number checker は関係 `EndsInNumber` を計算する**（空でない入力について。本文の assert）。 -/
theorem endsInANumber_iff {input : List Char} (hne : input ≠ []) :
    endsInANumber input = true ↔ EndsInNumber input := by
  unfold endsInANumber
  rw [ipv4Parts_eq, trimLastPart_eq hne]
  constructor
  · intro h
    split at h
    · simp at h
    · next last hl =>
      refine ⟨_, last, splitBy_spec _ input, hl, ?_⟩
      by_cases hd : (!last.isEmpty && last.all fun c => isAsciiDigit c) = true
      · simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true] at hd
        exact .inl ⟨hd.1, fun c hc => (isAsciiDigit_iff c).mp (hd.2 c hc)⟩
      · rw [if_neg hd] at h
        obtain ⟨⟨n, v⟩, hnv⟩ := Option.isSome_iff_exists.mp h
        exact .inr ⟨n, v, (ipv4NumberParser_iff last n v).mp hnv⟩
  · rintro ⟨raw, last, hsp, hl, hc⟩
    rw [hsp.eq_splitBy] at hl
    rw [hl]
    simp only
    rcases hc with ⟨hlne, hd⟩ | ⟨n, v, hnv⟩
    · rw [if_pos]
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true]
      exact ⟨hlne, fun c hc => (isAsciiDigit_iff c).mpr (hd c hc)⟩
    · split
      · rfl
      · rw [(ipv4NumberParser_iff last n v).mpr hnv]; rfl

/-! ## 証人

関係の側で書いた結果を、実装を `decide` で計算して確かめる。
-/

/-- `0x7f.1` は 127.0.0.1。16 進の part と、二つしか無い part の最後が残りの 3 byte を埋める。 -/
example : Ipv4Parses "0x7f.1".toList 2130706433 := (ipv4Parser_iff _ _).mp (by decide)

/-- `1.2.3` は 1.2.0.3。part が 3 個なら最後の part が 2 byte を受け持つ。 -/
example : Ipv4Parses "1.2.3".toList 16908291 := (ipv4Parser_iff _ _).mp (by decide)

/-- `08` は 8 進として読むので失敗する（本文の注記の「erroneous input "09"」と同じ）。 -/
example (a : Nat) : ¬ Ipv4Parses "08".toList a := fun h => by
  have h' := (ipv4Parser_iff _ _).mpr h
  rw [show ipv4Parser "08".toList = none by decide] at h'
  cases h'

/-- 最後以外の part が 255 を超えれば失敗する。 -/
example (a : Nat) : ¬ Ipv4Parses "1.256.3.4".toList a := fun h => by
  have h' := (ipv4Parser_iff _ _).mpr h
  rw [show ipv4Parser "1.256.3.4".toList = none by decide] at h'
  cases h'

end Url.Spec
