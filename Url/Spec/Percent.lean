import Url.Percent

/-!
# percent-decode の関係仕様（§1.3）

`percentDecodeBytes`（`Url/Percent.lean`）は byte 列を先頭から読み、`%` に hex digit が二つ続けば
一 byte にまとめる。ここでは同じものを、§1.3 の本文の言い回しのまま関係として書く。

> For each byte `byte` in `input`:
> 1. If `byte` is not 0x25 (%), then append `byte` to `output`.
> 2. Otherwise, if `byte` is 0x25 (%) and the next two bytes after `byte` in `input` are not in
>    the ranges 0x30 (0) to 0x39 (9), 0x41 (A) to 0x46 (F), and 0x61 (a) to 0x66 (f), all inclusive,
>    append `byte` to `output`.
> 3. Otherwise: let `bytePoint` be the two bytes after `byte` ... interpreted as a hexadecimal
>    number. Append a byte whose value is `bytePoint` to `output`. Skip the next two bytes in `input`.

hex digit の範囲と値は本文の三つの範囲で直に書き、`Infra.hexValue` は呼ばない。
2 の「the next two bytes are not in the ranges」は、二つとも範囲にあるのでなければ、と読む
（`%4` で入力が終わる場合と `%4g` の両方が `%` をそのまま残す）。

`percentDecodeBytes_iff` が、関係を満たす出力は parser の出力にちょうど一致すると言う。
-/

namespace Url.Spec

open Infra

/-- §1.3 の三つの範囲。0x30-0x39、0x41-0x46、0x61-0x66。 -/
def IsHexByte (b : UInt8) : Prop :=
  (0x30 ≤ b.toNat ∧ b.toNat ≤ 0x39) ∨ (0x41 ≤ b.toNat ∧ b.toNat ≤ 0x46) ∨
    (0x61 ≤ b.toNat ∧ b.toNat ≤ 0x66)

instance (b : UInt8) : Decidable (IsHexByte b) := by unfold IsHexByte; infer_instance

/-- hex digit として読んだ値（isomorphic decode して 16 進の一桁と読む）。 -/
def hexByteValue (b : UInt8) : Nat :=
  if b.toNat ≤ 0x39 then b.toNat - 0x30
  else if b.toNat ≤ 0x46 then b.toNat - 0x41 + 10
  else b.toNat - 0x61 + 10

/-- 「`input` の次の二つの byte が両方 hex digit である」。 -/
def NextTwoHex (rest : Bytes) : Prop :=
  ∃ h1 h2 r, rest = h1 :: h2 :: r ∧ IsHexByte h1 ∧ IsHexByte h2

/-- §1.3 percent-decode。step 2 の三つの分岐をそのまま構成子にする。 -/
inductive PctDecodes : Bytes → Bytes → Prop
  /-- step 1：空の入力は空の出力。 -/
  | nil : PctDecodes [] []
  /-- step 2.1：`%` でない byte はそのまま。 -/
  | plain {b : UInt8} {rest out : Bytes} : b.toNat ≠ 0x25 → PctDecodes rest out →
      PctDecodes (b :: rest) (b :: out)
  /-- step 2.2：`%` の後に hex digit が二つ続かなければ、`%` をそのまま。 -/
  | lonePercent {b : UInt8} {rest out : Bytes} : b.toNat = 0x25 → ¬ NextTwoHex rest →
      PctDecodes rest out → PctDecodes (b :: rest) (b :: out)
  /-- step 2.3：`%` と hex digit 二つを、その値の一 byte にする。 -/
  | encoded {b h1 h2 : UInt8} {rest out : Bytes} : b.toNat = 0x25 → IsHexByte h1 → IsHexByte h2 →
      PctDecodes rest out →
      PctDecodes (b :: h1 :: h2 :: rest)
        (UInt8.ofNat (hexByteValue h1 * 16 + hexByteValue h2) :: out)

theorem toNat_ofNat_byte (b : UInt8) : (Char.ofNat b.toNat).toNat = b.toNat := by
  have hlt : b.toNat < 256 := b.toNat_lt
  unfold Char.ofNat
  rw [dif_pos (by simp [Nat.isValidChar]; omega)]
  simp [Char.ofNatAux, Char.toNat]

/-- parser が使う `hexValue` は、byte を文字にして読むと本文の範囲と値に一致する。 -/
theorem hexValue_byte (b : UInt8) :
    hexValue (Char.ofNat b.toNat) = if IsHexByte b then some (hexByteValue b) else none := by
  unfold hexValue hexByteValue
  rw [toNat_ofNat_byte]
  by_cases hh : IsHexByte b
  · rw [if_pos hh]
    unfold IsHexByte at hh
    repeat' split
    all_goals first | rfl | (simp_all; try omega) | omega
  · rw [if_neg hh]
    unfold IsHexByte at hh
    repeat' split
    all_goals first | rfl | (exfalso; simp only [Bool.and_eq_true, decide_eq_true_eq] at *; omega)

/-- 次が二 byte 未満なら、hex digit は二つ続かない。 -/
theorem not_nextTwoHex_short {rest : Bytes} (h : rest.length < 2) : ¬ NextTwoHex rest := by
  rintro ⟨h1, h2, r, rfl, -, -⟩
  simp at h
  omega

/-- **`percentDecodeBytes` の出力は関係を満たす。** -/
theorem percentDecodeBytes_spec : ∀ l : Bytes, PctDecodes l (percentDecodeBytes l)
  | [] => .nil
  | [b] => by
    simp only [percentDecodeBytes]
    by_cases hb : b.toNat = 0x25
    · exact .lonePercent hb (not_nextTwoHex_short (by simp)) .nil
    · exact .plain hb .nil
  | [b, b1] => by
    simp only [percentDecodeBytes]
    by_cases hb : b.toNat = 0x25
    · exact .lonePercent hb (not_nextTwoHex_short (by simp)) (percentDecodeBytes_spec [b1])
    · exact .plain hb (percentDecodeBytes_spec [b1])
  | b :: b1 :: b2 :: rest => by
    have ih := percentDecodeBytes_spec (b1 :: b2 :: rest)
    have ih3 := percentDecodeBytes_spec rest
    simp only [percentDecodeBytes]
    by_cases hb : b.toNat = 0x25
    · rw [if_pos (by simp [hb]), hexValue_byte, hexValue_byte]
      by_cases hx : IsHexByte b1 ∧ IsHexByte b2
      · rw [if_pos hx.1, if_pos hx.2]
        exact .encoded hb hx.1 hx.2 ih3
      · have hn : ¬ NextTwoHex (b1 :: b2 :: rest) := by
          rintro ⟨x, y, r, he, hx1, hy⟩
          simp only [List.cons.injEq] at he
          obtain ⟨rfl, rfl, rfl⟩ := he
          exact hx ⟨hx1, hy⟩
        by_cases h1 : IsHexByte b1
        · have h2 : ¬ IsHexByte b2 := fun h2 => hx ⟨h1, h2⟩
          simp only [h1, h2, ↓reduceIte]
          exact .lonePercent hb hn ih
        · simp only [h1, ↓reduceIte]
          exact .lonePercent hb hn ih
    · rw [if_neg (by simp [hb])]
      exact .plain hb ih

/-- **関係は決定的である。** 本文の三つの分岐は、どの入力についても一つしか当たらない。 -/
theorem PctDecodes.deterministic {l o1 o2 : Bytes} (h1 : PctDecodes l o1) (h2 : PctDecodes l o2) :
    o1 = o2 := by
  induction h1 generalizing o2 with
  | nil => cases h2; rfl
  | plain hb _ ih =>
    cases h2 with
    | plain _ h => rw [ih h]
    | lonePercent hb' _ _ => exact absurd hb' hb
    | encoded hb' _ _ _ => exact absurd hb' hb
  | lonePercent hb hn _ ih =>
    cases h2 with
    | plain hb' _ => exact absurd hb hb'
    | lonePercent _ _ h => rw [ih h]
    | encoded _ hx1 hx2 _ => exact absurd ⟨_, _, _, rfl, hx1, hx2⟩ hn
  | encoded hb hx1 hx2 _ ih =>
    cases h2 with
    | plain hb' _ => exact absurd hb hb'
    | lonePercent _ hn _ => exact absurd ⟨_, _, _, rfl, hx1, hx2⟩ hn
    | encoded _ _ _ h => rw [ih h]

/-- **`PctDecodes input out ↔ percentDecodeBytes input = out`。** 入力に制限は無い。 -/
theorem percentDecodeBytes_iff {input out : Bytes} :
    PctDecodes input out ↔ percentDecodeBytes input = out :=
  ⟨fun h => (h.deterministic (percentDecodeBytes_spec input)).symm,
    fun h => h ▸ percentDecodeBytes_spec input⟩

end Url.Spec
