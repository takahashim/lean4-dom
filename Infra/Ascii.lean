/-!
# Infra Standard の code point

WHATWG Infra Standard の ASCII まわりの語彙。
DOM Standard（attribute 名の大文字小文字、名前の検査）と
URL Standard（scheme、percent-encoding、host の解析）が同じものを使う。

判定は Infra の書き方に合わせて **code point の値** で書く。
`Char` の順序で書くより仕様に近く、算術の補題も素直に出る。

`String` と `Char`（surrogate を除いた Unicode scalar value）の上で定義する。
byte 列が要るところは `Infra/Bytes.lean` にある。
-/

namespace Infra

/-- Infra の ASCII whitespace。TAB / LF / FF / CR / SPACE。 -/
def isAsciiWhitespace (c : Char) : Bool :=
  c.toNat == 0x09 || c.toNat == 0x0A || c.toNat == 0x0C || c.toNat == 0x0D || c.toNat == 0x20

/-- Infra の C0 control。U+0000 から U+001F。 -/
def isC0Control (c : Char) : Bool := c.toNat ≤ 0x1F

/-- Infra の C0 control or space。 -/
def isC0ControlOrSpace (c : Char) : Bool := c.toNat ≤ 0x20

/-- Infra の ASCII digit。U+0030 から U+0039。 -/
def isAsciiDigit (c : Char) : Bool := 0x30 ≤ c.toNat && c.toNat ≤ 0x39

/-- Infra の ASCII upper hex digit。 -/
def isAsciiUpperHexDigit (c : Char) : Bool :=
  isAsciiDigit c || (0x41 ≤ c.toNat && c.toNat ≤ 0x46)

/-- Infra の ASCII lower hex digit。 -/
def isAsciiLowerHexDigit (c : Char) : Bool :=
  isAsciiDigit c || (0x61 ≤ c.toNat && c.toNat ≤ 0x66)

/-- Infra の ASCII hex digit。 -/
def isAsciiHexDigit (c : Char) : Bool := isAsciiUpperHexDigit c || isAsciiLowerHexDigit c

/-- Infra の ASCII upper alpha。U+0041 から U+005A。 -/
def isAsciiUpperAlpha (c : Char) : Bool := 0x41 ≤ c.toNat && c.toNat ≤ 0x5A

/-- Infra の ASCII lower alpha。U+0061 から U+007A。 -/
def isAsciiLowerAlpha (c : Char) : Bool := 0x61 ≤ c.toNat && c.toNat ≤ 0x7A

/-- Infra の ASCII alpha。 -/
def isAsciiAlpha (c : Char) : Bool := isAsciiUpperAlpha c || isAsciiLowerAlpha c

/-- Infra の ASCII alphanumeric。 -/
def isAsciiAlphanumeric (c : Char) : Bool := isAsciiDigit c || isAsciiAlpha c

/-- Infra の ASCII code point。 -/
def isAscii (c : Char) : Bool := c.toNat ≤ 0x7F

/-- ASCII lowercase の 1 文字分。 -/
def asciiLowerChar (c : Char) : Char :=
  if isAsciiUpperAlpha c then Char.ofNat (c.toNat + 32) else c

/-- ASCII の大文字を小文字にする（Infra の "ASCII lowercase"）。 -/
def asciiLowercase (s : String) : String :=
  String.ofList (s.toList.map asciiLowerChar)

/-- ASCII の小文字を大文字にする（Infra の "ASCII uppercase"）。 -/
def asciiUppercase (s : String) : String :=
  String.ofList (s.toList.map fun c =>
    if isAsciiLowerAlpha c then Char.ofNat (c.toNat - 32) else c)

/-- hex digit の数値。hex digit でなければ `none`。 -/
def hexValue (c : Char) : Option Nat :=
  if 0x30 ≤ c.toNat && c.toNat ≤ 0x39 then some (c.toNat - 0x30)
  else if 0x41 ≤ c.toNat && c.toNat ≤ 0x46 then some (c.toNat - 0x41 + 10)
  else if 0x61 ≤ c.toNat && c.toNat ≤ 0x66 then some (c.toNat - 0x61 + 10)
  else none

/-- 数字の数値。ASCII digit でなければ `none`。 -/
def digitValue (c : Char) : Option Nat :=
  if 0x30 ≤ c.toNat && c.toNat ≤ 0x39 then some (c.toNat - 0x30) else none

/-- hex digit の値は 16 未満である。percent-decoding が byte に収まることの根拠。 -/
theorem hexValue_lt {c : Char} {v : Nat} (h : hexValue c = some v) : v < 16 := by
  unfold hexValue at h
  split at h
  · next hb =>
    have hv := Option.some.inj h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    omega
  · split at h
    · next _ hb =>
      have hv := Option.some.inj h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      omega
    · split at h
      · next _ _ hb =>
        have hv := Option.some.inj h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
        omega
      · simp at h

/-- 数字の値は 10 未満である。 -/
theorem digitValue_lt {c : Char} {v : Nat} (h : digitValue c = some v) : v < 10 := by
  unfold digitValue at h
  split at h
  · next hb =>
    have hv := Option.some.inj h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    omega
  · simp at h

/-- ASCII の範囲なら `Char.ofNat` は値をそのまま持つ。 -/
theorem toNat_ofNat_ascii {n : Nat} (h : n < 0x80) : (Char.ofNat n).toNat = n := by
  unfold Char.ofNat
  rw [dif_pos (by simp [Nat.isValidChar]; omega)]
  simp [Char.ofNatAux, Char.toNat]

/-- **ASCII lowercase は whitespace かどうかを変えない。** -/
theorem isAsciiWhitespace_asciiLowerChar (c : Char) :
    isAsciiWhitespace (asciiLowerChar c) = isAsciiWhitespace c := by
  unfold asciiLowerChar
  by_cases h : isAsciiUpperAlpha c = true
  · rw [if_pos h]
    unfold isAsciiUpperAlpha at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have hv : (Char.ofNat (c.toNat + 32)).toNat = c.toNat + 32 :=
      toNat_ofNat_ascii (by omega)
    have hL : isAsciiWhitespace (Char.ofNat (c.toNat + 32)) = false := by
      unfold isAsciiWhitespace
      rw [hv]
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
      refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> omega
    have hR : isAsciiWhitespace c = false := by
      unfold isAsciiWhitespace
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
      refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> omega
    rw [hL, hR]
  · rw [if_neg h]

/-- ASCII lowercase は文字を ASCII の中で動かすだけで、別の記号を作らない。 -/
theorem asciiLowerChar_ne {c d : Char} (hd : isAsciiLowerAlpha d = false) (h : ¬c = d) :
    ¬asciiLowerChar c = d := by
  unfold asciiLowerChar
  split
  · next hu =>
    simp only [isAsciiUpperAlpha, Bool.and_eq_true, decide_eq_true_eq] at hu
    simp only [isAsciiLowerAlpha, Bool.and_eq_false_iff, decide_eq_false_iff_not,
      Nat.not_le] at hd
    intro heq
    have ht : (Char.ofNat (c.toNat + 32)).toNat = d.toNat := by rw [heq]
    rw [toNat_ofNat_ascii (by omega)] at ht
    omega
  · exact h

/-! ## list 上の道具 -/

/-- 各文字を変えない写像なら、list は変わらない。 -/
theorem map_self_of_mem : ∀ {l : List Char} {f : Char → Char}, (∀ c ∈ l, f c = c) → l.map f = l
  | [], _, _ => rfl
  | c :: t, f, h => by
    simp only [List.map_cons, h c (by simp)]
    rw [map_self_of_mem (fun x hx => h x (by simp [hx]))]

/-! ## ASCII lowercase の性質 -/

/-- 小文字に直しても変わらない文字だけの列は、`asciiLowercase` で変わらない。 -/
theorem asciiLowercase_id {l : List Char} (h : ∀ c ∈ l, asciiLowerChar c = c) :
    asciiLowercase (String.ofList l) = String.ofList l := by
  unfold asciiLowercase
  rw [String.toList_ofList, map_self_of_mem h]

/-- 小文字に直す操作は二度やっても同じである。 -/
theorem asciiLowerChar_idem (c : Char) : asciiLowerChar (asciiLowerChar c) = asciiLowerChar c := by
  unfold asciiLowerChar
  split
  · next h =>
    simp only [isAsciiUpperAlpha, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [if_neg ?_]
    simp only [isAsciiUpperAlpha, Bool.and_eq_true, decide_eq_true_eq, not_and, Nat.not_le]
    rw [toNat_ofNat_ascii (by omega)]
    omega
  · rfl

/-- 小文字に直しても ASCII のままである。 -/
theorem asciiLowerChar_ascii {c : Char} (h : isAscii c = true) :
    isAscii (asciiLowerChar c) = true := by
  simp only [isAscii, decide_eq_true_eq] at h ⊢
  unfold asciiLowerChar
  split
  · next h2 =>
    simp only [isAsciiUpperAlpha, Bool.and_eq_true, decide_eq_true_eq] at h2
    rw [toNat_ofNat_ascii (by omega)]
    omega
  · exact h

/-- upper alpha でない文字は `asciiLowerChar` で変わらない。 -/
theorem asciiLowerChar_of_not_upper {c : Char} (h : isAsciiUpperAlpha c = false) :
    asciiLowerChar c = c := by
  unfold asciiLowerChar
  rw [if_neg (by rw [h]; simp)]

/-- ASCII でない文字は `asciiLowerChar` で変わらない。 -/
theorem asciiLowerChar_of_not_ascii {c : Char} (h : isAscii c = false) :
    asciiLowerChar c = c := by
  refine asciiLowerChar_of_not_upper ?_
  simp only [isAscii, decide_eq_false_iff_not, Nat.not_le] at h
  simp only [isAsciiUpperAlpha, Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_le]
  exact Or.inr (by omega)

/-! ## digit と hex digit の対応 -/

/-- ASCII digit なら `digitValue` は値を返す。 -/
theorem digitValue_isSome {c : Char} (h : isAsciiDigit c = true) :
    digitValue c = some (c.toNat - 0x30) := by
  unfold digitValue
  rw [if_pos (by simpa [isAsciiDigit] using h)]

/-- ASCII digit でなければ `digitValue` は `none` である。 -/
theorem digitValue_eq_none {c : Char} (h : isAsciiDigit c = false) : digitValue c = none := by
  unfold digitValue
  rw [if_neg (by simpa [isAsciiDigit] using h)]

/-- ASCII hex digit なら `hexValue` は値を返す。 -/
theorem hexValue_isSome {c : Char} (h : isAsciiHexDigit c = true) :
    ∃ v, hexValue c = some v := by
  unfold hexValue
  simp only [isAsciiHexDigit, isAsciiUpperHexDigit, isAsciiLowerHexDigit, isAsciiDigit,
    Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  split
  · exact ⟨_, rfl⟩
  · split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · next h1 h2 h3 =>
        exfalso
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, Nat.not_le] at h1 h2 h3
        omega

end Infra
