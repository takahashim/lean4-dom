/-!
# UTF-16 の code unit

WebIDL の `DOMString` は 16-bit code unit の列で、仕様が「文字列を比較する」と言うとき
その順序は **code unit の辞書式**である（URL Standard §6.2 の `sort` がそれを名指ししている）。

code point 順と一致しない。BMP の外の code point は surrogate pair
（U+D800..U+DBFF, U+DC00..U+DFFF）になるので、code unit では U+E000 以上の BMP 文字より
**小さく**なる。たとえば U+1F308（🌈）は D83C DF08 で、U+FB03（ﬃ）より code unit では前に来るが、
code point では後ろである。
-/

namespace Infra

/-- code point が占める UTF-16 code unit。BMP なら 1 つ、それ以外は surrogate pair。 -/
def codeUnits (c : Char) : List UInt16 :=
  if c.toNat < 0x10000 then [UInt16.ofNat c.toNat]
  else
    let m := c.toNat - 0x10000
    [UInt16.ofNat (0xD800 + m / 0x400), UInt16.ofNat (0xDC00 + m % 0x400)]

/-- 文字列の UTF-16 code unit 列。 -/
def utf16Units (s : String) : List UInt16 := s.toList.flatMap codeUnits

/-- code unit 列の辞書式比較。 -/
def lexLt : List UInt16 → List UInt16 → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a == b then lexLt as bs else a < b

/-- WebIDL の `DOMString` としての大小（code unit 順）。 -/
def strLt (a b : String) : Bool := lexLt (utf16Units a) (utf16Units b)

/-! ## 性質 -/

/-- 同じ列どうしは小さくない。 -/
@[simp] theorem lexLt_self : ∀ l : List UInt16, lexLt l l = false
  | [] => rfl
  | a :: rest => by simp [lexLt, lexLt_self rest]

/-- 同じ文字列どうしは小さくない。 -/
@[simp] theorem strLt_self (a : String) : strLt a a = false := by
  simp [strLt]

/-- 小さいなら等しくない。`sort` の安定性の証明で使う。 -/
theorem ne_of_strLt {a b : String} (h : strLt a b = true) : a ≠ b := by
  intro he
  rw [he, strLt_self] at h
  exact absurd h (by simp)

/-! ## code unit 順は全順序である -/

theorem lexLt_asymm : ∀ {a b : List UInt16}, lexLt a b = true → lexLt b a = false
  | [], [], h => by simp [lexLt] at h
  | [], _ :: _, _ => rfl
  | _ :: _, [], h => by simp [lexLt] at h
  | x :: xs, y :: ys, h => by
    unfold lexLt at h ⊢
    by_cases hxy : x = y
    · subst hxy
      simp only [beq_self_eq_true, if_true] at h ⊢
      exact lexLt_asymm h
    · rw [if_neg (by simpa using hxy)] at h
      rw [if_neg (by simpa using Ne.symm hxy)]
      simp only [decide_eq_true_eq, UInt16.lt_iff_toNat_lt] at h
      simp only [decide_eq_false_iff_not, UInt16.lt_iff_toNat_lt]
      omega

theorem lexLt_trans : ∀ {a b c : List UInt16}, lexLt a b = true → lexLt b c = true → lexLt a c = true
  | [], [], _, h, _ => by simp [lexLt] at h
  | [], _ :: _, [], _, h => by simp [lexLt] at h
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp [lexLt] at h
  | _ :: _, _ :: _, [], _, h => by simp [lexLt] at h
  | x :: xs, y :: ys, z :: zs, h1, h2 => by
    unfold lexLt at h1 h2 ⊢
    by_cases hxy : x = y <;> by_cases hyz : y = z
    · subst hxy hyz
      simp only [beq_self_eq_true, if_true] at h1 h2 ⊢
      exact lexLt_trans h1 h2
    · subst hxy
      simp only [beq_self_eq_true, if_true] at h1
      rw [if_neg (by simpa using hyz)] at h2 ⊢
      exact h2
    · subst hyz
      simp only [beq_self_eq_true, if_true] at h2
      rw [if_neg (by simpa using hxy)] at h1 ⊢
      exact h1
    · rw [if_neg (by simpa using hxy)] at h1
      rw [if_neg (by simpa using hyz)] at h2
      simp only [decide_eq_true_eq, UInt16.lt_iff_toNat_lt] at h1 h2
      have hxz : ¬x = z := by
        intro e; subst e; omega
      rw [if_neg (by simpa using hxz)]
      simp only [decide_eq_true_eq, UInt16.lt_iff_toNat_lt]
      omega

theorem lexLt_total : ∀ {a b : List UInt16}, a ≠ b → lexLt a b = true ∨ lexLt b a = true
  | [], [], h => absurd rfl h
  | [], _ :: _, _ => Or.inl rfl
  | _ :: _, [], _ => Or.inr rfl
  | x :: xs, y :: ys, h => by
    unfold lexLt
    by_cases hxy : x = y
    · subst hxy
      simp only [beq_self_eq_true, if_true]
      exact lexLt_total (fun e => h (by rw [e]))
    · rw [if_neg (by simpa using hxy), if_neg (by simpa using Ne.symm hxy)]
      simp only [decide_eq_true_eq, UInt16.lt_iff_toNat_lt]
      have : x.toNat ≠ y.toNat := fun e => hxy (UInt16.toNat_inj.mp e)
      omega

/-! ## UTF-16 への変換は単射である -/

theorem char_valid (c : Char) : c.toNat < 0xD800 ∨ (0xDFFF < c.toNat ∧ c.toNat < 0x110000) := by
  have h : c.val.toNat.isValidChar := c.valid
  unfold Nat.isValidChar at h
  exact h

/-- **一つの code point の code unit は、後ろに何が続いても読み分けられる。** -/
theorem codeUnits_append_inj {c d : Char} {s t : List UInt16}
    (h : codeUnits c ++ s = codeUnits d ++ t) : c = d ∧ s = t := by
  have hc := char_valid c
  have hd := char_valid d
  have hext : c.toNat = d.toNat → c = d := fun e => Char.ext (UInt32.toNat_inj.mp e)
  unfold codeUnits at h
  by_cases hcb : c.toNat < 0x10000 <;> by_cases hdb : d.toNat < 0x10000
  · simp only [hcb, hdb, if_true, List.singleton_append, List.cons.injEq] at h
    have := congrArg UInt16.toNat h.1
    simp only [UInt16.toNat_ofNat', Nat.reducePow] at this
    exact ⟨hext (by omega), h.2⟩
  · simp only [hcb, hdb, if_true, if_false, List.cons_append,
      List.cons.injEq] at h
    have := congrArg UInt16.toNat h.1
    simp only [UInt16.toNat_ofNat', Nat.reducePow] at this
    omega
  · simp only [hcb, hdb, if_true, if_false, List.cons_append,
      List.cons.injEq] at h
    have := congrArg UInt16.toNat h.1
    simp only [UInt16.toNat_ofNat', Nat.reducePow] at this
    omega
  · simp only [hcb, hdb, if_false, List.cons_append, List.cons.injEq] at h
    have h1 := congrArg UInt16.toNat h.1
    have h2 := congrArg UInt16.toNat h.2.1
    simp only [UInt16.toNat_ofNat', Nat.reducePow] at h1 h2
    refine ⟨hext ?_, by simpa using h.2.2⟩
    omega

theorem flatMap_codeUnits_inj : ∀ {a b : List Char},
    a.flatMap codeUnits = b.flatMap codeUnits → a = b
  | [], [], _ => rfl
  | [], d :: _, h => by
    unfold codeUnits at h
    simp only [List.flatMap_nil, List.flatMap_cons] at h
    split at h <;> simp at h
  | c :: _, [], h => by
    unfold codeUnits at h
    simp only [List.flatMap_nil, List.flatMap_cons] at h
    split at h <;> simp at h
  | c :: a, d :: b, h => by
    simp only [List.flatMap_cons] at h
    obtain ⟨hcd, hab⟩ := codeUnits_append_inj h
    rw [hcd, flatMap_codeUnits_inj hab]

/-- **文字列は UTF-16 の code unit 列で決まる。** -/
theorem utf16Units_inj {a b : String} (h : utf16Units a = utf16Units b) : a = b :=
  String.toList_inj.mp (flatMap_codeUnits_inj h)

/-! ## 文字列の code unit 順 -/

theorem strLt_asymm {a b : String} (h : strLt a b = true) : strLt b a = false := lexLt_asymm h

theorem strLt_trans {a b c : String} (h1 : strLt a b = true) (h2 : strLt b c = true) :
    strLt a c = true := lexLt_trans h1 h2

/-- **違う文字列は code unit 順でどちらかが小さい。** -/
theorem strLt_total {a b : String} (h : a ≠ b) : strLt a b = true ∨ strLt b a = true :=
  lexLt_total (fun e => h (utf16Units_inj e))

/-- 「小さくない」は推移的である（`a ≤ b`, `b ≤ c` なら `a ≤ c`）。 -/
theorem strLe_trans {a b c : String} (h1 : strLt b a = false) (h2 : strLt c b = false) :
    strLt c a = false := by
  cases h : strLt c a with
  | false => rfl
  | true =>
    exfalso
    by_cases hab : a = b
    · subst hab; rw [h] at h2; cases h2
    rcases strLt_total hab with hab' | hba
    · by_cases hbc : b = c
      · subst hbc; rw [strLt_asymm hab'] at h; cases h
      rcases strLt_total hbc with hbc' | hcb
      · have := strLt_trans (strLt_trans hab' hbc') h
        simp at this
      · rw [hcb] at h2; cases h2
    · rw [hba] at h1; cases h1

end Infra
