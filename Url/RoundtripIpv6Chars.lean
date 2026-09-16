import Url.RoundtripAuthority

/-!
# IPv6 serializer が出す文字
-/

namespace Url

open Infra

/-! ## IPv6 host

`[` と `]` で囲まれた host。中では `:` が port の区切りにならないので、
host state は bracket を数えながら読む。
-/

/-- 小文字 16 進の数字か、IPv6 の区切りの `:` である。 -/
def isHexOrColon (c : Char) : Bool :=
  (0x30 ≤ c.toNat && c.toNat ≤ 0x39) || (0x61 ≤ c.toNat && c.toNat ≤ 0x66) || c == ':'

theorem toHexString_go_chars : ∀ (fuel n : Nat) (acc : List Char), n ≤ fuel →
    (∀ c ∈ acc, isHexOrColon c = true) →
    ∀ c ∈ toHexString.go n acc, isHexOrColon c = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro n acc hle hacc
    have hn : n = 0 := Nat.le_zero.mp hle
    subst hn
    simpa [toHexString.go] using hacc
  | succ f ih =>
    intro n acc hle hacc
    cases n with
    | zero => simpa [toHexString.go] using hacc
    | succ m =>
      rw [toHexString.go]
      refine ih ((m + 1) / 16) _ (by omega) ?_
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · have hd : (m + 1) % 16 < 16 := Nat.mod_lt _ (by omega)
        simp only [isHexOrColon, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        rw [toNat_ofNat_ascii (by split <;> omega)]
        split <;> omega
      · exact hacc c hc

theorem toHexString_chars (n : Nat) :
    ∀ c ∈ (toHexString n).toList, isHexOrColon c = true := by
  unfold toHexString
  split
  · intro c hc; simp at hc; subst hc; decide
  · rw [String.toList_ofList]
    exact toHexString_go_chars n n [] (by omega) (by simp)


theorem ipv6Serializer_go_chars (cmp : Option Nat) : ∀ (l : List (Nat × Nat)) (ig : Bool),
    ∀ c ∈ (ipv6Serializer.go cmp l ig).toList, isHexOrColon c = true := by
  intro l
  induction l with
  | nil => intro ig c hc; simp [ipv6Serializer.go] at hc
  | cons p rest ih =>
    intro ig c hc
    obtain ⟨pv, i⟩ := p
    rw [ipv6Serializer.go] at hc
    split at hc
    · exact ih true c hc
    · split at hc
      · rw [String.toList_append] at hc
        rcases List.mem_append.mp hc with hc | hc
        · split at hc <;> (simp at hc; subst hc; decide)
        · exact ih true c hc
      · rw [String.toList_append, String.toList_append] at hc
        rcases List.mem_append.mp hc with hc | hc
        · rcases List.mem_append.mp hc with hc | hc
          · exact toHexString_chars pv c hc
          · split at hc
            · simp at hc
            · simp at hc; subst hc; decide
        · exact ih false c hc

/-- IPv6 を serialize した文字は 16 進の数字か `:` である。 -/
theorem ipv6Serializer_chars (a : Ipv6) :
    ∀ c ∈ (ipv6Serializer a).toList, isHexOrColon c = true :=
  ipv6Serializer_go_chars _ _ _



end Url
