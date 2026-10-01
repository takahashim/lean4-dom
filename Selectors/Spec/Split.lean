import Selectors.Parser

/-!
# selector parser の list 操作の関係仕様（部分）

`Selectors/Parser.lean` の `dropToComma`（forgiving な list の読み飛ばし）と
`splitAtOf`（`:nth-child(An+B of S)` の最初の top-level `of` で切る）を、
実行関数を呼ばずに list の分解として書く。

どちらも「最初の印まで」という条件が入りやすく、off-by-one の温床である。
-/

namespace Selectors.Spec

open Selectors

/-! ## `dropToComma` -/

/-- `l` を最初の `,` まで（その `,` も含めて）捨てた残り。`r` はその残り。 -/
def DropsToComma (l r : List Component) : Prop :=
  (∃ pre post : List Component,
    l = pre ++ Component.tok .comma :: post ∧ r = post ∧ ∀ c ∈ pre, isComma c = false) ∨
  ((∀ c ∈ l, isComma c = false) ∧ r = [])

theorem dropToComma_mem_comma {c : Component} (h : isComma c = true) : c = Component.tok .comma := by
  cases c with
  | tok t => cases t <;> simp [isComma] at h ⊢
  | func _ _ => simp [isComma] at h
  | block _ _ => simp [isComma] at h

theorem dropsToComma_of_dropToComma : ∀ (l r : List Component),
    dropToComma l = r → DropsToComma l r
  | [], r, h => by
    refine Or.inr ⟨?_, ?_⟩
    · intro c hc; simp at hc
    · rw [← h]; rfl
  | c :: rest, r, h => by
    rw [dropToComma] at h
    by_cases hc : isComma c = true
    · rw [if_pos hc] at h
      refine Or.inl ⟨[], r, ?_, rfl, by simp⟩
      rw [dropToComma_mem_comma hc, h, List.nil_append]
    · rw [if_neg hc] at h
      rcases dropsToComma_of_dropToComma rest r h with
        ⟨pre, post, hl, hr, hno⟩ | ⟨hno, hr⟩
      · refine Or.inl ⟨c :: pre, post, ?_, hr, ?_⟩
        · rw [hl]; rfl
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact eq_false_of_ne_true hc
          · exact hno x hx
      · refine Or.inr ⟨?_, hr⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact eq_false_of_ne_true hc
        · exact hno x hx

theorem dropToComma_of_dropsToComma : ∀ (pre post : List Component),
    (∀ c ∈ pre, isComma c = false) → dropToComma (pre ++ Component.tok .comma :: post) = post
  | [], post, _ => by simp [dropToComma, isComma]
  | c :: pre, post, hno => by
    have hc : isComma c = false := hno c (by simp)
    rw [List.cons_append, dropToComma, if_neg (by rw [hc]; simp)]
    exact dropToComma_of_dropsToComma pre post (fun x hx => hno x (by simp [hx]))

theorem dropToComma_of_no_comma : ∀ (l : List Component),
    (∀ c ∈ l, isComma c = false) → dropToComma l = []
  | [], _ => rfl
  | c :: rest, hno => by
    have hc : isComma c = false := hno c (by simp)
    rw [dropToComma, if_neg (by rw [hc]; simp)]
    exact dropToComma_of_no_comma rest (fun x hx => hno x (by simp [hx]))

theorem dropsToComma_of_dropToComma_mpr {l r : List Component} (h : DropsToComma l r) :
    dropToComma l = r := by
  rcases h with ⟨pre, post, hl, hr, hno⟩ | ⟨hno, hr⟩
  · rw [hl, hr]; exact dropToComma_of_dropsToComma pre post hno
  · rw [hr]; exact dropToComma_of_no_comma l hno

/-- **`dropToComma` は「最初の `,` の後ろ」をちょうど返す。** -/
theorem dropToComma_spec (l r : List Component) : dropToComma l = r ↔ DropsToComma l r :=
  ⟨dropsToComma_of_dropToComma l r, dropsToComma_of_dropToComma_mpr⟩

/-! ## `splitAtOf` -/

theorem splitAtOf_some_of : ∀ (l a b : List Component), splitAtOf l = some (a, b) →
    ∃ m : Component, l = a ++ m :: b ∧ isOfIdent m = true ∧
      ∀ c ∈ a, isOfIdent c = false
  | [], _, _, h => by simp [splitAtOf] at h
  | c :: rest, a, b, h => by
    rw [splitAtOf] at h
    by_cases hc : isOfIdent c = true
    · rw [if_pos hc] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨c, by simp, hc, by simp⟩
    · rw [if_neg hc] at h
      split at h
      · next a0 b0 hs =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨m, hm, hmof, hno⟩ := splitAtOf_some_of rest a0 b0 hs
        refine ⟨m, ?_, hmof, ?_⟩
        · rw [hm]; rfl
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact eq_false_of_ne_true hc
          · exact hno x hx
      · simp at h

theorem splitAtOf_of_splitAtOf : ∀ (a b : List Component) (m : Component),
    isOfIdent m = true → (∀ c ∈ a, isOfIdent c = false) → splitAtOf (a ++ m :: b) = some (a, b)
  | [], b, m, hm, _ => by
    show splitAtOf (m :: b) = some ([], b)
    rw [splitAtOf, if_pos hm]
  | c :: a, b, m, hm, hno => by
    have hc : isOfIdent c = false := hno c (by simp)
    rw [List.cons_append, splitAtOf, if_neg (by rw [hc]; simp)]
    rw [splitAtOf_of_splitAtOf a b m hm (fun x hx => hno x (by simp [hx]))]

/-- **`splitAtOf` は最初の top-level の `of` で切る。** -/
theorem splitAtOf_spec (l a b : List Component) :
    splitAtOf l = some (a, b) ↔
      ∃ m : Component, l = a ++ m :: b ∧ isOfIdent m = true ∧
        ∀ c ∈ a, isOfIdent c = false :=
  ⟨splitAtOf_some_of l a b, by
    rintro ⟨m, hl, hm, hno⟩
    rw [hl]
    exact splitAtOf_of_splitAtOf a b m hm hno⟩

end Selectors.Spec
