import Selectors.Spec.Token
import Selectors.Spec.TokenSound

/-!
# tokenizer の関係仕様は決定的である

`Selectors/Spec/Token.lean` の各関係は入力の形で規則が排他なので、結果を一意に決める。
`Selectors/Spec/TokenSound.lean` と合わせると、関係が実行関数を特徴づける。
-/

namespace Selectors.Spec

open Selectors

/-- `Preprocessed` は結果を一意に決める。 -/
theorem Preprocessed.deterministic : ∀ {l o1 o2 : List Char},
    Preprocessed l o1 → Preprocessed l o2 → o1 = o2
  | _, _, _, .nil, .nil => rfl
  | _, _, _, .crlf h1, .crlf h2 => by rw [Preprocessed.deterministic h1 h2]
  | _, _, _, .crlf _, .cr hn _ => absurd rfl (hn _)
  | _, _, _, .cr hn _, .crlf _ => absurd rfl (hn _)
  | _, _, _, .cr _ h1, .cr _ h2 => by rw [Preprocessed.deterministic h1 h2]
  | _, _, _, .ff h1, .ff h2 => by rw [Preprocessed.deterministic h1 h2]
  | _, _, _, .null h1, .null h2 => by rw [Preprocessed.deterministic h1 h2]
  | _, _, _, .other _ h1, .other _ h2 => by rw [Preprocessed.deterministic h1 h2]
  | _, _, _, .crlf _, .other hc _ => absurd rfl hc.1
  | _, _, _, .other hc _, .crlf _ => absurd rfl hc.1
  | _, _, _, .cr _ _, .other hc _ => absurd rfl hc.1
  | _, _, _, .other hc _, .cr _ _ => absurd rfl hc.1
  | _, _, _, .ff _, .other hc _ => absurd rfl hc.2.1
  | _, _, _, .other hc _, .ff _ => absurd rfl hc.2.1
  | _, _, _, .null _, .other hc _ => absurd rfl hc.2.2
  | _, _, _, .other hc _, .null _ => absurd rfl hc.2.2

/-- **前処理の関係と実行関数は一致する。** -/
theorem Preprocessed.eq_filterCodePoints_iff {l out : List Char} :
    Preprocessed l out ↔ out = filterCodePoints l :=
  ⟨fun h => Preprocessed.deterministic h (filterCodePoints_spec l),
   fun h => h ▸ filterCodePoints_spec l⟩

end Selectors.Spec
