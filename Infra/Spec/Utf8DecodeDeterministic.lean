import Infra.Spec.Utf8Decode
import Infra.Spec.Utf8DecodeSound

/-!
# UTF-8 decode の関係仕様は決定的である

`Chunk` の各規則は入力の形で排他なので、`Decodes` は結果を一意に決める。
`Infra.Spec.utf8Decode_spec` と合わせると、`Decodes` が `utf8Decode` を特徴づける。
-/

namespace Infra.Spec

open Infra

/-- 同じ byte 列から出る `Chunk` の結果は一意である。 -/
theorem Chunk.deterministic {bs : Bytes} {c1 c2 : Char} {bs1 bs2 : Bytes}
    (h1 : Chunk bs c1 bs1) (h2 : Chunk bs c2 bs2) : c1 = c2 ∧ bs1 = bs2 := by
  -- `ContinuationValue` は開かない。omega は atom のまま扱え、開くと `simp at *` が止まらない。
  cases h1 <;> cases h2 <;>
    simp only [IsAscii, IsLead2, IsLead3, IsLead4, FirstCont3, FirstCont4,
      IsContinuation] at * <;>
    first
      | exact ⟨rfl, trivial⟩
      | exact ⟨Char.toNat_inj.mp (by omega), trivial⟩
      | exact ⟨trivial, trivial⟩
      | (exfalso; omega)
      | (simp_all; omega)
      | simp_all

/-- `Decodes` は結果を一意に決める。 -/
theorem Decodes.deterministic : ∀ {bs : Bytes} {cs1 cs2 : List Char},
    Decodes bs cs1 → Decodes bs cs2 → cs1 = cs2
  | _, _, _, .nil, .nil => rfl
  | _, _, _, .nil, .cons hc _ => nomatch hc
  | _, _, _, .cons hc _, .nil => nomatch hc
  | _, _, _, .cons hc ht, .cons hc2 ht2 => by
    obtain ⟨rfl, rfl⟩ := Chunk.deterministic hc hc2
    rw [Decodes.deterministic ht ht2]

/--
**仕様と実行関数は一致する。**

`Decodes bs cs` が成り立つのは `cs = utf8Decode bs` のときに限る。
`utf8Decode_spec`（実装は仕様を満たす）と `Decodes.deterministic`（仕様は一意）から従う。
-/
theorem Decodes.eq_utf8Decode_iff {bs : Bytes} {cs : List Char} :
    Decodes bs cs ↔ cs = utf8Decode bs := by
  constructor
  · intro h
    exact Decodes.deterministic h (utf8Decode_spec bs)
  · intro h
    rw [h]
    exact utf8Decode_spec bs

end Infra.Spec
