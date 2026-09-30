/-!
# list の汎用補題

ASCII や UTF-8 に依存しない、`List` 一般の補題。
`Infra/Ascii.lean` と `Url/Roundtrip.lean` が共有する。
-/

namespace Infra

/-- 各要素を変えない写像なら、list は変わらない。 -/
theorem map_self_of_mem : ∀ {α : Type _} {l : List α} {f : α → α},
    (∀ c ∈ l, f c = c) → l.map f = l
  | _, [], _, _ => rfl
  | _, c :: t, f, h => by
    simp only [List.map_cons, h c (by simp)]
    rw [map_self_of_mem (fun x hx => h x (by simp [hx]))]

end Infra
