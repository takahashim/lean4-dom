/-!
# `List` の補助補題

Lean core に無い、または名前が version 間で揺れやすい補題をここに閉じ込める。
core 側に同名の補題が入った場合はこの module を削るだけで済むよう、
`Dom.List` namespace に置く。
-/

namespace Dom.ListUtil

open List

/--
重複の無い list が別の list に含まれるなら、長さは後者以下である（鳩の巣原理）。

`Dom/Properties/Tree.lean` の fuel 充足性の証明で使う。
祖先の連鎖は（acyclic なので）重複を持たず、その全要素が store の key に含まれるため、
連鎖の長さは store の要素数以下になる、という形で用いる。
-/
theorem length_le_of_nodup_subset {α : Type _} [DecidableEq α] :
    ∀ {l₁ l₂ : List α}, l₁.Nodup → l₁ ⊆ l₂ → l₁.length ≤ l₂.length
  | [], _, _, _ => Nat.zero_le _
  | a :: t, l₂, hnd, hsub => by
    have hmem : a ∈ l₂ := hsub (List.mem_cons_self ..)
    have hnd' : t.Nodup := (List.nodup_cons.mp hnd).2
    have hnotin : a ∉ t := (List.nodup_cons.mp hnd).1
    have hsub' : t ⊆ l₂.erase a := by
      intro x hx
      have hxa : x ≠ a := fun h => hnotin (h ▸ hx)
      exact (List.mem_erase_of_ne hxa).mpr (hsub (List.mem_cons_of_mem _ hx))
    have ih := length_le_of_nodup_subset hnd' hsub'
    have hlen : (l₂.erase a).length = l₂.length - 1 := List.length_erase_of_mem hmem
    have hpos : 0 < l₂.length := by
      cases l₂ with
      | nil => simp at hmem
      | cons _ _ => simp
    simp only [List.length_cons]
    omega

/--
`l` における `a` の位置。含まれない場合は `l.length` を返す。

core の `List.idxOf` は version 間で名前が揺れているため、自前で定義して補題も自前で持つ。
-/
def idx {α : Type _} [DecidableEq α] : List α → α → Nat
  | [], _ => 0
  | x :: rest, a => if x = a then 0 else idx rest a + 1

@[simp] theorem idx_nil {α : Type _} [DecidableEq α] (a : α) : idx ([] : List α) a = 0 := rfl

@[simp] theorem idx_cons_self {α : Type _} [DecidableEq α] (a : α) (l : List α) :
    idx (a :: l) a = 0 := by simp [idx]

theorem idx_cons_ne {α : Type _} [DecidableEq α] {x a : α} (h : x ≠ a) (l : List α) :
    idx (x :: l) a = idx l a + 1 := by simp [idx, h]

/--
互いに素な部分列の連結は重複を持たない。

`preorder` の重複の無さを、部分木ごとの列挙の重複の無さから組み立てるときに使う。
-/
theorem nodup_flatMap {α β : Type _} [DecidableEq β] {g : α → List β} :
    ∀ {l : List α}, l.Nodup → (∀ a ∈ l, (g a).Nodup) →
      (∀ a ∈ l, ∀ b ∈ l, a ≠ b → ∀ x, x ∈ g a → x ∉ g b) →
      (l.flatMap g).Nodup
  | [], _, _, _ => by simp
  | a :: l, hnd, hg, hdisj => by
    have hnd' : l.Nodup := (List.nodup_cons.mp hnd).2
    have hnotin : a ∉ l := (List.nodup_cons.mp hnd).1
    have ih : (l.flatMap g).Nodup :=
      nodup_flatMap hnd'
        (fun b hb => hg b (List.mem_cons_of_mem _ hb))
        (fun b hb c hc hbc => hdisj b (List.mem_cons_of_mem _ hb) c (List.mem_cons_of_mem _ hc) hbc)
    rw [List.flatMap_cons]
    refine List.nodup_append.mpr ⟨hg a (List.mem_cons_self ..), ih, ?_⟩
    intro x hx y hy hxy
    subst hxy
    obtain ⟨c, hc, hxc⟩ := List.mem_flatMap.mp hy
    have hac : a ≠ c := fun h => hnotin (h ▸ hc)
    exact hdisj a (List.mem_cons_self ..) c (List.mem_cons_of_mem _ hc) hac x hx hxc

/--
重複の無さの boolean 版。`List.Nodup` の decidability instance に依存せずに済ませる。
-/
def nodupB {α : Type _} [DecidableEq α] : List α → Bool
  | [] => true
  | x :: rest => decide (x ∉ rest) && nodupB rest

theorem nodupB_iff {α : Type _} [DecidableEq α] :
    ∀ (l : List α), nodupB l = true ↔ l.Nodup
  | [] => by simp [nodupB]
  | x :: rest => by simp [nodupB, List.nodup_cons, nodupB_iff rest]

/-- list の要素は、その要素を境に前後へ分割できる。 -/
theorem mem_split {α : Type _} : ∀ {l : List α} {a : α}, a ∈ l → ∃ s t, l = s ++ a :: t
  | [], _, h => absurd h (by simp)
  | x :: rest, a, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨[], rest, rfl⟩
    · obtain ⟨s, u, hu⟩ := mem_split h
      exact ⟨x :: s, u, by rw [hu]; rfl⟩

end Dom.ListUtil
