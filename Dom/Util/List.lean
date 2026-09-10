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

/--
`l` に最初に現れる `c` の直前に `a` を挿入する。`c` が無ければ末尾に加える。

DOM Standard §4.2.3 insert の「child の直前に挿入する」step に対応する。
-/
def insertBeforeFirst {α : Type _} [DecidableEq α] : List α → α → α → List α
  | [], _, a => [a]
  | x :: rest, c, a => if x = c then a :: x :: rest else x :: insertBeforeFirst rest c a

/-- `child` の直前（`child` が `none` なら末尾）に `a` を挿入する。 -/
def insertBefore {α : Type _} [DecidableEq α] (l : List α) (child : Option α) (a : α) : List α :=
  match child with
  | none => l ++ [a]
  | some c => insertBeforeFirst l c a

@[simp] theorem insertBefore_none {α : Type _} [DecidableEq α] (l : List α) (a : α) :
    insertBefore l none a = l ++ [a] := rfl

@[simp] theorem insertBefore_some {α : Type _} [DecidableEq α] (l : List α) (c a : α) :
    insertBefore l (some c) a = insertBeforeFirst l c a := rfl

@[simp] theorem insertBeforeFirst_nil {α : Type _} [DecidableEq α] (c a : α) :
    insertBeforeFirst ([] : List α) c a = [a] := rfl

theorem insertBeforeFirst_cons_self {α : Type _} [DecidableEq α] {y c : α} (h : y = c)
    (rest : List α) (a : α) : insertBeforeFirst (y :: rest) c a = a :: y :: rest := by
  simp [insertBeforeFirst, h]

theorem insertBeforeFirst_cons_ne {α : Type _} [DecidableEq α] {y c : α} (h : y ≠ c)
    (rest : List α) (a : α) :
    insertBeforeFirst (y :: rest) c a = y :: insertBeforeFirst rest c a := by
  simp [insertBeforeFirst, h]

theorem mem_insertBeforeFirst {α : Type _} [DecidableEq α] (c a x : α) :
    ∀ (l : List α), x ∈ insertBeforeFirst l c a ↔ x = a ∨ x ∈ l
  | [] => by simp
  | y :: rest => by
    by_cases h : y = c
    · rw [insertBeforeFirst_cons_self h]; simp
    · rw [insertBeforeFirst_cons_ne h]
      simp only [List.mem_cons, mem_insertBeforeFirst c a x rest]
      exact or_left_comm

theorem mem_insertBefore {α : Type _} [DecidableEq α] (l : List α) (child : Option α) (a x : α) :
    x ∈ insertBefore l child a ↔ x = a ∨ x ∈ l := by
  cases child with
  | none => simp only [insertBefore_none, List.mem_append, List.mem_singleton]; exact Or.comm
  | some c => rw [insertBefore_some]; exact mem_insertBeforeFirst c a x l

theorem nodup_insertBeforeFirst {α : Type _} [DecidableEq α] {a : α} (c : α) :
    ∀ (l : List α), l.Nodup → a ∉ l → (insertBeforeFirst l c a).Nodup
  | [], _, _ => by simp
  | y :: rest, hnd, hnot => by
    have hnd' : rest.Nodup := (List.nodup_cons.mp hnd).2
    have hy : y ∉ rest := (List.nodup_cons.mp hnd).1
    have hay : a ≠ y := fun he => hnot (he ▸ List.mem_cons_self ..)
    have hanot : a ∉ rest := fun he => hnot (List.mem_cons_of_mem _ he)
    by_cases h : y = c
    · rw [insertBeforeFirst_cons_self h]
      exact List.nodup_cons.mpr ⟨hnot, hnd⟩
    · rw [insertBeforeFirst_cons_ne h]
      refine List.nodup_cons.mpr ⟨?_, nodup_insertBeforeFirst c rest hnd' hanot⟩
      intro hmem
      rcases (mem_insertBeforeFirst c a y rest).mp hmem with he | he
      · exact hay he.symm
      · exact hy he

theorem nodup_insertBefore {α : Type _} [DecidableEq α] {l : List α} {a : α}
    (child : Option α) (hnd : l.Nodup) (hnot : a ∉ l) : (insertBefore l child a).Nodup := by
  cases child with
  | none =>
    rw [insertBefore_none]
    refine List.nodup_append.mpr ⟨hnd, by simp, ?_⟩
    intro x hx y hy hxy
    subst hxy
    have hxa : x = a := by simpa using hy
    subst hxa
    exact hnot hx
  | some c => exact nodup_insertBeforeFirst c l hnd hnot

/-- `c` が `l` に現れるなら、`a` はちょうど `c` の直前に入る。 -/
theorem insertBeforeFirst_eq_of_mem {α : Type _} [DecidableEq α] {c : α} (a : α) :
    ∀ {l : List α}, c ∈ l →
      ∃ s₁ s₂, l = s₁ ++ c :: s₂ ∧ insertBeforeFirst l c a = s₁ ++ a :: c :: s₂
  | [], h => absurd h (by simp)
  | y :: rest, h => by
    by_cases hy : y = c
    · exact ⟨[], rest, by rw [hy]; rfl, by rw [insertBeforeFirst_cons_self hy, hy]; rfl⟩
    · have hrest : c ∈ rest := by
        rcases List.mem_cons.mp h with he | he
        · exact absurd he.symm hy
        · exact he
      obtain ⟨s₁, s₂, h₁, h₂⟩ := insertBeforeFirst_eq_of_mem a hrest
      exact ⟨y :: s₁, s₂, by rw [h₁]; rfl, by rw [insertBeforeFirst_cons_ne hy, h₂]; rfl⟩

/--
`l` から `a` をすべて取り除く。

`List.erase` は最初の一つしか取り除かないが、model では children の重複が
`WellFormed.children_nodup` で排除されているため結果は同じである。
すべて取り除く形にしておくと `a ∉ removeAll l a` が重複の無さを仮定せずに成り立ち、
証明が短くなる。
-/
def removeAll {α : Type _} [DecidableEq α] (l : List α) (a : α) : List α :=
  l.filter fun x => decide (x ≠ a)

theorem mem_removeAll {α : Type _} [DecidableEq α] (l : List α) (a x : α) :
    x ∈ removeAll l a ↔ x ≠ a ∧ x ∈ l := by
  simp only [removeAll, List.mem_filter, decide_eq_true_eq]
  exact And.comm

theorem not_mem_removeAll {α : Type _} [DecidableEq α] (l : List α) (a : α) :
    a ∉ removeAll l a := by
  simp [mem_removeAll]

theorem nodup_removeAll {α : Type _} [DecidableEq α] {l : List α} (h : l.Nodup) (a : α) :
    (removeAll l a).Nodup :=
  List.Pairwise.filter _ h

/-- `l` を最初に現れる `a` の直前で二つに分ける。`a` が無ければ `none`。 -/
def splitAt? {α : Type _} [DecidableEq α] : List α → α → Option (List α × List α)
  | [], _ => none
  | x :: rest, a =>
    if x = a then some ([], rest)
    else (splitAt? rest a).map fun q => (x :: q.1, q.2)

theorem splitAt?_eq_some {α : Type _} [DecidableEq α] {a : α} :
    ∀ {l : List α} {s₁ s₂ : List α}, splitAt? l a = some (s₁, s₂) → l = s₁ ++ a :: s₂
  | [], _, _, h => by simp [splitAt?] at h
  | x :: rest, s₁, s₂, h => by
    by_cases hx : x = a
    · simp only [splitAt?, if_pos hx, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1, ← h.2, hx]; rfl
    · simp only [splitAt?, if_neg hx, Option.map_eq_some_iff] at h
      obtain ⟨q, hq, he⟩ := h
      obtain ⟨u, v⟩ := q
      simp only [Prod.mk.injEq] at he
      rw [← he.1, ← he.2, splitAt?_eq_some hq]
      rfl

theorem removeAll_eq_self {α : Type _} [DecidableEq α] {l : List α} {a : α} (h : a ∉ l) :
    removeAll l a = l := by
  unfold removeAll
  refine List.filter_eq_self.mpr ?_
  intro x hx
  simp only [decide_eq_true_eq, ne_eq]
  intro he
  exact h (he ▸ hx)

/-- 分割した形での `removeAll`。 -/
theorem removeAll_append_cons {α : Type _} [DecidableEq α] {u v : List α} {a : α}
    (hu : a ∉ u) (hv : a ∉ v) : removeAll (u ++ a :: v) a = u ++ v := by
  unfold removeAll
  rw [List.filter_append, List.filter_cons]
  simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false]
  rw [show (u.filter fun x => decide (x ≠ a)) = u from removeAll_eq_self hu,
    show (v.filter fun x => decide (x ≠ a)) = v from removeAll_eq_self hv]

/-- 重複が無い list から要素を一つ取り除くと、長さがちょうど 1 減る。 -/
theorem length_removeAll {α : Type _} [DecidableEq α] :
    ∀ {l : List α} {a : α}, l.Nodup → a ∈ l → (removeAll l a).length + 1 = l.length
  | [], _, _, h => absurd h (by simp)
  | x :: rest, a, hnd, hmem => by
    have hrest : rest.Nodup := (List.nodup_cons.mp hnd).2
    have hx : x ∉ rest := (List.nodup_cons.mp hnd).1
    by_cases he : x = a
    · subst he
      have h1 : removeAll (x :: rest) x = removeAll rest x := by
        simp [removeAll]
      rw [h1, removeAll_eq_self hx]
      simp
    · have hmem' : a ∈ rest := by
        rcases List.mem_cons.mp hmem with h | h
        · exact absurd h.symm he
        · exact h
      have h1 : removeAll (x :: rest) a = x :: removeAll rest a := by
        simp [removeAll, he]
      have ih := length_removeAll hrest hmem'
      rw [h1]
      simp only [List.length_cons]
      omega

theorem length_insertBeforeFirst {α : Type _} [DecidableEq α] (c a : α) :
    ∀ (l : List α), (insertBeforeFirst l c a).length = l.length + 1
  | [] => rfl
  | x :: rest => by
    by_cases h : x = c
    · rw [insertBeforeFirst_cons_self h]; simp
    · rw [insertBeforeFirst_cons_ne h]
      simp [length_insertBeforeFirst c a rest]

theorem length_insertBefore {α : Type _} [DecidableEq α] (l : List α) (child : Option α) (a : α) :
    (insertBefore l child a).length = l.length + 1 := by
  cases child with
  | none => simp
  | some c => simpa using length_insertBeforeFirst c a l

/-- 最後の要素。空なら既定値。名前の揺れを避けるため自前で定義する。 -/
def lastD {α : Type _} : List α → α → α
  | [], d => d
  | [x], _ => x
  | _ :: rest, d => lastD rest d

theorem lastD_mem_or {α : Type _} : ∀ (l : List α) (d : α), lastD l d ∈ l ∨ lastD l d = d
  | [], _ => Or.inr rfl
  | [x], d => Or.inl (by simp [lastD])
  | x :: y :: rest, d => by
    rcases lastD_mem_or (y :: rest) d with h | h
    · exact Or.inl (List.mem_cons_of_mem _ (by simpa [lastD] using h))
    · exact Or.inr (by simpa [lastD] using h)

/--
`findIdx?` が `some i` を返すことと、その要素の直前で分割できることは同値である。

`Dom/Basic/Tree.lean` の `index` は children の中での位置なので、
この補題で「children を分割した形」と行き来する。
-/
theorem findIdx?_eq_some_iff_split {α : Type _} [DecidableEq α] {a : α} :
    ∀ {l : List α} {i : Nat},
      l.findIdx? (fun x => decide (x = a)) = some i ↔
        ∃ u v, l = u ++ a :: v ∧ u.length = i ∧ a ∉ u
  | [], i => by
    constructor
    · intro h; simp at h
    · rintro ⟨u, v, hu, _, _⟩
      cases u <;> simp at hu
  | x :: rest, i => by
    constructor
    · intro h
      rw [List.findIdx?_cons] at h
      by_cases hx : x = a
      · rw [if_pos (by simp [hx])] at h
        have hi : i = 0 := (Option.some.inj h).symm
        subst hi
        exact ⟨[], rest, by rw [hx]; rfl, rfl, by simp⟩
      · rw [if_neg (by simp [hx])] at h
        obtain ⟨i', hi', he⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨u, v, hu, hlen, hnot⟩ := findIdx?_eq_some_iff_split.mp hi'
        refine ⟨x :: u, v, by rw [hu]; rfl, by simp only [List.length_cons, hlen]; omega, ?_⟩
        intro hm
        rcases List.mem_cons.mp hm with he' | he'
        · exact hx he'.symm
        · exact hnot he'
    · rintro ⟨u, v, hu, hlen, hnot⟩
      rw [List.findIdx?_cons]
      cases u with
      | nil =>
        have hxa : x = a := (List.cons.inj hu).1
        rw [if_pos (by simp [hxa])]
        have hi : i = 0 := by simpa using hlen.symm
        rw [hi]
      | cons y u' =>
        obtain ⟨hy, hrest⟩ := List.cons.inj hu
        have hxa : x ≠ a := by
          intro he
          exact hnot (by rw [← hy, he]; exact List.mem_cons_self ..)
        rw [if_neg (by simp [hxa])]
        refine Option.map_eq_some_iff.mpr ⟨u'.length, ?_, ?_⟩
        · exact findIdx?_eq_some_iff_split.mpr ⟨u', v, hrest, rfl,
            fun hm => hnot (List.mem_cons_of_mem _ hm)⟩
        · simp only [List.length_cons] at hlen; omega

/-- 同じ位置で分割した list の、その位置の要素は等しい。 -/
theorem append_cons_inj {α : Type _} :
    ∀ {u u' : List α} {a b : α} {v v' : List α},
      u ++ a :: v = u' ++ b :: v' → u.length = u'.length → a = b
  | [], [], a, b, v, v', h, _ => (List.cons.inj h).1
  | [], _ :: _, _, _, _, _, _, hlen => by simp at hlen
  | _ :: _, [], _, _, _, _, _, hlen => by simp at hlen
  | x :: u, y :: u', a, b, v, v', h, hlen => by
    refine append_cons_inj (u := u) (u' := u') (a := a) (b := b) (v := v) (v' := v') ?_ ?_
    · exact (List.cons.inj h).2
    · simp only [List.length_cons] at hlen; omega

/-- `removeAll` した後の `findIdx?`。取り除いた位置より後ろなら 1 減る。 -/
theorem findIdx?_removeAll {α : Type _} [DecidableEq α] {l : List α} {a c : α} {i k : Nat}
    (hnd : l.Nodup) (hcn : c ≠ a)
    (ha : l.findIdx? (fun x => decide (x = a)) = some i)
    (hc : l.findIdx? (fun x => decide (x = c)) = some k) :
    (removeAll l a).findIdx? (fun x => decide (x = c)) = some (if i < k then k - 1 else k) := by
  obtain ⟨u, v, hl, hulen, hnu⟩ := findIdx?_eq_some_iff_split.mp ha
  subst hl
  obtain ⟨hndu, hndav, hcross⟩ := List.nodup_append.mp hnd
  have hnv : a ∉ v := (List.nodup_cons.mp hndav).1
  have hndv : v.Nodup := (List.nodup_cons.mp hndav).2
  rw [removeAll_append_cons hnu hnv]
  have hcmem : c ∈ u ++ a :: v := by
    obtain ⟨w1, w2, hw, _, _⟩ := findIdx?_eq_some_iff_split.mp hc
    rw [hw]; simp
  rcases List.mem_append.mp hcmem with hcu | hcav
  · -- c は取り除く位置より前
    obtain ⟨u1, u2, hu⟩ := mem_split hcu
    subst hu
    obtain ⟨hndu1, hndcu2, hcross1⟩ := List.nodup_append.mp hndu
    have hnu1 : c ∉ u1 := fun hm => hcross1 c hm c (by simp) rfl
    have hkeq : k = u1.length := by
      have : (u1 ++ c :: (u2 ++ a :: v)).findIdx? (fun x => decide (x = c)) = some u1.length :=
        findIdx?_eq_some_iff_split.mpr ⟨u1, u2 ++ a :: v, by simp, rfl, hnu1⟩
      rw [show u1 ++ c :: u2 ++ a :: v = u1 ++ c :: (u2 ++ a :: v) by simp] at hc
      rw [this] at hc
      exact (Option.some.inj hc).symm
    have hilt : k < i := by
      rw [hkeq, ← hulen]
      simp
    rw [if_neg (by omega)]
    rw [show u1 ++ c :: u2 ++ v = u1 ++ c :: (u2 ++ v) by simp]
    rw [findIdx?_eq_some_iff_split.mpr ⟨u1, u2 ++ v, rfl, rfl, hnu1⟩, hkeq]
  · -- c は取り除く位置より後ろ
    have hcv : c ∈ v := by
      rcases List.mem_cons.mp hcav with he | hm
      · exact absurd he hcn
      · exact hm
    obtain ⟨v1, v2, hv⟩ := mem_split hcv
    subst hv
    obtain ⟨hndv1, hndcv2, hcrossv⟩ := List.nodup_append.mp hndv
    have hnv1 : c ∉ v1 := fun hm => hcrossv c hm c (by simp) rfl
    have hncu : c ∉ u := fun hm => hcross c hm c (by simp) rfl
    have hnpre : c ∉ u ++ a :: v1 := by
      intro hm
      rcases List.mem_append.mp hm with h | h
      · exact hncu h
      · rcases List.mem_cons.mp h with he | h
        · exact hcn he
        · exact hnv1 h
    have hkeq : k = (u ++ a :: v1).length := by
      have : (u ++ a :: (v1 ++ c :: v2)).findIdx? (fun x => decide (x = c))
          = some (u ++ a :: v1).length :=
        findIdx?_eq_some_iff_split.mpr ⟨u ++ a :: v1, v2, by simp, rfl, hnpre⟩
      rw [this] at hc
      exact (Option.some.inj hc).symm
    have hilt : i < k := by
      rw [hkeq, ← hulen]
      simp
    rw [if_pos hilt]
    rw [show u ++ (v1 ++ c :: v2) = (u ++ v1) ++ c :: v2 by simp]
    have hnpre2 : c ∉ u ++ v1 := by
      intro hm
      rcases List.mem_append.mp hm with h | h
      · exact hncu h
      · exact hnv1 h
    rw [findIdx?_eq_some_iff_split.mpr ⟨u ++ v1, v2, rfl, rfl, hnpre2⟩, hkeq]
    simp

end Dom.ListUtil
