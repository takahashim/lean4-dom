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

/-- `removeAll` は filter した長さを増やさない。 -/
theorem length_filter_removeAll {α : Type _} [DecidableEq α] (a : α) (p : α → Bool) :
    ∀ (l : List α), ((removeAll l a).filter p).length ≤ (l.filter p).length
  | [] => Nat.le_refl _
  | x :: rest => by
    have ih := length_filter_removeAll a p rest
    by_cases hx : x = a
    · have h1 : removeAll (x :: rest) a = removeAll rest a := by
        simp [removeAll, hx]
      rw [h1, List.filter_cons]
      split
      · simp only [List.length_cons]; omega
      · exact ih
    · have h1 : removeAll (x :: rest) a = x :: removeAll rest a := by
        simp [removeAll, hx]
      rw [h1, List.filter_cons, List.filter_cons]
      split
      · simp only [List.length_cons]; omega
      · exact ih

/-- filter した結果が空なら、`removeAll` した後も空である。 -/
theorem filter_removeAll_eq_nil {α : Type _} [DecidableEq α] {l : List α} {a : α}
    {p : α → Bool} (h : l.filter p = []) : (removeAll l a).filter p = [] := by
  have := length_filter_removeAll a p l
  rw [h] at this
  exact List.eq_nil_of_length_eq_zero (Nat.le_zero.mp (by simpa using this))

/-- `removeAll` しても、最初に現れる `c` の前後の分割はそれぞれを `removeAll` したものになる。 -/
theorem splitAt?_removeAll {α : Type _} [DecidableEq α] {a c : α} (hc : c ≠ a) :
    ∀ {l u v : List α}, splitAt? l c = some (u, v) →
      splitAt? (removeAll l a) c = some (removeAll u a, removeAll v a)
  | [], _, _, h => by simp [splitAt?] at h
  | x :: rest, u, v, h => by
    by_cases hxc : x = c
    · simp only [splitAt?, if_pos hxc, Option.some.injEq, Prod.mk.injEq] at h
      have hxa : x ≠ a := by rw [hxc]; exact hc
      have h1 : removeAll (x :: rest) a = x :: removeAll rest a := by simp [removeAll, hxa]
      rw [h1, ← h.1, ← h.2]
      simp [splitAt?, hxc, removeAll]
    · simp only [splitAt?, if_neg hxc, Option.map_eq_some_iff] at h
      obtain ⟨q, hq, he⟩ := h
      obtain ⟨u', v'⟩ := q
      simp only [Prod.mk.injEq] at he
      have ih := splitAt?_removeAll hc hq
      by_cases hxa : x = a
      · have h1 : removeAll (x :: rest) a = removeAll rest a := by simp [removeAll, hxa]
        have h2 : removeAll u a = removeAll u' a := by
          rw [← he.1]; simp [removeAll, hxa]
        rw [h1, h2, ← he.2]
        exact ih
      · have h1 : removeAll (x :: rest) a = x :: removeAll rest a := by simp [removeAll, hxa]
        have h2 : removeAll u a = x :: removeAll u' a := by
          rw [← he.1]; simp [removeAll, hxa]
        rw [h1, h2, ← he.2]
        simp [splitAt?, hxc, ih]

/-- `splitAt?` が `none` を返すのは、その要素が無いときだけである。 -/
theorem splitAt?_isSome_of_mem {α : Type _} [DecidableEq α] {a : α} :
    ∀ {l : List α}, a ∈ l → (splitAt? l a).isSome
  | [], h => by simp at h
  | x :: rest, h => by
    by_cases hx : x = a
    · simp [splitAt?, hx]
    · rcases List.mem_cons.mp h with he | hm
      · exact absurd he.symm hx
      · have := splitAt?_isSome_of_mem hm
        cases hs : splitAt? rest a with
        | none => rw [hs] at this; simp at this
        | some q => simp [splitAt?, hx, hs]

/-! ## filter と insertBefore -/

theorem length_filter_insertBeforeFirst {α : Type _} [DecidableEq α] (p : α → Bool) (c a : α) :
    ∀ l : List α, ((insertBeforeFirst l c a).filter p).length =
      (l.filter p).length + (if p a then 1 else 0)
  | [] => by
    simp only [insertBeforeFirst_nil, List.filter_nil, List.length_nil, Nat.zero_add]
    by_cases h : p a <;> simp [List.filter, h]
  | y :: rest => by
    by_cases hy : y = c
    · rw [insertBeforeFirst_cons_self hy]
      by_cases h : p a <;> simp [List.filter, h, Nat.add_comm]
    · rw [insertBeforeFirst_cons_ne hy]
      by_cases h : p y <;>
        simp [List.filter, h, length_filter_insertBeforeFirst p c a rest, Nat.succ_add]

/-- `insertBefore` で増える要素は高々一つなので、filter の長さも高々一つ増える。 -/
theorem length_filter_insertBefore {α : Type _} [DecidableEq α] (p : α → Bool)
    (l : List α) (child : Option α) (a : α) :
    ((insertBefore l child a).filter p).length =
      (l.filter p).length + (if p a then 1 else 0) := by
  cases child with
  | none =>
    rw [insertBefore_none, List.filter_append]
    by_cases h : p a <;> simp [List.filter, h]
  | some c => rw [insertBefore_some]; exact length_filter_insertBeforeFirst p c a l

theorem filter_insertBeforeFirst_of_neg {α : Type _} [DecidableEq α] {p : α → Bool} {a : α}
    (ha : p a = false) (c : α) :
    ∀ l : List α, (insertBeforeFirst l c a).filter p = l.filter p
  | [] => by simp [List.filter, ha]
  | y :: rest => by
    by_cases hy : y = c
    · rw [insertBeforeFirst_cons_self hy]; simp [List.filter, ha]
    · rw [insertBeforeFirst_cons_ne hy]
      by_cases h : p y <;> simp [List.filter, h, filter_insertBeforeFirst_of_neg ha c rest]

/-- filter を通らない要素を挿しても、filter の結果は変わらない。 -/
theorem filter_insertBefore_of_neg {α : Type _} [DecidableEq α] {p : α → Bool} {a : α}
    (ha : p a = false) (l : List α) (child : Option α) :
    (insertBefore l child a).filter p = l.filter p := by
  cases child with
  | none => rw [insertBefore_none, List.filter_append]; simp [List.filter, ha]
  | some c => rw [insertBefore_some]; exact filter_insertBeforeFirst_of_neg ha c l

/-! ## splitAt? と append -/

/-- 分割点が前半にあるなら、後ろに足した分は `after` 側に付く。 -/
theorem splitAt?_append_left {α : Type _} [DecidableEq α] {x : α} :
    ∀ {A : List α} {u v : List α}, splitAt? A x = some (u, v) → ∀ C : List α,
      splitAt? (A ++ C) x = some (u, v ++ C)
  | [], _, _, h, _ => by simp [splitAt?] at h
  | y :: rest, u, v, h, C => by
    by_cases hy : y = x
    · simp only [splitAt?, if_pos hy, Option.some.injEq, Prod.mk.injEq] at h
      simp [splitAt?, hy, ← h.1, ← h.2]
    · simp only [splitAt?, if_neg hy, Option.map_eq_some_iff] at h
      obtain ⟨q, hq, he⟩ := h
      obtain ⟨u', v'⟩ := q
      simp only [Prod.mk.injEq] at he
      simp [splitAt?, hy, splitAt?_append_left hq C, ← he.1, ← he.2]

/-- 分割点が前半に無いなら、前半はそのまま `before` 側に付く。 -/
theorem splitAt?_append_right {α : Type _} [DecidableEq α] {x : α} :
    ∀ {A : List α}, x ∉ A → ∀ {C u v : List α}, splitAt? C x = some (u, v) →
      splitAt? (A ++ C) x = some (A ++ u, v)
  | [], _, _, _, _, h => by simpa using h
  | y :: rest, hnot, C, u, v, h => by
    have hy : y ≠ x := fun he => hnot (he ▸ List.mem_cons_self ..)
    have hrest : x ∉ rest := fun hm => hnot (List.mem_cons_of_mem _ hm)
    simp [splitAt?, hy, splitAt?_append_right hrest h]

/-- 挿した要素自身の分割は、その前後そのものである。 -/
theorem splitAt?_append_cons_self {α : Type _} [DecidableEq α] {n : α} {A : List α}
    (hnot : n ∉ A) (B : List α) : splitAt? (A ++ n :: B) n = some (A, B) := by
  have h : splitAt? (n :: B) n = some ([], B) := by simp [splitAt?]
  simpa using splitAt?_append_right hnot h

/-- 含まれない要素では `splitAt?` は `none` を返す。 -/
theorem splitAt?_eq_none_of_not_mem {α : Type _} [DecidableEq α] {a : α} :
    ∀ {l : List α}, a ∉ l → splitAt? l a = none
  | [], _ => rfl
  | y :: rest, hnot => by
    have hy : y ≠ a := fun he => hnot (he ▸ List.mem_cons_self ..)
    have hrest : a ∉ rest := fun hm => hnot (List.mem_cons_of_mem _ hm)
    simp [splitAt?, hy, splitAt?_eq_none_of_not_mem hrest]

/-- 含まれる要素なら `splitAt?` は分割を返す。 -/
theorem exists_splitAt?_of_mem {α : Type _} [DecidableEq α] {a : α} {l : List α} (h : a ∈ l) :
    ∃ u v, splitAt? l a = some (u, v) := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (splitAt?_isSome_of_mem h)
  exact ⟨q.1, q.2, hq⟩

/-- 元の list に無ければ、取り除いた後にも無い。 -/
theorem splitAt?_removeAll_none {α : Type _} [DecidableEq α] {a c : α}
    {l : List α} (h : splitAt? l c = none) : splitAt? (removeAll l a) c = none := by
  refine splitAt?_eq_none_of_not_mem ?_
  intro hmem
  have hmem' := ((mem_removeAll l a c).mp hmem).2
  obtain ⟨u, v, hs⟩ := exists_splitAt?_of_mem hmem'
  rw [hs] at h
  simp at h

/-- `removeAll` は filter なので sublist である。 -/
theorem removeAll_sublist {α : Type _} [DecidableEq α] (l : List α) (a : α) :
    (removeAll l a).Sublist l := List.filter_sublist

theorem removeAll_append {α : Type _} [DecidableEq α] (l₁ l₂ : List α) (a : α) :
    removeAll (l₁ ++ l₂) a = removeAll l₁ a ++ removeAll l₂ a := by
  unfold removeAll; exact List.filter_append ..

theorem removeAll_cons {α : Type _} [DecidableEq α] (x : α) (l : List α) (a : α) :
    removeAll (x :: l) a = if x = a then removeAll l a else x :: removeAll l a := by
  unfold removeAll
  by_cases h : x = a <;> simp [List.filter, h]

/--
`A ++ c :: B` から `n` と `c` を取り除くと、`A` と `B` から `n` を取り除いたものが並ぶ。

`c` が `A` にも `B` にも現れないこと（children の Nodup）を使う。
-/
theorem removeAll_removeAll_split {α : Type _} [DecidableEq α] {A B : List α} {c n : α}
    (hcA : c ∉ A) (hcB : c ∉ B) :
    removeAll (removeAll (A ++ c :: B) n) c = removeAll A n ++ removeAll B n := by
  have hA : removeAll (removeAll A n) c = removeAll A n :=
    removeAll_eq_self fun hm => hcA ((mem_removeAll _ _ _).mp hm).2
  have hB : removeAll (removeAll B n) c = removeAll B n :=
    removeAll_eq_self fun hm => hcB ((mem_removeAll _ _ _).mp hm).2
  rw [removeAll_append, removeAll_cons]
  by_cases hcn : c = n
  · rw [if_pos hcn, removeAll_append, hA, hB]
  · rw [if_neg hcn, removeAll_append, removeAll_cons, if_pos rfl, hA, hB]

/-- Nodup な list を `A ++ c :: B` と分けると、`c` は前半にも後半にも現れない。 -/
theorem nodup_split {α : Type _} {A B : List α} {c : α} (h : (A ++ c :: B).Nodup) :
    c ∉ A ∧ c ∉ B := by
  have h1 := List.nodup_append.mp h
  exact ⟨fun hm => h1.2.2 c hm c (by simp) rfl, (List.nodup_cons.mp h1.2.1).1⟩

/-- `set` の要素は、置いた値か元の list の要素である。 -/
theorem mem_set_cases {α : Type _} :
    ∀ (l : List α) (i : Nat) (x y : α), y ∈ l.set i x → y = x ∨ y ∈ l
  | [], _, _, _, h => by simp at h
  | z :: rest, 0, x, y, h => by
    simp only [List.set, List.mem_cons] at h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)
  | z :: rest, i + 1, x, y, h => by
    simp only [List.set, List.mem_cons] at h
    rcases h with h | h
    · exact Or.inr (by rw [h]; exact List.mem_cons_self ..)
    · rcases mem_set_cases rest i x y h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (List.mem_cons_of_mem _ h')

/-! ## 述語で最初の一つだけを触る -/

/-- 述語を満たす最初の要素を `f` で置き換える。無ければそのまま。 -/
def updateFirst {α : Type _} (p : α → Bool) (f : α → α) : List α → List α
  | [] => []
  | x :: xs => if p x then f x :: xs else x :: updateFirst p f xs

/-- 述語を満たす最初の要素を取り除く。無ければそのまま。 -/
def eraseFirst {α : Type _} (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs => if p x then xs else x :: eraseFirst p xs

/-- `f` が `g` の値を変えないなら、`updateFirst` は `g` の像を変えない。 -/
theorem map_updateFirst {α β : Type _} {p : α → Bool} {f : α → α} {g : α → β}
    (hf : ∀ x, g (f x) = g x) : ∀ l : List α, (updateFirst p f l).map g = l.map g
  | [] => rfl
  | x :: xs => by
    show (if p x then f x :: xs else x :: updateFirst p f xs).map g = (x :: xs).map g
    by_cases h : p x
    · simp [h, hf]
    · simp [h, map_updateFirst hf xs]

/-- `updateFirst` は長さを変えない。 -/
theorem length_updateFirst {α : Type _} {p : α → Bool} {f : α → α} :
    ∀ l : List α, (updateFirst p f l).length = l.length
  | [] => rfl
  | x :: xs => by
    show (if p x then f x :: xs else x :: updateFirst p f xs).length = (x :: xs).length
    by_cases h : p x
    · simp [h]
    · simp [h, length_updateFirst xs]

/-- `eraseFirst` の結果は元の list の部分列である。 -/
theorem eraseFirst_sublist {α : Type _} {p : α → Bool} :
    ∀ l : List α, (eraseFirst p l).Sublist l
  | [] => List.Sublist.refl _
  | x :: xs => by
    show (if p x then xs else x :: eraseFirst p xs).Sublist (x :: xs)
    by_cases h : p x
    · simp only [if_pos h]; exact (List.Sublist.refl xs).cons x
    · simp only [if_neg h]; exact (eraseFirst_sublist xs).cons_cons x

/-- `updateFirst` の要素は、元の要素か `f` を当てたものである。 -/
theorem mem_updateFirst {α : Type _} {p : α → Bool} {f : α → α} {y : α} :
    ∀ {l : List α}, y ∈ updateFirst p f l → y ∈ l ∨ ∃ x ∈ l, y = f x
  | [], h => by simp [updateFirst] at h
  | x :: xs, h => by
    show y ∈ x :: xs ∨ ∃ z ∈ x :: xs, y = f z
    have h' : y ∈ (if p x then f x :: xs else x :: updateFirst p f xs) := h
    by_cases hx : p x
    · rw [if_pos hx] at h'
      rcases List.mem_cons.mp h' with rfl | h'
      · exact Or.inr ⟨x, List.mem_cons_self, rfl⟩
      · exact Or.inl (List.mem_cons_of_mem _ h')
    · rw [if_neg hx] at h'
      rcases List.mem_cons.mp h' with rfl | h'
      · exact Or.inl List.mem_cons_self
      · rcases mem_updateFirst h' with h'' | ⟨z, hz, hy⟩
        · exact Or.inl (List.mem_cons_of_mem _ h'')
        · exact Or.inr ⟨z, List.mem_cons_of_mem _ hz, hy⟩

end Dom.ListUtil
