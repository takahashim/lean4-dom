import Dom.Properties.Tree

/-!
# tree order の列と `precedes`

`precedes` は「その node が属する木を tree order に並べた列での前後」である。
ここでは、その列を分解したときの補題をまとめる。

* `precedes_iff_mem_after` — `n` が先行するのは、列の `n` より後ろにあるものだけである
* `precedes_eq_precedesIn_preorder` — 部分木の列でも前後関係は同じである
* `precedesIn_lastD_eq_false` — 列の最後の要素は誰にも先行しない

`remove` の関係意味論（`Dom/Spec/Remove.lean`）の
"adjust a node pointer" がこれらを使う。
-/

namespace Dom

open Dom.ListUtil

/-! ## 木の中にあることの持ち上げ -/

/-- ancestor は木にある。 -/
theorem exists_data_of_ancestor' {t : Tree} (hwf : WellFormed t) {a n : NodeId}
    (h : Ancestor t a n) : ∃ ad, t.get? a = some ad := by
  induction h with
  | step hp => exact exists_data_of_parentOf hwf hp
  | trans _ _ ih => exact ih

theorem exists_data_of_inclusiveAncestor {t : Tree} (hwf : WellFormed t) {a n : NodeId}
    (h : InclusiveAncestor t a n) {nd : NodeData} (hn : t.get? n = some nd) :
    ∃ ad, t.get? a = some ad := by
  rcases h with rfl | ha
  · exact ⟨nd, hn⟩
  · exact exists_data_of_ancestor' hwf ha

/-- descendant も木にある。 -/
theorem exists_data_of_inclusiveDescendant {t : Tree} {r x : NodeId} {rd : NodeData}
    (hr : t.get? r = some rd) (h : InclusiveDescendant t x r) : ∃ xd, t.get? x = some xd := by
  rcases h with rfl | ha
  · exact ⟨rd, hr⟩
  · cases ha with
    | step hp => obtain ⟨xd, hxd, -⟩ := parentOf_eq_some hp; exact ⟨xd, hxd⟩
    | trans hp _ => obtain ⟨xd, hxd, -⟩ := parentOf_eq_some hp; exact ⟨xd, hxd⟩

/-! ## 列の中の位置と `precedesIn` -/

theorem precedesIn_self : ∀ (l : List NodeId) (a : NodeId), l.Nodup → precedesIn l a a = false
  | [], _, _ => rfl
  | x :: rest, a, hnd => by
    by_cases hxa : x = a
    · subst hxa
      rw [precedesIn_cons_self]
      simp only [decide_eq_false_iff_not]
      exact (List.nodup_cons.mp hnd).1
    · rw [precedesIn_cons_ne hxa hxa]
      exact precedesIn_self rest a (List.nodup_cons.mp hnd).2

/-- 列に無い node は誰にも先行しない。 -/
theorem precedesIn_of_not_mem {a b : NodeId} :
    ∀ (l : List NodeId), a ∉ l → precedesIn l a b = false
  | [], _ => rfl
  | x :: rest, ha => by
    have hxa : x ≠ a := fun he => ha (he ▸ List.mem_cons_self ..)
    by_cases hxb : x = b
    · rw [precedesIn_cons_target hxa hxb]
    · rw [precedesIn_cons_ne hxa hxb]
      exact precedesIn_of_not_mem rest (fun h => ha (List.mem_cons_of_mem _ h))

/-- 後ろにある要素は、前にある要素に先行しない。 -/
theorem precedesIn_eq_false_of_later {a b : NodeId} :
    ∀ (l₁ l₂ : List NodeId), a ∉ l₁ → b ∈ l₁ → precedesIn (l₁ ++ a :: l₂) a b = false
  | [], _, _, hb => by simp at hb
  | x :: rest, l₂, ha, hb => by
    have hxa : x ≠ a := fun he => ha (he ▸ List.mem_cons_self ..)
    by_cases hxb : x = b
    · rw [List.cons_append, precedesIn_cons_target hxa hxb]
    · rw [List.cons_append, precedesIn_cons_ne hxa hxb]
      refine precedesIn_eq_false_of_later rest l₂ (fun h => ha (List.mem_cons_of_mem _ h)) ?_
      rcases List.mem_cons.mp hb with he | h
      · exact absurd he.symm hxb
      · exact h

/-- 前にある要素だけを飛ばした形。 -/
theorem precedesIn_split {a b : NodeId} :
    ∀ (l₁ l₂ : List NodeId), a ∉ l₁ →
      precedesIn (l₁ ++ a :: l₂) a b = (if b ∈ l₁ then false else decide (b ∈ l₂))
  | [], _, _ => by rw [List.nil_append, precedesIn_cons_self]; simp
  | x :: rest, l₂, ha => by
    have hxa : x ≠ a := fun he => ha (he ▸ List.mem_cons_self ..)
    by_cases hxb : x = b
    · rw [List.cons_append, precedesIn_cons_target hxa hxb, if_pos (by rw [← hxb]; simp)]
    · rw [List.cons_append, precedesIn_cons_ne hxa hxb,
        precedesIn_split rest l₂ (fun h => ha (List.mem_cons_of_mem _ h))]
      by_cases hb : b ∈ rest
      · rw [if_pos hb, if_pos (List.mem_cons_of_mem _ hb)]
      · rw [if_neg hb, if_neg (by simpa using ⟨fun he => hxb he.symm, hb⟩)]

theorem lastD_mem {α : Type} : ∀ (l : List α) (d : α), l ≠ [] → lastD l d ∈ l
  | [], _, h => absurd rfl h
  | [x], _, _ => by simp [lastD]
  | x :: y :: rest, d, _ =>
    List.mem_cons_of_mem _ (by
      simpa [lastD] using lastD_mem (y :: rest) d (by simp))

/-- 列の最後の要素は、その列のどの要素にも先行しない。 -/
theorem precedesIn_lastD_eq_false :
    ∀ (l : List NodeId) (d x : NodeId), l.Nodup → x ∈ l → precedesIn l (lastD l d) x = false
  | [], _, _, _, hx => by simp at hx
  | [a], d, x, _, hx => by
    have : x = a := by simpa using hx
    subst this
    simp [lastD, precedesIn_cons_self]
  | a :: b :: rest, d, x, hnd, hx => by
    have hm : lastD (b :: rest) d ∈ b :: rest := lastD_mem _ d (by simp)
    have hma : lastD (b :: rest) d ≠ a := by
      intro he
      exact (List.nodup_cons.mp hnd).1 (he ▸ hm)
    have hlast : lastD (a :: b :: rest) d = lastD (b :: rest) d := rfl
    rw [hlast]
    by_cases hxa : a = x
    · rw [precedesIn_cons_target (Ne.symm hma) hxa]
    · rw [precedesIn_cons_ne (Ne.symm hma) hxa]
      refine precedesIn_lastD_eq_false (b :: rest) d x (List.nodup_cons.mp hnd).2 ?_
      rcases List.mem_cons.mp hx with he | h
      · exact absurd he.symm hxa
      · exact h

/-! ## 部分木の列でも前後関係は同じ -/

/--
tree order の前後関係は、どの祖先を根として列挙しても同じである。

`precedesIn_preorder_iff_struct` が、列挙の順序が木の構造だけで決まることを言っているので、
根の取り方に依らない。
-/
theorem precedes_eq_precedesIn_preorder {t : Tree} (hwf : WellFormed t) {r x y : NodeId}
    {rd : NodeData} (hr : t.get? r = some rd) (hx : InclusiveDescendant t x r)
    (hy : InclusiveDescendant t y r) :
    precedes t x y = precedesIn (preorder t r) x y := by
  by_cases hxy : x = y
  · subst hxy
    rw [precedesIn_self _ _ (preorder_nodup hwf r)]
    show precedesIn (treeOrder t x) x x = false
    exact precedesIn_self _ _ (treeOrder_nodup hwf x)
  · -- root を根としても r を根としても、同じ構造的な条件になる。
    have hrootx : InclusiveDescendant t x (root t x) := root_inclusive_ancestor t x
    have hrx : root t r = root t x := by
      rcases hx with he | ha
      · rw [he]
      · exact (root_eq_of_ancestor hwf ha).symm ▸ rfl
    have hrooty : InclusiveDescendant t y (root t x) := by
      have hry : InclusiveDescendant t r (root t x) := by
        rw [← hrx]; exact root_inclusive_ancestor t r
      exact InclusiveAncestor.trans_inclusive hry hy
    obtain ⟨rootd, hrootd⟩ : ∃ d, t.get? (root t x) = some d := by
      obtain ⟨xd, hxd⟩ := exists_data_of_inclusiveDescendant hr hx
      exact exists_data_of_inclusiveAncestor hwf hrootx hxd
    have h1 := precedesIn_preorder_iff_struct hwf hrootd hrootx hrooty hxy
    have h2 := precedesIn_preorder_iff_struct hwf hr hx hy hxy
    show precedesIn (preorder t (root t x)) x y = _
    cases hb1 : precedesIn (preorder t (root t x)) x y <;>
      cases hb2 : precedesIn (preorder t r) x y
    · rfl
    · exact absurd (h1.mpr (h2.mp hb2)) (by simp [hb1])
    · exact absurd (h2.mpr (h1.mp hb1)) (by simp [hb2])
    · rfl

/-! ## tree order の列を切ったとき -/

/-- `n` が先行するのは、tree order の列で `n` より後ろにあるものだけである。 -/
theorem precedes_iff_mem_after {t : Tree} (hwf : WellFormed t) {n x : NodeId}
    {before after : List NodeId} (hsplit : treeOrder t n = before ++ n :: after) :
    precedes t n x = true ↔ x ∈ after := by
  have hnd : (before ++ n :: after).Nodup := hsplit ▸ treeOrder_nodup hwf n
  obtain ⟨hb, hna, hdisj⟩ := List.nodup_append.mp hnd
  have hnb : n ∉ before := fun h => hdisj n h n (List.mem_cons_self ..) rfl
  show precedesIn (treeOrder t n) n x = true ↔ _
  rw [hsplit, precedesIn_split before after hnb]
  by_cases hx : x ∈ before
  · rw [if_pos hx]
    simp only [Bool.false_eq_true, false_iff]
    exact fun hxa => hdisj x hx x (List.mem_cons_of_mem _ hxa) rfl
  · rw [if_neg hx]
    simp

end Dom
