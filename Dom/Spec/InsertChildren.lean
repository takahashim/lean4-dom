import Dom.Spec.InsertCongr
import Dom.Spec.AdoptCongr

/-!
# `insert` の後の parent の children

`InsertSpec` から「parent の children は、元の children の reference child の直前に
入る node の列を挟んだもの」を取り出す。`Range.insertNode` の step 10-11 の newOffset が
「最後に入った node の次」に等しいことを示すのに使う。
-/

namespace Dom.Spec

open Dom
open Dom.ListUtil (insertAllBefore)

/-! ## 列の補題 -/

theorem insertBeforeFirst_split {c a : NodeId} :
    ∀ (pre post : List NodeId), c ∉ pre →
      ListUtil.insertBeforeFirst (pre ++ c :: post) c a = pre ++ a :: c :: post
  | [], post, _ => by simp [ListUtil.insertBeforeFirst]
  | x :: pre, post, hc => by
    have hx : x ≠ c := fun he => hc (by simp [he])
    simp only [List.cons_append, ListUtil.insertBeforeFirst, if_neg hx]
    rw [insertBeforeFirst_split pre post (fun h => hc (by simp [h]))]

theorem insertAllBefore_some {c : NodeId} :
    ∀ (ns pre post : List NodeId), c ∉ pre → c ∉ ns →
      insertAllBefore (pre ++ c :: post) (some c) ns = pre ++ ns ++ c :: post
  | [], pre, post, _, _ => by simp [ListUtil.insertAllBefore]
  | a :: ns, pre, post, hpre, hns => by
    have hac : a ≠ c := fun he => hns (by simp [he])
    show ListUtil.insertAllBefore (ListUtil.insertBefore (pre ++ c :: post) (some c) a) (some c) ns = _
    rw [ListUtil.insertBefore_some, insertBeforeFirst_split pre post hpre,
      show pre ++ a :: c :: post = (pre ++ [a]) ++ c :: post by simp,
      insertAllBefore_some ns (pre ++ [a]) post (by simp [hpre, hac.symm])
        (fun h => hns (by simp [h]))]
    simp

theorem insertAllBefore_none : ∀ (ns l : List NodeId), insertAllBefore l none ns = l ++ ns
  | [], l => by simp [ListUtil.insertAllBefore]
  | a :: ns, l => by
    show ListUtil.insertAllBefore (ListUtil.insertBefore l none a) none ns = _
    rw [ListUtil.insertBefore_none, insertAllBefore_none ns]
    simp

/-! ## 木の変化の枠 -/

variable {s s' : DOMState}

theorem documentAssigned_frame {t t' : Tree} {node doc : NodeId}
    (h : DocumentAssigned t t' node doc) (hn : ∃ d, t.get? node = some d) (m : NodeId) :
    childrenOf t' m = childrenOf t m ∧ parentOf t' m = parentOf t m := by
  by_cases hin : InclusiveDescendant t m node
  · cases hm : t.get? m with
    | some d =>
      have := h.inside m d hm hin
      rw [parentOf_eq, parentOf_eq, childrenOf_eq this, childrenOf_eq hm, this, hm]
      exact ⟨rfl, rfl⟩
    | none =>
      exfalso
      rcases hin with he | ha
      · obtain ⟨d, hd⟩ := hn
        rw [he, hm] at hd
        cases hd
      · obtain ⟨p, hp⟩ := ha.parent_isSome
        rw [parentOf_eq, hm] at hp
        cases hp
  · have := h.outside m hin
    rw [parentOf_eq, parentOf_eq, this]
    unfold childrenOf
    rw [this]
    exact ⟨rfl, rfl⟩

/-- parent の無い node の adopt は、children と parent を一つも変えない。 -/
theorem adoptSpec_frame_of_no_parent {node doc : NodeId} (h : AdoptSpec s node doc s')
    (hnp : parentOf s.tree node = none) (m : NodeId) :
    childrenOf s'.tree m = childrenOf s.tree m ∧ parentOf s'.tree m = parentOf s.tree m := by
  obtain ⟨od, hod, s₁, hst2, hst3⟩ := h
  obtain ⟨nd, hnd⟩ := exists_data_of_ownerDocumentOf hod
  have hs₁ : s₁ = s := by
    rcases hst2 with ⟨-, rfl⟩ | ⟨⟨p, hp⟩, -⟩
    · rfl
    · rw [hnp] at hp; cases hp
  subst hs₁
  split at hst3
  · subst hst3; exact ⟨rfl, rfl⟩
  · exact documentAssigned_frame hst3.1 ⟨nd, hnd⟩ m

theorem removeSpec_frame {c : NodeId} {b : Bool} (h : RemoveSpec s c b s') :
    ∃ p, parentOf s.tree c = some p ∧ parentOf s'.tree c = none ∧
      (∀ m, m ≠ c → parentOf s'.tree m = parentOf s.tree m) ∧
      (∀ m, m ≠ p → childrenOf s'.tree m = childrenOf s.tree m) := by
  obtain ⟨p, -, hpre, -, -, -, htr, -, -⟩ := h
  exact ⟨p, hpre, htr.detached, htr.otherParents, htr.otherChildren⟩

/-- 同じ parent `q` の子を順に外すと、`q` 以外の children は変わらず、外したものは parent を失う。 -/
theorem removeEachSpec_frame {q : NodeId} {b : Bool} : ∀ {ns : List NodeId} {s s' : DOMState},
    RemoveEachSpec s ns b s' → ns.Nodup → (∀ c ∈ ns, parentOf s.tree c = some q) →
    (∀ m, m ≠ q → childrenOf s'.tree m = childrenOf s.tree m) ∧
      (∀ c ∈ ns, parentOf s'.tree c = none) ∧
      (∀ m, m ∉ ns → parentOf s'.tree m = parentOf s.tree m)
  | [], s, s', h, _, _ => by
    cases h
    exact ⟨fun _ _ => rfl, fun _ h => by simp at h, fun _ _ => rfl⟩
  | n :: ns, s, s', h, hnd, hq => by
    cases h with
    | cons hr hrest =>
      obtain ⟨p, hp, hdet, hop, hoc⟩ := removeSpec_frame hr
      rw [hq n (by simp)] at hp
      cases hp
      have hnd' := List.nodup_cons.mp hnd
      obtain ⟨ihc, ihd, ihp⟩ := removeEachSpec_frame hrest hnd'.2 (fun c hc => by
        rw [hop c (fun he => hnd'.1 (he ▸ hc))]
        exact hq c (by simp [hc]))
      refine ⟨fun m hm => by rw [ihc m hm, hoc m hm], fun c hc => ?_, fun m hm => ?_⟩
      · rcases List.mem_cons.mp hc with rfl | hc'
        · rw [ihp c hnd'.1, hdet]
        · exact ihd c hc'
      · rw [ihp m (fun h => hm (by simp [h])), hop m (fun h => hm (by simp [h]))]

/-! ## step 7 -/

/--
**step 7 で一つずつ入れると、parent の children には reference child の直前に順に並ぶ。**

入れる node はどれも parent を持たず（step 4 と、`insert` を呼ぶ側が外している）、
reference child は parent の子で、入れる列に入っていない。
-/
theorem insertedEach_children {parent doc : NodeId} {child : Option NodeId} :
    ∀ {ns : List NodeId} {s s' : DOMState}, InsertedEach parent child doc s ns s' →
      ns.Nodup → (∀ n ∈ ns, parentOf s.tree n = none) →
      (∀ c, child = some c → c ∉ ns) →
      childrenOf s'.tree parent = insertAllBefore (childrenOf s.tree parent) child ns ∧
        (∀ n ∈ ns, parentOf s'.tree n = some parent) ∧
        (∀ m, m ∉ ns → parentOf s'.tree m = parentOf s.tree m)
  | [], s, s', h, _, _, _ => by
    cases h
    exact ⟨rfl, fun _ h => by simp at h, fun _ _ => rfl⟩
  | n :: ns, s, s', h, hnd, hnp, hc => by
    cases h with
    | cons ha hti hlive hrest =>
      rename_i sa sb
      have hnd' := List.nodup_cons.mp hnd
      have hfa := adoptSpec_frame_of_no_parent ha (hnp n (by simp))
      have hpa : ∀ m, parentOf sb.tree m = if m = n then some parent else parentOf s.tree m := by
        intro m
        by_cases hm : m = n
        · rw [if_pos hm, hm]; exact hti.attached
        · rw [if_neg hm, hti.otherParents m hm, (hfa m).2]
      obtain ⟨ihc, ihn, ihp⟩ := insertedEach_children hrest hnd'.2
        (fun x hx => by
          rw [hpa x, if_neg (fun he : x = n => hnd'.1 (he ▸ hx))]
          exact hnp x (by simp [hx]))
        (fun c hcs hcx => hc c hcs (by simp [hcx]))
      refine ⟨?_, fun x hx => ?_, fun m hm => ?_⟩
      · rw [ihc, hti.children, (hfa parent).1]
        rfl
      · rcases List.mem_cons.mp hx with rfl | hx'
        · rw [ihp x hnd'.1, hpa x, if_pos rfl]
        · exact ihn x hx'
      · rw [ihp m (fun h => hm (by simp [h])), hpa m, if_neg (fun h => hm (by simp [h]))]

/--
**`insert` の後の parent の children。**

node は parent を持たず、parent でなく、reference child は parent の子で node でない。
-/
theorem insertSpec_children {node parent : NodeId} {child : Option NodeId} {b : Bool}
    (hwf : WellFormed s.tree) (h : InsertSpec s node parent child b s')
    (hnp : parentOf s.tree node = none) (hnep : node ≠ parent)
    (hchild : ∀ c, child = some c → parentOf s.tree c = some parent) :
    ∃ nodes, NodesToInsert s.tree node nodes ∧
      childrenOf s'.tree parent = insertAllBefore (childrenOf s.tree parent) child nodes ∧
      ∀ n ∈ nodes, parentOf s'.tree n = some parent := by
  obtain ⟨nodes, hnodes, hcase⟩ := h
  refine ⟨nodes, hnodes, ?_⟩
  rcases hcase with ⟨rfl, rfl⟩ | ⟨hne, s₁, s₂, s₃, idx, prev, pd, hfp, -, -, hra, -, hie, -, hoo⟩
  · exact ⟨by simp [ListUtil.insertAllBefore], fun _ h => by simp at h⟩
  · obtain ⟨d, hd, hnc⟩ := hnodes
    obtain ⟨d', hd', hfpc⟩ := hfp
    rw [hd] at hd'
    cases hd'
    -- step 4 の後：入れる node はどれも parent を持たず、parent の children は変わらない
    have step4 : (∀ m, m ≠ node → childrenOf s₁.tree m = childrenOf s.tree m) ∧
        (∀ c ∈ nodes, parentOf s₁.tree c = none) ∧
        (∀ m, m ∉ nodes → parentOf s₁.tree m = parentOf s.tree m) := by
      by_cases hk : d.kind = NodeKind.documentFragment
      · rw [if_pos hk] at hfpc
        obtain ⟨sr, hre, -, hoo'⟩ := hfpc
        have hns : nodes = d.children := by
          rcases hnc with ⟨-, h⟩ | ⟨hk', -⟩
          · exact h
          · exact absurd hk hk'
        subst hns
        obtain ⟨hc, hd₀, hp⟩ := removeEachSpec_frame (q := node) hre (hwf.children_nodup node d hd)
          (fun c hc => by
            obtain ⟨cd, hcd, hcp⟩ := hwf.parent_child node d hd c hc
            rw [parentOf_eq, hcd]; exact hcp)
        rw [hoo'.tree]
        exact ⟨hc, hd₀, hp⟩
      · rw [if_neg hk] at hfpc
        subst hfpc
        have hns : nodes = [node] := by
          rcases hnc with ⟨hk', -⟩ | ⟨-, h⟩
          · exact absurd hk' hk
          · exact h
        subst hns
        exact ⟨fun _ _ => rfl, fun c hc => by simp at hc; rw [hc]; exact hnp, fun _ _ => rfl⟩
    obtain ⟨hc₁, hd₁, hp₁⟩ := step4
    have ht₂ : s₂.tree = s₁.tree := hra.tree
    -- 入れる列には重複が無く、reference child は入っていない
    have hnd : nodes.Nodup := by
      rcases hnc with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact hwf.children_nodup node d hd
      · simp
    have hcnot : ∀ c, child = some c → c ∉ nodes := by
      intro c hcs hcm
      have hcp := hchild c hcs
      rcases hnc with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · obtain ⟨cd, hcd, hcp'⟩ := hwf.parent_child node d hd c hcm
        simp only [parentOf_eq, hcd, Option.bind_some] at hcp
        rw [hcp'] at hcp
        exact hnep (Option.some.inj hcp)
      · simp at hcm
        rw [hcm, hnp] at hcp
        cases hcp
    obtain ⟨hcE, hpE, -⟩ := insertedEach_children hie hnd
      (fun n hn => by rw [ht₂]; exact hd₁ n hn) hcnot
    refine ⟨?_, fun n hn => by rw [hoo.tree]; exact hpE n hn⟩
    rw [hoo.tree, hcE, ht₂, hc₁ parent (fun he => hnep he.symm)]

/-! ## live range の数 -/

theorem removeSpec_ranges_length {c : NodeId} {b : Bool} (h : RemoveSpec s c b s') :
    s'.ranges.length = s.ranges.length := by
  obtain ⟨p, idx, -, -, hra, -⟩ := h
  exact hra.1

theorem removeEachSpec_ranges_length {b : Bool} : ∀ {ns : List NodeId} {s s' : DOMState},
    RemoveEachSpec s ns b s' → s'.ranges.length = s.ranges.length
  | [], _, _, h => by cases h; rfl
  | _ :: _, _, _, h => by
    cases h with
    | cons hr hrest => rw [removeEachSpec_ranges_length hrest, removeSpec_ranges_length hr]

theorem adoptSpec_ranges_length {node doc : NodeId} (h : AdoptSpec s node doc s') :
    s'.ranges.length = s.ranges.length := by
  obtain ⟨od, -, s₁, hst2, hst3⟩ := h
  have h₁ : s₁.ranges.length = s.ranges.length := by
    rcases hst2 with ⟨-, rfl⟩ | ⟨-, hr⟩
    · rfl
    · exact removeSpec_ranges_length hr
  split at hst3
  · subst hst3; exact h₁
  · rw [hst3.2.ranges, h₁]

theorem insertedEach_ranges_length {parent doc : NodeId} {child : Option NodeId} :
    ∀ {ns : List NodeId} {s s' : DOMState}, InsertedEach parent child doc s ns s' →
      s'.ranges.length = s.ranges.length
  | [], _, _, h => by cases h; rfl
  | _ :: _, _, _, h => by
    cases h with
    | cons ha _ hlive hrest =>
      rw [insertedEach_ranges_length hrest, hlive.ranges, adoptSpec_ranges_length ha]

/-- **`insert` は live range の数を変えない。** -/
theorem insertSpec_ranges_length {node parent : NodeId} {child : Option NodeId} {b : Bool}
    (h : InsertSpec s node parent child b s') : s'.ranges.length = s.ranges.length := by
  obtain ⟨nodes, -, hcase⟩ := h
  rcases hcase with ⟨-, rfl⟩ | ⟨-, s₁, s₂, s₃, idx, prev, pd, hfp, -, -, hra, -, hie, -, hoo⟩
  · rfl
  · have h₁ : s₁.ranges.length = s.ranges.length := by
      obtain ⟨d, -, hfpc⟩ := hfp
      split at hfpc
      · obtain ⟨sr, hre, -, hoo'⟩ := hfpc
        rw [hoo'.ranges, removeEachSpec_ranges_length hre]
      · subst hfpc; rfl
    rw [hoo.ranges, insertedEach_ranges_length hie, hra.length, h₁]

end Dom.Spec
