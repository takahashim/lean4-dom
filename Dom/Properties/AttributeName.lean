import Dom.Attribute.Algorithms
import Dom.Attribute.Node
import Dom.Properties.Tree

/-!
# 名前の検査と attribute 探索の契約

§1.3 の名前検査と §4.9 の attribute 探索について、差分テストからは出てこない
性質を書く。名前検査どうしの包含と、`findAttr` が返す owner element の整合が中心である。

`splitAtFirstColon` の round-trip（`p ++ ":" ++ l = s`）は
`String.intercalate sep (s.splitOn sep) = s` が要るが、この Lean の標準 library には
無く、Mathlib も使わない方針なので今は書いていない。
-/

namespace Dom

/-! ## `splitAtFirstColon` -/

/-- colon が無ければ分けられない。 -/
theorem splitAtFirstColon_eq_none_iff {s : String} :
    splitAtFirstColon s = none ↔ (s.splitOn ":").length ≤ 1 := by
  unfold splitAtFirstColon
  cases hs : s.splitOn ":" with
  | nil => simp
  | cons a rest =>
    cases rest with
    | nil => simp
    | cons b rest' => simp

/-! ## 名前の検査 -/

/-- 有効な名前は空でない。 -/
theorem not_isEmpty_of_isValidNamespacePrefix {s : String}
    (h : isValidNamespacePrefix s = true) : s.isEmpty = false := by
  unfold isValidNamespacePrefix at h
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  exact h.1

theorem not_isEmpty_of_isValidAttributeLocalName {s : String}
    (h : isValidAttributeLocalName s = true) : s.isEmpty = false := by
  unfold isValidAttributeLocalName at h
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  exact h.1

/--
**valid attribute local name は valid namespace prefix でもある。**

前者は後者の条件に `=` を加えたものなので、条件は狭い。
二つを別々に書き下しているので、この包含は定理で押さえておく。
-/
theorem isValidNamespacePrefix_of_isValidAttributeLocalName {s : String}
    (h : isValidAttributeLocalName s = true) : isValidNamespacePrefix s = true := by
  unfold isValidAttributeLocalName at h
  unfold isValidNamespacePrefix
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h ⊢
  refine ⟨h.1, ?_⟩
  refine List.all_eq_true.mpr fun c hc => ?_
  have := List.all_eq_true.mp h.2 c hc
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this ⊢
  exact ⟨this.1.1, this.2⟩

/-! ## §4.9 の attribute 探索 -/

/-- `getAttributeValue` は見つかった attribute の値、無ければ空文字列である。 -/
theorem getAttributeValue_eq (d : NodeData) (ns : Option String) (ln : String) :
    getAttributeValue d ns ln =
      match getAttributeByKey d ns ln with
      | none => ""
      | some a => a.value := rfl

/-- **`findAttr` が owner element を返したなら、その element は本当にその attribute を持つ。** -/
theorem findAttr_owner {s : DOMState} {aid : AttrId} {a : Attr} {n : NodeId}
    (h : findAttr s aid = some (a, some n)) :
    ∃ d, s.tree.get? n = some d ∧ a ∈ d.attributes ∧ a.id = aid := by
  unfold findAttr at h
  cases ho : ownerElementOf s.tree aid with
  | none =>
    simp only [ho] at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨x, -, hx⟩ := h
    simp at hx
  | some m =>
    simp only [ho] at h
    cases hd : s.tree.get? m with
    | none => rw [hd] at h; simp at h
    | some d =>
      rw [hd] at h
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨x, hx, hax, hnm⟩ := h
      refine ⟨d, ?_, ?_, ?_⟩
      · rw [← Option.some.inj hnm]; exact hd
      · rw [← hax]; exact List.mem_of_find?_eq_some hx
      · rw [← hax]; simpa using List.find?_eq_some_iff_getElem.mp hx |>.1

/-- **`findAttr` が owner element を返さなかったなら、attribute は detach 側にある。** -/
theorem findAttr_detached {s : DOMState} {aid : AttrId} {a : Attr}
    (h : findAttr s aid = some (a, none)) : a ∈ s.detachedAttrs ∧ a.id = aid := by
  unfold findAttr at h
  cases ho : ownerElementOf s.tree aid with
  | some m =>
    simp only [ho] at h
    cases hd : s.tree.get? m with
    | none => rw [hd] at h; simp at h
    | some d =>
      rw [hd] at h
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨-, -, -, hnm⟩ := h
      simp at hnm
  | none =>
    simp only [ho] at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨x, hx, hax⟩ := h
    have hax' : x = a := by
      have := congrArg Prod.fst hax
      simpa using this
    subst hax'
    exact ⟨List.mem_of_find?_eq_some hx, by simpa using List.find?_eq_some_iff_getElem.mp hx |>.1⟩

end Dom
