import Dom.Spec.SelectorMatch
import Dom.Query.Lookup

/-!
# id・class・name で引く method の関係仕様

`Dom/Query/Lookup.lean` の三つの method が返すものを、実行関数の道具（`preorder`・
`splitWsAux`・`plainAttr`）を使わずに仕様の語彙で言い、実行関数がそれに一致することを示す。

| 関係 | 本文 |
| --- | --- |
| `HasId` | DOM §4.9 の element の ID。namespace の無い `id` attribute の値で、空でない |
| `HasClass` | DOM §4.9 の element の classes。`class` attribute の値に空白区切りの語として現れる |
| `ClassToken s c` | ordered set parser が `s` から読む語に `c` がある（`Dom/Spec/SelectorMatch.lean`） |
| `ClassIdMatches` | quirks mode なら ASCII case-insensitive、そうでなければ identical（同上） |

`getElementById()` が tree order で **最初の** element を返すことは `List.find?` そのものなので、
ここでは当たるものを返すこと（`getElementById_eq_some`）と、無ければ null（`getElementById_eq_none_iff`）
だけを述べる。
-/

namespace Dom.Spec

open Dom Selectors Infra

/-- DOM §4.9 の element の ID が `i` である。 -/
def HasId (t : Tree) (e : NodeId) (i : String) : Prop :=
  i ≠ "" ∧ ∃ d, t.get? e = some d ∧ PlainAttrValue d "id" i

/-- DOM §4.9 の element の classes に `c` がある。 -/
def HasClass (t : Tree) (e : NodeId) (c : String) : Prop :=
  ∃ d, t.get? e = some d ∧ ∃ av, PlainAttrValue d "class" av ∧ ClassToken av c

theorem mem_descendantElements_iff {t : Tree} (hwf : WellFormed t) {node : NodeId}
    {d : NodeData} (hn : t.get? node = some d) (e : NodeId) :
    e ∈ descendantElements t node ↔ Descendant t e node ∧ isElementNode t e = true := by
  simp only [descendantElements, List.mem_filter, mem_preorder_iff hwf hn, Bool.and_eq_true,
    bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨hin, hne, hel⟩
    rcases hin with heq | hanc
    · exact absurd heq.symm hne
    · exact ⟨hanc, hel⟩
  · rintro ⟨hanc, hel⟩
    refine ⟨Or.inr hanc, fun heq => ?_, hel⟩
    rw [heq] at hanc
    exact absurd hanc (ancestor_irrefl hwf _)

/-- **ordered set parser が読む語は、空白区切りの語にちょうど当たる。** 重複を落としても変わらない。 -/
theorem mem_orderedSetParse_iff (s c : String) : c ∈ orderedSetParse s ↔ ClassToken s c := by
  rw [← classWord_iff, orderedSetParse, List.mem_eraseDups, List.mem_map, List.any_eq_true]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, by simp⟩
  · rintro ⟨w, hw, heq⟩
    have heq : w = c.toList := by simpa using heq
    subst heq
    exact ⟨c.toList, hw, by simp⟩

theorem elementIdOf_eq_some_iff {t : Tree} (hav : AttributesValid t) (e : NodeId) (i : String) :
    elementIdOf t e = some i ↔ HasId t e i := by
  unfold elementIdOf HasId
  cases hd : t.get? e with
  | none => simp
  | some d =>
    simp only [Option.some.injEq, exists_eq_left']
    rw [← plainAttr_eq_some_iff (hav.keysNodup e d hd)]
    cases hp : plainAttr d "id" with
    | none => simp
    | some v =>
      by_cases hv : v.isEmpty
      · have : v = "" := by simpa using hv
        subst this
        simp
      · have : v ≠ "" := by simpa using hv
        simp only [hv, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, ne_eq]
        constructor
        · rintro rfl; exact ⟨this, rfl⟩
        · rintro ⟨-, rfl⟩; rfl

theorem mem_elementClassesOf_iff {t : Tree} (hav : AttributesValid t) (e : NodeId) (c : String) :
    c ∈ elementClassesOf t e ↔ HasClass t e c := by
  unfold elementClassesOf HasClass
  cases hd : t.get? e with
  | none => simp
  | some d =>
    simp only [Option.some.injEq, exists_eq_left']
    cases hp : plainAttr d "class" with
    | none =>
      simp only [List.not_mem_nil, false_iff, not_exists, not_and]
      intro av hav'
      rw [← plainAttr_eq_some_iff (hav.keysNodup e d hd)] at hav'
      simp [hp] at hav'
    | some v =>
      rw [mem_orderedSetParse_iff]
      constructor
      · intro h
        exact ⟨v, (plainAttr_eq_some_iff (hav.keysNodup e d hd) _ _).mp hp, h⟩
      · rintro ⟨av, hav', h⟩
        rw [← plainAttr_eq_some_iff (hav.keysNodup e d hd), hp] at hav'
        cases hav'
        exact h

/-! ## `getElementById()` -/

/-- **Document か DocumentFragment なら、当たる element を返す。** -/
theorem getElementById_eq_some {t : Tree} (hwf : WellFormed t) (hav : AttributesValid t)
    {node e : NodeId} {i : String} {d : NodeData} (hn : t.get? node = some d)
    (h : getElementById t node i = .ok (some e)) :
    Descendant t e node ∧ isElementNode t e = true ∧ HasId t e i := by
  unfold getElementById at h
  split at h
  · cases h
  · simp only [Except.ok.injEq] at h
    have hmem := List.mem_of_find?_eq_some h
    have hid := List.find?_some h
    rw [mem_descendantElements_iff hwf hn] at hmem
    exact ⟨hmem.1, hmem.2, (elementIdOf_eq_some_iff hav e i).mp (by simpa using hid)⟩

/-- **null になるのは、ID が `i` である descendant の element が無いときだけ。** -/
theorem getElementById_eq_none_iff {t : Tree} (hwf : WellFormed t) (hav : AttributesValid t)
    {node : NodeId} {i : String} {d : NodeData} (hn : t.get? node = some d)
    (hk : d.kind = .document ∨ d.kind = .documentFragment) :
    getElementById t node i = .ok none ↔
      ∀ e, Descendant t e node → isElementNode t e = true → ¬ HasId t e i := by
  have hreq : requireNonElementParentNode t node = .ok () := by
    unfold requireNonElementParentNode
    rcases hk with hk | hk <;> simp [hn, hk]
  simp only [getElementById, hreq, Except.ok.injEq, List.find?_eq_none, beq_iff_eq,
    elementIdOf_eq_some_iff hav, mem_descendantElements_iff hwf hn, and_imp]

/-- **TypeError になるのは、Document でも DocumentFragment でもないときだけ。** -/
theorem getElementById_error_iff {t : Tree} {node : NodeId} {i : String} {d : NodeData}
    (hn : t.get? node = some d) :
    (∃ ex, getElementById t node i = .error ex) ↔
      ¬ (d.kind = .document ∨ d.kind = .documentFragment) := by
  unfold getElementById requireNonElementParentNode
  by_cases hk : d.kind = .document ∨ d.kind = .documentFragment
  · rcases hk with hk | hk <;> simp [hn, hk]
  · simp only [not_or] at hk
    simp [hn, hk.1, hk.2]

/-! ## `getElementsByClassName()` -/

/--
**Document か Element なら、`classNames` の語をすべて classes に持つ descendant の element を返す。**
語が一つも無ければ何も返さない。語と class の比較は、受け手の node document が quirks mode なら
ASCII case-insensitive である（`ClassIdMatches`）。
-/
theorem mem_getElementsByClassName_iff {t : Tree} (hwf : WellFormed t) (hav : AttributesValid t)
    {node : NodeId} {s : String} {d : NodeData} (hn : t.get? node = some d)
    (hk : d.kind = .document ∨ d.kind = .element) :
    ∃ l, getElementsByClassName t node s = .ok l ∧ ∀ e, e ∈ l ↔
      Descendant t e node ∧ isElementNode t e = true ∧
        (∃ c, ClassToken s c) ∧
          ∀ c, ClassToken s c → ∃ c', HasClass t e c' ∧ ClassIdMatches t d c' c := by
  have hreq : requireDocumentOrElement t node = .ok () := by
    unfold requireDocumentOrElement
    rcases hk with hk | hk <;> simp [hn, hk]
  simp only [getElementsByClassName, hreq]
  by_cases hemp : (orderedSetParse s).isEmpty
  · refine ⟨[], by simp [hemp], fun e => ?_⟩
    have : orderedSetParse s = [] := List.isEmpty_iff.mp hemp
    simp only [List.not_mem_nil, false_iff, not_and]
    intro _ _ ⟨c, hc⟩
    rw [← mem_orderedSetParse_iff, this] at hc
    cases hc
  · refine ⟨_, by simp [hemp]; rfl, fun e => ?_⟩
    rw [List.mem_filter, mem_descendantElements_iff hwf hn, List.all_eq_true]
    have hq : receiverInQuirksMode t node = inQuirksModeOf t d := by
      simp [receiverInQuirksMode, hn]
    simp only [hq, List.any_eq_true, quirksFold_eq_iff, mem_elementClassesOf_iff hav,
      mem_orderedSetParse_iff]
    constructor
    · rintro ⟨⟨hd, hel⟩, hall⟩
      obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ (by simpa using hemp)
      exact ⟨hd, hel, ⟨c, (mem_orderedSetParse_iff s c).mp hc⟩, hall⟩
    · rintro ⟨hd, hel, -, hall⟩
      exact ⟨⟨hd, hel⟩, hall⟩

/-! ## `getElementsByName()` -/

/--
**Document なら、HTML element で namespace の無い `name` attribute の値が `n` の descendant を返す。**
-/
theorem mem_getElementsByName_iff {t : Tree} (hwf : WellFormed t) (hav : AttributesValid t)
    {node : NodeId} {n : String} {d : NodeData} (hn : t.get? node = some d)
    (hk : d.kind = .document) :
    ∃ l, getElementsByName t node n = .ok l ∧ ∀ e, e ∈ l ↔
      Descendant t e node ∧ isElementNode t e = true ∧
        ∃ de, t.get? e = some de ∧ de.namespace = some htmlNamespace ∧
          PlainAttrValue de "name" n := by
  have hreq : ∃ x, requireDocument t node = .ok x := by
    unfold requireDocument
    simp [hn, hk]
  obtain ⟨x, hx⟩ := hreq
  simp only [getElementsByName, hx]
  refine ⟨_, rfl, fun e => ?_⟩
  rw [List.mem_filter, mem_descendantElements_iff hwf hn, and_assoc]
  apply and_congr_right; intro _; apply and_congr_right; intro _
  cases he : t.get? e with
  | none => simp
  | some de =>
    simp only [Option.some.injEq, exists_eq_left', Bool.and_eq_true, beq_iff_eq,
      plainAttr_eq_some_iff (hav.keysNodup e de he)]

end Dom.Spec
