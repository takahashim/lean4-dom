import Dom.Spec.Lookup
import Dom.Spec.TreeOrder

/-!
# lookup が返す element の順序（§4.2.6、§4.5、§4.9、HTML §3.1.5）

`Dom/Spec/Lookup.lean` は、id・class・name で引く method が **どの** element を返すかを述べる。ここでは
それに tree order を足す。

* `getElementById()` は、当たる element のうち tree order で **最初の** ものを返す（`getElementById_first`）。
* `getElementsByClassName()`・`getElementsByName()`・`getElementsByTagName()`・`getElementsByTagNameNS()` の
  列は tree order に並ぶ（`..._sorted`）。当たる element の集まりが決まれば、tree order に並んだ列は一つしか無い
  （`Dom.ListUtil.eq_of_pairwise_of_mem_iff`）ので、列そのものが関係で決まる。

`getElementsByTagName()` と `getElementsByTagNameNS()` は、当たる element を本文の
"list of elements with qualified name"・"list of elements with namespace and local name" の語彙で書いた
（`mem_getElementsByTagName_iff`・`mem_getElementsByTagNameNS_iff`）。
-/

namespace Dom.Spec

open Dom Selectors Infra

theorem descendantElements_sorted {t : Tree} (hwf : WellFormed t) {node : NodeId} {d : NodeData}
    (hn : t.get? node = some d) : (descendantElements t node).Pairwise (PrecedesStruct t) :=
  (treeOrderList_preorder hwf hn).2.filter _

theorem descendantElements_inclusive {t : Tree} (hwf : WellFormed t) {node : NodeId}
    {d : NodeData} (hn : t.get? node = some d) :
    ∀ e ∈ descendantElements t node, InclusiveDescendant t e node :=
  fun e he => Or.inr ((mem_descendantElements_iff hwf hn e).mp he).1

/-- **`getElementById()` は、当たる descendant の element のうち tree order で最初のものを返す。** -/
theorem getElementById_first {t : Tree} (hwf : WellFormed t) (hav : AttributesValid t)
    {node e : NodeId} {i : String} {d : NodeData} (hn : t.get? node = some d)
    (h : getElementById t node i = .ok (some e)) :
    ∀ e', Descendant t e' node → isElementNode t e' = true → HasId t e' i →
      ¬ PrecedesStruct t e' e := by
  unfold getElementById at h
  split at h
  · cases h
  · simp only [Except.ok.injEq] at h
    obtain ⟨-, -, hfirst⟩ := find?_first_of_sorted hwf hn (descendantElements_inclusive hwf hn)
      (descendantElements_sorted hwf hn) h
    intro e' hd hel hid
    exact hfirst e' ((mem_descendantElements_iff hwf hn e').mpr ⟨hd, hel⟩)
      (by simpa using (elementIdOf_eq_some_iff hav e' i).mpr hid)

theorem getElementsByClassName_sorted {t : Tree} (hwf : WellFormed t) {node : NodeId}
    {s : String} {d : NodeData} (hn : t.get? node = some d) {l : List NodeId}
    (h : getElementsByClassName t node s = .ok l) : l.Pairwise (PrecedesStruct t) := by
  unfold getElementsByClassName at h
  split at h
  · cases h
  · simp only at h
    split at h
    · cases h; exact List.Pairwise.nil
    · cases h; exact (descendantElements_sorted hwf hn).filter _

theorem getElementsByName_sorted {t : Tree} (hwf : WellFormed t) {node : NodeId}
    {n : String} {d : NodeData} (hn : t.get? node = some d) {l : List NodeId}
    (h : getElementsByName t node n = .ok l) : l.Pairwise (PrecedesStruct t) := by
  unfold getElementsByName at h
  split at h
  · cases h
  · cases h; exact (descendantElements_sorted hwf hn).filter _

theorem getElementsByTagName_sorted {t : Tree} (hwf : WellFormed t) {node : NodeId}
    {q : String} {d : NodeData} (hn : t.get? node = some d) {l : List NodeId}
    (h : getElementsByTagName t node q = .ok l) : l.Pairwise (PrecedesStruct t) := by
  unfold getElementsByTagName at h
  split at h
  · cases h
  · split at h
    · cases h; exact descendantElements_sorted hwf hn
    · cases h; exact (descendantElements_sorted hwf hn).filter _

theorem getElementsByTagNameNS_sorted {t : Tree} (hwf : WellFormed t) {node : NodeId}
    {ns : Option String} {ln : String} {d : NodeData} (hn : t.get? node = some d)
    {l : List NodeId} (h : getElementsByTagNameNS t node ns ln = .ok l) :
    l.Pairwise (PrecedesStruct t) := by
  unfold getElementsByTagNameNS at h
  split at h
  · cases h
  · cases h; exact (descendantElements_sorted hwf hn).filter _

/-! ## list of elements with qualified name / namespace and local name -/

/--
§4.2.6 "list of elements with qualified name" の条件。`*` なら何でも当たる。root の node document が
HTML document なら、HTML namespace の element は qualified name が `q` の ASCII lowercase と、
それ以外の element は qualified name が `q` と等しいものが当たる。そうでなければ qualified name が `q`。
-/
def QualifiedNameMatches (t : Tree) (root : NodeData) (q : String) (ed : NodeData) : Prop :=
  q = "*" ∨
    ((∃ doc, t.get? root.ownerDocument = some doc ∧ doc.isHTMLDocument = true) ∧
        ((ed.namespace = some htmlNamespace ∧ ed.qualifiedName = asciiLowercase q) ∨
          (ed.namespace ≠ some htmlNamespace ∧ ed.qualifiedName = q))) ∨
    ((¬ ∃ doc, t.get? root.ownerDocument = some doc ∧ doc.isHTMLDocument = true) ∧
        ed.qualifiedName = q)

/--
§4.2.6 "list of elements with namespace and local name" の条件。空文字列の namespace は null。
`*` は namespace でも local name でも何でも当たる。
-/
def NamespaceLocalNameMatches (ns : Option String) (ln : String) (ed : NodeData) : Prop :=
  (normalizeNamespace ns = some "*" ∨ ed.namespace = normalizeNamespace ns) ∧
    (ln = "*" ∨ ed.localName = ln)

theorem isHTMLDocumentOf_iff (t : Tree) (d : NodeData) :
    isHTMLDocumentOf t d = true ↔ ∃ doc, t.get? d.ownerDocument = some doc ∧ doc.isHTMLDocument = true := by
  unfold isHTMLDocumentOf
  cases h : t.get? d.ownerDocument <;> simp

/-- **`getElementsByTagName()` は "list of elements with qualified name" の element を返す。** -/
theorem mem_getElementsByTagName_iff {t : Tree} (hwf : WellFormed t) {node : NodeId} {q : String}
    {d : NodeData} (hn : t.get? node = some d) (hk : d.kind = .document ∨ d.kind = .element) :
    ∃ l, getElementsByTagName t node q = .ok l ∧ ∀ e, e ∈ l ↔
      Descendant t e node ∧ isElementNode t e = true ∧
        ∃ ed, t.get? e = some ed ∧ QualifiedNameMatches t d q ed := by
  have hreq : requireDocumentOrElement t node = .ok () := by
    unfold requireDocumentOrElement
    rcases hk with hk | hk <;> simp [hn, hk]
  have hel : ∀ e, isElementNode t e = true → ∃ ed, t.get? e = some ed := by
    intro e he
    unfold isElementNode kindOf at he
    cases h : t.get? e <;> simp_all
  unfold getElementsByTagName
  rw [hreq]
  simp only [hn]
  by_cases hstar : q = "*"
  · refine ⟨_, by simp [hstar]; rfl, fun e => ?_⟩
    rw [mem_descendantElements_iff hwf hn]
    constructor
    · rintro ⟨hd, he⟩
      obtain ⟨ed, hed⟩ := hel e he
      exact ⟨hd, he, ed, hed, Or.inl hstar⟩
    · rintro ⟨hd, he, -⟩; exact ⟨hd, he⟩
  · refine ⟨_, by simp [hstar]; rfl, fun e => ?_⟩
    rw [List.mem_filter, mem_descendantElements_iff hwf hn]
    unfold QualifiedNameMatches
    have hhtml := isHTMLDocumentOf_iff t d
    constructor
    · rintro ⟨⟨hd, he⟩, hm⟩
      obtain ⟨ed, hed⟩ := hel e he
      refine ⟨hd, he, ed, hed, Or.inr ?_⟩
      rw [hed] at hm
      by_cases hh : isHTMLDocumentOf t d = true
      · simp only [hh, if_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne,
          ne_eq] at hm
        exact Or.inl ⟨hhtml.mp hh, hm⟩
      · have hh' : isHTMLDocumentOf t d = false := by simpa using hh
        simp only [hh', Bool.false_eq_true, if_false, beq_iff_eq] at hm
        exact Or.inr ⟨fun hx => hh (hhtml.mpr hx), hm⟩
    · rintro ⟨hd, he, ed, hed, hm⟩
      refine ⟨⟨hd, he⟩, ?_⟩
      rw [hed]
      rcases hm with hm | ⟨hx, hm⟩ | ⟨hx, hm⟩
      · exact absurd hm hstar
      · have hh := hhtml.mpr hx
        simp only [hh, if_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
        exact hm
      · have hh : isHTMLDocumentOf t d = false := by
          cases hb : isHTMLDocumentOf t d
          · rfl
          · exact absurd (hhtml.mp hb) hx
        simp only [hh, Bool.false_eq_true, if_false, beq_iff_eq]
        exact hm

/-- **`getElementsByTagNameNS()` は "list of elements with namespace and local name" の element を返す。** -/
theorem mem_getElementsByTagNameNS_iff {t : Tree} (hwf : WellFormed t) {node : NodeId}
    {ns : Option String} {ln : String} {d : NodeData} (hn : t.get? node = some d)
    (hk : d.kind = .document ∨ d.kind = .element) :
    ∃ l, getElementsByTagNameNS t node ns ln = .ok l ∧ ∀ e, e ∈ l ↔
      Descendant t e node ∧ isElementNode t e = true ∧
        ∃ ed, t.get? e = some ed ∧ NamespaceLocalNameMatches ns ln ed := by
  have hreq : requireDocumentOrElement t node = .ok () := by
    unfold requireDocumentOrElement
    rcases hk with hk | hk <;> simp [hn, hk]
  unfold getElementsByTagNameNS
  rw [hreq]
  refine ⟨_, rfl, fun e => ?_⟩
  rw [List.mem_filter, mem_descendantElements_iff hwf hn]
  unfold NamespaceLocalNameMatches
  constructor
  · rintro ⟨⟨hd, he⟩, hm⟩
    cases hed : t.get? e with
    | none => rw [hed] at hm; cases hm
    | some ed =>
      rw [hed] at hm
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hm
      exact ⟨hd, he, ed, rfl, hm.1, hm.2⟩
  · rintro ⟨hd, he, ed, hed, hm1, hm2⟩
    refine ⟨⟨hd, he⟩, ?_⟩
    rw [hed]
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
    exact ⟨hm1, hm2⟩

end Dom.Spec
