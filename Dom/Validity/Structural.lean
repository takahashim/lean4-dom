import Dom.Properties.Tree

/-!
# 構造上の妥当性

`WellFormed`（parent と children の整合、children の重複禁止、非循環性、
node document が Document であること）に、**kind から来る構造制約** を重ねる。

`notes/research-foundation-roadmap.md` §4 の `StructurallyValid` である。
`WellFormed` は一般的な木の整合性なのでそのまま残し、
DOM 固有の妥当性はこの層から上に足していく。
-/

namespace Dom

/--
kind から決まる構造制約。

* Document は parent を持たない（tree order の root であるため）。
* DocumentFragment も parent を持たない。`insert` は step 1 で fragment を
  children に展開するので、fragment 自身が誰かの子になることは無い。
  仕様は「fragment は tree の root である」と直接は書いていないが、
  §4.2.3 の insert がそう保つ。`replace` の step 10 の assertion
  （addedNodes と removedNodes のどちらかは空でない）はこれに依存する。
* children を持てるのは Document / DocumentFragment / Element だけである
  （§4.2.3 "ensure pre-insertion validity" step 1 が parent に許す種別）。
  したがって CharacterData と DocumentType の children は常に空である。
* DocumentType の parent は Document だけである（同 step 5）。

三つ目は `notes/research-foundation-roadmap.md` §4 の一覧には無かったが、
`insert` が `DocumentTreesValid` を保つことの証明に要る。
これが無いと「doctype を子に持つ DocumentFragment」が admissible になり、
それを Document に入れると doctype が document element より後ろに来てしまう。
仕様は step 5 で毎回この状態を防いでいるので、局所不変条件として正しい。
-/
structure StructurallyValid (t : Tree) : Prop where
  wellFormed : WellFormed t
  documentHasNoParent : ∀ n d, t.get? n = some d → d.kind = .document → d.parent = none
  fragmentHasNoParent :
    ∀ n d, t.get? n = some d → d.kind = .documentFragment → d.parent = none
  childrenOnlyUnderContainers :
    ∀ n d, t.get? n = some d → d.children ≠ [] → d.kind.canHaveChildren = true
  doctypeParentIsDocument :
    ∀ n d, t.get? n = some d → d.kind = .documentType →
      ∀ p, d.parent = some p → ∀ pd, t.get? p = some pd → pd.kind = .document

namespace StructurallyValid

/-- leaf の children は空である。`childrenOnlyUnderContainers` の対偶。 -/
theorem children_eq_nil {t : Tree} (h : StructurallyValid t) {n : NodeId} {d : NodeData}
    (hn : t.get? n = some d) (hk : d.kind.canHaveChildren = false) : d.children = [] := by
  by_cases hc : d.children = []
  · exact hc
  · exact absurd (h.childrenOnlyUnderContainers n d hn hc) (by rw [hk]; simp)

/-- leaf は parent になれない。 -/
theorem canHaveChildren_of_parentOf {t : Tree} (h : StructurallyValid t) {c p : NodeId}
    {pd : NodeData} (hp : parentOf t c = some p) (hpd : t.get? p = some pd) :
    pd.kind.canHaveChildren = true := by
  refine h.childrenOnlyUnderContainers p pd hpd ?_
  intro hnil
  obtain ⟨cd, hcd, hcdp⟩ := parentOf_eq_some hp
  obtain ⟨pd', hpd', hmem⟩ := h.wellFormed.child_parent c cd p hcd hcdp
  rw [hpd] at hpd'
  cases hpd'
  rw [hnil] at hmem
  simp at hmem

/-- Document は root である。 -/
theorem parentOf_document {t : Tree} (h : StructurallyValid t) {n : NodeId} {d : NodeData}
    (hn : t.get? n = some d) (hk : d.kind = .document) : parentOf t n = none := by
  simp [parentOf, hn, h.documentHasNoParent n d hn hk]

end StructurallyValid

/-! ## 実行時の検査 -/

def checkStructurallyValid (t : Tree) : Bool :=
  t.checkWellFormed &&
    t.nodes.checkAll fun _ d =>
      (!(d.kind == .document) || d.parent.isNone) &&
        (!(d.kind == .documentFragment) || d.parent.isNone) &&
        (d.children.isEmpty || d.kind.canHaveChildren) &&
        (!(d.kind == .documentType) ||
          (match d.parent with
           | none => true
           | some p => kindOf t p == some .document))

theorem checkStructurallyValid_iff (t : Tree) :
    checkStructurallyValid t = true ↔ StructurallyValid t := by
  simp only [checkStructurallyValid, Bool.and_eq_true, checkWellFormed_iff,
    NodeStore.checkAll_iff]
  constructor
  · rintro ⟨hwf, hall⟩
    refine ⟨hwf, ?_, ?_, ?_, ?_⟩
    · intro n d hn hk
      have := hall n d hn
      simp only [hk] at this
      simpa using this.1.1.1
    · intro n d hn hk
      have := hall n d hn
      simp only [hk] at this
      simpa using this.1.1.2
    · intro n d hn hc
      have := hall n d hn
      simp only [Bool.or_eq_true] at this
      rcases this.1.2 with he | hk
      · exact absurd (List.isEmpty_iff.mp he) hc
      · exact hk
    · intro n d hn hk p hp pd hpd
      have := hall n d hn
      simp only [hk] at this
      have h2 := this.2
      simp only [hp] at h2
      simpa [kindOf, hpd] using h2
  · intro h
    refine ⟨h.wellFormed, ?_⟩
    intro n d hn
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · by_cases hk : d.kind = NodeKind.document
      · exact Or.inr (by simp [h.documentHasNoParent n d hn hk])
      · exact Or.inl (by simpa using hk)
    · by_cases hk : d.kind = NodeKind.documentFragment
      · exact Or.inr (by simp [h.fragmentHasNoParent n d hn hk])
      · exact Or.inl (by simpa using hk)
    · by_cases hc : d.children = []
      · exact Or.inl (by simp [hc])
      · exact Or.inr (h.childrenOnlyUnderContainers n d hn hc)
    · by_cases hk : d.kind = NodeKind.documentType
      · refine Or.inr ?_
        cases hp : d.parent with
        | none => simp
        | some p =>
          cases hpd : t.get? p with
          | none =>
            exfalso
            obtain ⟨pd', hpd', _⟩ := h.wellFormed.child_parent n d p hn hp
            rw [hpd] at hpd'; simp at hpd'
          | some pd =>
            simp [kindOf, hpd, h.doctypeParentIsDocument n d hn hk p hp pd hpd]
      · exact Or.inl (by simpa using hk)

end Dom
