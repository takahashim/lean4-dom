import Dom.Validity.Structural

/-!
# node document の妥当性

`notes/research-foundation-roadmap.md` §4 の `NodeDocumentsValid`。

`NodeData.ownerDocument` が表しているのは API の `ownerDocument` ではなく、
仕様の **node document** である。両者は Document 自身で食い違う。
API の `document.ownerDocument` は `null` だが、
Document の node document は自分自身だからである。
この module の名前と定理はすべて node document のほうを指す。
-/

namespace Dom

/--
node document の整合性。

* Document の node document は自分自身である。
* 一つの tree edge の両端は同じ node document に属する。
  すなわち adopt を通さずに node document が変わることはない。

「node document が存在して Document である」は `WellFormed.ownerDocument_is_document`
にあるので、ここでは重複させない。
-/
structure NodeDocumentsValid (t : Tree) : Prop where
  documentIsOwnNodeDocument :
    ∀ n d, t.get? n = some d → d.kind = .document → d.ownerDocument = n
  treeEdgePreservesNodeDocument :
    ∀ c p, parentOf t c = some p → ownerDocumentOf t c = ownerDocumentOf t p

namespace NodeDocumentsValid

/-- 親子は同じ node document を持つ。 -/
theorem ownerDocument_eq_of_parentOf {t : Tree} (h : NodeDocumentsValid t) {c p : NodeId}
    (hp : parentOf t c = some p) : ownerDocumentOf t c = ownerDocumentOf t p :=
  h.treeEdgePreservesNodeDocument c p hp

/-- ancestor まで遡っても node document は同じである。 -/
theorem ownerDocument_eq_of_ancestor {t : Tree} (h : NodeDocumentsValid t) {a n : NodeId}
    (hanc : Ancestor t a n) : ownerDocumentOf t n = ownerDocumentOf t a := by
  induction hanc with
  | @step m hp => exact h.ownerDocument_eq_of_parentOf hp
  | @trans m b hp _ ih => exact (h.ownerDocument_eq_of_parentOf hp).trans ih

/-- 同じ木にある node は同じ node document を持つ。 -/
theorem ownerDocument_eq_of_inclusiveAncestor {t : Tree} (h : NodeDocumentsValid t)
    {a n : NodeId} (hanc : InclusiveAncestor t a n) :
    ownerDocumentOf t n = ownerDocumentOf t a := by
  rcases hanc with rfl | hanc
  · rfl
  · exact h.ownerDocument_eq_of_ancestor hanc

/-- Document を root に持つ木の node document は、その Document である。 -/
theorem ownerDocument_of_document_root {t : Tree} (h : NodeDocumentsValid t)
    {doc n : NodeId} {dd : NodeData} (hdd : t.get? doc = some dd) (hk : dd.kind = .document)
    (hanc : InclusiveAncestor t doc n) : ownerDocumentOf t n = some doc := by
  rw [h.ownerDocument_eq_of_inclusiveAncestor hanc]
  simp [ownerDocumentOf_eq, hdd, h.documentIsOwnNodeDocument doc dd hdd hk]

end NodeDocumentsValid

/-! ## 実行時の検査 -/

def checkNodeDocumentsValid (t : Tree) : Bool :=
  t.nodes.checkAll fun n d =>
    (!(d.kind == .document) || d.ownerDocument == n) &&
      (match d.parent with
       | none => true
       | some p => ownerDocumentOf t p == some d.ownerDocument)

theorem checkNodeDocumentsValid_iff (t : Tree) :
    checkNodeDocumentsValid t = true ↔ NodeDocumentsValid t := by
  simp only [checkNodeDocumentsValid, NodeStore.checkAll_iff]
  constructor
  · intro hall
    refine ⟨?_, ?_⟩
    · intro n d hn hk
      have := hall n d hn
      simp only [Bool.and_eq_true, hk] at this
      simpa using this.1
    · intro c p hp
      obtain ⟨cd, hcd, hcdp⟩ := parentOf_eq_some hp
      have := hall c cd hcd
      simp only [Bool.and_eq_true, hcdp] at this
      have h2 : ownerDocumentOf t p = some cd.ownerDocument := by simpa using this.2
      have hc : ownerDocumentOf t c = some cd.ownerDocument := by simp [ownerDocumentOf_eq, hcd]
      rw [hc, h2]
  · intro h n d hn
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne,
      beq_iff_eq]
    refine ⟨?_, ?_⟩
    · by_cases hk : d.kind = NodeKind.document
      · exact Or.inr (h.documentIsOwnNodeDocument n d hn hk)
      · exact Or.inl hk
    · cases hp : d.parent with
      | none => simp
      | some p =>
        have hn' : t.get? n = some d := hn
        have hpar : parentOf t n = some p := by simp [parentOf_eq, hn', hp]
        have hedge := h.treeEdgePreservesNodeDocument n p hpar
        have hself : ownerDocumentOf t n = some d.ownerDocument := by
          simp [ownerDocumentOf_eq, hn']
        rw [hself] at hedge
        simpa using hedge.symm

end Dom
