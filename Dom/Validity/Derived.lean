import Dom.Validity.State
import Dom.Properties.Range
import Dom.Properties.Iterator

/-!
# admissibility から導かれる補助前提

`notes/research-foundation-roadmap.md` §4 の目的は、
Range と Iterator の保存定理を使うたびに **モデル外の前提** を渡さずに済むようにすることである。

これまで `ChildCountKind` と `OtherDocumentIteratorsOutside` は
定理の仮定として外から渡していた。どちらも `AdmissibleDOMState` から導ける。
-/

namespace Dom

/-- children を持てる kind なら、node length は children の個数である。 -/
theorem childCountKind_of_canHaveChildren {t : Tree} {n : NodeId}
    (h : ∀ d, t.get? n = some d → d.kind.canHaveChildren = true) : ChildCountKind t n := by
  intro d hd
  have := h d hd
  cases hk : d.kind <;> rw [hk] at this <;> simp_all [NodeKind.canHaveChildren,
    NodeKind.isCharacterData]

/--
parent になっている node は、必ず children を持てる kind である。

したがって `ChildCountKind` は `parentOf` から出る。
`remove` 系の定理が `hlen : ChildCountKind t p` を要求していたのは、
この事実を invariant として持っていなかったからである。
-/
theorem childCountKind_of_parentOf {t : Tree} (h : StructurallyValid t) {c p : NodeId}
    (hp : parentOf t c = some p) : ChildCountKind t p := by
  refine childCountKind_of_canHaveChildren ?_
  intro d hd
  exact h.canHaveChildren_of_parentOf hp hd

theorem AdmissibleDOMState.childCountKind {s : DOMState} (h : AdmissibleDOMState s)
    {c p : NodeId} (hp : parentOf s.tree c = some p) : ChildCountKind s.tree p :=
  childCountKind_of_parentOf h.structural hp

/--
別の node document に属する iterator は、外す部分木の中を指していない。

`IteratorsValid` から reference は root の inclusive descendant であり、
`n` の inclusive descendant でもあるなら、`inclusive_ancestor_linear` により
`root` と `n` は一方が他方の inclusive ancestor である。
`NodeDocumentsValid` から同じ木の node は同じ node document を持つので、
node document が違うという仮定と矛盾する。
-/
theorem AdmissibleDOMState.otherDocumentIteratorsOutside {s : DOMState}
    (h : AdmissibleDOMState s) (n : NodeId) : OtherDocumentIteratorsOutside s n := by
  intro it hit hne
  cases hb : isInclusiveAncestorOf s.tree n it.reference with
  | false => rfl
  | true =>
    exfalso
    have hanc : InclusiveAncestor s.tree n it.reference :=
      (isInclusiveAncestorOf_iff h.wellFormed n it.reference).mp hb
    have hroot : InclusiveAncestor s.tree it.root it.reference := (h.iterators it hit).2
    refine hne ?_
    rcases inclusive_ancestor_linear hroot hanc with hle | hle
    · exact (h.nodeDocuments.ownerDocument_eq_of_inclusiveAncestor hle).symm
    · exact h.nodeDocuments.ownerDocument_eq_of_inclusiveAncestor hle

end Dom
