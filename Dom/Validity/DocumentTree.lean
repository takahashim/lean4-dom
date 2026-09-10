import Dom.Validity.NodeDocument
import Dom.Mutation.Algorithms

/-!
# document tree の妥当性

`notes/research-foundation-roadmap.md` §4 の `DocumentTreesValid`。

Document の children には仕様上の制約がある（§4.2.3 "ensure pre-insertion validity" step 6）。
これまで model はこの制約を **API 境界の検査** としてしか持っておらず、
状態の invariant として述べていなかった。ここで invariant にする。

制約は Document の children についてだけのものなので、
`Document` 以外の kind については何も言わない。
-/

namespace Dom

/--
Document の children の並びが仕様の制約を満たすか。

* element の子は高々一つ。
* doctype の子は高々一つ。
* Text の子は無い。
* doctype は document element より前にある。

四つ目は「doctype の後ろに element が無い」ではなく
「element の後ろに doctype が無い」として述べる。
仕様の step 6 が `doctypeFollows`（child より後ろに doctype があるか）で
判定しているのと同じ向きである。
-/
def DocumentChildrenOk (t : Tree) (doc : NodeId) : Prop :=
  (elementChildren t doc).length ≤ 1 ∧
    (doctypeChildren t doc).length ≤ 1 ∧
    textChildren t doc = [] ∧
    ∀ e ∈ elementChildren t doc, doctypeFollows t doc e = false

structure DocumentTreesValid (t : Tree) : Prop where
  documentChildren : ∀ doc d, t.get? doc = some d → d.kind = .document → DocumentChildrenOk t doc

/-! ## 実行時の検査 -/

def checkDocumentChildrenOk (t : Tree) (doc : NodeId) : Bool :=
  (elementChildren t doc).length ≤ 1 &&
    (doctypeChildren t doc).length ≤ 1 &&
    (textChildren t doc).isEmpty &&
    (elementChildren t doc).all fun e => !doctypeFollows t doc e

theorem checkDocumentChildrenOk_iff (t : Tree) (doc : NodeId) :
    checkDocumentChildrenOk t doc = true ↔ DocumentChildrenOk t doc := by
  simp only [checkDocumentChildrenOk, DocumentChildrenOk, Bool.and_eq_true,
    decide_eq_true_eq, List.isEmpty_iff, List.all_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩

def checkDocumentTreesValid (t : Tree) : Bool :=
  t.nodes.checkAll fun n d => !(d.kind == .document) || checkDocumentChildrenOk t n

theorem checkDocumentTreesValid_iff (t : Tree) :
    checkDocumentTreesValid t = true ↔ DocumentTreesValid t := by
  simp only [checkDocumentTreesValid, NodeStore.checkAll_iff]
  constructor
  · intro hall
    refine ⟨fun doc d hdoc hk => ?_⟩
    have := hall doc d hdoc
    simp only [hk, Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at this
    rcases this with hne | hok
    · exact absurd rfl hne
    · exact (checkDocumentChildrenOk_iff t doc).mp hok
  · intro h n d hn
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne]
    by_cases hk : d.kind = NodeKind.document
    · exact Or.inr ((checkDocumentChildrenOk_iff t n).mpr (h.documentChildren n d hn hk))
    · exact Or.inl hk

end Dom
