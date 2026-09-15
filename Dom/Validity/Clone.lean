import Dom.Mutation.Clone
import Dom.Validity.Create
import Dom.Validity.Admissible

/-!
# clone しても妥当性は保たれる

`cloneNode` は §4.5 の factory（`withFresh`）と §4.2.3 の `append` しか呼ばない。
どちらも妥当性を保つことが既に示してあるので、保存はその合成である。

`withFresh` の側で要る `FreshNodeData` は、原本の node data から出る。
attribute は写すので `AttributesValid` の三条件を原本から引き継ぎ、
node document は Document の copy なら自分自身、それ以外なら引数の document である。
-/

namespace Dom

/-- step 4 は妥当性を保ち、木の形も変えない。 -/
theorem admissible_cloneAppend {s s' : DOMState} {copy : NodeId} {parent : Option NodeId}
    (hv : AdmissibleDOMState s) (h : cloneAppend s copy parent = .ok s') :
    AdmissibleDOMState s' ∧ ShapePreserving s.tree s'.tree := by
  unfold cloneAppend at h
  split at h
  · rw [← Except.ok.inj h]; exact ⟨hv, ShapePreserving.refl _⟩
  · exact ⟨admissible_append hv h, shapePreserving_append h⟩

/-- copy の node data は `FreshNodeData` を満たす。 -/
theorem freshNodeData_cloneData {s : DOMState} {n doc : NodeId} {d : NodeData}
    (hv : AdmissibleDOMState s) (hd : s.tree.get? n = some d) (hdoc : IsDocument s.tree doc) :
    FreshNodeData s.tree (freshId s.tree)
      (cloneData d (cloneDocumentOf d doc (freshId s.tree))) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro hk
    simp only [cloneData_attributes]
    exact hv.attributes.onlyElements n d hd (by simpa using hk)
  · simpa using hv.attributes.keysNodup n d hd
  · simpa using hv.attributes.prefixHasNamespace n d hd
  · by_cases hkd : d.kind = .document
    · exact Or.inl ⟨by simpa using hkd, by simp [cloneDocumentOf, hkd]⟩
    · refine Or.inr ⟨by simpa using hkd, ?_⟩
      simpa [cloneDocumentOf, hkd] using hdoc

/-- **clone しても妥当性は保たれる。** -/
theorem admissible_cloneMany (fuel : Nat) : ∀ (s : DOMState) (l : List NodeId) (doc : NodeId)
    (parent : Option NodeId) (kids : List NodeId) (s' : DOMState),
    AdmissibleDOMState s → IsDocument s.tree doc →
    cloneMany fuel s l doc parent = .ok (kids, s') →
    AdmissibleDOMState s' ∧ IsDocument s'.tree doc := by
  induction fuel with
  | zero =>
    intro s l doc parent kids s' hv hdoc h
    cases l with
    | nil =>
      simp only [cloneMany, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ⟨hv, hdoc⟩
    | cons n rest => simp [cloneMany] at h
  | succ fuel ih =>
    intro s l doc parent kids s' hv hdoc h
    cases l with
    | nil =>
      simp only [cloneMany, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ⟨hv, hdoc⟩
    | cons n rest =>
      simp only [cloneMany] at h
      split at h
      · simp at h
      · next d hd =>
        split at h
        · simp at h
        · next s₂ happ =>
          split at h
          · simp at h
          · next kids₀ s₃ hkids =>
            split at h
            · simp at h
            · next siblings s₄ hsib =>
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨-, rfl⟩ := h
              -- step 2
              have hcreate := createsNode_withFresh (freshNodeData_cloneData hv hd hdoc)
              have hv₁ : AdmissibleDOMState (cloneSingle s d doc).2 :=
                admissible_createsNode hv hcreate
              have hdoc₁ : IsDocument (cloneSingle s d doc).2.tree doc := by
                obtain ⟨dd, hdd, hk⟩ := hdoc
                exact ⟨dd, (withFresh_addsNode s _).get?_of hdd, hk⟩
              -- step 4
              obtain ⟨hv₂, hsp⟩ := admissible_cloneAppend hv₁ happ
              have hdoc₂ : IsDocument s₂.tree doc := hdoc₁.map hsp
              -- step 5
              obtain ⟨hv₃, hdoc₃⟩ :=
                ih s₂ d.children doc (some (cloneSingle s d doc).1) kids₀ s₃ hv₂ hdoc₂ hkids
              exact ih s₃ rest doc parent siblings s₄ hv₃ hdoc₃ hsib

/-- **`cloneNode` は妥当性を保つ。** -/
theorem admissible_cloneNode {s s' : DOMState} {n c : NodeId} {deep : Bool}
    (hv : AdmissibleDOMState s) (h : cloneNode s n deep = .ok (c, s')) :
    AdmissibleDOMState s' := by
  unfold cloneNode at h
  split at h
  · simp at h
  · next d hd =>
    have hdoc : IsDocument s.tree d.ownerDocument :=
      hv.wellFormed.ownerDocument_is_document n d hd
    split at h
    · split at h
      · simp at h
      · next c₀ kids s₀ hcm =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact (admissible_cloneMany _ s [n] d.ownerDocument none (c₀ :: kids) s₀ hv hdoc hcm).1
      · simp at h
    · have he := Except.ok.inj h
      have hs : (cloneSingle s d d.ownerDocument).2 = s' := congrArg Prod.snd he
      rw [← hs]
      exact admissible_createsNode hv (createsNode_withFresh (freshNodeData_cloneData hv hd hdoc))

end Dom
