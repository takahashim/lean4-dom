import Dom.Spec.AttributeSound
import Dom.Query.NodeQuery

/-!
# "locate a namespace" と "locate a namespace prefix" の関係仕様（§4.4）

本文の二つの algorithm は element の parent element へ再帰する。関係はその再帰のまま帰納的に書き、
実行関数（element chain の列を前から見る）がそれを満たすことを示す。

| 関係 | 本文 |
| --- | --- |
| `ParentElementIs t n p` | §4.2 の parent element |
| `DocumentElementIs t n e` | §4.2 の document element（element の子のうち最初のもの） |
| `IsXmlnsDecl prefix a` | "locate a namespace" step 4 の attribute の条件 |
| `LocateNamespaceElem` | "locate a namespace" の Element の枝（step 1-6） |
| `LocateNamespace` | "locate a namespace" 全体（node の interface で分ける） |
| `LocatePrefixElem` | "locate a namespace prefix"（step 1-4） |
| `LookupPrefixResult` | `lookupPrefix(namespace)` |
-/

namespace Dom.Spec

open Dom

/-- §4.2 の parent element。parent が element でなければ null。 -/
def ParentElementIs (t : Tree) (n : NodeId) : Option NodeId → Prop
  | some p => parentOf t n = some p ∧ kindOf t p = some .element
  | none => ∀ p, parentOf t n = some p → kindOf t p ≠ some .element

/-- §4.2 の document element：element の子のうち最初のもの。 -/
def DocumentElementIs (t : Tree) (n : NodeId) : Option NodeId → Prop
  | some e => ∃ pre post, childrenOf t n = pre ++ e :: post ∧ kindOf t e = some .element ∧
      ∀ x ∈ pre, kindOf t x ≠ some .element
  | none => ∀ x ∈ childrenOf t n, kindOf t x ≠ some .element

/-- "locate a namespace" step 4 の attribute。 -/
def IsXmlnsDecl («prefix» : Option String) (a : Attr) : Prop :=
  (a.namespace = some xmlnsNamespace ∧ a.prefix = some "xmlns" ∧ some a.localName = «prefix») ∨
    («prefix» = none ∧ a.namespace = some xmlnsNamespace ∧ a.prefix = none ∧ a.localName = "xmlns")

/-- "locate a namespace" の Element の枝。 -/
inductive LocateNamespaceElem (t : Tree) («prefix» : Option String) : NodeId → Option String → Prop
  /-- step 1 -/
  | xml {e : NodeId} {d : NodeData} : t.get? e = some d → «prefix» = some "xml" →
      LocateNamespaceElem t «prefix» e (some xmlNamespace)
  /-- step 2 -/
  | xmlns {e : NodeId} {d : NodeData} : t.get? e = some d → «prefix» = some "xmlns" →
      LocateNamespaceElem t «prefix» e (some xmlnsNamespace)
  /-- step 3 -/
  | own {e : NodeId} {d : NodeData} : t.get? e = some d → «prefix» ≠ some "xml" →
      «prefix» ≠ some "xmlns" → d.namespace ≠ none → d.prefix = «prefix» →
      LocateNamespaceElem t «prefix» e d.namespace
  /-- step 4 -/
  | decl {e : NodeId} {d : NodeData} {a : Attr} : t.get? e = some d → «prefix» ≠ some "xml" →
      «prefix» ≠ some "xmlns" → ¬ (d.namespace ≠ none ∧ d.prefix = «prefix») →
      FirstAttr d.attributes (IsXmlnsDecl «prefix») (some a) →
      LocateNamespaceElem t «prefix» e (if a.value = "" then none else some a.value)
  /-- step 5 -/
  | top {e : NodeId} {d : NodeData} : t.get? e = some d → «prefix» ≠ some "xml" →
      «prefix» ≠ some "xmlns" → ¬ (d.namespace ≠ none ∧ d.prefix = «prefix») →
      FirstAttr d.attributes (IsXmlnsDecl «prefix») none → ParentElementIs t e none →
      LocateNamespaceElem t «prefix» e none
  /-- step 6 -/
  | up {e p : NodeId} {d : NodeData} {r : Option String} : t.get? e = some d →
      «prefix» ≠ some "xml" → «prefix» ≠ some "xmlns" → ¬ (d.namespace ≠ none ∧ d.prefix = «prefix») →
      FirstAttr d.attributes (IsXmlnsDecl «prefix») none → ParentElementIs t e (some p) →
      LocateNamespaceElem t «prefix» p r → LocateNamespaceElem t «prefix» e r

/-- "locate a namespace"（Attr の枝を除く）。 -/
def LocateNamespace (t : Tree) (n : NodeId) («prefix» : Option String) (r : Option String) : Prop :=
  ∃ d, t.get? n = some d ∧
    match d.kind with
    | .element => LocateNamespaceElem t «prefix» n r
    | .document =>
      (DocumentElementIs t n none ∧ r = none) ∨
        ∃ e, DocumentElementIs t n (some e) ∧ LocateNamespaceElem t «prefix» e r
    | .documentType | .documentFragment => r = none
    | _ =>
      (ParentElementIs t n none ∧ r = none) ∨
        ∃ e, ParentElementIs t n (some e) ∧ LocateNamespaceElem t «prefix» e r

/-- "locate a namespace prefix"。 -/
inductive LocatePrefixElem (t : Tree) («namespace» : String) : NodeId → Option String → Prop
  /-- step 1 -/
  | own {e : NodeId} {d : NodeData} : t.get? e = some d → d.namespace = some «namespace» →
      d.prefix ≠ none → LocatePrefixElem t «namespace» e d.prefix
  /-- step 2 -/
  | decl {e : NodeId} {d : NodeData} {a : Attr} : t.get? e = some d →
      ¬ (d.namespace = some «namespace» ∧ d.prefix ≠ none) →
      FirstAttr d.attributes (fun a => a.prefix = some "xmlns" ∧ a.value = «namespace») (some a) →
      LocatePrefixElem t «namespace» e (some a.localName)
  /-- step 4 -/
  | top {e : NodeId} {d : NodeData} : t.get? e = some d →
      ¬ (d.namespace = some «namespace» ∧ d.prefix ≠ none) →
      FirstAttr d.attributes (fun a => a.prefix = some "xmlns" ∧ a.value = «namespace») none →
      ParentElementIs t e none → LocatePrefixElem t «namespace» e none
  /-- step 3 -/
  | up {e p : NodeId} {d : NodeData} {r : Option String} : t.get? e = some d →
      ¬ (d.namespace = some «namespace» ∧ d.prefix ≠ none) →
      FirstAttr d.attributes (fun a => a.prefix = some "xmlns" ∧ a.value = «namespace») none →
      ParentElementIs t e (some p) → LocatePrefixElem t «namespace» p r →
      LocatePrefixElem t «namespace» e r

/-- §4.4 `lookupPrefix(namespace)`（Attr の枝を除く）。 -/
def LookupPrefixResult (t : Tree) (n : NodeId) («namespace» : Option String) (r : Option String) :
    Prop :=
  ((«namespace» = none ∨ «namespace» = some "") ∧ r = none) ∨
  ∃ ns, «namespace» = some ns ∧ ns ≠ "" ∧ ∃ d, t.get? n = some d ∧
    match d.kind with
    | .element => LocatePrefixElem t ns n r
    | .document =>
      (DocumentElementIs t n none ∧ r = none) ∨
        ∃ e, DocumentElementIs t n (some e) ∧ LocatePrefixElem t ns e r
    | .documentType | .documentFragment => r = none
    | _ =>
      (ParentElementIs t n none ∧ r = none) ∨
        ∃ e, ParentElementIs t n (some e) ∧ LocatePrefixElem t ns e r

/-! ## element chain -/

theorem ancestors_nil_of_parent_none {t : Tree} {n : NodeId} (h : parentOf t n = none) :
    ancestors t n = [] := by
  unfold ancestors
  cases t.size with
  | zero => rfl
  | succ f => exact ancestorChain_succ_none h

theorem elementChain_up {t : Tree} (hwf : WellFormed t) {e p : NodeId}
    (he : kindOf t e = some .element) (hp : ParentElementIs t e (some p)) :
    elementChain t e = e :: elementChain t p := by
  obtain ⟨hpar, hpk⟩ := hp
  unfold elementChain
  rw [ancestors_eq_cons hwf hpar]
  simp [List.takeWhile_cons, he]

theorem elementChain_top {t : Tree} {e : NodeId}
    (he : kindOf t e = some .element) (hp : ParentElementIs t e none) :
    elementChain t e = [e] := by
  unfold elementChain
  cases hpar : parentOf t e with
  | none => rw [ancestors_nil_of_parent_none hpar]; simp [he]
  | some p =>
    have hwf' := hp p hpar
    -- parent が element でないので takeWhile はそこで止まる
    unfold ancestors
    cases hs : t.size with
    | zero => simp [ancestorChain, he]
    | succ f =>
      rw [ancestorChain_succ_some hpar]
      simp [he, hwf']

theorem parentElementIs_parentElement (t : Tree) (n : NodeId) :
    ParentElementIs t n (parentElement t n) := by
  unfold parentElement
  cases hp : parentOf t n with
  | none => intro p h; rw [hp] at h; cases h
  | some p =>
    simp only
    split
    · next h => exact ⟨hp, by simpa using h⟩
    · next h => intro q hq; rw [hp] at hq; cases hq; simpa using h

theorem documentElementIs_documentElement (t : Tree) (n : NodeId) :
    DocumentElementIs t n (documentElement t n) := by
  unfold documentElement
  cases hf : (childrenOf t n).find? (fun c => kindOf t c == some NodeKind.element) with
  | none =>
    intro x hx hk
    have := List.find?_eq_none.mp hf x hx
    simp [hk] at this
  | some e =>
    obtain ⟨he, pre, post, hsplit, hpre⟩ := List.find?_eq_some_iff_append.mp hf
    exact ⟨pre, post, hsplit, by simpa using he, fun x hx hk => by simpa [hk] using hpre x hx⟩

theorem isXmlnsDecl_iff («prefix» : Option String) (a : Attr) :
    ((a.namespace == some xmlnsNamespace && a.prefix == some "xmlns" &&
        some a.localName == «prefix») ||
      («prefix».isNone && a.namespace == some xmlnsNamespace && a.prefix.isNone &&
        a.localName == "xmlns")) = true ↔ IsXmlnsDecl «prefix» a := by
  unfold IsXmlnsDecl
  cases «prefix» <;> cases hp : a.prefix <;> simp [and_assoc]

/-- 一段ぶん：列の先頭の element について本文の step 1-6 をたどる。 -/
theorem locateNamespaceIn_step {t : Tree} {«prefix» : Option String} {e : NodeId} {d : NodeData}
    (hd : t.get? e = some d) (rest : List NodeId)
    (hrest : (ParentElementIs t e none ∧ rest = []) ∨
      ∃ q, ParentElementIs t e (some q) ∧
        LocateNamespaceElem t «prefix» q (locateNamespaceIn t «prefix» rest)) :
    LocateNamespaceElem t «prefix» e (locateNamespaceIn t «prefix» (e :: rest)) := by
  unfold locateNamespaceIn
  by_cases hxml : «prefix» = some "xml"
  · simp only [hxml, beq_self_eq_true, if_true]
    exact .xml hd rfl
  · have hxml' : («prefix» == some "xml") = false := by simpa using hxml
    rw [if_neg (by simp [hxml'])]
    by_cases hxmlns : «prefix» = some "xmlns"
    · simp only [hxmlns, beq_self_eq_true, if_true]
      exact .xmlns hd rfl
    · have hxmlns' : («prefix» == some "xmlns") = false := by simpa using hxmlns
      rw [if_neg (by simp [hxmlns']), hd]
      simp only
      by_cases hown : d.namespace ≠ none ∧ d.prefix = «prefix»
      · rw [if_pos (by simp [Option.isSome_iff_ne_none, hown.1, hown.2])]
        exact .own hd hxml hxmlns hown.1 hown.2
      · rw [if_neg (by
          simp only [Bool.and_eq_true, Option.isSome_iff_ne_none, beq_iff_eq]
          exact hown)]
        let P : Attr → Bool := fun a =>
          (a.namespace == some xmlnsNamespace && a.prefix == some "xmlns" &&
              some a.localName == «prefix») ||
            («prefix».isNone && a.namespace == some xmlnsNamespace && a.prefix.isNone &&
              a.localName == "xmlns")
        have hfa := firstAttr_of_find? (as := d.attributes) (p := P) rfl
        have hfa' : ∀ r, FirstAttr d.attributes (fun a => P a = true) r →
            FirstAttr d.attributes (IsXmlnsDecl «prefix») r := by
          intro r hr
          cases r with
          | none => intro x hx hpx; exact hr x hx ((isXmlnsDecl_iff _ x).mpr hpx)
          | some a =>
            obtain ⟨pre, post, hs, hp, hpre⟩ := hr
            exact ⟨pre, post, hs, (isXmlnsDecl_iff _ a).mp hp,
              fun x hx hpx => hpre x hx ((isXmlnsDecl_iff _ x).mpr hpx)⟩
        split
        · next a ha =>
          rw [ha] at hfa
          have h := LocateNamespaceElem.decl (t := t) hd hxml hxmlns hown (hfa' _ hfa)
          by_cases hv : a.value = ""
          · simpa [hv] using h
          · simpa [hv] using h
        · next ha =>
          rw [ha] at hfa
          rcases hrest with ⟨htop, rfl⟩ | ⟨q, hq, hrec⟩
          · exact .top hd hxml hxmlns hown (hfa' _ hfa) htop
          · exact .up hd hxml hxmlns hown (hfa' _ hfa) hq hrec

/-- element chain の上の探索は、本文の再帰を満たす。 -/
theorem locateNamespaceIn_sound {t : Tree} (hwf : WellFormed t) («prefix» : Option String) :
    ∀ (k : Nat) (e : NodeId), (ancestors t e).length ≤ k → kindOf t e = some .element →
      LocateNamespaceElem t «prefix» e (locateNamespaceIn t «prefix» (elementChain t e)) := by
  intro k
  induction k with
  | zero =>
    intro e hk he
    obtain ⟨d, hd⟩ : ∃ d, t.get? e = some d := by
      unfold kindOf at he; cases h : t.get? e <;> simp_all
    have hpe := parentElementIs_parentElement t e
    cases hq : parentElement t e with
    | none =>
      rw [hq] at hpe
      rw [elementChain_top he hpe]
      exact locateNamespaceIn_step hd [] (Or.inl ⟨hpe, rfl⟩)
    | some q =>
      rw [hq] at hpe
      rw [ancestors_eq_cons hwf hpe.1] at hk
      simp at hk
  | succ k ih =>
    intro e hk he
    obtain ⟨d, hd⟩ : ∃ d, t.get? e = some d := by
      unfold kindOf at he; cases h : t.get? e <;> simp_all
    have hpe := parentElementIs_parentElement t e
    cases hq : parentElement t e with
    | none =>
      rw [hq] at hpe
      rw [elementChain_top he hpe]
      exact locateNamespaceIn_step hd [] (Or.inl ⟨hpe, rfl⟩)
    | some q =>
      rw [hq] at hpe
      rw [elementChain_up hwf he hpe]
      have hlen : (ancestors t q).length ≤ k := by
        rw [ancestors_eq_cons hwf hpe.1] at hk; simp at hk; omega
      exact locateNamespaceIn_step hd _ (Or.inr ⟨q, hpe, ih q hlen hpe.2⟩)

theorem locateNamespaceElem_of_chain {t : Tree} (hwf : WellFormed t) («prefix» : Option String)
    {e : NodeId} (he : kindOf t e = some .element) :
    LocateNamespaceElem t «prefix» e (locateNamespaceIn t «prefix» (elementChain t e)) :=
  locateNamespaceIn_sound hwf «prefix» _ e (Nat.le_refl _) he

/-- **"locate a namespace" の実行関数は、本文の再帰を満たす。** -/
theorem locateNamespace_sound {t : Tree} (hwf : WellFormed t) {n : NodeId} {d : NodeData}
    (hn : t.get? n = some d) («prefix» : Option String) :
    LocateNamespace t n «prefix» (locateNamespace t n «prefix») := by
  refine ⟨d, hn, ?_⟩
  unfold locateNamespace
  rw [hn]
  simp only
  have hkind : ∀ e, ParentElementIs t n (some e) ∨ DocumentElementIs t n (some e) →
      kindOf t e = some .element := by
    rintro e (⟨-, h⟩ | ⟨-, -, -, h, -⟩) <;> exact h
  have hgen : (ParentElementIs t n none ∧
        (match parentElement t n with
          | none => none
          | some e => locateNamespaceIn t «prefix» (elementChain t e)) = none) ∨
      ∃ e, ParentElementIs t n (some e) ∧ LocateNamespaceElem t «prefix» e
        (match parentElement t n with
          | none => none
          | some e => locateNamespaceIn t «prefix» (elementChain t e)) := by
    have hpe := parentElementIs_parentElement t n
    cases hq : parentElement t n with
    | none => rw [hq] at hpe; exact Or.inl ⟨hpe, rfl⟩
    | some e =>
      rw [hq] at hpe
      exact Or.inr ⟨e, hpe, locateNamespaceElem_of_chain hwf «prefix» (hkind e (Or.inl hpe))⟩
  cases hk : d.kind with
  | element =>
    simp only
    exact locateNamespaceElem_of_chain hwf «prefix» (by simp [kindOf, hn, hk])
  | document =>
    simp only
    have hde := documentElementIs_documentElement t n
    cases hq : documentElement t n with
    | none => rw [hq] at hde; exact Or.inl ⟨hde, rfl⟩
    | some e =>
      rw [hq] at hde
      exact Or.inr ⟨e, hde, locateNamespaceElem_of_chain hwf «prefix» (hkind e (Or.inr hde))⟩
  | documentType => rfl
  | documentFragment => rfl
  | text => exact hgen
  | cdataSection => exact hgen
  | processingInstruction => exact hgen
  | comment => exact hgen

/-- **`lookupNamespaceURI(prefix)`**：空文字列の prefix を null にして "locate a namespace" する。 -/
theorem lookupNamespaceURI_sound {t : Tree} (hwf : WellFormed t) {n : NodeId} {d : NodeData}
    (hn : t.get? n = some d) («prefix» : Option String) :
    LocateNamespace t n (if «prefix» = some "" then none else «prefix»)
      (lookupNamespaceURI t n «prefix») := by
  unfold lookupNamespaceURI
  have := locateNamespace_sound hwf hn (if «prefix» == some "" then none else «prefix»)
  simpa using this

/-- **`isDefaultNamespace(namespace)`**：null で locate した結果が namespace（空文字列なら null）と同じか。 -/
theorem isDefaultNamespace_sound {t : Tree} (hwf : WellFormed t) {n : NodeId} {d : NodeData}
    (hn : t.get? n = some d) («namespace» : Option String) :
    ∃ r, LocateNamespace t n none r ∧
      (isDefaultNamespace t n «namespace» = true ↔
        r = (if «namespace» = some "" then none else «namespace»)) := by
  refine ⟨_, locateNamespace_sound hwf hn none, ?_⟩
  unfold isDefaultNamespace
  simp

/-! ## "locate a namespace prefix" -/

theorem locatePrefixIn_step {t : Tree} {ns : String} {e : NodeId} {d : NodeData}
    (hd : t.get? e = some d) (rest : List NodeId)
    (hrest : (ParentElementIs t e none ∧ rest = []) ∨
      ∃ q, ParentElementIs t e (some q) ∧
        LocatePrefixElem t ns q (locateNamespacePrefixIn t ns rest)) :
    LocatePrefixElem t ns e (locateNamespacePrefixIn t ns (e :: rest)) := by
  unfold locateNamespacePrefixIn
  rw [hd]
  simp only
  by_cases hown : d.namespace = some ns ∧ d.prefix ≠ none
  · rw [if_pos (by simp [Option.isSome_iff_ne_none, hown.1, hown.2])]
    exact .own hd hown.1 hown.2
  · rw [if_neg (by
      simp only [Bool.and_eq_true, Option.isSome_iff_ne_none, beq_iff_eq]
      exact hown)]
    let P : Attr → Bool := fun a => a.prefix == some "xmlns" && a.value == ns
    have hfa := firstAttr_of_find? (as := d.attributes) (p := P) rfl
    have hfa' : ∀ r, FirstAttr d.attributes (fun a => P a = true) r →
        FirstAttr d.attributes (fun a => a.prefix = some "xmlns" ∧ a.value = ns) r := by
      intro r hr
      cases r with
      | none => intro x hx hpx; exact hr x hx (by simp [P, hpx.1, hpx.2])
      | some a =>
        obtain ⟨pre, post, hs, hp, hpre⟩ := hr
        exact ⟨pre, post, hs, by simpa [P] using hp,
          fun x hx hpx => hpre x hx (by simp [P, hpx.1, hpx.2])⟩
    split
    · next a ha =>
      rw [ha] at hfa
      exact .decl hd hown (hfa' _ hfa)
    · next ha =>
      rw [ha] at hfa
      rcases hrest with ⟨htop, rfl⟩ | ⟨q, hq, hrec⟩
      · exact .top hd hown (hfa' _ hfa) htop
      · exact .up hd hown (hfa' _ hfa) hq hrec

theorem locatePrefixIn_sound {t : Tree} (hwf : WellFormed t) (ns : String) :
    ∀ (k : Nat) (e : NodeId), (ancestors t e).length ≤ k → kindOf t e = some .element →
      LocatePrefixElem t ns e (locateNamespacePrefixIn t ns (elementChain t e)) := by
  intro k
  induction k with
  | zero =>
    intro e hk he
    obtain ⟨d, hd⟩ : ∃ d, t.get? e = some d := by
      unfold kindOf at he; cases h : t.get? e <;> simp_all
    have hpe := parentElementIs_parentElement t e
    cases hq : parentElement t e with
    | none =>
      rw [hq] at hpe
      rw [elementChain_top he hpe]
      exact locatePrefixIn_step hd [] (Or.inl ⟨hpe, rfl⟩)
    | some q =>
      rw [hq] at hpe
      rw [ancestors_eq_cons hwf hpe.1] at hk
      simp at hk
  | succ k ih =>
    intro e hk he
    obtain ⟨d, hd⟩ : ∃ d, t.get? e = some d := by
      unfold kindOf at he; cases h : t.get? e <;> simp_all
    have hpe := parentElementIs_parentElement t e
    cases hq : parentElement t e with
    | none =>
      rw [hq] at hpe
      rw [elementChain_top he hpe]
      exact locatePrefixIn_step hd [] (Or.inl ⟨hpe, rfl⟩)
    | some q =>
      rw [hq] at hpe
      rw [elementChain_up hwf he hpe]
      have hlen : (ancestors t q).length ≤ k := by
        rw [ancestors_eq_cons hwf hpe.1] at hk; simp at hk; omega
      exact locatePrefixIn_step hd _ (Or.inr ⟨q, hpe, ih q hlen hpe.2⟩)

/-- **`lookupPrefix(namespace)` の実行関数は、本文の再帰を満たす。** -/
theorem lookupPrefix_sound {t : Tree} (hwf : WellFormed t) {n : NodeId} {d : NodeData}
    (hn : t.get? n = some d) («namespace» : Option String) :
    LookupPrefixResult t n «namespace» (lookupPrefix t n «namespace») := by
  have hchain : ∀ (ns : String) e, kindOf t e = some .element →
      LocatePrefixElem t ns e (locateNamespacePrefixIn t ns (elementChain t e)) :=
    fun ns e he => locatePrefixIn_sound hwf ns _ e (Nat.le_refl _) he
  unfold lookupPrefix LookupPrefixResult
  cases «namespace» with
  | none => exact Or.inl ⟨Or.inl rfl, rfl⟩
  | some ns =>
    simp only
    by_cases hemp : ns = ""
    · subst hemp; exact Or.inl ⟨Or.inr rfl, rfl⟩
    · rw [if_neg (by simpa using hemp)]
      refine Or.inr ⟨ns, rfl, hemp, d, hn, ?_⟩
      rw [hn]
      simp only
      have hgen : (ParentElementIs t n none ∧
            (match parentElement t n with
              | none => none
              | some e => locateNamespacePrefixIn t ns (elementChain t e)) = none) ∨
          ∃ e, ParentElementIs t n (some e) ∧ LocatePrefixElem t ns e
            (match parentElement t n with
              | none => none
              | some e => locateNamespacePrefixIn t ns (elementChain t e)) := by
        have hpe := parentElementIs_parentElement t n
        cases hq : parentElement t n with
        | none => rw [hq] at hpe; exact Or.inl ⟨hpe, rfl⟩
        | some e => rw [hq] at hpe; exact Or.inr ⟨e, hpe, hchain ns e hpe.2⟩
      cases hk : d.kind with
      | element => exact hchain ns n (by simp [kindOf, hn, hk])
      | document =>
        simp only
        have hde := documentElementIs_documentElement t n
        cases hq : documentElement t n with
        | none => rw [hq] at hde; exact Or.inl ⟨hde, rfl⟩
        | some e =>
          rw [hq] at hde
          obtain ⟨pre, post, hs, he, hpre⟩ := hde
          exact Or.inr ⟨e, ⟨pre, post, hs, he, hpre⟩, hchain ns e he⟩
      | documentType => rfl
      | documentFragment => rfl
      | text => exact hgen
      | cdataSection => exact hgen
      | processingInstruction => exact hgen
      | comment => exact hgen

end Dom.Spec
