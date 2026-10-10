import Dom.Validity.Create

/-!
# 名前の検査と element の作成の関係仕様（§1.3、§4.5）

§1.3 の三つの名前の条件を本文の言い方のまま命題に書き、実行側の Boolean の検査と一致させる
（`validElementLocalName_iff` ほか）。そのうえで `createElement()` を、「Document でなければ失敗し、
名前が valid element local name でなければ InvalidCharacterError、そうでなければ step 2-5 の element を一つ作る」
という関係 `CreateElementResult` に書き、実行関数がそれを満たすことを示す（`createElement_result_sound`）。
-/

namespace Dom.Spec

open Dom Infra

/-- 名前に使えない文字：ASCII whitespace、U+0000 NULL、U+002F (/)、U+003E (>)。 -/
def ForbiddenNameChar (c : Char) : Prop :=
  isAsciiWhitespace c = true ∨ c.toNat = 0 ∨ c = '/' ∨ c = '>'

/-- §1.3 valid namespace prefix。 -/
def ValidNamespacePrefix (s : String) : Prop :=
  s.toList ≠ [] ∧ ∀ c ∈ s.toList, ¬ ForbiddenNameChar c

/-- §1.3 valid attribute local name。 -/
def ValidAttributeLocalName (s : String) : Prop :=
  s.toList ≠ [] ∧ ∀ c ∈ s.toList, ¬ ForbiddenNameChar c ∧ c ≠ '='

/-- ASCII alpha。 -/
def IsAsciiAlpha (c : Char) : Prop := ('a' ≤ c ∧ c ≤ 'z') ∨ ('A' ≤ c ∧ c ≤ 'Z')

/-- §1.3 valid element local name の step 4 で許す後続の code point。 -/
def ElementNameRestChar (c : Char) : Prop :=
  IsAsciiAlpha c ∨ ('0' ≤ c ∧ c ≤ '9') ∨ c = '-' ∨ c = '.' ∨ c = ':' ∨ c = '_' ∨ 0x80 ≤ c.toNat

/-- §1.3 valid element local name（step 1-5）。 -/
def ValidElementLocalName (s : String) : Prop :=
  ∃ c rest, s.toList = c :: rest ∧
    ((IsAsciiAlpha c ∧ ∀ x ∈ c :: rest, ¬ ForbiddenNameChar x) ∨
      (¬ IsAsciiAlpha c ∧ (c = ':' ∨ c = '_' ∨ 0x80 ≤ c.toNat) ∧ ∀ x ∈ rest, ElementNameRestChar x))

theorem forbidden_iff (c : Char) :
    (!isAsciiWhitespace c && c.toNat != 0x00 && c != '/' && c != '>') = true ↔ ¬ ForbiddenNameChar c := by
  unfold ForbiddenNameChar
  cases h : isAsciiWhitespace c <;> simp <;> grind

theorem isEmpty_eq_false_iff (s : String) : s.isEmpty = false ↔ s.toList ≠ [] := by
  cases h : s.isEmpty
  · simp only [true_iff]
    intro hl; simp [String.isEmpty_iff, ← String.toList_inj, hl] at h
  · simp only [Bool.true_eq_false, false_iff, ne_eq, Decidable.not_not]
    simp [String.isEmpty_iff] at h; simp [h]

theorem validNamespacePrefix_iff (s : String) :
    isValidNamespacePrefix s = true ↔ ValidNamespacePrefix s := by
  unfold isValidNamespacePrefix ValidNamespacePrefix
  rw [Bool.and_eq_true, Bool.not_eq_true', isEmpty_eq_false_iff, List.all_eq_true]
  exact and_congr_right fun _ => forall₂_congr fun c _ => forbidden_iff c

theorem validAttributeLocalName_iff (s : String) :
    isValidAttributeLocalName s = true ↔ ValidAttributeLocalName s := by
  unfold isValidAttributeLocalName ValidAttributeLocalName
  rw [Bool.and_eq_true, Bool.not_eq_true', isEmpty_eq_false_iff, List.all_eq_true]
  refine and_congr_right fun _ => forall₂_congr fun c _ => ?_
  unfold ForbiddenNameChar
  cases h : isAsciiWhitespace c <;> simp <;> grind

theorem restChar_iff (x : Char) :
    (('a' ≤ x && x ≤ 'z') || ('A' ≤ x && x ≤ 'Z') || ('0' ≤ x && x ≤ '9') ||
      x == '-' || x == '.' || x == ':' || x == '_' || decide (x.toNat ≥ 0x80)) = true ↔
      ElementNameRestChar x := by
  unfold ElementNameRestChar IsAsciiAlpha
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  grind

theorem validElementLocalName_iff (s : String) :
    isValidElementLocalName s = true ↔ ValidElementLocalName s := by
  unfold isValidElementLocalName ValidElementLocalName
  cases hs : s.toList with
  | nil => simp
  | cons c rest =>
    have hex : (∃ c' rest', c :: rest = c' :: rest' ∧
        ((IsAsciiAlpha c' ∧ ∀ x ∈ c' :: rest', ¬ ForbiddenNameChar x) ∨
          (¬ IsAsciiAlpha c' ∧ (c' = ':' ∨ c' = '_' ∨ 0x80 ≤ c'.toNat) ∧
            ∀ x ∈ rest', ElementNameRestChar x))) ↔
        ((IsAsciiAlpha c ∧ ∀ x ∈ c :: rest, ¬ ForbiddenNameChar x) ∨
          (¬ IsAsciiAlpha c ∧ (c = ':' ∨ c = '_' ∨ 0x80 ≤ c.toNat) ∧
            ∀ x ∈ rest, ElementNameRestChar x)) := by
      constructor
      · rintro ⟨c', rest', he, h⟩
        simp only [List.cons.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact h
      · intro h; exact ⟨c, rest, rfl, h⟩
    rw [hex]
    simp only
    have ha : ((('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')) = true) ↔ IsAsciiAlpha c := by
      unfold IsAsciiAlpha; simp
    by_cases hac : IsAsciiAlpha c
    · rw [if_pos (ha.mpr hac), List.all_eq_true]
      constructor
      · intro h; exact Or.inl ⟨hac, fun x hx => (forbidden_iff x).mp (h x hx)⟩
      · rintro (⟨-, h⟩ | ⟨hna, -⟩)
        · exact fun x hx => (forbidden_iff x).mpr (h x hx)
        · exact absurd hac hna
    · rw [if_neg (fun h => hac (ha.mp h))]
      have hf : ((c == ':' || c == '_' || decide (c.toNat ≥ 0x80)) = true) ↔
          (c = ':' ∨ c = '_' ∨ 0x80 ≤ c.toNat) := by
        simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]; grind
      by_cases hfc : c = ':' ∨ c = '_' ∨ 0x80 ≤ c.toNat
      · rw [if_pos (hf.mpr hfc), List.all_eq_true]
        constructor
        · intro h; exact Or.inr ⟨hac, hfc, fun x hx => (restChar_iff x).mp (h x hx)⟩
        · rintro (⟨h, -⟩ | ⟨-, -, h⟩)
          · exact absurd h hac
          · exact fun x hx => (restChar_iff x).mpr (h x hx)
      · rw [if_neg (fun h => hfc (hf.mp h))]
        simp only [Bool.false_eq_true, false_iff, not_or, not_and]
        exact ⟨fun h => absurd h hac, fun _ h => absurd h hfc⟩

/-! ## `createElement()` -/

/-- §4.5 `createElement(localName)`（options と custom element を除く）。 -/
def CreateElementResult (s : DOMState) (doc : NodeId) (localName : String)
    (r : Except DOMException (NodeId × DOMState)) : Prop :=
  ∃ dd, s.tree.get? doc = some dd ∧ dd.kind = .document ∧
    ((¬ ValidElementLocalName localName ∧ r = .error .invalidCharacterError) ∨
      (ValidElementLocalName localName ∧ ∃ n s', r = .ok (n, s') ∧
        CreatesNode s n s'
          { kind := .element, ownerDocument := doc,
            «namespace» :=
              if dd.isHTMLDocument = true ∨ dd.contentType = "application/xhtml+xml" then
                some htmlNamespace else none,
            localName := if dd.isHTMLDocument = true then asciiLowercase localName else localName }))

theorem createElement_result_sound {s : DOMState} {doc : NodeId} {dd : NodeData}
    (hdd : s.tree.get? doc = some dd) (hk : dd.kind = .document) (localName : String) :
    CreateElementResult s doc localName (createElement s doc localName) := by
  refine ⟨dd, hdd, hk, ?_⟩
  by_cases hv : isValidElementLocalName localName = true
  · cases h : createElement s doc localName with
    | error e =>
      unfold createElement at h
      simp [requireDocument, hdd, hk, hv] at h
    | ok p =>
      obtain ⟨n, s'⟩ := p
      obtain ⟨dd', hdd', -, hc⟩ := createElement_creates h
      rw [hdd] at hdd'; cases hdd'
      refine Or.inr ⟨(validElementLocalName_iff _).mp hv, n, s', rfl, ?_⟩
      have e1 : (if (dd.isHTMLDocument || dd.contentType == "application/xhtml+xml") = true then
            some htmlNamespace else none) =
          (if dd.isHTMLDocument = true ∨ dd.contentType = "application/xhtml+xml" then
            some htmlNamespace else none) := by
        by_cases h1 : dd.isHTMLDocument = true ∨ dd.contentType = "application/xhtml+xml"
        · rw [if_pos h1, if_pos (by simpa [Bool.or_eq_true, beq_iff_eq] using h1)]
        · rw [if_neg h1, if_neg (by simpa [Bool.or_eq_true, beq_iff_eq] using h1)]
      rw [e1] at hc
      exact hc
  · refine Or.inl ⟨fun h => hv ((validElementLocalName_iff _).mpr h), ?_⟩
    unfold createElement
    simp [requireDocument, hdd, hk, hv]

end Dom.Spec
