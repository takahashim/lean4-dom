import Dom.Attribute.Name
import Dom.Spec.Create

/-!
# "validate and extract" を本文の step 順に書いたもの（§1.4）

実行関数 `validateAndExtractAttribute` / `validateAndExtractElement`（`Dom/Attribute/Name.lean`）は、
step 1 の namespace の正規化を step 8 以降の検査の直前に一度だけ行い、
context の代わりに attribute 版と element 版の二つの関数を持つ。
ここでは本文の順（正規化を先に行い、context で step 6・7 を切り替える）のまま書き、
二つの実行関数がそれと等しいことを示す。

`*_eq_steps` は step の並べ替えを扱う。さらに `FirstColonSplit` は文字列の分解を、
`ValidateAndExtractResult` は宣言的な名前の条件と例外の優先順位を定義する。
`splitAtFirstColon_spec` と `validateAndExtract*_spec` は、実行側の splitter や
boolean validator を使わないこれらの関係への適合を証明する。
-/

namespace Dom.Spec

open Dom

/-- 最初のコロンが prefix と local name を分ける。prefix はコロンを含まない。 -/
def FirstColonSplit (q : String) : Option (String × String) → Prop
  | none => ':' ∉ q.toList
  | some (p, l) => q.toList = p.toList ++ ':' :: l.toList ∧ ':' ∉ p.toList

private theorem splitFirstColonChars_spec : ∀ cs : List Char,
    match splitFirstColonChars cs with
    | none => ':' ∉ cs
    | some (p, l) => cs = p ++ ':' :: l ∧ ':' ∉ p := by
  intro cs
  induction cs with
  | nil => simp [splitFirstColonChars]
  | cons c cs ih =>
    by_cases hc : c = ':'
    · subst hc; simp [splitFirstColonChars]
    · simp only [splitFirstColonChars, if_neg hc]
      cases hs : splitFirstColonChars cs with
      | none => simp only [hs] at ih; simpa [hs, hc, Ne.symm hc] using ih
      | some pair =>
        obtain ⟨p, l⟩ := pair
        simp only [hs] at ih
        simp [ih.1, ih.2, Ne.symm hc]

/-- 実行関数から独立に書いた分解の定理。空の prefix と、後ろに続くコロンも含む。 -/
theorem splitAtFirstColon_spec (q : String) : FirstColonSplit q (splitAtFirstColon q) := by
  have h := splitFirstColonChars_spec q.toList
  unfold splitAtFirstColon
  cases hs : splitFirstColonChars q.toList with
  | none => simpa [hs, FirstColonSplit] using h
  | some pair =>
    obtain ⟨p, l⟩ := pair
    simpa [hs, FirstColonSplit] using h

private theorem firstColonSplit_unique_chars : ∀ (p₁ p₂ l₁ l₂ : List Char),
    p₁ ++ ':' :: l₁ = p₂ ++ ':' :: l₂ → ':' ∉ p₁ → ':' ∉ p₂ → p₁ = p₂ ∧ l₁ = l₂
  | [], [], _, _, he, _, _ => by simpa using he
  | [], c :: _, _, _, he, _, hn => by
    have hc : c = ':' := (List.cons.inj he).1.symm
    subst hc; simp at hn
  | c :: _, [], _, _, he, hn, _ => by
    have hc : c = ':' := (List.cons.inj he).1
    subst hc; simp at hn
  | c :: p₁, c' :: p₂, l₁, l₂, he, hn₁, hn₂ => by
    simp only [List.cons_append] at he
    have hcc := (List.cons.inj he).1
    have htail := (List.cons.inj he).2
    subst hcc
    obtain ⟨hp, hl⟩ := firstColonSplit_unique_chars p₁ p₂ l₁ l₂ htail
      (fun hm => hn₁ (by simp [hm])) (fun hm => hn₂ (by simp [hm]))
    exact ⟨congrArg (c :: ·) hp, hl⟩

theorem firstColonSplit_unique {q : String} {a b : Option (String × String)}
    (ha : FirstColonSplit q a) (hb : FirstColonSplit q b) : a = b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some pair =>
      obtain ⟨p, l⟩ := pair
      exact False.elim (ha (by rw [hb.1]; simp))
  | some pair =>
    obtain ⟨p₁, l₁⟩ := pair
    cases b with
    | none => exact False.elim (hb (by rw [ha.1]; simp))
    | some pair =>
      obtain ⟨p₂, l₂⟩ := pair
      obtain ⟨hp, hl⟩ := firstColonSplit_unique_chars p₁.toList p₂.toList l₁.toList l₂.toList
        (ha.1.symm.trans hb.1) ha.2 hb.2
      simp only [String.toList_inj] at hp hl
      subst hp; subst hl; rfl

/-- 走査する実行関数の結果は、独立に書いた「最初のコロン」の関係とちょうど一致する。 -/
theorem splitAtFirstColon_iff {q : String} {r : Option (String × String)} :
    FirstColonSplit q r ↔ splitAtFirstColon q = r :=
  ⟨fun h => firstColonSplit_unique (splitAtFirstColon_spec q) h,
    fun h => h ▸ splitAtFirstColon_spec q⟩

/-- "validate and extract" の context。 -/
inductive NameContext where
  | attribute
  | element
  deriving DecidableEq, Repr

/-- **§1.4 "validate and extract"、本文の step 順。** -/
def validateAndExtractSteps (ctx : NameContext) («namespace» : Option String)
    (qualifiedName : String) : Except DOMException (Option String × Option String × String) :=
  -- step 1
  let ns := if «namespace» = some "" then none else «namespace»
  -- step 2-4.2
  let (pfx, localName) :=
    match splitAtFirstColon qualifiedName with
    | none => ((none : Option String), qualifiedName)
    | some (p, l) => (some p, l)
  -- step 4.3
  if pfx.any (fun p => !isValidNamespacePrefix p) then .error .invalidCharacterError
  -- step 6
  else if ctx = .attribute ∧ !isValidAttributeLocalName localName then .error .invalidCharacterError
  -- step 7
  else if ctx = .element ∧ !isValidElementLocalName localName then .error .invalidCharacterError
  -- step 8
  else if pfx.isSome ∧ ns = none then .error .namespaceError
  -- step 9
  else if pfx = some "xml" ∧ ns ≠ some xmlNamespace then .error .namespaceError
  -- step 10
  else if (qualifiedName = "xmlns" ∨ pfx = some "xmlns") ∧ ns ≠ some xmlnsNamespace then
    .error .namespaceError
  -- step 11
  else if ns = some xmlnsNamespace ∧ ¬ (qualifiedName = "xmlns" ∨ pfx = some "xmlns") then
    .error .namespaceError
  -- step 12
  else .ok (ns, pfx, localName)

/-- step 1 の書き方の違い：`normalizeNamespace` は空文字列を `isEmpty` で見る。 -/
theorem normalizeNamespace_eq (ns : Option String) :
    normalizeNamespace ns = if ns = some "" then none else ns := by
  cases ns with
  | none => rfl
  | some n =>
    unfold normalizeNamespace
    by_cases h : n = ""
    · subst h; rfl
    · have : n.isEmpty = false := by
        cases hn : n.isEmpty with
        | false => rfl
        | true => exact absurd (String.isEmpty_iff.mp hn) h
      simp [this, h]

/-- 検査の結果を `Except` に変える（実行関数の末尾の match と同じもの）。 -/
private def errOr {α : Type} (o : Option DOMException) (x : α) : Except DOMException α :=
  match o with
  | some e => .error e
  | none => .ok x

private theorem errOr_ite {α : Type} (c : Prop) [Decidable c] (a b : Option DOMException) (x : α) :
    errOr (if c then a else b) x = if c then errOr a x else errOr b x := by
  split <;> rfl

private theorem errOr_some {α : Type} (e : DOMException) (x : α) : errOr (some e) x = .error e := rfl

private theorem errOr_none {α : Type} (x : α) : errOr none x = .ok x := rfl

private theorem steps_eq (valid : String → Bool) (ctx : NameContext)
    (hvalid : ∀ l, valid l = (match ctx with
      | .attribute => isValidAttributeLocalName l
      | .element => isValidElementLocalName l))
    («namespace» : Option String) (qualifiedName : String) :
    (let (pfx, localName) :=
      match splitAtFirstColon qualifiedName with
      | none => ((none : Option String), qualifiedName)
      | some (p, l) => (some p, l)
    if pfx.any (fun p => !isValidNamespacePrefix p) then .error .invalidCharacterError
    else errOr (validateAndExtractError valid (normalizeNamespace «namespace») pfx localName
          qualifiedName) (normalizeNamespace «namespace», pfx, localName)) =
      validateAndExtractSteps ctx «namespace» qualifiedName := by
  unfold validateAndExtractSteps
  rw [normalizeNamespace_eq]
  generalize (if «namespace» = some "" then none else «namespace») = ns
  generalize splitAtFirstColon qualifiedName = sp
  have h67 : ∀ (l : String) (rest : Except DOMException (Option String × Option String × String)),
      (if (!valid l) = true then Except.error DOMException.invalidCharacterError else rest) =
        (if ctx = .attribute ∧ (!isValidAttributeLocalName l) = true then
          Except.error DOMException.invalidCharacterError
        else if ctx = .element ∧ (!isValidElementLocalName l) = true then
          Except.error DOMException.invalidCharacterError
        else rest) := by
    intro l rest
    cases ctx <;> simp [hvalid]
  rcases sp with _ | ⟨p, l⟩ <;> dsimp only <;> congr 1 <;>
    simp only [validateAndExtractError, errOr_ite, errOr_some, errOr_none] <;> rw [h67] <;>
    simp

/-- **attribute 版の実行関数は、本文の step 順に書いたものと等しい。** -/
theorem validateAndExtractAttribute_eq_steps («namespace» : Option String) (qualifiedName : String) :
    validateAndExtractAttribute «namespace» qualifiedName =
      validateAndExtractSteps .attribute «namespace» qualifiedName :=
  steps_eq _ .attribute (fun _ => rfl) «namespace» qualifiedName

/-- **element 版の実行関数は、本文の step 順に書いたものと等しい。** -/
theorem validateAndExtractElement_eq_steps («namespace» : Option String) (qualifiedName : String) :
    validateAndExtractElement «namespace» qualifiedName =
      validateAndExtractSteps .element «namespace» qualifiedName :=
  steps_eq _ .element (fun _ => rfl) «namespace» qualifiedName

/-- 実行関数から独立に書いた名前の検査の関係。最初のコロンでの分解と、valid な名前を述べる
    命題を使う。例外の優先順位は §1.4 に従う。 -/
noncomputable def ValidateAndExtractResult (ctx : NameContext) (ns₀ : Option String)
    (q : String) (res : Except DOMException (Option String × Option String × String)) : Prop := by
  classical
  exact ∃ sp, FirstColonSplit q sp ∧
    let ns := if ns₀ = some "" then none else ns₀
    let (pfx, localName) := match sp with
      | none => ((none : Option String), q)
      | some (p, l) => (some p, l)
    res =
      if ∃ p, pfx = some p ∧ ¬ ValidNamespacePrefix p then .error .invalidCharacterError
      else if ctx = .attribute ∧ ¬ ValidAttributeLocalName localName then .error .invalidCharacterError
      else if ctx = .element ∧ ¬ ValidElementLocalName localName then .error .invalidCharacterError
      else if pfx ≠ none ∧ ns = none then .error .namespaceError
      else if pfx = some "xml" ∧ ns ≠ some xmlNamespace then .error .namespaceError
      else if (q = "xmlns" ∨ pfx = some "xmlns") ∧ ns ≠ some xmlnsNamespace then .error .namespaceError
      else if ns = some xmlnsNamespace ∧ ¬ (q = "xmlns" ∨ pfx = some "xmlns") then .error .namespaceError
      else .ok (ns, pfx, localName)

/-- 本文の step 順の実行関数は、独立に書いた分解と名前の条件を満たす。 -/
theorem validateAndExtractSteps_spec (ctx : NameContext) (ns : Option String) (q : String) :
    ValidateAndExtractResult ctx ns q (validateAndExtractSteps ctx ns q) := by
  classical
  refine ⟨splitAtFirstColon q, splitAtFirstColon_spec q, ?_⟩
  unfold validateAndExtractSteps
  cases hs : splitAtFirstColon q with
  | none =>
    simp only [Option.any_none, Bool.false_eq_true, if_false, Option.isSome_none]
    have ha : isValidAttributeLocalName q = false ↔ ¬ ValidAttributeLocalName q :=
      Bool.eq_false_iff.trans (not_congr (validAttributeLocalName_iff q))
    have he : isValidElementLocalName q = false ↔ ¬ ValidElementLocalName q :=
      Bool.eq_false_iff.trans (not_congr (validElementLocalName_iff q))
    simp only [Bool.not_eq_true', ha, he]
    simp
  | some pair =>
    obtain ⟨p, l⟩ := pair
    simp only [Option.any_some, Option.isSome_some]
    have hp : (!isValidNamespacePrefix p) = true ↔ ¬ ValidNamespacePrefix p := by
      rw [Bool.not_eq_true']
      exact Bool.eq_false_iff.trans (not_congr (validNamespacePrefix_iff p))
    have ha : (!isValidAttributeLocalName l) = true ↔ ¬ ValidAttributeLocalName l := by
      rw [Bool.not_eq_true']
      exact Bool.eq_false_iff.trans (not_congr (validAttributeLocalName_iff l))
    have he : (!isValidElementLocalName l) = true ↔ ¬ ValidElementLocalName l := by
      rw [Bool.not_eq_true']
      exact Bool.eq_false_iff.trans (not_congr (validElementLocalName_iff l))
    simp only [hp, ha, he]
    simp

theorem validateAndExtractResult_deterministic {ctx : NameContext} {ns : Option String} {q : String}
    {a b : Except DOMException (Option String × Option String × String)}
    (ha : ValidateAndExtractResult ctx ns q a) (hb : ValidateAndExtractResult ctx ns q b) : a = b := by
  obtain ⟨spa, hspa, ha⟩ := ha
  obtain ⟨spb, hspb, hb⟩ := hb
  have he := firstColonSplit_unique hspa hspb
  subst he
  exact ha.trans hb.symm

/-- attribute の文脈での、仕様全体についての定理。 -/
theorem validateAndExtractAttribute_spec {ns : Option String} {q : String}
    {res : Except DOMException (Option String × Option String × String)} :
    ValidateAndExtractResult .attribute ns q res ↔ validateAndExtractAttribute ns q = res := by
  rw [validateAndExtractAttribute_eq_steps]
  exact ⟨fun h => validateAndExtractResult_deterministic (validateAndExtractSteps_spec _ _ _) h,
    fun h => h ▸ validateAndExtractSteps_spec _ _ _⟩

/-- element の文脈での、仕様全体についての定理。 -/
theorem validateAndExtractElement_spec {ns : Option String} {q : String}
    {res : Except DOMException (Option String × Option String × String)} :
    ValidateAndExtractResult .element ns q res ↔ validateAndExtractElement ns q = res := by
  rw [validateAndExtractElement_eq_steps]
  exact ⟨fun h => validateAndExtractResult_deterministic (validateAndExtractSteps_spec _ _ _) h,
    fun h => h ▸ validateAndExtractSteps_spec _ _ _⟩

end Dom.Spec
