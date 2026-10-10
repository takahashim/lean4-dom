import Dom.Attribute.Name

/-!
# "validate and extract" を本文の step 順に書いたもの（§1.4）

実行関数 `validateAndExtractAttribute` / `validateAndExtractElement`（`Dom/Attribute/Name.lean`）は、
step 1 の namespace の正規化を step 8 以降の検査の直前に一度だけ行い、
context の代わりに attribute 版と element 版の二つの関数を持つ。
ここでは本文の順（正規化を先に行い、context で step 6・7 を切り替える）のまま書き、
二つの実行関数がそれと等しいことを示す。

「最初の U+003A で分ける」には実行側と同じ `splitAtFirstColon` を使う。
この定理が言うのは step の並べ方と context の扱いが本文と同じ結果になることで、
文字列の切り方そのものの正しさではない。
-/

namespace Dom.Spec

open Dom

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

end Dom.Spec
