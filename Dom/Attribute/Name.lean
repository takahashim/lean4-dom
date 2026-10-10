import Dom.Basic.Exception
import Infra.Ascii

/-!
# 名前の検査と namespace の切り出し

DOM Standard §1.3 "Name validation" と "validate and extract"。

次のものを扱う。

* valid namespace prefix
* valid attribute local name
* valid element local name
* validate and extract（context は "attribute" と "element" の二つの関数に分ける）

本文の step 順に書いた "validate and extract" と、ここの二つの関数が等しいことは
`Dom/Spec/ValidateAndExtract.lean` にある。
-/

namespace Dom

-- Infra Standard の語彙は `Infra/Ascii.lean` にある（URL Standard と共有する）。
export Infra (isAsciiWhitespace asciiLowercase asciiUppercase)

/--
DOM Standard §1.3 valid namespace prefix。

長さ 1 以上で、ASCII whitespace / U+0000 / `/` / `>` を含まない。
-/
def isValidNamespacePrefix (s : String) : Bool :=
  !s.isEmpty && s.toList.all fun c =>
    !isAsciiWhitespace c && c.toNat != 0x00 && c != '/' && c != '>'

/--
DOM Standard §1.3 valid attribute local name。

valid namespace prefix の条件に `=` を加えたものである。
-/
def isValidAttributeLocalName (s : String) : Bool :=
  !s.isEmpty && s.toList.all fun c =>
    !isAsciiWhitespace c && c.toNat != 0x00 && c != '/' && c != '=' && c != '>'

/-- 仕様が namespace 引数に対して繰り返す「空文字列なら null」。 -/
def normalizeNamespace : Option String → Option String
  | some n => if n.isEmpty then none else some n
  | none => none

@[simp] theorem normalizeNamespace_idem (ns : Option String) :
    normalizeNamespace (normalizeNamespace ns) = normalizeNamespace ns := by
  cases ns with
  | none => rfl
  | some n => by_cases h : n.isEmpty <;> simp [normalizeNamespace, h]

/-- Infra の HTML namespace。 -/
def htmlNamespace : String := "http://www.w3.org/1999/xhtml"

/-- Infra の XML namespace。 -/
def xmlNamespace : String := "http://www.w3.org/XML/1998/namespace"

/-- Infra の XMLNS namespace。 -/
def xmlnsNamespace : String := "http://www.w3.org/2000/xmlns/"

/--
最初の U+003A (`:`) で分ける。colon が無ければ `none`。

`splitOn` は colon ごとに分けるので、二個目以降は後半に戻す。
-/
def splitAtFirstColon (s : String) : Option (String × String) :=
  match s.splitOn ":" with
  | [] => none
  | [_] => none
  | p :: rest => some (p, String.intercalate ":" rest)

/--
DOM Standard §1.3 valid element local name。

ASCII alpha で始まるなら、ASCII whitespace / U+0000 / `/` / `>` を含まなければよい。
そうでなければ、先頭が `:` / `_` / U+0080 以上で、続きが
ASCII alphanumeric / `-` / `.` / `:` / `_` / U+0080 以上であること。
-/
def isValidElementLocalName (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: rest =>
    if (('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')) then
      (c :: rest).all fun x =>
        !isAsciiWhitespace x && x.toNat != 0x00 && x != '/' && x != '>'
    else if c == ':' || c == '_' || c.toNat ≥ 0x80 then
      rest.all fun x =>
        ('a' ≤ x && x ≤ 'z') || ('A' ≤ x && x ≤ 'Z') || ('0' ≤ x && x ≤ '9') ||
          x == '-' || x == '.' || x == ':' || x == '_' || x.toNat ≥ 0x80
    else false

/--
DOM Standard §1.3 "validate and extract" の step 6 と step 8-11。

prefix の検査（step 4.3）を終えた後の検査をまとめる。
切り出してあるのは、失敗の条件を単体で述べられるようにするためである。
-/
def validateAndExtractError (validLocalName : String → Bool)
    («namespace» «prefix» : Option String)
    (localName qualifiedName : String) : Option DOMException :=
  -- step 6。context が "attribute" か "element" かで local name の条件が違う。
  if !validLocalName localName then some .invalidCharacterError
  -- step 8
  else if «prefix».isSome && «namespace».isNone then some .namespaceError
  -- step 9
  else if «prefix» == some "xml" && «namespace» != some xmlNamespace then some .namespaceError
  -- step 10
  else if (qualifiedName == "xmlns" || «prefix» == some "xmlns") &&
      «namespace» != some xmlnsNamespace then some .namespaceError
  -- step 11
  else if «namespace» == some xmlnsNamespace &&
      !(qualifiedName == "xmlns" || «prefix» == some "xmlns") then some .namespaceError
  else none

/-- step 8。検査を通ったなら、prefix があるところには namespace もある。 -/
theorem validateAndExtractError_prefix {valid : String → Bool}
    {«namespace» «prefix» : Option String}
    {localName qualifiedName : String}
    (h : validateAndExtractError valid «namespace» «prefix» localName qualifiedName = none)
    (hs : «prefix».isSome = true) : «namespace».isSome = true := by
  cases hns : «namespace» with
  | some _ => rfl
  | none =>
    exfalso
    subst hns
    unfold validateAndExtractError at h
    split at h
    · simp at h
    · rw [if_pos (by simp [hs])] at h
      simp at h

/-!
## step 8-11 が名前に課すもの

"validate and extract" の step 8-11 を、返す (namespace, prefix, local name) の組の性質として書く。

* prefix があるなら namespace もある（step 8）。
* prefix が `xml` なら namespace は XML namespace（step 9）。
* prefix が `xmlns` なら namespace は XMLNS namespace（step 10 の後半）。
* namespace が XMLNS namespace で prefix が無いなら、local name は `xmlns`（step 11）。

入れていないものが二つある。

* step 10 の前半（qualified name が `xmlns` なら XMLNS namespace）。`setAttribute("xmlns", …)` は
  "validate and extract" を通らず、namespace が null で local name が `xmlns` の attribute を作る。
  これは仕様どおりで、状態の性質としては成り立たない。
* step 11 のうち prefix がある場合（XMLNS namespace なら prefix は `xmlns`）。これを返り値の
  性質として示すには「colon を含む qualified name は `xmlns` でない」が要るが、
  `String.splitOn` は kernel で評価できず、model はその補題を持たない。
-/

/-- "validate and extract" の step 8-11 が保証する、namespace と prefix の対応。 -/
structure NamespaceWellFormed («namespace» «prefix» : Option String) (localName : String) :
    Prop where
  prefixHasNamespace : «prefix».isSome = true → «namespace».isSome = true
  xmlPrefix : «prefix» = some "xml" → «namespace» = some xmlNamespace
  xmlnsPrefix : «prefix» = some "xmlns" → «namespace» = some xmlnsNamespace
  xmlnsNamespace : «namespace» = some xmlnsNamespace → «prefix» = none → localName = "xmlns"

/-- `NamespaceWellFormed` の検査。loader が初期状態に使う。 -/
def namespaceWellFormedB («namespace» «prefix» : Option String) (localName : String) : Bool :=
  decide ((«prefix».isSome = true → «namespace».isSome = true) ∧
    («prefix» = some "xml" → «namespace» = some xmlNamespace) ∧
    («prefix» = some "xmlns" → «namespace» = some xmlnsNamespace) ∧
    («namespace» = some xmlnsNamespace → «prefix» = none → localName = "xmlns"))

theorem namespaceWellFormedB_iff {«namespace» «prefix» : Option String} {localName : String} :
    namespaceWellFormedB «namespace» «prefix» localName = true ↔
      NamespaceWellFormed «namespace» «prefix» localName := by
  unfold namespaceWellFormedB
  rw [decide_eq_true_iff]
  exact ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun h => ⟨h.1, h.2, h.3, h.4⟩⟩

/--
step 6-11 を通ったなら、名前の組は `NamespaceWellFormed` を満たし、
qualified name が `xmlns` なら XMLNS namespace にある（step 10 の前半）。

`hln` は「prefix が無ければ local name は qualified name そのもの」（step 3-4）。
-/
theorem validateAndExtractError_wellFormed {valid : String → Bool}
    {«namespace» «prefix» : Option String} {localName qualifiedName : String}
    (h : validateAndExtractError valid «namespace» «prefix» localName qualifiedName = none)
    (hln : «prefix» = none → localName = qualifiedName) :
    NamespaceWellFormed «namespace» «prefix» localName ∧
      (qualifiedName = "xmlns" → «namespace» = some xmlnsNamespace) := by
  unfold validateAndExtractError at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i h8
      split at h
      · simp at h
      · rename_i h9
        split at h
        · simp at h
        · rename_i h10
          split at h
          · simp at h
          · rename_i h11
            simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
              Option.isNone_iff_eq_none, not_and, Classical.not_not] at h8 h9 h10 h11
            refine ⟨⟨fun hs => ?_, fun hp => h9 hp, fun hp => h10 (Or.inr hp), fun hn hp => ?_⟩,
              fun hq => h10 (Or.inl hq)⟩
            · cases hns : «namespace» with
              | some _ => rfl
              | none => exact absurd hns (h8 hs)
            · rw [hln hp]
              apply Classical.byContradiction
              intro hq
              apply h11 hn
              simp [hq, hp]

/--
DOM Standard §1.3 "validate and extract"、context は "attribute"。

step 5 の assert は step 4.3 の分岐から従うので書かない。
返り値は (namespace, prefix, local name)。
-/
def validateAndExtractAttribute («namespace» : Option String) (qualifiedName : String) :
    Except DOMException (Option String × Option String × String) :=
  -- step 2-4.2
  let (pfx, localName) :=
    match splitAtFirstColon qualifiedName with
    | none => ((none : Option String), qualifiedName)
    | some (p, l) => (some p, l)
  -- step 4.3
  if pfx.any (fun p => !isValidNamespacePrefix p) then .error .invalidCharacterError
  else
    -- step 1 の正規化はここで一度だけ行う。
    match validateAndExtractError isValidAttributeLocalName
        (normalizeNamespace «namespace») pfx localName qualifiedName with
    | some e => .error e
    -- step 12
    | none => .ok (normalizeNamespace «namespace», pfx, localName)

/--
DOM Standard §1.3 "validate and extract"、context は "element"。

attribute 版との違いは step 6 の local name の条件だけである。
-/
def validateAndExtractElement («namespace» : Option String) (qualifiedName : String) :
    Except DOMException (Option String × Option String × String) :=
  let (pfx, localName) :=
    match splitAtFirstColon qualifiedName with
    | none => ((none : Option String), qualifiedName)
    | some (p, l) => (some p, l)
  if pfx.any (fun p => !isValidNamespacePrefix p) then .error .invalidCharacterError
  else
    match validateAndExtractError isValidElementLocalName
        (normalizeNamespace «namespace») pfx localName qualifiedName with
    | some e => .error e
    | none => .ok (normalizeNamespace «namespace», pfx, localName)

/--
成功したときの返り値の性質。

* namespace は正規化済みである（step 1）。
* prefix があるなら namespace もある（step 8 がそれ以外を弾く）。

二つ目は attribute list の鍵の一意性を保つのに要る（`Dom/Validity/Attributes.lean`）。
-/
theorem validateAndExtractAttribute_ok {«namespace» : Option String} {qualifiedName : String}
    {ns' pfx : Option String} {localName : String}
    (h : validateAndExtractAttribute «namespace» qualifiedName = .ok (ns', pfx, localName)) :
    ns' = normalizeNamespace «namespace» ∧ (pfx.isSome → ns'.isSome) := by
  unfold validateAndExtractAttribute at h
  -- `let (pfx, localName) := match ...` の分解、step 4.3、step 6-11 の順に分岐を潰す。
  split at h
  next =>
    split at h
    · simp at h
    · split at h
      · simp at h
      · next hnone =>
        have he := Except.ok.inj h
        simp only [Prod.mk.injEq] at he
        obtain ⟨e1, e2, _⟩ := he
        subst e1; subst e2
        exact ⟨rfl, fun hs => validateAndExtractError_prefix hnone hs⟩

/-- step 3-4 で切り出した (prefix, local name) は、prefix が無ければ qualified name そのもの。 -/
private theorem split_local {qualifiedName : String} {pfx : Option String} {localName : String}
    (h : (match splitAtFirstColon qualifiedName with
      | none => ((none : Option String), qualifiedName)
      | some (p, l) => (some p, l)) = (pfx, localName)) :
    pfx = none → localName = qualifiedName := by
  intro hp
  split at h
  · exact ((Prod.mk.inj h).2).symm
  · rw [hp] at h; simp at h

/--
**"validate and extract"（attribute）が返す名前の組は `NamespaceWellFormed` を満たす。**

qualified name が `xmlns` なら XMLNS namespace にあることも言う（step 10 の前半）。
-/
theorem validateAndExtractAttribute_wellFormed {«namespace» : Option String}
    {qualifiedName : String} {ns' pfx : Option String} {localName : String}
    (h : validateAndExtractAttribute «namespace» qualifiedName = .ok (ns', pfx, localName)) :
    ns' = normalizeNamespace «namespace» ∧ NamespaceWellFormed ns' pfx localName ∧
      (qualifiedName = "xmlns" → ns' = some xmlnsNamespace) ∧
      isValidAttributeLocalName localName = true := by
  unfold validateAndExtractAttribute at h
  split at h
  next pfx₀ ln₀ hsplit =>
    split at h
    · simp at h
    · split at h
      · simp at h
      · next hnone =>
        have he := Except.ok.inj h
        simp only [Prod.mk.injEq] at he
        obtain ⟨e1, e2, e3⟩ := he
        subst e1; subst e2; subst e3
        obtain ⟨hw, hx⟩ := validateAndExtractError_wellFormed hnone (split_local hsplit)
        refine ⟨rfl, hw, hx, ?_⟩
        unfold validateAndExtractError at hnone
        split at hnone
        · simp at hnone
        · rename_i h6; simpa using h6

/-- **"validate and extract"（element）も同じ。** local name の条件だけが違う。 -/
theorem validateAndExtractElement_wellFormed {«namespace» : Option String}
    {qualifiedName : String} {ns' pfx : Option String} {localName : String}
    (h : validateAndExtractElement «namespace» qualifiedName = .ok (ns', pfx, localName)) :
    ns' = normalizeNamespace «namespace» ∧ NamespaceWellFormed ns' pfx localName ∧
      (qualifiedName = "xmlns" → ns' = some xmlnsNamespace) ∧
      isValidElementLocalName localName = true := by
  unfold validateAndExtractElement at h
  split at h
  next pfx₀ ln₀ hsplit =>
    split at h
    · simp at h
    · split at h
      · simp at h
      · next hnone =>
        have he := Except.ok.inj h
        simp only [Prod.mk.injEq] at he
        obtain ⟨e1, e2, e3⟩ := he
        subst e1; subst e2; subst e3
        obtain ⟨hw, hx⟩ := validateAndExtractError_wellFormed hnone (split_local hsplit)
        refine ⟨rfl, hw, hx, ?_⟩
        unfold validateAndExtractError at hnone
        split at hnone
        · simp at hnone
        · rename_i h6; simpa using h6

end Dom
