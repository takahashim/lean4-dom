import Dom.Basic.Exception

/-!
# 名前の検査と namespace の切り出し

DOM Standard §1.3 "Name validation" と "validate and extract"。

attribute を扱うために要るのは次の三つである。

* valid namespace prefix
* valid attribute local name
* validate and extract（context は "attribute"）

valid element local name は element の local name を model が持たないので扱わない。
-/

namespace Dom

/-- Infra の ASCII whitespace。TAB / LF / FF / CR / SPACE。 -/
def isAsciiWhitespace (c : Char) : Bool :=
  c.toNat == 0x09 || c.toNat == 0x0A || c.toNat == 0x0C || c.toNat == 0x0D || c.toNat == 0x20

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
DOM Standard §1.3 "validate and extract" の step 6 と step 8-11。

prefix の検査（step 4.3）を終えた後の検査をまとめる。
切り出してあるのは、失敗の条件を単体で述べられるようにするためである。
-/
def validateAndExtractError («namespace» «prefix» : Option String)
    (localName qualifiedName : String) : Option DOMException :=
  -- step 6
  if !isValidAttributeLocalName localName then some .invalidCharacterError
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
theorem validateAndExtractError_prefix {«namespace» «prefix» : Option String}
    {localName qualifiedName : String}
    (h : validateAndExtractError «namespace» «prefix» localName qualifiedName = none)
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
    match validateAndExtractError (normalizeNamespace «namespace») pfx localName qualifiedName with
    | some e => .error e
    -- step 12
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

end Dom
