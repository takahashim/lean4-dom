/-!
# `DOMException` と、WebIDL の exception

PLAN §3.4。失敗しうる algorithm は `Except DOMException` を返す。

WebIDL の exception は、`DOMException` か、ECMAScript の error を表す simple exception（`TypeError` ほか）である。
`TypeError` は `DOMException` ではないので、`DOMException` の constructor には入れない。
`TypeError` を投げるのは、method を呼ぶ層（`Dom/Exec/Invoke.lean`）の WebIDL の検査
（this の interface、引数の変換）と、仕様の method steps 自身が "throw a TypeError" と書く所
（`MutationObserver.observe` の step 3-6）だけである。それらは `IdlException` を返す。

例外の種類は differential testing の比較対象に含める。
Dommy がどの例外を投げるかまで model と一致させるため、
仕様および WPT で使われる名前を `name` として持たせる。
-/

namespace Dom

/-- DOM Standard §3.3 の `DOMException` のうち、本 model が投げうるもの。 -/
inductive DOMException where
  | hierarchyRequestError
  | notFoundError
  | indexSizeError
  | invalidNodeTypeError
  | wrongDocumentError
  /-- §5.5 `compareBoundaryPoints(how, …)` の `how` が四つの定数のどれでもない場合。 -/
  | notSupportedError
  /-- §4.9 の attribute 名検査。valid attribute local name / valid namespace prefix。 -/
  | invalidCharacterError
  /-- §4.9 の namespace 検査（"validate and extract" の step 7-10）。 -/
  | namespaceError
  /-- §4.9 "set an attribute" step 2。別の element に付いている `Attr` を渡した場合。 -/
  | inUseAttributeError
  /-- §1.3 "scope-match a selectors string" step 2。selector を読めなかった場合。 -/
  | syntaxError
  /--
  model の対象外。**仕様の例外ではない。**

  `DOMString` は UTF-16 の code unit 列なので surrogate pair を割った切り出しも定義されるが、
  Lean の `Char` は surrogate を含まないので `String` では表せない。
  その切り出しを求められた操作はこれを返す。

  名前を `__` で始めてあるのは、仕様の例外名と衝突させないためである。
  差分テストはこの印が出た step 以降を比較しない。
  実装がたまたま同じところで失敗しても、それは仕様適合の証拠にならない。
  -/
  | outsideModel
deriving DecidableEq, Repr, Inhabited

namespace DOMException

/-- 仕様および WPT で使われる名前。 -/
def name : DOMException → String
  | hierarchyRequestError => "HierarchyRequestError"
  | notFoundError => "NotFoundError"
  | indexSizeError => "IndexSizeError"
  | invalidNodeTypeError => "InvalidNodeTypeError"
  | wrongDocumentError => "WrongDocumentError"
  | notSupportedError => "NotSupportedError"
  | invalidCharacterError => "InvalidCharacterError"
  | namespaceError => "NamespaceError"
  | inUseAttributeError => "InUseAttributeError"
  | syntaxError => "SyntaxError"
  | outsideModel => "__outsideModel__"

end DOMException

instance : ToString DOMException := ⟨DOMException.name⟩

/--
WebIDL の exception（§3.14.1）のうち、本 model が投げうるもの。

`dom` は `DOMException`、`typeError` は simple exception の `TypeError` である。
-/
inductive IdlException where
  | dom (e : DOMException)
  | typeError
deriving DecidableEq, Repr, Inhabited

namespace IdlException

/-- 仕様および WPT で使われる名前。`TypeError` は ECMAScript の error の名前である。 -/
def name : IdlException → String
  | dom e => e.name
  | typeError => "TypeError"

end IdlException

instance : ToString IdlException := ⟨IdlException.name⟩

/-- algorithm の結果を、WebIDL の exception を返す層へ持ち上げる。 -/
def liftDom {α : Type} (r : Except DOMException α) : Except IdlException α :=
  match r with
  | .error e => .error (.dom e)
  | .ok a => .ok a

@[simp] theorem liftDom_ok {α : Type} (a : α) : liftDom (.ok a : Except DOMException α) = .ok a := rfl

@[simp] theorem liftDom_error {α : Type} (e : DOMException) :
    liftDom (.error e : Except DOMException α) = .error (.dom e) := rfl

theorem liftDom_eq_ok {α : Type} {r : Except DOMException α} {a : α} :
    liftDom r = .ok a ↔ r = .ok a := by
  cases r <;> simp [liftDom]

end Dom
