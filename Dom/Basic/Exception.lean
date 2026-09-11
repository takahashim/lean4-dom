/-!
# `DOMException`

PLAN §3.4。失敗しうる操作は `Except DOMException` を返す。

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
  /-- §4.9 の attribute 名検査。valid attribute local name / valid namespace prefix。 -/
  | invalidCharacterError
  /-- §4.9 の namespace 検査（"validate and extract" の step 7-10）。 -/
  | namespaceError
  /--
  WebIDL の `TypeError`。`DOMException` ではないが、
  仕様が例外として投げ分けるので同じ型で扱う。

  `MutationObserver.observe` の options 検査と、
  `moveBefore` の receiver が `ParentNode` でない場合に使う。
  -/
  | typeError
  /--
  model の対象外。**仕様の例外ではない。**

  `DOMString` は UTF-16 の code unit 列なので surrogate pair を割った切り出しも定義されるが、
  Lean の `Char` は surrogate を含まないので `String` では表せない（roadmap §13.1）。
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
  | invalidCharacterError => "InvalidCharacterError"
  | namespaceError => "NamespaceError"
  | typeError => "TypeError"
  | outsideModel => "__outsideModel__"

end DOMException

instance : ToString DOMException := ⟨DOMException.name⟩

end Dom
