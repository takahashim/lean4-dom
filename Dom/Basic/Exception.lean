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
deriving DecidableEq, Repr, Inhabited

namespace DOMException

/-- 仕様および WPT で使われる名前。 -/
def name : DOMException → String
  | hierarchyRequestError => "HierarchyRequestError"
  | notFoundError => "NotFoundError"
  | indexSizeError => "IndexSizeError"
  | invalidNodeTypeError => "InvalidNodeTypeError"
  | wrongDocumentError => "WrongDocumentError"

end DOMException

instance : ToString DOMException := ⟨DOMException.name⟩

end Dom
