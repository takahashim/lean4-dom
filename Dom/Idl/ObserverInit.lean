import Dom.Idl.Value
import Dom.Observer.Deliver

/-!
# JavaScript の値を `MutationObserverInit` に変換する

```webidl
dictionary MutationObserverInit {
  boolean childList = false;
  boolean attributes;
  boolean characterData;
  boolean subtree = false;
  boolean attributeOldValue;
  boolean characterDataOldValue;
  sequence<DOMString> attributeFilter;
};
```

WebIDL の dictionary への変換（§3.2.17）は次のとおりである。

1. 値が undefined、null、object のどれでもなければ TypeError。
2. member を辞書順に読む。各 member は、値が null か undefined なら undefined とみなし、そうでなければ
   `Get` で読む。undefined でなければ member の型へ変換し、undefined なら既定値を使う。既定値が無ければ
   member は存在しない。

辞書順では `attributeFilter` が最初で、変換が失敗しうるのはこの member だけである（boolean への変換は
失敗しない）。
-/

namespace Dom.Idl

/-- **JavaScript の値を `MutationObserverInit` に変換する。** -/
def toMutationObserverInit (v : JsValue) : Except IdlException MutationObserverInit :=
  match v with
  | .undefined | .null | .object _ | .array _ => do
    let filterValue := v.get "attributeFilter"
    let attributeFilter ←
      if filterValue.isUndefined then pure none else some <$> toSequenceDOMString filterValue
    pure { attributeFilter
           attributeOldValue := boolMember? v "attributeOldValue"
           attributes := boolMember? v "attributes"
           characterData := boolMember? v "characterData"
           characterDataOldValue := boolMember? v "characterDataOldValue"
           childList := boolMember v "childList" false
           subtree := boolMember v "subtree" false }
  | .bool _ | .number _ | .string _ => .error .typeError

/-! ## 例 -/

#guard (toMutationObserverInit (.object [("childList", .number ⟨1, 0⟩), ("attributes", .null)])).toOption ==
  some { childList := true, attributes := some false }
#guard (toMutationObserverInit (.object [("attributeFilter", .array [.number ⟨15, 1⟩, .null])])).toOption ==
  some { attributeFilter := some ["1.5", "null"] }
#guard (toMutationObserverInit (.object [("attributeFilter", .null)])).toOption == none
#guard (toMutationObserverInit (.object [("attributeFilter", .string "id")])).toOption == none
#guard (toMutationObserverInit (.bool true)).toOption == none

end Dom.Idl
