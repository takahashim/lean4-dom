import Trace.Basic
import Dom

/-!
# §1 Infrastructure（ordered sets・selectors・name validation）
-/

namespace Trace.Dom.Infra

open Trace

def entries : List Entry := [
  { alg := "concept-ordered-set-parser"
    impl := [``Dom.orderedSetParse, ``Dom.splitWsAux]
    spec := [``Dom.Spec.ClassToken]
    approx := [("2-3", "ordered set を List String で持ち、`eraseDups` で後から重複を落とす（最初の出現を残すので append を繰り返したのと同じ列）")] },
  { alg := "concept-ordered-set-serializer"
    impl := [``Dom.tokenListUpdate]
    approx := [("*", "専用の関数は無く、DOMTokenList の update steps（`tokenListUpdate`）の中で `\" \".intercalate` として書いている")] },
  { alg := "scope-match-a-selectors-string"
    impl := [``Dom.scopeMatch, ``Dom.matchTree, ``Selectors.parseSelector, ``Dom.matchSelList]
    -- step 3 の "match a selector against a tree" は、root ではなく node の部分木を列挙する。
    -- 結果が Selectors §17 の定義と列として等しいことは `ScopeMatchResult` の sound と complete。
    spec := [``Dom.Spec.ScopeMatchResult, ``Dom.Spec.MatchAgainstTree, ``Dom.Spec.SelectorListMatches]
    approx := [("1", "parse a selector は model の selector 文法（`parseSelector` が受け付ける部分集合）で行う。受け付けない構文は failure（SyntaxError）になる")] },
  { alg := "valid-namespace-prefix"
    impl := [``Dom.isValidNamespacePrefix] },
  { alg := "valid-attribute-local-name"
    impl := [``Dom.isValidAttributeLocalName] },
  { alg := "valid-element-local-name"
    impl := [``Dom.isValidElementLocalName] },
  { alg := "validate-and-extract"
    impl := [``Dom.validateAndExtractAttribute, ``Dom.validateAndExtractElement,
             ``Dom.validateAndExtractError, ``Dom.splitAtFirstColon, ``Dom.normalizeNamespace]
    spec := [``Dom.Spec.validateAndExtractSteps, ``Dom.Spec.validateAndExtractAttribute_eq_steps,
             ``Dom.Spec.validateAndExtractElement_eq_steps]
    omitted := [("5", .other "assert。step 4.3 の分岐から従うので検査しない")] }
]

def exclusions : List Exclusion := []

end Trace.Dom.Infra
