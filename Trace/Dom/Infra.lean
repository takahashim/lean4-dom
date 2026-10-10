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
    spec := [``Dom.Spec.SelectorListMatches]
    approx := [("1", "parse a selector は model の selector 文法（`parseSelector` が受け付ける部分集合）で行う。受け付けない構文は failure（SyntaxError）になる"),
               ("3", "root の全 element ではなく node の descendant element だけを候補にする（scoping root が node なので、それ以外は scoping で落ちるという前提。node 自身は候補に入れない）")] },
  { alg := "valid-namespace-prefix"
    impl := [``Dom.isValidNamespacePrefix] },
  { alg := "valid-attribute-local-name"
    impl := [``Dom.isValidAttributeLocalName] },
  { alg := "valid-element-local-name"
    impl := [``Dom.isValidElementLocalName] },
  { alg := "validate-and-extract"
    impl := [``Dom.validateAndExtractAttribute, ``Dom.validateAndExtractElement,
             ``Dom.validateAndExtractError, ``Dom.splitAtFirstColon, ``Dom.normalizeNamespace]
    omitted := [("5", .other "assert。step 4.3 の分岐から従うので検査しない")]
    approx := [("1", "namespace の正規化（空文字列を null に）を step 4.3 の後で一度だけ行う。step 1-4 の間で namespace は読まないので結果は同じ"),
               ("6-7", "context の代わりに attribute 版と element 版の二つの関数を持ち、local name の検査関数だけを差し替える")] }
]

def exclusions : List Exclusion := []

end Trace.Dom.Infra
