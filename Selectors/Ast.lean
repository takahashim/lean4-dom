import Selectors.Token

/-!
# selector の構文木（Selectors Level 4 §18）

`docs/selectors-spec-version.md` に書いた範囲だけを持つ。namespace prefix と
pseudo-element は構文木に無い。`ns|E` は parse に失敗する。
-/

namespace Selectors

/-- §16 の combinator。 -/
inductive Combinator where
  /-- 空白。 -/
  | descendant
  /-- `>` -/
  | child
  /-- `+` -/
  | nextSibling
  /-- `~` -/
  | subsequentSibling
deriving DecidableEq, Repr, Inhabited

/-- §6.3 の attribute 照合の演算子。 -/
inductive AttrOp where
  /-- `=` -/
  | exact
  /-- `~=` 空白区切りの語のどれか。 -/
  | includes
  /-- `|=` 値そのものか、`-` を挟んで始まる。 -/
  | dashMatch
  /-- `^=` 前方一致。 -/
  | prefixMatch
  /-- `$=` 後方一致。 -/
  | suffixMatch
  /-- `*=` 部分一致。 -/
  | substring
deriving DecidableEq, Repr, Inhabited

/-- §6.3.3 の `i` / `s` flag。 -/
inductive AttrCase where
  /-- flag 無し。document の言語が決める。 -/
  | byDocument
  /-- `i` -/
  | insensitive
  /-- `s` -/
  | sensitive
deriving DecidableEq, Repr, Inhabited

/-- attribute selector の値の側。 -/
structure AttrTest where
  op : AttrOp
  value : String
  case : AttrCase
deriving DecidableEq, Repr, Inhabited

/-- CSS Syntax §9 の `<a-n-plus-b>`。 -/
structure AnB where
  a : Int
  b : Int
deriving DecidableEq, Repr, Inhabited

/-- `:nth-*()` の四種。 -/
inductive NthKind where
  | child
  | lastChild
  | ofType
  | lastOfType
deriving DecidableEq, Repr, Inhabited

mutual

/-- §3.1 の simple selector。 -/
inductive Simple where
  /-- type selector `E`。namespace は持たない。 -/
  | typeSel (name : String)
  /-- `*`。 -/
  | univ
  /-- `#id`。 -/
  | id (v : String)
  /-- `.class`。 -/
  | cls (v : String)
  /--
  `[name]` と `[name op value flag]`。

  `anyNs` は `[*|name]`、つまり namespace を問わないこと。
  素の `[name]` は namespace を持たない attribute だけに当たる（§6.3）。
  -/
  | attr (name : String) (anyNs : Bool) (test : Option AttrTest)
  | root
  | empty
  | firstChild
  | lastChild
  | onlyChild
  | firstOfType
  | lastOfType
  | onlyOfType
  /-- `:nth-child(An+B of S)` ほか。`of S` は `:nth-of-type()` では持てない。 -/
  | nth (kind : NthKind) (ab : AnB) (ofSel : Option (List Complex))
  | isSel (l : List Complex)
  | whereSel (l : List Complex)
  | notSel (l : List Complex)
  /-- `:has()`。引数は anchor を先頭に置いた形に直してある。 -/
  | has (l : List Complex)
  /-- `:scope`。照合の scoping root を指す。 -/
  | scope
  /--
  relative selector の先頭に暗黙に置かれる anchor。

  構文には無い。`:has()` の引数を「`anchor` から始まる complex selector」に
  直すときだけ現れる。`:scope` とは別物で、`:has()` の外側の scoping root ではなく
  `:has()` を付けた element を指す。
  -/
  | anchor
deriving Repr, Inhabited

/--
§3.1 の complex selector。**右端の compound を先頭に持つ。**

照合は右から進む（subject が右端だから）ので、この向きだと再帰がそのまま書ける。
`a > b c` は `seq [c] descendant (seq [b] child (one [a]))` になる。
-/
inductive Complex where
  /-- compound 一つだけ。 -/
  | one (c : List Simple)
  /-- `left comb c`。`c` が subject 側。 -/
  | seq (c : List Simple) (comb : Combinator) (left : Complex)
deriving Repr, Inhabited

end

/-- §3.1 の compound selector。空でない `Simple` の並び。 -/
abbrev Compound := List Simple

/-- §3.1 の selector list。 -/
abbrev SelectorList := List Complex

end Selectors
