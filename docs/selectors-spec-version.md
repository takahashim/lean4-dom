# Selectors の形式化が参照する仕様の版

| 仕様 | 版 | repository | file | commit |
| --- | --- | --- | --- | --- |
| Selectors Level 4 | Editor's Draft, 2026-07-30 | `w3c/csswg-drafts` | `selectors-4/Overview.bs` | `c282dbebe51162f438dcafa1a1d77634f366a6e3` |
| CSS Syntax Level 3 | Editor's Draft, 2026-07-30 | `w3c/csswg-drafts` | `css-syntax-3/Overview.bs` | `f971255463f01fb740e2a3a7ecfe83e319cddab9` |

* Selectors 本文：https://drafts.csswg.org/selectors-4/
* CSS Syntax 本文：https://drafts.csswg.org/css-syntax-3/

DOM Standard 側の版は `docs/spec-version.md` にある。
`querySelector()` ほかの接続部分は DOM §4.2.6 "Interface `ParentNode`" から入る。

## 形式化の範囲

selector は CSS 全体の一部なので、どこまでを model に入れるかを先に決めてある。

### 入れるもの

* selector list（`,` 区切り）と complex selector、四つの combinator（` ` `>` `+` `~`）
* type selector `E`・universal `*`・`*|E`
* `#id`・`.class`
* attribute selector `[attr]` と六つの演算子（`=` `~=` `|=` `^=` `$=` `*=`）、`i`/`s` flag
* 構造 pseudo-class：`:root` `:empty` `:first-child` `:last-child` `:only-child`
  `:first-of-type` `:last-of-type` `:only-of-type`
  `:nth-child()` `:nth-last-child()` `:nth-of-type()` `:nth-last-of-type()`（`of S` を含む）
* 論理 pseudo-class：`:is()` `:where()` `:not()` `:has()`
  （§14.10 のとおり `:has()` は入れ子にできない。`:is()` を挟めば forgiving に落ちる）
* `:scope`

### 入れないもの

* **利用者側の状態に依る pseudo-class**（`:hover` `:focus` `:checked` `:visited` ほか）。
  node tree だけからは決まらない。
* **pseudo-element**（`::before` ほか）。`querySelector()` は元から一致させない。
  ただし仕様では **構文としては正しい**ので、実装は例外を投げずに空を返す。
  model は parse に失敗させるので、そこは観測できる違いになる。
  `:hover` のような状態の pseudo-class も同じである。
  受け付けて「決して当たらない」に直すには、仕様が定める名前の一覧が要る。
  その一覧は CSS と HTML にまたがって動くので、いまは範囲の外に置いてある。
* **namespace prefix `ns|E`**。DOM Standard は `ParentNode` の API に namespace を
  「加えない」と明言しており、prefix を宣言する手段が無い。よって常に parse に失敗する。
* **quirks mode**。model の document は quirks mode を持たない。

`tokenize` が仕様と違えてある点は `Selectors/Token.lean` 冒頭に列挙してある。
