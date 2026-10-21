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
  （§14.10 のとおり `:has()` は入れ子にできない。`:is()` を挟めば forgiving に落ちる）。
  `:is()` と `:where()` の引数は `<forgiving-selector-list>` で、構文上は `<any-value>?` である。
  読めない項目を捨てるのはそのあとなので、bad-string-token・bad-url-token・対応しない
  `)` `]` `}` を引数に含むと、項目ではなく selector 全体が無効になる
  （`is-argument-must-be-any-value.json`・`is-argument-bad-string-is-invalid.json`）
* `:scope`。`Document` や `DocumentFragment` を受け手にすると、scoping root は featureless な
  virtual scoping root になる。§3.3 "Featureless Elements" のとおり、そこに当たりうるのは
  `:scope`、当たりうる引数を持つ `:is()` `:where()` `:not()`、同じ compound に当たりうる
  他の simple selector がある `:has()` と、それらだけからなる compound である。
  `:is(:scope) > *` や `:scope:has(.foo) > *` は当たり、`:not(.foo) > *` の `:not(.foo)` は
  引数が当たりえないので virtual scoping root には当たらない
  （`featureless-virtual-root-logical-combinations.json`）。読み方の細部は
  `Dom/Selector/Match.lean` の "featureless な node に当たりうる selector" の節にある
* CSS Syntax の tokenizer は `<url-token>` と `<bad-url-token>` を含めて本文どおりに作る
  （§4.3.4・§4.3.6・§4.3.14）。selector の文法はどちらも受け付けないが、`:is()` の中では
  token の切り方が結果を変える（`url-token-in-forgiving-list.json`・
  `bad-url-token-makes-is-invalid.json`）
* `<an+b>` は CSS Syntax §9.2 の文法どおりで、`'+'` を前に置けるのは `n`・`n-`・
  `n-*` で始まる形だけである。`:nth-child(+-n+3)` は無効になる（`anb-plus-only-before-n.json`）

### 入れないもの

* **利用者側の状態に依る pseudo-class**（`:hover` `:focus` `:checked` `:visited` ほか）。
  node tree だけからは決まらない。
* **pseudo-element**（`::before` ほか）。`querySelector()` は元から一致させない。

### 範囲外のものを model がどう扱うか

§17.2 "Invalid Selectors and Error Handling" は、

> UAs **must** treat as invalid any pseudo-classes, pseudo-elements, combinators,
> or other syntactic constructs for which they have no usable level of support.

と定める。だから範囲外の構文を parse に失敗させるのは、**仕様が指示している扱い**である
（model という UA の対応水準がそこまでだ、ということ）。

観測できる違いが出るのは、それを forgiving でない位置に置いたときだけである。

| selector | model | 実装 |
| --- | --- | --- |
| `:is(p, :hover)` | `p` に当たる | `p` に当たる |
| `:is(:hover)` | 何にも当たらない | 何にも当たらない |
| `p:hover` | `SyntaxError` | 何にも当たらない |
| `:not(p, :hover)` | `SyntaxError` | `p` 以外に当たる |

前の二つが一致するのは、forgiving な list が読めない項目を捨てるからで、
実装の側も「対応しているが当たらない」ので同じ結果になる。
`test/scenarios/unsupported-pseudo-class-inside-is.json` がそこを見ている。
* **namespace prefix `ns|E`・`ns|*`・`[ns|att]`**。DOM Standard は `ParentNode` の API に
  namespace を「加えない」と明言しており、prefix を宣言する手段が無い。§17.2 は
  "a simple selector containing an undeclared namespace prefix is invalid" と定めるので、
  常に parse に失敗する。これは仕様どおりである。
* **空の namespace prefix `|E`・`|*`・`[|att]`**。こちらは宣言を要さない。本文の意味は
  「namespace を持たない E」「namespace を持たない element」「namespace を持たない attribute
  `att`」（`[|att]` は `[att]` と同じ）である。**model はこれらを読まず、parse に失敗する。**
  上の `ns|E` と違って仕様が無効と定めているわけではないので、これは model の範囲の制限であり、
  本文どおりに受理する実装とは結果が食い違う（model は SyntaxError を返す）。
  model が読む namespace prefix は `*|E`・`*|*`・`[*|att]` だけである。
* **quirks mode は class と id にだけ効く**。HTML §"Case-sensitivity of selectors" のとおり、
  element の node document が quirks mode なら class selector と id selector を ASCII
  case-insensitive に比べる。limited-quirks mode は no-quirks mode と同じである。

`tokenize` が仕様と違えてある点は `Selectors/Token.lean` 冒頭に列挙してある。
