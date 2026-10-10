# Threats to validity

この形式化から何が言えて何が言えないかを、先に並べておく。

## 1. 形式化の対象が仕様と一致している保証は無い

Lean の定義が WHATWG DOM Standard を正しく写しているかは、形式的には示せない。
定義が仕様と違えば、定理はすべて「違う仕様」についての定理になる。

**緩和。**

* `docs/traceability.md` が algorithm ごとに step 要約と `dom.bs` の固定 commit を記録する。
* `Trace/Dom/` の対応表が、固定 commit の `dom.bs` の algorithm を一つ残らず「表に載せる」か
  「理由付きで対象外」に分け、表に載せた algorithm の step を「実装」「近似」「除外」に分ける。
  CI がその網羅を検査し、週次の job が仕様の改訂で変わった step を挙げる（`docs/spec-version.md`、
  集計は `docs/spec-coverage.md`）。ただし「実装」と書いた step が本当にその step のことをしているかは、
  表を書いた人の読みである。
* 固定 scenario が normative branch ごとに置いてあり、期待結果の根拠（`_basis`）を持つ。
* Dommy との差分テストが、独立に書かれた実装との一致を有限の trace で確かめる。

**残る危険。** 三つとも「仕様を読んだ人間」を経由する。
仕様の読み違いが Lean と固定 scenario の両方に入れば検出できない。
第三の根拠（WPT の期待結果、主要ブラウザでの観測）は一部にしか付いていない。

## 2. 差分テストは observational equivalence を示さない

Dommy との一致は **有限の生成 trace 上の観測の一致** である。
一般の観測等価性を証明したものではない。

**残る危険。** 生成器が到達しない状態や操作列に不一致があっても分からない。
現在の生成器は node 8 個・操作 6 個前後を中心に振っており、
深い木や長い操作列、複数 document をまたぐ操作は薄い。

## 3. 比較対象に入れていないものがある

`Dom/Observation.lean` が比較対象を型で固定している。入れていないのは次である。

| 項目 | 理由 |
| --- | --- |
| wrapper の object identity | 作った node の同一性は id で比べられるようになったが、JS/Ruby の wrapper そのものの同一性は観測していない。実装が同じ node に別の wrapper を返すと id が引けず不一致に出る、という形で間接的にしか見えない |
| `Attr` の node としての性質（parent・node document・`Attr` を tree order に置くこと） | model の attribute は element の状態で node tree に入らない。`createAttribute` / `getAttributeNode` / `setAttributeNode` / `removeAttributeNode` / `removeNamedItem` と同一性（`AttrId`）は扱う |
| lone surrogate | offset と長さは UTF-16 の code unit で数えるが、surrogate pair を割った切り出しは Lean の `Char` で表せない。その操作は `__outsideModel__` を返し、比較から外れる。Dommy も同じところで断るが、それは仕様適合の証拠にならない |
| MutationObserver の callback 本体 | callback は model の外。どの observer にどの record が配送されるかまでは比べる |
| `NodeFilter` の callback | 同じく callback なので filter は常に null。`whatToShow` は純粋なので扱う |
| 名前で消した attribute | 仕様の "remove an attribute" は element を null にするだけで `Attr` object は残る。model は `removeAttribute` などで消した `Attr` を持たず、`removeAttributeNode` など呼び出し側に返るものだけを `detachedAttrs` に持つ。**先に `getAttributeNode` で参照を取ってから名前で消すと、仕様と観測が食い違う**（`Attr` が見つからない。値を書くと NotFoundError、同じ element への `setAttributeNode` が TypeError になる。仕様ではどちらも成功する）。`removeAttributeNS`・`toggleAttribute`・boolean の reflect の setter・dataset の削除も同じ経路を通る |
| Dommy の DOMString と boolean の変換 | Dommy の WebIDL の変換は JS の実行環境の側にあり、Ruby の runner は通らない。文字列でない値を DOMString の引数に、真偽値でない値を boolean の引数に書いた step と、`importNode` の options は、Dommy とは比べず、jsdom とブラウザとだけ比べる |
| Shadow tree | 対象外 |
| custom element / insertion steps / removing steps | hook の位置だけを保っている |

比較していない部分に不一致があっても、この harness では見つからない。

**node の生成は比較対象に入れた。** §4.5 の factory・§4.4 の `cloneNode`・
§4.5 の `importNode` / `adoptNode` は、runner が model の `freshId` と同じ規則
（木にある id の最大より一つ大きいもの、deep な clone は tree order）で
作った node に id を振ることで比べている。

生成 scenario もこれらを作る。ただし **必ず成功する形だけ**である。
作った node の id は「木にある id の最大より一つ大きいもの」なので、
失敗すると生成器の予測が実際とずれ、以降の操作が別の node を指してしまう。
名前の検査に落ちる形と、`deep` な clone / import のあとの生成は出さない。

**残る危険。** runner は HTML document しか作れないので、`createElement` の
step 2（ASCII lowercase）と step 4（HTML namespace）が効かない側（XML document）は
比べていない。名前の検査に落ちる形も固定 scenario の範囲だけである。

## 4. model 側の既知の近似

| 近似 | 影響 |
| --- | --- |
| `move` step 1 は shadow-including root ではなく root で判定する | shadow tree を含む木では仕様と違う。対象外なので実害は無い |
| 参照されなくなった node を状態から消す | "convert nodes into a node" が作った DocumentFragment は挿入の後で空になり、どこからも参照されない。JavaScript では観測できないので、model は parent・children・attribute を持たず live object や record から指されていない node を消す（`Dom.discard`）。仕様は object の寿命を定めないので、これは仕様の step ではなく、観測の範囲を JavaScript から辿れるものに合わせる約束である |
| WebIDL の層は、model が扱う member の検査と変換だけである | method を呼ぶ層（`Dom/Exec/Invoke.lean` の `idlCheck` と `Dom/Exec/Eval.lean` の `invokeOperation`）は、this が method を持つ interface を実装するか、`Range` の `Node` 引数が null でないか、`setAttributeNode` の引数が `Attr` かを検査し、`TypeError` を `DOMException` とは別の型（`IdlException.typeError`）で返す。TypeError になりうる変換（`addEventListener`・`observe`・`importNode` の options）もこの層で行う。TypeError を投げず副作用も無い変換（DOMString、boolean、整数型の ToNumber）は scenario を読むときに行う。DOMString への変換がそうであることは証明してあるが（`Idl.toDOMString_error`）、変換の位置が method の呼び出しの外にあることは関係の側では述べていない。scenario の JSON の object は自分のプロパティだけを持つ object として、配列は組み込みの `Array` として読むので、getter や prototype の上の member、上書きした `@@iterator`・`toString`・`valueOf` は表せない。整数型の引数は JavaScript と同じく倍精度に丸めてから ConvertToInt で変換し、有効数字が 20 桁を超える十進表記（丸めが実装に任される）は受けない。数の ToString は有効数字 15 桁以下の数に限る（それを超えると十進の値から倍精度の最短表記を決められない）。AbortSignal と CustomElementRegistry は無いので、undefined でない `signal` と `customElementRegistry` は常に TypeError になる。overload の選択は model に無い。interface の判定は node の kind で行う |
| `NodeStore` は association list | 性能ではなく証明の都合。`keys` に重複が無いことは構造では保証していない（`observe` は id で正規化して吸収する） |
| IDNA / UTS #46 は**相対的な保証**である | 写像表の正しさは証明していない。`IdnaTable.Resolved` を仮定に置き、実行時に `checkResolved` で検査する。NFC・Bidi・Joiner の code point は誤って扱うのではなく `none` で弾く（`outOfModel`）。**安全側に限定した model であって、UTS #46 適合ではない** |
| `insertAt` の guard が仕様より厳しい | 仕様は「`child` は `parent` の子」を `pre-insert` の validity（step 3）に置き、`move` の側には置いていない。model は primitive 側に置くので、`move` を `child = node` で呼ぶと仕様（先頭に入れる）と違って `notFoundError` になる。**差が観測できないことは散文ではなく検査で押さえてある**——`Dom.moveBefore_reference_ne` と `ruby test/callsites.rb`（`move` を呼ぶ実行定義は `moveBefore` だけ） |
| UTF-8 の復元規則は手で書いた関係との一致である | 不正な byte 列への U+FFFD の置き方（maximal subpart ごとに一つ）は `Infra/Spec/Utf8Decode.lean` の `Chunk` / `Decodes` に書き、`utf8Decode_spec` と `Decodes.eq_utf8Decode_iff` で `utf8Decode` がそれに一致することを示した。ただし `Chunk` を Encoding Standard の state machine と突き合わせたのは手作業で、WPT の `encoding/` は当てていない |
| CSS tokenizer は手で書いた関係との一致である | `Selectors/Spec/Token.lean` の関係を CSS Syntax §3.3・§4 から書き写し、`TokenizesInput.iff_tokenize` で `tokenize` がそれに一致することを示した。関係と本文の突き合わせは手作業で、WPT の `css/css-syntax/` は当てていない。生成器の selector は固定の語彙から組み立てるので、escape や comment の組み合わせは語彙にある形に限られる |
| selector の照合は手で書いた関係との一致である | `Dom/Spec/SelectorMatch.lean` の `SelectorListMatches` ほかを Selectors §3・§6・§14・§16・§17 から書き写し、`matchSelList_iff_spec` で `matchSelList` がそれに一致することを示した。前提は `WellFormed` と `AttributesValid`（attribute の組の一意性）である。関係と本文の突き合わせは手作業で、状態の pseudo-class（`:hover` ほか）は対象外のまま |
| selector の文法は手で書いた関係との一致である | `Selectors/Spec/Scan.lean` の `SelListRel` ほかを Selectors §18・§19.1 から書き写し、`parseSelector_spec` で `parseSelector` がそれに一致することを示した。文法は model の範囲（namespace prefix は `*|` だけ、pseudo-element 無し）に合わせてあるので、範囲の外の selector についての本文との一致は言っていない |

## 5. 「実装の不一致」の判定

差分テストで不一致が出たとき、どちらが仕様と違うかは自動では決まらない。
これまでの判定はすべて `dom.bs` の該当 step を手で追って行っており、
WPT やブラウザでの確認は付けていない。

**oracle は Lean の model だけである。** 実装を複数並べても多数決はしない。
model が仕様の翻訳として正しいかは別に担保するもの（関係意味論と soundness、
`docs/traceability.md` の step 対応）であって、実装の同意で決めるものではない。

**残る危険。** 仕様の読み違いがあれば、正しい実装を「不一致」として直してしまう。
実装側の修正には spec の URL と step を commit message に残してあるので、後から検証できる。

findings 19・20（`docs/status.md` の「findings 19・20 の見直し」）はこの危険の
外側にある第三の形を見せた。19 は「仕様の読み違い」ではなく、**仕様の本文が
自分自身の適合テストと矛盾したまま揺れている**場合で、csswg-drafts の issue が
open のままであることでしか見分けられない。20 は逆に、実装と WPT のほうが
csswg の撤回済みの読みで止まっている場合だった。どちらも `docs/traceability.md`
の step 対応や `dom.bs` を読むだけでは出てこず、csswg-drafts の issue tracker と
WPT の commit 履歴を当たって初めて分かった。

## 6. 証明の検査

`lake build` が通り、`sorry` が無く、公開主定理が
`propext` / `Classical.choice` / `Quot.sound` 以外の axiom に依存しないことは CI で確認している。
Lean 4 の kernel と `decide` の正しさは前提とする。

`exists_insert_breaking_boundaryLE` は `decide` を使うが `native_decide` は使わない。
つまり kernel が評価しており、コンパイラを信頼していない。

## 7. 再現性

`test/pinned-versions.json` が dom.bs の commit、Dommy の commit、makiri の version、
Ruby と Lean の toolchain を固定する。
差分テストの CI は Dommy の checkout と native gem の build を要するので、
`lake build` の CI とは分けてある。

**残る危険。** makiri は native 拡張を持つので、build 環境によって挙動が変わりうる。
RubyGems の公開版を使うことを `test/pinned-versions.json` に明記してある
（ローカル build のものだと `Makiri::Document#create_document_type` を持たないことがある）。
