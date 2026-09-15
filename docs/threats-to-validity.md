# Threats to validity

`notes/research-foundation-roadmap.md` §12 と §13。

この形式化から何が言えて何が言えないかを、先に並べておく。

## 1. 形式化の対象が仕様と一致している保証は無い

Lean の定義が WHATWG DOM Standard を正しく写しているかは、形式的には示せない。
定義が仕様と違えば、定理はすべて「違う仕様」についての定理になる。

**緩和。**

* `docs/traceability.md` が algorithm ごとに step 要約と `dom.bs` の固定 commit を記録する。
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
| wrapper の object identity | model は node を生成しないので、wrapper を作る API の同一性は観測できない。node を返す method の戻り値は `NodeId` で比べる |
| `Attr` の identity | attribute は element の状態であって object ではない |
| lone surrogate | offset と長さは UTF-16 の code unit で数えるが、surrogate pair を割った切り出しは Lean の `Char` で表せない。その操作は `__outsideModel__` を返し、比較から外れる。Dommy も同じところで断るが、それは仕様適合の証拠にならない |
| MutationObserver の callback 本体 | callback は model の外。どの observer にどの record が配送されるかまでは比べる |
| `NodeFilter` の callback | 同じく callback なので filter は常に null。`whatToShow` は純粋なので扱う |
| `Attr` を node として扱う API | model の attribute は element の状態で、node tree に入らない |
| node の生成 | model は §4.5 の factory と §4.4 の `cloneNode` を持つが、harness の比較対象には入れていない。scenario の element の namespace と local name は初期状態が与える |
| Shadow tree | 対象外 |
| custom element / insertion steps / removing steps | hook の位置だけを保っている |

比較していない部分に不一致があっても、この harness では見つからない。

## 4. model 側の既知の近似

| 近似 | 影響 |
| --- | --- |
| `move` step 1 は shadow-including root ではなく root で判定する | shadow tree を含む木では仕様と違う。対象外なので実害は無い |
| `convert nodes into a node` は呼び出し側で済ませた形で受け取る | `x.replaceWith(x)` のような「変換が node を動かす」場合を model 側で再現できない |
| WebIDL の TypeError を `DOMException` と同じ型で扱う | `moveBefore` と attribute の method の receiver、`observe` の options、`Range` の `Node` 引数がこれに当たる。名前は "TypeError" で一致するが、実際には `DOMException` ではない |
| `NodeStore` は association list | 性能ではなく証明の都合。`keys` に重複が無いことは構造では保証していない（`observe` は id で正規化して吸収する） |

## 5. 「実装の不一致」の判定

差分テストで不一致が出たとき、どちらが仕様と違うかは自動では決まらない。
これまでの判定はすべて `dom.bs` の該当 step を手で追って行っており、
WPT やブラウザでの確認は付けていない。

**oracle は Lean の model だけである。** 実装を複数並べても多数決はしない。
model が仕様の翻訳として正しいかは別に担保するもの（関係意味論と soundness、
`docs/traceability.md` の step 対応）であって、実装の同意で決めるものではない。

**残る危険。** 仕様の読み違いがあれば、正しい実装を「不一致」として直してしまう。
実装側の修正には spec の URL と step を commit message に残してあるので、後から検証できる。

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
