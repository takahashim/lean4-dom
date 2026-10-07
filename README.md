# lean4-dom

WHATWG および CSS WG の仕様を Lean 4 で実行可能に形式化したモデルである。
現時点では **DOM Standard**、**URL Standard**、**CSS Selectors** を対象としている。

本モデルは実行可能なオラクル（executable oracle）でもある。
同じ入力を Ruby による実装 [Dommy](https://github.com/takahashim/dommy) と本モデルの両方で実行し、それぞれの観測結果を突き合わせる差分テスト（differential testing）に利用している。

## DOM Standard

対象範囲は、node tree、document tree、mutation algorithms、mutation に追随する live Range、NodeIterator、TreeWalker、CharacterData mutation、element の attribute、MutationObserver（record とその配送）、event の配送、および `querySelector()` 等の selector API である。なお、Shadow DOM および Web Components は対象外としている。

参照する仕様は、`docs/spec-version.md` にて特定のコミットに固定した [`dom.bs`](https://github.com/whatwg/dom) である。

## URL Standard

対象範囲は、percent-encoding、IPv4 / IPv6 parser、host parser、basic URL parser、`application/x-www-form-urlencoded`、`URL` の getter / setter、および `URLSearchParams` である。
IDNA（UTS #46）については、仕様自体が外部仕様へ委譲しているため、`hostParser` が ToASCII を引数として受け取る構造にして境界を明確に区切った。

DOM とは異なり状態を持たない純粋関数であるため、検証の中心となる定理も「操作列に沿った不変量（invariant）の保持」ではなく、「parser の停止性」および「生成される record の妥当性」となる。
State machine の停止性証明では fuel を使わず、`(state の順位, 残りの文字数, 位相)` による辞書式測度を用いている。
期待値テストには WPT（Web Platform Tests）の `urltestdata.json` および `setters_tests.json` を直接利用できる
（`--wpt` で 820 件中 816 件が一致、`--setters` で 699 件の属性比較が一致。残る未一致分は IDNA を要するため対象外としており、fixture 内にその旨を明記している）。
詳細は `docs/url-status.md` および `docs/url-traceability.md` を参照されたい。

## CSS Selectors

対象範囲は、Selectors Level 4 のうち node tree の情報のみで判定可能な部分である。
selector list、4 種の combinator、type / universal / id / class / attribute の各種 selector、構造 pseudo-class、`:is()` / `:where()` / `:not()` / `:has()`、および `:scope` を実装している。
また、解析に必要な範囲で CSS Syntax Level 3（tokenizer および component value）も含めている。
なお、利用者の状態に依存する pseudo-class（`:hover` など）、pseudo-element、namespace prefix は含めていない。
範囲外の構文を parse 失敗として扱う設計は、仕様の §17.2 の指示に準拠したものである。

tokenizer、文法、照合処理のそれぞれについて、仕様本文から書き写した関係意味論（relational semantics）と実際の実行関数が一致することを証明している
（`Selectors.Spec.TokenizesInput.iff_tokenize`、`Selectors.Spec.parseSelector_spec`、`Dom.Spec.matchSelList_iff_spec`）。
`querySelector()` 等の API は `Dom/Selector/` に配置されており、DOM の差分テストに組み込まれている。
比較対象には Dommy に加えて jsdom も使用している。
参照仕様のバージョンおよび対象範囲は `docs/selectors-spec-version.md` に、検出された不一致は `docs/status.md` の Selectors の節に記載している。

## 共通基盤

ASCII 判定、大文字・小文字処理、および byte 列の扱いは Infra Standard に、UTF-8 の符号化・復号は Encoding Standard にそれぞれ準拠しており、これらは `Infra/` 配下に配置して DOM と URL の双方から共通で利用している。これにより、比較対象（Dommy）や CI 環境、および axiom 監査を一元化している。

## 証明されている内容

主な定理は `docs/theorems.md` にまとめている。中心となるのは以下の 3 つである。

#### 1. 妥当な状態は決定可能であり、任意の操作において保持される

```lean
theorem Dom.Exec.run_preserves_admissibility :
    ∀ (ops : List Operation) {s s' : DOMState},
      AdmissibleDOMState s → run s ops = .ok s' → AdmissibleDOMState s'
```

`AdmissibleDOMState` は 7 つの構成要素からなる連言である（木の構造、node document、Document の children 制約、live Range の端点、NodeIterator、observer registration、element の attribute list）。
`checkAdmissibleDOMState_iff` によって論理式と boolean の判定関数（checker）の同値性が示されているため、評価器は実行時に同じ条件を正確に検証できる。

#### 2. オラクルは自らの不変量を破壊しない

```lean
theorem Dom.Exec.runOperations_no_violation :
    ∀ (ops : List Operation) {s : DOMState} (i : Nat),
      AdmissibleDOMState s → (runOperations s ops i).2 = none
```

評価器は各ステップの実行後に 7 つの構成要素を実行時に検査する。
妥当な（admissible な）初期状態から開始した場合、この検査が違反を検知して発火することは決してない。
万が一 `invariantViolation` が発生した場合は、モデル側のアルゴリズムではなくテストハーネス側を疑うべきであることが保証される。

#### 3. `insert` 操作は live Range の `start ≤ end` 条件を維持しない（反例の証明）

```lean
theorem Dom.exists_insert_breaking_boundaryLE :
    ∃ s s' parent node child r r', ...
      BoundaryLE s.tree r.start r.«end» ∧
      insertBefore s parent node (some child) = .ok s' ∧
      ¬ BoundaryLE s'.tree r'.start r'.«end»
```

insert の step 5（parent を指す offset の `+count`）は、step 7（adopt → remove）よりも先に実行される。
移動対象の node 内にあった boundary point は step 7 の時点で `(旧 parent, 旧 index)` に移動するが、その時点ですでに step 5 の `+count` 補正が完了してしまっている。
node 自体はその位置より手前に挿入されるため、結果として start と end の位置関係が逆転する。
これは「直感的に期待される不変量が、現行の仕様上は必ずしも成立しない」ことを示す否定的な結果（negative result）である。
反例は具体的に構成されており、証明には `decide` のみを用い、`native_decide` は一切使用していない。

## 検出された不具合・不一致

差分テストを実施した結果、仕様との不一致やバグを検出し、修正につなげることができた。
検出事例は `docs/status.md` に通し番号 1〜27 として記録している。
25 件は Dommy 側、2 件（番号 9 および 27）はモデル側の不具合であった。主な事例は以下の通りである。

* `insertBefore` / `replaceChild` が、mutation record の挿入位置を「木構造が変更された後」の状態で参照していた（正しくは insert step 6 および replace step 4 の通り、変更前の値を用いる必要がある）。
* remove step 20（transient registered observer）が `suppressObservers` によって誤って抑制されていた（仕様上抑制されるのは step 21 の record のみである）。
* `Node.ownerDocument` が Element と Attr にしか実装されていなかった。
* live range の挿入に伴う位置調整処理が、仕様で定められた位置に存在しなかった。
* MutationObserver の通知順序が、仕様にある inclusive ancestor の走査順ではなく、observer の生成順になっていた。
* 当該 record type を要求していない registration が、同一 observer の要求している他の registration を覆い隠して（遮蔽して）しまっていた。
* attribute の取得に qualified name ではなく local name を用いていたため、`xml:b` を保持する element に対して `setAttribute("b", v)` を実行した際、新しい attribute が追加されずに既存の `xml:b` が上書きされていた。
* Document を parent とする `replaceChild` において DocumentFragment 向けの分岐が抜け落ちており、fragment の children が正しく展開されていなかった。

また、形式証明の過程においてもモデル側の不具合を特定・修正できた（`move` step 5 の `Text` 判定で CDATASection の考慮が漏れていた点や、`moveBefore` に IDL 由来の receiver チェックが不足していた点など）。
これらは差分テストのみでは検出できず、`AdmissibleDOMState` の保持を証明しようとする過程で初めて判明したものである。

## 使い方

```sh
# 証明を検証し、オラクルをビルドする
lake build

# 主定理の axiom 監査（sorryAx や独自の未検証 axiom が含まれている場合は失敗する）
lake env lean Audit.lean

# 固定のシナリオを loader に渡し、不変量（invariant）違反がないか検査する
lake exe dom-model --check test/scenarios

# URL 仕様モデルを WPT の期待値データに対して実行する
lake exe url-model --wpt test/url/wpt-ascii.json
lake exe url-model --setters test/url/wpt-setters.json
lake exe url-model --searchparams test/url/wpt-searchparams-sort.json

# 単一の URL をパースし、IDL attribute・origin・URL record を JSON 形式で出力する
# （パース失敗時は終了コード 1。非 ASCII ドメインの解析には --idna test/url/uts46-table.json が必要）
lake exe url-model --parse "../x?y" --base "https://example.com/a/b"

# 単一のシナリオを評価し、実行観測結果を JSON 形式で出力する
lake exe dom-model test/scenarios/basic-insert-remove.json
```

差分テストの詳しい実行方法については `test/README.md` を参照されたい。
実行には Dommy および makiri が必要なため、`lake build` を行う通常の CI パイプラインとは分離されている。

## ディレクトリ構成

| パス | 内容 |
| --- | --- |
| `Dom/Basic/` | node tree、`WellFormed`、`DOMState` の定義 |
| `Dom/Mutation/` | §4.2.3 のアルゴリズムおよび public API |
| `Dom/Range/`, `Dom/Traversal/`, `Dom/CharacterData/`, `Dom/Attribute/`, `Dom/Observer/` | live object、CharacterData、attribute、MutationObserver（record とその配送） |
| `Dom/Event/` | event の配送処理（§2.9） |
| `Dom/Query/`, `Dom/Selector/` | 副作用のない参照系メソッド、id・class・name による検索、selector の照合処理および `querySelector()` 等の API |
| `Dom/Spec/` | 仕様本文から独立して書き写した関係意味論と、実行関数がそれを満たすことの証明 |
| `Dom/Util/` | 自前で実装した `List` 関連の補題 |
| `Dom/Properties/` | 副作用・frame・契約・反例の証明 |
| `Dom/Validity/` | `AdmissibleDOMState` の定義と状態保持の証明 |
| `Dom/Observation.lean` | 差分テストにおける比較対象のデータ型定義 |
| `Dom/Exec/` | シナリオの型と評価（`Types` / `Eval`）、JSON 入出力（`Json`）、その実行エントリーポイント（`Scenario`） |
| `Infra/` | 共通語彙（ASCII、byte 列、UTF-8 エンコード/デコード、UTF-16 code unit）。`Dom` および `Url` から参照 |
| `Selectors/` | Selectors Level 4 および CSS Syntax Level 3 のうち selector 解析に必要な範囲（tokenizer、構文木、parser）。仕様バージョンは `docs/selectors-spec-version.md` に記載 |
| `Url/` | URL Standard（percent-encoding、IPv4 / IPv6、host parser、basic URL parser、urlencoded、`URL` および `URLSearchParams` の IDL） |
| `test/` | 固定シナリオ、テスト生成器、Dommy 用ランナー、比較器 |
| `docs/` | プロジェクトの状況、主要な定理一覧、仕様トレーサビリティ、検証上の限界（threats to validity） |

## 依存関係

Lean 4 のみに依存しており、Mathlib や Batteries 等の外部ライブラリは使用していない。
必要な補題はすべて `Dom/Util/List.lean` および `Infra/List.lean` 内に自前で定義している。
なお、`Lean.Data.Json` への依存は `Dom/Exec/Json.lean`、`UrlMain.lean`、`Audit.lean` のみに局所化されている。
操作列の型定義および評価処理は `Dom/Exec/Types.lean` と `Dom/Exec/Eval.lean` に配置されており、状態遷移の証明自体が入出力フォーマットに依存しない構造になっている。

## 本モデルの限界（Limitations）

詳細な限界事項は `docs/threats-to-validity.md` にまとめている。主な要点は以下の 3 点である。

1. Lean による定義が仕様を完全かつ正しく反映できているかについての形式的な保証はない。仕様トレーサビリティの確保や差分テストによってリスクを緩和しているが、根本的な仕様の誤読を自動検出することはできない。
2. 差分テストで確認できているのは「有限の生成トレース上における観測結果の一致」であり、一般的な観測等価性（observational equivalence）を保証するものではない。
3. 比較対象から意図的に除外している要素が存在する（wrapper の object identity、lone surrogate、MutationObserver の callback 本体、`Attr` の node としての性質、Shadow tree など）。詳細は `docs/threats-to-validity.md` §3 を参照されたい。

## ライセンス

[MIT](./LICENSE)
