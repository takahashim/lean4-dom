# lean4-dom

WHATWG の仕様を Lean 4 で実行可能に形式化したものである。
いまのところ **DOM Standard** と **URL Standard** が入っている。

形式化した model は **executable oracle** でもある。
同じ入力を Ruby の実装 [Dommy](https://github.com/takahashim/dommy) と
この model の両方で走らせ、観測を突き合わせる差分テストに使っている。

## DOM Standard

対象は node tree と document tree、mutation algorithms、
mutation に追随する live Range、NodeIterator、CharacterData mutation、
element の attribute、MutationObserver（record と配送）である。
Shadow DOM と Web Components は対象に含めない。

参照する仕様は `docs/spec-version.md` に固定した
[`dom.bs`](https://github.com/whatwg/dom) の commit である。

## URL Standard

対象は percent-encoding、IPv4 / IPv6 parser、host parser、basic URL parser、
`application/x-www-form-urlencoded`、`URL` の getter と setter、`URLSearchParams` である。
IDNA（UTS #46）は仕様自身が別仕様へ委譲しているので、
`hostParser` が ToASCII を引数で受け取る形にして境界を引いた。

DOM と違って状態を持たない純関数なので、中心の定理も
「操作列に沿った invariant の保存」ではなく
「parser の停止性」と「結果の record の妥当性」になる。
state machine は fuel ではなく `(state の順位, 残りの文字数, 位相)` の
辞書式測度で停止性を示してある。
期待値は WPT の `urltestdata.json` と `setters_tests.json` がそのまま使える
（`--wpt` で 820 件中 816 件一致、`--setters` で 699 件の属性比較が一致。
残りは IDNA が要るので対象外で、その印は fixture に書いてある）。
詳しくは `docs/url-status.md` と `docs/url-traceability.md`。

## 共有している部分

ASCII の判定、大文字小文字、byte 列と UTF-8 は Infra Standard のもので、
`Infra/` に置いて両方から使う。差分の相手（Dommy）も、CI も、axiom 監査も一つで済む。

## 何が示してあるか

十の主定理を `docs/theorems.md` に並べてある。中心は次の三つである。

**妥当な状態は決定可能で、どの操作でも保たれる。**

```lean
theorem Dom.Exec.run_preserves_admissibility :
    ∀ (ops : List Operation) {s s' : DOMState},
      AdmissibleDOMState s → run s ops = .ok s' → AdmissibleDOMState s'
```

`AdmissibleDOMState` は七つの成分の連言である。木の構造、node document、
Document の children の制約、live Range の端点、NodeIterator、observer registration、
element の attribute list。
`checkAdmissibleDOMState_iff` により boolean の checker と一致するので、
evaluator は実行時に同じ条件を検査できる。

**oracle は自分の invariant を破らない。**

```lean
theorem Dom.Exec.runOperations_no_violation :
    ∀ (ops : List Operation) {s : DOMState} (i : Nat),
      AdmissibleDOMState s → (runOperations s ops i).2 = none
```

evaluator は各 step の後で七成分を実行時に検査する。
admissible な初期状態から始めればこの検査は決して発火しない。
`invariantViolation` が出たら model の algorithm ではなく harness を疑えばよい。

**`insert` は live Range の start ≤ end を保たない。**

```lean
theorem Dom.exists_insert_breaking_boundaryLE :
    ∃ s s' parent node child r r', ...
      BoundaryLE s.tree r.start r.«end» ∧
      insertBefore s parent node (some child) = .ok s' ∧
      ¬ BoundaryLE s'.tree r'.start r'.«end»
```

insert step 5（parent を指す offset の `+count`）は step 7 の adopt → remove より前に走る。
動かす node の中にあった boundary point は step 7 で `(旧 parent, 旧 index)` に出るが、
その時点で step 5 の `+count` はもう済んでいる。
node 自身はその位置より前に入るので、start と end が逆転する。
自然に期待される invariant が現行仕様の property ではないことを示す negative result である。
反例は具体的に構成してあり、証明は `decide` だけを使う（`native_decide` は使わない）。

## 何を見つけたか

差分テストで仕様との不一致を見つけ、修正につなげた。
`docs/status.md` に通し番号 1-27 で並べてある。
25 件が Dommy 側、2 件（番号 9 と 27）が model 側である。例えば次のようなものである。

* `insertBefore` / `replaceChild` が mutation record の挿入点を木が動いた後に読んでいた。
  仕様は insert step 6 と replace step 4、つまり何も動く前の値である。
* remove step 20（transient registered observer）が `suppressObservers` で抑制されていた。
  抑制されるのは step 21 の record だけである。
* `Node.ownerDocument` が Element と Attr にしか実装されていなかった。
* live range の挿入側の調整が仕様の位置になかった。
* MutationObserver の通知順が、仕様の inclusive ancestor の walk ではなく observer の生成順だった。
* その record type を要求していない registration が、同じ observer の要求している registration を隠していた。
* attribute を qualified name ではなく local name で引いていたため、`xml:b` を持つ element で
  `setAttribute("b", v)` が別の attribute を足さずに `xml:b` を上書きしていた。
* Document を parent とする `replaceChild` に DocumentFragment の分岐が無く、
  fragment の children が取り出されないままだった。

証明も model 側の不具合を押し返した。`move` step 5 の `Text` 判定が CDATASection を
取りこぼしていたこと、`moveBefore` に IDL 由来の receiver 検査が無かったことである。
どちらも差分テストでは出ず、`AdmissibleDOMState` の保存を示そうとして初めて分かった。

## 使い方

```sh
# 証明を検査して oracle を build する
lake build

# 公開主定理の axiom audit（sorryAx や独自 axiom があれば失敗する）
lake env lean Audit.lean

# 固定 scenario を loader に通し、invariant 違反が無いことを検査する
lake exe dom-model --check test/scenarios

# URL 側を WPT の期待値表に通す
lake exe url-model --wpt test/url/wpt-ascii.json
lake exe url-model --setters test/url/wpt-setters.json
lake exe url-model --searchparams test/url/wpt-searchparams-sort.json

# 一つの scenario を評価して観測を JSON で出す
lake exe dom-model test/scenarios/basic-insert-remove.json
```

差分テストの走らせ方は `test/README.md` にある。
Dommy と makiri が要るので `lake build` の CI とは分けてある。

## 構成

| path | 内容 |
| --- | --- |
| `Dom/Basic/` | node tree、`WellFormed`、`DOMState` |
| `Dom/Mutation/` | §4.2.3 の algorithm と public API |
| `Dom/Range/`, `Dom/Traversal/`, `Dom/CharacterData/`, `Dom/Attribute/`, `Dom/Observer/` | live object、CharacterData、attribute、MutationObserver（record と配送） |
| `Dom/Properties/` | 効果・frame・契約・反例 |
| `Dom/Validity/` | `AdmissibleDOMState` とその保存 |
| `Dom/Observation.lean` | 差分テストの比較対象を型で固定する |
| `Dom/Exec/` | scenario の読み書きと evaluator |
| `Infra/` | 共有する語彙（ASCII、byte 列、UTF-8、UTF-16 の code unit）。`Dom` と `Url` が使う |
| `Url/` | URL Standard（percent-encoding、IPv4 / IPv6、host parser、basic URL parser、urlencoded、`URL` と `URLSearchParams` の IDL） |
| `test/` | 固定 scenario、生成器、Dommy runner、比較器 |
| `docs/` | 状況、主定理の一覧、仕様トレーサビリティ、threats to validity |

## 依存

Lean 4 のみ。Mathlib も Batteries も使わない。
必要な補題は `Dom/Util/List.lean` に自前で置いてある。
`Lean.Data.Json` は `Dom/Exec/` と `Audit.lean` に閉じている。

## 限界

`docs/threats-to-validity.md` に並べてある。要点は三つである。

1. Lean の定義が仕様を正しく写している保証は形式的には無い。
   トレーサビリティと差分テストで緩和しているが、仕様の読み違いは検出できない。
2. 差分テストは **有限の生成 trace 上の観測の一致** であり、
   一般の observational equivalence ではない。
3. 比較対象に入れていないものがある（wrapper の object identity、lone surrogate、
   MutationObserver の callback 本体、`Attr` の identity、Shadow tree）。
   `Dom/Observation.lean` に列挙してある。

## ライセンス

MIT。`LICENSE` を参照。
