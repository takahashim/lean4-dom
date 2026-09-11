# lean4-dom

WHATWG DOM Standard の structural mutation と live object を、
Lean 4 で実行可能に形式化したものである。

対象は node tree と document tree、mutation algorithms、
mutation に追随する live Range、NodeIterator、CharacterData mutation である。
Shadow DOM と Web Components は対象に含めない。

形式化した model は **executable oracle** でもある。
同じ操作列を Ruby の DOM 実装 [Dommy](https://github.com/takahashim/dommy) と
この model の両方で走らせ、観測を突き合わせる差分テストに使っている。

参照する仕様は `docs/spec-version.md` に固定した
[`dom.bs`](https://github.com/whatwg/dom) の commit である。

## 何が示してあるか

十の主定理を `docs/theorems.md` に並べてある。中心は次の三つである。

**妥当な状態は決定可能で、どの操作でも保たれる。**

```lean
theorem Dom.Exec.run_preserves_admissibility :
    ∀ (ops : List Operation) {s s' : DOMState},
      AdmissibleDOMState s → run s ops = .ok s' → AdmissibleDOMState s'
```

`AdmissibleDOMState` は六つの成分の連言である。木の構造、node document、
Document の children の制約、live Range の端点、NodeIterator、observer registration。
`checkAdmissibleDOMState_iff` により boolean の checker と一致するので、
evaluator は実行時に同じ条件を検査できる。

**oracle は自分の invariant を破らない。**

```lean
theorem Dom.Exec.runOperations_no_violation :
    ∀ (ops : List Operation) {s : DOMState} (i : Nat),
      AdmissibleDOMState s → (runOperations s ops i).2 = none
```

evaluator は各 step の後で六成分を実行時に検査する。
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

差分テストで Dommy の仕様不一致を 19 件見つけ、すべて修正につなげた。
一覧は `docs/status.md` にある。例えば次のようなものである。

* `insertBefore` / `replaceChild` が mutation record の挿入点を木が動いた後に読んでいた。
  仕様は insert step 6 と replace step 4、つまり何も動く前の値である。
* remove step 20（transient registered observer）が `suppressObservers` で抑制されていた。
  抑制されるのは step 21 の record だけである。
* `Node.ownerDocument` が Element と Attr にしか実装されていなかった。
* live range の挿入側の調整が仕様の位置になかった。

model 側の不具合も証明が押し返した。`move` step 5 の `Text` 判定が CDATASection を
取りこぼしていたこと、`moveBefore` に IDL 由来の receiver 検査が無かったことなどである。

## 使い方

```sh
# 証明を検査して oracle を build する
lake build

# 公開主定理の axiom audit（sorryAx や独自 axiom があれば失敗する）
lake env lean Audit.lean

# 固定 scenario を loader に通し、invariant 違反が無いことを検査する
lake exe dom-model --check test/scenarios

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
| `Dom/Range/`, `Dom/Traversal/`, `Dom/CharacterData/`, `Dom/Observer/` | live object と CharacterData と MutationObserver の record |
| `Dom/Properties/` | 効果・frame・契約・反例 |
| `Dom/Validity/` | `AdmissibleDOMState` とその保存 |
| `Dom/Observation.lean` | 差分テストの比較対象を型で固定する |
| `Dom/Exec/` | scenario の読み書きと evaluator |
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
3. 比較対象に入れていないものがある（object identity、UTF-16 の code unit 境界、
   MutationObserver の配送、attribute、Shadow tree）。
   `Dom/Observation.lean` に列挙してある。

## ライセンス

MIT。`LICENSE` を参照。
