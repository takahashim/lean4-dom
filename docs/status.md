# 実装状況

## Phase 1（tree model）— 完了

`PLAN.md` §4 の定義と theorem をすべて実装し、`sorry` なしで build が通る。
`lake exe dom-model` で小さな木に対する走査が動く。

### 実装した定義

| 定義 | module |
| --- | --- |
| `NodeId`, `NodeKind`, `NodeData`, `NodeData.length` | `Dom/Basic/NodeId.lean` |
| `NodeStore`（`get?`, `insert`, `erase`, `keys`, `size`, `mapValues`, `modify`）とその補題 | `Dom/Basic/Store.lean` |
| `Tree`, `parentOf`, `childrenOf`, `kindOf`, `ownerDocumentOf`, `lengthOf`, `Ancestor`, `InclusiveAncestor`, `Descendant`, `InclusiveDescendant`, `Sibling`, `index` | `Dom/Basic/Tree.lean` |
| `rootFuel`, `root`, `ancestorChain`, `ancestors`, `depth`, `preorderFuel`, `preorder`, `treeOrder`, `precedesIn`, `precedes`, `parentChainTerminates` | `Dom/Basic/Order.lean` |
| `WellFormed`, `checkWellFormed` とその構成要素 | `Dom/Basic/WellFormed.lean` |

### 証明した theorem（`Dom/Properties/Tree.lean`）

PLAN §4.2 の各項目との対応は次のとおり。

| PLAN §4.2 | theorem |
| --- | --- |
| `WellFormed` から parent の一意性が導ける | `unique_parent` |
| `root` は fuel が store の要素数以上なら停止して結果を返す | `rootFuel_parent_eq_none` |
| `root t n` は `n` の inclusive ancestor であり、parent を持たない | `root_inclusive_ancestor`, `root_parent_eq_none`, `root_unique` |
| `Ancestor` は推移的かつ非反射的である | `Ancestor.trans_ancestor`, `ancestor_irrefl`, `ancestor_asymm` |
| `preorder` は重複を持たず inclusive descendant をちょうど列挙する | `mem_preorder_iff`, `preorder_nodup` |
| `precedes` は `preorder` の順序と一致する | `precedesIn_iff_idx`, `precedes_iff_idx`, `precedes_of_ancestor` |
| `checkWellFormed` の健全性と完全性 | `checkWellFormed_iff` |

これらは `propext` / `Classical.choice` / `Quot.sound` 以外の axiom に依存しない
（`#print axioms` で確認済み。`sorryAx` は現れない）。

Phase 2 以降で再利用する補題として、次のものも用意した。

- `mem_childrenOf_of_parentOf` / `parentOf_of_mem_childrenOf` — parent と children の対応
- `ancestor_linear` / `inclusive_ancestor_linear` — 祖先の線形性
- `sibling_subtrees_disjoint` — 相異なる兄弟の部分木は交わらない
- `Ancestor.exists_child` — ancestor 関係を上端で分解する
- `depth_lt_size` / `depth_parent` — 深さの性質
- `exists_data_root` / `exists_data_of_parentOf` — root と parent が木に含まれること

## PLAN からの変更点

- **`NodeStore` の表現**（PLAN §3.1）。PLAN は `Std.HashMap NodeId NodeData` を挙げているが、
  実際には association list で実装した。Phase 1 の成果物は証明であり、
  必要な補題（`get?_insert_ne` など）を外部 library の API 名に依存せず自前で証明できるほうが
  toolchain 更新に強いためである。
  PLAN が意図したとおり、model と theorem は `Store.lean` の interface だけを通して store に触れるので、
  `Std.HashMap` へ差し替える場合も同じ statement の補題を用意すれば済む。
- **依存 library**（PLAN §2.1）。`Batteries` は導入していない。
  Phase 1 で必要だった補題は Lean core と `Dom/Util/List.lean` の自前の補題で足りた。
- **追加した定義**。PLAN §4.1 に無いが、証明の都合で `ancestorChain` と `depth` を導入した。
  `depth` は `preorder` の正しさを well-founded な減少量で示すために使う。
  `Sibling` は仕様上の概念なので併せて定義した。
- **`NodeId` の `Repr`**。derive せず、識別子の数値だけを表示する instance を手で定義した。
  Phase 4 の oracle 出力を読みやすくするためである。

## Phase 2（primitive mutation）— 完了

`PLAN.md` §5 の定義と theorem を実装し、`sorry` なしで build が通る。

### 実装した定義

| 定義 | module |
| --- | --- |
| `DOMException` とその `name` | `Dom/Basic/Exception.lean` |
| `detachFrom`, `detach` | `Dom/Mutation/Detach.lean` |
| `insertAtIn`, `insertAt` | `Dom/Mutation/Insert.lean` |
| `setOwnerDocument` | `Dom/Mutation/Adopt.lean` |
| `isAncestorOf`, `isInclusiveAncestorOf` | `Dom/Basic/Order.lean` |
| `insertBefore`, `removeAll` などの list 補助 | `Dom/Util/List.lean` |

### 証明した theorem（`Dom/Properties/Mutation.lean`）

PLAN §5.2 が要求する三種類を、三つの primitive すべてについて証明した。

| | preservation | effect | frame |
| --- | --- | --- | --- |
| `detach` | `detach_preserves_wellformed` | `detach_parentOf`, `detach_childrenOf` | `detach_frame` |
| `insertAt` | `insertAt_preserves_wellformed` | `insertAt_parentOf`, `insertAt_childrenOf`, `insertAt_children_split` | `insertAt_frame` |
| `setOwnerDocument` | `setOwnerDocument_preserves_wellformed` | `ownerDocumentOf_setOwnerDocument` | `get?_setOwnerDocument_of_not_mem` |

PLAN §5.3 の完了条件である `detach_preserves_wellformed` と
`insertAt_preserves_wellformed`（`memo.md` の最小 milestone）を含む。
いずれも `propext` / `Classical.choice` / `Quot.sound` 以外の axiom に依存しない。

Phase 3 で使う補題として次のものも用意した。

- `wellFormed_of` — parent と children の一致・重複の無さ・acyclicity・node document から `WellFormed` を組み立てる
- `mem_childrenOf_iff` — `WellFormed` から parent 関係と children 関係の一致を取り出す
- `ownerDocument_is_document_of` — node document と kind を保つ変更は最後の条件を保つ
- `ancestor_of_parentOf_subset` — parent が減る変更では ancestor 関係も減る
- `ancestor_of_parentOf_insert` — parent の辺を一本足したときの ancestor 関係
- `get?_detachFrom` / `get?_insertAtIn` / `get?_setOwnerDocument` — 結果の `get?` の完全な場合分け

## PLAN §5 の見直し（PLAN §14 の指示による）

実際に定義と証明を書いた結果、PLAN §5 について次のことが分かった。

- **`insertAt` の前提条件 4 は invariant のためではない。**
  PLAN §5.1 は四つの前提条件を挙げているが、そのうち
  「child が指定されていれば parent の子である」は well-formedness の保存には要らなかった。
  `insertBefore` は child が見つからなければ末尾に挿入するので、
  検査を省いても木は well-formed のままである。
  したがってこの検査は仕様準拠（`NotFoundError` を投げること）のためのものであり、
  `insertAtIn_preserves_wellformed` はこの前提を取らない。
  Phase 3 で `preInsert` を組み立てるとき、この検査が
  `ensurePreInsertionValidity` と二重にならないか確認する必要がある。
- **`setOwnerDocument` には前提が要る。**
  PLAN §5.1 はこの primitive を無条件の `Tree → Tree` としているが、
  `WellFormed` の `ownerDocument_is_document` を保つには
  「付け替え先 `doc` が document node として木に存在する」という前提が要る。
  Phase 3 の `adopt` では呼び出し側でこれを保証する。
- **`WellFormed` の前二条件は一つの同値にまとめられる。**
  `parent_child` と `child_parent` は
  「`parentOf t c = some p ↔ c ∈ childrenOf t p`」と等価である（`mem_childrenOf_iff`, `wellFormed_of`）。
  PLAN §3.3 の形はそのまま残したうえで、preservation の証明はこの同値を通す。
  三つの primitive すべてでこの形が効いた。
- **`Ancestor` の決定手続きが Phase 2 の時点で必要になった。**
  `insertAt` の前提条件 3（node が parent の inclusive ancestor でない）を計算するため、
  `isAncestorOf` / `isInclusiveAncestorOf` を追加し、
  健全性と完全性（`isAncestorOf_iff`, `isInclusiveAncestorOf_iff`）を示した。
  PLAN §4.1 には無い定義だが、Phase 3 の `ensurePreInsertionValidity` でも使う。
- **children からの除去は `List.erase` ではなく `removeAll` を使った。**
  `List.erase` は最初の一つしか除かないため、重複が無いことを仮定しないと
  「除去後に含まれない」が言えない。すべて除く `removeAll` にすると無条件で言えて証明が短くなる。
  `children_nodup` の下では両者は同じ list である。

## Phase 3（WHATWG の mutation algorithm）— 完了

`PLAN.md` §6 の algorithm と theorem を実装し、`sorry` なしで build が通る。
仕様は `docs/spec-version.md` の版の本文から step を写した。

### 実装した定義

| 定義 | module |
| --- | --- |
| live object 調整の hook（`liveRangePreRemove`, `iteratorPreRemove`, `liveRangeInsertAdjust`） | `Dom/Mutation/Algorithms.lean` |
| `remove`, `removeEach`, `adopt` | 同上 |
| `ensurePreInsertionValidity`（`checkElementInsertion`, `checkDoctypeInsertion`, `childHasParent`） | 同上 |
| `insert`, `insertEach`, `insertEachAt`, `insertNodesAt` | 同上 |
| `preInsert`, `append`, `preRemove`, `replace`, `replaceAll` | 同上 |
| `moveValidity`, `move` | 同上 |
| `nextSibling`, `previousSibling`, `viablePreviousSibling`, `viableNextSibling`, `elementChildren`, `doctypeChildren`, `textChildren`, `doctypeFollows`, `elementPrecedes` | 同上 |
| `appendChild`, `insertBefore`, `replaceChild`, `removeChild`, `replaceChildren`, `before`, `after`, `replaceWith`, `nodeRemove`, `moveBefore` | `Dom/Mutation/Api.lean` |

public API はすべて §4.2.3 の algorithm の薄い wrapper であり、
primitive（`detach`, `insertAt`）を直接呼ばない（PLAN §6.1）。

### 証明した theorem（`Dom/Properties/Algorithms.lean`）

PLAN §6.3 との対応は次のとおり。

| PLAN §6.3 | theorem |
| --- | --- |
| 各 algorithm の preservation | `remove_`, `adopt_`, `insert_`, `preInsert_`, `append_`, `preRemove_`, `replace_`, `replaceAll_`, `move_` + `*_preserves_wellformed`、および public API 10 個ぶん |
| `ensurePreInsertionValidity` が ok なら `insertAt` の前提条件が成り立つ | `ensurePreInsertionValidity_ok`, `insertAt_isOk_of_validity` |
| `insert` の後、node は child の直前にある | `insert_children_split`, `insert_parentOf` |
| `remove` の後、node は parent を持たず旧 parent の children に現れない | `remove_parentOf`, `remove_not_mem_childrenOf` |
| 既存 node の `insert` と `remove` ∘ `insert` の同値 | `insert_factors_through_remove` |
| PLAN §6.2 の `move_equivalent_to_remove_insert` | `move_eq_remove_insertAt`, `moveBefore_eq_remove_insertAt`, `move_childrenOf` |

補助として `KindPreserving` / `IsDocument` を導入した。
`adopt` の preservation には「付け替え先が document node である」ことが要るので、
この前提を algorithm の合成の間じゅう持ち回るために使う。

`lake exe dom-model` で PLAN §6.4 の完了条件を実際に確認できる。
DocumentFragment の展開、および Document の子に対する制約
（element は高々一つ、doctype は高々一つ、doctype より前に element を置けない、Text は不可）が
例外の種類込みで仕様どおりに動く。

## `moveBefore()` の扱い（PLAN §6.2 の宿題）

仕様本文を確認した結果、**model に含めた**。確認した内容は次のとおり。

* 現行の Living Standard には `ParentNode.moveBefore(node, child)` と、
  対応する **`move` algorithm**（§4.2.3）が step 付きで本文に入っている。
  PLAN §6.2 の「仕様本文で step を確認できていない」という保留は解消した。
* `move` は **live range pre-remove steps（step 10）と NodeIterator pre-remove steps（step 11）、
  および挿入側の live range offset 調整（step 16）を走らせる**。
  走らせないのは removing steps と insertion steps だけで、
  これらは他仕様のための拡張点なので本 model の対象外である。
  したがって木・Range・NodeIterator に射影した観測結果は remove と insert の合成と一致する。
* `move` は **node document を付け替えない**。step 1 が
  「newParent の root と node の root が同じ」ことを要求するためである。
  そのため一致するのは `insert`（adopt を含む）ではなく primitive の `insertAt` との合成になる。
  これを `move_eq_remove_insertAt` として証明した。
* validity の検査は `ensure pre-insert validity` とは別物で、step 1-6 の独自のものである
  （同じ root、inclusive ancestor でない、child の parent、node は Element か CharacterData、
  Text を document に入れない、document の子の element/doctype 制約）。
* step 8 の「Assert: oldParent is non-null」は step 1 と step 2 から従う。
  parent を持たない node は自分自身が root なので、step 1 を通るには newParent の root と
  一致する必要があり、そのとき step 2 に引っかかる。
  model では到達しない分岐として `hierarchyRequestError` を返している。

## PLAN §6 の見直しで分かったこと

* **`ensure pre-insert validity` の引数が計画時点と違う。**
  現行の仕様は `childrenToExclude` を取る形で、`replace` が « child » を渡す。
  以前の版で `replace` の側に inline で書かれていた例外条件がここにまとめられている。
  model はこの形に合わせた。
* **Phase 5 に向けた注意：`insert` と `move` で live range 調整の順序が違う。**
  `insert` は step 5（child の index を使った offset 調整）を step 7 の adopt → remove の
  **前** に走らせるが、`move` は step 16 の調整を step 14 の removal の **後** に走らせる。
  oldParent と newParent が同じときは child の index が両者で変わるので、
  Range の観測結果が変わりうる。Phase 5 で hook に中身を入れるときは、
  この順序をそのまま model に反映する必要がある。
  現在の hook はいずれも恒等関数なので、Phase 3 の範囲では差が出ない。
* **`replaceWith` の step 5 の検査は本 model では常に真になる。**
  仕様が「this's parent is parent」を確かめるのは step 4 の
  "converting nodes into a node" が `this` を `node` の中へ移しうるためだが、
  本 model は node を生成しないのでこの経路が無い。
* **可変長引数の API は「まとめた後の node」を受け取る形にした。**
  `before` / `after` / `replaceWith` / `replaceChildren` は
  "converting nodes into a node" で DocumentFragment を生成するが、
  本 model は node を生成しないので、生成済みの node を引数に取る。

## Phase 4（Dommy との differential testing）— 一巡した

`PLAN.md` §7 の仕組みを用意し、実際に Dommy と突き合わせて不一致を検出した。

### 実装したもの

| file | 役割 |
| --- | --- |
| `Dom/Exec/Json.lean` | scenario の JSON 入出力（§7.1, §7.2） |
| `Dom/Exec/Scenario.lean` | 初期状態の構築と操作列の評価 |
| `Main.lean` | `dom-model SCENARIO.json` と `dom-model --batch DIR` |
| `test/dommy_runner.rb` | Dommy 側の評価。`--capabilities` で実装状況も出す |
| `test/compare.rb` | 出力の比較（parent / children / tree order / 例外） |
| `test/generate.rb` | scenario の乱数生成（§7.3） |
| `test/difftest.rb` | driver。生成・評価・比較・最小化 |
| `test/scenarios/*.json` | 固定 scenario |

使い方は `test/README.md` にまとめた。

JSON の parse と serialize には toolchain 同梱の `Lean.Data.Json` を使う。
`Lean` への依存は `Dom/Exec/` に閉じており、`Dom.lean` からも `Dom/Properties/` からも
import しないので、証明側の build には影響しない。

Lean 側は各 step の後で `checkWellFormed` を走らせ、
invariant が破れていれば出力に `invariantViolation` を足す（PLAN §3.5）。
これまでの実行で一度も立っていない。

### Dommy 側で見つかった不一致

生成 scenario 80 本（seed 7、1 本あたり操作 8 個）で 22 本が不一致になり、
すべて 1〜2 操作まで最小化できた。原因は次の 4 種類である。
代表例を `test/scenarios/` に固定 scenario として残した。

1. **`before()` / `after()` / `replaceWith()` / `replaceChildren()` が
   ensure pre-insert validity を通っていない。**
   `appendChild` / `insertBefore` / `replaceChild` は正しく検査するのに、
   ChildNode と ParentNode の便利 method は検査を迂回する。結果として
   * 仕様が禁じる木を作れてしまう
     （`element.after(text)` で Text が Document の子になる。
     `childnode-after-bypasses-validity.json`、`replacewith-bypasses-validity.json`）
   * backend の `Makiri::Error` がそのまま外に出る
     （`text.before(自分の parent)`。`childnode-before-leaks-backend-error.json`、
     `replacechildren-bypasses-validity.json`）

   これは `memo.md` §7 が想定していた「どの API から始めても検査が迂回されない」
   という性質が破れている例である。
   model 側では public API がすべて `ensurePreInsertionValidity` を通る構造になっており、
   その保存は `Dom/Properties/Algorithms.lean` で証明してある。
2. **空の Document への `appendChild(doctype)` が何もしない。**
   例外も投げず、doctype は子にならず parent も付かない。
   仕様では valid なので子になるべきである。
   `doctype-append-to-empty-document.json`
3. **XML document（`implementation.createDocument(null, null, null)`）の
   DocumentFragment に `appendChild` すると `Makiri::Error` になる。**
   HTML document の fragment なら通る。
   runner はこれを避けて、HTML document の子を外して空にしたものを使っている。
4. **API の実装漏れ。** `dommy_runner.rb --capabilities` で一覧できる。

   | kind | 仕様にあって Dommy に無いもの |
   | --- | --- |
   | `Document` | insertBefore, replaceChild, removeChild, replaceChildren, before, after, replaceWith, remove |
   | `Element` | replaceWith |
   | CharacterData と DocumentType | childNodes（空の NodeList を返すべき）、および node tree を変える method 全般 |
   | `DocumentFragment` | （ChildNode の method は仕様上も無いので問題なし） |
   | すべて | moveBefore |

   `Document` に `node_type` が無い、`DocumentType` に `node_name` が無いなど、
   Node interface の属性にも欠けがある。

### 現状の一致状況

上の 4 種類を避けた範囲（Dommy が実装している (kind, 操作) の組だけを生成し、
doctype を初期状態に置かない）では、生成 scenario は一致する。
`--all-ops` や `--doctype-prob 0.5` を付けると、上の不一致が再現する。

## 未着手

Phase 5 以降（`Dom/Range/`, `Dom/Traversal/`, `Dom/CharacterData/`）は
directory を用意しただけで、まだ空である。

PLAN §7.4 の完了条件は「tree mutation の範囲で Lean と Dommy の出力が一致すること」だが、
現時点では Dommy 側の不具合により一致していない。
model と仕様を読み直した結果、いずれも Dommy 側を直すべきものと判断した。
Phase 5（Range）に進むか、先に Dommy の修正を待つかは別途決める。
