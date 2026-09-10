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

### 突き合わせた相手

| | 版 |
| --- | --- |
| Dommy | commit `fd501e0` |
| makiri | RubyGems 公開版 0.8.0（`x86_64-linux`） |

makiri をローカル checkout から build して使う場合は注意が要る。
`Makiri::Document#create_document_type` を持たない build だと、
Dommy は `DOMImplementation#createDocumentType` で node-backed でない
`DocumentType` にフォールバックし（`backend/makiri_adapter.rb:188`、`document.rb:266`）、
`appendChild` が backend に届かなくなる。
この差で下の 2 番の症状が変わるので、公開版を使うか、
`Makiri::Document#create_document_type` があることを確かめてから使う。

### Dommy 側で見つかった不一致

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
2. **`DOMImplementation#createDocumentType` が作った wrapper の同一性が保たれない。**
   `appendChild` 自体は成功し、`doctype.parentNode` も document を返す。
   しかし `document.childNodes` が返す `DocumentType` は append したものと別の Ruby object で、
   `equal?` も `==` も false になる。
   `createDocumentType` が node-backed wrapper を作りながら wrapper cache に
   登録していないためである（`document.rb:266`。`clone_node` は `document.rb:169` で登録している）。
   Element では同一性が保たれる。
   DOM では node の同一性は観測可能なので、これ自体が仕様との不一致である。
   `doctype-wrapper-identity.json`

   runner は同定できなかった node を `"?"` として出すので、
   `children=["?"]` という形で不一致が見える。
   `--doctype-prob 0.5` を付けると 80 本中 40 本が「initial 状態が一致しない」で落ちる
   （Phase 4 時点の生成器では 38 本）。これが既定で doctype を混ぜない理由である。
3. **XML document（`implementation.createDocument(null, null, null)`）の
   DocumentFragment に `appendChild` すると `Makiri::Error` になる。**
   HTML document の fragment なら通る。
   runner はこれを避けて、HTML document の子を外して空にしたものを使っている。
4. **API の実装漏れ。** `dommy_runner.rb --capabilities` で一覧できる。
   下の表は、仕様がその interface に定めている操作のうち Dommy に無いものだけを挙げる
   （`Node` はすべての node、`ParentNode` は Document / DocumentFragment / Element、
   `ChildNode` は DocumentType / Element / CharacterData）。

   | kind | 仕様にあって Dommy に無いもの |
   | --- | --- |
   | `Document` | insertBefore, replaceChild, removeChild, replaceChildren, moveBefore |
   | `Element` | replaceWith, moveBefore |
   | `DocumentFragment` | moveBefore |
   | CharacterData と `DocumentType` | appendChild, insertBefore, replaceChild, removeChild |

   CharacterData と DocumentType は `before` / `after` / `replaceWith` / `remove` を持っている。
   無いのは `Node` の四つと、`childNodes`（空の `NodeList` を返すべき）である。
   `Document#nodeType` と `DocumentType#nodeName` の欠落も確認した。

### 現状の一致状況

既定オプション（HTML document を使い、Dommy が実装している (kind, 操作) の組だけを生成し、
doctype を初期状態に置かない）でも一致しない。
seed 7、80 本、1 本あたり操作 8 個で、**mismatch 19 / match 36 / unsupported 25** である。
19 本はすべて 1 番（validity の迂回）が原因で、
`before` / `after` / `replaceWith` / `replaceChildren` に分かれる。

1 番を避ける option は無いので、「上の 4 種類を避ければ一致する」とは言えない。
他の mode では次のようになる。

| 実行 | 結果 |
| --- | --- |
| 既定 | mismatch 19 / match 36 / unsupported 25 |
| `--doctype-prob 0.5` | mismatch 40 / match 22 / unsupported 11 / error 7 |
| `--all-ops` | mismatch 10 / match 13 / unsupported 57 |

`--all-ops` は仕様上の全 API を生成するので unsupported が増え、
そのぶん比較まで進む本数が減る。不一致の内訳は既定と同じく 1 番である。

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

## Phase 5（Range）— 一巡した

`PLAN.md` §8 の定義・調整・証明・differential testing を実装した。

### `DOMState` への持ち上げ

PLAN §8.1 に従い、状態を `DOMState`（tree + ranges + iterators）にした。
Phase 2 の primitive（`detach`, `insertAt`, `setOwnerDocument`）は木だけを変えるので
`Tree` の上に残し、§4.2.3 の algorithm と public API を `DOMState` に持ち上げた。
Phase 1・2 の定理はそのままで、Phase 3 の定理は結論を `s'.tree` について述べる形に直した。

### 実装した定義

| 定義 | module |
| --- | --- |
| `BoundaryPoint`, `RangeState`, `IteratorState`, `DOMState` | `Dom/Basic/State.lean` |
| `ValidBoundaryPoint`, `bpPosition`, `BoundaryLE`, `RangeValid`, `RangesValid`, `checkRangesValid` | `Dom/Range/BoundaryPoint.lean` |
| `liveRangePreRemove`（仕様の live range pre-remove steps）、`liveRangeInsertAdjust`（insert step 5 / move step 16） | `Dom/Range/Adjust.lean` |

Phase 3 で恒等関数の hook として置いてあった位置に、そのまま中身が入った。
hook の位置は仕様の step 順序に合わせてあるので、
`remove` / `insert` / `replace` / `replaceAll` / `move` と public API 10 個は変更なしで
Range に追随するようになった。

### 証明した theorem（`Dom/Properties/Range.lean`）

| PLAN §8.3 | theorem |
| --- | --- |
| `remove_preserves_ranges_valid`（両端が木の中にある部分） | `remove_preserves_endpoints` |
| 削除された node を端点に持つ range は操作後に存在しない | `remove_leaves_subtree`, `move_leaves_subtree` |
| `insert_preserves_ranges_valid`（同上、parent を持たない node の場合） | `insert_preserves_endpoints` |
| public API への持ち上げ | `preRemove_`, `removeChild_`, `nodeRemove_preserves_endpoints` |

補助として `valid_liveRangePreRemoveBP`（削除側の調整）と
`valid_rangeShiftAfterInsert` / `valid_of_insertAt`（挿入側の調整）を証明した。

`ChildCountKind`（node の length が children の個数で決まる kind であること）を前提に置いている。
仕様の pre-insertion validity は parent を Document / DocumentFragment / Element に限るので
子を持つ node ではつねに成り立つが、`WellFormed` はこれを要求していないためである。

### 証明できていない部分

* **`BoundaryLE`（start ≤ end の順序）の保存。**
  `RangeValid` のうち順序の部分は、mutation の後の tree order について
  まとまった理論が要る。定義と実行時検査（`checkRangesValid`）は用意してあり、
  differential testing の各 step で確認しているが、証明はしていない。
* **parent を持つ node の `insert` についての端点の保存。**
  仕様は挿入側の調整（insert step 5）を adopt → remove（step 7）より前に置いているため、
  その途中では offset が parent の length を一時的に超えうる。
  最終状態では valid になるが、合成の証明には length の増減を追う補題がもう一段要る。
* **DocumentFragment を展開する `insert` についての端点の保存。**

## Phase 5 で見つかった Dommy の不一致

range を differential testing の比較対象に加えたところ、
Phase 4 で見つかった 4 種類に加えて次が見つかった（Dommy `fd501e0` / makiri 0.8.0）。

5. **移動する node の中を指す range の offset が 1 ずれる。**
   `test/scenarios/range-adjust-order-on-move.json`

   ```text
   element(1) の children = [text(2), comment(3)]、range は comment(3) の中
   insertBefore(parent=1, node=3, child=2)   # comment を text の前へ移す
   → 仕様: range = (1,1)-(1,1)   Dommy: (1,2)-(1,2)
   ```

   仕様の `insert` は step 5（child の index を使った live range の offset 調整）を
   step 7 の adopt → remove より **前** に走らせる。
   step 5 の時点で child(2) の index は 0 なので、offset 0 の range は増えない。
   その後 remove の pre-remove steps が range を `(parent, 削除時の index=1)` に移す。
   Dommy はこの順序が逆になっているらしく、移した後で +1 している。

   この順序の危うさは Phase 3 で仕様を読んだ時点で気づいて
   `docs/status.md` に「Phase 5 に向けた注意」として書いておいたもので、
   実装が実際にそこで食い違っていた。木の形は両者一致しているので、
   Range を比較対象に入れて初めて見える不一致である。

## Phase 6（NodeIterator）— 一巡した

`PLAN.md` §9 の定義・調整・証明・differential testing を実装した。

### 実装した定義（`Dom/Traversal/NodeIterator.lean`）

| 定義 | 対応する仕様 |
| --- | --- |
| `iteratorCollection` | §6.1 iterator collection |
| `firstFollowingOutside` | "adjust a node pointer" step 2.1 |
| `adjustNodePointer` | "adjust a node pointer" |
| `iteratorPreRemoveOne`, `iteratorPreRemove` | "NodeIterator pre-remove steps"（remove step 4 / move step 11） |
| `nextNode`, `previousNode` | `nextNode()` / `previousNode()` |
| `ValidIterator`, `IteratorsValid`, `checkIteratorsValid` | PLAN §9.2 |

Phase 3 で恒等関数の hook として置いてあった `iteratorPreRemove` にそのまま中身が入った。
Range のときと同様、algorithm と public API のコードは変えていない。

filter（`whatToShow` と `NodeFilter`）は扱わない。
`SHOW_ALL` かつ filter が null の場合、すなわち iterator collection が
すべての node に一致する場合だけを model にする。
仕様の traverse は filter が accept するまで繰り返すが、
filter が無ければ 1 周で決まるので `nextNode` / `previousNode` は候補を一つ求める形になる。
仕様の candidate reference は traverse の途中でしか非 null にならないので状態には持たない。

### 証明した theorem（`Dom/Properties/Iterator.lean`）

| PLAN §9.2 | theorem |
| --- | --- |
| `IteratorsValid`（reference が木にあり root の inclusive descendant） | `ValidIterator` の定義と `checkIteratorsValid` |
| `remove_preserves_iterators_valid` | 同名 |
| 削除された node の inclusive descendant は reference にならない | `remove_iterators_leave_subtree`, `move_iterators_leave_subtree` |

中心になるのは次の二つである。

* `ancestor_detach_of_not_below` — `detach` が外す辺が経路上に無ければ ancestor 関係は残る。
  「経路上にある」は「削除する node が下端の inclusive ancestor であり、
  かつ上端がその ancestor である」と書ける。
* `adjustNodePointer_spec` — root が生き残る場合、調整後の pointer は
  削除される部分木の外にあり、root の inclusive descendant である。
  仕様の step 2（後続を探す）と step 3-4（parent か前の兄弟の最後の子孫）の
  両方について示す。

前提として `OtherDocumentIteratorsOutside` を置いている。
仕様は「root の node document が削除する node の node document と同じ」iterator だけを
調整するので、それ以外の iterator が削除される部分木を指していないことは
node document が木の構造と整合していれば成り立つが、
`WellFormed` はそれを要求していないためである。

### differential testing

scenario の `iterators` は仕様の `createNodeIterator` に合わせて
`(root, true)` から始める形にした（Dommy に reference の setter が無いため）。
操作 `iteratorNext` / `iteratorPrevious` で動かす。

`iterator-adjust-on-remove.json` と `iterator-adjust-pointer-before.json` で、
pre-remove steps の step 3-4（parent へ）と step 2（後続へ）の両方を通し、
Dommy と一致することを確認した。生成 scenario でも iterator 由来の不一致は出ていない。
**Dommy の NodeIterator の pre-remove steps は仕様どおりに動いている。**

見つかった小さな抜けが一つある。
`NodeIterator#referenceNode` と `#pointerBeforeReferenceNode` が
Ruby の method として公開されておらず、`__js_get__` 経由でしか読めない。
Dommy の Ruby API は他が snake_case で揃っているので、そこだけ不揃いである。
runner は `__js_get__` へ fallback するようにしてある。

## Phase 7（CharacterData）— 一巡した

`PLAN.md` §10 の定義・証明・differential testing を実装した。

### 実装した定義（`Dom/CharacterData/ReplaceData.lean`）

| 定義 | 対応する仕様 |
| --- | --- |
| `adjustedCount` | replace data step 3（count の切り詰め） |
| `spliceData` | replace data step 5-7 |
| `replaceDataAdjustBP`, `replaceDataAdjustRange` | replace data step 8-11（live range の調整） |
| `replaceData` | §4.10 "replace data" |
| `appendData`, `insertData`, `deleteData`, `setData`, `substringData` | §4.10 の method |

仕様の `replace data` には node が CharacterData であるという検査が無い
（`CharacterData` interface の method からしか呼ばれないため）。
本 model は node を kind で区別するので、
CharacterData 以外に対しては `invalidNodeTypeError` を返す。

**`data` の長さの単位に差がある。** 仕様は UTF-16 の code unit 数だが、
Lean の `String.length` は code point 数である。
BMP の範囲では両者は一致するので、本 model は BMP に限って仕様どおりになる。
differential testing の生成器も BMP の文字しか使わない。
astral 面の文字（surrogate pair）まで扱うには、`NodeData.length` と
`spliceData` を UTF-16 の単位で定義し直す必要がある。

### 証明した theorem（`Dom/Properties/CharacterData.lean`）

| PLAN §10.2 | theorem |
| --- | --- |
| `replaceData_preserves_wellformed` | 同名。`data` しか変えないので木の構造は変わらない（`wellFormed_withData`） |
| `replaceData_preserves_ranges_valid`（両端が木の中にある部分） | `replaceData_preserves_endpoints` |
| wrapper への持ち上げ | `appendData_`, `insertData_`, `deleteData_`, `setData_` + `preserves_wellformed` / `preserves_endpoints` |

端点の証明の要は `length_spliceData` である。
`offset ≤ length` と `offset + count ≤ length`（step 3 の切り詰め後）のもとで
`新しい長さ + count = 元の長さ + data の長さ` が成り立つので、
step 8-11 の三つの場合をどれも `omega` で片づけられる。

### differential testing

固定 scenario 二つで仕様の分岐をすべて通した。

* `characterdata-replace-data-ranges.json` — step 8-11 の三つの場合
  （offset 以下は不変、`(offset, offset+count]` は offset に、それより後ろは
  `+ data の長さ − count`）
* `characterdata-index-size-and-clamp.json` — `offset > length` の `IndexSizeError` と
  step 3 の count の切り詰め、および `appendData` / `insertData` / `setData`

いずれも Dommy と一致した。生成 scenario でも CharacterData 由来の不一致は出ていない。
**Dommy の CharacterData は仕様どおりに動いている。**

## PLAN の第3の成功条件

`memo.md` §17 の第3の成功条件は
「mutation の任意の組み合わせの後でも Range boundary points が valid であることを証明する」である。

現時点で証明できているのは、`ValidBoundaryPoint`（node が木にあり offset が length 以下）の
保存であり、対象は次のとおりである。

* `remove` とそれを経由する public API（`preRemove` / `removeChild` / `nodeRemove`）
* parent を持たない node の `insert`
* `replaceData` とその wrapper

証明できていないのは次の三つで、`docs/status.md` の各 Phase の節に理由を書いた。

1. `BoundaryLE`（start ≤ end の順序）の保存
2. parent を持つ node の `insert`（仕様が調整を removal より前に置くため、途中で一時的に invalid になる）
3. DocumentFragment を展開する `insert`

いずれも定義と実行時検査（`checkRangesValid`）は用意してあり、
differential testing の各 step で確認している。

## 未着手

Phase 8（`PLAN.md` §11）の再評価。MutationObserver と Shadow DOM に進むかどうかを、
Phase 4-7 の differential testing で見つかった不一致の傾向から判断する。
