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
| `Dom/Exec/Types.lean` | scenario の型（操作列と step の結果）。JSON を知らない |
| `Dom/Exec/Eval.lean` | 初期状態の構築と操作列の評価。JSON を知らない |
| `Dom/Exec/Json.lean` | scenario の JSON 入出力（§7.1, §7.2） |
| `Dom/Exec/Scenario.lean` | 上の二つをつないで scenario 一つを走らせる入口 |
| `Main.lean` | `dom-model SCENARIO.json` と `dom-model --batch DIR` |
| `test/dommy_runner.rb` | Dommy 側の評価。`--capabilities` で実装状況も出す |
| `test/compare.rb` | 出力の比較（parent / children / tree order / 例外） |
| `test/generate.rb` | scenario の乱数生成（§7.3） |
| `test/difftest.rb` | driver。生成・評価・比較・最小化 |
| `test/scenarios/*.json` | 固定 scenario |

使い方は `test/README.md` にまとめた。

JSON の parse と serialize には toolchain 同梱の `Lean.Data.Json` を使う。
`Lean` への依存は `Dom/Exec/Json.lean` 一つに閉じており、`Dom.lean` からも `Dom/Properties/` からも
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
| `Dom/Exec/Types.lean` | scenario の型（操作列と step の結果）。JSON を知らない |
| `Dom/Exec/Eval.lean` | 初期状態の構築と操作列の評価。JSON を知らない |
| `Dom/Exec/Json.lean` | scenario の JSON 入出力（§7.1, §7.2） |
| `Dom/Exec/Scenario.lean` | 上の二つをつないで scenario 一つを走らせる入口 |
| `Main.lean` | `dom-model SCENARIO.json` と `dom-model --batch DIR` |
| `test/dommy_runner.rb` | Dommy 側の評価。`--capabilities` で実装状況も出す |
| `test/compare.rb` | 出力の比較（parent / children / tree order / 例外） |
| `test/generate.rb` | scenario の乱数生成（§7.3） |
| `test/difftest.rb` | driver。生成・評価・比較・最小化 |
| `test/scenarios/*.json` | 固定 scenario |

使い方は `test/README.md` にまとめた。

JSON の parse と serialize には toolchain 同梱の `Lean.Data.Json` を使う。
`Lean` への依存は `Dom/Exec/Json.lean` 一つに閉じており、`Dom.lean` からも `Dom/Properties/` からも
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

### 残りだった三点（後から証明した）

Phase 5 の時点で残していた三点のうち、二つは完全に、一つは部分的に証明した。
詳しくは後述の「残り三点の解消」を参照。

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

filter は扱わない（`whatToShow` は後で入れた。この節の後の
「NodeIterator の `whatToShow`」を参照）。
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
BMP の範囲では両者は一致するので、当初は BMP に限って仕様どおりとしていた
（後で code unit で数えるようにした。この節の後の「UTF-16 の code unit 境界」を参照）。
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

（2 と 3 はその後証明した。1 は `remove` については証明した。
`insert` / `move` の挿入側は仕様がその性質を持たないことが分かった。以下の節を参照。）

いずれも定義と実行時検査（`checkRangesValid`）は用意してあり、
differential testing の各 step で確認している。

## 残り三点の解消

Phase 5 と 7 で残していた三点に取り組んだ。

### 1. DocumentFragment を展開する `insert`（完全に証明した）

`insert_fragment_preserves_endpoints`。

要になったのは、仕様の step 4 が fragment の children を **先に全部外す** ことである。
そのため step 7 の時点ではどの node も parent を持たず、
`insertEach` の中で removal が起きない。
step 5 で足した余裕（children の個数）が、
`insertAt` 一回につき一つずつちょうど使い切られる。

用意した補助は次のとおり。

* `removeEach_from_parent` — 同じ parent を持つ node の列をまとめて外す。
  外した後どの node も parent を持たないことも返す。
* `insertEach_valid_of_no_parent` — parent を持たない node の列を入れる。

### 2. parent を持つ node の `insert`（完全に証明した）

`insert_single_preserves_endpoints`、および fragment と合わせた
`insert_preserves_endpoints`。

仕様は挿入側の調整（step 5）を adopt → remove（step 7）より前に置くので、
途中では offset が parent の length を一時的に超える。
これを扱うために **余裕つきの validity** を導入した。

```lean
def BoundaryValidUpTo (t : Tree) (parent : NodeId) (slack : Nat) (bp : BoundaryPoint) : Prop :=
  ∃ d, t.get? bp.node = some d ∧
    bp.offset ≤ d.length + (if bp.node = parent then slack else 0)
```

`slack = 0` はちょうど `ValidBoundaryPoint` になる。
step 5 が余裕を一つ作り（`rangeValidUpTo_liveRangeInsertAdjust`）、
削除側の調整が余裕を保ち（`boundaryValidUpTo_liveRangePreRemoveBP`。
parent がちょうど削除元なら length と offset が同時に一つ減る）、
最後の `insertAt` が余裕を使い切る（`boundaryValidUpTo_insertAt`）。

`insertAt` の成功から「node は parent の inclusive ancestor でない」を
削除前の木へ引き戻すのに `ancestor_detach_of_not_below`（Phase 6 で作った補題）を使った。

### 3. `BoundaryLE`（start ≤ end の順序）の保存（部分的に証明した）

**両端が同じ node を指す range については証明した。**

`boundaryLE_same_node` により、この場合の順序は offset の比較そのものになる
（仕様の boundary point position の step 2）。
あとは調整が同じ node の上で単調であることを示せばよい。

* `rangeShiftAfterRemove_mono`, `liveRangePreRemoveBP_mono`
* `rangeShiftAfterInsert_mono`
* `replaceDataAdjustBP_mono`

これらから `remove` / `insert` / `move` / `replaceData` と
public API について `RangesSameNodeOrdered` の保存を示し、
`remove_preserves_boundaryLE`, `insert_preserves_boundaryLE`,
`replaceData_preserves_boundaryLE` を得た。
differential testing の生成器が作る range もこの形である。

**両端が別の node を指す場合**は、`remove` については証明した（次節）。
`insert` / `move` の挿入側は、その後 **定理が偽であること** が分かった
（「`insert` 側の `BoundaryLE` は保たれない」の節）。

## 別 node の `BoundaryLE`：`remove` について証明した

新しい module `Dom/Properties/Path.lean`（約 900 行）で、
boundary point position を **数列の辞書式比較** に言い換えてから証明した。

### key による言い換え

root から node へ至る経路上の各段の index を並べた列に offset を付けたものを
boundary point の **key** とする。

```lean
def pathNodes (t : Tree) (n : NodeId) : List NodeId := (n :: ancestors t n).reverse
def pathIndices (t : Tree) (n : NodeId) : List Nat :=
  ((pathNodes t n).drop 1).map fun x => (index t x).getD 0
def bpKey (t : Tree) (bp : BoundaryPoint) : List Nat := pathIndices t bp.node ++ [bp.offset]
```

```lean
theorem bpPosition_eq_lexCmp (hwf : WellFormed t) {a b : BoundaryPoint} {ad bd : NodeData}
    (ha : t.get? a.node = some ad) (hb : t.get? b.node = some bd)
    (hroot : root t a.node = root t b.node) :
    bpPosition t a b = lexCmp (bpKey t a) (bpKey t b)
```

仕様の boundary point position は step 2（同じ node）、step 3（follow なら入れ替え）、
step 4（ancestor なら `childTowards` の index と offset を比べる）、step 5（それ以外は before）
に分かれるが、key の辞書式比較はこの四つをまとめて表す。

この定理を出すために、`Dom/Properties/Tree.lean` に tree order の
**構造的な特徴づけ** を足した。

```lean
def PrecedesStruct (t : Tree) (x y : NodeId) : Prop :=
  Ancestor t x y ∨
    ∃ p cx cy i j, parentOf t cx = some p ∧ parentOf t cy = some p ∧
      index t cx = some i ∧ index t cy = some j ∧ i < j ∧
      InclusiveAncestor t cx x ∧ InclusiveAncestor t cy y

theorem precedes_iff_struct (hwf : WellFormed t) {a b : NodeId} {ad : NodeData}
    (ha : t.get? a = some ad) (hroot : root t a = root t b) (hab : a ≠ b) :
    precedes t a b = true ↔ PrecedesStruct t a b
```

健全性（構造 → `precedes`）は「前の兄弟の部分木は後の兄弟の部分木に先行する」
（`precedesIn_preorderFuel_of_sibling_deep`）から、
完全性は三分律（`precedesStruct_total`）と `precedesIn` の非対称性から出る。
当初想定していた「preorder における部分木は連続した区間である」という補題は要らなかった。

key が node を決めること（`eq_of_pathIndices_eq`）も示した。
これは `p` までの key が `x` の key の真の prefix なら `p` は `x` の inclusive ancestor である、
という形（`inclusiveAncestor_of_dropPrefix`）で使う。

### live range pre-remove steps は key の上で単調

`node`（parent は `p`、index は `i`）を外すとき、key は次の写像で移る。

```lean
def shiftDown (i x : Nat) : Nat := if i < x then x - 1 else x

def shiftTail (i : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs => shiftDown i x :: (if x = i then [] else xs)

def shiftKey (P : List Nat) (i : Nat) (key : List Nat) : List Nat :=
  match dropPrefixNat P key with
  | none => key
  | some rest => P ++ shiftTail i rest
```

`P` は `p` までの index 列である。`shiftTail` の `if x = i then []` が
「外す部分木の中を指していた点は `(p, i)` へ移る」に対応し、
`shiftDown` が「`i` より後ろの index / offset は一つ減る」に対応する。

```lean
theorem bpKey_detach (hwf : WellFormed t) (hwf' : WellFormed t')
    (hpar : parentOf t n = some p) (hi : index t n = some i) (hd : detach t n = .ok t')
    {bp : BoundaryPoint} (hroot : root t bp.node = root t p) :
    bpKey t' (liveRangePreRemoveBP t n p i bp) = shiftKey (pathIndices t p) i (bpKey t bp)

theorem shiftKey_mono (P : List Nat) (i : Nat) {u v : List Nat} (h : lexCmp u v ≠ .gt) :
    lexCmp (shiftKey P i u) (shiftKey P i v) ≠ .gt
```

`shiftKey` の単調性は、`shiftDown i` が単調で、
`shiftDown i x = shiftDown i y` かつ `x < y` なら `x = i`（すなわちその点は部分木の中にいた）
という観察に尽きる。

### 結果

```lean
theorem boundaryLE_detach (hwf : WellFormed t) (hwf' : WellFormed t') ... :
    BoundaryLE t' (liveRangePreRemoveBP t n p i a) (liveRangePreRemoveBP t n p i b)

theorem remove_preserves_boundaryLE {s s' : DOMState} {n p : NodeId}
    (hwf : WellFormed s.tree) (hp : parentOf s.tree n = some p)
    (hv : RangeEndpointsValid s)
    (hord : ∀ r ∈ s.ranges, BoundaryLE s.tree r.start r.«end»)
    (h : remove s n = .ok s') :
    ∀ r ∈ s'.ranges, BoundaryLE s'.tree r.start r.«end»
```

`ValidBoundaryPoint` の保存と合わせて `RangesValid` の保存になり、
`remove` を経由する public API に持ち上げた。

* `remove_preserves_rangesValid`
* `preRemove_preserves_rangesValid`
* `removeChild_preserves_rangesValid`
* `nodeRemove_preserves_rangesValid`

木が別の場合（range が外す部分木と無関係な木にある場合）も
`liveRangePreRemoveBP_of_other_root` で分けて扱っており、仮定は
「両端が木の中にある」「もともと順序が付いている」だけである。

## `insert` 側の `BoundaryLE` は **保たれない**（仕様の性質）

挿入側を証明しようとしていたが、**定理そのものが偽**であることが
differential testing で分かった。生成器を別 node の range を作るように直した直後に、
model 側の invariant 検査（`checkRangesValid`）が破れる scenario が出た。

最小例（`test/scenarios/range-order-broken-by-insert.json`）:

```
<element 1>
  <comment 2 "cc">     ← range.start = (2, 0)
  <text 3 "tt">        ← range.end   = (3, 2)

element1.insertBefore(text3, comment2)
```

仕様どおりに追うと:

* insert step 5（`child` = 2、index 0）。parent を指す boundary は無いので何もしない。
* insert step 7 の adopt → remove。3 は index 1 なので、
  live range pre-remove steps で end が `(1, 1)` へ出る。
* 3 を 2 の前に入れて children は `[3, 2]`。node 2 の index は 1。

結果は start = `(2, 0)`、end = `(1, 1)` で、**start が end より後**になる。

つまり `BoundaryLE`（start ≤ end）は仕様の invariant ではない。
仕様が順序を正規化するのは `setStart` / `setEnd` の側だけで
（「bp が end より後なら end も動かす」）、
木を変える algorithm の側にはそれに当たる step が無い。
`dom.bs` にも live range について順序の invariant は書かれていない
（書かれているのは「start と end の root は同じ」だけ）。

原因は step の順序である。offset の調整（step 5）が
木を変える step 7 より前に置かれているので、
「動かす node の中にあった boundary」は step 5 を通り過ぎたあとに
`(parent, 旧 index)` へ出る。node はその位置より前へ入るため、順序が逆転する。

この発見を受けて次の二つを直した。

* `Dom/Range/BoundaryPoint.lean` に `checkRangeEndpointsValid` を足した。
  両端が木の中にあることだけを見る。
* `Dom/Exec/Eval.lean` の各 step の invariant を
  `checkRangesValid` から `checkRangeEndpointsValid` に弱めた。
  初期状態については `checkRangesValid` のまま
  （scenario の range は `setStart` / `setEnd` で作れるものに限りたいため）。

証明側の帰結は次のとおり。

* `remove` の `BoundaryLE` 保存は成り立つ（前節）。
* `insert` / `move` の `BoundaryLE` 保存は **成り立たない**。証明すべき定理ではない。
* 仕様の invariant として残るのは `ValidBoundaryPoint`（両端が木の中にある）で、
  これは `remove` / `insert` / `move` / `replaceData` すべてについて証明済みである。

なお Dommy は調整を remove の後に回すので、この例では end = `(1, 2)` となり
たまたま順序を保つ。ただしそれは仕様と違う値であり、下の finding 2 と同じ原因である。

## 生成器の拡張（別 node の range）

`test/generate.rb` の `random_ranges` は両端を同じ node に置いていたので、
今回証明した「別 node の `BoundaryLE`」を一度も叩けていなかった。次のように直した。

* 3 回に 2 回は、同じ root にある **別々の node** に両端を置く。
  どちらを start にするかは **key の辞書式比較** で決める。
  `Dom/Properties/Path.lean` の `bpKey`（root からの index 列 ++ offset）を
  Ruby 側に写したもので、`bpPosition_eq_lexCmp` により仕様の
  boundary point position と一致する。
* boundary point に doctype を選ばない。
  仕様の `setStart` / `setEnd` は doctype を `InvalidNodeTypeError` で弾くので、
  以前は Dommy 側だけが例外を投げて「Dommy 側でエラー」になっていた。
* `--ranges N` / `--iterators N` を `generate.rb` と `difftest.rb` に足した。

model の各 step が `checkRangeEndpointsValid` を検査しているので、
この生成器は「別 node の range を持つ状態で mutation を重ねても
両端が木の中に残るか」を常時監視することになる。
上の「`insert` 側の `BoundaryLE` は保たれない」も、
生成器を直した直後の最初の sweep で出た。

副産物として、生成した別 node の range は初期状態で
`checkRangesValid`（順序を含む）を通る必要があるが、
sweep 中に一度も「初期状態の range が valid でない」は出ていない。
これは Ruby 側の辞書式比較と Lean 側の `bpPosition` が一致していることの
実験的な裏付けになっている。

## Dommy 側の修正（Dommy commit `87432de`, `f2af31a`, `f461486`, `d604752`, `c6ce3c3`, `0b34062`）

finding 1（validity の迂回）と finding 2（range 調整の順序）を直した。
あわせて、同じ sweep で新たに出た五つも直した。全部で七つある。

1. **ChildNode の三つが validity を全く通らない**（finding 1、`87432de`）。
   `before` / `after` / `replaceWith` は最後に **親** への pre-insert（replace）で終わるので、
   親側の validity が走らなければならない。親は Document のこともあり、
   その場合は step 6（Text の子を持てない、element は高々一つ、doctype は document element より前）
   が加わる。親の wrapper に `__internal_ensure_insertion_validity__` を生やして dispatch する形にした。
   引数を変換する前に検査するので、弾かれた呼び出しは木を変えない。
2. **step 2（node が parent の inclusive ancestor）が Fragment / ShadowRoot で無効だった**（`87432de`）。
   `check_insertion!` が Element だけの override だったため、
   `frag.replaceChildren(frag)` や `frag.appendChild(frag)` が通っていた。
   `Internal::ParentNode` に移して三者で共有した。
3. **step 2 が Document 引数で発火しない**（`f2af31a`）。
   `Dommy::Document` は `__dommy_backend_node__` を持たないので早期 return していた。
   `el.insertBefore(document, ref)` が step 3 の `NotFoundError` になっていた
   （仕様は step 2 の `HierarchyRequestError`）。
   Document は `backend_doc` で解決し、親を document まで登るようにした。
4. **`insertBefore(x, x)` の reference 差し替えが validity より前**（`f2af31a`）。
   仕様は pre-insert step 1 で **呼び出し側が渡した** reference を検査し、
   step 3 で初めて差し替える。Dommy は先に差し替えていたので、
   `x` が parent の子でないときに `NotFoundError` にならず黙って append していた。

### 5. live range の挿入側調整が仕様の位置にない（finding 2、`f461486`）

仕様の insert step 5（parent を指す offset の調整）は step 7 の adopt → remove より
**前** に走る。Dommy は木を変え終わってから `notify_child_list_mutation` の中で
調整していたので、「その insert 自身の removal が parent の上へ動かした boundary」を
二重に数えていた。

```
<div><!--cc--><em/></div>            range: (em, 0) - (em, 0)
div.insertBefore(em, comment)
→ 仕様 (div, 1) / Dommy は (div, 2)
```

後追いの `__internal_ranges_inserted__` を
`__internal_ranges_will_insert__(parent, ref, count)` に置き換え、
各挿入箇所が step 5 の位置で呼ぶ形にした。
`ChildNode#convert_for_insert` が「調整 → 引数の変換」を一つにまとめているので、
両者が離れないようになっている。

順序で気をつける点が三つあった。

* **replace** は置き換える node の adopt（step 6、旧 parent から外す）が
  古い子の除去（step 7）より **前** で、挿入（step 9）はその後。
  つまり調整は二つの除去の後に来る。
  最初これを逆に並べ替えてしまい、差分テストで 4 件の回帰が出て気づいた。
* **pre-insert step 3**（reference child が挿入する node 自身なら、
  reference をその next sibling へ進める）は step 5 より前に走る。
  でないと `x.before(x)` が x の位置で調整してしまう。
* **append（reference が null）は何も調整しない**。
  `replaceChildren` / replace-all / `textContent=` は影響を受けない。

### 6. Document への fragment 挿入で insert step 4 が走らない（`f461486`）

`document.appendChild(fragment)` は fragment の backend node をそのまま backend に渡していて、
backend が children を黙って splice するので、
insert step 4（fragment の children を **removing steps 付きで** 外す）が走っていなかった。
fragment の子の中にあった live range は、動いた node を指したまま取り残されていた。
Document 側でも `extract_children` を通すようにした。

### 7. `Fragment#replaceChild` の例外の順序（`f461486`）

parent 判定を validity より前に置いていたので、
`frag.replaceChild(frag, frag)` が step 2 の `HierarchyRequestError` ではなく
`NotFoundError` になっていた。`ShadowRoot#replaceChild` も同じで、
`ShadowRoot#insertBefore` には validity 検査自体が無かった。

### 修正後の一致状況

`--ranges 4 --iterators 2 --nodes 10 --ops 10` で seed 10 個 × 各 100 scenario、
**合計 1000 scenario で不一致ゼロ**。固定 scenario も `doctype-wrapper-identity`
（finding 3）以外はすべて一致する。
修正前は既定の設定でも 80 中 22 件が不一致だった。

回帰 test は次の二つ。

* `test/wpt/test_wpt_child_node_pre_insertion_validity.rb`（19 件）
* `test/wpt/test_wpt_live_range_insert_order.rb`（6 件）

Dommy の既存 suite は 3909 runs / 0 failures。

## API の欠落（finding 5、Dommy commit `d604752`）

`unsupported` の主因だった Ruby API の欠落を埋めた。
仕様では `appendChild` / `insertBefore` / `replaceChild` / `removeChild` は
`Node` の method なのですべての node が持つが、
Dommy は JS bridge にはあって Ruby には無い、という状態だった。

* **CharacterData と DocumentType** に四つとも無かった。
  共有 module `Internal::LeafNode` にまとめた。leaf を parent にした挿入は
  `HierarchyRequestError`（pre-insert / replace とも step 1 で parent の型を見るので、
  reference child より先に決まる）、`removeChild` は `NotFoundError`、
  いずれも WebIDL の引数 coercion が先。
  両 class の JS bridge もここへ dispatch するようにしたので、二つの surface がずれない。
* **Document** は `appendChild` しか無かった。
  `insertBefore` / `replaceChild` / `removeChild` / `replaceChildren` /
  `append` / `prepend` を `document_*` の実装へ転送する形で足した。
* **Element** に `replace_with` を足した（`replace_with_nodes` は既存の呼び出しがあるので残した）。

これで **仕様がその kind に定めている操作のうち Dommy に無いのは `moveBefore` だけ** になった。

### 8. Document を parent としたときの step 2 が無い（`d604752`）

上の API を足して差分テストから届くようになった直後に出た。
「node が parent の inclusive ancestor」（step 2）の検査が Document parent に対して無く、
`document.replaceChild(document, x)`（x は document の子でない）が
step 3 の `NotFoundError` になっていた。仕様では step 2 が先なので
`HierarchyRequestError` である。
Document にとっての step 2 は「document を自分自身に入れられない」に帰着する。

### 9. `replaceChildren` の validity は既存の children を除外する（**model 側の不具合**）

同じ sweep で `document.replaceChildren(element)` が
Lean は `HierarchyRequestError`、Dommy は成功、という不一致が出た。
確認したところ **Lean の model が間違っていた**。

仕様の `replaceChildren` step 2 は

> Ensure pre-insert validity given node, this, null, and **this's children**.

で、第四引数の `childrenToExclude` に自分の children を渡す。
直後の replace all がそれらを外すので、
「element は高々一つ」などの個数の制約から除いてよい（whatwg/dom#1045）。
model は `[]` を渡していたので、既に document element がある document に対して
`replaceChildren(element)` を弾いてしまっていた。
`Dom/Mutation/Api.lean` の `replaceChildren` を
`childrenOf s.tree parent` を渡すように直した。

Dommy は最初から `ignore_existing: true` で正しく実装していた。

## doctype 周り（finding 3、Dommy commit `c6ce3c3`）

### 10. `createDocumentType` の wrapper が cache に載らない

`Document#createDocumentType` は wrapper cache を通さずに直接
`DocumentType` を作っていたので、cache に登録されていなかった。
その結果、あとから木を経由して取り出した doctype
（`document.childNodes` / `document.doctype` / NodeIterator）は
factory が返したものとは **別の object** になり、`equal?` / `isSameNode` が false だった。
他の `create*` と同じように cache に seed するようにした。

### 11. doctype の `before` / `after` / `replaceWith` が専用経路だった

validity 検査を一切通さず、childList record も積まず、
挿入位置を doctype の実際の位置ではなく heuristic
（document element、あるいは最初の子）で決めていた。
そのため Text を document の子にできてしまい、
`doctype.replaceWith(documentElement)` は backend まで届いて生の error が漏れていた。

node backed な doctype は document の普通の ChildNode なので、
共有の `Internal::ChildNode` の実装を使うようにした。
これで親（Document）の ensure-pre-insertion-validity が走り
（`replaceWith` では仕様の replace どおり doctype を個数から除外する）、
live range の insert steps も走る。
backend が doctype node を作れないときの synthetic doctype は従来どおりにした
（木の中に無いので、仕様ならこれらの method は step 2 で return する）。

これで `--doctype-prob 0.5` でも不一致は出なくなった。

## finding 4（XML document の DocumentFragment）— Makiri 側の制約

切り分けた結果、二層あることが分かった。

1. **Dommy**: `Backend.fragment(html, owner_doc:)` は Makiri 版が `owner_doc` を無視して
   `Makiri::DocumentFragment.parse` を呼ぶので、XML document の
   `createDocumentFragment` が **HTML arena の** fragment を返す。
   そこへ XML arena の element を入れようとすると
   `TypeError: wrong argument type Makiri::XML::Node (expected Makiri::HTML::Node)` になる。
2. **Makiri 0.8.0**: 正しく XML document の arena で fragment を作っても
   （`xml_doc.fragment("")`）、その fragment への `add_child` は
   text / comment / element のいずれでも
   `Makiri::Error: invalid placement` になる。
   一方 `xml_doc.fragment("<a/>")` のように **parse で作れば** 子を持てる。
   つまり fragment node 自体は子を保持できるが、後から足せない。

1 だけ直しても error の種類が変わるだけなので、2 が先である。
2 は Makiri repo の話であり、ここでは扱わない。

## `moveBefore` の実装（Dommy commit `0b34062`）

仕様 §4.2.3 の move algorithm（2025 年追加）を Dommy に実装した。
`Internal::ParentNode`（Element / DocumentFragment / ShadowRoot）と `Document` の両方。

move は remove + insert の合成ではない。

* removing steps も insertion steps も走らせない（connected / disconnected callback が出ない）。
* adopt しない。step 1 が「node と newParent の shadow-including root が同じ」を
  要求するので node document は変わらない。
* validity は `ensure pre-insert validity` ではなく step 1-6 の独自のもの。

一方で live range / NodeIterator の pre-remove steps と挿入側の offset 調整は共有する。

**その順序が insert とちょうど逆である。** pre-remove steps が step 10、
range の offset 調整が step 16 なので、
「removal が parent の上へ持ち上げた boundary」は move では **調整される**。
insert では step 5 が先に済んでいるので調整されない（前述）。
子が三つの parent で `parent.moveBefore(最後の子, 最初の子)` を行い、
最後の子の中に collapsed range があると、結果は `(parent, 3)` であって `(parent, 2)` ではない。

実装中に二つ間違えて、差分テストが両方とも捕まえた。

* backend node の比較に `equal?` を使っていた。
  Makiri は `parent` を呼ぶたびに同じ node に対して別の Ruby object を返すので、
  step 1 の root 比較が常に失敗して `HierarchyRequestError` になっていた。`==` に直した。
* `Dommy::Document` は `__dommy_backend_node__` を持たないので、
  `document.moveBefore(node, document)` の reference child が nil に落ちていた
  （step 3 の `NotFoundError` にならず append 扱いになる）。

これで **仕様がその kind に定めている操作は Dommy にすべてある**。
`dommy_runner.rb --capabilities` の欠落表は全 kind `(なし)` になった。

差分テストの `unsupported` は Dommy の実装漏れではなく、
harness が「存在しない id を指した引数」を意図的に飛ばしている分である
（model は `notFoundError`、Dommy は引数が nil になり WebIDL の `TypeError` 相当なので、
そのままでは意味のある比較にならない）。
その旨を `test/dommy_runner.rb` と `test/compare.rb` の表示に書いた。

## Dommy の不一致は無くなった

pin は main（`875d653`）。固定 scenario 99 本＋生成 40 本で
**136 ok / 3 skip / 0 mismatch** である。skip の三つは
`characterdata-utf16-split-is-outside-model` と
`range-insert-node-into-text-is-outside-model`（どちらも model 側の対象外）と
生成 scenario 一本である。

差分テストが出した findings は全部 Dommy 側に入った。

| finding | Dommy |
| --- | --- |
| 1-26 | 既存 |
| 6（parent の無い node） | PR 41 `7eb57a8` |
| `Node` 引数の WebIDL 変換 | PR 42 `e018027` |
| 7 / 8（`deleteContents` / `insertNode`） | PR 43 `940adb4` |
| 9（`TreeWalker.parentNode`）/ 11（CharacterData target の event path）/ `normalize` | PR 44 `9522489` |

`normalize` が `Document` と `CharacterData` にも付いたので、
前は skip だった `normalize-on-document` と `normalize-on-text-is-noop` も
比べられるようになり、どちらも一致している。

**finding 4**（Makiri 側の `XML::DocumentFragment#add_child`）だけは Dommy の外である。

## Phase 8：MutationObserver の record（一巡した）

`PLAN.md` §11 の判断材料は「Phase 4-7 の不一致の傾向」である。
そこまでに見つかった 12 件はすべて tree mutation と Range で、
**record の内容と積む位置は同じ「step の順序」の材料** だった。
Dommy の直前の commit 二つ（`8c6d030`, `a06fd1e`）も normalize の record の話であり、
実際に動いている領域でもある。よって MutationObserver に進んだ。
Shadow DOM は node tree そのものを広げるので、いまは対象にしていない。

### model（`Dom/Observer/Record.lean`）

仕様 §4.3.4 の "queue a mutation record"（target の inclusive ancestor を上へ辿り、
各 node の registered observer list を順に見て、
**初出順の map** に集め oldValue を上書きする step 2）、
"queue a tree mutation record"、および remove step 20 の
transient registered observer を実装した。

`DOMState` に observer ごとの record queue と、
node を持つ一本の registered observer list を足した。
配送（mutation observer microtask と "notify mutation observers"）は対象外なので、
record は取り出すまで貯まり、transient registration は消えない。

algorithm 側は `suppressObservers` を持つようになり、
record を仕様の位置で積む。

| step | 位置 |
| --- | --- |
| remove step 21 | detach の後 |
| insert step 4.2 | fragment の children を外した直後（`suppressObservers` に関わらず積む） |
| insert step 9 | previousSibling は step 6 の位置、つまり **木を変える前** に決める |
| replace step 10 | 一つにまとめる（古い子の除去と insert は抑制する） |
| replace all step 7 | 同上 |
| move step 23-24 | 旧 parent と新 parent に一つずつ |
| replace data step 4 | data を変える **前** に、変える前の値を oldValue として積む |

書いていて分かったことが二つある。

* remove step 20（transient observer）は step 14 の後にあり、
  「parent の ancestor は子を一つ外しても変わらない」ので detach の後に置いてよい。
  こうすると `detachWithLiveAdjust` が remove と move の共有部分のまま残り、
  既存の木 / range / iterator の定理は flag を一般化して record の wrapper を剥がすだけ
  （`remove_eq_of_detach`）で通る。
* `replaceData` は `DOMState` を field ごとに組み立てていたので、
  新しい二つの field を黙って落とすところだった。`{ s with … }` に直した。

### harness

scenario に `observers` を足した（`target` と `subtree` / `childList` /
`characterData` / `characterDataOldValue`）。
`observe(target, options)` を一度呼んだ状態にあたる。
出力は observer ごとの record 列で、Dommy 側は callback を呼ばない
（scheduler を回さない）まま `takeRecords` で取り出して貯める。
model も配送を扱わないので、これで両側が揃う。

生成器は `--observers N` を取り、
仕様の `observe` が「childList / attributes / characterData のどれかは true」
を要求するので、少なくとも一方を立てる。

### 見つかった Dommy の不一致（Dommy commit `faaeb63`）

12. **Document の subtree observer が木の外の node にも当たる。**
    `matches_document?` が subtree なら無条件に true を返していた。
    仕様は target の inclusive ancestor を辿って registration に届くので、
    切り離された node や fragment の中の node は document の registration に届かない。
    切り離された comment の `data` を変えると characterData record が積まれていた。
13. **childList record の previousSibling / nextSibling が空。**
    `before` / `after` / `append` / `prepend` / `appendChild` が渡していなかったので、
    coordinator が「入った後の位置」から推測していた。
    仕様は insert step 6、つまり **木を変える前** の挿入位置から取る。
    `parent.appendChild(parent.lastChild)` は previousSibling が
    **その node 自身** になり、後追いの推測では出せない値である。
14. **`takeRecords()` が transient registered observer を消していた。**
    仕様の `takeRecords` は「queue を複製し、空にし、返す」の三 step だけで、
    transient を終わらせるのは microtask checkpoint のほうである。
    手で record を汲むと、外した部分木の観測が黙って止まっていた。
15. **`Fragment#removeChild` が record を積まない。**
    `detach_node` を直接呼んでいた。remove step 21 は parent に record を積み、
    fragment も parent である。

修正後、`--observers 3 --move` で seed 6 個 × 各 50 scenario、不一致ゼロ。

## Phase A：admissibility（三つの木の層は全 algorithm で完了）

`notes/research-foundation-roadmap.md` §4 の `AdmissibleDOMState` を、
状態の invariant として立てて algorithm ごとに保存を証明した。

### 立てた層

| 層 | module | 内容 |
| --- | --- | --- |
| `StructurallyValid` | `Dom/Validity/Structural.lean` | `WellFormed` に加えて、Document は parent を持たない／leaf に children は無い／doctype の parent は Document |
| `NodeDocumentsValid` | `Dom/Validity/NodeDocument.lean` | Document の node document は自分自身／tree edge の両端は同じ node document |
| `DocumentTreesValid` | `Dom/Validity/DocumentTree.lean` | Document の children は element 高々一つ、doctype 高々一つ、Text 無し、element より後ろに doctype 無し |

`AdmissibleDOMState`（`Dom/Validity/State.lean`）はこの三つに
range の端点・iterator・observer registration の妥当性を足したものである。

### algorithm ごとの保存（`Dom/Validity/AlgorithmPreservation.lean`）

`remove` / `removeEach` / `adopt` / `insert` / `replace` / `replace all` / `move` /
`moveBefore` / `replaceData` について、三つの層すべての保存を証明した。

要になった補題は二つである。

* `documentChildrenOk_of_detach` — children から一つ外すだけなら Document の制約は保たれる。
* `documentChildrenOk_of_insertAt` — 一つ挿すときに必要なのは、
  「Text でない」「element を入れるなら他に element が無く挿入点の後ろに doctype が無い」
  「doctype を入れるなら他に doctype が無く挿入点の前に element が無い」の三つだけである。
  これは `ensure pre-insertion validity` の step 6 / 9 / 10-11 と
  `move` の step 5 / 6 が確立する事実とちょうど一致する。

`insert` は node の列をまとめて入れるので、`InsertSeqOk` を loop 不変条件として置いた。
一回の `insert` が入れる element と doctype は**合わせて高々一つ**である
（fragment の children に doctype は無く、fragment でなければ node は一つ）。
この一行が不変条件を loop で通す鍵になっている。

`replace` は検査を「`child` を除外して、木を変える前に」走らせるので、
結論を除去の後まで運ぶ必要がある。
reference child が `child` のあった位置の直後に来ること
（`replace_reference_head`）を示すと、
「後ろに doctype が無い」「前に element が無い」がそのまま移る。

### 証明が仕様・model に押し返したもの

* **`move` の step 5 が `Text` を取り違えていた**（model 側の不具合）。
  `kind == .text` で判定していたので、CDATASection を Document に move できた。
  仕様の `Text` は interface なので CDATASection を含む。`isText` に直した。
* **`moveBefore` に receiver の検査が無かった**（model 側の不具合）。
  `move` algorithm の step 1-6 は newParent が children を持てるかを検査しない。
  これは `moveBefore` が `ParentNode` の method であることによる IDL 側の制約である。
  model は任意の node id を受け取れたので、Text node の中に element を move できた。
* **roadmap §4 の `AdmissibleDOMState` は不足していた**。
  「doctype の parent は Document」を入れないと `insert` で閉じない。
  `StructurallyValid` に足した。

### loader

`Dom/Exec/Eval.lean` は初期状態と各 step で
`AdmissibleDOMState` の六つの成分をすべて検査するようになった。
固定 scenario 13 本と、seed 10 個 × 各 100 本の生成 scenario
（range 4 / iterator 2 / observer 3 / `moveBefore` あり）はすべて通り、
どの step でも invariant 違反は出ない。

### 六成分すべての保存（Phase A 完了）

木の三層に加えて、残り三つも algorithm ごとに示した。

| 成分 | module | 要点 |
| --- | --- | --- |
| iterator | `Dom/Validity/Iterators.lean` | reference を動かすのは `remove` の pre-remove steps だけ。`insertAt` と `setOwnerDocument` は既存の ancestor 関係をそのまま残す |
| range の端点 | `Dom/Validity/Admissible.lean` | `move` / `replace` / `replace all` / `adopt` の分を追加 |
| observer registration | `Dom/Validity/Observers.lean` | registration が増えるのは `remove` step 20 だけ。足される transient は既存の observer index を継ぎ、外した node を指す |

`OtherDocumentIteratorsOutside`（別 document の iterator は外す部分木の外にいる）は
`StructurallyValid` と `NodeDocumentsValid` と `IteratorsValid` から出るので、
この三つを束ねた `IterCtx` を運ぶ形にした。
`ChildCountKind` も `StructurallyValid` から出るので、
どちらも定理の仮定として外から渡す必要が無くなった。

### public API（`Dom/Validity/Admissible.lean`）

`appendChild` / `insertBefore` / `replaceChild` / `removeChild` / `replaceChildren` /
`before` / `after` / `replaceWith` / `remove` / `moveBefore` と
CharacterData の四つについて、`AdmissibleDOMState` の保存を示した。
`sorry` は無く、依存する axiom は `propext` / `Classical.choice` / `Quot.sound` だけである。

最後に埋まったのは pre-insert の step 2-3（自分自身の直前に挿すときの reference child のずらし）で、
`ensurePreInsertionValidity_shift` として独立に示した。
ずらした先より後ろにある node は元の reference child より後ろにもあり、
doctype は element ではないので、step 9 と step 10-11 の検査はそのまま通る。

### oracle が自分の invariant を破らないこと（`Dom/Exec/Invariant.lean`）

`runOperations_no_violation`：admissible な初期状態から始めれば、
`runOperations` の実行時検査は決して発火しない。
`invariantViolation` が出たら model の algorithm ではなく
harness の側（初期状態の構築や操作の割り当て）を疑えばよい、と形式的に言えるようになった。

## §7 の主定理と §8 の negative result

`notes/research-foundation-roadmap.md` §7 と §8 に挙がっていた定理を入れた。

### §7（`Dom/Exec/Invariant.lean`）

| 定理 | 内容 |
| --- | --- |
| `admissible_applyOperation` | 一つの操作は admissibility を保つ |
| `run_preserves_admissibility` | 有限の操作列も保つ |
| `reachable_admissible` | admissible な初期状態から到達できる状態は admissible |
| `runOperations_no_violation` | oracle の実行時検査は決して発火しない |

`ReachableFrom` は public API だけで構成できることを表す帰納的述語で、
局所不変条件の閉包である `AdmissibleDOMState` とは別概念として分けてある。

### §8（`Dom/Properties/Counterexample.lean`）

`exists_insert_breaking_boundaryLE`。
admissible な状態と、両端が正しく並んだ range と、一回の `insertBefore` があって、
操作後も状態は admissible で range の両端は木の中にあるのに、start ≤ end が成り立たない。

反例の状態は具体的に構成してあり、証明は `decide`（kernel で評価する）だけを使う。
`native_decide` は使っていないので、依存する axiom は
`propext` / `Classical.choice` / `Quot.sound` の三つだけである。

| node | kind | 備考 |
| --- | --- | --- |
| 0 | Document | |
| 1 | element | children は [2, 3] |
| 2 | Comment | data "cc" |
| 3 | Text | data "tt" |

range は start = (2, 0)、end = (3, 2)。
`element1.insertBefore(text3, comment2)` の後、children は [3, 2] になり、
range は start = (2, 0)、end = (1, 1) になる。
node 2 は index 1 なので start は end より後ろである。

原因は step の順序である。insert step 5（parent を指す boundary point の offset を `+count`）は
step 7 の adopt → remove より前に走る。
動かす node の中にあった boundary point は step 7 で `(旧 parent, 旧 index)` に出るが、
その時点で step 5 の `+count` はもう済んでいる。
node 自身はその位置より前に入るので、start と end が逆転する。

系として `boundaryLE_not_preserved_by_insert` も置いた。
`AdmissibleDOMState` に `BoundaryLE` を入れると `insert` で閉じない、という形である。
`Dom/Validity/State.lean` が range について両端の validity しか要求しない理由がこれで形式的になった。

同じ例の JSON 版が `test/scenarios/range-order-broken-by-insert.json` である。

## 観測モデル（roadmap §9）

差分テストで **何を比べるか** を Lean 側の型で固定した（`Dom/Observation.lean`）。

```lean
structure ObservedNode where
  id : NodeId
  kind : NodeKind
  parent : Option NodeId
  children : List NodeId
  nodeDocument : NodeId
  data : String

structure Observation where
  nodes : List ObservedNode
  ranges : List RangeState
  iterators : List IteratorState
  records : List (List MutationRecord)
  result : OperationResult

def observe (s : DOMState) (result : OperationResult) : Observation
```

`Dom/Exec/Json.lean` はこの `Observation` を serialize するだけになった。
Lean と Dommy の内部表現が同じである必要は無く、
同じ `Observation` に落ちることを「一致した」の意味とする。

比較対象に足したものが二つある。

* **node document**。これまで JSON に出していなかった。
* **例外の後の状態**。失敗した step でも観測を出すようにしたので、
  「失敗した操作が状態を変えていないこと」を比べられる。
  Dommy は木をその場で書き換えるので、これは実際に意味のある比較である。

比較しないもの（`Dom/Observation.lean` の doc comment に列挙）は、
store の表現、object identity、文字列の内部表現、MutationObserver の配送、Shadow tree である。

生成器の「存在しない id」の混入率は 0.15 から 0.05 に下げた。
Dommy 側には存在しない node を渡しようが無く、その step 以降は比較できないので、
差分テストの予算を食うだけだったためである。
seed あたり 100 本で比較できる scenario が 36-47 本から 89-95 本に増えた。

### 見つかった Dommy の不一致（Dommy commit `60e1335`, `0f64b92`, `40e1a33`）

16. **`Node.ownerDocument` が Element と Attr にしか無い。**
    IDL は `Node` の attribute なので、Text / Comment / ProcessingInstruction /
    CDATASection / DocumentFragment / DocumentType も答えなければならない。
    Ruby から呼ぶと `NoMethodError` になっていた。
17. **挿入点を木が動いた後に読んでいる。**
    "queue a tree mutation record" の previousSibling / nextSibling は
    algorithm が決めた挿入点、すなわち **何も動く前** の値である
    （insert step 6、replace step 4）。
    `insertBefore`（Element / ShadowRoot / Document）と `replaceChild` / `replaceWith` が
    後から読んでいたので、挿入する node が挿入点の兄弟だった場合に値がずれていた。
    さらに `DocumentFragment#insertBefore` は挿入の record をそもそも積んでいなかった。
18. **抑制された removal で transient registered observer を登録しない。**
    remove step 20 は `suppressObservers` に **かからない**（かかるのは step 21 の record だけ）。
    replace all step 3、insert step 4、replace step 7 はどれも抑制付きで remove するので、
    subtree observer が外されたばかりの部分木の変更を見失っていた。
    step 20 を removal の primitive（`Document#detach_node`）へ移した。
19. **`x.replaceWith(x)` が replace ではなく pre-insert になっていた。**
    "convert nodes into a node" が引数を動かすのは二つ以上のときだけ（fragment を作るため）で、
    一つなら何も動かない。したがって step 5 の「this の parent が parent」は真のままであり、
    replace step 7 は「child の parent が非 null」でないので removedNodes は空になる。

修正後、seed 10 個 × 各 100 本（range 4 / iterator 2 / observer 3 / `moveBefore` あり）で不一致ゼロ。

## 契約の棚卸し（roadmap §6）

五種類の契約について、中心 algorithm ごとの現状を並べる。
`—` は「この algorithm では意味を持たない」、空欄は未着手である。

| algorithm | preservation | success | exception | effect | frame |
| --- | --- | --- | --- | --- | --- |
| `remove` | `admissible_remove` | `remove_succeeds_iff` | `remove_error_iff` | `remove_parentOf`, `remove_not_mem_childrenOf`, `detach_childrenOf`, `remove_ranges`, `remove_iterators` | `detach_frame` |
| `insert` | `admissible_insert` | | `ensurePreInsertionValidity_step1/2/3`（順序） | `insert_parentOf`, `insert_children_split`, `insert_preserves_endpoints` | `insertAt_frame` |
| `replace` | `admissible_replace` | | `replace_cycle_precedes_notFound` | `replace_reference_head` | `insertAt_frame`, `detach_frame` |
| `replace all` | `admissible_replaceAll` | | — | `removeEach_childrenOf_nil` | `insertAt_frame`, `detach_frame` |
| `move` | `admissible_move` | | `moveValidity_step1/2/3/4`（順序） | `move_eq_remove_insertAt`, `move_parentOf`, `move_childrenOf`, `move_ranges`, `move_iterators` | `insertAt_frame`, `detach_frame` |
| `replace data` | `admissible_replaceData` | | | `replaceData_ok` | `get?_withData` |

`*_succeeds_iff` を `insert` / `replace` / `move` に置いていないのは、
`ensure pre-insertion validity` と `move` の step 1-6 をそのまま命題に写すだけになり、
研究上の内容が増えないためである（roadmap §6 の但し書き）。
代わりに **検査の順序** を残した。複数の違反が同時にあるときにどれが先に返るかは観測可能で、
Dommy で実際に不一致が見つかった箇所でもある。

```lean
theorem replace_cycle_precedes_notFound :
    replace s parent parent parent = .error .hierarchyRequestError
```

`parent.replaceChild(parent, parent)` は cycle（step 2）で止まるので
HierarchyRequestError であり、NotFoundError ではない。
親子関係を前もって見てしまう実装はここを取り違える。

public API 側は preservation と委譲を置いた（`Dom/Properties/Contract.lean`）。
`appendChild` / `insertBefore` / `replaceChild` / `removeChild` /
`replaceChildren(null)` の委譲は definitional なので `rfl` で済む。
`remove()` と `moveBefore` は分岐があるので、その条件付きで述べてある。

## Phase C / D の足回り

### 仕様トレーサビリティ（roadmap §10）

`docs/traceability.md` を用意した。
各 algorithm について、WHATWG の step 要約・実行関数・契約・固定 scenario・
Dommy 側の WPT 由来 test を一行に並べてある。
参照する `dom.bs` は `docs/spec-version.md` の固定 commit である。
仕様改訂時の追従手順（差分を取り、現れた algorithm 名で表を検索し、行ごとに review する）も書いた。

対象外は理由付きで表に並べた。Shadow DOM、MutationObserver の配送、attribute、
UTF-16 の code unit 境界、node 生成と可変長引数変換、object identity、NodeIterator の filter、
そして WebIDL の TypeError である。

### normative branch の網羅（roadmap §11.3）

scenario の件数ではなく **分岐の網羅** を指標にした。
`ensure pre-insert validity` の全分岐（step 1-11 と element / doctype の挿入検査）と、
`move` の step 1-6 および IDL の receiver 制約に、それぞれ固定 scenario を置いた。
固定 scenario は 13 本から 35 本になり、Dommy との比較は全件一致である
（`move-receiver-must-be-parentnode` は model 固有の近似なので比較対象外）。

### 期待結果の根拠（roadmap §12）

各固定 scenario に `_basis` を足した。
仕様由来か定理由来かの別、参照する `dom.bs` commit、algorithm 名と step、一行の理由である。
根拠が無いと、scenario が落ち始めたときにどちらが仕様と違うのか判定できない。

### CI（roadmap §11.1-11.3）

証明の層（`ci.yml`）は次を実行する。

* `lake build`
* `sorry` の拒否
* 公開主定理の axiom audit（`Audit.lean`）
* 固定 scenario の loader 通過と invariant 違反の検査（`dom-model --check`）

`Audit.lean` は、許容した三つ（`propext` / `Classical.choice` / `Quot.sound`）以外の
axiom に依存する定理があると elaboration に失敗する。`sorryAx` もここで落ちる。

差分の層（`differential.yml`）は Dommy の checkout と native gem の build を要するので
分けてある。手動起動で固定 scenario と固定 seed の生成 scenario、
nightly で設定三通り × seed 10 個を走らせ、最小化した反例を artifact に上げる。
固定する version は `test/pinned-versions.json` にまとめた。

## MutationObserver の配送（roadmap の「未着手」の一つ）

Phase 8 は record を積むところで止めていた。配送側（§4.3 の
"queue a mutation observer microtask" と "notify mutation observers"、
および `observe` / `disconnect` / `takeRecords`）を `Dom/Observer/Deliver.lean` に足した。

### model

callback の呼び出しは model の外にあるので、`notifyMutationObservers` は
「どの observer に何が配送されるか」を `List (Nat × List MutationRecord)` で返す形にした。

| 仕様 | 定義 |
| --- | --- |
| `observe(target, options)`（step 3 / 6 の TypeError を含む） | `MutationObserver.observe` |
| `disconnect()` | `MutationObserver.disconnect` |
| `takeRecords()` | `MutationObserver.takeRecords` |
| "queue a mutation observer microtask" | `queueMutationObserverMicrotask`, `addPendingObserver` |
| "notify mutation observers" step 5 | `removeTransients`, `notifyOne`, `notifyEach` |
| "notify mutation observers" 全体 | `notifyMutationObservers` |

`DOMState` に `microtaskQueued : Bool` と `pendingObservers : List Nat` が要る。
前者は "queue a mutation observer microtask" の step 1（すでに queue 済みなら何もしない）、
後者は notify が畳む対象である。
`DOMException` に `typeError` を足した。

### 仕様の読み方を一箇所決めた

"notify mutation observers" step 5.2 と `observe` step 7.1 は、transient registered observer を
**observer の node list に載っている node から** 取り除く。
一方 remove step 20 は transient を「外す node」の registered observer list に足すだけで、
node list には触れない。本文どおりだと transient は決して掃除されないので、
remove step 20 が node list にもその node を足すと読んだ
（`addTransientObservers` が `ObserverState.nodeList` に append する）。
ブラウザと Dommy もそう振る舞う。
この判断は `Dom/Observer/Deliver.lean` の冒頭に書いてある。

### admissibility

配送は木・range・iterator を動かさないので、六成分はそのまま通る
（`Dom/Validity/Admissible.lean`）。

`admissible_observe`, `admissible_disconnect`, `admissible_takeRecords`,
`admissible_removeTransients`, `admissible_notifyEach`, `admissible_notifyMutationObservers`。
`notifyEach` は observer を一つずつ畳むので、帰納法で
`admissible_takeRecords` と `admissible_removeTransients` に落ちる。

### 観測モデルと harness

`Observation` に `delivered` を足した。`records`（各 observer の queue）だけでなく、
**どの observer にどの順で**配送されたかを比べる。
`test/dommy_runner.rb` は本物の `MutationObserver` を動かし、
callback が呼ばれた順にそのまま記録する。
`test/generate.rb` に `OBSERVER_OPS`（`observe` / `disconnect` / `takeRecords` / `notify`）を足し、
`--observers N` を指定したときだけ混ぜる。

`delivered` の比較を入れた最初の版は harness 側が壊れていた
（`deliveries.each_with_index` で observer index 順に並べ直してしまい、callback 順を落としていた）。
Dommy 側の修正を stash して A/B を取り、順序の不一致が本物であることを確かめてから直した。

### 見つかった Dommy の不一致（Dommy commit `aff1882`）

20. **通知順が inclusive ancestor の walk に従っていない。**
    "queue a mutation record" は target の inclusive ancestor を上へ辿り、
    各 node の registered observer list を順に見る。
    transient registered observer は外された node の list に **append** されるので、
    その node に元から付いていた registration より後に来る。
    Dommy は observer の生成順で並べていたので、
    `remove` で transient が付いた subtree observer が、
    その node 自身の registration より先に呼ばれることがあった。
    `@observed` の entry と `@transients` に単調増加の sequence number を振り、
    `matching_key(chain, target, type) = [chain_index, seq]` で並べるようにした。
21. **その record type を要求していない registration が、要求している registration を隠す。**
    `find_matching_entry` が scope（`subtree` と target の一致）だけで最初の登録を返し、
    呼び出し側がその登録の `characterData` を見て記録を諦めていた。
    同じ observer が同じ木に二度登録していて、先の登録がその type を求めていないと、
    後の登録が求めていても record がまったく積まれない。
    述語を `entry_in_scope?` と `entry_wants?` に割り、type を呼び出し側から渡すようにした。

どちらも生成 scenario で見つけた。最小化したものを固定 scenario に入れてある
(`observer-transient-follows-existing-registration`,
`observer-uninterested-registration-does-not-shadow`)。
いずれも Dommy `aff1882` の一つ前では不一致になり、`aff1882` では一致することを確認した。

### 修正後の一致状況

固定 scenario 38 本（うち `move-receiver-must-be-parentnode` は model 固有で比較対象外）と、
生成 scenario 1600 本（seed 8 個 × 200 本、`--observers 3`）で不一致ゼロ。
残りは `unsupported`、すなわち scenario が作っていない node id を harness が断ったものである。

## MutationObserver の attribute（roadmap の「未着手」の残り）

`attributes` / `attributeOldValue` / `attributeFilter` を扱うには model に attribute が要る。
`NodeData` に attribute list を足し、§4.9 の algorithm と §1.3 の名前検査を入れた。

### model

| 仕様 | 定義 | module |
| --- | --- | --- |
| attribute（`Attr` の namespace / prefix / local name / value） | `Attr` | `Dom/Basic/NodeId.lean` |
| valid namespace prefix / valid attribute local name | `isValidNamespacePrefix`, `isValidAttributeLocalName` | `Dom/Attribute/Name.lean` |
| validate and extract（context は "attribute"） | `validateAndExtractAttribute`, `validateAndExtractError` | 同上 |
| get an attribute by name / by namespace and local name / get an attribute value | `getAttributeByName`, `getAttributeByKey`, `getAttributeValue` | `Dom/Attribute/Algorithms.lean` |
| handle attribute changes | `handleAttributeChanges` | 同上 |
| change / append / remove an attribute | `changeAttribute`, `appendAttribute`, `removeAttributeFrom` | 同上 |
| set an attribute value | `setAttributeValue` | 同上 |
| `setAttribute` / `setAttributeNS` / `removeAttribute` / `removeAttributeNS` / `toggleAttribute` | 同名 | 同上 |
| `getAttribute` / `hasAttribute` / `getAttributeNames` | 同名 | 同上 |

attribute は仕様では `Attr` node だが、model では element の状態として持つ。
node tree に入らない（parent を持てず tree order にも現れない）ので、
`Tree` の不変条件に絡まないためである。
その帰結として `setAttributeNode` と `NamedNodeMap`、および
"set an attribute" / "replace an attribute" は扱わない。

`DOMException` に `InvalidCharacterError` と `NamespaceError` を足した。
receiver が Element でない場合は WebIDL の TypeError を返す。

### `MutationObserverInit` の「省略」を表に出した

IDL は `childList` / `subtree` / `attributeOldValue` / `characterDataOldValue` に
`false` の既定値を与えるが、`attributes` と `characterData` には与えない。
`observe` の step 1-2 が「**存在しない** なら true にする」なので、
この二つは `Option Bool` で持つことにした（`MutationObserverInit.resolve` が step 1-2）。

これで step 3-6 の TypeError が四通りそろう（`observeOptionsError`）。
それまでの model は `{characterDataOldValue: true}` で `characterData` を省いた場合に
TypeError を返していたが、仕様は step 2 でそれを observing な registration にする。

`attributeFilter` は存在の有無に意味がある。
"queue a mutation record" step 2.3 の三つ目の条件は
「filter が **存在して**、name を含まないか namespace が非 null なら積まない」である。
namespace 付きの attribute は filter では拾えない。

### 第七成分 `AttributesValid`

* Element 以外は attribute を持たない。
* 一つの element の attribute list は (namespace, local name) で一意である。
* prefix があるなら namespace もある。

二つ目は仕様が明文で書いていないが、"get an attribute by namespace and local name" が
「その attribute（あれば）」と単数で書いているのはこれを前提にしている。
三つ目は二つ目を保つのに要る。prefix 付き・namespace 無しの attribute があると、
`setAttribute` が qualified name で探して見つけられないまま同じ鍵の attribute を append してしまう。
"validate and extract" の step 8 が毎回これを保証している
（`validateAndExtractAttribute_ok`）。

§4.2.3 の algorithm はどれも attribute を触らないので、この成分は自動的に保たれる。
`KindPreserving` を `ShapePreserving` に広げ、kind と並べて attribute list も運ぶようにした
（`Dom/Properties/Algorithms.lean`）。既存の保存補題はすべてそのまま通る。

逆に §4.9 の algorithm は attribute しか変えないので、他の六成分が保たれることを
`AttributesOnly`（attribute list 以外を変えない変更）で一度に示した
（`Dom/Validity/Attributes.lean`）。

public API の保存は `admissible_setAttribute` / `_setAttributeNS` / `_removeAttribute` /
`_removeAttributeNS` / `_toggleAttribute`。

### 契約

* `setAttribute_getAttribute` — 書いた値は同じ qualified name で読み戻せる。
  鍵の一意性が要る（同じ鍵が二つあると step 5 が前を書き換えて step 4 が後ろを見る）。
* `removeAttribute_erases` — qualified name で見つけた一つだけを外す。
  qualified name が同じでも namespace が違えば残る、という仕様どおりの弱い形である。
* `validateAndExtractAttribute_ok` — 返す namespace は正規化済みで、prefix があれば namespace もある。

### 実行時検査と loader の穴（指摘による）

`AdmissibleDOMState` は六成分を持ち `checkAdmissibleDOMState` は六成分すべてと同値だったが、
`buildState` と `runOperations` は五成分しか見ていなかった。
存在しない node を対象とする observer を含む scenario が終了コード 0 で通っていた。
どちらも七成分すべてを検査するようにし、`runOperations_no_violation` に分岐を足した。
`Dom/Validity/State.lean` の `ReachableFrom` の参照先も
`Dom/Properties/Trace.lean` から `Dom/Exec/Invariant.lean` に直した。

### 見つかった Dommy の不一致（Dommy commit `8b0e4bb`）

22. **oldValue を registration 一つからしか読んでいない。**
    "queue a mutation record" step 2.3.3 は、条件を満たす registration を **すべて** 回り、
    old value を要求するものがあればそこで oldValue を立てる。
    Dommy は探索が最初に当たった registration の
    `characterDataOldValue` / `attributeOldValue` だけを見ていたので、
    同じ observer の別の registration が要求していても `oldValue` が null になっていた。
23. **`attributeFilter` が registration ごとの条件になっていない。**
    filter は step 2.3 の条件の一部（三つ目の bullet）であって、
    observer 単位の後置きの絞り込みではない。
    filter がこの attribute を含まない registration が、
    同じ observer の filter 無しの registration を隠していた。
    namespace 付きの attribute を filter が拾わないことも同じ bullet なので、
    まとめて `entry_wants?` に移した。
24. **attribute を local name で引いていた。**
    `getAttribute` / `setAttribute` / `removeAttribute` / `hasAttribute` / `toggleAttribute` は
    どれも **qualified name** で attribute を同定する。
    backend の `node[name]` は local name で引くので、`xml:b` を持つ element に対して
    `getAttribute("b")` がその値を返し、`setAttribute("b", v)` が `xml:b` を上書きし、
    `toggleAttribute("b")` が追加ではなく削除になっていた。
    `Attr#value` も同じ取り違えで、同名の二つが互いの値を報告していた。
    `Backend.attr_by_qualified_name` を足して、この一族をすべてそこへ通した。

    この修正は Dommy 側で二つ目の不具合を表に出した。それまで backend が
    `setAttribute("xmlns", …)` の書き込みを XMLNS namespace の attribute にしていたため、
    XML serializer が「namespace で declaration を見分ける」実装でも動いていた。
    仕様どおり null namespace に置くようにした結果、その attribute が
    default namespace の declaration として扱われなくなり、
    element の namespace と食い違うときに落とされないまま二重に出力されていた
    （`<manifest xmlns="" xmlns="…opf"/>`、well-formed XML ではない）。
    WPT の "Drop inconsistent xmlns=... by matching on local name" のとおり
    local name で見分けるように直した（Dommy commit `ec859a9`）。
    差分テストではなく WPT で出たものなので、通し番号は振っていない。

### 一致状況

固定 scenario 41 本（うち `move-receiver-must-be-parentnode` は IDL 由来の検査を固定する
scenario で、Dommy 側は `NoMethodError` になるため比較対象外）と、
生成 scenario 2000 本（seed 10 個 × 200 本、`--observers 3 --move`）で不一致ゼロ。

`DOMException` に `typeError` が入ったので、`moveBefore` の receiver が `ParentNode` で
ないときの例外を HierarchyRequestError の代用から本来の TypeError に直した。

## NodeIterator の `whatToShow`（対象外だったものの一つ）

`NodeFilter` の callback は model の外にあるので filter は常に null のままだが、
`whatToShow` は node type の bitmask で純粋に決まるので、これは model にできる。

仕様の iterator collection は「root を根とし、filter がどの node にも一致する collection」、
すなわち root の inclusive descendant 全部であって、`whatToShow` はそこには効かない。
効くのは traverse の中の "filter" で、bit の立っていない node は FILTER_SKIP になり、
accept するまで先へ進む（traverse step 3.1-3.3）。
filter が null なら、これは「bit の立っている最初の候補を探す」ことになる。

| 仕様 | 定義 |
| --- | --- |
| `nodeType` の数値 | `NodeKind.nodeType`（`Dom/Basic/NodeId.lean`） |
| filter（filter は null なので step 1-2 だけ） | `showsNode` |
| traverse（next / previous） | `nextNode`, `previousNode` |

`IteratorState` に `whatToShow : Nat`（既定は `SHOW_ALL`）を足した。
`ValidIterator` は変わらない（reference が木にあり root の inclusive descendant であること）。
候補は collection の部分列から選ぶので、`validIterator_nextNode` /
`validIterator_previousNode` も同じ形で通る。

生成器は半分を `SHOW_ALL`、残りを element / text / comment などの組にする。
固定 scenario は `iterator-whattoshow-skips`。

### 見つかった Dommy の不一致（Dommy commit `40db924`）

25. **Document を parent とする `replaceChild` に DocumentFragment の分岐が無い。**
    `Document#replaceChild` は fragment を adopt してその 1 node を入れていたので、
    fragment の children が取り出されないままだった。
    "replace" step 9 の insert は step 1 で fragment の children を取り除く。
    これは suppressObservers にかからない removal なので、
    live range と NodeIterator の pre-remove steps が走り、
    fragment には childList record が積まれる。飛ばしていた結果、

    * fragment の中を指していた live range が、動いた後の子を指したまま残る
    * insert step 5 の range のずれが children の個数ではなく 1 になる
    * childList record の addedNodes が children ではなく fragment になる

    `Element#replaceChild` は共通の経路を通っていて正しく、
    Document 固有の実装だけが抜けていた。
    `document_insert_before` と同じ helper を使い、取り出しを
    step 7（置き換えられる child の removal）の後に置くようにした。
    iterator を 3 本に増やした sweep で出た（それまでは 1 本だったので当たらなかった）。

固定 scenario は `document-replacechild-fragment`。

## element の namespace と local name（対象外だったものの一つ）

attribute の名前を ASCII lowercase するかどうかは、element が HTML namespace にあって
その node document が HTML document かで決まる
（"get an attribute by name" step 1、`setAttribute` step 2、`toggleAttribute` step 2）。
model に element の namespace が無かったのでこの分岐は走らず、
「model の element は HTML namespace に無い」という近似で済ませていた。
`NodeData` に element の namespace / prefix / local name と、
Document の type（HTML document かどうか）を足して、この近似を外した。

| 仕様 | 定義 |
| --- | --- |
| Element の namespace / namespace prefix / local name | `NodeData.namespace` / `.prefix` / `.localName` |
| Document の type が "html" | `NodeData.isHTMLDocument` |
| §1.4 qualified name | `NodeData.qualifiedName` |
| §1.3 valid element local name | `isValidElementLocalName` |
| Infra の ASCII lowercase / uppercase | `asciiLowercase`, `asciiUppercase` |
| §4.8 `Element.tagName` | `tagName` |
| 名前の正規化（上の三箇所に共通） | `attrNameFor` |

`NodeData.shape` を「parent・children・node document・data を落とした残り」に変えた。
以前は (kind, attributes) の組だったが、落とす側を並べる形にすると
`NodeData` に field が増えても自動的に `ShapePreserving` の保存対象に入る。
`AttributesOnly` は元から同じ形（attribute だけを落とす）だったので変えていない。

element の名前の妥当性（Element だけが名前を持つ、valid element local name である、
prefix があるなら namespace もある）は loader が検査する。
`AdmissibleDOMState` の成分にはしていない。node 生成は model の対象外（roadmap §13.2）で、
これを崩せる algorithm が無いためである。

観測には namespace / prefix / local name / `tagName` を加えた。
生成器は element の 3/4 を HTML namespace の `div` / `span` / `p`、
残りを SVG namespace の `rect`（一部は prefix 付き）にし、
attribute の操作に渡す名前には大文字を混ぜる。
固定 scenario は `attribute-name-case-follows-namespace` と
`record-attribute-name-keeps-case`。

### 見つかった Dommy の不一致（Dommy commit `8011543`）

26. **mutation record の attributeName を無条件に小文字化していた。**
    record の attributeName は attribute の local name である。
    名前を折りたたむのは `setAttribute` の step 2 だけで、しかも
    HTML namespace の element が HTML document にあるときに限る。
    record を積む時点では名前は決まっているのに、
    `notify_attribute_mutation` が「attribute の namespace が null なら」という条件で
    もう一度小文字にしていたので、SVG element に `A` を置くと record は `a` になり、
    `a` だけを挙げた attributeFilter が `A` の変更を拾っていた。
    ついでに record の newValue の読み戻しも、local name で引く
    `target_node[attr]` から namespace 込みの読みに直した。

## UTF-16 の code unit 境界（(b) で対応した）

仕様の offset は UTF-16 の code unit の index である
（`CharacterData.length`、CharacterData の offset と count、
CharacterData node を指す Range の boundary point）。
model は Lean の `String` を使うので code point で数えていて、
一致するのは BMP の範囲だけだった。
`"a😀b"` は仕様の length が 4、model では 3 になるので、
`deleteData(3, 1)` は仕様では `"b"` を消すが model では何もしなかった。
差分テストの相手である Dommy は `Dommy::Internal::Utf16` で code unit を数えているので、
食い違っていたのは model の側である。

**「UTF-16 として正しく動く範囲を明示した部分モデル」** にした。
長さと offset は code unit で数え、切断は scalar 境界でだけ定義する。

| 仕様 | 定義 | module |
| --- | --- | --- |
| code point が占める code unit 数 | `Utf16.unitsOf` | `Dom/Basic/Utf16.lean` |
| UTF-16 の code unit 数 | `Utf16.length`, `Utf16.lengthOfList` | 同上 |
| code unit `n` で分ける（境界でなければ `none`） | `Utf16.splitAt?` | 同上 |
| §4.10 replace data の step 5-7 | `spliceData?` | `Dom/CharacterData/ReplaceData.lean` |
| §4.4 node length | `NodeData.length`（CharacterData は `Utf16.length data`） | `Dom/Basic/NodeId.lean` |

### 側条件を Range へ持ち出さない

boundary point が surrogate pair の途中を指すことと、そこで文字列を切ることは別である。
仕様の boundary point は offset が node の長さ以下であることしか求めておらず、
scalar 境界であることは要求しない。`"a😀b"` の offset 2 は妥当な boundary point で、
数値として持ち回るだけなら文字列を切らないので model でもそのまま扱える。

そこで境界の検査は切断の中だけに置いた。
`spliceData?` が成功したことから長さの等式 `length_spliceData?` が出るので、
Range の保存証明はその等式だけを使う。
`replaceData_preserves_endpoints` はもともと `replaceData … = .ok s'` を前提にしていて、
そこから等式を取り出せるため、**公開する保存定理に新しい側条件は増えていない**。

### 対象外の印を仕様の例外と混ぜない

surrogate pair を割った切り出しは、仕様では定義されているが
Lean の `Char`（surrogate を除いた Unicode scalar value）では表せない。
これを `IndexSizeError` などの仕様の例外にすると、
「仕様どおりに失敗した」ことと区別がつかなくなる。
`DOMException.outsideModel`（名前は `__outsideModel__`）という専用の印を返し、
差分テストはその step 以降を比較しない。

Ruby の UTF-8 String も lone surrogate を持てないので Dommy も同じところで断るが、
**両者が同じところで失敗することは仕様適合の証拠にならない**。
harness は Dommy 側のその失敗も `__unsupported__` として扱い、一致とは数えない。

### 検証

生成器は CharacterData の初期 data の 1/4 に astral character を混ぜ、
`appendData` / `insertData` / `replaceData` / `setData` にも astral を渡す。
pair をまたぐ offset と pair の途中を指す offset の両方が出る。

astral を含む生成 scenario 89 本のうち 76 本が最後まで比較できて一致し、
13 本は pair を割る操作の手前まで比較できた。
固定 scenario は `characterdata-utf16-offsets`（pair の途中を指す boundary point、
pair をまたぐ削除と挿入、offset 調整）と
`characterdata-utf16-split-is-outside-model`（対象外の切断）。

### 見つかった model の不具合

27. **transient registered observer を transient の source にしていなかった。**
    仕様の transient registered observer は「source を持つ registered observer」であり、
    それ自身が registered observer list の要素である。
    したがって remove step 20 の「inclusive ancestor の registered observer list を見る」は
    transient も拾い、外れた部分木の中でさらに removal が起きても追跡が途切れない。
    model は `!r.transient` で除いていたので、二段目の removal で record を落としていた。
    `docs/status.md` の finding 9 に続く、二件目の model 側の不具合である。
    固定 scenario は `transient-observer-chains-through-removals`。

## 戻り値（object identity のうち観測できる部分）

observation は `ok` / 例外 / 状態しか比べておらず、**method の戻り値を捨てていた**。
`toggleAttribute` の `Bool` は model がすでに計算していたのに
`applyOperation` が `Prod.fst` で落としていたし、
`nextNode()` / `previousNode()` が返す node も `stepIterator` が捨てていた。
つまり `toggleAttribute` の返り値も iterator の返り値も、
全部間違っていても差分テストは通る状態だった。

戻り値はどれも **操作前の状態と操作だけ** で決まるので、
すでにあった `deliveredBy` と同じ形で `returnValueOf` を足した。
`applyOperation` の型も `admissible_applyOperation` も
`runOperations_no_violation` も変えていない。

| 操作 | 戻り値 | 仕様 |
| --- | --- | --- |
| `appendChild` / `insertBefore` | 入れた node | pre-insert step 5 |
| `replaceChild` / `removeChild` | 取り除いた側の child | replace step 11 / pre-remove step 3 |
| `nextNode()` / `previousNode()` | traverse が返した node、端なら null | traverse step 6 |
| `toggleAttribute` | attribute が結果として付いているか | toggleAttribute step 4-6 |
| `takeRecords()` | 空にする前の record queue | takeRecords step 1-3 |
| それ以外 | `undefined` | |

観測には kind を添える。`null` を返すことと `undefined` を返すことは別で、
`removeChild` が null を返したら不一致だが `remove()` が undefined を返すのは正しい。
失敗した step には戻り値が無いので、その step では field ごと出さない。

`Attr` の identity（`setAttributeNode`、`NamedNodeMap`、`InUseAttributeError`）は入れていない。
attribute を element の状態から object に変える構造変更が要るわりに、対象 API が狭い。

### node の identity

harness は Dommy の object を `equal?` で id に引いている。
`==` のフォールバックを外した。
WHATWG の adopt は node を作り変えずに動かすので、
wrapper が作り直されたら不一致になるべきである
（Makiri は arena をまたいで node を移動できないため、Dommy はここを明示的に維持している）。

固定 scenario は `return-values`。
`toggleAttribute` の step 4-6 の四通り（attribute の有無 × force の有無）、
collection の端で null を返す `nextNode()`、
空にする前後の `takeRecords()`、`undefined` との区別を通す。

## `Node.normalize()`（§4.4）

Dommy が実装しているのに oracle の無かった algorithm の一つ。
model（`Dom/CharacterData/Normalize.lean`）と保存の証明
（`Dom/Validity/Normalize.lean`）を置き、`Operation.normalize` として
差分テストに載せた。

### 算法

descendant の exclusive Text node を tree order で辿り、
長さ 0 のものを外し（step 2）、続く exclusive Text の兄弟を先頭へ畳む。
畳む側は `replaceData` と `remove` の合成で、その間に boundary point の
引き渡し（step 6.1-6.4）を挟む。**引き渡しは remove より前**でなければならない。
後にすると live range の pre-remove steps が boundary point を parent 側へ移してしまう。

保存の証明で新しいのは引き渡しの部分だけである。
消える兄弟の中を指していた boundary point は survivor の継ぎ目より後ろへ移るが、
その時点で survivor の長さは「継ぎ目 + 兄弟の長さ」まで伸びているので、
端点は木の中に収まったままである（`endpointsValid_normalizeMerge`）。

### record の並びは仕様と engine で違う

仕様を字義どおり読むと、step 3-4 は run 全体の data を一度に連結して
"replace data" を一回呼ぶので、characterData の record は run ごとに一つになる。
実際の engine（Blink・WebCore・Gecko）は兄弟ごとに畳み、
四つの Text の run に対して characterData / childList / characterData / childList …
と積む。WPT が固定しているのは childList の側だけである。

**model は engine 側の読みを採った。** 木と live range の最終状態はどちらの読みでも同じで、
違うのは record の並びだけだからである。Dommy も同じ判断をしていて
（実装の comment に三つの engine で確かめた記録がある）、
`normalize-record-order-per-sibling` で両者が一致することを確かめている。

### 見つかったこと：`normalize()` が Node に無い

`normalize()` は WebIDL では `Node` の method なので、
Document・Text・Comment・ProcessingInstruction・DocumentType でも呼べる
（descendant が無ければ何も起きないだけである）。
Dommy は ParentNode の側にしか置いていないため、次のようになっている。

| 受け手 | Dommy |
| --- | --- |
| Element / DocumentFragment | あり |
| **Document** | **無し** |
| Text / Comment / ProcessingInstruction / DocumentType | 無し |

Ruby から呼ぶと `NoMethodError`、JS bridge 経由（`__js_call__`）だと
**黙って何もしない**。Document の分は観測できる差で、
`document.normalize()` が隣り合う Text を畳まない。

差分テストの capability 報告がこれを並べる。`normalize-on-document` と
`normalize-on-text-is-noop` はその印として置いた scenario で、
Dommy が実装したら比較対象になる。

### 差分テスト

固定 scenario 六本が一致（capability の印の二本は skip）。
生成 scenario は seed 7 / 11 / 23 / 31 で不一致 0。

## `Range` の API（§5.5、boundary point を動かす側）

model の range は「scenario が初期状態として与え、木の変更が動かす」だけで、
API そのものは走らせていなかった。Dommy には `range.rb` が 1100 行あるので、
oracle の無い塊として一番大きい。boundary point を動かす method を model に入れ
（`Dom/Range/Api.lean`）、保存を証明し（`Dom/Validity/RangeApi.lean`）、
`Operation` に足して差分テストに載せた。

対象は `setStart` / `setEnd` / `setStartBefore` ほか四つ / `collapse` /
`selectNode` / `selectNodeContents` / `isPointInRange` / `intersectsNode` である。
`extractContents` ほかは node を生むので roadmap §13.2 の対象外である。
`deleteContents` / `insertNode` / `compareBoundaryPoints` / `comparePoint` は
この節の時点では未着手で、下の「木を変える側と比べる側」で入れた。

### 保存は一つの補題に落ちる

どの method も `ranges` の一要素を差し替えるだけなので、
`admissible_withRange`（差し替えた range の両端が木の中にあれば admissibility は保たれる）
に帰着する。新しい端点の妥当性の出どころは三つある。

* `setStart` / `setEnd` — 仕様の step 1-2 の検査（`rangeBoundaryError`）
* `collapse` — 元の range の端点
* `selectNode` — 「子の index は parent の length 未満」（`index_lt_children_length`）

### 見つかったこと：parent の無い node の検査が無い（findings 6）

parent の無い node は boundary point を決められないので、仕様は

* `selectNode(node)` step 2
* `setStartBefore` / `setStartAfter` / `setEndBefore` / `setEndAfter` step 2

で `InvalidNodeTypeError` を投げる。Dommy はこの検査を持たず、`parent_of(node)` の
`nil` をそのまま `set_start` へ渡すので、次のどちらかになる。

* `selectNode(document)` — **container が nil の range** ができる
  （`startContainer` は IDL で non-nullable なのに null になる）
* `setEndAfter(root)` — `nil` の length を 0 と見て `IndexSizeError`

生成 scenario 180 件で出た不一致 23 件はすべてこの一件が原因だった。
`selectNodeContents(doctype)` の step 1（`InvalidNodeTypeError`）も同じく抜けている。

`range-boundary-needs-parent` がこの四つを固定した scenario である。

**Dommy `f9618d1` で修正した。** `selectNode` と四つの sibling setter に step 1-2 を、
`selectNodeContents` に step 1 の doctype 検査を入れた
（WPT `dom/ranges/Range-selectNode.html` の判定を手で抜き出した test も付けた。
写したものではない）。

### 差分テスト

固定 scenario は `range-boundary-needs-parent` 以外の六本が一致。
生成 scenario は seed 5 / 12 / 19 で、上記以外の不一致は無い。

## `Range` の API（§5.5、木を変える側と比べる側）

boundary point を動かす側に続けて、残りの四つを入れた。
`compareBoundaryPoints` / `comparePoint` は値を返すだけ、
`deleteContents` / `insertNode` は木を変える。
`extractContents` ほかは node を生むので roadmap §13.2 の対象外のままである。

### `deleteContents`

仕様の step 4「nodes to remove」は **range に contained な node 全部**から、
親も contained なものを落としたものである（`nodesToRemove`）。
step 5-6 が新しい boundary point を決め、step 7-9 が
「start 側の切り詰め → node の削除 → end 側の切り詰め」の順に木を変える。

保存は `admissible_removeEach` と `admissible_replaceData` に落ちるが、
**step 10 が置く boundary point が最終状態でも妥当であること**は証明していない。
仕様の帰結ではあるので、model は実行時に `checkValidBoundaryPoint` で検査し、
妥当でなければ live range の調整が残した端点を使う。
差分テストでその枝に落ちたことは無い。

### `insertNode`

step 7（start node が Text なら offset で split する）は node を作るので
roadmap §13.2 の対象外で、その場合は `__outsideModel__` を返す
（`range-insert-node-into-text-is-outside-model`）。
ただし step 1 の検査はその前に置くので、
`HierarchyRequestError` になる場合はちゃんと例外になる。

step 10-11 の newOffset は「入った node の最後の次」に等しいので、
model はそちらの形で書いた（`siblingBP`）。
そうすると step 13 が置く端点の妥当性が `index` の上界から出るので、
`deleteContents` と違って実行時検査が要らない（`admissible_rangeInsertNode`）。

### 見つかったこと 1：`deleteContents` が共通祖先の子しか消さない（findings 7）

`extractContents` / `cloneContents` の step は
「common ancestor の contained な**子**」を集め、
両端に掛かる子を再帰で処理する。`deleteContents` にはその再帰が無いので、
step 4 は木全体から contained な node を集める。
Dommy は前者の helper（`nodes_to_remove` が `common_ancestor_container.child_nodes` を見る）を
`delete_contents` でも使っているので、
**共通祖先の子より深いところしか contained でない range では何も消さない**。

start node が end node の inclusive ancestor になる形が最小例で、
`range-delete-contents-partially-contained-end` と `-start` が固定した。
どちらも Dommy は木を変えない。

### 見つかったこと 2：`insertNode` の step 1 と step 9-10 の順序（findings 8）

* **step 1 の検査が無い。** start node が ProcessingInstruction / Comment、
  parent の無い Text、あるいは入れようとしている node 自身なら
  `HierarchyRequestError` である。Dommy にこの検査は無い。
  Comment が start node の場合は pre-insert の側で同じ例外になるので表に出ないが、
  **start node が Text でそれ自身を入れる**場合は通ってしまい、
  Text を split して自分自身を入れた木になる
  （`range-insert-node-start-text-is-self`）。
  parent の無い Text が start node なら黙って何もしない
  （`range-insert-node-detached-text-start`）。
* **newOffset を数える位置。** 仕様は step 9 で node を外して**から**
  step 10-11 で newOffset を数える。Dommy は外す前に数えている。
  node が同じ parent の前方にいると index がひとつずれるので、
  collapsed だった range の end が一つ後ろになる
  （`range-insert-node-moves-preceding-sibling`）。
  referenceNode が null になる形では、
  end が parent の length を超えた **妥当でない boundary point** にもなる。

### 差分テスト

固定 scenario 78 本のうち、一致 68・skip 4（model の対象外と capability の欠落）・
不一致 6 である。不一致は findings 6 が一本（`range-boundary-needs-parent`）、
findings 7 が二本（`range-delete-contents-partially-contained-end` / `-start`）、
findings 8 が三本（`range-insert-node-moves-preceding-sibling`,
`-start-text-is-self`, `-detached-text-start`）で、
**どれも Dommy を直すまで赤である**。
生成 scenario は seed 51 / 52 / 53 で、上記以外の不一致は無い。

## TreeWalker（§6.2）

`NodeIterator` は model にあったが `TreeWalker` は無かった。Dommy には
`tree_walker.rb` が 620 行あり、WPT も通している。oracle の無い塊としては
`range.rb` の次に大きい。七つの走査 method を model に入れ
（`Dom/Traversal/TreeWalker.lean`）、保存を証明し（`Dom/Properties/Walker.lean`、
`Dom/Validity/Walkers.lean`）、差分テストに載せた。

### FILTER_REJECT が出ないので、走査は列の探索になる

`NodeFilter` の callback は model の外なので filter は null である。すると
"filter" は **FILTER_ACCEPT か FILTER_SKIP しか返さない**。SKIP された node は
透けるだけなので、仕様の pointer 走査（親へ上がったり最後の子へ降りたりする loop）は
どれも「ある順に並べた候補列を、先頭から accept されるまで見る」ことに等しくなる。

| method | 候補列 |
| --- | --- |
| `nextNode` | `preorder`（root の部分木）の current より後ろ |
| `previousNode` | 同じ列の current より前を逆順に |
| `firstChild` | `preorder` の current の部分木（自身を除く） |
| `lastChild` | 同じものを `mirrorPreorder`（children を逆にたどる preorder）で |
| `nextSibling` / `previousSibling` | 段ごとに「後ろ（前）の兄弟の部分木」、尽きたら親へ |
| `parentNode` | current の祖先を root まで（root 自身も含む） |

`mirrorPreorder` が `preorder` と同じ node の集合を並べ替えただけであることは
`mem_mirrorPreorderFuel_iff` で示した。これで `lastChild` /
`previousSibling` の結果も「木の中の node」だと分かる。

`nextSibling` の段の上がり方だけは列に潰せない。上がった先が accept されるなら
そこで止まる（step 3.5）ので、祖先の chain を引数に取る再帰
（`walkerSiblingSearch`）にしてある。降りる途中の node は SKIP されたものばかりなので、
止まりうるのは current の祖先だけである。

### 不変条件は `NodeIterator` より弱い

`walkers` は `DOMState` の成分だが、**`AdmissibleDOMState` には入れていない**。

§6.2 には `NodeIterator` の "removing steps" にあたるものが無い。
current の祖先が remove されても walker は動かないので、
「current は root の inclusive descendant」という `ValidIterator` 並みの条件は
**remove で壊れる**。それは仕様どおりの挙動なので、状態の不変条件にはできない
（`walker-not-adjusted-by-remove`）。

残るのは「root と current が木にある」（`WalkersValid`）で、これは
走査が返すのが常に木の中の node であることから出る（`walkersValid_walkerStep`）。
木を変える algorithm は `walkers` を触らないので、そちらは定義から保たれる。

### 見つかったこと：`parentNode` に仕様に無い検査がある（findings 9）

仕様の `parentNode()` は「node が root でない間、親へ上がって accept を見る」だけで、
**root へ戻れるかは見ない**。current が remove で root の外に出ていれば、
外れた木の親を返す。Dommy は `reachable_from_root?` で「root から辿れる node」に
限っているので、その場合 null を返す。

`walker-parent-node-leaves-root` がそれを固定した scenario である。
`nextNode` / `previousNode` / `firstChild` / 兄弟の残りは、
外れた木の中でも仕様と一致していた（`walker-not-adjusted-by-remove`）。
食い違うのは `parentNode` だけである。

### 差分テスト

固定 scenario は 83 本になり、一致 72・skip 4・不一致 7 である。
walker の五本では `walker-parent-node-leaves-root` だけが赤で、残りは一致する。
`walker-last-child-mirrors-order` は `lastChild` の順序が
「tree order の逆」ではなく「兄弟の順だけを逆にした preorder」であることを固定している。
生成 scenario は walker の走査だけ（seed 71）、走査と remove / insert を混ぜたもの
（seed 81 / 82、計 160 本）で不一致 0 だった。
findings 9 は「current が外れた木の *内側* にいる」という狭い形なので、
生成 scenario では出ず、手で作って初めて出た。

## 値を返すだけの method（§4.4 / §4.9 / §4.10 / §5.5）

Dommy が実装していて model に無かったもののうち、**木も live object も変えない**ものを
まとめて入れた。どれも純関数なので、admissibility の保存は
「状態を返すだけ」という一本の補題（`admissible_requireNodes`）で済む。

* §4.4 `compareDocumentPosition` / `contains` / `getRootNode` / `isEqualNode` /
  `textContent`（getter）/ `nodeValue`（getter）
* §4.10 `substringData`
* §4.9 `getAttribute` / `hasAttribute` / `getAttributeNames`（model には既にあったが、
  harness から呼べていなかった）
* §5.5 `Range` の stringifier

`isEqualNode` は attribute を **順序非依存**で、しかも **prefix を見ずに**
（namespace・local name・value だけで）突き合わせる。
`Range` の stringifier の step 4 は `deleteContents` と同じ
「contained な Text を tree order で」であって、common ancestor の子ではない。

model が持っていない持ち物が二つある。DocumentType の name / public ID / system ID と
ProcessingInstruction の target で、`equals` はどちらも見る。
harness はどちらも固定値（`"html"` と `"pi"`）で作るので判定は変わらないが、
その範囲でしか検証していない。

### 実装依存の枝をどう比べるか（findings 10）

`compareDocumentPosition` の step 6 は、同じ木にない二つの node について

> DISCONNECTED と IMPLEMENTATION_SPECIFIC に、PRECEDING **か** FOLLOWING を足したもの。
> ただし**一貫していること**（"with the constraint that this is to be consistent"）

と言う。どちらを選ぶかは実装に任されているので、差分テストはその二 bit を落として比べる
（`test/compare.rb` の `normalize_returned`）。model は node id の順という全順序で決めていて、
**逆から呼べば逆の答えになる**ことを定理にした
（`compareDocumentPosition_disconnected_consistent`、`docs/theorems.md` の 11）。

Dommy は**どちら向きでも `DISCONNECTED|IMPLEMENTATION_SPECIFIC|PRECEDING`（35）を返す**。
`a.compareDocumentPosition(b)` と `b.compareDocumentPosition(a)` が両方「相手が先」になるので、
どんな全順序とも整合しない。ブラウザは逆向きの値を返す。
仕様が実装に任せているのは**選び方**であって、一貫性は任されていない。

この枝は上記のとおり比較から落としてあるので、**差分テストでは赤にならない**。
`compare-document-position-disconnected-is-consistent` を
`comparable: false` の model 固有 scenario として置き、model 側の答えを固定してある。

### 名前空間の探索（§4.4）

同じく値を返すだけだが、仕様の分岐が多いので別に入れた。
`lookupNamespaceURI` / `lookupPrefix` / `isDefaultNamespace` の三つで、
どれも "locate a namespace" / "locate a namespace prefix" を parent element へ
遡って走らせる。model では祖先の列（`elementChain`）を作って畳む形にした。

読み違えやすいところが三つある。

* `xml` と `xmlns` は木を見ずに決まる（locate a namespace の step 1-2）。
* element 自身の namespace の一致（step 3）は `xmlns` 属性（step 4）より**先**である。
  既定 namespace の属性があっても、element の namespace が勝つ。
* step 4 は属性が見つかった時点で**止まる**。値が空文字列なら null を返して、
  親へは遡らない。

`lookupPrefix` の step 1 は「namespace が一致し、かつ prefix が非 null」なので、
prefix の無い element は自分では答えられず、`xmlns:` 属性か祖先に回る。

Dommy はこの三つを `internal/namespaces.rb` と `node.rb` に持っていて、
**固定 scenario 二本と生成 scenario 140 本（seed 101 / 102）で不一致は無かった**。
ただし生成器が作る element は HTML namespace で prefix が無いものだけなので、
prefix 付きの element が絡む枝は固定 scenario でしか見ていない。

### 差分テスト

固定 scenario は 93 本になり、一致 82・skip 4・不一致 7（findings 6-9）・
model 固有 2 である。新しく入れた十本はすべて一致した。
生成 scenario は seed 91 / 92 / 101 / 102（計 260 本）で、
この範囲の操作に不一致は無い。

## event の配送（§2.7 / §2.9）

model が一行も触れていなかった最大の塊である。Dommy は `event.rb` に 2000 行持っていて
WPT も通しているのに、oracle が無かった。

### callback をどう扱うか

listener の callback は `NodeFilter` と同じく model の外である。
ただし **呼ばれた順序は観測できる**ので、scenario 側で listener に
「決まった副作用」（`ListenerAction`）を宣言させることにした。

* `stopPropagation` / `stopImmediatePropagation` / `preventDefault`
* `removeListener`（配送中に他の listener を外す）
* `addListener`（配送中に listener を足す）

観測は「呼ばれた listener の列」（`invocations`、callback 番号・currentTarget・eventPhase）と
`dispatchEvent` の戻り値である。listener list そのものは Dommy が外から見せないので、
**配送を二度行って差を見る**形にしてある（`once` や配送中の削除はこれで見える）。

### model の範囲

shadow tree が無いので retargeting も slot も composed path も要らず、
event path は target から根までの祖先列そのものになる。
`Window` が無いので Document の "get the parent" は null、
activation behavior（`click` の既定動作）は HTML 側の hook なので扱わない。
`isTrusted` は常に false なので、invoke の step 10（legacy な type の付け替え）も起きない。

### 保存は「listener list しか変わらない」に尽きる

`listeners` は `walkers` と同じく `AdmissibleDOMState` の成分ではない。
木の形とは独立で、木を変える algorithm はこれを触らないからである
（node が木から外れても listener はその node に付いたまま、というのが仕様の挙動）。
配送の側は `ListenersOnly`（listener list 以外は同じ）を
`innerInvoke` → `invokeItem` → `runPass` → `dispatchEvent` と積み上げて示し、
そこから admissibility を出した（`docs/theorems.md` の 12）。

### 見つかったこと：CharacterData を target にすると event path が壊れる（findings 11）

dispatch の step 5.9.6 は「parent が Window であるか、**target の root が parent の
shadow-including inclusive ancestor** であるなら、shadow-adjusted target が null の item を積む」
と言う。そうでない場合（= shadow の境界を越えた場合）だけ、その parent を新しい target にする。

Dommy の `root_of(node)` は `node.root_node` を、**その method を持つ node にだけ**尋ねる。
`root_node` は Element と Document にはあるが `CharacterData` には無いので、
Text / Comment / ProcessingInstruction を target にすると root が nil になり、
検査が常に false になって**祖先が次々と「新しい target」として積まれる**。結果として

* 祖先の listener の `eventPhase` が CAPTURING / BUBBLING ではなく **AT_TARGET** になる、
* `bubbles` が false でも祖先の listener が呼ばれる、
* `event.target` が配送の途中で祖先に**すり替わる**（document の listener から見ても）。

target が Element なら正しい。`event-dispatch-at-character-data-target` がこれを固定した
最小の scenario である。

### 差分テスト

固定 scenario は 97 本になり、一致 85・skip 4・不一致 8・model 固有 2 である。
event の四本のうち赤は findings 11 の一本だけで、
phase の順序・`once`・二つの stop・`preventDefault`・配送中の追加と削除はすべて一致した。
生成 scenario は seed 111 / 112 / 113（計 200 本）で不一致 5、
**すべて findings 11（target が Text / Comment / PI）**だった。
直るまで、event を混ぜた生成 scenario はこの原因で赤が出続ける。

## event の配送（§2.7 / §2.9）

model が一行も触れていなかった最大の塊である。Dommy は `event.rb` に 2000 行持っていて
WPT も通しているのに、oracle が無かった。

### callback をどう扱うか

listener の callback は `NodeFilter` と同じく model の外である。
ただし **呼ばれた順序は観測できる**ので、scenario 側で listener に
「決まった副作用」（`ListenerAction`）を宣言させることにした。

* `stopPropagation` / `stopImmediatePropagation` / `preventDefault`
* `removeListener`（配送中に他の listener を外す）
* `addListener`（配送中に listener を足す）

観測は「呼ばれた listener の列」（`invocations`、callback 番号・currentTarget・eventPhase）と
`dispatchEvent` の戻り値である。listener list そのものは Dommy が外から見せないので、
**配送を二度行って差を見る**形にしてある（`once` や配送中の削除はこれで見える）。

### model の範囲

shadow tree が無いので retargeting も slot も composed path も要らず、
event path は target から根までの祖先列そのものになる。
`Window` が無いので Document の "get the parent" は null、
activation behavior（`click` の既定動作）は HTML 側の hook なので扱わない。
`isTrusted` は常に false なので、invoke の step 10（legacy な type の付け替え）も起きない。

### 保存は「listener list しか変わらない」に尽きる

`listeners` は `walkers` と同じく `AdmissibleDOMState` の成分ではない。
木の形とは独立で、木を変える algorithm はこれを触らないからである
（node が木から外れても listener はその node に付いたまま、というのが仕様の挙動）。
配送の側は `ListenersOnly`（listener list 以外は同じ）を
`innerInvoke` → `invokeItem` → `runPass` → `dispatchEvent` と積み上げて示し、
そこから admissibility を出した（`docs/theorems.md` の 12）。

### 見つかったこと：CharacterData を target にすると event path が壊れる（findings 11）

dispatch の step 5.9.6 は「parent が Window であるか、**target の root が parent の
shadow-including inclusive ancestor** であるなら、shadow-adjusted target が null の item を積む」
と言う。そうでない場合（= shadow の境界を越えた場合）だけ、その parent を新しい target にする。

Dommy の `root_of(node)` は `node.root_node` を、**その method を持つ node にだけ**尋ねる。
`root_node` は Element と Document にはあるが `CharacterData` には無いので、
Text / Comment / ProcessingInstruction を target にすると root が nil になり、
検査が常に false になって**祖先が次々と「新しい target」として積まれる**。結果として

* 祖先の listener の `eventPhase` が CAPTURING / BUBBLING ではなく **AT_TARGET** になる、
* `bubbles` が false でも祖先の listener が呼ばれる、
* `event.target` が配送の途中で祖先に**すり替わる**（document の listener から見ても）。

target が Element なら正しい。`event-dispatch-at-character-data-target` がこれを固定した
最小の scenario である。

### 差分テスト

固定 scenario は 97 本になり、一致 85・skip 4・不一致 8・model 固有 2 である。
event の四本のうち赤は findings 11 の一本だけで、
phase の順序・`once`・二つの stop・`preventDefault`・配送中の追加と削除はすべて一致した。
生成 scenario は seed 111 / 112 / 113（計 200 本）で不一致 5、
**すべて findings 11（target が Text / Comment / PI）**だった。
直るまで、event を混ぜた生成 scenario はこの原因で赤が出続ける。

## 関係意味論の層を作り始めた（`remove`）

これまで本 model は **実行関数そのものを意味論**としてきた。
`docs/traceability.md` にも「spec relation の列は置いていない」と書いてあったとおりで、
この形だと仕様の翻訳を誤っても、その誤った関数についての定理は証明できてしまう。

そこで仕様本文から独立に書き写した関係を `Dom/Spec/` に置き、
実行関数がそれを満たすこと（soundness）を別に証明する層を作った。最初の対象は `remove` である。
`remove` は tree mutation・live range・NodeIterator・MutationObserver の四つすべてに触るので、
この層の形を決めるのにちょうどよい。

### 関係は実行側を呼ばない

`Dom/Spec/Remove.lean` は `liveRangePreRemove` / `detach` / `adjustNodePointer` /
`addTransientObservers` / `queueTreeMutationRecord` を **一つも呼ばない**。
使うのは `parentOf` / `childrenOf` / `ancestors` / `precedes` といった観測の語彙だけである。
そうしないと二層に分けた意味が無くなる。

`RemoveSpec` は仕様の副作用ごとに六つの component の連言にしてある。

| component | 仕様の step | 中身 |
| --- | --- | --- |
| `RemovePre` | 1-2 | parent が非 null |
| `RangeAdjusted` | 3 | 各 boundary point が三つの枝のどれかで決まる |
| `IteratorAdjusted` | 4 | node pointer が `PointerAdjusted` で決まる |
| `TreeRemoved` | 7 | parent の children から消える + frame |
| `TransientAdded` | 20 | transient registered observer の集合 |
| `RecordQueued` | 21 | interested な observer の queue に一つだけ積む |

component に分けたのは、`insert` へ広げるときに `TreeRemoved` 以外の骨格を
そのまま使えるからである。

### 証明で要った道具

`PointerAdjusted` の step 2「部分木の外にある最初の following」を
「その条件を満たす他のどの node より前にある」と宣言的に書いたので、
tree order の列を切ったときの補題が要った（`Dom/Properties/TreeOrder.lean`）。

* `precedes_iff_mem_after` — `n` が先行するのは列の `n` より後ろにあるものだけ
* `precedes_eq_precedesIn_preorder` — 前後関係はどの祖先を根に取っても同じ
* `precedesIn_lastD_eq_false` — 列の最後の要素は誰にも先行しない

step 21 のほうは「どの observer が record を受け取るか」を
`interestedObservers` の二重の畳み込みから取り出す必要があり、
`Dom/Properties/Record.lean` に畳み込みの一般補題（membership・重複の無さ・
record queue の変化）を置いた。これは `insert` の step でもそのまま使える。

### model 側の近似として分かったこと

* 仕様の step 20 は registered observer list にしか触れないが、model は配送時の掃除が
  届くように observer の node list にも足している。その差は record の中身には出ないので、
  `TransientAdded` は node list について何も言わない。
* `RecordQueued` は childList の record に限った形で書いてある（oldValue が付かないので
  "queue a mutation record" の step 2.3.2-2.3.3 が効かない）。
  attributes / characterData を含む一般形は `insert` 側と一緒に広げる。

### 関係が結果を一つに決めること

soundness だけでは足りない。関係が緩ければ、どんな実装でもそれを満たしてしまう。
そこで **`RemoveSpec` を満たす状態は観測として一つしかない**ことも示した
（`removeSpec_deterministic`）。

木の表現そのものは決まらない。store が association list なので、同じ `get?` を持つ
表現が複数ある。決まるのは観測——各 node の `get?`、live range、NodeIterator、
observer ごとの record queue、pending と microtask、registered observer list の所属——である。

これを書く途中で、関係が **弱すぎる箇所が二つ**見つかった。どちらも直した。

* `suppressObservers` が true の枝で observer の個数を言っていなかった。
* record を積む枝で「元からあった pending observer が残る」ことを言っていなかった。

どちらも実行関数は満たしているが、関係が言っていなければ一意性は出ない。
一意性の証明は、関係が実装を本当に縛れているかの検査になっている。

### `adopt` と `insert` も同じ形で入れた

`insert` は step 4 で `remove` を、step 7.1 で `adopt` を呼ぶ。
関係もそれぞれ `RemoveSpec` / `AdoptSpec` を composition する形にした。
**仕様本文が "remove node" / "adopt node" と書いているとおりの構成**であって、
実行関数の再利用ではない。

component は七つ。

| component | 仕様の step |
| --- | --- |
| `NodesToInsert` | 1（fragment なら children、そうでなければ node 一つ） |
| `FragmentPrepared` | 4（children を外し、抑制に関わらず fragment に record を積む） |
| `ChildIndex` / `PreviousSiblingOf` | 5 の index と 6 |
| `RangeInsertAdjusted` | 5 |
| `InsertedEach` | 7（各 node を adopt してから木に入れる） |
| `TreeRecordQueued` | 9 |

childList の record を積む step は `remove` の step 21 と同じなので、
`TreeRecordQueued` として切り出して両方で共有している。

証明で一つ手間だったのは step 5 の「child の index」である。
関係の側は「index が存在する」と書いたが、実行側は `.getD 0` で逃げている。
そこで **step 7 の最初の `insertAt` が「child は parent の子」を検査すること**から
遡って index の存在を導いた（`adopt` が外すのは入れる node だけなので、
step 5 の時点でも child は parent の子である）。

### `replace data` と、oldValue が載る条件

§4.10 の `replace data` も入れた。木の形は変えず、一つの node の data と
live range の offset、それに characterData の record を動かす step である。

ここで record の関係を広げた。childList の record は oldValue を持たないので
「interested な observer の queue に一つ積む」で済んだが、characterData は
**oldValue が載る条件**がある。仕様の "queue a mutation record" は
observer を初出順に集めつつ、同じ observer が二度出たら oldValue を上書きする。
つまり載るのは「その observer の registration のどれかが `characterDataOldValue` を持つとき」である。
`CharacterDataOldValueWanted` がその条件で、畳み込みがそれを計算していることを
`mem_pair_interestedObservers` で示した。

### 観測が等しい状態どうしの congruence

`insert` のように関係を繋いだものの一意性には、`remove` 単体の一意性では足りない。
途中の状態は **観測としてしか**一致しないので、
「入力の観測が等しければ出力の観測も等しい」（congruence）が要る。

まず観測の等しさを定義した（`Dom/Spec/ObsEq.lean`）。
木は表現ではなく `get?` の一致（`TreeObsEq`）、状態はそれに
range・iterator・registered observer の所属・observer ごとの record queue・
pending・microtask を足したもの（`ObsEq`）である。

`parentOf` / `childrenOf` / `index` / `previousSibling` のような観測は
`get?` から素直に決まるが、`root` と `precedes` は `t.size` を fuel に使うので
そうはいかない。前者は `root_unique`、後者は
「tree order の前後は木の構造だけで決まる」（`precedesIn_preorder_iff_struct`）を
経由して、well-formed を仮定して示した。`WellFormed` 自体は `get?` だけで
書かれているので観測に沿って移る。

congruence の証明は二段である（`Dom/Spec/RemoveCongr.lean`）。

1. **transport**：`RemoveSpec` の各 component は観測の語彙だけで書かれているので、
   入力を観測の等しい状態に差し替えても成り立つ。
2. 差し替えてしまえば同じ入力から出た二つの結果になるので、
   `removeSpec_deterministic` がそのまま使える。

### transport できない書き方が一つ見つかった

`TreeRecordQueued` の `suppressObservers` が true の枝は
`s'.pendingObservers = s.pendingObservers` と **list の等式**で書いてあった。
pending observer の並びは観測に出ない（`removeSpec_deterministic` の結論も所属である）のに
関係の側だけが表現を縛っていたので、transport できない。所属の一致に弱めた。

関係を緩めても soundness は保たれ、一意性の結論も変わらない。
関係意味論の側に「観測に出ないものを縛らない」という制約が要る、という一例である。

### 連鎖のために、関係だけから well-formed を言う

`removeEach` のように繋ぐには、途中の木も well-formed である必要がある。
実行関数の不変量（`Dom/Validity/`）は関係の層からは使えないので、
`TreeRemoved` から直接示した（`treeRemoved_wellFormed`）。
`node` は parent を失うので、外した木の ancestor 鎖はそこで切れる。
つまり `Ancestor u a n → Ancestor t a n` で、acyclicity はそのまま移る。

### `adopt` は transport では済まない

`AdoptSpec` の step 2 は「parent が無ければ状態はそのまま」（`s₁ = s`）と書いてある。
これは **その derivation の入力そのもの**を指すので、観測の等しい別の状態に差し替えられない。
`adopt` の congruence は、二つの derivation を並べたまま段ごとに観測を持ち上げて示した
（`Dom/Spec/AdoptCongr.lean`）。

step 3 の node document 付け替え（`DocumentAssigned`）は parent も children も
触らないので、木の well-formed も保つ。ただし `ownerDocument_is_document` を保つには
`doc` が document である必要がある。それは `adopt` 自身ではなく §4.2.1 の pre-insert が
保証するので、仮定として持ち回っている。

### record を積む段に frame が無かった

`insert` の step 4.2 と step 9 は `TreeRecordQueued` だけで書いてあった。
この関係は observer の queue についてしか言わないので、
**木や live range がどうなるかを何も縛っていない**。つまり結果は一つに決まらない。

`remove` では同じ `(s, s')` の組に `TreeRemoved` などが並んでいたので気付かなかった。
record を積むだけの段には frame が要る。`ObserverOnly`（木・range・iterator・
registration が動かない）を足した。`replace data` の関係には最初から書いてあったので、
`insert` だけが抜けていたことになる。

### `insert` の一意性まで届いた

`insert` は step 4 で `remove` を、step 7.1 で `adopt` を呼ぶので、
congruence もその二つを composition する（`Dom/Spec/InsertCongr.lean`）。
段ごとに観測を持ち上げ、最後に `insertSpec_deterministic` になる。

途中で要ったのは、**関係だけから木の well-formed を言うこと**である。
`remove` は無条件だが、`insert` はそうはいかない。
`TreeInserted` が循環を作らないためには「入れる node が `parent` の
inclusive ancestor でない」が要る。これは §4.2.1 の pre-insertion validity が
保証するもので、`insert` 本体は前提として受け取る（仕様の構造がそうなっている）。

その条件は列の途中で壊れないことも要る。`adopt` は node を親から外し
ancestor を増やさないので、adopt を跨いでも残る。挿入が増やす辺は
「その node → `parent`」の一本だけなので（`ancestor_of_parentOf_insert`）、
残りの node についての同じ条件も残る。

### completeness を二つに分けた

soundness の逆は一つではない。

* **余計な model が無いこと** — 関係を満たす状態は、実行関数が作る状態と観測が等しい。
  これは soundness と一意性から出る。
* **実現できること** — 関係が満たせるなら、実行関数は失敗しない。
  これは契約（`Dom/Properties/Contract.lean`）から出る。

`remove` と `adopt` は両方示した（`Dom/Spec/Complete.lean`）。
`remove` は関係の step 1-2（parent が非 null）がそのまま契約の成功条件なので、
`remove_succeeds_iff` にそのまま渡せる。`adopt` は step 2 の `remove` を
parent がある node にしか呼ばないので、成功条件は step 1 だけである。

`insert` は前者だけである。`insertAt` の step 4（`child` が `parent` の子であること）を
関係が述べていないので、後者が言えない。仕様でもその検査は `insert` 本体ではなく
呼び出し側（pre-insert）にある。関係にその前提を足すか、
`preInsert` の側で言うかは別途決める。

これで roadmap の Phase 1 完了条件（関係が実行関数に依存しない・soundness・
一意性または completeness・`docs/traceability.md` の列）は `remove` と `insert` について揃った。

## `replace` の関係と、仕様の assertion が要求する不変量

`replace` は step 6 で `adopt`、step 7 で `remove`、step 9 で `insert` を呼ぶので、
関係もその三つを composition する（`Dom/Spec/Replace.lean`）。
step 1（ensure pre-insertion validity）は別の algorithm なので含めない。
`InsertSpec` が pre-insert を含まないのと同じ扱いである。

### 位置は木を変える前に決まる

step 2-3 の reference child と step 4 の previous sibling は、adopt も removal も走る前の
木で決まる。record に載るのはその値である。step 8 の `nodes` だけは removal の後に読むが、
`child` は `node` の子ではありえないので（step 1 の validity が「`node` は `parent` の
inclusive ancestor でない」を保証し、`child` の parent は `parent` である）、
どこで読んでも同じ列になる。実行関数は step 1 の直後に読んでいるので、
その一致は soundness の側で示した。

### `node` と `child` が同じことはありうる

最初「validity から `node ≠ child` が出る」と思って書いたが、証明が通らなかった。
`child` の parent が `parent` でも、それは `parent` が `child` の ancestor という話であって、
`node` が `parent` の ancestor という話ではない。子を自分自身で置き換える呼び出しは正当で、
仕様の step 3（reference child が `node` ならその次の兄弟にずらす）はそのためにある。

### 見つかったこと：DocumentFragment が子になる状態を invariant が禁じていない

step 10 の "queue a tree mutation record" は
「addedNodes と removedNodes のどちらかは空でない」を **assert** している。
これが破れるのは一通りだけである。`node` が `child` と同じ**空の DocumentFragment**のとき、
step 6 の adopt が `child` を親から外してしまうので removedNodes が空になり、
fragment の children も空なので addedNodes も空になる。

本物の DOM にこの状態は無い。`insert` は step 1 で fragment を children に展開するので、
fragment が誰かの子になることは無いからである。ところが model の
`StructurallyValid`（`Dom/Validity/Structural.lean`）はこれを言っていない。
`documentHasNoParent` はあるのに、その fragment 版が無い。

`StructurallyValid` に `fragmentHasNoParent` として足した（下記）。

### congruence は四つ目も同じ形で通った

`replace` の congruence（`Dom/Spec/ReplaceCongr.lean`）は
`adopt` → `remove` → `insert` → record と段ごとに観測を持ち上げるだけで済んだ。
`remove` / `adopt` / `insert` で作った道具がそのまま効いている。

step 1 の validity を関係に含めていないので、そこが保証する三つを仮定として受け取る。

* `node` は `parent` ではない
* `child` の parent は `parent` である
* 入れる node は `parent` の inclusive ancestor でない

`insert` の congruence が pre-insertion validity を仮定するのと同じ扱いである。
仮定は `s` について述べておいて、証明の中で `s₂`（adopt と removal の後）へ移す。
`adopt` も `remove` も ancestor を増やさないので、そのまま移せる。
`node` の kind と children も両方を跨いで残るので、step 8 の `nodes` も対応が付く。

## null 引数を比べられるようにした

差分テストは長らく「存在しない id を指す引数」を `unsupported` として飛ばしていた。
model が `notFoundError` を返すからだが、それは **model 側の都合**であって
仕様にある結果ではない。Dommy 側には「存在しない node」を渡しようが無いので、
比べる相手がいなかった。

代わりに **null** を渡せるようにした。WebIDL は method の step に入る前に引数を変換し、
`Range` の `Node` 引数はどれも non-nullable なので、null は
**手順が一つも走らないうちに** `TypeError` になる。これは仕様にある結果で、
Dommy にもそのまま渡せる。

`Operation` の `Range` の node 引数を `Option Nat` にして、`none` なら
`Dom.Exec.withNode` が step より先に `.typeError` を返す。
scenario の JSON では `"node": null` と書く。

### 順序が観測に出る

`setStart(null, 木より大きい offset)` は `IndexSizeError` ではなく `TypeError` になる。
変換が step 2 より先だからである。`insertNode(null)` も同じで、
step 6 の「start node が Text なら割る」より先に落ちるので木は変わらない。

固定 scenario を二本足した（`range-null-node-argument`,
`range-insert-node-null-leaves-text-alone`）。どちらも Dommy の
PR 42 前だと赤くなる——前者は `IndexSizeError`、後者は
**Text を "abcd" から "ab" に割ってから**例外を投げていた。PR 42 後は両方緑である。

生成器も `Range` の node 引数に 6% で null を混ぜ、offset にも 10% で
length を超える値を混ぜるようにした。seed 11 で 120 件回して、
不一致は finding 7 の一件だけだった。

pin は PR 42 の head（`e018027`）に上げた。

## ハーネスが偽の緑を出していた

Dommy 側から指摘を受けて直した。二つ重なると、**不一致があるのに「全部 ok」に見える**。

1. `difftest.rb` は `.lake/build/bin/dom-model` があれば、古いかどうかを確かめずに使う。
   古い binary は新しい操作を知らないので、その scenario の評価ごと失敗する。
2. `Compare.compare_dir` は `*.lean.json` のある scenario しか見ない。
   つまり **評価できなかった scenario は報告から静かに消える**。

実際に findings 8 の固定 scenario がまるごと消えたまま緑になっていた。

直し方は二つとも「消えないようにする」である。

* oracle は使う前に必ず `lake build dom-model` し直す（`DOM_MODEL` を明示したときは除く）。
* 突き合わせの基準を **scenario（`<base>.json`）の側**に移し、
  出力が無いものは ERROR にする。
* `--batch` の終了コードが 0 でなければ警告する。どの scenario かは ERROR の側に出る。

`lake build <Module>` は executable を作り直さないので、
proof を触った後に差分テストを回すとこれを踏みやすい。

## Dommy 側の修正が一巡した

`docs/status.md` の findings のうち、Range 周りは全部直った。

| finding | Dommy | 状態 |
| --- | --- | --- |
| 6（parent の無い node） | PR 41 `7eb57a8` | main |
| 7 / 8（`deleteContents` / `insertNode`） | PR 43 `d304172` | branch |
| `Node` 引数の WebIDL 変換 | PR 42 `e018027` | main |

pin は PR 43 の head に上げた。この状態で

* 固定 scenario の不一致は findings 9（`TreeWalker.parentNode`）と
  11（CharacterData target の event path）の二本だけ
* 生成 scenario は seed 3 で 120 件すべて一致（以前は `insertNode` が 2 件）、
  walker と listener を入れた seed 21 の 100 件でも finding 11 の一件だけ

になった。

## `move` の関係意味論

`move` は `remove` も `insert` も呼ばない。仕様が「pre-remove steps を走らせて
木から外し、offset を調整して入れる」と段を並べて書いているので、
関係もその段をそのまま並べた（`Dom/Spec/Move.lean`）。

`remove` との差は二つある。

* **transient registered observer を足さない**（`remove` の step 20 は `move` に無い）
* **record は最後に二つまとめて積む**（旧 parent に removal、新 parent に addition）

前者を言うために `ObserversUntouched`（`ObserverOnly` の裏）を足した。
registration まで含めて動かない、が `move` の外し方である。

### `detachWithLiveAdjust` は「observer を抑えた remove」の前半である

木から外す段の soundness は `remove` のものを借りた。`move` が呼ぶのは
`detachWithLiveAdjust` で、`remove` はその後ろに transient registered observer と
record を足しただけである。足す側は木も live range も NodeIterator も触らないので、
`suppressObservers` を立てた `remove` に読み替えれば
`remove_sound_range` / `_iterator` / `_tree` がそのまま効く。

### `match` は証明の中で書くと別物になる

step 17 の「挿入前の兄弟」は `move` の定義では

```lean
match child with
| some c => previousSibling s₁.tree c
| none => (childrenOf s₁.tree newParent).getLast?
```

と書いてある。同じ式を証明の中に書くと、周りの仮説を巻き込んだ**別の補助関数**に
なってしまい、定義の側の項と噛み合わない。`child` で場合分けして `match` を
潰してから進めた。`Option.elim` に書き換えるのも同じ理由で駄目である。

### congruence は道具が揃っていた

`move` の congruence（`Dom/Spec/MoveCongr.lean`）は、`remove` の三つの一意性と
`insert` の `rangeInsertAdjusted_congr` / `treeInserted_congr`、それに
`treeRecordQueued_congr` を繋ぐだけで済んだ。`insert` と違って `adopt` を
挟まないので、well-formed も document であることも要らない。

これで §4.2.3 と §4.2.4 の mutation は `remove` / `adopt` / `insert` / `replace` /
`move` の五つとも、関係・soundness・一意性が揃った。

## `StructurallyValid` に DocumentFragment の規則を足した

`documentHasNoParent` はあるのに fragment 版が無い、という穴を埋めた。

```lean
fragmentHasNoParent :
  ∀ n d, t.get? n = some d → d.kind = .documentFragment → d.parent = none
```

仕様は「fragment は tree の root である」と直接は書いていない。
そう保つのは §4.2.3 の `insert` で、step 1 が fragment を children に展開するので
fragment 自身が誰かの子になることは無い。
`replace` の step 10 の assertion がこれに依存していたので、
仮定（`FragmentsAreRoots`）に置いていたものを invariant に格上げした。

### 足すと preservation がどこで詰まるか

`insertAt` が「node は Document でない」を要求していたのと同じ場所に
「node は DocumentFragment でない」が要る。そこから上へ、
`insertEach` → `insertNodesAt` → `insert` の三段に仮説を通した。
`StructurallyValid` だけでなく `NodeDocumentsValid` と `IterCtx` の chain も
同じ `insertAt` を通るので、同じ三段が二度ずつ出てくる。

仮説を落とすのは `insert` の中である。fragment を展開する枝では
「fragment の children は fragment でない」（`child_not_fragment`、
新しい invariant からすぐ出る）、単独の node の枝では分岐の条件そのものである。

`move` は step 4 が Element と CharacterData しか動かさないので、そこで落ちる。
`replace` と `replaceAll` は `insert` を通るので何も要らない。

生成器は fragment を子にしないので（`CHILD_KINDS` に入っていない）、
差分テストへの影響は無かった。固定 scenario も生成 scenario も結果は変わらない。

## 差分テストの名前を実装から切り離した

jsdom や happy-dom のような別の実装も同じ scenario で測れるように、
harness の名前を汎用にした。

* `<base>.dommy.json` → `<base>.impl.json`
* `DOMMY_CMD` → `IMPL_CMD`（古い名前も読む）
* 表示に使う名前は `IMPL_NAME`（既定 `impl`）。判定には効かない

**oracle は Lean の model だけである。** 実装を並べても多数決はしない。
model が仕様の翻訳として正しいかは関係意味論と soundness、
`docs/traceability.md` の step 対応で担保するものであって、
実装の同意で決めるものではない。`docs/threats-to-validity.md` の §5 にそう書いた。

## JS の実装も同じ scenario で測れるようにした

`test/js_runner.mjs` を足した。jsdom と happy-dom を `--impl` で選ぶ。
名前でも module の path でも渡せるので、checkout した working tree をそのまま測れる。

比べられないものが二つある。

* **`notify`（MutationObserver の配送）。** 配送順は notify set の並びで決まるが、
  仕様には record queue を覗く口が無い（`takeRecords()` は空にしてしまう）。
  queue 自体は step ごとに `takeRecords()` で引き取って積み直しているので比べられる。
  配送だけが復元できない。
* **lone surrogate。** JS の String は持てるが、JSON にすると Ruby 側の parser が
  受け取れない。Ruby runner が UTF-8 の都合で断っているのと同じ場所である。

### jsdom の結果

checkout（30.0.1 + 数 commit）に対して固定 scenario 100 本が
**75 ok / 16 skip / 8 mismatch** だった。skip は `moveBefore` 未実装と
`notify` と lone surrogate である。

**候補として見つかったもの。**

* `Node.normalize()` が**受け手自身を含む**。`treeToArray(this)` を回しているので、
  Text node に対して呼ぶと自分と兄弟を畳んでしまう。仕様は
  「descendant exclusive Text node」なので Text への呼び出しは no-op である。
  固定 scenario は `normalize-on-text-is-noop`。
* **transient registered observer（§4.3.3 / remove step 20）が無い。**
  `lib/` に `transient` の語が一つも無い。外した部分木の中の変更が、
  配送まで observer に届かない。`observer-transient-follows-existing-registration`、
  `transient-observer-chains-through-removals`、`observer-delivery` の三本がこれである。

**既知の食い違いがそのまま出たもの。** normalize の record の形である。
仕様を字義どおり読むと characterData record は一つだが、browser engine は
兄弟ごとに積む（Dommy issue #24）。model は engine に合わせてあり、
jsdom は字義どおりなので、四本が mismatch になる。これは実装の誤りとは限らない。

**release と checkout で違ったもの。** npm の 30.0.1 では
`lookupNamespaceURI("xml")` が null を返し、insert step 5 の live range 調整が
step 7 の removal より後に走っていた。checkout では両方直っている
（`6d323653` ほか）。pin を切るなら release ではなく commit を指す必要がある。

### happy-dom の結果

checkout（`0d4cdbe7`）を compile して測った。固定 scenario 100 本が
**37 ok / 19 skip / 43 mismatch**。内訳は次のとおりである。

| 件数 | 中身 |
| --- | --- |
| 12 | §4.2.1 pre-insertion validity を通してしまう（`validity-step*`） |
| 6 | 例外が素の `Error` / 名前の無い `DOMException` |
| 1 | 失敗した操作が状態を変える（`range-insert-node-null-leaves-text-alone`） |
| 24 | 状態の差（live range の調整・normalize の record・observer・event） |

**確かめた候補。**

* **pre-insertion validity の Document 制約が無い。** doctype を Element の子にできる。
  Document に二つ目の document element を足せる。Text を Document の子にできる。
  仕様はどれも `HierarchyRequestError` である。
* **例外が `DOMException` ではない。** 素の `Error` を投げるので `name` が
  "HierarchyRequestError" にならない。差分テストは例外の名前で比べるので、
  そこで落ちる。
* **`createTextNode` / `createComment` / `createDocumentFragment` が node document を
  取り違える。** `implementation.createHTMLDocument()` で作った document に対して
  呼ぶと、node document が **window の document** になる。
  `createElement` / `createElementNS` / `createProcessingInstruction` は正しい。
  `NodeFactory.createNode` が「class の prototype に window symbol が無いときだけ」
  owner document を積む作りで、per-window の class にはそれが付いているため
  積まれず、constructor が window の document へ落ちる。
* **`DocumentType` に ChildNode mixin が無い。** `remove` / `before` / `after` /
  `replaceWith` を持たない。
* **`NodeIterator` が仕様の形をしていない。** `referenceNode` /
  `pointerBeforeReferenceNode` が無く、removal 後の調整（§6.1）も走らない。
  `TreeWalker` への委譲で作ってある。
* **`createProcessingInstruction` の target 検査が狭い。**
  `/^[a-z][a-z0-9-]+$/` は Name production より狭く、一文字・大文字・`_` `.` `:`・
  非 ASCII を弾く。
* **CharacterData の offset 検査が無い。** `substringData(9, 1)` は `""` を返し、
  `insertData(9, "x")` は末尾に足す。仕様はどちらも `IndexSizeError` である
  （§4.10 の各 method の step 1）。`deleteData` / `replaceData` も同じ。
* **live Range の調整が半分だけある。** 前の兄弟を外したときの offset の繰り下げ
  （§5.5 pre-remove steps 6-7）は動く。動かないのは二つで、
  **外す部分木の中を指していた端点を外へ出す**（同 steps 4-5）のと、
  **挿入したぶん offset を繰り上げる**（§4.2.3 insert step 5）である。

  ```text
  p の子が [a, b]、端点が (b, 0) のとき
    p.removeChild(b)          仕様 (p, 1)   happy-dom (b, 0)
  p の子が [a, q]、端点が (p, 2) のとき
    p.removeChild(a)          仕様 (p, 1)   happy-dom (p, 1)   ← 動く
    p.insertBefore(i, a)      仕様 (p, 3)   happy-dom (p, 2)
  ```

### 43 件は 43 個の誤りではない

固定 scenario の不一致 43 件は、たどると **八つほどの原因**に落ちる。

| おおよその件数 | 原因 |
| --- | --- |
| 12 | pre-insertion validity の Document 制約 |
| 6 | 例外が `DOMException` でない |
| 8 | live Range の調整（上の二つ） |
| 4 | CharacterData の offset 検査 |
| 4 | normalize の record の形（jsdom と同じ。model 側が疑わしい） |
| 3 | transient registered observer |
| 3 | event 周り |
| 3 | その他 |

この scenario 集合は**仕様の step の境目と過去の findings から組んである**ので、
普段使う経路より隅のほうに重みが寄っている。日常的な使い方の出来を測るものではない。

### runner 側で要った工夫

* document は **window の document を先に配る**。`createHTMLDocument` で作った
  document は上の node document の件で使えないので、scenario の大半（document 一つ）が
  測れるようにした。二つ目からは `createHTMLDocument` である。
* document を空にするのに `n.remove()` ではなく `removeChild` を使う。
  `DocumentType` に ChildNode mixin が無い実装で落ちるためである。

## 三実装を横に並べた

`test/compare_impls.rb` を足した。同じ scenario 集合（固定 99 本＋生成 80 本）を
Dommy・jsdom・happy-dom で評価して並べる。scenario は全実装で同じものを使う。
実装ごとの capabilities で生成を絞ると集合が変わって横に並べられないので、
ここでは絞らない。持っていない操作はその step で skip になる。

| | ok | skip | mismatch |
| --- | --- | --- | --- |
| Dommy（PR 43） | 170 | 7 | 2 |
| jsdom（checkout） | 148 | 23 | 8 |
| happy-dom（checkout） | 37 | 91 | 51 |

Dommy の 2 は findings 9（`TreeWalker.parentNode`）と 11（CharacterData target の
event path）である。happy-dom の skip が多いのは `lookupNamespaceURI` 系と
NodeIterator を持たないためで、生成 scenario がそこで止まる。

### 並べる意味は多数決ではない

**oracle は Lean の model だけである。** 実装の同意で仕様の読みを決めることはしない。
並べる意味は別のところにある。**二つ以上の実装が model と違う行**が見えることである。
そこは仕様の読み直しに値する場所で、`docs/threats-to-validity.md` §5 が言う
「仕様の読み違いがあれば、正しい実装を不一致として直してしまう」危険が
実際に出るとしたらそこである。

**差分テストで直した実装の一致は、独立した証拠にならない。** Dommy はこの
差分テストで 26 件直してあるので、model の写しになっている部分がある。

今回そう出たのは六つである。

* `normalize-descends-into-subtree` / `-empty-sibling-keeps-boundary` /
  `-merges-adjacent-text` — normalize が積む record の形。model は
  「engine は兄弟ごとに積む」（Dommy issue #24）として仕様の字義から離れており、
  jsdom と happy-dom は字義どおりである。**ここは browser か WPT で確かめる値打ちがある。**
  字義のほうが正しければ、model と Dommy の両方を直すことになる。
* `observer-delivery` / `observer-transient-follows-existing-registration` /
  `transient-observer-chains-through-removals` — transient registered observer
  （§4.3.3 / remove step 20）。jsdom も happy-dom も実装していない
  （どちらの source にも `transient` の語が無い）。仕様の step は明示的なので、
  ここは model が正しく、二つの実装が揃って持っていないだけだと読める。

後者が「二つ以上が違っても model が正しいことはある」という例になっている。
だから多数決にしない。

## browser を四列目に足した

`test/browser_runner.mjs` を足した。Playwright の Chromium
（Headless Shell 153.0.8010.12）を page として使い、`test/js/scenario.js` を
その中で走らせる。jsdom / happy-dom を動かす `js_runner.mjs` と**同じ本体**である。
DOM しか触らないので、素の script に切り出して両方から読めるようにした。

固定 scenario 99 本に対して **78 ok / 16 skip / 5 mismatch**。

### normalize の record の形は決着した

前に「二つ以上の実装が model と違う」として挙げた四本のうち、normalize の分は
**model が正しい**と分かった。`normalize-merges-adjacent-text` の step 0
（normalize そのもの）が Chromium と一致した。

`dommy-conformance` の記録（`e632f1a`）とも合う。そこには
**Chromium 141・WebKitGTK 2.52.6・Firefox がどれも run を兄弟ごとに畳む**
（append の characterData と removal の childList を一組ずつ積む）と書いてある。
字義どおりに読むと record は一つだが、engine はそう振る舞わない。
つまり jsdom と happy-dom の四本は、あちら側の食い違いである。

### 新しく開いた問いが一つある

**insert step 5 と step 7 の順序。** 同じ parent の中で node を動かし、
reference child が非 null のとき、model と Chromium が割れる。

```text
p の子が [c, n]、端点が n の中。p.insertBefore(n, c) で n を c の前へ動かす。
  model     (p, 1)   step 5（offset の繰り上げ）が step 7 の removal より先に走る。
                     端点はまだ n の中なので step 5 は当たらず、removal で (p,1) へ出る。
  Chromium  (p, 2)   removal が先に走ったかのように、(p,1) へ出たあと繰り上がる。
```

仕様の番号を素直に読むと step 5 が先である（`pre-insert` に removal は無く、
removal は insert step 7.1 の adopt の中にある）。model はそう読んでいる。

* jsdom の checkout は model と一致する。npm の 30.0.1 は Chromium と一致した。
* `dommy-conformance` の `cases/range/move-boundary.js` はこれを踏んでいない。
  あちらは **別の parent へ** append する形なので、`child` が null で step 5 が走らない。
  同じ parent の中を、reference child を指して動かす形が抜けている。

固定 scenario は `range-order-broken-by-insert`、`range-adjust-order-on-before`、
`range-adjust-order-on-move`、`range-delete-contents-across-nodes` の四本。

### WPT の期待値モデルが答えを持っていた

`dom/ranges/Range-mutations.js` は、期待値を**自分で計算して**比べる形になっている。
その計算がこうである。

```js
expectedStart = modifyForRemove(affectedNode, expectedStart);  // 外す側の調整が先
newParent.insertBefore(affectedNode, refNode);
expectedStart = modifyForInsert(affectedNode, expectedStart);  // 入れる側の調整が後
```

`modifyForRemove` は §5.5 の pre-remove steps そのもの（部分木の中の端点を
`(old parent, old index)` へ、old parent の offset を繰り下げ）である。
それを `insertBefore` の **前** に当て、入れる側の調整を **後** に当てている。
しかも入れる側は `indexOf(insertedNode)`、つまり**入れた後の new index** で判定する。
仕様の step 5 は `child` の index、それも入れる前の値である。

つまり **WPT は「外す調整 → 入れる調整」を期待値として持っている。**
Chromium はそのとおりに振る舞い、model は仕様の番号どおりに書いてあるので割れる。
`insertBeforeTests` の先頭の群（"Moving a node to its current position"）が
まさに同じ parent の中での移動で、reference child も非 null である。

### ところが WPT はその場所を試していない

期待値モデルが「外す調整 → 入れる調整」でも、**二つの順序が違う結果になる場合を
test case が持っていない**。二つが割れるのは、**同じ parent の中で node の index が
変わるとき**だけである。

`insertBeforeTests` の同じ parent の群は先頭の "Moving a node to its current
position"（`testDiv`, `paras[0]`, `paras[1]`）だけで、これは paras[0] を
paras[1] の前へ、つまり**もとの位置へ**動かす。old index も new index も 0 なので
入れる側の調整（`offset > new index`）が当たらず、どちらの順序でも同じ答えになる。
残りは別の parent へ動かす群で、そちらは外す側と入れる側で parent が違うから
やはり割れない。

こちらの `range-adjust-order-on-before` は old index 1 → new index 0 で、
そこがちょうど抜けている。

### jsdom を変えたのは DOM Standard の editor だった

`94301581 Align node insertion with the DOM Standard`（Domenic Denicola、2026-08-01）。
pre-insertion validity・insert・replace・replace all を現行の algorithm に揃える
commit で、live range の調整の位置もそこで仕様の番号どおりになった。
30.0.1 はその前の版である。

jsdom は `Range-mutations-insertBefore.html` を expected-failure にしていない。
上のとおり test が割れる場所を踏んでいないので、仕様どおりに直しても通る。

### 証拠の並び直し

| | 順序 | 重み |
| --- | --- | --- |
| 仕様の番号（pinned commit） | step 5 → step 7 | 曖昧さは無い |
| model・Dommy | 同上 | |
| jsdom checkout | 同上 | **editor 自身が仕様に揃えた** |
| WPT の期待値モデル | 外す → 入れる | **割れる場所を試していない** |
| Chromium | 外す → 入れる | test で固定されていない |
| jsdom 30.0.1 / happy-dom | 外す → 入れる | |

**model は孤立していない。** 仕様の字義と、いちばん最近いちばん意識して仕様を
読んだ実装（jsdom）と一致している。WPT の helper の書き方は engine 寄りだが、
そこを試す case が無いので固定されていない。

よってここは **model を変えない**。

### 記録する仕組みを入れた

`test/known-divergences.yml` と `test/known_divergences.rb` を足した。
`dommy-conformance` の `expectations/known-divergences.yml` と同じ考え方である。

**入れてよいのは「実装が仕様本文から離れていて、model が本文に従っている」場合だけ**
である。model のほうが怪しいなら記録ではなく調査が要る。
各 entry は記録したときの不一致の**形**を digest で固定するので、
黙って形が変わったら当たらなくなり、ふつうの不一致として出る。
消えた divergence も報告する（記録を外す合図である）。

Chromium の五つを記録した。insert の順序が三つ、あとの二つは調べる途中で出たものである。

* **§5.5 `deleteContents` の record の順序。** 仕様は step 6（start 側の replace
  data）→ step 7（nodes to remove を外す）→ step 8（end 側の replace data）で、
  characterData・childList・childList・characterData と積まれる。Chromium は
  characterData を二つ先に積む。木も live range も一致し、record の並びだけが違う。
* **`frag.replaceChildren(frag)` を Chromium が黙って通す。** 仕様の
  `replaceChildren` は step 2 で pre-insertion validity を走らせ、その step 2 が
  「node が parent の inclusive ancestor なら `HierarchyRequestError`」と言う。
  引数が一つの Node なら "convert nodes into a node" はそれをそのまま返すので、
  node と parent は同じ object である。Element なら Chromium も投げる
  （`div.replaceChildren(div)`）。`frag.appendChild(frag)` も投げる。
  **DocumentFragment を自分自身で置き換えたときだけ**素通りし、children も残る。

これで四実装の並びはこうなった（固定 99 本＋生成 40 本、Dommy は main `875d653`）。

| | ok | skip | known | mismatch |
| --- | --- | --- | --- | --- |
| **Dommy** | 136 | 3 | 0 | **0** |
| jsdom | 109 | 22 | 0 | 8 |
| happy-dom | 37 | 57 | 0 | 45 |
| **Chromium** | 112 | 22 | **5** | **0** |

Dommy と Chromium が赤ゼロで並んだ。Dommy はこの差分テストで直してきたので
model の写しになっている部分があり、その一致は独立した証拠にならない。
Chromium のほうは、離れている五箇所を記録した上でのゼロである。

### 残っていること

* **WPT に case を足す。** 同じ parent の中で index が変わる移動。
  これがあれば engine のどれが仕様どおりかが初めて固定される。
* 上の Chromium の二件は、報告する値打ちがある。

### 途中で harness も一つ直した

`Compare.diff_state` が live range と NodeIterator の差を表示していなかった。
「状態が一致しない」とだけ出て中身が分からず、record した divergence の digest も
値を固定できていなかった。どちらも出すようにした。

normalize とは形が違う。あちらは engine が揃っていて仕様の字義のほうが
書き足りなかった。こちらは仕様に曖昧さが無く、engine の側が試されていないだけである。

もう一つ、`replacechildren-bypasses-validity` で Chromium が通してしまう
（model は `HierarchyRequestError`）。これも未調査である。

## node を作れるようにした（roadmap Phase 6）

model はこれまで node を作らず、初期状態として与えられた木を動かすだけだった。
§4.5 の factory を六つ入れた。

`createElement` / `createElementNS` / `createTextNode` / `createComment` /
`createDocumentFragment` と、その土台の `requireDocument`。

### 新しい id は状態ではなく木から導く

roadmap は `DOMState` に allocator（`nextNodeId`）を足す案だったが、
**store にある id の最大より一つ大きいもの**を使う形にした。
こうすると「新しい」ことが `AdmissibleDOMState` の不変条件ではなく
store についての定理（`freshId_get?_eq_none`）になり、成分を増やさずに済む。

これが成り立つのは **model が store から node を消さない**からである。
`detach` は parent を切るだけで entry は残る。だから最大値は下がらず、
一度使った id が後でまた新しいものとして出てくることはない。

### 効果も妥当性も一つの形にまとめた

作る algorithm はどれも「detach された node を一つ足す」だけなので、
効果は `AddsNode`（作る前に無い・作った後にある・ほかは変わらない）、
data の条件は `FreshNodeData`（parent も children も attribute も無い・
Document でない・node document は Document）に集約した。

そこから roadmap §8.3 が求めるものが出る。

* freshness と new node exists — `AddsNode` の二つの field
* new node is detached — `parentOf_self` と `not_child`
* ownerDocument / kind / namespace / localName — 各 method の `*_creates`
* all existing nodes are unchanged — `others`

妥当性の保存（`admissible_createsNode`）は七成分ぜんぶを通した。
`documentTrees` だけは少し手が要る。`DocumentChildrenOk` は Document の children と
その kind から決まるので、**kind が全 node で一致する**という既存の congr 補題
（`documentChildrenOk_congr`）は使えない。作った node の kind は変わるからである。
children に限った版（`documentChildrenOk_congr_of_children`）を別に置いた。

### まだ無いもの

`createProcessingInstruction` と `createCDATASection`。前者の target は仕様が
Name production を参照しており、model はその production を持たない。

## clone を入れた（roadmap §8.4）

§4.4 の `cloneNode(deep)` と、その土台の "clone a single node"。
roadmap が求めた二つ、**identity は違う**と**観測できる形は同じ**を分けて証明した。

| roadmap §8.4 | theorem |
| --- | --- |
| clone ≠ original | `cloneNode_ne`（`cloneNode_fresh` 経由） |
| observable subtree contents are equivalent | `cloneNode_cloneOf` |

ほかに、妥当性の保存（`admissible_cloneNode`）、原本が動かないこと（`cloneNode_keep`）、
live range が動かないこと（`cloneNode_ranges`）。

### 仕様の手順をそのまま呼ぶ

"clone a node" の step 4 は「parent が null でなければ copy を parent に **append**
する」で、step 5 の children の clone はそのあとである。だから model も自前で木を
触らず、§4.2.3 の `append` を呼ぶ。妥当性の保存も live range の調整も mutation record も、
そちらで既に証明したものがそのまま効く。`admissible_cloneNode` は
`admissible_createsNode` と `admissible_append` の合成でしかない。

step 5 が children に渡す `document` は **copy ではなく引数の document のまま**である。
Document を clone したときに children の copy の node document が copy になるのは、
`append` の中の adopt が付け替えるからで、model もその経路を通る。
copy 自身の node document だけは "clone a single node" が決めるので、
Document の copy が自分自身を指すところは `cloneDocumentOf` が見る。

### `FreshNodeData` を広げた

§4.5 の factory が作るのは attribute を持たない非 Document の node だったので、
`FreshNodeData` は `d.attributes = []` と `d.kind ≠ .document` を要求していた。
clone は element の attribute をそのまま写し、Document の clone もある。

attribute の条件は `AttributesValid` の三条件（Element 以外は持たない・鍵が重複しない・
prefix があるなら namespace もある）に置き換えた。原本が満たしているので写しても満たす。
node document は「Document なら copy 自身・そうでなければ木にある Document」の
二択にした。前者があるので、この条件は作る id を見なければ書けない。

### 「同じ形」は bisimulation で述べる

`CloneOf t c n` は関係 `R` を一つ挙げる形で定義してある。`R` で結ばれた組は
一段ぶんの観測（`NodeData.shape` と `data` と children の個数）が一致し、
children どうしもまた `R` で結ばれている、と言えばよい。有限の木では最大不動点と
最小不動点は一致するので、これは「対応する位置の node の内容がすべて等しい」と同じである。

この形にしたのは証明の都合でもある。帰納法の途中で得た対応を後の状態へ持ち上げるとき、
inductive な定義だと derivation に現れる node すべてについて「その node は動いていない」
を言う必要がある。bisimulation なら `R` を自分で選べるので、
**pointwise な対応**（`CloneCorr`）を帰納法で作り、最後にそれを `R` として渡せばよい。

その `CloneCorr` は原本の側を **`t₀`**（`cloneNode` 入口の木）で見る。clone は木を
伸ばしていくので、途中の状態で原本を見ると外側の copy が children を足される分だけ
動いてしまう。`t₀` は動かないので、持ち上げに原本側の持ち上げが要らない。

### まだ無いもの

**`cloneNode` が失敗しないこと。** `append` は pre-insertion validity を毎回検査するので、
model の `cloneNode` は原理的には `HierarchyRequestError` を返しうる。妥当な木では
返らない（copy の children は原本の children を順に写したものなので、
Document の制約もそのまま満たす）が、その証明はまだ無い。

差分テストにも出していない。`docs/threats-to-validity.md` §3 の「node の生成」が
`createElement` などと同じくまだ比較対象の外にある。

`NodeIterator` が動かないことも述べていない。`insert` は iterator を触らないが、
その形の補題が無い。

### 次

`importNode` / `adoptNode`（roadmap §8.5）。

## 生成 scenario の最小化を広げた

不一致が出た生成 scenario を小さくする shrinker は前からあったが、落とせるのは
**操作と node だけ**だった。live object と文字列も落とすようにした（`test/difftest.rb`）。

順序は「操作 → 生きている object（range / iterator / walker / listener / observer）→
node → 文字列」で、一巡して何も落とせなくなるまで繰り返す。
候補はまとめて評価するので、1 round につき process 起動は 2 回のままである。

index で指す live object を落とすと参照がずれるので、操作側の index を付け替え、
落ちた番号を指す操作は捨てる。listener の `action` が持つ listener 番号も同じく直す。
listener の `callback` は宣言順の既定値なので、最小化の前に明示しておく
（そうしないと一つ落としただけで他の listener の番号が動く）。

効果は分かりやすい。findings 11 の例は
**node 6・listener 4・操作 8 から、node 3・listener 1・操作 1** になった。
range の例も 3 本あった range が 1 本に落ちる。

既にある scenario を最小化するには `--shrink FILE` を使う。

### 最小化が別の不一致へ逃げていた

nightly の counterexample を見直したところ、154 件のうち 3 件が
**最小化の副産物**だった。operations が空なのに「初期状態が一致しない」と出る。

原因は二つある。node を落とすと children の index が動くので、
range の両端の tree order が入れ替わる。文字列を縮めると offset が length を超える。
どちらも **Dommy では作れない初期状態**である（Dommy は `setStart` / `setEnd` を
通すので、逆順の端点はその場で畳まれる）。model は初期状態をそのまま組み立てるので、
そこで不一致が出る。最小化は「不一致が残るか」しか見ていないので、
元の不一致を離れてこちらへ滑り落ちていた。

候補を評価する前に「live object が指す node が残っているか」と
「range の両端が木の中にあり start ≤ end か」を検査するようにした
（`Difftest#sane_scenario?`）。落とせる候補が減るだけで、最小化の結果は変わらない。

### nightly が赤かった中身

`4b1fe81` で Range API の操作が生成器に入って以降、nightly の Differential は
毎晩赤である。中身を数えたところ、一晩 154 件の counterexample のうち

* 約 146 件が **finding 6**（parent の無い node の検査）
* 約 10 件が **findings 7 / 8**（`deleteContents` と `insertNode`）
* 3 件が上の最小化の副産物

で、新しい発見は無かった。finding 6 を Dommy 側で直したので、
同じ設定（nodes 8 / ops 6 / ranges 4、seed 3、100 件）の不一致は
**14 件から 2 件**になった。残る 2 件はどちらも finding 8 である。

nightly は既知の不一致でも赤のままにする方針である
（不一致を expected に落とすと、直ったことに気付けなくなる）。

## 未着手

* ProcessingInstruction の attribute map（§4.11 の `setAttribute` ほか）。
  element の attribute list とは別の仕組みで、attribute の mutation record を積まない。
  Dommy も未実装なので差分テストで裏を取れない。
* Shadow DOM。node tree に shadow tree / host / slot assignment が加わるので、
  model の骨格（`Tree` と `WellFormed`）から広げることになる。
  MutationObserver と違って既存の定理の多くに影響する。
* `Attr` を node として扱う API（`setAttributeNode`, `attributes` の `NamedNodeMap`、
  それに伴う "set an attribute" と "replace an attribute"、`InUseAttributeError`）。
  model の attribute は element の状態なので、node として観測できない。
  `InUseAttributeError` は attribute の object identity で決まるが、
  identity は roadmap §13.3 で対象外としている。
