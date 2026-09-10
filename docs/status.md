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

## 未着手

Phase 2 以降（`Dom/Mutation/`, `Dom/Range/`, `Dom/Traversal/`, `Dom/CharacterData/`, `Dom/Exec/`）は
directory を用意しただけで、まだ空である。

`PLAN.md` §14 の最後にあるとおり、Phase 2 に入る前に PLAN §5 以降を
実際の定義（特に `NodeStore` の interface と `WellFormed` の形）に合わせて見直す必要がある。
