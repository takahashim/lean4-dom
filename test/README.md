# differential testing

`PLAN.md` §7。同じ scenario を Lean の model と Dommy の両方で評価し、
各 step の観測可能な状態を突き合わせる。

```text
             scenario (JSON)
                   │
        ┌──────────┴──────────┐
        ▼                     ▼
  dom-model --batch    dommy_runner.rb --batch
        │                     │
   *.lean.json           *.dommy.json
        └──────────┬──────────┘
                   ▼
              compare.rb
```

## 実行

```sh
# Lean 側を build しておく
lake build

# Dommy を bundle で解決できる状態にしておく（makiri が要る）
export BUNDLE_GEMFILE=/path/to/Gemfile
export DOMMY_CMD="bundle exec ruby $PWD/test/dommy_runner.rb"

# 固定 scenario だけ
ruby test/difftest.rb --fixed-only

# 固定 scenario ＋ 乱数生成 100 本
ruby test/difftest.rb --count 100 --seed 1
```

`makiri` を AddressSanitizer 付きで build している場合は、
Dommy 側の command にだけ preload を指定する。

```sh
export DOMMY_CMD="env LD_PRELOAD=/usr/lib/x86_64-linux-gnu/libasan.so.8 \
                  ASAN_OPTIONS=detect_leaks=0 bundle exec ruby $PWD/test/dommy_runner.rb"
```

`difftest.rb` 自身は Dommy を読み込まない。
ASan 付きの process から fork できないため、Lean の oracle の起動は
Dommy を読み込んでいない process の仕事にしてある。

## file

| file | 役割 |
| --- | --- |
| `difftest.rb` | driver。生成・評価・比較・最小化を行う |
| `dommy_runner.rb` | Dommy 側の評価。`--capabilities` で実装状況を出す |
| `compare.rb` | 出力の比較。`compare.rb DIR` 単体でも使える |
| `generate.rb` | scenario の乱数生成 |
| `scenarios/*.json` | 固定 scenario（回帰用） |

## scenario の形式

```json
{
  "nodes": [
    {"id": 0, "kind": "document"},
    {"id": 1, "kind": "element", "parent": 0},
    {"id": 2, "kind": "text", "parent": 1, "data": "abc"},
    {"id": 3, "kind": "element"}
  ],
  "ranges": [],
  "iterators": [],
  "operations": [
    {"op": "insertBefore", "parent": 1, "node": 3, "child": null},
    {"op": "removeChild", "parent": 1, "node": 2}
  ]
}
```

* `nodes` の並び順が children の順序を決める。
* `ownerDocument` は省略できる（`document` は自分自身、それ以外は最初の document node）。
* `data` は CharacterData 以外では無視する。
* `ranges` と `iterators` は Phase 5 以降で使う。形式だけ予約してある。
* `_` で始まる key（`_note` など）は無視されるので、注記を書いてよい。

`kind` は `document` / `documentType` / `documentFragment` / `element` /
`text` / `cdataSection` / `processingInstruction` / `comment`。

`op` と引数：

| op | 引数 |
| --- | --- |
| `appendChild` | `parent`, `node` |
| `insertBefore` | `parent`, `node`, `child`（null 可） |
| `replaceChild` | `parent`, `node`, `child` |
| `removeChild` | `parent`, `node` |
| `replaceChildren` | `parent`, `node`（null 可） |
| `before` / `after` / `replaceWith` | `target`, `node` |
| `remove` | `target` |
| `moveBefore` | `parent`, `node`, `child`（null 可） |

仕様の `before()` / `after()` / `replaceWith()` / `replaceChildren()` は
可変長引数を "converting nodes into a node" で一つの node にまとめるが、
本 model は node を生成しないので、まとめた結果の node を引数に取る。

初期状態は `WellFormed` を満たす必要があり、Lean 側は読み込み時に
`checkWellFormed` で拒否する。加えて DOM の node tree 制約も満たす必要がある
（Dommy 側は `appendChild` で木を組み立てるため）。

## 出力の形式

```json
{
  "initial": {"nodes": [...], "ranges": [], "iterators": []},
  "steps": [
    {"ok": true, "nodes": [...], "ranges": [], "iterators": []},
    {"ok": false, "exception": "NotFoundError"}
  ]
}
```

例外が起きた step で評価を打ち切る。
Lean 側は各 step の後で `checkWellFormed` を実行し、
破れていれば `"invariantViolation": <step 番号>` を足す。

Dommy が実装していない操作は `{"ok": false, "exception": "__unsupported__"}` として報告し、
仕様上の例外との不一致と区別する。

比較は node の `parent` と `children`、そこから導いた tree order、
`kind`、`data`、および例外の名前について行う。
tree order は children から導けるので出力には含めず、比較側で導出する。
