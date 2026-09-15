# differential testing

`PLAN.md` §7。同じ scenario を Lean の model と検査対象の DOM 実装の両方で評価し、
各 step の観測可能な状態を突き合わせる。

**oracle は Lean の model だけである。** 実装側は準拠度を測られる相手であって、
食い違いは実装の findings として扱う（多数決はしない)。

```text
             scenario (JSON)
                   │
        ┌──────────┴──────────┐
        ▼                     ▼
  dom-model --batch      実装の runner --batch
        │                     │
   *.lean.json            *.impl.json
        └──────────┬──────────┘
                   ▼
              compare.rb
```

実装は runner を差し替えて選ぶ。`IMPL_CMD` がその command、
`IMPL_NAME` が表示に使う名前である（判定には効かない)。

| runner | 対象 |
| --- | --- |
| `dommy_runner.rb` | Dommy（Ruby） |
| `js_runner.mjs` | jsdom / happy-dom（`--impl` で選ぶ） |
| `browser_runner.mjs` | Playwright の Chromium |

`js_runner.mjs` の `--impl` は名前でも module の path でもよい。
path を渡せば checkout した working tree をそのまま測れる。

```sh
export IMPL_CMD="node $PWD/test/js_runner.mjs --impl /path/to/jsdom/lib/api.js"
export IMPL_NAME=jsdom
```

複数の実装を横に並べるには `compare_impls.rb` を使う。

```sh
ruby test/compare_impls.rb --count 80 --seed 7 \
  --impl "dommy=bundle exec ruby $PWD/test/dommy_runner.rb" \
  --impl "jsdom=node $PWD/test/js_runner.mjs --impl /path/to/jsdom/lib/api.js"
```

scenario は全実装で同じものを使う（実装ごとの capabilities で絞ると集合が
変わって横に並べられない）。**多数決はしない。** 並べる意味は
「二つ以上の実装が model と違う行」が見えることで、そこは仕様の読み直しに
値する場所だという印である。差分テストで直した実装は model の写しに
なっているので、その一致を独立した証拠として数えてはいけない。

## 記録済みの divergence

実装が仕様本文から離れていて、こちらの findings ではないものは
`test/known-divergences.yml` に書く。当たった不一致は `known` として報告し、
失敗に数えない。

**入れてよいのは「実装が仕様本文から離れていて、model が本文に従っている」場合だけ**
である。model のほうが怪しいなら、記録ではなく調査が要る
（`docs/threats-to-validity.md` §5）。

各 entry は記録したときの不一致の**形**を digest で固定する。黙って形が変わったら
当たらなくなり、ふつうの不一致として出る。消えた divergence も報告する。

browser を動かすには Playwright が要る（`PLAYWRIGHT_PATH` か node_modules か
global install から探す）。**browser は oracle ではない。** 並べる意味は、
実装が揃って model と違うときに「実装側の穴」と「model の読み違い」を
分けられることにある。

scenario を評価する本体は `test/js/scenario.js` にあり、Node からも page の中からも
同じものを走らせる。DOM しか触らないので import も export も持たない素の script で、
読み込むと `globalThis.__domScenario` が生える。

JS 側で比べられないものが二つある。**`notify`（MutationObserver の配送）**は
配送順が notify set の並びで決まり、仕様には queue を覗く口が無いので復元できない
（record queue 自体は `takeRecords()` で引き取って積み直しているので比べられる）。
**lone surrogate** を含む文字列は JSON で Ruby 側へ渡せないので、その step で止める。

## 実行

```sh
# Lean 側を build しておく
lake build

# Dommy を bundle で解決できる状態にしておく（makiri が要る）
export BUNDLE_GEMFILE=/path/to/Gemfile
export IMPL_CMD="bundle exec ruby $PWD/test/dommy_runner.rb"
export IMPL_NAME=dommy

# makiri は RubyGems の公開版を使う。
# ローカル checkout から build したものだと
# `Makiri::Document#create_document_type` を持たないことがあり、
# その場合 Dommy が node-backed でない DocumentType にフォールバックして
# doctype がそもそも木に入らなくなる（症状が変わるので比較結果を誤読しやすい）。

# 固定 scenario だけ
ruby test/difftest.rb --fixed-only

# 固定 scenario ＋ 乱数生成 100 本
ruby test/difftest.rb --count 100 --seed 1

# live object と observer を混ぜる（生成 scenario の規模は既定より大きくなる）
ruby test/difftest.rb --count 200 --seed 1 --ranges 4 --iterators 2 --observers 3 --move
```

生成側の option：

| option | 意味 |
| --- | --- |
| `--count N` / `--seed N` | 生成する本数と乱数の種 |
| `--nodes N` / `--ops N` | 一本あたりの node 数と操作数 |
| `--ranges N` / `--iterators N` / `--observers N` | 初期状態に置く live Range / NodeIterator / MutationObserver の数 |
| `--move` | `moveBefore` を生成する |
| `--doctype-prob F` | document に doctype を置く確率 |
| `--all-ops` | Dommy の実装状況で操作を絞らない |
| `--fixed-only` | 生成をせず固定 scenario だけ走らせる |

`--observers N` を指定したときだけ、`observe` / `disconnect` / `takeRecords` /
`notify`（microtask checkpoint）も生成される。

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
  "observers": [],
  "operations": [
    {"op": "insertBefore", "parent": 1, "node": 3, "child": null},
    {"op": "removeChild", "parent": 1, "node": 2}
  ]
}
```

* `nodes` の並び順が children の順序を決める。
* `ownerDocument` は省略できる（`document` は自分自身、それ以外は最初の document node）。
* `data` は CharacterData 以外では無視する。offset と長さは仕様どおり
  UTF-16 の code unit で数える。surrogate pair を割る切り出しだけは
  model の対象外で、`{"ok": false, "exception": "__outsideModel__"}` になる。
  比較器はその step 以降を比べない（実装が同じところで失敗しても一致とは数えない）。
* `ranges` は `{"start": {"node": 1, "offset": 0}, "end": {"node": 1, "offset": 2}}` の形。
  Lean 側は読み込み時に両端の validity（node が木にあり offset が length 以下）を検査する。
* `iterators` は `{"root": 1, "reference": 1, "pointerBeforeReference": true,
  "whatToShow": 4294967295}` の形。
  仕様の `createNodeIterator` は reference を (root, true) に初期化する。
  `whatToShow` は node type − 1 の bit を見る bitmask で、省略すると `SHOW_ALL`。
  `filter` は callback なので常に null として扱う。
* `observers` は `observe(target, options)` を一度呼んだ状態を作る。
  `{"target": 1, "subtree": true, "childList": true, "attributes": true,
  "attributeOldValue": true, "attributeFilter": ["a"], "characterData": true,
  "characterDataOldValue": true}` の形で、`target` を省くと registration を持たない
  observer だけができる（scenario 側で `observe` 操作を使う場合はこちら）。
* element の `namespace` / `prefix` / `localName` は、省略すると
  HTML namespace の `div` になる（Dommy の `createElement("div")` に合わせてある）。
  document の `isHTMLDocument` は省略すると true。
  attribute 名を ASCII lowercase するかどうかがこの二つで決まる。
* element の `attributes` は
  `{"namespace": null, "prefix": null, "localName": "a", "value": "1"}` の list。
  Element 以外に置いても無視される。
  prefix を付けるなら namespace も要る（`AttributesValid`）。
* `_` で始まる key（`_note`、`_basis` など）は無視されるので、注記を書いてよい。
  固定 scenario には期待結果の根拠を `_basis` に書く（`docs/traceability.md`）。

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
| `replaceData` | `node`, `offset`, `count`, `data` |
| `appendData` | `node`, `data` |
| `insertData` | `node`, `offset`, `data` |
| `deleteData` | `node`, `offset`, `count` |
| `setData` | `node`, `data` |
| `setAttribute` | `element`, `name`, `value` |
| `setAttributeNS` | `element`, `namespace`（null 可）, `name`, `value` |
| `removeAttribute` | `element`, `name` |
| `removeAttributeNS` | `element`, `namespace`（null 可）, `name` |
| `toggleAttribute` | `element`, `name`, `force`（null 可） |
| `iteratorNext` / `iteratorPrevious` | `iterator`（`iterators` の index） |
| `observe` | `observer`（`observers` の index）, `target`, および `MutationObserverInit` の各 key |
| `disconnect` / `takeRecords` | `observer` |
| `notify` | 無し（microtask checkpoint。"notify mutation observers" を走らせる） |
| `createElement` | `document`, `localName` |
| `createElementNS` | `document`, `namespace`（null 可）, `name` |
| `createTextNode` / `createComment` | `document`, `data` |
| `createDocumentFragment` | `document` |
| `cloneNode` | `node`, `deep` |
| `importNode` | `document`, `node`, `deep` |
| `adoptNode` | `document`, `node` |

### 作った node の id

model の `freshId` は **木にある id の最大より一つ大きいもの**で、deep な clone は
tree order（preorder）でそれを順に使う。runner も同じ規則で振る
（`register_subtree` / `registerSubtree`）。これで、生成した node も id で比べられる。

`adoptNode` は node を作らないので、返るのは渡した id のままである。
実装が別の wrapper を返していれば id が引けず `"?"` になって不一致に出る。

`observe` の options は、省略と `false` を区別する。
`attributes` と `characterData` は IDL に既定値が無く、`observe` の step 1-2 が
「存在しないなら true にする」ので、書かないことに意味がある。
`attributeFilter` も存在の有無が条件になる。

仕様の `before()` / `after()` / `replaceWith()` / `replaceChildren()` は
可変長引数を "converting nodes into a node" で一つの node にまとめるが、
その変換は呼び出し側で済ませた形（まとめた結果の node）を引数に取る。

document は必ず HTML document になる（runner は `Window` の document と
`createHTMLDocument` しか使えない）。`isHTMLDocument: false` を指定した scenario は
Dommy 側の runner が断る。黙って HTML document を返すと、`createElement` の
step 2（ASCII lowercase）と step 4（HTML namespace）が偽の不一致になるからである。

初期状態は `WellFormed` を満たす必要があり、Lean 側は読み込み時に
`checkWellFormed` で拒否する。加えて DOM の node tree 制約も満たす必要がある
（Dommy 側は `appendChild` で木を組み立てるため）。

## 出力の形式

```json
{
  "initial": {"nodes": [...], "ranges": [], "iterators": [], "observers": []},
  "steps": [
    {"ok": true, "nodes": [...], "ranges": [], "iterators": [],
     "observers": [[]], "delivered": [], "returned": {"kind": "undefined"}},
    {"ok": false, "exception": "NotFoundError"}
  ]
}
```

例外が起きた step で評価を打ち切る。

`observers` は observer ごとの record queue（`takeRecords()` が返すもの）、
`delivered` は microtask checkpoint で callback に配送された record を
**呼ばれた順に** 並べたものである（`notify` 以外の step では空）。

`returned` は操作の戻り値で、`kind` は `undefined` / `node` / `boolean` / `records` の
いずれか。`null` を返すことと `undefined` を返すことを取り違えないよう kind を添える。
失敗した step には戻り値が無いので field ごと出さない。

Lean 側は各 step の後で `AdmissibleDOMState` の七成分を実行時に検査し、
破れていれば `"invariantViolation": {"step": N, "invariant": NAME}` を足す。
`NAME` は `wellFormed` / `structurallyValid` / `nodeDocumentsValid` /
`documentTreesValid` / `rangeEndpointsValid` / `iteratorsValid` /
`observerRegistrationsValid` / `attributesValid` のいずれかである。
初期状態が admissible なら発火しないことは
`Dom.Exec.runOperations_no_violation` で証明してあるので、
発火したら harness 側を疑う。

Dommy が実装していない操作は `{"ok": false, "exception": "__unsupported__"}` として報告し、
仕様上の例外との不一致と区別する。

比較するのは、node の `kind` / `parent` / `children` / `nodeDocument` / `data` /
`attributes`、そこから導いた tree order、live Range の両端、NodeIterator の
root と reference と pointer-before-reference flag と whatToShow、
observer ごとの record queue、配送された record、操作の戻り値、および例外の名前である。
tree order は children から導けるので出力には含めず、比較側で導出する。
比較しないものは `Dom/Observation.lean` の doc comment に列挙してある。

## 固定する version

再現のために固定する version は `test/pinned-versions.json` にある。
dom.bs の commit、Dommy の commit、makiri の version、Ruby と Lean の toolchain である。
上げるときは固定 scenario と生成 scenario を両方通してからにする。

## CI

差分テストは `.github/workflows/differential.yml` にある。
Dommy の checkout と native gem の build が要るので、`lake build` の CI とは分けてあり、
既定では走らない。

* `deterministic` — 手動起動。固定 scenario 全件と、固定 seed の生成 scenario 100 本。
* `exploration` — nightly。node 数・操作数・Range 数・Iterator 数・observer 数を
  三通りに変え、seed 10 個 × 各 100 本。

不一致が出ると最小化した scenario が `test/scenarios/failing-*.json` に書かれ、
artifact として上がる。内容を確認したうえで固定 scenario に昇格させる。
