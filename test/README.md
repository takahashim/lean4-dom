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
| `dommy_runner.rb` | Dommy（Ruby の API を直接呼ぶ） |
| `dommy_js_runner.rb` | Dommy（dommy-js-quickjs の QuickJS の中で `js/scenario.js` を走らせる。`IMPL_NAME=dommy-js`） |
| `js_runner.mjs` | jsdom / happy-dom（`--impl` で選ぶ） |
| `browser_runner.mjs` | Playwright の Chromium・Firefox・WebKit（`BROWSER` で選ぶ。既定は `chromium`） |

`dommy_runner.rb` は Dommy の Ruby の API を呼ぶので、Dommy が JS の層（`js/host_runtime.js`）で行う WebIDL の
変換（DOMString・boolean・可変長の引数の変換、引数の個数の検査）を通らず、それらの値を書いた step は比べない。
`dommy_js_runner.rb` はブラウザと同じ `js/scenario.js` を JavaScript の側から走らせるので、変換の層まで含めて
比べられる。Gemfile には dommy、makiri、dommy-js-quickjs、quickjs が要る。

```sh
export BUNDLE_GEMFILE=/path/to/Gemfile   # dommy・makiri・dommy-js-quickjs・quickjs
export IMPL_CMD="bundle exec ruby $PWD/test/dommy_js_runner.rb" IMPL_NAME=dommy-js
ruby test/difftest.rb --fixed-only
```

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

## call-site の固定

`ruby test/callsites.rb` は、**guard が仕様より厳しい primitive の呼び出し元**を
固定する。いまは `move` だけで、呼んでよいのは `moveBefore` である。

model の `insertAt` は「`child` は `parent` の子」を primitive の前提として検査する。
仕様はその検査を `pre-insert` の validity（step 3）に置いていて `move` の側には
置いていないので、`move` を `child = node` で呼ぶと結果が食い違う。その差が
観測できない根拠は「その呼び方をする経路が無い」ことだけなので、
散文ではなくここで固定する（Lean 側の対は `Dom.moveBefore_reference_ne`）。

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
global install から探す）。browser は環境変数 `BROWSER`（`chromium`・`firefox`・`webkit`）で選び、
`IMPL_NAME` も同じ名前にする（`known-divergences.yml` は `IMPL_NAME` で引く）。

```sh
BROWSER=firefox IMPL_NAME=firefox IMPL_CMD="node $PWD/test/browser_runner.mjs" \
  ruby test/difftest.rb --fixed-only
```

**browser は oracle ではない。** 並べる意味は、
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

### batch の途中で実装が落ちたとき

実装の process ごと落ちる（segfault する）と、それ以降の scenario の出力が
まるごと無くなる。`difftest.rb` は batch のあとで**足りない出力だけを一本ずつ
回し直す**ので、落ちた scenario だけが ERROR になる。
既知のものは `test/crashers/` にある。

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
| `url_diff.rb` / `url_js.mjs` | URL Standard の basic URL parser の差分（下の「URL parser」） |
| `urlencoded_diff.rb` | URL Standard §5.1 の urlencoded parser の差分（下の「urlencoded parser」） |

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
* 操作の引数の field には JSON の任意の値を書ける。WebIDL の変換（ToString、ToBoolean、ToNumber、
  dictionary・union・sequence、`Node` への変換）は model と実装の両方が行う。数は node の id、`{"attr": id}` は
  `Attr` で、それ以外の値は `Node` の引数では node でない値（TypeError）になる。field を書かなければ、その引数を
  既定値（文字列なら空文字列、`Node?` なら null）で渡したことにする。
* 操作に `"argc": k` を書くと、method に渡す引数を前から k 個に切り詰める。必須の引数より少なければ
  TypeError になる（`Dom/Exec/Invoke.lean` の `requiredArgs`。JS の runner は `ARGC_CALLS` で同じ呼び方をする）。
  Dommy は引数の個数の検査を JS の層で行うので、Dommy の runner は比べない。
* element の `namespace` / `prefix` / `localName` は、省略すると
  HTML namespace の `div` になる（Dommy の `createElement("div")` に合わせてある）。
  document の `isHTMLDocument` は省略すると true。
  attribute 名を ASCII lowercase するかどうかがこの二つで決まる。
* document の `mode` は `"no-quirks"`（省略時）・`"quirks"`・`"limited-quirks"`。
  runner は quirks と limited-quirks の document を HTML parser（Dommy は backend の parser、
  JS は `DOMParser`。WebKit の `DOMParser` は doctype が無くても no-quirks を返すので、そのときは
  iframe の document に `document.write` で読ませる）に doctype を読ませて作り、子を外してから使う。
  quirks mode では class selector・id selector・`getElementsByClassName()` の比較が
  ASCII case-insensitive になる。生成 scenario では `--quirks-prob F` で混ぜる（既定は 0）。
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
| `createAttribute` | `document`, `name` |
| `createAttributeNS` | `document`, `namespace`（null 可）, `name` |
| `getAttributeNode` | `element`, `name` |
| `getAttributeNodeNS` | `element`, `namespace`（null 可）, `name` |
| `setAttributeNode` / `removeAttributeNode` | `element`, `attr`（attribute の id） |
| `removeNamedItem` | `element`, `name` |
| `attrQuery` | `attr`, `query`（`ownerDocument`・`parentNode`・`parentElement`・`ownerElement`・`getRootNode`・`nodeName`・`nodeValue`・`textContent`・`isConnected`・`hasChildNodes`・`firstChild`） |
| `setAttrValue` | `attr`, `value`, `via`（`value`・`nodeValue`・`textContent` のどの setter を使うか） |

`Node` を受ける引数（`compareDocumentPosition`・`nodeContains`・`isEqualNode` の `node` と `other`、
`getRootNode`・`getTextContent`・`getNodeValue`・`lookupNamespaceURI`・`lookupPrefix`・`isDefaultNamespace`・
`cloneNode` の `node`、`importNode`・`adoptNode` の `node`、`appendChild` の `parent` と `node`）には、
node の id の代わりに `{"attr": id}` を書いて `Attr` を渡せる（`Dom/Attribute/AsNode.lean`）。
`Attr` を `adoptNode` して element から外れた（外す実装がある）`Attr` は、runner が `detachedAttrs` に入れる。

### 作った attribute の id

attribute にも同一性がある（仕様の `Attr` は node である）。model は `AttrId` で表し、
runner も同じ規則で振る（`refresh_attr_ids` / `refreshAttrIds`）。

* 初期状態は **node の id の昇順・node の中では list 順に 1 から**。
* 新しい attribute は **いま木にある id と detach された `Attr`（`detachedAttrs`）の id を合わせた最大より
  一つ大きいもの**（model の `freshStateAttrId`）。
* 木にも `detachedAttrs` にも無い attribute（`removeAttribute` で消したもの）の id は覚えない。
  model 側の最大も現在の状態だけで決まる。

`Attr` object の同一性で引くので、`setAttribute` が既にある attribute を書き換えたのか
作り直したのかが観測できる。clone した element の attribute は原本とは別のものなので、
id も違う。`cloneNode` と `importNode` に `Attr` を渡して作った `Attr` も同じ規則で振り、
`detachedAttrs` に入る。

### 作った node の id

model の `freshId` は **木にある id の最大より一つ大きいもの**で、deep な clone は
tree order（preorder）でそれを順に使う。runner も同じ規則で振る
（`register_subtree` / `registerSubtree`）。これで、生成した node も id で比べられる。

`adoptNode` は node を作らないので、返るのは渡した id のままである。
実装が別の wrapper を返していれば id が引けず `"?"` になって不一致に出る。

`Attr` を指す引数は attribute の id である。`createAttribute` が作った `Attr` や
`removeAttributeNode` が外した `Attr` は、どの element にも付いていない状態で
出力の `detachedAttrs` に並ぶ。**名前で消した attribute（`removeAttribute`）は
そこに入らない** — 仕様では element を null にするだけで object は残るが、
それを指す参照がどこにも無いので観測できないからである。

生成器（`generate.rb`）は **必ず成功する形だけ**を作る。失敗すると作った node の
id の予測が実際とずれ、以降の操作が別の node を指してしまうからである。
名前の検査に落ちる形（`createElement("")` など）と、`deep` な clone / import の
あとの生成は出さない。

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

## URL parser

`test/url_diff.rb` は、`URL(input, base)` を model と実装で突き合わせる。比べるのは失敗するかどうかと、
成功したときの IDL attribute（`href` から `hash` まで）と origin である。

* model：`url-model --parse-batch FILE test/url/uts46-table.json`（`parseUrl`）。
* Dommy：`Dommy::URL.parse(input, base)`。
* JS：`test/url_js.mjs` を通す。`--js node`（Node の組み込みの URL、Ada）、
  `--js whatwg-url=PATH`（URL Standard の参照実装）、`--js jsdom=PATH`（jsdom の `window.URL`）、
  `--js chromium` `--js firefox` `--js webkit`（Playwright の browser。`PLAYWRIGHT_PATH` は `browser_runner.mjs` と同じ）。
* `--dump FILE` で case と全実装の結果を JSON に書き出す。割れ方の分類に使う。
* `file:`（と中身が `file:` の `blob:`）の origin は実装依存なので比べない。

入力は WPT の表（`test/url/wpt-ascii.json`）の 820 件、その変形（区切りや空白を一つ二つ足す・消す・置き換える）、
部品（scheme、`/` と `\` の並び、userinfo、IPv4・IPv6・domain・opaque host、port、`.` と `..` と drive letter を
含む path、query、fragment）から組み立てた URL で、base は無いか、special・非 special・`file:`・opaque path のどれか。
非 ASCII の domain を含むので、model には UTS #46 の表を渡す。

```sh
lake build url-model
npm install --prefix /tmp/wu whatwg-url@17.1.2
BUNDLE_GEMFILE=/path/to/Gemfile bundle exec ruby test/url_diff.rb --count 10000 --seed 1 \
  --js whatwg-url=/tmp/wu/node_modules/whatwg-url/index.js --js node
```

割れた case は全実装の結果を並べて出す。一致は多数決ではなく、どちらが仕様どおりかは本文で決める。
CI の `deterministic` job は Dommy と whatwg-url で seed 1 の 3,000 件を流す。browser と Node は既知の不一致が
多いので CI には入れていない（`docs/url-status.md` の「実装との突き合わせ」）。

`--setters` を付けると §6.1 の setter を突き合わせる。parse した URL の IDL attribute（`protocol` から `hash`
まで）に値を代入してから、同じ IDL attribute と origin を比べる。入力は WPT の `setters_tests.json`
（`test/url/wpt-setters.json`）の 257 件（`href` の setter は parse そのものなので外す）と、乱数の URL に
setter ごとの値（区切り文字、percent、port の境界、`file:`、IPv6、IDNA など）とその変形を当てたものである。
model は `--parse-batch` の case に `"setter"` と `"value"` を足したもの、JS は代入、Dommy は `#{setter}=` を使う。
CI では parser と同じく Dommy と whatwg-url で seed 1 の 3,000 件を流す。

```sh
BUNDLE_GEMFILE=/path/to/Gemfile bundle exec ruby test/url_diff.rb --setters --count 8000 --seed 1 \
  --js whatwg-url=/tmp/wu/node_modules/whatwg-url/index.js --js node
```

## urlencoded parser

`test/urlencoded_diff.rb` は、URL Standard §5.1 の application/x-www-form-urlencoded parser を
model と Dommy で突き合わせる。scenario の形式は使わず、文字列の列をまとめて両方に通す。

* model：`url-model --urlencoded-batch FILE`（`parseUrlencodedString`）。関係仕様との一致は
  `Url/Spec/Urlencoded.lean` の `parseUrlencoded_iff` が証明している。
* Dommy：`Dommy::URLSearchParams` の文字列の parse。公開の constructor は先頭の `?` を一つ落とすが、
  それは `URLSearchParams` の constructor の手順なので、owner 付きで作って §5.1 だけを比べる。

入力は固定の 45 件（区切り、`+`、percent-decode、不正な UTF-8 の列、BOM）と、乱数で作った列である。

```sh
lake build url-model
BUNDLE_GEMFILE=/path/to/Gemfile bundle exec ruby test/urlencoded_diff.rb --count 20000 --seed 1
```

CI の `deterministic` job は seed 1 で 5,000 件を流す。

## 名前空間の囮の sweep

`test/js/decoy.js` は model を oracle にしない検査である。fixture（`test/decoy/fixture.html`）の element に
namespace 付きの囮の attribute を置き（あるいは SVG・MathML・null namespace の element を足し）、その前後で
読める値を全部読んで、変わったものを記録する。「変わってよいか」は三つの browser が揃っているかで決め、
DOM の範囲は `Dom/Properties/NullNamespace.lean` の定理で裏を取る（`docs/status.md` の「名前空間の取り違え」）。

```sh
export PLAYWRIGHT_PATH=/path/to/node_modules/playwright
node test/decoy_sweep.mjs --enumerate test/decoy/names.json    # getter の名前（commit 済み）
for b in chromium firefox webkit; do BROWSER=$b node test/decoy_sweep.mjs test/decoy/names.json OUT/out-$b.json; done
L=$PWD; O=$PWD/OUT
(cd /path/to/dommy-js-quickjs && bundle exec ruby $L/test/decoy_dommy.rb $L/test/decoy/names.json $O/out-dommy.json)
(cd /path/to/dommy-js-quickjs && bundle exec ruby $L/test/decoy_dommy.rb $L/test/decoy/names.json $O/out-dommy-ruby.json --ruby-path)
ruby test/decoy_compare.rb OUT
```

三つ目の引数（`attr:` / `elem:` / `write:` / `frag:` など）を渡すと、その接頭辞の case だけを走らせる。
`--ruby-path` は Dommy の JS 側の attribute snapshot を外して、reflect を必ず Ruby の getter に通す。
