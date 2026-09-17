// jsdom / happy-dom 用の scenario runner。
//
// lean4-dom の `lake exe dom-model` と同じ形式の JSON を書く。
// 比較は test/compare.rb が行う。
//
//   node test/js_runner.mjs --impl jsdom --capabilities
//   node test/js_runner.mjs --impl happy-dom --batch DIR
//   node test/js_runner.mjs --impl jsdom SCENARIO.json
//
// `--batch DIR` では `DIR/<base>.impl.json` に書く。
// scenario を評価する本体は `test/js/scenario.js` にある（browser でも同じものを使う）。
//
// **oracle は Lean の model だけである。** ここで動かす実装は準拠度を測られる側で、
// 食い違いは実装側の findings として扱う。

import { readFileSync, writeFileSync, readdirSync } from "node:fs";
import { join, basename, dirname } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
// 素の script なので、global scope で評価して `__domScenario` を生やす。
(0, eval)(readFileSync(join(here, "js/scenario.js"), "utf8"));
const { run, capabilities } = globalThis.__domScenario;

/* ------------------------------------------------------------------ 実装の入口 */

// `--impl` は名前（jsdom / happy-dom）でも module の path でもよい。
// path で渡せば、checkout した working tree をそのまま測れる。
// 名前で渡したときの実体は `JSDOM_MODULE` / `HAPPY_DOM_MODULE` で差し替える。
async function openImplementation(name) {
  const isPath = (s) => s.includes("/") || s.startsWith(".") || s.startsWith("file:");
  if (name === "jsdom" || (isPath(name) && /jsdom/.test(name))) {
    const spec = isPath(name) ? name : (process.env.JSDOM_MODULE ?? "jsdom");
    const { JSDOM } = await import(spec);
    return { name, window: new JSDOM("<!doctype html><html></html>").window };
  }
  if (name === "happy-dom" || isPath(name)) {
    const spec = isPath(name) ? name : (process.env.HAPPY_DOM_MODULE ?? "happy-dom");
    const { Window } = await import(spec);
    return { name, window: new Window() };
  }
  throw new Error(`未知の実装 ${name}`);
}

/* ------------------------------------------------------------------ CLI */

function isScenarioFile(path) {
  return path.endsWith(".json") && !path.endsWith(".lean.json") && !path.endsWith(".impl.json");
}

// scenario ごとに window を作り直す。
//
// 使い回すと、`makeDocumentFactory` が最初の document node に割り当てる
// `win.document` が全 scenario で同じ object になる。`makeDocumentFactory` は
// 子を外して空にするが、**event listener と MutationObserver の登録は外せない**。
// そのため前の scenario が document に付けた listener が次の scenario の
// dispatch に割り込む。`stopImmediatePropagation` する listener が残っていると
// 次の scenario の listener が一つも呼ばれず、**偽の不一致**になる。
//
// `browser_runner.mjs` は同じ理由で最初から scenario ごとに page を作っている。
async function runBatch(impl, dir) {
  let failed = 0;
  for (const name of readdirSync(dir).sort()) {
    const path = join(dir, name);
    if (!isScenarioFile(path)) continue;
    const base = basename(name, ".json");
    let out;
    try {
      const { window: fresh } = await openImplementation(impl);
      out = run(fresh, JSON.parse(readFileSync(path, "utf8")));
    } catch (e) {
      failed = 1;
      out = { error: `${e?.constructor?.name}: ${e?.message}` };
    }
    writeFileSync(join(dir, `${base}.impl.json`), JSON.stringify(out));
  }
  return failed;
}

const argv = process.argv.slice(2);
let impl = process.env.IMPL_MODULE ?? "jsdom";
const implIndex = argv.indexOf("--impl");
if (implIndex >= 0) {
  impl = argv[implIndex + 1];
  argv.splice(implIndex, 2);
}
if (argv[0] === "--capabilities") {
  const { window: win } = await openImplementation(impl);
  console.log(JSON.stringify(capabilities(win), null, 2));
  process.exit(0);
} else if (argv[0] === "--batch") {
  const dir = argv[1];
  if (!dir) {
    console.error("usage: js_runner.mjs [--impl NAME] --batch DIR");
    process.exit(2);
  }
  process.exit(await runBatch(impl, dir));
} else {
  const path = argv[0];
  if (!path) {
    console.error("usage: js_runner.mjs [--impl NAME] [--capabilities|--batch DIR] SCENARIO.json");
    process.exit(2);
  }
  try {
    const { window: win } = await openImplementation(impl);
    console.log(JSON.stringify(run(win, JSON.parse(readFileSync(path, "utf8")))));
  } catch (e) {
    console.error(`${path}: 初期状態を組み立てられない: ${e?.constructor?.name}: ${e?.message}`);
    process.exit(1);
  }
}
