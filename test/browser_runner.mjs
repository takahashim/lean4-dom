// browser（Playwright の Chromium）用の scenario runner。
//
// lean4-dom の `lake exe dom-model` と同じ形式の JSON を書く。
// 比較は test/compare.rb が行う。
//
//   node test/browser_runner.mjs --capabilities
//   node test/browser_runner.mjs --batch DIR
//   node test/browser_runner.mjs SCENARIO.json
//
// scenario を評価する本体は `test/js/scenario.js` にある。jsdom / happy-dom を
// 動かす `js_runner.mjs` と同じものを、page の中で走らせる。
//
// **browser は oracle ではない。** oracle は Lean の model だけである。
// browser を並べる意味は、仕様の読み直しに値する場所を見つけることにある
// （`docs/threats-to-validity.md` §5）。実装が揃って model と違うとき、
// それが実装側の穴なのか model の読み違いなのかを分けるのに効く。
//
// Playwright は `PLAYWRIGHT_PATH`、local な node_modules、global install の
// 順に探す。browser は Playwright の既定の場所から取る。

import { readFileSync, writeFileSync, readdirSync } from "node:fs";
import { join, basename, dirname } from "node:path";
import { fileURLToPath } from "node:url";
import { createRequire } from "node:module";

const here = dirname(fileURLToPath(import.meta.url));
const scenarioSource = readFileSync(join(here, "js/scenario.js"), "utf8");
const require = createRequire(import.meta.url);

function loadPlaywright() {
  const candidates = [
    process.env.PLAYWRIGHT_PATH,
    "playwright",
    "/usr/lib/node_modules/playwright",
    "/usr/local/lib/node_modules/playwright"
  ].filter(Boolean);
  for (const candidate of candidates) {
    try {
      return require(candidate);
    } catch (e) {
      if (e.code !== "MODULE_NOT_FOUND" && e.code !== "ERR_MODULE_NOT_FOUND") throw e;
    }
  }
  throw new Error("playwright が見つからない。`npm i playwright` するか PLAYWRIGHT_PATH を渡す。");
}

const BLANK = "<!DOCTYPE html><html><head></head><body></body></html>";

// scenario 一本につき新しい page を使う。前の scenario が document を
// 書き換えているので、同じ page を使い回すと初期状態が揃わない。
async function onPage(browser, fn) {
  const page = await browser.newPage();
  try {
    await page.setContent(BLANK);
    await page.addScriptTag({ content: scenarioSource });
    return await fn(page);
  } finally {
    await page.close();
  }
}

function isScenarioFile(path) {
  return path.endsWith(".json") && !path.endsWith(".lean.json") && !path.endsWith(".impl.json");
}

async function main() {
  const argv = process.argv.slice(2);
  const { chromium } = loadPlaywright();
  const browser = await chromium.launch();
  try {
    if (argv[0] === "--capabilities") {
      const caps = await onPage(browser, (page) =>
        page.evaluate(() => globalThis.__domScenario.capabilities(window)));
      console.log(JSON.stringify(caps, null, 2));
      return 0;
    }
    if (argv[0] === "--batch") {
      const dir = argv[1];
      if (!dir) {
        console.error("usage: browser_runner.mjs --batch DIR");
        return 2;
      }
      let failed = 0;
      for (const name of readdirSync(dir).sort()) {
        const path = join(dir, name);
        if (!isScenarioFile(path)) continue;
        const base = basename(name, ".json");
        const scenario = JSON.parse(readFileSync(path, "utf8"));
        let out;
        try {
          out = await onPage(browser, (page) =>
            page.evaluate((sc) => {
              try {
                return globalThis.__domScenario.run(window, sc);
              } catch (e) {
                return { error: `${e?.constructor?.name}: ${e?.message}` };
              }
            }, scenario));
        } catch (e) {
          out = { error: `${e?.constructor?.name}: ${e?.message}` };
        }
        if (out?.error) failed = 1;
        writeFileSync(join(dir, `${base}.impl.json`), JSON.stringify(out));
      }
      return failed;
    }
    const path = argv[0];
    if (!path) {
      console.error("usage: browser_runner.mjs [--capabilities|--batch DIR] SCENARIO.json");
      return 2;
    }
    const scenario = JSON.parse(readFileSync(path, "utf8"));
    const out = await onPage(browser, (page) =>
      page.evaluate((sc) => globalThis.__domScenario.run(window, sc), scenario));
    console.log(JSON.stringify(out));
    return 0;
  } finally {
    await browser.close();
  }
}

process.exit(await main());
