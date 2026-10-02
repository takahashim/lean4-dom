// URL の差分テストの JS 側。`test/url_diff.rb` から呼ばれる。
//
//   node test/url_js.mjs CASES.json IMPL...
//
// CASES.json は `[{"input": ..., "base": ...}, ...]`。IMPL は次のどれかで、実装ごとの結果を
// `{"<名前>": [結果, ...], ...}` として一行の JSON で出す。結果は失敗なら null、
// 成功なら IDL attribute（href から hash まで）と origin。
//
// * `node`                     Node の組み込みの URL（Ada）
// * `whatwg-url=/path/to/mod`  whatwg-url（URL Standard の参照実装）。`URL` を export する module
// * `jsdom=/path/to/api.js`    jsdom の window.URL（中身は whatwg-url）
// * `chromium` `firefox` `webkit`  Playwright の browser の page の中の URL
//
// Playwright は `browser_runner.mjs` と同じく `PLAYWRIGHT_PATH`、local な node_modules、
// global install の順に探す。

import { readFileSync } from "node:fs";
import { createRequire } from "node:module";

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

const BROWSERS = ["chromium", "firefox", "webkit"];

// page の中で評価する。`parseOne` と同じことをする（関数は page へ持ち込めないので書き直してある）。
async function parseInBrowser(engine, cases) {
  const browser = await loadPlaywright()[engine].launch();
  try {
    const page = await browser.newPage();
    return await page.evaluate(({ cases, fields }) => cases.map((c) => {
      try {
        const u = c.base === undefined || c.base === null ? new URL(c.input) : new URL(c.input, c.base);
        return Object.fromEntries(fields.map((f) => [f, String(u[f])]));
      } catch {
        return null;
      }
    }), { cases, fields: FIELDS });
  } finally {
    await browser.close();
  }
}

const FIELDS = ["href", "protocol", "username", "password", "host", "hostname", "port",
  "pathname", "search", "hash", "origin"];

async function openImplementation(spec) {
  if (spec === "node") return { name: "node", URL: globalThis.URL };
  const eq = spec.indexOf("=");
  if (eq < 0) throw new Error(`実装の指定が読めない: ${spec}`);
  const name = spec.slice(0, eq);
  const path = spec.slice(eq + 1);
  const mod = await import(path);
  if (name === "jsdom" || mod.JSDOM) {
    const { JSDOM } = mod.JSDOM ? mod : mod.default;
    return { name, URL: new JSDOM("").window.URL };
  }
  const URLClass = mod.URL ?? mod.default?.URL;
  if (!URLClass) throw new Error(`${path} は URL を export していない`);
  return { name, URL: URLClass };
}

function parseOne(URLClass, c) {
  try {
    const u = c.base === undefined || c.base === null ? new URLClass(c.input) : new URLClass(c.input, c.base);
    return Object.fromEntries(FIELDS.map((f) => [f, String(u[f])]));
  } catch {
    return null;
  }
}

const [casesPath, ...impls] = process.argv.slice(2);
const cases = JSON.parse(readFileSync(casesPath, "utf8"));
const out = {};
for (const spec of impls) {
  if (BROWSERS.includes(spec)) {
    out[spec] = await parseInBrowser(spec, cases);
    continue;
  }
  const impl = await openImplementation(spec);
  out[impl.name] = cases.map((c) => parseOne(impl.URL, c));
}
process.stdout.write(JSON.stringify(out));
