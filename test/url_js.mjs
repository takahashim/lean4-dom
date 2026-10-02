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

import { readFileSync } from "node:fs";

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
  const impl = await openImplementation(spec);
  out[impl.name] = cases.map((c) => parseOne(impl.URL, c));
}
process.stdout.write(JSON.stringify(out));
