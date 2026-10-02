// 名前空間の囮の sweep を browser（Playwright）で走らせる。
//
//   node test/decoy_sweep.mjs --enumerate OUT.json      # property 名を集める（三つの browser の和）
//   BROWSER=chromium node test/decoy_sweep.mjs NAMES.json OUT.json [CASE_PREFIX]
//
// 本体は `test/js/decoy.js`、比較は `test/decoy_compare.rb`。
// fixture の外への通信はすべて止める（`<base>` が外の host を指している）。

import { readFileSync, writeFileSync } from "node:fs";
import { join, dirname } from "node:path";
import { fileURLToPath } from "node:url";
import { createRequire } from "node:module";

const here = dirname(fileURLToPath(import.meta.url));
const source = readFileSync(join(here, "js/decoy.js"), "utf8");
const fixture = readFileSync(join(here, "decoy/fixture.html"), "utf8");
const require = createRequire(import.meta.url);

function loadPlaywright() {
  for (const c of [process.env.PLAYWRIGHT_PATH, "playwright"].filter(Boolean)) {
    try {
      return require(c);
    } catch (e) {
      if (e.code !== "MODULE_NOT_FOUND" && e.code !== "ERR_MODULE_NOT_FOUND") throw e;
    }
  }
  throw new Error("playwright が見つからない。PLAYWRIGHT_PATH を渡す。");
}

async function withPage(context, fn) {
  const page = await context.newPage();
  try {
    await page.setContent(fixture);
    await page.evaluate(source);
    return await fn(page);
  } finally {
    await page.close();
  }
}

async function launch(pw, engine) {
  const browser = await pw[engine].launch();
  const context = await browser.newContext();
  await context.route("**/*", (route) => route.abort());
  return { browser, context };
}

const argv = process.argv.slice(2);
const pw = loadPlaywright();

if (argv[0] === "--enumerate") {
  const union = { document: new Set(), elements: {}, setters: {} };
  for (const engine of ["chromium", "firefox", "webkit"]) {
    const { browser, context } = await launch(pw, engine);
    const names = await withPage(context, (page) => page.evaluate(() => __decoySweep.enumerate()));
    await browser.close();
    for (const n of names.document) union.document.add(n);
    for (const key of ["elements", "setters"]) {
      for (const [k, list] of Object.entries(names[key])) {
        union[key][k] ??= new Set();
        for (const n of list) union[key][k].add(n);
      }
    }
  }
  const sorted = (s) => Array.from(s).sort();
  const out = {
    document: sorted(union.document),
    elements: Object.fromEntries(Object.entries(union.elements).map(([k, v]) => [k, sorted(v)])),
    setters: Object.fromEntries(Object.entries(union.setters).map(([k, v]) => [k, sorted(v)]))
  };
  writeFileSync(argv[1], JSON.stringify(out));
  process.exit(0);
}

const [namesPath, outPath, prefix = ""] = argv;
const names = JSON.parse(readFileSync(namesPath, "utf8"));
const engine = process.env.BROWSER || "chromium";
const { browser, context } = await launch(pw, engine);
const ids = await withPage(context, (page) => page.evaluate(() => __decoySweep.caseIds()));
const results = [];
for (const id of ids.filter((x) => x.startsWith(prefix))) {
  try {
    results.push(await withPage(context, (page) =>
      page.evaluate(([id, names]) => __decoySweep.runCase(id, names), [id, names])));
  } catch (e) {
    results.push({ id, error: `host:${e.message.split("\n")[0]}` });
  }
}
await browser.close();
writeFileSync(outPath, JSON.stringify({ impl: engine, results }));
