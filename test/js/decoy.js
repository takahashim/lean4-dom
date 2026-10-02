// 名前空間の囮（decoy）による不干渉の sweep。
//
// 「仕様が (namespace, local name) の組で同定しているものを、文字列の名前だけで
// 同定している」形の不具合を探す。囮を一つ置いて、その前後で読める値を全部読み、
// 変わったものを報告する。比べる相手は囮を置く前の同じ実装なので、
// model の無い API（HTML の reflect、`dataset`、`document.links` …）にも当たる。
//
// 変わってよいかどうかはここでは決めない。browser 三つと並べて、
// **Dommy だけが変わる行**と**browser が揃って変わるのに Dommy が変わらない行**を
// 拾うのは `test/decoy_compare.rb` である。
//
// 素の script として読み、global に `__decoySweep` を生やす。
// browser（`test/decoy_sweep.mjs`）と Dommy の QuickJS（`test/decoy_dommy.rb`）で
// 同じものを走らせる。fixture は `test/decoy/fixture.html` で、一つの case ごとに
// 新しい document に読み直す。

(function () {
  "use strict";

  const SVG_NS = "http://www.w3.org/2000/svg";
  const MATHML_NS = "http://www.w3.org/1998/Math/MathML";
  const HTML_NS = "http://www.w3.org/1999/xhtml";
  const XML_NS = "http://www.w3.org/XML/1998/namespace";
  const XLINK_NS = "http://www.w3.org/1999/xlink";
  const DECOY_NS = "urn:x-decoy";
  // prefix 無しの囮は別の namespace に置く。同じ namespace だと (namespace, local name) が
  // prefix 付きの囮と同じになり、`setAttributeNS` が前の囮の値を書き換えるだけになる。
  const DECOY_NS_B = "urn:x-decoy-b";

  // 囮にする attribute の名前。global attribute と、fixture の element が持つものを並べる。
  const ATTR_NAMES = [
    "id", "class", "slot", "name", "lang", "dir", "hidden", "title", "style", "tabindex",
    "contenteditable", "draggable", "spellcheck", "translate", "accesskey", "autofocus",
    "inert", "popover", "nonce", "autocapitalize", "inputmode", "enterkeyhint", "is", "part",
    "role", "aria-label", "aria-hidden", "data-foo", "data-new",
    "href", "src", "alt", "value", "type", "for", "form", "list", "disabled", "checked",
    "selected", "required", "readonly", "multiple", "placeholder", "maxlength", "minlength",
    "size", "rows", "cols", "pattern", "min", "max", "step", "open", "label", "action",
    "method", "target", "enctype", "novalidate", "autocomplete", "rel", "download",
    "hreflang", "referrerpolicy", "start", "reversed", "colspan", "rowspan", "headers",
    "scope", "abbr", "width", "height", "usemap", "low", "high", "optimum", "coords",
    "shape", "content", "async", "defer", "crossorigin", "formaction", "formmethod"
  ];

  // null namespace の attribute だが、名前が他の namespace の attribute の qualified name に
  // 見えるもの。`setAttribute` で置く（local name がそのまま `xml:lang` になる）。
  const LOOKALIKE_NAMES = ["xml:lang", "xml:space", "xml:base", "xlink:href", "xmlns", "xmlns:p"];

  // 本物の namespace 付き attribute。HTML でも効くもの（`xml:lang`）を含むので、
  // これは「変わるべきもの」を見る向きである。
  const REAL_NS_ATTRS = [
    [XML_NS, "xml:lang", "de"], [XML_NS, "xml:space", "preserve"], [XML_NS, "xml:base", "/xb/"],
    [XLINK_NS, "xlink:href", "/xl"], [XLINK_NS, "xlink:title", "xt"]
  ];

  // 囮の element の local name。HTML 仕様が「HTML namespace の X element」に限って
  // 何かを定めているものを並べる。
  const ELEMENT_NAMES = [
    "a", "area", "img", "form", "input", "select", "option", "optgroup", "label", "button",
    "textarea", "fieldset", "legend", "output", "title", "base", "link", "meta", "style",
    "script", "template", "slot", "table", "caption", "thead", "tbody", "tr", "td", "th",
    "body", "head", "html", "details", "summary", "dialog", "embed", "object", "map", "li",
    "ol", "datalist", "progress", "meter", "noscript", "span", "div"
  ];

  // 囮の element に付ける null namespace の attribute。
  const ELEMENT_ATTRS = [
    ["name", "dn"], ["href", "/d"], ["src", "/d.png"], ["for", "in1"], ["form", "f1"],
    ["value", "dv"], ["label", "dl"], ["type", "text"], ["rel", "stylesheet"],
    ["content", "dc"], ["lang", "de"], ["dir", "rtl"], ["selected", ""], ["checked", ""],
    ["disabled", ""], ["open", ""], ["hidden", ""]
  ];

  const ELEMENT_NAMESPACES = {
    svg: [SVG_NS, ""], mathml: [MATHML_NS, ""], none: [null, ""], decoy: [DECOY_NS, ""],
    // prefix 付きでも HTML namespace の element は HTML element である（逆向きの囮）。
    htmlPrefixed: [HTML_NS, "h:"]
  };

  // 囮の element を入れる場所。文脈で意味が変わる collection（form の elements、
  // select の options、table の rows …）を撫でるために散らす。
  const PARENTS = {
    html: (d) => d.documentElement, head: (d) => d.head, body: (d) => d.body,
    form: (d) => d.getElementById("f1"), select: (d) => d.getElementById("s1"),
    tbody: (d) => d.getElementById("tbd1"), label: (d) => d.getElementById("l1"),
    fieldset: (d) => d.getElementById("fs1"), ol: (d) => d.getElementById("ol1"),
    details: (d) => d.getElementById("dt1"), map: (d) => d.getElementById("mp1"),
    datalist: (d) => d.getElementById("dl1"), svg: (d) => d.getElementById("svg1")
  };

  // 読むと時間で変わる、または読むこと自体が重いもの。
  const SKIP_PROPS = new Set([
    "lastModified", "cookie", "timeline", "fonts", "currentTime", "timeStamp",
    "outerText", "__proto__", "constructor", "defaultView", "location", "implementation",
    "scrollingElement", "styleSheets", "adoptedStyleSheets", "visibilityState",
    "wasDiscarded", "hasFocus", "fragmentDirective", "featurePolicy", "permissionsPolicy",
    "rootElement", "pictureInPictureElement", "pointerLockElement", "fullscreenElement",
    "domain", "referrer", "URL", "documentURI", "baseURI", "readyState", "prerendering",
    "activeViewTransition"
  ]);

  // 読み取り専用の method で引く値。selector は model の範囲より広い。
  const SELECTORS = [
    "[id]", "#decoy", ".decoy", "[lang]", ":lang(de)", ":lang(fr)", ":lang(en)",
    ":dir(rtl)", ":dir(ltr)", ":link", ":any-link", ":checked", ":disabled", ":enabled",
    ":required", ":optional", ":read-only", ":read-write", ":placeholder-shown", ":default",
    ":indeterminate", ":valid", ":invalid", ":in-range", ":out-of-range", ":defined",
    ":open", ":empty", "[hidden]", "a", "A", "title", "[data-foo]", "[href]", "[name]",
    "[class]", "[slot]", "[dir]", "[type]", "label", "option", "*|a", "[*|href]"
  ];
  const IDS = ["decoy", "d1", "in1", "a1", "dz-a", "dz-input", "dz-option", "dz-title"];
  const NAMES = ["decoy", "dn", "n1", "an", "fm", "im", "r", "sn"];
  const TAG_NAMES = ["a", "A", "title", "TITLE", "h:a", "H:A", "option", "input", "*"];
  const NAMED_ITEMS = ["decoy", "dn", "d1", "an", "n1", "fm", "in1", "dz-a", "dz-input"];

  /* ---------------------------------------------------------------- 値の文字列化 */

  // fixture を読み込んだ直後の element に番号を振る。囮で増えた node は
  // `new:<namespace>:<local name>` で呼ぶ。
  function labeler(doc) {
    const labels = new Map();
    let i = 0;
    const all = doc.getElementsByTagName("*");
    for (let k = 0; k < all.length; k++) {
      const e = all[k];
      labels.set(e, (e.id ? e.id : e.localName + "@" + i));
      i++;
    }
    return function label(node) {
      if (node === null || node === undefined) return String(node);
      if (labels.has(node)) return labels.get(node);
      if (node === doc) return "#document";
      if (node.nodeType === 1) {
        const ns = node.namespaceURI === HTML_NS ? "html" : node.namespaceURI === SVG_NS ? "svg"
          : node.namespaceURI === MATHML_NS ? "mathml" : String(node.namespaceURI);
        return "new:" + ns + ":" + node.localName;
      }
      return node.nodeName;
    };
  }

  const VALIDITY_FIELDS = [
    "valueMissing", "typeMismatch", "patternMismatch", "tooLong", "tooShort",
    "rangeUnderflow", "rangeOverflow", "stepMismatch", "badInput", "customError", "valid"
  ];

  function brand(v) {
    return Object.prototype.toString.call(v).slice(8, -1);
  }

  function show(v, label) {
    if (v === null || v === undefined) return String(v);
    const t = typeof v;
    if (t === "string") return JSON.stringify(v);
    if (t === "number" || t === "boolean" || t === "bigint") return String(v);
    if (t === "function") return "function";
    if (t === "symbol") return "symbol";
    let b;
    try { b = brand(v); } catch (e) { return "object"; }
    try {
      if (typeof v.nodeType === "number") return "node:" + label(v);
      if (b === "DOMTokenList") return "tokens:" + JSON.stringify(String(v.value));
      if (b === "DOMStringMap") {
        const keys = Object.keys(v).sort();
        return "map:" + JSON.stringify(keys.map((k) => [k, v[k]]));
      }
      if (b === "CSSStyleDeclaration" || b === "CSS2Properties") return "style:" + JSON.stringify(v.cssText);
      if (b === "ValidityState") return "validity:" + VALIDITY_FIELDS.map((f) => f + "=" + v[f]).join(",");
      if (b === "NamedNodeMap") {
        const out = [];
        for (let i = 0; i < v.length; i++) out.push(attrKey(v[i]));
        return "attrs:" + JSON.stringify(out);
      }
      if (typeof v.length === "number" && v.length < 200 && typeof v.item === "function") {
        const out = [];
        for (let i = 0; i < v.length; i++) out.push(show(v[i], label));
        return b + ":" + JSON.stringify(out);
      }
      if (Array.isArray(v)) return "array:" + JSON.stringify(v.slice(0, 50).map((x) => show(x, label)));
    } catch (e) {
      return b + "!" + (e && e.name);
    }
    return b;
  }

  function attrKey(a) {
    return (a.namespaceURI === null ? "" : a.namespaceURI) + "|" +
      (a.prefix === null ? "" : a.prefix) + "|" + a.localName + "=" + a.value;
  }

  /* ---------------------------------------------------------------- 観測 */

  // `names` は element ごとの property 名（`elementKey` で引く）と document の property 名。
  function elementKey(e) {
    return (e.namespaceURI || "") + " " + e.localName;
  }

  function read(obj, prop, label) {
    try {
      return show(obj[prop], label);
    } catch (e) {
      return "throw:" + (e && e.name);
    }
  }

  function call(fn, label) {
    try {
      return show(fn(), label);
    } catch (e) {
      return "throw:" + (e && e.name);
    }
  }

  function snapshot(doc, elements, names, label) {
    const out = {};
    for (const p of names.document || []) {
      if (!SKIP_PROPS.has(p)) out["document." + p] = read(doc, p, label);
    }
    for (const e of elements) {
      const l = label(e);
      for (const p of names.elements[elementKey(e)] || []) {
        if (!SKIP_PROPS.has(p)) out[l + "." + p] = read(e, p, label);
      }
      // `Node` ではない読み方。どれも仕様が null namespace の attribute を読む。
      out[l + ".dataset"] = read(e, "dataset", label);
      out[l + ".matches(:lang(de))"] = call(() => e.matches(":lang(de)"), label);
    }
    for (const s of SELECTORS) out["qsa(" + s + ")"] = call(() => doc.querySelectorAll(s), label);
    for (const id of IDS) out["getElementById(" + id + ")"] = call(() => doc.getElementById(id), label);
    for (const n of NAMES) out["getElementsByName(" + n + ")"] = call(() => doc.getElementsByName(n), label);
    for (const n of ["decoy", "c1", "dz"]) out["getElementsByClassName(" + n + ")"] = call(() => doc.getElementsByClassName(n), label);
    for (const n of TAG_NAMES) out["getElementsByTagName(" + n + ")"] = call(() => doc.getElementsByTagName(n), label);
    for (const n of NAMED_ITEMS) {
      out["all.namedItem(" + n + ")"] = call(() => doc.getElementsByTagName("*").namedItem(n), label);
      out["forms.namedItem(" + n + ")"] = call(() => doc.forms.namedItem(n), label);
      out["f1.elements.namedItem(" + n + ")"] = call(() => doc.getElementById("f1").elements.namedItem(n), label);
      out["document[" + n + "]"] = call(() => doc[n], label);
      out["f1[" + n + "]"] = call(() => doc.getElementById("f1")[n], label);
    }
    return out;
  }

  function diff(before, after) {
    const changes = [];
    const keys = new Set(Object.keys(before).concat(Object.keys(after)));
    for (const k of Array.from(keys).sort()) {
      if (before[k] !== after[k]) changes.push([k, before[k], after[k]]);
    }
    return changes;
  }

  function fixtureElements(doc) {
    const all = doc.getElementsByTagName("*");
    const out = [];
    for (let i = 0; i < all.length; i++) out.push(all[i]);
    return out;
  }

  /* ---------------------------------------------------------------- case */

  // 囮を置く手順。`target` は fixture の element。
  const ATTR_DECOYS = {
    // A：prefix 付き。local name だけで引く実装に当たる。
    prefixed: (e) => { for (const n of ATTR_NAMES) e.setAttributeNS(DECOY_NS, "p:" + n, "decoy"); },
    // B：prefix 無し。qualified name でも local name でも一致してしまう。
    unprefixed: (e) => { for (const n of ATTR_NAMES) e.setAttributeNS(DECOY_NS_B, n, "decoy"); },
    // C：null namespace で、名前が別の namespace の qualified name に見えるもの。
    lookalike: (e) => { for (const n of LOOKALIKE_NAMES) e.setAttribute(n, n === "xml:lang" ? "de" : "decoy"); },
    // C'：本物の namespace 付き attribute（変わるべき向き）。
    realNamespaced: (e) => { for (const [ns, qn, v] of REAL_NS_ATTRS) e.setAttributeNS(ns, qn, v); }
  };

  function caseIds(doc) {
    const ids = ["control"];
    const els = fixtureElements(doc);
    const label = labeler(doc);
    for (const kind of Object.keys(ATTR_DECOYS)) {
      for (const e of els) ids.push("attr:" + kind + ":" + label(e));
    }
    for (const ns of Object.keys(ELEMENT_NAMESPACES)) {
      for (const p of Object.keys(PARENTS)) ids.push("elem:" + ns + ":" + p);
    }
    for (const e of els) ids.push("write:" + label(e));
    for (const m of Object.keys(FRAGMENT_METHODS)) {
      for (const c of Object.keys(FRAGMENT_CONTEXTS)) ids.push("frag:" + m + ":" + c);
    }
    return ids;
  }

  function findByLabel(doc, label, wanted) {
    for (const e of fixtureElements(doc)) if (label(e) === wanted) return e;
    throw new Error("no element " + wanted);
  }

  function insertDecoyElements(doc, nsKey, parent) {
    const [ns, prefix] = ELEMENT_NAMESPACES[nsKey];
    for (const ln of ELEMENT_NAMES) {
      const e = doc.createElementNS(ns, prefix + ln);
      e.setAttribute("id", "dz-" + ln);
      e.setAttribute("class", "dz");
      for (const [n, v] of ELEMENT_ATTRS) e.setAttribute(n, v);
      e.appendChild(doc.createTextNode("Z"));
      parent.appendChild(e);
    }
  }

  // 書く側。囮を全部置いてから、setter を一つずつ呼び、attribute list の差を記録する。
  // browser は名前空間付きの attribute に触らないので、触った行がそのまま候補になる。
  function writeCase(doc, target, names, label) {
    ATTR_DECOYS.prefixed(target);
    ATTR_DECOYS.unprefixed(target);
    const attrs = () => {
      const out = [];
      for (let i = 0; i < target.attributes.length; i++) out.push(attrKey(target.attributes[i]));
      return out.sort();
    };
    const results = [];
    const record = (what, fn) => {
      const before = attrs();
      let err = null;
      try { fn(); } catch (e) { err = "throw:" + (e && e.name); }
      const after = attrs();
      const removed = before.filter((x) => !after.includes(x));
      const added = after.filter((x) => !before.includes(x));
      results.push([what, err, removed, added]);
    };
    const setters = names.setters[elementKey(target)] || [];
    for (const p of setters) {
      if (SKIP_PROPS.has(p) || /^on/.test(p) || p === "outerHTML" || p === "innerHTML" ||
          p === "textContent" || p === "innerText" || p === "nodeValue") continue;
      let cur;
      try { cur = target[p]; } catch (e) { continue; }
      const t = typeof cur;
      let v;
      if (t === "string") v = "w";
      else if (t === "boolean") v = !cur;
      else if (t === "number") v = 3;
      else if (cur !== null && t === "object" && (brand(cur) === "DOMTokenList" ||
          brand(cur) === "CSSStyleDeclaration" || brand(cur) === "CSS2Properties")) {
        v = brand(cur) === "DOMTokenList" ? "w" : "color: blue";
      } else continue;
      record("set " + p + "=" + JSON.stringify(v), () => { target[p] = v; });
    }
    record("dataset.foo=w", () => { target.dataset.foo = "w"; });
    record("dataset.new=w", () => { target.dataset["new"] = "w"; });
    record("delete dataset.foo", () => { delete target.dataset.foo; });
    record("classList.add(w2)", () => { target.classList.add("w2"); });
    record("classList.remove(c1)", () => { target.classList.remove("c1"); });
    record("classList.toggle(c2)", () => { target.classList.toggle("c2"); });
    record("style.setProperty(color)", () => { target.style.setProperty("color", "green"); });
    return results;
  }

  /* ---------------------------------------------------------------- 断片の解釈 */

  // HTML の fragment parsing algorithm は context element で foreign content に入るかが決まる。
  // context が SVG / MathML の element なら `<rect/>` は SVG の element になる。
  // HTML parser は model の外なので、ここは browser と並べるだけである。
  const FRAGMENT_MARKUP = "<rect/><mi></mi><b>x</b><svg><circle/></svg><math><mi/></math><p>t</p>";
  const FRAGMENT_CONTEXTS = {
    svg: (d) => d.getElementById("svg1"),
    svgA: (d) => d.getElementById("sa1"),
    math: (d) => d.getElementById("m1"),
    html: (d) => d.getElementById("d1")
  };
  // 文脈の element に対して markup を入れる。outerHTML は文脈の子を置き換えるので、
  // 文脈と同じ namespace の子を一つ作ってから置き換える。
  const FRAGMENT_METHODS = {
    innerHTML: (d, ctx) => { ctx.innerHTML = FRAGMENT_MARKUP; },
    insertAdjacentHTML: (d, ctx) => {
      ctx.textContent = "";
      ctx.insertAdjacentHTML("beforeend", FRAGMENT_MARKUP);
    },
    outerHTML: (d, ctx) => {
      ctx.textContent = "";
      const child = d.createElementNS(ctx.namespaceURI, "g");
      ctx.appendChild(child);
      child.outerHTML = FRAGMENT_MARKUP;
    },
    createContextualFragment: (d, ctx) => {
      ctx.textContent = "";
      const r = d.createRange();
      r.selectNodeContents(ctx);
      ctx.appendChild(r.createContextualFragment(FRAGMENT_MARKUP));
    }
  };

  function fragmentCase(doc, method, context) {
    const ctx = FRAGMENT_CONTEXTS[context](doc);
    let error = null;
    try {
      FRAGMENT_METHODS[method](doc, ctx);
    } catch (e) {
      error = "throw:" + (e && e.name);
    }
    const created = [];
    const all = ctx.getElementsByTagName("*");
    for (let i = 0; i < all.length; i++) {
      const e = all[i];
      const ns = e.namespaceURI === HTML_NS ? "html" : e.namespaceURI === SVG_NS ? "svg"
        : e.namespaceURI === MATHML_NS ? "mathml" : String(e.namespaceURI);
      created.push(ns + ":" + e.localName);
    }
    return { id: "frag:" + method + ":" + context, error, fragment: created };
  }

  function runCase(doc, id, names) {
    const label = labeler(doc);
    const elements = fixtureElements(doc);
    const parts = id.split(":");
    if (parts[0] === "frag") return fragmentCase(doc, parts[1], parts[2]);
    if (parts[0] === "write") {
      return { id, writes: writeCase(doc, findByLabel(doc, label, parts.slice(1).join(":")), names, label) };
    }
    const before = snapshot(doc, elements, names, label);
    let error = null;
    try {
      if (parts[0] === "attr") {
        ATTR_DECOYS[parts[1]](findByLabel(doc, label, parts.slice(2).join(":")));
      } else if (parts[0] === "elem") {
        insertDecoyElements(doc, parts[1], PARENTS[parts[2]](doc));
      }
    } catch (e) {
      error = "throw:" + (e && e.name) + ":" + (e && e.message);
    }
    const after = snapshot(doc, elements, names, label);
    return { id, error, changes: diff(before, after) };
  }

  /* ---------------------------------------------------------------- property 名 */

  // browser でだけ呼ぶ。prototype chain の accessor を element の種類ごとに集める。
  function enumerate(doc) {
    const collect = (obj) => {
      const getters = new Set();
      const setters = new Set();
      let p = Object.getPrototypeOf(obj);
      while (p && p !== Object.prototype) {
        for (const n of Object.getOwnPropertyNames(p)) {
          const d = Object.getOwnPropertyDescriptor(p, n);
          if (d && d.get) getters.add(n);
          if (d && d.set) setters.add(n);
        }
        p = Object.getPrototypeOf(p);
      }
      return [Array.from(getters).sort(), Array.from(setters).sort()];
    };
    const elements = {};
    const setters = {};
    for (const e of fixtureElements(doc)) {
      const [g, s] = collect(e);
      elements[elementKey(e)] = g;
      setters[elementKey(e)] = s;
    }
    return { document: collect(doc)[0], elements, setters };
  }

  globalThis.__decoySweep = {
    caseIds: () => caseIds(document),
    runCase: (id, names) => runCase(document, id, names),
    enumerate: () => enumerate(document)
  };
})();
