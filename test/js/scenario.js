// scenario を評価する本体。**この file は DOM しか触らない。**
//
// Node から呼ぶとき（`test/js_runner.mjs`、jsdom / happy-dom）と、browser の page の
// 中で呼ぶとき（`test/browser_runner.mjs`）の両方で同じものを動かすために、
// import も export も持たない素の script にしてある。読み込むと
// `globalThis.__domScenario` に `run` と `capabilities` が生える。
//
// 実装が持っていない口のせいで比べられない step は
// `{"ok": false, "exception": "__unsupported__", "reason": ...}` として報告する。
// 仕様上の例外との区別を残すためで、実装漏れの印ではない。

const UNSUPPORTED = "__unsupported__";
const UNKNOWN_NODE = "?";
const SHOW_ALL = 0xffffffff;
const HTML_NS = "http://www.w3.org/1999/xhtml";

/** この harness では比べられない、という印。実装漏れとは区別する。 */
class Unsupported extends Error {}

/**
 * scenario の document 一つ分の、空の Document を配る。
 *
 * 最初の一つは window の document をそのまま使う。二つ目からは
 * `createHTMLDocument` で足す。window の document を使うのは、実装が
 * 「window の document でしか正しく動かない口」を持っていることがあるからで
 * （happy-dom の `createTextNode` は node document を window の document に
 * してしまう）、scenario の大半は document 一つなので、それで測れる幅が広がる。
 */
function makeDocumentFactory(win) {
  let first = true;
  return () => {
    const doc = first ? win.document : win.document.implementation.createHTMLDocument("");
    first = false;
    // `n.remove()` ではなく `removeChild` を使う。ChildNode mixin を
    // DocumentType に付けていない実装があるので、そこで落ちないようにする。
    for (const n of [...doc.childNodes]) doc.removeChild(n);
    return doc;
  };
}

/* ------------------------------------------------------------------ 操作の表 */

// 操作が呼ぶ JS 側の method 名。capability 判定にも使う。
const OP_METHOD = {
  appendChild: "appendChild", insertBefore: "insertBefore", replaceChild: "replaceChild",
  removeChild: "removeChild", replaceChildren: "replaceChildren", before: "before",
  after: "after", replaceWith: "replaceWith", remove: "remove", moveBefore: "moveBefore",
  replaceData: "replaceData", appendData: "appendData", insertData: "insertData",
  deleteData: "deleteData", setData: "data", setAttribute: "setAttribute",
  setAttributeNS: "setAttributeNS", removeAttribute: "removeAttribute",
  removeAttributeNS: "removeAttributeNS", toggleAttribute: "toggleAttribute",
  dispatchEvent: "dispatchEvent", addEventListener: "addEventListener",
  removeEventListener: "removeEventListener", normalize: "normalize",
  createElement: "createElement", createElementNS: "createElementNS",
  createTextNode: "createTextNode", createComment: "createComment",
  createDocumentFragment: "createDocumentFragment", cloneNode: "cloneNode",
  importNode: "importNode", adoptNode: "adoptNode"
};

// node を作る操作。受け手は Document である（cloneNode を除く）。
const CREATE_OPS = ["createElement", "createElementNS", "createTextNode", "createComment",
  "createDocumentFragment", "importNode", "adoptNode"];

// nodeType から scenario の kind 名へ。作った node に kind を付けるのに使う。
const NODE_TYPE_KIND = {
  1: "element", 3: "text", 4: "cdataSection", 7: "processingInstruction",
  8: "comment", 9: "document", 10: "documentType", 11: "documentFragment"
};

// 値を返すだけの操作と、その IDL 名。
const QUERY_JS_NAME = {
  compareDocumentPosition: "compareDocumentPosition", nodeContains: "contains",
  getRootNode: "getRootNode", isEqualNode: "isEqualNode", getTextContent: "textContent",
  getNodeValue: "nodeValue", substringData: "substringData", getAttribute: "getAttribute",
  hasAttribute: "hasAttribute", getAttributeNames: "getAttributeNames",
  lookupNamespaceURI: "lookupNamespaceURI", lookupPrefix: "lookupPrefix",
  isDefaultNamespace: "isDefaultNamespace"
};
const QUERY_OPS = Object.keys(QUERY_JS_NAME);
const QUERY_GETTERS = ["getTextContent", "getNodeValue"];

const WALKER_OPS = ["walkerParentNode", "walkerFirstChild", "walkerLastChild",
  "walkerPreviousSibling", "walkerNextSibling", "walkerPreviousNode", "walkerNextNode"];
const WALKER_METHOD = {
  walkerParentNode: "parentNode", walkerFirstChild: "firstChild", walkerLastChild: "lastChild",
  walkerPreviousSibling: "previousSibling", walkerNextSibling: "nextSibling",
  walkerPreviousNode: "previousNode", walkerNextNode: "nextNode"
};
const RANGE_OPS = ["rangeSetStart", "rangeSetEnd", "rangeSetStartBefore", "rangeSetStartAfter",
  "rangeSetEndBefore", "rangeSetEndAfter", "rangeCollapse", "rangeSelectNode",
  "rangeSelectNodeContents", "rangeIsPointInRange", "rangeIntersectsNode",
  "rangeCompareBoundaryPoints", "rangeComparePoint", "rangeDeleteContents",
  "rangeInsertNode", "rangeToString"];
const CHARACTER_DATA_OPS = ["replaceData", "appendData", "insertData", "deleteData", "setData"];
const ATTRIBUTE_OPS = ["setAttribute", "setAttributeNS", "removeAttribute",
  "removeAttributeNS", "toggleAttribute"];
const NODE_RETURNING_OPS = ["appendChild", "insertBefore", "replaceChild", "removeChild",
  "iteratorNext", "iteratorPrevious", "getRootNode", ...WALKER_OPS, ...CREATE_OPS, "cloneNode"];

/* ------------------------------------------------------------------ 初期状態 */

class Builder {
  constructor(win, specs) {
    this.win = win;
    this.newDocument = makeDocumentFactory(win);
    this.specs = specs;
    this.objects = new Map();
    this.documents = new Map();
  }

  build() {
    const defaultDocId = this.specs.find((s) => s.kind === "document")?.id;
    for (const s of this.specs) this.create(s, defaultDocId);
    // children の順序は nodes 配列の並び順で決まる。
    for (const s of this.specs) {
      if (s.parent === null || s.parent === undefined) continue;
      const parent = this.objects.get(s.parent);
      if (!parent || typeof parent.appendChild !== "function") {
        throw new Error(`node ${s.parent} に appendChild が無い`);
      }
      parent.appendChild(this.objects.get(s.id));
    }
    return this.objects;
  }

  ownerDocument(spec, defaultDocId) {
    const id = spec.ownerDocument ?? (spec.kind === "document" ? spec.id : defaultDocId);
    const doc = this.documents.get(id);
    if (!doc) throw new Error(`node ${spec.id}: ownerDocument ${id} が document ではない`);
    return doc;
  }

  create(spec, defaultDocId) {
    const data = String(spec.data ?? "");
    if (spec.kind === "document") {
      const doc = this.newDocument();
      this.documents.set(spec.id, doc);
      this.objects.set(spec.id, doc);
      return;
    }
    const doc = this.ownerDocument(spec, defaultDocId);
    let node;
    switch (spec.kind) {
      case "element": node = this.createElement(doc, spec); break;
      case "text": node = doc.createTextNode(data); break;
      case "comment": node = doc.createComment(data); break;
      case "processingInstruction": node = doc.createProcessingInstruction("pi", data); break;
      case "cdataSection": node = doc.createCDATASection(data); break;
      case "documentFragment": node = doc.createDocumentFragment(); break;
      case "documentType": node = doc.implementation.createDocumentType("html", "", ""); break;
      default: throw new Error(`未知の kind ${spec.kind}`);
    }
    applyInitialAttributes(node, spec.attributes);
    this.objects.set(spec.id, node);
  }

  createElement(doc, spec) {
    const ns = spec.namespace ?? HTML_NS;
    const qn = spec.prefix ? `${spec.prefix}:${spec.localName}` : (spec.localName ?? "div");
    if (ns === HTML_NS && !spec.prefix) return doc.createElement(qn);
    return doc.createElementNS(ns, qn);
  }
}

// scenario が与えた初期 attribute を、observer が居ないうちに置く。
// 常に namespace 版を使う。`setAttribute` は HTML namespace の element が
// HTML document にあるとき名前を ASCII lowercase するので、名前をそのまま置けない。
function applyInitialAttributes(node, attrs) {
  if (!attrs || attrs.length === 0) return;
  if (typeof node.setAttributeNS !== "function") {
    throw new Unsupported("attributes on non-element");
  }
  for (const a of attrs) {
    const qn = a.prefix ? `${a.prefix}:${a.localName}` : String(a.localName ?? "");
    node.setAttributeNS(a.namespace ?? null, qn, String(a.value ?? ""));
  }
}

/* ------------------------------------------------------------------ 観測 */

function makeIdLookup(objects) {
  const byNode = new Map();
  const sync = () => {
    for (const [id, node] of objects) if (!byNode.has(node)) byNode.set(node, id);
  };
  sync();
  // `Map` は SameValueZero なので、object の同一性で引ける。
  // 実装が wrapper を作り直していたら見つからず、`?` として不一致に出る。
  // 途中で作った node は `objects` に足されるので、見つからなければ引き直す。
  return (node) => {
    if (node === null || node === undefined) return null;
    let id = byNode.get(node);
    if (id === undefined) {
      sync();
      id = byNode.get(node);
    }
    return id === undefined ? UNKNOWN_NODE : id;
  };
}

/** 作った node の kind。 */
function kindName(node) {
  const k = NODE_TYPE_KIND[node?.nodeType];
  if (!k) throw new Unsupported("nodeType");
  return k;
}

/**
 * 作った node に scenario の id を振る。
 *
 * model の `freshId` は **木にある id の最大より一つ大きいもの**で、deep な clone は
 * tree order（preorder）でそれを順に使う。こちらも同じ規則で振る。
 * これで、生成した node も id で比べられるようになる。
 */
function registerSubtree(ctx, node) {
  if (node === null || node === undefined) return null;
  let max = -1;
  for (const id of ctx.objects.keys()) if (id > max) max = id;
  const id = max + 1;
  ctx.objects.set(id, node);
  ctx.kinds.set(id, kindName(node));
  for (const c of [...(node.childNodes ?? [])]) registerSubtree(ctx, c);
  return id;
}

function elementField(node, name) {
  if (node?.nodeType !== 1) return null;
  const v = node[name];
  return v === null || v === undefined ? null : String(v);
}

function attributeNodes(node) {
  if (node?.nodeType !== 1 || !node.attributes) return [];
  return [...node.attributes];
}

/**
 * attribute に model と同じ規則で id を振る。
 *
 *   初期状態   node の id の昇順・node の中では list 順に 1 から
 *   新しいもの いま木にある id の最大より一つ大きいもの
 *
 * 1 から始めるのは、model の `maxAttrId` が attribute の無い木で 0 を返すからである。
 *
 * model の `freshAttrId` がそうしている。`Attr` object の同一性で引くので、
 * `setAttribute` が既にある attribute を書き換えたのか作り直したのかが観測できる。
 * いま無い attribute の id は覚えない（model 側の最大も現在の木だけで決まる）。
 */
function refreshAttrIds(ctx) {
  const old = ctx.attrIds ?? new Map();
  const ordered = [];
  for (const nid of [...ctx.objects.keys()].sort((a, b) => a - b)) {
    for (const a of attributeNodes(ctx.objects.get(nid))) ordered.push(a);
  }
  const fresh = new Map();
  let max = 0;
  for (const a of ordered) {
    const id = old.get(a);
    if (id === undefined) continue;
    fresh.set(a, id);
    if (id > max) max = id;
  }
  for (const a of ordered) {
    if (fresh.has(a)) continue;
    max += 1;
    fresh.set(a, max);
  }
  ctx.attrIds = fresh;
}

function attributesOf(ctx, node) {
  return attributeNodes(node).map((a) => ({
    id: ctx.attrIds.get(a),
    namespace: a.namespaceURI ?? null,
    prefix: a.prefix ?? null,
    localName: a.localName,
    value: String(a.value ?? "")
  }));
}

function dataOf(node) {
  try {
    return typeof node.data === "string" ? node.data : "";
  } catch {
    return "";
  }
}

function snapshot(ctx) {
  const { objects, kinds, idOf } = ctx;
  refreshAttrIds(ctx);
  const nodes = [...objects.keys()].sort((a, b) => a - b).map((id) => {
    const node = objects.get(id);
    return {
      id,
      kind: kinds.get(id),
      parent: idOf(node.parentNode ?? null),
      children: [...(node.childNodes ?? [])].map(idOf),
      nodeDocument: kinds.get(id) === "document" ? id : idOf(node.ownerDocument ?? null),
      data: dataOf(node),
      attributes: attributesOf(ctx, node),
      namespace: elementField(node, "namespaceURI"),
      prefix: elementField(node, "prefix"),
      localName: elementField(node, "localName") ?? "",
      tagName: elementField(node, "tagName")
    };
  });
  const out = {
    nodes,
    ranges: ctx.ranges.map((r) => ({
      start: { node: idOf(r.startContainer), offset: r.startOffset },
      end: { node: idOf(r.endContainer), offset: r.endOffset }
    })),
    iterators: ctx.iteratorSnapshot(),
    walkers: ctx.walkers.map((w) => ({
      root: idOf(w.root), current: idOf(w.currentNode), whatToShow: w.whatToShow
    }))
  };
  if (ctx.observerCount > 0) out.observers = ctx.observerQueues();
  return out;
}

/* ------------------------------------------------------------------ 戻り値 */

function returnValueSnapshot(idOf, op, returned) {
  const name = op.op;
  if (NODE_RETURNING_OPS.includes(name)) {
    return { kind: "node", node: returned === null || returned === undefined ? null : idOf(returned) };
  }
  switch (name) {
    case "toggleAttribute": case "rangeIsPointInRange": case "rangeIntersectsNode":
    case "dispatchEvent": case "nodeContains": case "isEqualNode": case "hasAttribute":
    case "isDefaultNamespace":
      return { kind: "boolean", value: !!returned };
    case "rangeCompareBoundaryPoints": case "rangeComparePoint": case "compareDocumentPosition":
      return { kind: "number", value: Number(returned) | 0 };
    case "getTextContent": case "getNodeValue": case "substringData": case "getAttribute":
    case "rangeToString": case "lookupNamespaceURI": case "lookupPrefix":
      return { kind: "string", value: returned === null || returned === undefined ? null : String(returned) };
    case "getAttributeNames":
      return { kind: "strings", value: [...(returned ?? [])].map(String) };
    case "takeRecords":
      return { kind: "records", records: returned ?? [] };
    default:
      return { kind: "undefined" };
  }
}

/**
 * lone surrogate を含むか。
 *
 * JS の String は lone surrogate を持てるが、JSON に出すと `\ud83d` 単独になり、
 * Ruby の JSON parser が受け取れない。Ruby 側の runner も UTF-8 String の都合で
 * 同じところを断っているので、同じく「比べられない」として扱う。
 */
function hasLoneSurrogate(str) {
  for (let i = 0; i < str.length; i++) {
    const c = str.charCodeAt(i);
    if (c >= 0xd800 && c <= 0xdbff) {
      const next = str.charCodeAt(i + 1);
      if (!(next >= 0xdc00 && next <= 0xdfff)) return true;
      i++;
    } else if (c >= 0xdc00 && c <= 0xdfff) {
      return true;
    }
  }
  return false;
}

function anyLoneSurrogate(value) {
  if (typeof value === "string") return hasLoneSurrogate(value);
  if (Array.isArray(value)) return value.some(anyLoneSurrogate);
  if (value && typeof value === "object") return Object.values(value).some(anyLoneSurrogate);
  return false;
}

/** 実装の例外から仕様上の名前を取り出す。 */
function exceptionName(e) {
  if (typeof e?.name === "string" && e.name.length > 0) return e.name;
  return e?.constructor?.name ?? "Error";
}

/* ------------------------------------------------------------------ 操作の適用 */

function receiverId(op) {
  if (CHARACTER_DATA_OPS.includes(op.op)) return op.node;
  if (QUERY_OPS.includes(op.op) && "node" in op) return op.node;
  if (ATTRIBUTE_OPS.includes(op.op)) return op.element;
  return "target" in op ? op.target : op.parent;
}

function need(value, what) {
  if (value === null || value === undefined) throw new Unsupported(what);
  return value;
}

function observeOptions(spec) {
  const o = {
    childList: !!spec.childList,
    subtree: !!spec.subtree,
    characterData: !!spec.characterData,
    characterDataOldValue: !!spec.characterDataOldValue,
    attributes: !!spec.attributes,
    attributeOldValue: !!spec.attributeOldValue
  };
  if (spec.attributeFilter) o.attributeFilter = spec.attributeFilter;
  return o;
}

function applyRangeOp(ctx, op) {
  const range = need(ctx.ranges[op.range], "range index");
  // `"node": null` は「Node でない引数」である。WebIDL は step に入る前に引数を
  // 変換するので、そのまま渡して TypeError を見る。存在しない id は作りようが
  // 無いので、従来どおり比較から外す。
  let node = null;
  if ("node" in op && op.node !== null && op.node !== undefined) {
    node = need(ctx.objects.get(op.node), "missing node");
  }
  switch (op.op) {
    case "rangeSetStart": return range.setStart(node, op.offset);
    case "rangeSetEnd": return range.setEnd(node, op.offset);
    case "rangeSetStartBefore": return range.setStartBefore(node);
    case "rangeSetStartAfter": return range.setStartAfter(node);
    case "rangeSetEndBefore": return range.setEndBefore(node);
    case "rangeSetEndAfter": return range.setEndAfter(node);
    case "rangeCollapse": return range.collapse(!!op.toStart);
    case "rangeSelectNode": return range.selectNode(node);
    case "rangeSelectNodeContents": return range.selectNodeContents(node);
    case "rangeIsPointInRange": return range.isPointInRange(node, op.offset);
    case "rangeIntersectsNode": return range.intersectsNode(node);
    case "rangeCompareBoundaryPoints":
      return range.compareBoundaryPoints(op.how, need(ctx.ranges[op.source], "range index"));
    case "rangeComparePoint": return range.comparePoint(node, op.offset);
    case "rangeDeleteContents": return range.deleteContents();
    case "rangeInsertNode": return range.insertNode(node);
    case "rangeToString": return range.toString();
  }
}

function applyQueryOp(ctx, op) {
  const receiver = need(ctx.objects.get("element" in op ? op.element : op.node), "missing node");
  const name = QUERY_JS_NAME[op.op];
  if (QUERY_GETTERS.includes(op.op)) {
    if (!(name in receiver)) throw new Unsupported(name);
    return receiver[name];
  }
  if (typeof receiver[name] !== "function") throw new Unsupported(name);
  switch (op.op) {
    case "compareDocumentPosition": case "nodeContains": case "isEqualNode":
      return receiver[name](need(ctx.objects.get(op.other), "missing node"));
    case "getRootNode": case "getAttributeNames": return receiver[name]();
    case "substringData": return receiver[name](op.offset, op.count);
    case "getAttribute": case "hasAttribute": return receiver[name](op.name);
    case "lookupNamespaceURI": return receiver[name](op.prefix ?? null);
    case "lookupPrefix": case "isDefaultNamespace": return receiver[name](op.namespace ?? null);
  }
}

function apply(ctx, op) {
  const { objects, idOf } = ctx;
  switch (op.op) {
    case "iteratorNext": case "iteratorPrevious": {
      const it = need(ctx.iterators[op.iterator], "iterator index");
      return op.op === "iteratorNext" ? it.nextNode() : it.previousNode();
    }
    case "observe": {
      const mo = need(ctx.observerSet?.observers[op.observer], "observer index");
      const target = need(objects.get(op.target), "missing target");
      return mo.observe(target, observeOptions(op));
    }
    case "disconnect": {
      const mo = need(ctx.observerSet?.observers[op.observer], "observer index");
      mo.disconnect();
      // 仕様の disconnect は record queue も空にする。
      ctx.observerSet.queues[op.observer] = [];
      return undefined;
    }
    case "takeRecords": {
      need(ctx.observerSet?.observers[op.observer], "observer index");
      ctx.observerSet.drain();
      return ctx.observerSet.take(op.observer);
    }
    case "notify":
      // 配送順は notify set の並びで決まる。こちら側の queue からは復元できない。
      throw new Unsupported("MutationObserver の配送順");
    case "createElement": case "createElementNS": case "createTextNode":
    case "createComment": case "createDocumentFragment":
    case "importNode": case "adoptNode": {
      const doc = need(objects.get(op.document), "missing node");
      if (typeof doc[OP_METHOD[op.op]] !== "function") throw new Unsupported(op.op);
      const src = (op.op === "importNode" || op.op === "adoptNode")
        ? need(objects.get(op.node), "missing node")
        : null;
      let made;
      switch (op.op) {
        case "createElement": made = doc.createElement(String(op.localName ?? "")); break;
        case "createElementNS":
          made = doc.createElementNS(op.namespace ?? null, String(op.name ?? "")); break;
        case "createTextNode": made = doc.createTextNode(String(op.data ?? "")); break;
        case "createComment": made = doc.createComment(String(op.data ?? "")); break;
        case "createDocumentFragment": made = doc.createDocumentFragment(); break;
        case "importNode": made = doc.importNode(src, !!op.deep); break;
        default: made = doc.adoptNode(src); break;
      }
      // adoptNode は node を作らない。渡した node がそのまま返るので id は既にある。
      if (op.op !== "adoptNode") registerSubtree(ctx, made);
      return made;
    }
    case "cloneNode": {
      const src = need(objects.get(op.node), "missing node");
      if (typeof src.cloneNode !== "function") throw new Unsupported("cloneNode");
      const copy = src.cloneNode(!!op.deep);
      registerSubtree(ctx, copy);
      return copy;
    }
    case "dispatchEvent": {
      const target = need(objects.get(op.target), "missing node");
      const event = new ctx.win.Event(String(op.type),
        { bubbles: !!op.bubbles, cancelable: !!op.cancelable });
      return target.dispatchEvent(event);
    }
    case "addEventListener": {
      const target = need(objects.get(op.target), "missing node");
      const cb = need(ctx.callbacks[op.source], "listener index");
      return target.addEventListener(String(op.type), cb,
        { capture: !!op.capture, once: !!op.once });
    }
    case "removeEventListener": {
      const target = need(objects.get(op.target), "missing node");
      const cb = need(ctx.callbacks[op.callback], "listener index");
      return target.removeEventListener(String(op.type), cb, { capture: !!op.capture });
    }
  }
  if (QUERY_OPS.includes(op.op)) return applyQueryOp(ctx, op);
  if (WALKER_OPS.includes(op.op)) {
    const w = need(ctx.walkers[op.walker], "walker index");
    const m = WALKER_METHOD[op.op];
    if (typeof w[m] !== "function") throw new Unsupported(m);
    return w[m]();
  }
  if (RANGE_OPS.includes(op.op)) return applyRangeOp(ctx, op);
  if (CHARACTER_DATA_OPS.includes(op.op)) {
    const node = need(objects.get(op.node), "missing node");
    if (op.op === "setData") {
      if (!("data" in node)) throw new Unsupported("data");
      node.data = String(op.data ?? "");
      return undefined;
    }
    const m = OP_METHOD[op.op];
    if (typeof node[m] !== "function") throw new Unsupported(m);
    switch (op.op) {
      case "replaceData": return node.replaceData(op.offset, op.count, String(op.data ?? ""));
      case "appendData": return node.appendData(String(op.data ?? ""));
      case "insertData": return node.insertData(op.offset, String(op.data ?? ""));
      case "deleteData": return node.deleteData(op.offset, op.count);
    }
  }
  if (ATTRIBUTE_OPS.includes(op.op)) {
    const el = need(objects.get(op.element), "missing node");
    const m = OP_METHOD[op.op];
    if (typeof el[m] !== "function") throw new Unsupported(m);
    const name = String(op.name);
    switch (op.op) {
      case "setAttribute": return el.setAttribute(name, String(op.value ?? ""));
      case "setAttributeNS":
        return el.setAttributeNS(op.namespace ?? null, name, String(op.value ?? ""));
      case "removeAttribute": return el.removeAttribute(name);
      case "removeAttributeNS": return el.removeAttributeNS(op.namespace ?? null, name);
      case "toggleAttribute":
        return "force" in op && op.force !== null
          ? el.toggleAttribute(name, op.force)
          : el.toggleAttribute(name);
    }
  }
  const receiver = need(objects.get(receiverId(op)), "missing node");
  const m = OP_METHOD[op.op];
  if (m === undefined) throw new Error(`未知の op ${op.op}`);
  if (typeof receiver[m] !== "function") throw new Unsupported(op.op);
  // 存在しない id を指した引数は、実装側では undefined になる。仕様では
  // 「Node でない値」なので TypeError 相当だが、model 側は notFoundError を
  // 返すので、そのままでは意味のある比較にならない。harness 側の都合である。
  const o = (key) => (key === null || key === undefined ? null : objects.get(key));
  switch (op.op) {
    case "appendChild": return receiver.appendChild(need(o(op.node), "missing node"));
    case "insertBefore": {
      const node = need(o(op.node), "missing node");
      const child = op.child === null || op.child === undefined
        ? null : need(o(op.child), "missing child");
      return receiver.insertBefore(node, child);
    }
    case "replaceChild":
      return receiver.replaceChild(need(o(op.node), "missing node"),
        need(o(op.child), "missing child"));
    case "removeChild": return receiver.removeChild(need(o(op.node), "missing node"));
    case "replaceChildren":
      return op.node === null || op.node === undefined
        ? receiver.replaceChildren()
        : receiver.replaceChildren(need(o(op.node), "missing node"));
    case "before": return receiver.before(need(o(op.node), "missing node"));
    case "after": return receiver.after(need(o(op.node), "missing node"));
    case "replaceWith": return receiver.replaceWith(need(o(op.node), "missing node"));
    case "remove": return receiver.remove();
    case "normalize": return receiver.normalize();
    case "moveBefore": {
      const node = need(o(op.node), "missing node");
      const child = op.child === null || op.child === undefined
        ? null : need(o(op.child), "missing child");
      return receiver.moveBefore(node, child);
    }
  }
  throw new Error(`未知の op ${op.op}`);
}

/* ------------------------------------------------------------------ live object */

// scenario の Range。
function buildRanges(objects, documents, specs) {
  return (specs ?? []).map((spec) => {
    const doc = documents.values().next().value;
    if (!doc) throw new Error("document が無いので Range を作れない");
    const range = doc.createRange();
    range.setStart(objects.get(spec.start.node), spec.start.offset);
    range.setEnd(objects.get(spec.end.node), spec.end.offset);
    return range;
  });
}

// scenario の TreeWalker。`createTreeWalker` は current を root に置く。
function buildWalkers(objects, documents, specs) {
  return (specs ?? []).map((spec) => {
    const doc = documents.values().next().value;
    if (!doc) throw new Error("document が無いので TreeWalker を作れない");
    const w = doc.createTreeWalker(objects.get(spec.root), spec.whatToShow ?? SHOW_ALL, null);
    if (spec.current !== undefined && spec.current !== null && spec.current !== spec.root) {
      w.currentNode = objects.get(spec.current);
    }
    return w;
  });
}

// scenario の NodeIterator。仕様の `createNodeIterator` は reference を
// (root, true) に初期化する。reference の setter は仕様に無いので、
// scenario 側もこの初期状態から始めることを求める。
function buildIterators(objects, documents, specs) {
  return (specs ?? []).map((spec) => {
    if (spec.reference !== spec.root || spec.pointerBeforeReference === false) {
      throw new Error(`iterator の初期状態は (root, true) でなければならない`);
    }
    const doc = documents.values().next().value;
    if (!doc) throw new Error("document が無いので NodeIterator を作れない");
    return doc.createNodeIterator(objects.get(spec.root), spec.whatToShow ?? SHOW_ALL, null);
  });
}

// scenario の event listener。callback そのものは model の外なので、
// scenario が宣言した「決まった副作用」を行う関数を作る。
// 呼ばれたことは log に積み、差分テストはその列を比べる。
function buildListeners(objects, idOf, specs, log) {
  const list = specs ?? [];
  const callbacks = [];
  list.forEach((spec, i) => {
    const callbackId = spec.callback ?? i;
    callbacks[i] = (event) => {
      log.push({
        callback: callbackId,
        currentTarget: idOf(event.currentTarget),
        eventPhase: event.eventPhase
      });
      try {
        runListenerAction(objects, callbacks, list, spec.action, event);
      } catch (e) {
        // 実装は listener の例外を握り潰すので、その前に印を残す。
        log.push({ callback: callbackId, error: `${e?.constructor?.name}: ${e?.message}` });
      }
    };
  });
  list.forEach((spec, i) => {
    const target = objects.get(spec.target);
    if (!target) throw new Unsupported("missing listener target");
    target.addEventListener(String(spec.type), callbacks[i],
      { capture: !!spec.capture, once: !!spec.once });
  });
  return callbacks;
}

function runListenerAction(objects, callbacks, specs, action, event) {
  const kind = action && typeof action === "object" ? action.kind : action;
  switch (kind) {
    case undefined: case null: case "none": return;
    case "stopPropagation": return event.stopPropagation();
    case "stopImmediatePropagation": return event.stopImmediatePropagation();
    case "preventDefault": return event.preventDefault();
    case "removeListener": {
      const spec = specs[action.index];
      if (!spec) throw new Unsupported("listener index");
      objects.get(spec.target).removeEventListener(String(spec.type), callbacks[action.index],
        { capture: !!spec.capture });
      return;
    }
    case "addListener": {
      const cb = callbacks[action.source];
      if (!cb) throw new Unsupported("listener index");
      objects.get(action.target).addEventListener(String(action.type), cb,
        { capture: !!action.capture });
      return;
    }
    default: throw new Unsupported(`listener action ${kind}`);
  }
}

/**
 * scenario の MutationObserver。
 *
 * 仕様には「積まれた record を取り出さずに読む」口が無い（`takeRecords()` は
 * 空にしてしまう）。そこで step ごとに `takeRecords()` で引き取り、こちら側の
 * queue に積み直す。queue の中身と `takeRecords` の戻り値はこれで一致する。
 *
 * 配送（`notify` = microtask checkpoint）だけは支えられない。
 * 仕様の配送順は notify set の並びで決まり、こちら側の queue からは復元できない。
 */
class ObserverSet {
  constructor(win, idOf, specs) {
    this.idOf = idOf;
    this.queues = (specs ?? []).map(() => []);
    this.observers = (specs ?? []).map(() => new win.MutationObserver(() => {}));
  }

  registerInitial(objects, specs) {
    (specs ?? []).forEach((spec, i) => {
      if (spec.target === undefined || spec.target === null) return;
      this.observers[i].observe(objects.get(spec.target), observeOptions(spec));
    });
  }

  /** 積まれた record を引き取って自前の queue へ移す。step ごとに呼ぶ。 */
  drain() {
    this.observers.forEach((mo, i) => {
      for (const rec of mo.takeRecords()) this.queues[i].push(this.recordSnapshot(rec));
    });
  }

  snapshot() {
    return this.queues.map((q) => [...q]);
  }

  take(index) {
    const out = this.queues[index];
    this.queues[index] = [];
    return out;
  }

  recordSnapshot(rec) {
    const nodes = (key) => [...(rec[key] ?? [])].map(this.idOf);
    return {
      type: rec.type,
      target: this.idOf(rec.target),
      addedNodes: nodes("addedNodes"),
      removedNodes: nodes("removedNodes"),
      previousSibling: this.idOf(rec.previousSibling),
      nextSibling: this.idOf(rec.nextSibling),
      attributeName: rec.attributeName ?? null,
      attributeNamespace: rec.attributeNamespace ?? null,
      oldValue: rec.oldValue ?? null
    };
  }
}

/* ------------------------------------------------------------------ 一本走らせる */

function run(win, scenario) {
  const specs = scenario.nodes ?? [];
  const kinds = new Map(specs.map((s) => [s.id, s.kind]));
  const builder = new Builder(win, specs);
  const objects = builder.build();
  const idOf = makeIdLookup(objects);
  const ranges = buildRanges(objects, builder.documents, scenario.ranges);
  const walkers = buildWalkers(objects, builder.documents, scenario.walkers);

  // NodeIterator は `referenceNode` / `pointerBeforeReferenceNode` が読めないと
  // 観測できない。読めない実装では、初期状態（root, true）だけを出して step は
  // 比較から外す。
  const iteratorSpecs = scenario.iterators ?? [];
  let iterators = [];
  let iteratorsReadable = true;
  if (iteratorSpecs.length > 0) {
    iterators = buildIterators(objects, builder.documents, iteratorSpecs);
    iteratorsReadable = iterators.every((it) => "referenceNode" in it);
  }
  const iteratorSnapshot = () =>
    iteratorsReadable
      ? iterators.map((it) => ({
          root: idOf(it.root),
          reference: idOf(it.referenceNode),
          pointerBeforeReference: it.pointerBeforeReferenceNode,
          whatToShow: it.whatToShow
        }))
      : iteratorSpecs.map((spec) => ({
          root: spec.root, reference: spec.root,
          pointerBeforeReference: true, whatToShow: spec.whatToShow ?? SHOW_ALL
        }));

  const observerSpecs = scenario.observers ?? [];
  const observerCount = observerSpecs.length;
  const observerSet = observerCount > 0 ? new ObserverSet(win, idOf, observerSpecs) : null;
  if (observerSet) observerSet.registerInitial(objects, observerSpecs);
  const observerQueues = () => (observerSet ? observerSet.snapshot() : []);

  const invocationLog = [];
  const callbacks = buildListeners(objects, idOf, scenario.listeners, invocationLog);

  const ctx = { win, objects, kinds, idOf, ranges, walkers, iterators, callbacks,
    iteratorSnapshot, observerCount, observerQueues, observerSet };

  const initial = { ...snapshot(ctx), delivered: [] };
  if (anyLoneSurrogate(initial)) {
    throw new Error("初期状態に lone surrogate がある（JSON で渡せない）");
  }
  const steps = [];
  const blocked = iteratorSpecs.length > 0 && !iteratorsReadable
    ? "NodeIterator: referenceNode / pointerBeforeReferenceNode が無い"
    : null;

  for (const op of scenario.operations ?? []) {
    if (blocked) {
      steps.push({ ok: false, exception: UNSUPPORTED, reason: blocked });
      break;
    }
    invocationLog.length = 0;
    let returned;
    let step;
    try {
      returned = apply(ctx, op);
      if (observerSet) observerSet.drain();
      step = { ...snapshot(ctx), ok: true, delivered: [],
        invocations: [...invocationLog],
        returned: returnValueSnapshot(idOf, op, returned) };
    } catch (e) {
      if (e instanceof Unsupported) {
        steps.push({ ok: false, exception: UNSUPPORTED, reason: `Unsupported: ${e.message}` });
        break;
      }
      // 失敗した操作は状態を変えてはならない。比べられるように観測を出す。
      if (observerSet) observerSet.drain();
      step = { ...snapshot(ctx), ok: false, exception: exceptionName(e),
        delivered: [], invocations: [...invocationLog] };
    }
    if (anyLoneSurrogate(step)) {
      steps.push({ ok: false, exception: UNSUPPORTED,
        reason: "lone surrogate: JSON で渡せない" });
      break;
    }
    steps.push(step);
    if (!step.ok) break;
  }
  return { initial, steps };
}

/* ------------------------------------------------------------------ capabilities */

function capabilities(win) {
  const doc = makeDocumentFactory(win)();
  const builders = {
    document: () => doc,
    element: () => doc.createElement("div"),
    text: () => doc.createTextNode("x"),
    comment: () => doc.createComment("x"),
    processingInstruction: () => doc.createProcessingInstruction("pi", "x"),
    cdataSection: () => doc.createCDATASection("x"),
    documentFragment: () => doc.createDocumentFragment(),
    documentType: () => doc.implementation.createDocumentType("html", "", "")
  };
  const out = {};
  for (const [kind, make] of Object.entries(builders)) {
    let node;
    try {
      node = make();
    } catch {
      continue;
    }
    const ops = [];
    for (const [op, m] of Object.entries(OP_METHOD)) {
      if (op === "setData") {
        if ("data" in node) ops.push(op);
      } else if (typeof node[m] === "function") {
        ops.push(op);
      }
    }
    for (const q of QUERY_OPS) {
      const name = QUERY_JS_NAME[q];
      if (QUERY_GETTERS.includes(q) ? name in node : typeof node[name] === "function") {
        ops.push(q);
      }
    }
    out[kind] = ops;
  }
  return out;
}


globalThis.__domScenario = { run, capabilities, UNSUPPORTED };
