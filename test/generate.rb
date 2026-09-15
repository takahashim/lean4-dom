# frozen_string_literal: true

# scenario の乱数生成（PLAN §7.3）。
#
#   bundle exec ruby test/generate.rb [--seed N] [--nodes N] [--ops N] [--move]
#
# 生成方針
#   * node の個数を小さく保つ。
#   * insert / remove / replace / move / fragment insert を偏りなく混ぜる。
#   * 例外になる操作（自分自身の子孫への insert、存在しない child の指定など）は、
#     引数を無作為に選ぶことで自然に混ざる。
#
# 初期状態は WellFormed を満たすだけでなく、DOM の node tree 制約も満たす必要がある。
# Dommy 側は `appendChild` で木を組み立てるので、Document の子の制約
# （element は高々一つ、doctype は高々一つ、doctype が先）を破ると組み立てられない。

require "json"

module Generate
  # element の子になれる kind。
  CHILD_KINDS = %w[element text comment processingInstruction].freeze

  # `moveBefore` は Dommy が未実装なので、既定では生成しない。
  OPS = %w[appendChild insertBefore replaceChild removeChild replaceChildren
           before after replaceWith remove normalize
           rangeSetStart rangeSetEnd rangeSetStartBefore rangeSetStartAfter
           rangeSetEndBefore rangeSetEndAfter rangeCollapse rangeSelectNode
           rangeSelectNodeContents rangeIsPointInRange rangeIntersectsNode
           rangeCompareBoundaryPoints rangeComparePoint rangeDeleteContents
           rangeInsertNode rangeToString
           compareDocumentPosition nodeContains getRootNode isEqualNode
           getTextContent getNodeValue substringData
           getAttribute hasAttribute getAttributeNames
           lookupNamespaceURI lookupPrefix isDefaultNamespace
           dispatchEvent addEventListener removeEventListener
           walkerParentNode walkerFirstChild walkerLastChild
           walkerPreviousSibling walkerNextSibling walkerPreviousNode walkerNextNode
           replaceData appendData insertData deleteData setData
           setAttribute setAttributeNS removeAttribute removeAttributeNS
           toggleAttribute].freeze

  # 仕様上どの interface がどの操作を持つか。
  #   Node        すべての node
  #   ParentNode  Document / DocumentFragment / Element
  #   ChildNode   DocumentType / Element / CharacterData
  # event の操作。受け手は EventTarget（= どの node でもよい）。
  EVENT_OPS = %w[dispatchEvent addEventListener removeEventListener].freeze

  # 生成する event の type。少なくしておくと listener と当たりやすい。
  EVENT_TYPES = %w[a b].freeze

  NODE_OPS = %w[appendChild insertBefore replaceChild removeChild normalize
                compareDocumentPosition nodeContains getRootNode isEqualNode
                getTextContent getNodeValue
                dispatchEvent addEventListener removeEventListener
                lookupNamespaceURI lookupPrefix isDefaultNamespace
           dispatchEvent addEventListener removeEventListener].freeze
  PARENT_NODE_OPS = %w[replaceChildren moveBefore].freeze
  CHILD_NODE_OPS = %w[before after replaceWith remove].freeze
  CHARACTER_DATA_OPS = %w[replaceData appendData insertData deleteData setData
                          substringData].freeze
  ATTRIBUTE_OPS = %w[setAttribute setAttributeNS removeAttribute removeAttributeNS
                     toggleAttribute getAttribute hasAttribute getAttributeNames].freeze

  # attribute の local name は少ない候補から選ぶ。
  # そうしないと `attributeFilter` も「同じ鍵への二度目の書き込み」も当たらない。
  ATTR_NAMES = %w[a b data-x].freeze
  # 操作が渡す名前には大文字を混ぜる。HTML namespace の element が HTML document に
  # あるときだけ ASCII lowercase されるので、そこで挙動が分かれる。
  ATTR_OP_NAMES = (ATTR_NAMES + %w[A data-X]).freeze
  ATTR_VALUES = ["", "1", "vv"].freeze

  # element の local name。SVG namespace のものも混ぜて、
  # 「HTML namespace の element だけが attribute 名を lowercase する」分岐を撫でる。
  ELEMENT_NAMES = %w[div span p].freeze
  SVG_NS = "http://www.w3.org/2000/svg"

  def self.element_identity(rng)
    r = rng.rand
    if r < 0.75 then { "localName" => ELEMENT_NAMES.sample(random: rng) }
    elsif r < 0.9 then { "namespace" => SVG_NS, "localName" => "rect" }
    else { "namespace" => SVG_NS, "prefix" => "svg", "localName" => "rect" }
    end
  end

  # `setAttributeNS` に渡す namespace。null と XML namespace のほかに、
  # "validate and extract" の NamespaceError を踏ませるための組も混ぜる。
  XML_NS = "http://www.w3.org/XML/1998/namespace"
  XMLNS_NS = "http://www.w3.org/2000/xmlns/"
  ATTR_NAMESPACES = [nil, "http://example.com/ns", XML_NS, XMLNS_NS].freeze

  SPEC_OPS = {
    "document" => NODE_OPS + PARENT_NODE_OPS,
    "documentFragment" => NODE_OPS + PARENT_NODE_OPS,
    "element" => NODE_OPS + PARENT_NODE_OPS + CHILD_NODE_OPS + ATTRIBUTE_OPS,
    "text" => NODE_OPS + CHILD_NODE_OPS + CHARACTER_DATA_OPS,
    "comment" => NODE_OPS + CHILD_NODE_OPS + CHARACTER_DATA_OPS,
    "processingInstruction" => NODE_OPS + CHILD_NODE_OPS + CHARACTER_DATA_OPS,
    "cdataSection" => NODE_OPS + CHILD_NODE_OPS + CHARACTER_DATA_OPS,
    "documentType" => NODE_OPS + CHILD_NODE_OPS
  }.freeze

  # 仕様がその kind に定めている操作か。
  def self.spec_has?(kind, op)
    SPEC_OPS.fetch(kind, []).include?(op)
  end

  class Builder
    attr_reader :nodes

    def initialize(rng)
      @rng = rng
      @nodes = []
      @next_id = 0
    end

    def add(kind, parent: nil, data: "")
      id = @next_id
      @next_id += 1
      spec = { "id" => id, "kind" => kind }
      spec["parent"] = parent unless parent.nil?
      spec["data"] = data unless data.empty?
      @nodes << spec
      id
    end

    # 子を持てる node（element と documentFragment）の id。
    def containers
      @nodes.select { |n| %w[element documentFragment].include?(n["kind"]) }.map { |n| n["id"] }
    end

    def ids
      @nodes.map { |n| n["id"] }
    end
  end

  module_function

  # CharacterData だけが data を持つ。
  CHARACTER_DATA = %w[text comment processingInstruction cdataSection].freeze

  # CharacterData の初期 data。
  #
  # 1/4 は astral character（surrogate pair）を混ぜる。仕様の offset は UTF-16 の
  # code unit なので、pair をまたぐ offset と pair の途中を指す offset の両方が出る。
  # 後者で切ろうとする操作は model の対象外になり、比較から外れる。
  ASTRAL = "\u{1F600}"

  def data_for(kind, tag, rng = nil)
    return "" unless CHARACTER_DATA.include?(kind)
    return tag if rng.nil? || rng.rand >= 0.25

    ["#{ASTRAL}#{tag}", "#{tag}#{ASTRAL}", "#{tag[0]}#{ASTRAL}#{tag[-1]}"].sample(random: rng)
  end

  # element が最初から持っている attribute。
  #
  # 鍵の一意性は `AttributesValid` が要求するので、local name を重複させない。
  # prefix を付ける場合は namespace も付ける（同じく `AttributesValid`）。
  def initial_attributes(rng)
    return [] if rng.rand < 0.6

    ATTR_NAMES.sample(1 + rng.rand(2), random: rng).map do |name|
      if rng.rand < 0.25
        { "namespace" => XML_NS, "prefix" => "xml", "localName" => name,
          "value" => ATTR_VALUES.sample(random: rng) }
      else
        { "namespace" => nil, "prefix" => nil, "localName" => name,
          "value" => ATTR_VALUES.sample(random: rng) }
      end
    end
  end

  def build_tree(rng, node_count, doctype_prob: 0.0)
    b = Builder.new(rng)
    doc = b.add("document")
    b.add("documentType", parent: doc) if rng.rand < doctype_prob
    root = (b.add("element", parent: doc) if rng.rand < 0.9)
    # 木から切り離された DocumentFragment と、その子。
    frag = b.add("documentFragment")
    rng.rand(3).times do
      kind = CHILD_KINDS.sample(random: rng)
      b.add(kind, parent: frag, data: data_for(kind, "f", rng))
    end

    remaining = [node_count - b.nodes.size, 0].max
    remaining.times do
      kind = CHILD_KINDS.sample(random: rng)
      # 1/4 は切り離された node にする。
      parent =
        if rng.rand < 0.25
          nil
        else
          candidates = b.containers - [frag]
          candidates = [root].compact if candidates.empty?
          candidates.empty? ? nil : candidates.sample(random: rng)
        end
      b.add(kind, parent: parent, data: data_for(kind, "t#{b.ids.size}", rng))
    end
    b.nodes.each do |spec|
      next unless spec["kind"] == "element"

      spec.merge!(element_identity(rng))
      spec["attributes"] = initial_attributes(rng)
    end
    b.nodes
  end

  def random_operation(rng, ids, ops, iterator_count = 0, observer_count = 0, range_count = 0,
                       walker_count = 0, listener_count = 0)
    op = ops.sample(random: rng)
    if ITERATOR_OPS.include?(op)
      return nil if iterator_count.zero?

      return { "op" => op, "iterator" => rng.rand(iterator_count) }
    end
    if OBSERVER_OPS.include?(op)
      return { "op" => "notify" } if op == "notify"
      return nil if observer_count.zero?

      mo = rng.rand(observer_count)
      return { "op" => op, "observer" => mo } unless op == "observe"

      # `observe` の options は `random_observed_types` が作る。
      return { "op" => op, "observer" => mo, "target" => ids.sample(random: rng),
               "subtree" => rng.rand < 0.6 }.merge(random_observed_types(rng))
    end
    if RANGE_OPS.include?(op)
      return nil if range_count.zero?

      r = rng.rand(range_count)
      # `Range` の `Node` 引数は WebIDL で non-nullable である。null は step に入る前の
      # 引数変換で TypeError になるので、順序（`setStart(null, 大きい offset)` が
      # IndexSizeError にならないこと）を撫でるために、たまに null を混ぜる。
      node = rng.rand < 0.06 ? nil : ids.sample(random: rng)
      # 大きい offset も混ぜる。null と合わせると変換が先だと分かる。
      offset = -> { rng.rand < 0.1 ? 99 : rng.rand(4) }
      return case op
             when "rangeSetStart", "rangeSetEnd", "rangeIsPointInRange"
               { "op" => op, "range" => r, "node" => node, "offset" => offset.call }
             when "rangeCollapse" then { "op" => op, "range" => r, "toStart" => rng.rand < 0.5 }
             when "rangeDeleteContents", "rangeToString" then { "op" => op, "range" => r }
             when "rangeComparePoint"
               { "op" => op, "range" => r, "node" => node, "offset" => offset.call }
             when "rangeCompareBoundaryPoints"
               # `how` は 0-3 のほかに範囲外も混ぜて NotSupportedError を撫でる。
               { "op" => op, "range" => r, "how" => rng.rand(5), "source" => rng.rand(range_count) }
             else { "op" => op, "range" => r, "node" => node }
             end
    end
    if WALKER_OPS.include?(op)
      return nil if walker_count.zero?

      return { "op" => op, "walker" => rng.rand(walker_count) }
    end
    pick = -> { ids.sample(random: rng) }
    # 存在しない id をたまに混ぜて notFoundError を誘う。
    #
    # ただし Dommy 側には「存在しない node」を渡しようが無いので、
    # その step 以降は差分比較できない（runner は `__unsupported__` を返す）。
    # model 側の `get? = none` の分岐を撫でる価値はあるが、
    # 比率を上げると差分テストの予算を食うだけなので低く抑える。
    maybe = -> { rng.rand < 0.05 ? ids.max + 1 + rng.rand(3) : pick.call }
    case op
    when "appendChild" then { "op" => op, "parent" => pick.call, "node" => maybe.call }
    when "insertBefore"
      { "op" => op, "parent" => pick.call, "node" => maybe.call,
        "child" => rng.rand < 0.5 ? nil : maybe.call }
    when "replaceChild"
      { "op" => op, "parent" => pick.call, "node" => maybe.call, "child" => maybe.call }
    when "removeChild" then { "op" => op, "parent" => pick.call, "node" => maybe.call }
    when "replaceChildren"
      { "op" => op, "parent" => pick.call, "node" => rng.rand < 0.3 ? nil : maybe.call }
    when "before", "after", "replaceWith"
      { "op" => op, "target" => pick.call, "node" => maybe.call }
    when "remove" then { "op" => op, "target" => pick.call }
    when "normalize" then { "op" => op, "target" => pick.call }
    when "compareDocumentPosition", "nodeContains", "isEqualNode"
      { "op" => op, "node" => pick.call, "other" => pick.call }
    when "getRootNode", "getTextContent", "getNodeValue" then { "op" => op, "node" => pick.call }
    when "substringData"
      { "op" => op, "node" => pick.call, "offset" => rng.rand(5), "count" => rng.rand(4) }
    when "getAttribute", "hasAttribute"
      { "op" => op, "element" => pick.call, "name" => ATTR_OP_NAMES.sample(random: rng) }
    when "getAttributeNames" then { "op" => op, "element" => pick.call }
    when "dispatchEvent"
      { "op" => op, "target" => pick.call, "type" => EVENT_TYPES.sample(random: rng),
        "bubbles" => rng.rand < 0.6, "cancelable" => rng.rand < 0.5 }
    when "addEventListener"
      return nil if listener_count.zero?

      { "op" => op, "target" => pick.call, "type" => EVENT_TYPES.sample(random: rng),
        "source" => rng.rand(listener_count), "capture" => rng.rand < 0.4,
        "once" => rng.rand < 0.3 }
    when "removeEventListener"
      return nil if listener_count.zero?

      { "op" => op, "target" => pick.call, "type" => EVENT_TYPES.sample(random: rng),
        "callback" => rng.rand(listener_count), "capture" => rng.rand < 0.4 }
    when "lookupNamespaceURI"
      { "op" => op, "node" => pick.call,
        "prefix" => [nil, "", "p", "xml", "xmlns", "q"].sample(random: rng) }
    when "lookupPrefix", "isDefaultNamespace"
      { "op" => op, "node" => pick.call,
        "namespace" => [nil, "", "urn:x", "urn:y", ATTR_NAMESPACES.compact.sample(random: rng),
                        "http://www.w3.org/1999/xhtml"].sample(random: rng) }
    when "replaceData"
      { "op" => op, "node" => pick.call, "offset" => rng.rand(5), "count" => rng.rand(4),
        "data" => ["x", "yz", "abc", ASTRAL][rng.rand(4)] }
    when "appendData"
      { "op" => op, "node" => pick.call, "data" => ["x", "yz", ASTRAL][rng.rand(3)] }
    when "insertData"
      { "op" => op, "node" => pick.call, "offset" => rng.rand(5),
        "data" => ["x", "yz", ASTRAL][rng.rand(3)] }
    when "deleteData"
      { "op" => op, "node" => pick.call, "offset" => rng.rand(5), "count" => rng.rand(4) }
    when "setData"
      { "op" => op, "node" => pick.call,
        "data" => ["", "pq", "rstu", ASTRAL, "p#{ASTRAL}q"][rng.rand(5)] }
    when "setAttribute"
      { "op" => op, "element" => pick.call, "name" => ATTR_OP_NAMES.sample(random: rng),
        "value" => ATTR_VALUES.sample(random: rng) }
    when "setAttributeNS"
      ns, qn = random_ns_and_qualified_name(rng)
      { "op" => op, "element" => pick.call, "namespace" => ns, "name" => qn,
        "value" => ATTR_VALUES.sample(random: rng) }
    when "removeAttribute"
      { "op" => op, "element" => pick.call, "name" => ATTR_OP_NAMES.sample(random: rng) }
    when "removeAttributeNS"
      { "op" => op, "element" => pick.call,
        "namespace" => ATTR_NAMESPACES.sample(random: rng),
        "name" => ATTR_NAMES.sample(random: rng) }
    when "toggleAttribute"
      { "op" => op, "element" => pick.call, "name" => ATTR_OP_NAMES.sample(random: rng),
        "force" => [nil, true, false].sample(random: rng) }
    when "moveBefore"
      { "op" => op, "parent" => pick.call, "node" => maybe.call,
        "child" => rng.rand < 0.5 ? nil : maybe.call }
    end
  end

  # `setAttributeNS` の (namespace, qualifiedName)。
  #
  # prefix 付きの qualified name を半分ほど混ぜて、"validate and extract" の
  # step 8-11（prefix に namespace が要る、`xml` と `xmlns` の対応）を撫でる。
  def random_ns_and_qualified_name(rng)
    ns = ATTR_NAMESPACES.sample(random: rng)
    local = ATTR_NAMES.sample(random: rng)
    return [ns, local] if rng.rand < 0.5

    [ns, "#{%w[p xml xmlns].sample(random: rng)}:#{local}"]
  end

  # 受け手（method を呼ぶ相手）の id。§4.4 の query は `node` を受け手に取る。
  NODE_RECEIVER_OPS = %w[compareDocumentPosition nodeContains getRootNode isEqualNode
                         getTextContent getNodeValue
                         lookupNamespaceURI lookupPrefix isDefaultNamespace].freeze

  def receiver_id(op)
    return op["node"] if CHARACTER_DATA_OPS.include?(op["op"])
    return op["node"] if NODE_RECEIVER_OPS.include?(op["op"])
    return op["element"] if ATTRIBUTE_OPS.include?(op["op"])

    op.key?("target") ? op["target"] : op["parent"]
  end

  # scenario の node から length を求める（`NodeData.length` と同じ規則）。
  # UTF-16 の code unit 数。仕様の `CharacterData.length` と `NodeData.length` はこれ。
  def utf16_length(str)
    str.to_s.encode(Encoding::UTF_16LE).bytesize / 2
  end

  def length_of(spec, nodes)
    kind = spec["kind"]
    return utf16_length(spec["data"]) if CHARACTER_DATA.include?(kind)
    return 0 if kind == "documentType"

    nodes.count { |n| n["parent"] == spec["id"] }
  end

  # boundary point になれない kind。仕様 §5.5 の `setStart` / `setEnd` は
  # doctype を InvalidNodeTypeError で弾く。
  NON_BOUNDARY_KINDS = %w[documentType].freeze

  def boundary_candidates(nodes)
    nodes.reject { |n| NON_BOUNDARY_KINDS.include?(n["kind"]) }
  end

  # `nodes` を id 引きの hash にする。経路をたどる補助。
  def index_by_id(nodes)
    nodes.to_h { |n| [n["id"], n] }
  end

  def parent_of(by_id, id)
    by_id[id] && by_id[id]["parent"]
  end

  # `id` の root。scenario の木は有限で循環が無いので単純にたどれる。
  def root_of(by_id, id)
    cur = id
    cur = parent_of(by_id, cur) while parent_of(by_id, cur)
    cur
  end

  # parent の children における `id` の位置。
  def child_index(nodes, by_id, id)
    p = parent_of(by_id, id)
    return nil if p.nil?

    nodes.select { |n| n["parent"] == p }.index { |n| n["id"] == id }
  end

  # boundary point の key（`Dom/Properties/Path.lean` の `bpKey`）。
  # root からの各段の index の列に offset を付けたもの。
  # 仕様 §5.3 の boundary point position は、この列の辞書式比較に一致する
  # （`bpPosition_eq_lexCmp`）ので、start ≤ end はこれで判定できる。
  def bp_key(nodes, by_id, id, offset)
    path = []
    cur = id
    while parent_of(by_id, cur)
      path.unshift(child_index(nodes, by_id, cur))
      cur = parent_of(by_id, cur)
    end
    path << offset
  end

  # 辞書式比較。短いほうが prefix なら短いほうが小さい。
  def lex_compare(a, b)
    a.each_with_index do |x, i|
      return 1 if i >= b.size

      c = x <=> b[i]
      return c unless c.zero?
    end
    a.size == b.size ? 0 : -1
  end

  # range を一つ作る。
  #
  # 3 回に 1 回は両端を同じ node に置き（従来と同じ形）、
  # 残りは同じ root にある別々の node に置いて、key の辞書式順で start / end を決める。
  # 別 node の range は tree order と `childTowards` を通るので、
  # mutation の後の boundary point position を突き合わせられる。
  def random_range(rng, nodes, by_id, candidates)
    a = candidates.sample(random: rng)
    same_node = rng.rand < 0.34
    b =
      if same_node
        a
      else
        root = root_of(by_id, a["id"])
        pool = candidates.select { |n| root_of(by_id, n["id"]) == root }
        pool.sample(random: rng) || a
      end

    if a["id"] == b["id"]
      len = length_of(a, nodes)
      s = rng.rand(len + 1)
      e = s + rng.rand(len - s + 1)
      return { "start" => { "node" => a["id"], "offset" => s },
               "end" => { "node" => a["id"], "offset" => e } }
    end

    ao = rng.rand(length_of(a, nodes) + 1)
    bo = rng.rand(length_of(b, nodes) + 1)
    first = { "node" => a["id"], "offset" => ao }
    second = { "node" => b["id"], "offset" => bo }
    ka = bp_key(nodes, by_id, a["id"], ao)
    kb = bp_key(nodes, by_id, b["id"], bo)
    first, second = second, first if lex_compare(ka, kb).positive?
    { "start" => first, "end" => second }
  end

  def random_ranges(rng, nodes, count)
    candidates = boundary_candidates(nodes)
    return [] if candidates.empty?

    by_id = index_by_id(nodes)
    Array.new(count) { random_range(rng, nodes, by_id, candidates) }
  end

  # iterator を動かす操作。受け手が node ではないので kind の絞り込みは要らない。
  ITERATOR_OPS = %w[iteratorNext iteratorPrevious].freeze

  # range を動かす操作。受け手は range なので、node は引数として渡す。
  RANGE_OPS = %w[rangeSetStart rangeSetEnd rangeSetStartBefore rangeSetStartAfter
                 rangeSetEndBefore rangeSetEndAfter rangeCollapse rangeSelectNode
                 rangeSelectNodeContents rangeIsPointInRange rangeIntersectsNode
                 rangeCompareBoundaryPoints rangeComparePoint rangeDeleteContents
                 rangeInsertNode rangeToString].freeze

  # TreeWalker を動かす操作。受け手は walker なので、node は引数に取らない。
  WALKER_OPS = %w[walkerParentNode walkerFirstChild walkerLastChild
                  walkerPreviousSibling walkerNextSibling
                  walkerPreviousNode walkerNextNode].freeze

  # MutationObserver の操作。`notify` は microtask checkpoint である。
  # `observe` だけは受け手が node（target）なので、kind の絞り込みを通す。
  OBSERVER_OPS = %w[observe disconnect takeRecords notify].freeze

  # 仕様の `createNodeIterator` は reference を (root, true) に初期化する。
  # Dommy に setter が無いので、生成する iterator もこの状態から始める。
  # NodeFilter の定数。`whatToShow` は nodeType − 1 の bit を見る bitmask である。
  SHOW_ALL = 0xFFFFFFFF
  SHOW_ELEMENT = 0x1
  SHOW_TEXT = 0x4
  SHOW_COMMENT = 0x80
  SHOW_DOCUMENT = 0x100

  # event listener を宣言する。
  #
  # callback の副作用は scenario が決める（model には callback が無い）。
  # `removeListener` と `addListener` は他の宣言を指すので、index が範囲に入るように作る。
  def random_listeners(rng, nodes, count)
    return [] if count.zero? || nodes.empty?

    Array.new(count) do |i|
      spec = nodes.sample(random: rng)
      listener = { "target" => spec["id"], "type" => EVENT_TYPES.sample(random: rng),
                   "capture" => rng.rand < 0.4, "once" => rng.rand < 0.25 }
      action =
        case rng.rand(10)
        when 0 then "stopPropagation"
        when 1 then "stopImmediatePropagation"
        when 2 then "preventDefault"
        when 3 then { "kind" => "removeListener", "index" => rng.rand(count) }
        when 4
          { "kind" => "addListener", "target" => nodes.sample(random: rng)["id"],
            "type" => EVENT_TYPES.sample(random: rng), "source" => rng.rand(count),
            "capture" => rng.rand < 0.4 }
        end
      action ? listener.merge("action" => action) : listener
    end
  end

  # TreeWalker を作る。current は `createTreeWalker` と同じく root から始める。
  def random_walkers(rng, nodes, count)
    return [] if count.zero? || nodes.empty?

    Array.new(count) do
      spec = nodes.sample(random: rng)
      what =
        if rng.rand < 0.5
          SHOW_ALL
        else
          [SHOW_ELEMENT, SHOW_TEXT, SHOW_ELEMENT | SHOW_TEXT,
           SHOW_COMMENT, SHOW_ELEMENT | SHOW_COMMENT | SHOW_DOCUMENT].sample(random: rng)
        end
      { "root" => spec["id"], "whatToShow" => what }
    end
  end

  def random_iterators(rng, nodes, count)
    Array.new(count) do
      spec = nodes.sample(random: rng)
      # 半分は SHOW_ALL。残りは一部の node type だけを通す組にして、
      # traverse が accept するまで繰り返す分岐を撫でる。
      what =
        if rng.rand < 0.5
          SHOW_ALL
        else
          [SHOW_ELEMENT, SHOW_TEXT, SHOW_ELEMENT | SHOW_TEXT,
           SHOW_COMMENT, SHOW_ELEMENT | SHOW_COMMENT | SHOW_DOCUMENT].sample(random: rng)
        end
      { "root" => spec["id"], "reference" => spec["id"], "pointerBeforeReference" => true,
        "whatToShow" => what }
    end
  end

  # MutationObserver を作る。
  #
  # 一つの observer が一つの node を観測する形だけを作る（`observe` を一度呼んだ状態）。
  # 仕様の `observe` は childList / attributes / characterData が
  # どれも true でなければ TypeError を投げるので、少なくとも一つは立てる。
  def random_observers(rng, nodes, count)
    return [] if count.zero? || nodes.empty?

    Array.new(count) do
      spec = nodes.sample(random: rng)
      { "target" => spec["id"], "subtree" => rng.rand < 0.6 }.merge(random_observed_types(rng))
    end
  end

  # 観測する record 種別の組。少なくとも一つは true になる。
  #
  # `attributeFilter` は「存在するだけで」絞り込みになるので、
  # 空 list と非空 list の両方を混ぜる。
  def random_observed_types(rng)
    child_list = rng.rand < 0.6
    attributes = rng.rand < 0.6
    character_data = child_list || attributes ? rng.rand < 0.5 : true
    out = { "childList" => child_list,
            "attributes" => attributes,
            "attributeOldValue" => attributes && rng.rand < 0.7,
            "characterData" => character_data,
            "characterDataOldValue" => character_data && rng.rand < 0.7 }
    if attributes && rng.rand < 0.4
      out["attributeFilter"] = ATTR_NAMES.sample(rng.rand(ATTR_NAMES.size + 1), random: rng)
    end
    out
  end

  # `allow` は `(op, receiver_kind) -> Boolean`。
  # Dommy が実装していない (kind, op) の組を避けたいときに渡す。
  def scenario(rng, node_count: 8, op_count: 8, ops: OPS, allow: nil, doctype_prob: 0.0,
               range_count: 2, iterator_count: 1, observer_count: 0, walker_count: 0,
               listener_count: 0)
    nodes = build_tree(rng, node_count, doctype_prob: doctype_prob)
    ids = nodes.map { |n| n["id"] }
    kinds = nodes.to_h { |n| [n["id"], n["kind"]] }
    operations = []
    attempts = 0
    while operations.size < op_count && attempts < op_count * 100
      attempts += 1
      op = random_operation(rng, ids, ops, iterator_count, observer_count, range_count,
                            walker_count, listener_count)
      next if op.nil?
      if EVENT_OPS.include?(op["op"])
        # 受け手は EventTarget なので kind の絞り込みは要らない。
        operations << op
        next
      end
      if WALKER_OPS.include?(op["op"])
        # 受け手は walker なので kind の絞り込みは要らない。
        operations << op
        next
      end
      if RANGE_OPS.include?(op["op"])
        # 受け手は range なので kind の絞り込みは要らない。
        operations << op
        next
      end
      if ITERATOR_OPS.include?(op["op"]) || %w[disconnect takeRecords notify].include?(op["op"])
        operations << op
        next
      end
      if op["op"] == "observe"
        # `observe` の receiver は MutationObserver なので kind の絞り込みは無い。
        operations << op
        next
      end
      kind = kinds[receiver_id(op)]
      # 仕様がその kind に定めていない操作は生成しない。
      next if kind.nil? || !spec_has?(kind, op["op"])
      next if allow && !allow.call(op, kind)

      operations << op
    end
    { "nodes" => nodes, "ranges" => random_ranges(rng, nodes, range_count),
      "iterators" => random_iterators(rng, nodes, iterator_count),
      "walkers" => random_walkers(rng, nodes, walker_count),
      "listeners" => random_listeners(rng, nodes, listener_count),
      "observers" => random_observers(rng, nodes, observer_count),
      "operations" => operations }
  end
end

if $PROGRAM_NAME == __FILE__
  require "optparse"
  opts = { seed: Random.new_seed, nodes: 8, ops: 8, move: false, doctype: 0.0,
           ranges: 2, iterators: 1, observers: 0, walkers: 1, listeners: 0 }
  OptionParser.new do |o|
    o.on("--seed N", Integer) { |v| opts[:seed] = v }
    o.on("--nodes N", Integer) { |v| opts[:nodes] = v }
    o.on("--ops N", Integer) { |v| opts[:ops] = v }
    o.on("--move") { opts[:move] = true }
    o.on("--doctype-prob F", Float) { |v| opts[:doctype] = v }
    o.on("--ranges N", Integer) { |v| opts[:ranges] = v }
    o.on("--iterators N", Integer) { |v| opts[:iterators] = v }
    o.on("--observers N", Integer) { |v| opts[:observers] = v }
    o.on("--walkers N", Integer) { |v| opts[:walkers] = v }
    o.on("--listeners N", Integer) { |v| opts[:listeners] = v }
  end.parse!
  ops = opts[:move] ? Generate::OPS + ["moveBefore"] : Generate::OPS
  rng = Random.new(opts[:seed])
  puts JSON.pretty_generate(
    Generate.scenario(rng, node_count: opts[:nodes], op_count: opts[:ops], ops: ops,
                           doctype_prob: opts[:doctype], range_count: opts[:ranges],
                           iterator_count: opts[:iterators], observer_count: opts[:observers],
                           walker_count: opts[:walkers], listener_count: opts[:listeners])
  )
end
