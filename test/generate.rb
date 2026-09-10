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
           before after replaceWith remove
           replaceData appendData insertData deleteData setData].freeze

  # 仕様上どの interface がどの操作を持つか。
  #   Node        すべての node
  #   ParentNode  Document / DocumentFragment / Element
  #   ChildNode   DocumentType / Element / CharacterData
  NODE_OPS = %w[appendChild insertBefore replaceChild removeChild].freeze
  PARENT_NODE_OPS = %w[replaceChildren moveBefore].freeze
  CHILD_NODE_OPS = %w[before after replaceWith remove].freeze
  CHARACTER_DATA_OPS = %w[replaceData appendData insertData deleteData setData].freeze

  SPEC_OPS = {
    "document" => NODE_OPS + PARENT_NODE_OPS,
    "documentFragment" => NODE_OPS + PARENT_NODE_OPS,
    "element" => NODE_OPS + PARENT_NODE_OPS + CHILD_NODE_OPS,
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

  def data_for(kind, tag)
    CHARACTER_DATA.include?(kind) ? tag : ""
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
      b.add(kind, parent: frag, data: data_for(kind, "f"))
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
      b.add(kind, parent: parent, data: data_for(kind, "t#{b.ids.size}"))
    end
    b.nodes
  end

  def random_operation(rng, ids, ops, iterator_count = 0)
    op = ops.sample(random: rng)
    if ITERATOR_OPS.include?(op)
      return nil if iterator_count.zero?

      return { "op" => op, "iterator" => rng.rand(iterator_count) }
    end
    pick = -> { ids.sample(random: rng) }
    # 存在しない id をたまに混ぜて notFoundError を誘う。
    maybe = -> { rng.rand < 0.15 ? ids.max + 1 + rng.rand(3) : pick.call }
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
    when "replaceData"
      { "op" => op, "node" => pick.call, "offset" => rng.rand(5), "count" => rng.rand(4),
        "data" => %w[x yz abc][rng.rand(3)] }
    when "appendData" then { "op" => op, "node" => pick.call, "data" => %w[x yz][rng.rand(2)] }
    when "insertData"
      { "op" => op, "node" => pick.call, "offset" => rng.rand(5), "data" => %w[x yz][rng.rand(2)] }
    when "deleteData"
      { "op" => op, "node" => pick.call, "offset" => rng.rand(5), "count" => rng.rand(4) }
    when "setData" then { "op" => op, "node" => pick.call, "data" => %w[[] pq rstu][rng.rand(3)] }
    when "moveBefore"
      { "op" => op, "parent" => pick.call, "node" => maybe.call,
        "child" => rng.rand < 0.5 ? nil : maybe.call }
    end
  end

  # 操作の受け手（method を呼ぶ相手）の id。
  def receiver_id(op)
    return op["node"] if CHARACTER_DATA_OPS.include?(op["op"])

    op.key?("target") ? op["target"] : op["parent"]
  end

  # scenario の node から length を求める（`NodeData.length` と同じ規則）。
  def length_of(spec, nodes)
    kind = spec["kind"]
    return spec["data"].to_s.length if CHARACTER_DATA.include?(kind)
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

  # 仕様の `createNodeIterator` は reference を (root, true) に初期化する。
  # Dommy に setter が無いので、生成する iterator もこの状態から始める。
  def random_iterators(rng, nodes, count)
    Array.new(count) do
      spec = nodes.sample(random: rng)
      { "root" => spec["id"], "reference" => spec["id"], "pointerBeforeReference" => true }
    end
  end

  # MutationObserver を作る。
  #
  # 一つの observer が一つの node を観測する形だけを作る（`observe` を一度呼んだ状態）。
  # 仕様の `observe` は childList / attributes / characterData が
  # どれも true でなければ TypeError を投げるので、少なくとも一方は立てる。
  # model は attribute を扱わないので、選べるのは childList と characterData である。
  def random_observers(rng, nodes, count)
    return [] if count.zero? || nodes.empty?

    Array.new(count) do
      spec = nodes.sample(random: rng)
      child_list = rng.rand < 0.7
      character_data = child_list ? rng.rand < 0.6 : true
      { "target" => spec["id"],
        "subtree" => rng.rand < 0.6,
        "childList" => child_list,
        "characterData" => character_data,
        "characterDataOldValue" => character_data && rng.rand < 0.7 }
    end
  end

  # `allow` は `(op, receiver_kind) -> Boolean`。
  # Dommy が実装していない (kind, op) の組を避けたいときに渡す。
  def scenario(rng, node_count: 8, op_count: 8, ops: OPS, allow: nil, doctype_prob: 0.0,
               range_count: 2, iterator_count: 1, observer_count: 0)
    nodes = build_tree(rng, node_count, doctype_prob: doctype_prob)
    ids = nodes.map { |n| n["id"] }
    kinds = nodes.to_h { |n| [n["id"], n["kind"]] }
    operations = []
    attempts = 0
    while operations.size < op_count && attempts < op_count * 100
      attempts += 1
      op = random_operation(rng, ids, ops, iterator_count)
      next if op.nil?
      if ITERATOR_OPS.include?(op["op"])
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
      "observers" => random_observers(rng, nodes, observer_count),
      "operations" => operations }
  end
end

if $PROGRAM_NAME == __FILE__
  require "optparse"
  opts = { seed: Random.new_seed, nodes: 8, ops: 8, move: false, doctype: 0.0,
           ranges: 2, iterators: 1, observers: 0 }
  OptionParser.new do |o|
    o.on("--seed N", Integer) { |v| opts[:seed] = v }
    o.on("--nodes N", Integer) { |v| opts[:nodes] = v }
    o.on("--ops N", Integer) { |v| opts[:ops] = v }
    o.on("--move") { opts[:move] = true }
    o.on("--doctype-prob F", Float) { |v| opts[:doctype] = v }
    o.on("--ranges N", Integer) { |v| opts[:ranges] = v }
    o.on("--iterators N", Integer) { |v| opts[:iterators] = v }
    o.on("--observers N", Integer) { |v| opts[:observers] = v }
  end.parse!
  ops = opts[:move] ? Generate::OPS + ["moveBefore"] : Generate::OPS
  rng = Random.new(opts[:seed])
  puts JSON.pretty_generate(
    Generate.scenario(rng, node_count: opts[:nodes], op_count: opts[:ops], ops: ops,
                           doctype_prob: opts[:doctype], range_count: opts[:ranges],
                           iterator_count: opts[:iterators], observer_count: opts[:observers])
  )
end
