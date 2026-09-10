# frozen_string_literal: true

# Dommy 側の scenario runner。
#
# lean4-dom の `lake exe dom-model SCENARIO.json` と同じ形式の JSON を標準出力に書く。
# 比較は test/compare.rb が行う。
#
#   bundle exec ruby test/dommy_runner.rb SCENARIO.json
#
# Dommy が未実装の操作（受け手の class に method が無い場合）は
# `{"ok": false, "exception": "__unsupported__"}` として報告し、
# 仕様上の例外との不一致と区別できるようにする。

require "json"
require "dommy"

module DommyRunner
  UNSUPPORTED = "__unsupported__"

  # 各操作が呼び出す Dommy の method 名。capability 判定にも使う。
  OP_METHOD = {
    "appendChild" => :append_child,
    "insertBefore" => :insert_before,
    "replaceChild" => :replace_child,
    "removeChild" => :remove_child,
    "replaceChildren" => :replace_children,
    "before" => :before,
    "after" => :after,
    "replaceWith" => :replace_with,
    "remove" => :remove,
    "moveBefore" => :move_before,
    "replaceData" => :replace_data,
    "appendData" => :append_data,
    "insertData" => :insert_data,
    "deleteData" => :delete_data,
    "setData" => :data=
  }.freeze

  # 受け手が `node` である操作（CharacterData の method）。
  CHARACTER_DATA_OPS = %w[replaceData appendData insertData deleteData setData].freeze

  # scenario の kind から Dommy の node を作る。
  class Builder
    def initialize(specs)
      @specs = specs
      @objects = {}
      @documents = {}
    end

    # scenario の document node に対応する、空の Document を作る。
    #
    # `Window` 経由で作るのは `MutationObserver` が window を要るためである。
    # 生まれたときは doctype と <html> を持っているので、子を外して空にしてから使う。
    # `implementation.create_document(nil, nil, nil)` なら最初から空だが、
    # そちらは XML document になり `documentFragment.appendChild` が
    # `Makiri::Error` になるため使えない。
    def new_empty_document
      win = Dommy::Window.new
      doc = win.document
      doc.child_nodes.to_a.each { |n| n.remove if n.respond_to?(:remove) }
      doc
    end

    attr_reader :documents

    def build
      default_doc_id = @specs.find { |s| s["kind"] == "document" }&.fetch("id")
      @specs.each { |s| create(s, default_doc_id) }
      # children の順序は nodes 配列の並び順で決まる。
      @specs.each do |s|
        parent_id = s["parent"]
        next if parent_id.nil?

        parent = @objects[parent_id]
        unless parent.respond_to?(:append_child)
          raise "node #{parent_id} (#{kind_of_id(parent_id)}) に append_child が無い"
        end

        parent.append_child(@objects[s["id"]])
      end
      @objects
    end

    private

    def kind_of_id(id)
      @specs.find { |s| s["id"] == id }&.fetch("kind")
    end

    def owner_document(spec, default_doc_id)
      id = spec["ownerDocument"] || (spec["kind"] == "document" ? spec["id"] : default_doc_id)
      @documents[id] or raise "node #{spec['id']}: ownerDocument #{id.inspect} が document ではない"
    end

    def create(spec, default_doc_id)
      id = spec["id"]
      data = spec["data"].to_s
      if spec["kind"] == "document"
        doc = new_empty_document
        @documents[id] = doc
        @objects[id] = doc
        return
      end

      doc = owner_document(spec, default_doc_id)
      @objects[id] =
        case spec["kind"]
        when "element" then doc.create_element("div")
        when "text" then doc.create_text_node(data)
        when "comment" then doc.create_comment(data)
        when "processingInstruction" then doc.create_processing_instruction("pi", data)
        when "cdataSection" then doc.create_cdata_section(data)
        when "documentFragment" then doc.create_document_fragment
        when "documentType" then doc.implementation.create_document_type("html", "", "")
        else raise "未知の kind #{spec['kind'].inspect}"
        end
    end
  end

  module_function

  # Dommy の例外から仕様上の名前を取り出す。
  def exception_name(error)
    if error.respond_to?(:name) && error.name.is_a?(String) && !error.name.empty?
      error.name
    else
      error.class.name.split("::").last
    end
  end

  # scenario の id へ引き直す。
  # Dommy が別の wrapper object を返して同定できない場合は "?" を返す。
  # `nil`（parent が無い）と区別できるようにするためで、
  # DOM では node の同一性は観測可能なので、これ自体が不一致として報告される。
  UNKNOWN_NODE = "?"

  def node_id(objects, node)
    return nil if node.nil?

    objects.each { |id, obj| return id if obj.equal?(node) }
    objects.each { |id, obj| return id if obj == node }
    UNKNOWN_NODE
  end

  # Dommy は class によって `parent_node` / `child_nodes` を持たないことがある。
  # 木の意味としては「parent は無い」「children は空」なので、そう読み替える。
  def parent_of(node)
    node.respond_to?(:parent_node) ? node.parent_node : nil
  end

  def children_of(node)
    node.respond_to?(:child_nodes) ? node.child_nodes.to_a : []
  end

  def data_of(node)
    node.respond_to?(:data) ? node.data.to_s : ""
  rescue StandardError
    ""
  end

  # scenario の iterator を Dommy の NodeIterator として作る。
  #
  # 仕様の `createNodeIterator` は reference を (root, true) に初期化する。
  # Dommy には reference の setter が無いので、
  # scenario 側もこの初期状態から始めることを求める。
  def build_iterators(objects, documents, specs)
    (specs || []).map do |spec|
      unless spec["reference"] == spec["root"] && spec["pointerBeforeReference"] != false
        raise "iterator の初期状態は (root, true) でなければならない: #{spec.inspect}"
      end

      doc = documents.values.first or raise "document が無いので NodeIterator を作れない"
      doc.create_node_iterator(objects.fetch(spec["root"]))
    end
  end

  # Dommy は referenceNode / pointerBeforeReferenceNode を Ruby の method として
  # 公開しておらず、JS bridge 経由でしか読めない。
  def iterator_attr(it, name)
    snake = name.gsub(/([A-Z])/) { "_#{Regexp.last_match(1).downcase}" }
    return it.public_send(snake) if it.respond_to?(snake)

    it.__js_get__(name)
  end

  def iterator_snapshot(objects, iterators)
    iterators.map do |it|
      { "root" => node_id(objects, it.root),
        "reference" => node_id(objects, iterator_attr(it, "referenceNode")),
        "pointerBeforeReference" => iterator_attr(it, "pointerBeforeReferenceNode") }
    end
  end

  # scenario の range を Dommy の Range として作る。
  def build_ranges(objects, documents, specs)
    (specs || []).map do |spec|
      start_node = objects.fetch(spec["start"]["node"])
      doc = documents.values.first or raise "document が無いので Range を作れない"
      range = doc.create_range
      range.set_start(start_node, spec["start"]["offset"])
      range.set_end(objects.fetch(spec["end"]["node"]), spec["end"]["offset"])
      range
    end
  end

  # scenario の observer を Dommy の MutationObserver として作る。
  #
  # Dommy の `MutationObserver.new` は window を要る。scenario の document は
  # `Dommy::Document.new` 由来なので `default_view` から取る。
  # callback は呼ばない（scheduler を回さない）ので、record は queue に貯まり、
  # `takeRecords` で取り出せる。model 側も配送を扱わないので、これで揃う。
  def build_observers(objects, documents, specs)
    (specs || []).map do |spec|
      target = objects.fetch(spec["target"])
      doc = documents.values.first or raise "document が無いので MutationObserver を作れない"
      win = doc.default_view or raise "window が無いので MutationObserver を作れない"
      obs = Dommy::MutationObserver.new(win, proc { |_records| nil })
      options = {
        "childList" => !!spec["childList"],
        "subtree" => !!spec["subtree"],
        "characterData" => !!spec["characterData"],
        "characterDataOldValue" => !!spec["characterDataOldValue"]
      }
      obs.__js_call__("observe", [target, options])
      obs
    end
  end

  # model と同じく、これまでに積まれた record を全部並べる。
  # Dommy 側は `takeRecords` が queue を空にするので、こちらで貯めておく。
  def take_records(objects, observers, accumulated)
    observers.each_with_index do |obs, i|
      obs.__js_call__("takeRecords", []).each do |rec|
        accumulated[i] << record_snapshot(objects, rec)
      end
    end
    accumulated.map(&:dup)
  end

  def record_snapshot(objects, rec)
    nodes = ->(key) { (rec.__js_get__(key) || []).to_a.map { |n| node_id(objects, n) } }
    old_value = rec.__js_get__("oldValue")
    { "type" => rec.__js_get__("type"),
      "target" => node_id(objects, rec.__js_get__("target")),
      "addedNodes" => nodes.call("addedNodes"),
      "removedNodes" => nodes.call("removedNodes"),
      "previousSibling" => node_id(objects, rec.__js_get__("previousSibling")),
      "nextSibling" => node_id(objects, rec.__js_get__("nextSibling")),
      "oldValue" => old_value.nil? ? nil : old_value.to_s }
  end

  def range_snapshot(objects, ranges)
    ranges.map do |r|
      { "start" => { "node" => node_id(objects, r.start_container), "offset" => r.start_offset },
        "end" => { "node" => node_id(objects, r.end_container), "offset" => r.end_offset } }
    end
  end

  def snapshot(objects, kinds, ranges = [], iterators = [], observers = nil)
    nodes = objects.keys.sort.map do |id|
      node = objects[id]
      {
        "id" => id,
        "kind" => kinds[id],
        "parent" => node_id(objects, parent_of(node)),
        "children" => children_of(node).map { |c| node_id(objects, c) },
        "data" => data_of(node)
      }
    end
    out = { "nodes" => nodes, "ranges" => range_snapshot(objects, ranges),
            "iterators" => iterator_snapshot(objects, iterators) }
    out["observers"] = observers if observers
    out
  end

  # 操作の受け手（method を呼ぶ相手）の id。
  def receiver_id(op)
    return op["node"] if CHARACTER_DATA_OPS.include?(op["op"])

    op.key?("target") ? op["target"] : op["parent"]
  end

  def apply(objects, op, iterators = [])
    case op["op"]
    when "iteratorNext", "iteratorPrevious"
      it = iterators[op["iterator"]]
      raise NotImplementedError, "iterator index" if it.nil?

      return op["op"] == "iteratorNext" ? it.next_node : it.previous_node
    end
    if CHARACTER_DATA_OPS.include?(op["op"])
      node = objects[op["node"]]
      method = OP_METHOD.fetch(op["op"])
      raise NotImplementedError, op["op"] if node.nil? || !node.respond_to?(method)

      return case op["op"]
             when "replaceData" then node.replace_data(op["offset"], op["count"], op["data"].to_s)
             when "appendData" then node.append_data(op["data"].to_s)
             when "insertData" then node.insert_data(op["offset"], op["data"].to_s)
             when "deleteData" then node.delete_data(op["offset"], op["count"])
             when "setData" then node.data = op["data"].to_s
             end
    end
    o = ->(key) { key.nil? ? nil : objects[key] }
    receiver = objects[receiver_id(op)]
    method = OP_METHOD.fetch(op["op"]) { raise "未知の op #{op['op'].inspect}" }
    raise NotImplementedError, op["op"] if receiver.nil? || !receiver.respond_to?(method)

    # 存在しない id を指した引数は、Dommy 側では nil になる。
    # 仕様では「Node でない値」なので TypeError 相当だが、
    # model 側は `notFoundError` を返すので、そのままでは意味のある比較にならない。
    # `--capabilities` が示す実装漏れとは別で、これは harness 側の都合である。
    case op["op"]
    when "appendChild"
      raise NotImplementedError, "missing node" if o[op["node"]].nil?

      receiver.append_child(o[op["node"]])
    when "insertBefore"
      raise NotImplementedError, "missing node" if o[op["node"]].nil?
      raise NotImplementedError, "missing child" if op["child"] && o[op["child"]].nil?

      receiver.insert_before(o[op["node"]], o[op["child"]])
    when "replaceChild"
      raise NotImplementedError, "missing node" if o[op["node"]].nil? || o[op["child"]].nil?

      receiver.replace_child(o[op["node"]], o[op["child"]])
    when "removeChild"
      raise NotImplementedError, "missing node" if o[op["node"]].nil?

      receiver.remove_child(o[op["node"]])
    when "replaceChildren"
      if op["node"].nil?
        receiver.replace_children
      else
        raise NotImplementedError, "missing node" if o[op["node"]].nil?

        receiver.replace_children(o[op["node"]])
      end
    when "before", "after", "replaceWith"
      raise NotImplementedError, "missing node" if o[op["node"]].nil?

      receiver.public_send(method, o[op["node"]])
    when "remove"
      receiver.remove
    when "moveBefore"
      raise NotImplementedError, "missing node" if o[op["node"]].nil?
      raise NotImplementedError, "missing child" if op["child"] && o[op["child"]].nil?

      receiver.move_before(o[op["node"]], o[op["child"]])
    end
  end

  def run(scenario)
    kinds = scenario["nodes"].to_h { |s| [s["id"], s["kind"]] }
    builder = Builder.new(scenario["nodes"])
    objects = builder.build
    ranges = build_ranges(objects, builder.documents, scenario["ranges"])
    iterators = build_iterators(objects, builder.documents, scenario["iterators"])
    observers = build_observers(objects, builder.documents, scenario["observers"])
    accumulated = observers.map { [] }
    initial = snapshot(objects, kinds, ranges, iterators,
                       observers.empty? ? nil : take_records(objects, observers, accumulated))
    steps = []
    (scenario["operations"] || []).each do |op|
      begin
        apply(objects, op, iterators)
      rescue NotImplementedError, NoMethodError
        steps << { "ok" => false, "exception" => UNSUPPORTED }
        break
      rescue StandardError => e
        steps << { "ok" => false, "exception" => exception_name(e) }
        break
      end
      recs = observers.empty? ? nil : take_records(objects, observers, accumulated)
      steps << snapshot(objects, kinds, ranges, iterators, recs).merge("ok" => true)
    end
    { "initial" => initial, "steps" => steps }
  end

  # 各 kind が各操作を実装しているかの一覧。
  def capabilities
    doc = Dommy::Document.new
    doc.child_nodes.to_a.each { |n| n.remove if n.respond_to?(:remove) }
    impl = doc.implementation
    # HTML document では CDATASection を作れない（仕様どおり）ので、作れた kind だけを見る。
    builders = {
      "document" => -> { doc },
      "element" => -> { doc.create_element("div") },
      "text" => -> { doc.create_text_node("x") },
      "comment" => -> { doc.create_comment("x") },
      "processingInstruction" => -> { doc.create_processing_instruction("pi", "x") },
      "cdataSection" => -> { doc.create_cdata_section("x") },
      "documentFragment" => -> { doc.create_document_fragment },
      "documentType" => -> { impl.create_document_type("html", "", "") }
    }
    builders.filter_map do |kind, make|
      node = begin
        make.call
      rescue StandardError
        next nil
      end
      [kind, OP_METHOD.select { |_, m| node.respond_to?(m) }.keys]
    end.to_h
  end

  # 出力 file は入力として扱わない。
  def scenario_file?(path)
    path.end_with?(".json") && !path.end_with?(".lean.json") && !path.end_with?(".dommy.json")
  end

  # `DIR/*.json` をまとめて評価し、それぞれ `DIR/<base>.dommy.json` に書く。
  #
  # makiri を ASan 付きで build している環境では、この process から fork できない。
  # Lean の oracle を別 process として起動するのは driver 側の仕事にして、
  # ここでは file の読み書きだけを行う。
  def run_batch(dir)
    failed = 0
    Dir[File.join(dir, "*.json")].sort.each do |path|
      next unless scenario_file?(path)

      base = File.basename(path, ".json")
      out =
        begin
          run(JSON.parse(File.read(path)))
        rescue StandardError => e
          failed = 1
          { "error" => "#{e.class}: #{e.message}" }
        end
      File.write(File.join(dir, "#{base}.dommy.json"), JSON.generate(out))
    end
    failed
  end
end

if $PROGRAM_NAME == __FILE__
  case ARGV[0]
  when "--capabilities"
    puts JSON.pretty_generate(DommyRunner.capabilities)
    exit 0
  when "--batch"
    dir = ARGV[1] or abort "usage: dommy_runner.rb --batch DIR"
    exit DommyRunner.run_batch(dir)
  else
    path = ARGV[0] or abort "usage: dommy_runner.rb [--capabilities|--batch DIR] SCENARIO.json"
    scenario = JSON.parse(File.read(path))
    begin
      puts JSON.generate(DommyRunner.run(scenario))
    rescue StandardError => e
      warn "#{path}: 初期状態を組み立てられない: #{e.class}: #{e.message}"
      exit 1
    end
  end
end
