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

  # NodeFilter.SHOW_ALL。
  SHOW_ALL = 0xFFFFFFFF

  # Infra の HTML namespace。scenario が element の namespace を省いたときの既定。
  HTML_NS = "http://www.w3.org/1999/xhtml"

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
    "setData" => :data=,
    "setAttribute" => :set_attribute,
    "setAttributeNS" => :set_attribute_ns,
    "removeAttribute" => :remove_attribute,
    "removeAttributeNS" => :remove_attribute_ns,
    "toggleAttribute" => :toggle_attribute,
    "normalize" => :normalize
  }.freeze

  # 受け手が range である操作（§5.5 の Range の method）。
  RANGE_OPS = %w[rangeSetStart rangeSetEnd rangeSetStartBefore rangeSetStartAfter
                 rangeSetEndBefore rangeSetEndAfter rangeCollapse rangeSelectNode
                 rangeSelectNodeContents rangeIsPointInRange rangeIntersectsNode
                 rangeCompareBoundaryPoints rangeComparePoint rangeDeleteContents
                 rangeInsertNode rangeToString].freeze

  # 値を返すだけの操作（§4.4 / §4.9 / §4.10）。受け手は node か element。
  #
  # Ruby 側に snake_case の method が無くても JS bridge が持っていることがあるので、
  # 呼び出しは `js_call` / `js_get` を通す。
  QUERY_OPS = %w[compareDocumentPosition nodeContains getRootNode isEqualNode
                 getTextContent getNodeValue substringData
                 getAttribute hasAttribute getAttributeNames
                 lookupNamespaceURI lookupPrefix isDefaultNamespace].freeze

  # 上の操作が呼ぶ JS 側の名前。`nodeContains` と `getTextContent` ほかは
  # model 側の操作名と IDL 名が違う。
  QUERY_JS_NAME = {
    "compareDocumentPosition" => "compareDocumentPosition",
    "nodeContains" => "contains",
    "getRootNode" => "getRootNode",
    "isEqualNode" => "isEqualNode",
    "getTextContent" => "textContent",
    "getNodeValue" => "nodeValue",
    "substringData" => "substringData",
    "getAttribute" => "getAttribute",
    "hasAttribute" => "hasAttribute",
    "getAttributeNames" => "getAttributeNames",
    "lookupNamespaceURI" => "lookupNamespaceURI",
    "lookupPrefix" => "lookupPrefix",
    "isDefaultNamespace" => "isDefaultNamespace"
  }.freeze

  # attribute の getter として読むもの（method ではなく IDL attribute）。
  QUERY_GETTERS = %w[getTextContent getNodeValue].freeze

  # 受け手が TreeWalker である操作（§6.2）。
  WALKER_OPS = %w[walkerParentNode walkerFirstChild walkerLastChild
                  walkerPreviousSibling walkerNextSibling
                  walkerPreviousNode walkerNextNode].freeze

  # 受け手が `node` である操作（CharacterData の method）。
  CHARACTER_DATA_OPS = %w[replaceData appendData insertData deleteData setData].freeze

  # 受け手が `element` である操作（§4.9 の attribute）。
  ATTRIBUTE_OPS = %w[setAttribute setAttributeNS removeAttribute removeAttributeNS
                     toggleAttribute].freeze

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
      node =
        case spec["kind"]
        when "element" then create_element(doc, spec)
        when "text" then doc.create_text_node(data)
        when "comment" then doc.create_comment(data)
        when "processingInstruction" then doc.create_processing_instruction("pi", data)
        when "cdataSection" then doc.create_cdata_section(data)
        when "documentFragment" then doc.create_document_fragment
        when "documentType" then doc.implementation.create_document_type("html", "", "")
        else raise "未知の kind #{spec['kind'].inspect}"
        end
      apply_initial_attributes(node, spec["attributes"])
      @objects[id] = node
    end

    # scenario の namespace / prefix / local name から element を作る。
    #
    # 省略時は HTML namespace の `div`。`createElement` は HTML document なら
    # HTML namespace を与えるので、namespace が HTML のときはそちらを使う。
    def create_element(doc, spec)
      ns = spec["namespace"] || HTML_NS
      qn = spec["prefix"] ? "#{spec['prefix']}:#{spec['localName']}" : (spec["localName"] || "div")
      return doc.create_element(qn) if ns == HTML_NS && spec["prefix"].nil?

      doc.create_element_ns(ns, qn)
    end

    # scenario が与えた初期 attribute を、mutation record を積む前に置く。
    #
    # `setAttributeNS` / `setAttribute` を通すのは、Dommy に attribute list を
    # 直接差し込む口が無いためである。observer はまだ居ないので record は出ない。
    def apply_initial_attributes(node, attrs)
      return if attrs.nil? || attrs.empty?
      raise NotImplementedError, "attributes on non-element" unless node.respond_to?(:set_attribute)

      # 常に namespace 版を使う。`setAttribute` は HTML namespace の element が
      # HTML document にあるとき名前を ASCII lowercase するので、
      # scenario が書いた名前をそのまま置けない。
      attrs.each do |a|
        qn = a["prefix"] ? "#{a['prefix']}:#{a['localName']}" : a["localName"].to_s
        node.set_attribute_ns(a["namespace"], qn, a["value"].to_s)
      end
    end
  end

  module_function

  # IDL の戻り値のうち、どの kind として比べるか。
  #
  # `undefined` と `null` を取り違えないよう kind を添える
  # （`removeChild` が null を返したら不一致、`remove()` が undefined を返すのは正しい）。
  NODE_RETURNING_OPS = %w[appendChild insertBefore replaceChild removeChild
                          iteratorNext iteratorPrevious getRootNode
                          walkerParentNode walkerFirstChild walkerLastChild
                          walkerPreviousSibling walkerNextSibling
                          walkerPreviousNode walkerNextNode].freeze

  def return_value_snapshot(objects, op, returned)
    case op["op"]
    when *NODE_RETURNING_OPS
      { "kind" => "node", "node" => returned.nil? ? nil : node_id(objects, returned) }
    when "toggleAttribute", "rangeIsPointInRange", "rangeIntersectsNode"
      { "kind" => "boolean", "value" => !!returned }
    when "rangeCompareBoundaryPoints", "rangeComparePoint", "compareDocumentPosition"
      { "kind" => "number", "value" => returned.to_i }
    when "nodeContains", "isEqualNode", "hasAttribute", "isDefaultNamespace"
      { "kind" => "boolean", "value" => !!returned }
    when "getTextContent", "getNodeValue", "substringData", "getAttribute", "rangeToString",
         "lookupNamespaceURI", "lookupPrefix"
      { "kind" => "string", "value" => returned.nil? ? nil : returned.to_s }
    when "getAttributeNames"
      { "kind" => "strings", "value" => (returned || []).to_a.map(&:to_s) }
    when "takeRecords"
      { "kind" => "records",
        "records" => (returned || []).to_a.map { |rec| record_snapshot(objects, rec) } }
    else
      { "kind" => "undefined" }
    end
  end

  # Dommy が「表現できない」と言ったものか。
  #
  # Ruby の UTF-8 String は lone surrogate を持てないので、`Dommy::Internal::Utf16`
  # は surrogate pair を割る切り出しを RuntimeError で断る。
  # 仕様の例外ではないので、実装漏れと同じく `__unsupported__` として報告する。
  def out_of_range_representation?(error)
    error.is_a?(RuntimeError) && error.message.include?("surrogate pair")
  end

  # Dommy の例外から仕様上の名前を取り出す。
  def exception_name(error)
    return UNSUPPORTED if out_of_range_representation?(error)

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

  # scenario が作った node のうち、`node` と **同一の object** のもの。
  #
  # `equal?` で引く。`==` に落とすと、adopt が wrapper を作り直しても気付けない
  # （WHATWG の adopt は node を作り変えず、同じ node を動かす）。
  # 同一のものが無ければ `UNKNOWN_NODE` で、比較は不一致になる。
  def node_id(objects, node)
    return nil if node.nil?

    objects.each { |id, obj| return id if obj.equal?(node) }
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
      what = spec["whatToShow"] || SHOW_ALL
      doc.create_node_iterator(objects.fetch(spec["root"]), what, nil)
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
        "pointerBeforeReference" => iterator_attr(it, "pointerBeforeReferenceNode"),
        "whatToShow" => iterator_attr(it, "whatToShow") }
    end
  end

  # JS 名の method を呼ぶ。Ruby 側の snake_case（あるいは述語形）があればそれを使い、
  # 無ければ bridge 経由で呼ぶ。bridge も持っていなければ「比べられない」とする。
  def js_call(obj, name, args = [])
    snake = name.gsub(/([A-Z])/) { "_#{Regexp.last_match(1).downcase}" }
    return obj.public_send(snake, *args) if obj.respond_to?(snake)
    return obj.public_send("#{snake}?", *args) if obj.respond_to?("#{snake}?")
    raise NotImplementedError, name unless js_method?(obj, name)

    obj.__js_call__(name, args)
  end

  # IDL attribute の getter を読む。
  def js_get(obj, name)
    snake = name.gsub(/([A-Z])/) { "_#{Regexp.last_match(1).downcase}" }
    return obj.public_send(snake) if obj.respond_to?(snake)
    raise NotImplementedError, name unless obj.respond_to?(:__js_get__)

    value = obj.__js_get__(name)
    raise NotImplementedError, name if defined?(Dommy::Bridge::ABSENT) && value == Dommy::Bridge::ABSENT

    value
  end

  # bridge が公開している JS method か。
  def js_method?(obj, name)
    obj.respond_to?(:__js_method_names__) && obj.__js_method_names__.include?(name)
  end

  # その kind がその操作を持つか（capability report 用）。
  def supports_query?(node, op)
    name = QUERY_JS_NAME.fetch(op)
    snake = name.gsub(/([A-Z])/) { "_#{Regexp.last_match(1).downcase}" }
    return true if node.respond_to?(snake) || node.respond_to?("#{snake}?")
    return node.respond_to?(:__js_get__) if QUERY_GETTERS.include?(op)

    js_method?(node, name)
  end

  # scenario の TreeWalker を Dommy の TreeWalker として作る。
  #
  # `createTreeWalker` は current を root に置く。scenario が `current` を指定した場合は
  # setter で動かす（§6.2 の `currentNode` は書ける）。
  def build_walkers(objects, documents, specs)
    (specs || []).map do |spec|
      doc = documents.values.first or raise "document が無いので TreeWalker を作れない"
      what = spec["whatToShow"] || SHOW_ALL
      walker = doc.create_tree_walker(objects.fetch(spec["root"]), what, nil)
      current = spec["current"]
      walker.current_node = objects.fetch(current) if current && current != spec["root"]
      walker
    end
  end

  def walker_snapshot(objects, walkers)
    walkers.map do |w|
      { "root" => node_id(objects, w.root),
        "current" => node_id(objects, w.current_node),
        "whatToShow" => w.what_to_show }
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
  # callback は配送された record をそのまま控える。`notify` 操作（microtask
  # checkpoint）で呼ばれ、その step の観測として出す。
  #
  # `target` が無い spec は、registration を持たない observer を作るだけにする。
  # scenario の側で `observe` 操作を使う場合がこれである。
  #
  # 戻り値は [observers, log]。log は配送された順に [observer index, records] を並べる。
  # 配送の順序自体が観測対象なので、observer の index 順に並べ直してはいけない。
  def build_observers(objects, documents, specs)
    log = []
    observers = (specs || []).each_with_index.map do |spec, index|
      doc = documents.values.first or raise "document が無いので MutationObserver を作れない"
      win = doc.default_view or raise "window が無いので MutationObserver を作れない"
      obs = Dommy::MutationObserver.new(win, proc { |records|
        log << { "observer" => index,
                 "records" => records.to_a.map { |rec| record_snapshot(objects, rec) } }
      })
      if spec["target"]
        obs.__js_call__("observe", [objects.fetch(spec["target"]), observe_options(spec)])
      end
      obs
    end
    [observers, log]
  end

  def observe_options(spec)
    {
      "childList" => !!spec["childList"],
      "subtree" => !!spec["subtree"],
      "characterData" => !!spec["characterData"],
      "characterDataOldValue" => !!spec["characterDataOldValue"],
      "attributes" => !!spec["attributes"],
      "attributeOldValue" => !!spec["attributeOldValue"]
    }.tap { |o| o["attributeFilter"] = spec["attributeFilter"] if spec["attributeFilter"] }
  end

  # element の attribute list を model と同じ形に並べる。
  #
  # Dommy は attribute を `Attr` node として持つので、
  # namespace / prefix / local name / value だけを取り出す。
  # Element だけが namespace / prefix / local name を持つ。
  def element_field(node, name)
    return nil unless node.respond_to?(:__js_get__) && node.__js_get__("nodeType") == 1

    v = node.__js_get__(name)
    v.nil? ? nil : v.to_s
  end

  def attributes_of(node)
    return [] unless node.respond_to?(:__js_get__) && node.__js_get__("nodeType") == 1
    return [] unless node.respond_to?(:attributes)

    node.attributes.to_a.map do |a|
      { "namespace" => a.namespace_uri, "prefix" => a.prefix,
        "localName" => a.local_name, "value" => a.value.to_s }
    end
  end

  # microtask checkpoint。配送はここで走る。
  def run_microtask_checkpoint(documents)
    doc = documents.values.first or return nil
    win = doc.default_view or return nil
    win.scheduler.perform_microtask_checkpoint
    nil
  end

  # 現在 queue に積まれている record を、取り出さずに並べる。
  # `takeRecords()` が返すものと同じで、配送が走ると空になる。
  def queued_records(objects, observers)
    observers.map do |obs|
      obs.records.map { |rec| record_snapshot(objects, rec) }
    end
  end

  # その step で callback に配送された record。model の `delivered` に対応する。
  # 配送された順に並ぶ。
  def delivered_snapshot(log)
    log.map { |entry| { "observer" => entry["observer"], "records" => entry["records"] } }
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
      "attributeName" => rec.__js_get__("attributeName")&.to_s,
      "attributeNamespace" => rec.__js_get__("attributeNamespace")&.to_s,
      "oldValue" => old_value.nil? ? nil : old_value.to_s }
  end

  def range_snapshot(objects, ranges)
    ranges.map do |r|
      { "start" => { "node" => node_id(objects, r.start_container), "offset" => r.start_offset },
        "end" => { "node" => node_id(objects, r.end_container), "offset" => r.end_offset } }
    end
  end

  # WHATWG の node document。Document 自身の node document は仕様では null だが、
  # model は「Document の node document は自分自身」として持つので、そちらに合わせる。
  def node_document_id(objects, id, node, kinds)
    return id if kinds[id] == "document"
    return UNKNOWN_NODE unless node.respond_to?(:owner_document)

    node_id(objects, node.owner_document)
  end

  def snapshot(objects, kinds, ranges = [], iterators = [], observers = nil, walkers = [])
    nodes = objects.keys.sort.map do |id|
      node = objects[id]
      {
        "id" => id,
        "kind" => kinds[id],
        "parent" => node_id(objects, parent_of(node)),
        "children" => children_of(node).map { |c| node_id(objects, c) },
        "nodeDocument" => node_document_id(objects, id, node, kinds),
        "data" => data_of(node),
        "attributes" => attributes_of(node),
        "namespace" => element_field(node, "namespaceURI"),
        "prefix" => element_field(node, "prefix"),
        "localName" => element_field(node, "localName") || "",
        "tagName" => element_field(node, "tagName")
      }
    end
    out = { "nodes" => nodes, "ranges" => range_snapshot(objects, ranges),
            "iterators" => iterator_snapshot(objects, iterators),
            "walkers" => walker_snapshot(objects, walkers) }
    out["observers"] = observers if observers
    out
  end

  # 操作の受け手（method を呼ぶ相手）の id。
  def receiver_id(op)
    return op["node"] if CHARACTER_DATA_OPS.include?(op["op"])
    return op["node"] if QUERY_OPS.include?(op["op"]) && op.key?("node")
    return op["element"] if ATTRIBUTE_OPS.include?(op["op"])

    op.key?("target") ? op["target"] : op["parent"]
  end

  def apply(objects, op, iterators = [], ctx = {})
    case op["op"]
    when "iteratorNext", "iteratorPrevious"
      it = iterators[op["iterator"]]
      raise NotImplementedError, "iterator index" if it.nil?

      return op["op"] == "iteratorNext" ? it.next_node : it.previous_node
    when "observe"
      obs = (ctx[:observers] || [])[op["observer"]]
      raise NotImplementedError, "observer index" if obs.nil?
      raise NotImplementedError, "missing target" if objects[op["target"]].nil?

      return obs.__js_call__("observe", [objects[op["target"]], observe_options(op)])
    when "disconnect"
      obs = (ctx[:observers] || [])[op["observer"]]
      raise NotImplementedError, "observer index" if obs.nil?

      return obs.__js_call__("disconnect", [])
    when "takeRecords"
      obs = (ctx[:observers] || [])[op["observer"]]
      raise NotImplementedError, "observer index" if obs.nil?

      return obs.__js_call__("takeRecords", [])
    when "notify"
      return run_microtask_checkpoint(ctx[:documents] || {})
    end

    if QUERY_OPS.include?(op["op"])
      receiver = objects[op.key?("element") ? op["element"] : op["node"]]
      raise NotImplementedError, "missing node" if receiver.nil?

      name = QUERY_JS_NAME.fetch(op["op"])
      return js_get(receiver, name) if QUERY_GETTERS.include?(op["op"])

      return case op["op"]
             when "compareDocumentPosition", "nodeContains", "isEqualNode"
               other = objects[op["other"]]
               raise NotImplementedError, "missing node" if other.nil?

               js_call(receiver, name, [other])
             when "getRootNode" then js_call(receiver, name, [])
             when "substringData" then js_call(receiver, name, [op["offset"], op["count"]])
             when "getAttribute", "hasAttribute" then js_call(receiver, name, [op["name"]])
             when "getAttributeNames" then js_call(receiver, name, [])
             when "lookupNamespaceURI" then js_call(receiver, name, [op["prefix"]])
             when "lookupPrefix", "isDefaultNamespace" then js_call(receiver, name, [op["namespace"]])
             end
    end

    if WALKER_OPS.include?(op["op"])
      walker = (ctx[:walkers] || [])[op["walker"]]
      raise NotImplementedError, "walker index" if walker.nil?

      return case op["op"]
             when "walkerParentNode" then walker.parent_node
             when "walkerFirstChild" then walker.first_child
             when "walkerLastChild" then walker.last_child
             when "walkerPreviousSibling" then walker.previous_sibling
             when "walkerNextSibling" then walker.next_sibling
             when "walkerPreviousNode" then walker.previous_node
             when "walkerNextNode" then walker.next_node
             end
    end
    if RANGE_OPS.include?(op["op"])
      range = (ctx[:ranges] || [])[op["range"]]
      raise NotImplementedError, "range index" if range.nil?

      node = op.key?("node") ? objects[op["node"]] : nil
      raise NotImplementedError, "missing node" if op.key?("node") && node.nil?

      return case op["op"]
             when "rangeSetStart" then range.set_start(node, op["offset"])
             when "rangeSetEnd" then range.set_end(node, op["offset"])
             when "rangeSetStartBefore" then range.set_start_before(node)
             when "rangeSetStartAfter" then range.set_start_after(node)
             when "rangeSetEndBefore" then range.set_end_before(node)
             when "rangeSetEndAfter" then range.set_end_after(node)
             when "rangeCollapse" then range.collapse(op["toStart"] ? true : false)
             when "rangeSelectNode" then range.select_node(node)
             when "rangeSelectNodeContents" then range.select_node_contents(node)
             when "rangeIsPointInRange" then range.is_point_in_range(node, op["offset"])
             when "rangeIntersectsNode" then range.intersects_node(node)
             when "rangeCompareBoundaryPoints"
               other = (ctx[:ranges] || [])[op["source"]]
               raise NotImplementedError, "range index" if other.nil?

               range.compare_boundary_points(op["how"], other)
             when "rangeComparePoint" then range.compare_point(node, op["offset"])
             when "rangeDeleteContents" then range.delete_contents
             when "rangeInsertNode" then range.insert_node(node)
             when "rangeToString" then range.to_s
             end
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
    if ATTRIBUTE_OPS.include?(op["op"])
      element = objects[op["element"]]
      method = OP_METHOD.fetch(op["op"])
      raise NotImplementedError, op["op"] if element.nil? || !element.respond_to?(method)

      name = op["name"].to_s
      return case op["op"]
             when "setAttribute" then element.set_attribute(name, op["value"].to_s)
             when "setAttributeNS"
               element.set_attribute_ns(op["namespace"], name, op["value"].to_s)
             when "removeAttribute" then element.remove_attribute(name)
             when "removeAttributeNS" then element.remove_attribute_ns(op["namespace"], name)
             when "toggleAttribute"
               if op.key?("force") && !op["force"].nil?
                 element.toggle_attribute(name, op["force"])
               else
                 element.toggle_attribute(name)
               end
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
    when "normalize"
      receiver.normalize
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
    walkers = build_walkers(objects, builder.documents, scenario["walkers"])
    observers, delivery_log = build_observers(objects, builder.documents, scenario["observers"])
    ctx = { objects: objects, kinds: kinds, ranges: ranges, iterators: iterators,
            walkers: walkers, observers: observers, documents: builder.documents }
    initial = snapshot(objects, kinds, ranges, iterators,
                       observers.empty? ? nil : queued_records(objects, observers), walkers)
                .merge("delivered" => [])
    steps = []
    (scenario["operations"] || []).each do |op|
      delivery_log.clear
      begin
        returned = apply(objects, op, iterators, ctx)
      rescue NotImplementedError, NoMethodError => e
        # この harness で比べられない step。理由を残しておくと、
        # harness の制約と Dommy の実装漏れを取り違えずに済む。
        steps << { "ok" => false, "exception" => UNSUPPORTED,
                   "reason" => "#{e.class}: #{e.message}" }
        break
      rescue StandardError => e
        # 失敗した操作は状態を変えてはならない（roadmap §9）。
        # 変えていないことを比べられるように、失敗した step でも観測を出す。
        recs = observers.empty? ? nil : queued_records(objects, observers)
        steps << snapshot(objects, kinds, ranges, iterators, recs, walkers)
                 .merge("ok" => false, "exception" => exception_name(e),
                        "delivered" => delivered_snapshot(delivery_log))
        break
      end
      recs = observers.empty? ? nil : queued_records(objects, observers)
      steps << snapshot(objects, kinds, ranges, iterators, recs, walkers)
               .merge("ok" => true, "delivered" => delivered_snapshot(delivery_log),
                      "returned" => return_value_snapshot(objects, op, returned))
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
      ops = OP_METHOD.select { |_, m| node.respond_to?(m) }.keys
      ops += QUERY_OPS.select { |q| supports_query?(node, q) }
      [kind, ops]
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
