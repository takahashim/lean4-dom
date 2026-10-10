# frozen_string_literal: true

# Dommy 側の scenario runner。
#
# lean4-dom の `lake exe dom-model SCENARIO.json` と同じ形式の JSON を標準出力に書く。
# `--batch DIR` では `DIR/<base>.impl.json` に書く。比較は test/compare.rb が行う。
# 実装ごとに runner を用意して差し替える形なので、この file は Dommy 専用である。
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
    "dispatchEvent" => :dispatch_event,
    "addEventListener" => :add_event_listener,
    "removeEventListener" => :remove_event_listener,
    "normalize" => :normalize,
    "createElement" => :create_element,
    "createElementNS" => :create_element_ns,
    "createTextNode" => :create_text_node,
    "createComment" => :create_comment,
    "createDocumentFragment" => :create_document_fragment,
    "cloneNode" => :clone_node,
    "importNode" => :import_node,
    "adoptNode" => :adopt_node,
    "createAttribute" => :create_attribute,
    "createAttributeNS" => :create_attribute_ns,
    "getAttributeNode" => :get_attribute_node,
    "getAttributeNodeNS" => :get_attribute_node_ns,
    "setAttributeNode" => :set_attribute_node,
    "removeAttributeNode" => :remove_attribute_node,
    "removeNamedItem" => :attributes
  }.freeze

  # `Attr` を渡す / 返す操作。受け手は Document か Element である。
  ATTR_NODE_OPS = %w[createAttribute createAttributeNS getAttributeNode getAttributeNodeNS
                     setAttributeNode removeAttributeNode removeNamedItem].freeze

  # node を作る操作。受け手は Document である（cloneNode を除く）。
  CREATE_OPS = %w[createElement createElementNS createTextNode createComment
                  createDocumentFragment importNode adoptNode].freeze

  # nodeType から scenario の kind 名へ。作った node に kind を付けるのに使う。
  NODE_TYPE_KIND = {
    1 => "element", 3 => "text", 4 => "cdataSection", 7 => "processingInstruction",
    8 => "comment", 9 => "document", 10 => "documentType", 11 => "documentFragment"
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
                 lookupNamespaceURI lookupPrefix isDefaultNamespace
                 querySelector querySelectorAll matches closest
                 getElementById getElementsByClassName getElementsByName].freeze

  # id・class・name で引く method と、それを持つ node の種別（nodeType）。
  # 種別が合わなければ実装と同じく TypeError にする。
  LOOKUP_OPS = {
    "getElementById" => ["elementId", [9, 11]],
    "getElementsByClassName" => ["classNames", [1, 9]],
    "getElementsByName" => ["elementName", [9]]
  }.freeze

  # selector を取る method（§4.2.6 / §4.8）。受け手の種別が合わなければ TypeError。
  SELECTOR_OPS = %w[querySelector querySelectorAll matches closest].freeze
  # `matches` と `closest` は Element の method である。
  SELECTOR_ELEMENT_OPS = %w[matches closest].freeze

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
    "isDefaultNamespace" => "isDefaultNamespace",
    "querySelector" => "querySelector",
    "querySelectorAll" => "querySelectorAll",
    "matches" => "matches",
    "closest" => "closest",
    "getElementById" => "getElementById",
    "getElementsByClassName" => "getElementsByClassName",
    "getElementsByName" => "getElementsByName"
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

  # §4.9 の reflect（`id` / `className` / `slot`）、§7.1 の `classList`、
  # §4.2.10.1 の `children.namedItem`。どれも namespace が null の attribute を読み書きする。
  # Ruby 側の名前が揃っていないので、bridge（`__js_get__` / `__js_set__` / `__js_call__`）を通す。
  REFLECT_OPS = %w[getReflected setReflected classListAdd classListRemove classListToggle
                   classListReplace classListContains childrenNamedItem
                   datasetGet datasetSet datasetDelete datasetKeys].freeze

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
    #
    # quirks / limited-quirks の document は HTML parser でしか作れないので、doctype を
    # 読ませた backend の document から `Window` を作る（mode は parse のときに決まる）。
    MODE_SOURCE = {
      "quirks" => "",
      "limited-quirks" =>
        '<!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">'
    }.freeze

    def new_empty_document(mode = "no-quirks")
      win = if MODE_SOURCE.key?(mode)
              Dommy::Window.new(nil, backend_doc: Dommy::Backend.parse(MODE_SOURCE[mode]))
            else
              Dommy::Window.new
            end
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
        # この harness は `Window` の document しか作れないので、必ず HTML document になる。
        # scenario が非 HTML document を求めたら黙って HTML document を返さず、断る。
        # そうしないと `createElement` の step 2 / 4 が偽の不一致になる。
        if spec["isHTMLDocument"] == false
          raise "node #{id}: 非 HTML document はこの harness では作れない"
        end

        doc = new_empty_document(spec["mode"] || "no-quirks")
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
      # `createElement` は HTML document で名前を lowercase するので、
      # 大文字を含む local name を作りたいときは `createElementNS` を通す。
      return doc.create_element(qn) if ns == HTML_NS && spec["prefix"].nil? && qn == qn.downcase

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
                          walkerPreviousNode walkerNextNode
                          createElement createElementNS createTextNode createComment
                          createDocumentFragment cloneNode importNode adoptNode
                          querySelector closest getElementById].freeze

  # `Attr` を返す操作。
  ATTR_RETURNING_OPS = %w[createAttribute createAttributeNS getAttributeNode getAttributeNodeNS
                          setAttributeNode removeAttributeNode removeNamedItem].freeze

  # `attrQuery` の戻り値の種類。
  ATTR_QUERY_KIND = {
    "ownerDocument" => "node", "parentNode" => "node", "parentElement" => "node",
    "ownerElement" => "node", "firstChild" => "node", "getRootNode" => "node",
    "nodeName" => "string", "nodeValue" => "string", "textContent" => "string",
    "isConnected" => "boolean", "hasChildNodes" => "boolean"
  }.freeze

  def attr_object?(obj)
    obj.is_a?(Dommy::Attr)
  end

  def return_value_snapshot(ctx, op, returned)
    objects = ctx[:objects]
    # `Attr` を `Node` として渡した op は `Attr` を返しうる（getRootNode・cloneNode・importNode・adoptNode）。
    return { "kind" => "attr", "attr" => ctx[:attr_ids][returned] } if attr_object?(returned)

    if op["op"] == "attrQuery"
      return case ATTR_QUERY_KIND.fetch(op["query"])
             when "node" then { "kind" => "node", "node" => returned.nil? ? nil : node_id(objects, returned) }
             when "boolean" then { "kind" => "boolean", "value" => !!returned }
             else { "kind" => "string", "value" => returned.nil? ? nil : returned.to_s }
             end
    end
    case op["op"]
    when *NODE_RETURNING_OPS
      { "kind" => "node", "node" => returned.nil? ? nil : node_id(objects, returned) }
    when *ATTR_RETURNING_OPS
      { "kind" => "attr", "attr" => returned.nil? ? nil : ctx[:attr_ids][returned] }
    when "toggleAttribute", "rangeIsPointInRange", "rangeIntersectsNode",
         "classListToggle", "classListReplace", "classListContains"
      { "kind" => "boolean", "value" => !!returned }
    when "childrenNamedItem"
      { "kind" => "node", "node" => returned.nil? ? nil : node_id(objects, returned) }
    when "getReflected"
      if [true, false].include?(returned)
        { "kind" => "boolean", "value" => returned }
      else
        { "kind" => "string", "value" => returned.nil? ? nil : returned.to_s }
      end
    when "datasetGet"
      absent = returned.nil? || (defined?(Dommy::Bridge::ABSENT) && returned == Dommy::Bridge::ABSENT)
      { "kind" => "string", "value" => absent ? nil : returned.to_s }
    when "datasetKeys"
      { "kind" => "strings", "value" => (returned || []).to_a.map(&:to_s) }
    when "rangeCompareBoundaryPoints", "rangeComparePoint", "compareDocumentPosition"
      { "kind" => "number", "value" => returned.to_i }
    when "dispatchEvent"
      { "kind" => "boolean", "value" => !!returned }
    when "nodeContains", "isEqualNode", "hasAttribute", "isDefaultNamespace", "matches"
      { "kind" => "boolean", "value" => !!returned }
    when "querySelectorAll", "getElementsByClassName", "getElementsByName"
      { "kind" => "nodes", "nodes" => (returned || []).to_a.map { |n| node_id(objects, n) } }
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

  # 作った node の kind。
  #
  # Dommy は class によって `node_type` を Ruby の method として持たないので、
  # bridge 経由の `nodeType` も見る。
  def node_type_of(node)
    return node.node_type.to_i if node.respond_to?(:node_type)
    return node.__js_get__("nodeType").to_i if node.respond_to?(:__js_get__)

    nil
  end

  def kind_name(node)
    t = node_type_of(node)
    raise NotImplementedError, "nodeType" if t.nil?

    NODE_TYPE_KIND.fetch(t) { raise NotImplementedError, "nodeType #{t}" }
  end

  # 作った node に scenario の id を振る。
  #
  # model の `freshId` は **store にある id の最大より一つ大きいもの**で、
  # deep な clone は tree order（preorder）でそれを順に使う。こちらも同じ規則で振る。
  # これで、生成した node も id で比べられるようになる。
  def register_subtree(ctx, node)
    return nil if node.nil?

    objects = ctx[:objects]
    id = objects.keys.max.to_i + 1
    objects[id] = node
    ctx[:kinds][id] = kind_name(node)
    children_of(node).each { |c| register_subtree(ctx, c) }
    id
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

  # `DOMStringMap` の named property の getter / setter / deleter と、supported property names。
  def dataset_op(map, op)
    name = op["name"].to_s
    case op["op"]
    when "datasetGet"
      raise NotImplementedError, "dataset get" unless map.respond_to?(:__js_get__)

      map.__js_get__(name)
    when "datasetSet"
      raise NotImplementedError, "dataset set" unless map.respond_to?(:__js_set__)

      map.__js_set__(name, op["value"].to_s)
    when "datasetDelete"
      raise NotImplementedError, "dataset delete" unless map.respond_to?(:__js_delete__)

      map.__js_delete__(name)
      nil
    when "datasetKeys"
      raise NotImplementedError, "dataset keys" unless map.respond_to?(:__js_named_props__)

      map.__js_named_props__.uniq
    end
  end

  # IDL attribute の setter を呼ぶ。
  def js_set(obj, name, value)
    snake = name.gsub(/([A-Z])/) { "_#{Regexp.last_match(1).downcase}" }
    return obj.public_send("#{snake}=", value) if obj.respond_to?("#{snake}=")
    raise NotImplementedError, name unless obj.respond_to?(:__js_set__)

    result = obj.__js_set__(name, value)
    raise NotImplementedError, name if defined?(Dommy::Bridge::UNHANDLED) && result == Dommy::Bridge::UNHANDLED

    result
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

  # scenario の event listener を Dommy の listener として登録する。
  #
  # callback そのものは model の外なので、scenario が宣言した「決まった副作用」を
  # 行う lambda を作る。呼ばれたことは `log` に積み、差分テストはその列を比べる。
  # callback object の同一性（add の重複判定と removeEventListener が使う）は
  # 宣言ごとに一つの lambda を使い回すことで model の callback 番号と対応させる。
  def build_listeners(objects, specs, log)
    specs = specs || []
    callbacks = []
    specs.each_with_index do |spec, i|
      callback_id = spec["callback"] || i
      callbacks[i] = make_listener_callback(objects, callbacks, specs, spec, callback_id, log)
    end
    specs.each_with_index do |spec, i|
      target = objects[spec["target"]]
      raise NotImplementedError, "missing listener target" if target.nil?

      target.add_event_listener(spec["type"].to_s, callbacks[i],
                                { "capture" => !!spec["capture"], "once" => !!spec["once"] })
    end
    callbacks
  end

  def make_listener_callback(objects, callbacks, specs, spec, callback_id, log)
    action = spec["action"]
    lambda do |event|
      log << { "callback" => callback_id,
               "currentTarget" => node_id(objects, event.__js_get__("currentTarget")),
               "eventPhase" => event.__js_get__("eventPhase") }
      begin
        run_listener_action(objects, callbacks, specs, action, event)
      rescue StandardError => e
        # Dommy は listener の例外を握り潰すので、握り潰される前に印を残す。
        # 残しておけば差分として出るので、runner の不具合を見落とさない。
        log << { "callback" => callback_id, "error" => "#{e.class}: #{e.message}" }
      end
      nil
    end
  end

  def run_listener_action(objects, callbacks, specs, action, event)
    kind = action.is_a?(Hash) ? action["kind"] : action
    case kind
    when nil, "none" then nil
    when "stopPropagation" then event.__js_call__("stopPropagation", [])
    when "stopImmediatePropagation" then event.__js_call__("stopImmediatePropagation", [])
    when "preventDefault" then event.__js_call__("preventDefault", [])
    when "removeListener"
      i = action["index"]
      spec = specs[i] or raise NotImplementedError, "listener index"
      objects[spec["target"]].remove_event_listener(spec["type"].to_s, callbacks[i],
                                                    { "capture" => !!spec["capture"] })
    when "addListener"
      source = callbacks[action["source"]] or raise NotImplementedError, "listener index"
      objects[action["target"]].add_event_listener(action["type"].to_s, source,
                                                   { "capture" => !!action["capture"] })
    else raise NotImplementedError, "listener action #{kind}"
    end
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
        obs.__js_call__("observe", [objects.fetch(spec["target"]), initial_observe_options(spec)])
      end
      obs
    end
    [observers, log]
  end

  # 初期状態の observer の options。model は registration を直接組み立てる（`buildState`）ので、
  # step 1-2 の補完が効かないよう全部を明示して渡す。
  def initial_observe_options(spec)
    {
      "childList" => !!spec["childList"],
      "subtree" => !!spec["subtree"],
      "characterData" => !!spec["characterData"],
      "characterDataOldValue" => !!spec["characterDataOldValue"],
      "attributes" => !!spec["attributes"],
      "attributeOldValue" => !!spec["attributeOldValue"]
    }.tap { |o| o["attributeFilter"] = spec["attributeFilter"] if spec["attributeFilter"] }
  end

  # `observe` 操作の options。`MutationObserverInit` は既定値の無い member が多く、
  # step 1-2 は「存在するか」で分岐するので、scenario にある key だけを渡す。
  OBSERVE_KEYS = %w[childList subtree attributes attributeOldValue attributeFilter
                    characterData characterDataOldValue].freeze

  def observe_options(spec)
    spec.slice(*OBSERVE_KEYS)
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

  def attribute_nodes(node)
    return [] unless node_type_of(node) == 1
    return [] unless node.respond_to?(:attributes)

    node.attributes.to_a
  end

  # attribute に model と同じ規則で id を振る。
  #
  #   初期状態  node の id の昇順・node の中では list 順に 1 から
  #   新しいもの いま木にある id と detach された `Attr` の id を合わせた最大より一つ大きいもの
  #
  # 1 から始めるのは、model の `maxAttrId` が attribute の無い木で 0 を返すからである。
  #
  # model の `freshStateAttrId` がそうしている。`Attr` object の同一性で引くので、
  # `setAttribute` が既にある attribute を書き換えたのか作り直したのかが観測できる。
  # 木にも detach された list にも無い attribute の id は覚えない（model 側の最大も現在の状態だけで決まる）。
  def refresh_attr_ids(ctx)
    old = ctx[:attr_ids] || {}.compare_by_identity
    ordered = ctx[:objects].keys.sort.flat_map { |nid| attribute_nodes(ctx[:objects][nid]) }
    ordered += (ctx[:detached] || [])
    fresh = {}.compare_by_identity
    max = 0
    ordered.each do |a|
      id = old[a]
      next if id.nil?

      fresh[a] = id
      max = id if id > max
    end
    ordered.each do |a|
      next if fresh.key?(a)

      max += 1
      fresh[a] = max
    end
    ctx[:attr_ids] = fresh
  end

  def attr_snapshot(ctx, a)
    { "id" => ctx[:attr_ids][a], "namespace" => a.namespace_uri, "prefix" => a.prefix,
      "localName" => a.local_name, "value" => a.value.to_s }
  end

  def attributes_of(ctx, node)
    attribute_nodes(node).map { |a| attr_snapshot(ctx, a) }
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

  def snapshot(ctx, ranges = [], iterators = [], observers = nil, walkers = [])
    objects = ctx[:objects]
    kinds = ctx[:kinds]
    refresh_attr_ids(ctx)
    nodes = objects.keys.sort.map do |id|
      node = objects[id]
      {
        "id" => id,
        "kind" => kinds[id],
        "parent" => node_id(objects, parent_of(node)),
        "children" => children_of(node).map { |c| node_id(objects, c) },
        "nodeDocument" => node_document_id(objects, id, node, kinds),
        "data" => data_of(node),
        "attributes" => attributes_of(ctx, node),
        "namespace" => element_field(node, "namespaceURI"),
        "prefix" => element_field(node, "prefix"),
        "localName" => element_field(node, "localName") || "",
        "tagName" => element_field(node, "tagName")
      }
    end
    out = { "nodes" => nodes, "ranges" => range_snapshot(objects, ranges),
            "iterators" => iterator_snapshot(objects, iterators),
            "walkers" => walker_snapshot(objects, walkers),
            "detachedAttrs" => (ctx[:detached] || []).map { |a| attr_snapshot(ctx, a) } }
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

  # `Attr` を渡す / 返す操作。detach された `Attr` の list も model と同じ規則で保つ。
  #
  #   createAttribute*      作ったものを足す
  #   removeAttributeNode   外して返ったものを足す
  #   removeNamedItem       同上
  #   setAttributeNode      渡したものを外し、押し出されたものを足す
  #
  # 名前で消した attribute（`removeAttribute`）は誰も参照できないので入らない。
  def apply_attr_node(ctx, op)
    objects = ctx[:objects]
    detached = ctx[:detached]
    receiver = objects[op.key?("document") ? op["document"] : op["element"]]
    raise NotImplementedError, "missing node" if receiver.nil?

    case op["op"]
    when "createAttribute", "createAttributeNS"
      method = OP_METHOD.fetch(op["op"])
      raise NotImplementedError, op["op"] unless receiver.respond_to?(method)

      a = op["op"] == "createAttribute" ? receiver.create_attribute(op["name"].to_s)
                                        : receiver.create_attribute_ns(op["namespace"],
                                                                       op["name"].to_s)
      detached << a
      a
    when "getAttributeNode"
      raise NotImplementedError, op["op"] unless receiver.respond_to?(:get_attribute_node)

      receiver.get_attribute_node(op["name"].to_s)
    when "getAttributeNodeNS"
      raise NotImplementedError, op["op"] unless receiver.respond_to?(:get_attribute_node_ns)

      receiver.get_attribute_node_ns(op["namespace"], op["name"].to_s)
    when "setAttributeNode"
      raise NotImplementedError, op["op"] unless receiver.respond_to?(:set_attribute_node)

      a = find_attr(ctx, op["attr"])
      raise NotImplementedError, "missing attr" if a.nil?

      old = receiver.set_attribute_node(a)
      detached.reject! { |x| x.equal?(a) }
      detached << old if old && !old.equal?(a)
      old
    when "removeAttributeNode"
      raise NotImplementedError, op["op"] unless receiver.respond_to?(:remove_attribute_node)

      a = find_attr(ctx, op["attr"])
      raise NotImplementedError, "missing attr" if a.nil?

      removed = receiver.remove_attribute_node(a)
      detached << removed if removed
      removed
    else
      map = receiver.respond_to?(:attributes) ? receiver.attributes : nil
      raise NotImplementedError, op["op"] if map.nil? || !map.respond_to?(:remove_named_item)

      removed = map.remove_named_item(op["name"].to_s)
      # 仕様では無ければ NotFoundError。nil を返す実装はそこを実装していない。
      raise NotImplementedError, "removeNamedItem returned nil" if removed.nil?

      detached << removed
      removed
    end
  end

  # id で `Attr` object を引く。
  def find_attr(ctx, aid)
    ctx[:attr_ids].each { |a, id| return a if id == aid }
    nil
  end

  # `Node` を受ける field が `{"attr": id}`（`Attr`）か。
  def attr_ref?(value)
    value.is_a?(Hash) && value.key?("attr")
  end

  # `Node` を受ける field を object にする。数なら node、`{"attr": id}` なら `Attr`。
  def resolve_ref(ctx, value)
    obj = attr_ref?(value) ? find_attr(ctx, value["attr"]) : ctx[:objects][value]
    raise NotImplementedError, attr_ref?(value) ? "missing attr" : "missing node" if obj.nil?

    obj
  end

  # 引数の `Attr` が element から外れていたら、detach された list に入れる。
  def track_detached(ctx, attr)
    return unless attr_object?(attr) && attr.owner_element.nil?
    return if ctx[:detached].any? { |x| x.equal?(attr) }

    ctx[:detached] << attr
  end

  # `Attr` を `Node` として読む `attrQuery`。
  def apply_attr_query(ctx, op)
    a = find_attr(ctx, op["attr"])
    raise NotImplementedError, "missing attr" if a.nil?

    case op["query"]
    when "getRootNode", "hasChildNodes" then js_call(a, op["query"], [])
    else js_get(a, op["query"])
    end
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
    when "attrQuery"
      return apply_attr_query(ctx, op)
    when "setAttrValue"
      # `Attr.value`・`nodeValue`・`textContent` の setter。どれも "set an existing attribute value"。
      a = find_attr(ctx, op["attr"])
      raise NotImplementedError, "missing attr" if a.nil?

      via = op["via"] || "value"
      setter = "#{via.gsub(/([A-Z])/) { "_#{Regexp.last_match(1).downcase}" }}="
      if a.respond_to?(setter)
        a.public_send(setter, op["value"].to_s)
      elsif !a.respond_to?(:__js_set__) || a.__js_set__(via, op["value"].to_s) == Dommy::Bridge::UNHANDLED
        raise NotImplementedError, via
      end
      return nil
    when "appendChild"
      if attr_ref?(op["parent"]) || attr_ref?(op["node"])
        parent = resolve_ref(ctx, op["parent"])
        # `Attr` は `appendChild` を bridge（`__js_call__`）にだけ持つ。
        return js_call(parent, "appendChild", [resolve_ref(ctx, op["node"])])
      end
    when *CREATE_OPS
      doc = objects[op["document"]]
      raise NotImplementedError, "missing node" if doc.nil?
      raise NotImplementedError, op["op"] unless doc.respond_to?(OP_METHOD.fetch(op["op"]))

      src = nil
      src = resolve_ref(ctx, op["node"]) if %w[importNode adoptNode].include?(op["op"])
      node =
        case op["op"]
        when "createElement" then doc.create_element(op["localName"].to_s)
        when "createElementNS" then doc.create_element_ns(op["namespace"], op["name"].to_s)
        when "createTextNode" then doc.create_text_node(op["data"].to_s)
        when "createComment" then doc.create_comment(op["data"].to_s)
        when "createDocumentFragment" then doc.create_document_fragment
        when "importNode" then doc.import_node(src, op["deep"] ? true : false)
        when "adoptNode" then doc.adopt_node(src)
        end
      if attr_object?(node)
        # `Attr` の import は detach された `Attr` を作る。adopt は element から外れたときだけ list に入れる
        # （仕様の本文は外さないが、外す実装がある）。
        op["op"] == "importNode" ? ctx[:detached] << node : track_detached(ctx, node)
        return node
      end
      # adoptNode は node を作らない。渡した node がそのまま返るので id は既にある。
      register_subtree(ctx, node) unless op["op"] == "adoptNode"
      return node
    when *ATTR_NODE_OPS
      return apply_attr_node(ctx, op)
    when "cloneNode"
      src = resolve_ref(ctx, op["node"])
      # `Attr` は `cloneNode` を bridge（`__js_call__`）にだけ持つ。
      copy = js_call(src, "cloneNode", [op["deep"] ? true : false])
      if attr_object?(copy)
        ctx[:detached] << copy
        return copy
      end
      register_subtree(ctx, copy)
      return copy
    end

    case op["op"]
    when "dispatchEvent"
      target = objects[op["target"]]
      raise NotImplementedError, "missing node" if target.nil?

      event = Dommy::Event.new(op["type"].to_s,
                               { "bubbles" => !!op["bubbles"], "cancelable" => !!op["cancelable"] })
      return target.dispatch_event(event)
    when "addEventListener"
      target = objects[op["target"]]
      raise NotImplementedError, "missing node" if target.nil?

      cb = (ctx[:callbacks] || [])[op["source"]]
      raise NotImplementedError, "listener index" if cb.nil?

      return target.add_event_listener(op["type"].to_s, cb,
                                       { "capture" => !!op["capture"], "once" => !!op["once"] })
    when "removeEventListener"
      target = objects[op["target"]]
      raise NotImplementedError, "missing node" if target.nil?

      cb = (ctx[:callbacks] || [])[op["callback"]]
      raise NotImplementedError, "listener index" if cb.nil?

      return target.remove_event_listener(op["type"].to_s, cb, { "capture" => !!op["capture"] })
    end

    if QUERY_OPS.include?(op["op"])
      receiver = op.key?("element") ? objects[op["element"]] : resolve_ref(ctx, op["node"])
      raise NotImplementedError, "missing node" if receiver.nil?

      name = QUERY_JS_NAME.fetch(op["op"])
      return js_get(receiver, name) if QUERY_GETTERS.include?(op["op"])

      if SELECTOR_OPS.include?(op["op"])
        kinds = SELECTOR_ELEMENT_OPS.include?(op["op"]) ? [1] : [1, 9, 11]
        # 種別が合わないなら実装と同じく TypeError。合っているのに method が無いなら実装漏れ。
        raise TypeError, "#{name} is not a function" unless kinds.include?(node_type_of(receiver))

        return js_call(receiver, name, [op["selectors"]])
      end

      if (lookup = LOOKUP_OPS[op["op"]])
        field, kinds = lookup
        raise TypeError, "#{name} is not a function" unless kinds.include?(node_type_of(receiver))

        return js_call(receiver, name, [op[field].to_s])
      end

      return case op["op"]
             when "compareDocumentPosition", "nodeContains", "isEqualNode"
               js_call(receiver, name, [resolve_ref(ctx, op["other"])])
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

      # `"node": null` は「Node でない引数」である。WebIDL は step に入る前に
      # 引数を変換するので、そのまま渡して TypeError を見る。
      # 存在しない id はこちらでは作りようが無いので、従来どおり比較から外す。
      node =
        if !op.key?("node") || op["node"].nil?
          nil
        else
          objects[op["node"]] ||
            raise(NotImplementedError, "missing node")
        end

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
    if REFLECT_OPS.include?(op["op"])
      receiver = objects[op["element"] || op["node"]]
      raise NotImplementedError, op["op"] if receiver.nil?

      return case op["op"]
             when "getReflected" then js_get(receiver, op["property"])
             when "setReflected"
               v = op["value"]
               js_set(receiver, op["property"], [true, false].include?(v) ? v : v.to_s)
             when "datasetGet", "datasetSet", "datasetDelete", "datasetKeys"
               # `dataset` は HTMLOrSVGOrMathMLElement mixin の attribute。Dommy がその mixin を持つなら、
               # 含まない element（namespace が null の element など）では JS と同じく undefined で、
               # そこから名前を引くと TypeError。mixin の無い Dommy では従来どおり比べられないとする。
               mixin = defined?(Dommy::Internal::HTMLOrSVGOrMathMLElement) && Dommy::Internal::HTMLOrSVGOrMathMLElement
               raise TypeError, "dataset is undefined" if mixin && !receiver.is_a?(mixin)

               # `DOMStringMap` は名前付き property なので、Ruby の method ではなく bridge で触る。
               map = js_get(receiver, "dataset")
               raise NotImplementedError, "dataset" if map.nil?

               dataset_op(map, op)
             when "childrenNamedItem"
               js_call(js_get(receiver, "children"), "namedItem", [op["key"].to_s])
             else
               list = js_get(receiver, "classList")
               case op["op"]
               when "classListAdd" then js_call(list, "add", (op["tokens"] || []).map(&:to_s))
               when "classListRemove" then js_call(list, "remove", (op["tokens"] || []).map(&:to_s))
               when "classListToggle"
                 args = [op["token"].to_s]
                 args << op["force"] if op.key?("force") && !op["force"].nil?
                 js_call(list, "toggle", args)
               when "classListReplace"
                 js_call(list, "replace", [op["token"].to_s, op["newToken"].to_s])
               when "classListContains" then js_call(list, "contains", [op["token"].to_s])
               end
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
    invocation_log = []
    callbacks = build_listeners(objects, scenario["listeners"], invocation_log)
    observers, delivery_log = build_observers(objects, builder.documents, scenario["observers"])
    ctx = { objects: objects, kinds: kinds, ranges: ranges, iterators: iterators,
            walkers: walkers, observers: observers, documents: builder.documents,
            callbacks: callbacks, attr_ids: {}.compare_by_identity, detached: [] }
    initial = snapshot(ctx, ranges, iterators,
                       observers.empty? ? nil : queued_records(objects, observers), walkers)
                .merge("delivered" => [])
    steps = []
    (scenario["operations"] || []).each do |op|
      delivery_log.clear
      invocation_log.clear
      begin
        returned = apply(objects, op, iterators, ctx)
      rescue NotImplementedError, NoMethodError => e
        # この harness で比べられない step。理由を残しておくと、
        # harness の制約と Dommy の実装漏れを取り違えずに済む。
        steps << { "ok" => false, "exception" => UNSUPPORTED,
                   "reason" => "#{e.class}: #{e.message}" }
        break
      rescue StandardError => e
        # 失敗した操作は状態を変えてはならない。
        # 変えていないことを比べられるように、失敗した step でも観測を出す。
        recs = observers.empty? ? nil : queued_records(objects, observers)
        steps << snapshot(ctx, ranges, iterators, recs, walkers)
                 .merge("ok" => false, "exception" => exception_name(e),
                        "delivered" => delivered_snapshot(delivery_log),
                        "invocations" => invocation_log.dup)
        break
      end
      recs = observers.empty? ? nil : queued_records(objects, observers)
      steps << snapshot(ctx, ranges, iterators, recs, walkers)
               .merge("ok" => true, "delivered" => delivered_snapshot(delivery_log),
                      "invocations" => invocation_log.dup,
                      "returned" => return_value_snapshot(ctx, op, returned))
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
      ops += REFLECT_OPS if node.respond_to?(:class_list)
      ops << "childrenNamedItem" if node.respond_to?(:children) && !ops.include?("childrenNamedItem")
      [kind, ops]
    end.to_h
  end

  # 出力 file は入力として扱わない。
  def scenario_file?(path)
    path.end_with?(".json") && !path.end_with?(".lean.json") && !path.end_with?(".impl.json")
  end

  # `DIR/*.json` をまとめて評価し、それぞれ `DIR/<base>.impl.json` に書く。
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
      File.write(File.join(dir, "#{base}.impl.json"), JSON.generate(out))
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
