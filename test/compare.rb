# frozen_string_literal: true

# Lean の oracle と Dommy の出力を突き合わせる。
#
#   ruby test/compare.rb DIR
#
# `DIR/<base>.lean.json` と `DIR/<base>.dommy.json` の組を比較する。
# 出力の生成は次のとおり。
#
#   dom-model --batch DIR
#   bundle exec ruby test/dommy_runner.rb --batch DIR
#
# 比較対象は Lean 側の `Observation`（`Dom/Observation.lean`）である。
# node の kind / parent / 順序付き children / node document / data、
# そこから導いた tree order、live Range の両端、NodeIterator の三つ組、
# MutationObserver に積まれた record、操作の成否と例外、
# そして失敗した step で状態が変わっていないこと。

require "json"

module Compare
  UNSUPPORTED = "__unsupported__"

  # model 側が「この step は model の対象外」と言った印（`DOMException.outsideModel`）。
  #
  # 仕様の例外ではないので、実装側が同じところで失敗したとしても
  # 一致とは数えない。その step 以降を比較対象から外す。
  OUTSIDE_MODEL = "__outsideModel__"

  module_function

  # children から tree order（preorder）を導く。root は parent が nil の node。
  def tree_order(nodes)
    by_id = nodes.to_h { |n| [n["id"], n] }
    roots = nodes.reject { |n| n["parent"] }.map { |n| n["id"] }
    order = []
    walk = lambda do |id|
      order << id
      (by_id[id]&.fetch("children", []) || []).each { |c| walk.call(c) }
    end
    roots.sort.each { |r| walk.call(r) }
    order
  end

  # 比較に使う正規形。Lean 側の `ObservedNode` の field をそのまま並べる。
  def normalize_state(state)
    nodes = (state["nodes"] || []).sort_by { |n| n["id"] }
    {
      "nodes" => nodes.map { |n|
        n.slice("id", "kind", "parent", "children", "nodeDocument", "data", "attributes",
                "namespace", "prefix", "localName", "tagName")
      },
      "treeOrder" => tree_order(nodes),
      "ranges" => state["ranges"] || [],
      "iterators" => state["iterators"] || [],
      "observers" => state["observers"] || [],
      "delivered" => state["delivered"] || [],
      "returned" => state["returned"]
    }
  end

  def diff_state(a, b)
    na = normalize_state(a)
    nb = normalize_state(b)
    return nil if na == nb

    details = []
    if na["nodes"] != nb["nodes"]
      ids = (na["nodes"].map { |n| n["id"] } | nb["nodes"].map { |n| n["id"] }).sort
      ids.each do |id|
        x = na["nodes"].find { |n| n["id"] == id }
        y = nb["nodes"].find { |n| n["id"] == id }
        details << "  node #{id}: lean=#{x.inspect} dommy=#{y.inspect}" if x != y
      end
    end
    if na["treeOrder"] != nb["treeOrder"]
      details << "  treeOrder: lean=#{na['treeOrder']} dommy=#{nb['treeOrder']}"
    end
    if na["observers"] != nb["observers"]
      na["observers"].zip(nb["observers"]).each_with_index do |(x, y), i|
        details << "  observer #{i}: lean=#{x.inspect} dommy=#{y.inspect}" if x != y
      end
    end
    if na["delivered"] != nb["delivered"]
      details << "  delivered: lean=#{na['delivered'].inspect} dommy=#{nb['delivered'].inspect}"
    end
    if na["returned"] != nb["returned"]
      details << "  returned: lean=#{na['returned'].inspect} dommy=#{nb['returned'].inspect}"
    end
    details.join("\n")
  end

  # 戻り値は [status, messages]。status は :match / :mismatch / :unsupported / :error。
  def compare_outputs(lean, dommy)
    messages = []
    return [:error, ["Dommy 側でエラー: #{dommy['error']}"]] if dommy["error"]

    if (i = lean["invariantViolation"])
      messages << "step #{i} で model の invariant が破れている（model 側の不具合）"
    end

    if (d = diff_state(lean["initial"], dommy["initial"]))
      messages << "initial 状態が一致しない:\n#{d}"
      return [:mismatch, messages]
    end

    ls = lean["steps"]
    ds = dommy["steps"]
    unsupported = false
    [ls.size, ds.size].max.times do |i|
      l = ls[i]
      d = ds[i]
      if l && l["ok"] == false && l["exception"] == OUTSIDE_MODEL
        unsupported = true
        messages << "step #{i}: model の対象外なので比べられない" \
                    "（dommy=#{d && (d['ok'] ? 'ok' : d['exception'])}）"
        break
      end
      if d && d["ok"] == false && d["exception"] == UNSUPPORTED
        unsupported = true
        messages << "step #{i}: この harness では比べられない" \
                    "（lean=#{l && (l['ok'] ? 'ok' : l['exception'])}" \
                    "#{d['reason'] ? ", dommy=#{d['reason']}" : ''}）"
        break
      end
      if l.nil? || d.nil?
        messages << "step #{i}: step 数が違う（lean=#{ls.size} dommy=#{ds.size}）"
        return [:mismatch, messages]
      end
      if l["ok"] != d["ok"]
        messages << "step #{i}: 成否が違う（lean=#{l['ok'] ? 'ok' : l['exception']} " \
                    "dommy=#{d['ok'] ? 'ok' : d['exception']}）"
        return [:mismatch, messages]
      end
      unless l["ok"]
        if l["exception"] != d["exception"]
          messages << "step #{i}: 例外が違う（lean=#{l['exception']} dommy=#{d['exception']}）"
          return [:mismatch, messages]
        end
        # 失敗した操作は状態を変えてはならない。
        if d.key?("nodes") && (diff = diff_state(l, d))
          messages << "step #{i}: 例外の後の状態が一致しない（失敗した操作が状態を変えている）:\n#{diff}"
          return [:mismatch, messages]
        end
        next
      end
      if (diff = diff_state(l, d))
        messages << "step #{i}: 状態が一致しない:\n#{diff}"
        return [:mismatch, messages]
      end
    end

    [unsupported ? :unsupported : :match, messages]
  end

  # DIR の中の `<base>.lean.json` と `<base>.dommy.json` を突き合わせる。
  # 戻り値は base をキーにした [status, messages] の Hash。
  def compare_dir(dir)
    Dir[File.join(dir, "*.lean.json")].sort.to_h do |lean_path|
      base = File.basename(lean_path, ".lean.json")
      dommy_path = File.join(dir, "#{base}.dommy.json")
      result =
        if File.exist?(dommy_path)
          compare_outputs(JSON.parse(File.read(lean_path)), JSON.parse(File.read(dommy_path)))
        else
          [:error, ["#{base}.dommy.json が無い"]]
        end
      [base, result]
    end
  end
end

if $PROGRAM_NAME == __FILE__
  dir = ARGV[0] or abort "usage: compare.rb DIR"
  failed = 0
  Compare.compare_dir(dir).each do |base, (status, messages)|
    label = { match: "ok      ", unsupported: "skip    ", mismatch: "MISMATCH",
              error: "ERROR   " }.fetch(status)
    puts "#{label} #{base}"
    messages.each { |m| puts "  #{m}" } unless status == :match
    failed += 1 if %i[mismatch error].include?(status)
  end
  exit(failed.zero? ? 0 : 1)
end
