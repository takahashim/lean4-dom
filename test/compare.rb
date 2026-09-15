# frozen_string_literal: true

# Lean の oracle と、検査対象の実装の出力を突き合わせる。
#
#   ruby test/compare.rb DIR
#
# `DIR/<base>.lean.json` と `DIR/<base>.impl.json` の組を比較する。
# 出力の生成は次のとおり。
#
#   dom-model --batch DIR
#   <実装の runner> --batch DIR
#
# **oracle は Lean の model だけである。** もう一方は準拠度を測られる側であって、
# 食い違いは実装側の findings として扱う（多数決はしない。
# `docs/threats-to-validity.md` の「Dommy の不一致」の判定を参照）。
# 実装の名前は `IMPL_NAME` で差し替える。出力の表示に出るだけで、判定は変わらない。
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

  # 表示に使う実装の名前。判定には効かない。
  def impl_label
    ENV.fetch("IMPL_NAME", "impl")
  end

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

  # `compareDocumentPosition` の実装依存の枝を落とす。
  #
  # 仕様 §4.4 step 6 は、同じ木にない二つの node について
  # DISCONNECTED と IMPLEMENTATION_SPECIFIC に PRECEDING か FOLLOWING を足した値を返せと言い、
  # **どちらにするかは実装に任せている**（一貫していることだけを求める）。
  # そこを比べると実装ごとの選択の違いが不一致として出てしまうので、
  # IMPLEMENTATION_SPECIFIC (0x20) が立っているときは PRECEDING|FOLLOWING (0x06) を落とす。
  # 一貫性そのものは model 側の定理
  # （`compareDocumentPosition_disconnected_consistent`）と固定 scenario で見る。
  def normalize_returned(returned)
    return returned unless returned.is_a?(Hash) && returned["kind"] == "number"

    value = returned["value"]
    return returned unless value.is_a?(Integer) && (value & 0x20) != 0

    returned.merge("value" => value & ~0x06)
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
      "walkers" => state["walkers"] || [],
      "observers" => state["observers"] || [],
      "delivered" => state["delivered"] || [],
      "invocations" => state["invocations"] || [],
      "returned" => normalize_returned(state["returned"])
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
        details << "  node #{id}: lean=#{x.inspect} #{impl_label}=#{y.inspect}" if x != y
      end
    end
    if na["treeOrder"] != nb["treeOrder"]
      details << "  treeOrder: lean=#{na['treeOrder']} #{impl_label}=#{nb['treeOrder']}"
    end
    if na["walkers"] != nb["walkers"]
      na["walkers"].zip(nb["walkers"]).each_with_index do |(x, y), i|
        details << "  walker #{i}: lean=#{x.inspect} #{impl_label}=#{y.inspect}" if x != y
      end
    end
    if na["observers"] != nb["observers"]
      na["observers"].zip(nb["observers"]).each_with_index do |(x, y), i|
        details << "  observer #{i}: lean=#{x.inspect} #{impl_label}=#{y.inspect}" if x != y
      end
    end
    if na["invocations"] != nb["invocations"]
      details << "  invocations: lean=#{na['invocations'].inspect} #{impl_label}=#{nb['invocations'].inspect}"
    end
    if na["delivered"] != nb["delivered"]
      details << "  delivered: lean=#{na['delivered'].inspect} #{impl_label}=#{nb['delivered'].inspect}"
    end
    if na["returned"] != nb["returned"]
      details << "  returned: lean=#{na['returned'].inspect} #{impl_label}=#{nb['returned'].inspect}"
    end
    details.join("\n")
  end

  # 戻り値は [status, messages]。status は :match / :mismatch / :unsupported / :error。
  def compare_outputs(lean, impl)
    messages = []
    return [:error, ["#{impl_label} 側でエラー: #{impl['error']}"]] if impl["error"]

    if (i = lean["invariantViolation"])
      messages << "step #{i} で model の invariant が破れている（model 側の不具合）"
    end

    if (d = diff_state(lean["initial"], impl["initial"]))
      messages << "initial 状態が一致しない:\n#{d}"
      return [:mismatch, messages]
    end

    ls = lean["steps"]
    ds = impl["steps"]
    unsupported = false
    [ls.size, ds.size].max.times do |i|
      l = ls[i]
      d = ds[i]
      if l && l["ok"] == false && l["exception"] == OUTSIDE_MODEL
        unsupported = true
        messages << "step #{i}: model の対象外なので比べられない" \
                    "（#{impl_label}=#{d && (d['ok'] ? 'ok' : d['exception'])}）"
        break
      end
      if d && d["ok"] == false && d["exception"] == UNSUPPORTED
        unsupported = true
        messages << "step #{i}: この harness では比べられない" \
                    "（lean=#{l && (l['ok'] ? 'ok' : l['exception'])}" \
                    "#{d['reason'] ? ", #{impl_label}=#{d['reason']}" : ''}）"
        break
      end
      if l.nil? || d.nil?
        messages << "step #{i}: step 数が違う（lean=#{ls.size} #{impl_label}=#{ds.size}）"
        return [:mismatch, messages]
      end
      if l["ok"] != d["ok"]
        messages << "step #{i}: 成否が違う（lean=#{l['ok'] ? 'ok' : l['exception']} " \
                    "#{impl_label}=#{d['ok'] ? 'ok' : d['exception']}）"
        return [:mismatch, messages]
      end
      unless l["ok"]
        if l["exception"] != d["exception"]
          messages << "step #{i}: 例外が違う（lean=#{l['exception']} #{impl_label}=#{d['exception']}）"
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

  # DIR の scenario を両方の出力と突き合わせる。
  # 戻り値は base をキーにした [status, messages] の Hash。
  #
  # **基準は scenario（`<base>.json`）の側である。** 出力（`<base>.lean.json`）を
  # 基準にすると、評価できなかった scenario が報告から静かに消えて
  # 「全部 ok」に見えてしまう。古い binary が新しい操作を知らないときがそれで、
  # 実際に findings 8 の scenario がまるごと消えたまま緑になったことがある。
  def compare_dir(dir)
    inputs = Dir[File.join(dir, "*.json")].reject { |p| p.end_with?(".lean.json", ".impl.json") }
    inputs.sort.to_h do |input_path|
      base = File.basename(input_path, ".json")
      lean_path = File.join(dir, "#{base}.lean.json")
      impl_path = File.join(dir, "#{base}.impl.json")
      missing = []
      missing << "#{base}.lean.json が無い（Lean 側がこの scenario を評価できなかった）" \
        unless File.exist?(lean_path)
      missing << "#{base}.impl.json が無い（#{impl_label} 側がこの scenario を評価できなかった）" \
        unless File.exist?(impl_path)
      result =
        if missing.empty?
          compare_outputs(JSON.parse(File.read(lean_path)), JSON.parse(File.read(impl_path)))
        else
          [:error, missing]
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
