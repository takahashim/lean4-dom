# frozen_string_literal: true

# Lean の model と、検査対象の DOM 実装の differential testing の driver（PLAN §7）。
#
# **oracle は Lean の model だけである。** 実装側は準拠度を測られる相手であって、
# 食い違いは実装の findings として扱う。実装は runner を差し替えて選ぶ。
#
#   ruby test/difftest.rb [--count N] [--seed N] [--nodes N] [--ops N]
#                         [--move] [--all-ops] [--fixed-only]
#   ruby test/difftest.rb --shrink FILE   # 既にある scenario を最小化する
#
# この script 自身は実装を読み込まない。実装側の評価は別 process に投げる。
# Dommy の makiri を AddressSanitizer 付きで build している環境では、
# Dommy を読み込んだ process から fork できないためである。
#
# 環境変数
#   DOM_MODEL  Lean の oracle を呼ぶ command
#              （既定は .lake/build/bin/dom-model があればそれ、無ければ "lake exe dom-model"）
#   IMPL_CMD   検査対象の実装の runner を呼ぶ command
#              （既定 "bundle exec ruby test/dommy_runner.rb"。
#              古い名前 DOMMY_CMD も読む）
#              ASan 付きの makiri を使う環境では次のように指定する。
#                IMPL_CMD="env LD_PRELOAD=/usr/lib/x86_64-linux-gnu/libasan.so.8 \
#                          ASAN_OPTIONS=detect_leaks=0 bundle exec ruby test/dommy_runner.rb"
#   IMPL_NAME  表示に使う実装の名前（既定 "impl"）。判定には効かない。
#
# 既定では、実装が持っている (kind, 操作) の組だけを生成する。
# `--all-ops` を付けると仕様上の全 API を生成するので、未実装の箇所が可視化される。
# 不一致が見つかった scenario は最小化して `test/scenarios/` に保存する（PLAN §7.3）。
# 最小化は「操作 → 生きている object → node → 文字列」の順に一つずつ落とし、
# 不一致が保たれる限り落としたままにする。候補はまとめて評価するので、
# 1 round につき process 起動は 2 回で済む。

require "json"
require "optparse"
require "open3"
require "tmpdir"
require "fileutils"
require "set"
require_relative "generate"
require_relative "compare"
require_relative "known_divergences"

module Difftest
  ROOT = File.expand_path("..", __dir__)

  module_function

  # Lean の oracle を呼ぶ command。
  #
  # `.lake/build/bin/dom-model` があってもそのまま使ってはいけない。**古い binary は
  # 新しい操作を知らず、その scenario の評価ごと失敗する**。出力が出ないだけなので、
  # 以前は比較から静かに消えて「全部 ok」に見えていた。使う前に必ず build し直す。
  def lean_command
    return ENV["DOM_MODEL"].split if ENV["DOM_MODEL"]

    @lean_command ||= built_oracle
  end

  def built_oracle
    built = File.join(ROOT, ".lake/build/bin/dom-model")
    begin
      _, err, status = Open3.capture3("lake", "build", "dom-model", chdir: ROOT)
    rescue Errno::ENOENT
      warn "警告: lake が無いので `#{built}` を古いかもしれないまま使う"
      return File.executable?(built) ? [built] : ["lake", "exe", "dom-model"]
    end
    abort "oracle の build に失敗した:\n#{err}" unless status.success?

    [built]
  end

  def impl_command
    (ENV["IMPL_CMD"] || ENV["DOMMY_CMD"] ||
      "bundle exec ruby #{File.join(__dir__, 'dommy_runner.rb')}").split
  end

  def impl_label
    Compare.impl_label
  end

  def run!(cmd, allow_failure: false)
    out, err, status = Open3.capture3(*cmd)
    unless status.success? || allow_failure
      raise "command failed: #{cmd.join(' ')}\n#{err}"
    end

    [out, err]
  end

  def capabilities
    @capabilities ||= JSON.parse(run!(impl_command + ["--capabilities"]).first)
  end

  def allow_lambda
    caps = capabilities
    ->(op, kind) { !kind.nil? && caps.fetch(kind, []).include?(op["op"]) }
  end

  # DIR の scenario を両方の実装で評価して比較する。
  def evaluate(dir)
    run_batch(lean_command, dir, "Lean")
    run_batch(impl_command, dir, impl_label)
    Compare.compare_dir(dir)
  end

  # `--batch` は scenario 一つの失敗では止まらない。終了コードが 0 でないのは
  # 「まるごと評価できなかった scenario がある」という意味なので、黙って進めない。
  # どの scenario かは `Compare.compare_dir` が ERROR として並べる。
  def run_batch(cmd, dir, label)
    _, err, status = Open3.capture3(*cmd, "--batch", dir)
    return if status.success?

    warn "警告: #{label} の --batch が exit #{status.exitstatus} を返した"
    warn err.lines.first(5).join unless err.to_s.empty?
  end

  # 候補の scenario をまとめて評価し、不一致になるものの index を返す。
  def mismatching(candidates)
    Dir.mktmpdir do |dir|
      candidates.each_with_index do |sc, i|
        File.write(File.join(dir, format("c%04d.json", i)), JSON.generate(sc))
      end
      results = evaluate(dir)
      results.filter_map do |base, (status, _)|
        base[/\Ac(\d+)\z/, 1]&.to_i if status == :mismatch
      end.sort
    end
  end

  # 操作が参照する node の id。scenario の全 field を見る。
  NODE_REF_KEYS = %w[parent node child target element other source].freeze

  # live object の collection と、それを index で指す操作の field。
  #
  # `listeners` の `callback` は宣言の番号ではなく callback の id なので付け替えない
  # （`materialize_callbacks` で明示してあるので、落としても他の listener に影響しない）。
  def index_fields(key, op)
    case key
    when "ranges"
      op["op"] == "rangeCompareBoundaryPoints" ? %w[range source] : %w[range]
    when "iterators" then %w[iterator]
    when "walkers" then %w[walker]
    when "observers" then %w[observer]
    when "listeners" then op["op"] == "addEventListener" ? %w[source] : []
    else []
    end
  end

  # listener の callback 番号を明示しておく。既定値は宣言の順なので、
  # 一つ落とすと残りの番号が動いてしまう。
  def materialize_callbacks(scenario)
    listeners = scenario["listeners"]
    return scenario if listeners.nil? || listeners.empty?

    scenario.merge("listeners" => listeners.each_with_index.map { |l, i|
      l.key?("callback") ? l : l.merge("callback" => i)
    })
  end

  # `k` 番を落としたときに、操作の index 参照を付け替える。落ちた番号を指す操作は捨てる。
  def reindex_ops(ops, key, k)
    ops.filter_map do |op|
      fields = index_fields(key, op)
      next op if fields.empty?
      next nil if fields.any? { |f| op[f] == k }

      fields.reduce(op) { |acc, f| acc[f].is_a?(Integer) && acc[f] > k ? acc.merge(f => acc[f] - 1) : acc }
    end
  end

  # listener の action が持つ listener 番号も同じように付け替える。
  def reindex_listeners(listeners, key, k)
    return listeners unless key == "listeners"

    listeners.map do |l|
      a = l["action"]
      next l unless a.is_a?(Hash)

      field = { "removeListener" => "index", "addListener" => "source" }[a["kind"]]
      next l if field.nil? || !a[field].is_a?(Integer)
      next l.reject { |kk, _| kk == "action" } if a[field] == k

      a[field] > k ? l.merge("action" => a.merge(field => a[field] - 1)) : l
    end
  end

  # 生きている object を一つ落とした候補。
  def drop_live(scenario, key, k)
    list = scenario[key] || []
    dropped = scenario.merge(key => list.reject.with_index { |_, j| j == k })
    dropped = dropped.merge("listeners" => reindex_listeners(dropped["listeners"] || [], key, k)) if key == "listeners"
    dropped.merge("operations" => reindex_ops(dropped["operations"], key, k))
  end

  # 文字列を短くした候補。
  def string_candidates(scenario)
    out = []
    (scenario["nodes"] || []).each_with_index do |n, i|
      data = n["data"]
      next if data.nil? || data.empty?

      ["", data[0]].uniq.reject { |v| v == data }.each do |v|
        out << scenario.merge("nodes" => scenario["nodes"].each_with_index.map { |m, j|
          j == i ? m.merge("data" => v) : m
        })
      end
      next unless (attrs = n["attributes"])

      attrs.each_with_index do |a, ai|
        next if a["value"].nil? || a["value"].empty?

        out << scenario.merge("nodes" => scenario["nodes"].each_with_index.map { |m, j|
          next m unless j == i

          m.merge("attributes" => attrs.each_with_index.map { |b, bi| bi == ai ? b.merge("value" => "") : b })
        })
      end
    end
    out
  end

  # live object が指す node の id。落とした node を指したままにしないために見る。
  def live_node_refs(scenario)
    refs = []
    (scenario["ranges"] || []).each { |r| refs << r["start"]["node"] << r["end"]["node"] }
    %w[iterators walkers].each do |key|
      (scenario[key] || []).each { |o| refs << o["root"] << o["reference"] }
    end
    (scenario["observers"] || []).each { |o| refs << o["target"] }
    (scenario["listeners"] || []).each do |l|
      refs << l["target"]
      a = l["action"]
      refs << a["target"] if a.is_a?(Hash)
    end
    refs.compact
  end

  # range の両端が「木の中にあり、start が end 以下」であること。
  def ranges_sane?(scenario, nodes, by_id)
    (scenario["ranges"] || []).all? do |r|
      bps = [r["start"], r["end"]]
      next false unless bps.all? { |bp| bp["offset"] <= Generate.length_of(by_id[bp["node"]], nodes) }
      next false unless bps.map { |bp| Generate.root_of(by_id, bp["node"]) }.uniq.size == 1

      keys = bps.map { |bp| Generate.bp_key(nodes, by_id, bp["node"], bp["offset"]) }
      Generate.lex_compare(keys[0], keys[1]) <= 0
    end
  end

  # 最小化が壊してはいけない初期状態の条件。
  #
  # node を落とすと children の index が動くので、range の両端の順序が
  # 入れ替わることがある。文字列を縮めると offset が length を超える。
  # どちらも **実装では作れない初期状態**である（実装は `setStart` /
  # `setEnd` を通すので、逆順の端点はその場で畳まれる）。
  # そのまま候補にすると、最小化が元の不一致を離れて
  # 「初期状態の作り方が違う」という別の不一致へ逃げてしまう。
  def sane_scenario?(scenario)
    nodes = scenario["nodes"] || []
    by_id = Generate.index_by_id(nodes)
    return false unless live_node_refs(scenario).all? { |id| by_id.key?(id) }

    ranges_sane?(scenario, nodes, by_id)
  end

  # 候補を試し、まだ不一致なものがあればそれに進む。進めたかどうかを返す。
  def try_candidates(current, candidates)
    candidates = candidates.select { |c| sane_scenario?(c) }
    return [current, false] if candidates.empty?

    hits = mismatching(candidates)
    hits.empty? ? [current, false] : [candidates[hits.first], true]
  end

  # 不一致を保ったまま scenario を小さくする。
  #
  # 操作 → 生きている object → node → 文字列 の順に一つずつ落とし、
  # 一巡して何も落とせなくなるまで繰り返す。候補はまとめて評価するので、
  # 1 round につき process 起動は 2 回で済む。
  def shrink(scenario)
    current = materialize_callbacks(scenario)
    loop do
      progress = false

      # 操作
      loop do
        candidates = current["operations"].each_index.map do |i|
          current.merge("operations" => current["operations"].reject.with_index { |_, j| j == i })
        end
        current, moved = try_candidates(current, candidates)
        progress ||= moved
        break unless moved
      end

      # live object
      %w[ranges iterators walkers listeners observers].each do |key|
        loop do
          list = current[key] || []
          candidates = list.each_index.map { |k| drop_live(current, key, k) }
          current, moved = try_candidates(current, candidates)
          progress ||= moved
          break unless moved
        end
      end

      # node
      loop do
        used = current["operations"].flat_map { |op| op.values_at(*NODE_REF_KEYS) }.compact.to_set
        removable = current["nodes"].select do |n|
          !used.include?(n["id"]) && current["nodes"].none? { |m| m["parent"] == n["id"] }
        end
        candidates = removable.map { |n| current.merge("nodes" => current["nodes"] - [n]) }
        current, moved = try_candidates(current, candidates)
        progress ||= moved
        break unless moved
      end

      # 文字列
      loop do
        current, moved = try_candidates(current, string_candidates(current))
        progress ||= moved
        break unless moved
      end

      break unless progress
    end
    current
  end

  # 仕様がその kind に定めている操作のうち、実装に無いもの。
  # 仕様上そもそも無い操作（Document の ChildNode method など）は挙げない。
  def missing_operations
    capabilities.to_h { |kind, ops| [kind, Generate::SPEC_OPS.fetch(kind, []) - ops] }
  end

  def report_capabilities
    puts "仕様がその kind に定めている操作のうち、#{impl_label} に無いもの:"
    missing_operations.each do |kind, missing|
      puts format("  %-22s %s", kind, missing.empty? ? "(なし)" : missing.join(", "))
    end
    puts
  end
end

if $PROGRAM_NAME == __FILE__
  # doctype を初期状態に置く確率。既定は 0。
  # `DOMImplementation#createDocumentType` が作った wrapper が wrapper cache に
  # 登録されないため、`document.childNodes` が別の Ruby object を返し、
  # runner が node を同定できない（test/scenarios/doctype-wrapper-identity.json）。
  # 既定で混ぜると初期状態の時点で多数が不一致になり、
  # 操作の意味論の比較ができなくなる。
  opts = { count: 50, seed: Random.new_seed, nodes: 8, ops: 6,
           move: false, all: false, fixed_only: false, doctype: 0.0,
           ranges: 2, iterators: 1, observers: 0, walkers: 1, listeners: 0 }
  OptionParser.new do |o|
    o.on("--count N", Integer) { |v| opts[:count] = v }
    o.on("--seed N", Integer) { |v| opts[:seed] = v }
    o.on("--nodes N", Integer) { |v| opts[:nodes] = v }
    o.on("--ops N", Integer) { |v| opts[:ops] = v }
    o.on("--move") { opts[:move] = true }
    o.on("--all-ops") { opts[:all] = true }
    o.on("--fixed-only") { opts[:fixed_only] = true }
    o.on("--doctype-prob F", Float) { |v| opts[:doctype] = v }
    o.on("--ranges N", Integer) { |v| opts[:ranges] = v }
    o.on("--iterators N", Integer) { |v| opts[:iterators] = v }
    o.on("--observers N", Integer) { |v| opts[:observers] = v }
    o.on("--walkers N", Integer) { |v| opts[:walkers] = v }
    o.on("--listeners N", Integer) { |v| opts[:listeners] = v }
    # 特定の操作だけを生成する（新しく入れた API を集中して撫でるため）。
    o.on("--only-ops LIST", String) { |v| opts[:only] = v.split(",") }
    # 既にある scenario を最小化して標準出力に書く。
    o.on("--shrink FILE", String) { |v| opts[:shrink] = v }
  end.parse!

  if opts[:shrink]
    scenario = JSON.parse(File.read(opts[:shrink]))
    puts JSON.pretty_generate(Difftest.shrink(scenario))
    exit 0
  end

  Difftest.report_capabilities

  scenarios_dir = File.join(__dir__, "scenarios")
  all_fixed = Dir[File.join(scenarios_dir, "*.json")].reject do |p|
    p.end_with?(".lean.json", ".impl.json")
  end.sort
  # `_basis.comparable` が false の scenario は model 固有の近似を固定するためのもので、
  # 実装と突き合わせる対象ではない（`docs/traceability.md` の「対象外」を参照）。
  model_only, fixed = all_fixed.partition do |p|
    JSON.parse(File.read(p)).dig("_basis", "comparable") == false
  rescue StandardError
    false
  end

  unless model_only.empty?
    puts "model 固有（差分比較の対象外）:"
    model_only.each { |p| puts "  #{File.basename(p, '.json')}" }
    puts
  end
  failures = 0

  unless fixed.empty?
    puts "固定 scenario:"
    Dir.mktmpdir do |dir|
      fixed.each { |p| FileUtils.cp(p, dir) }
      Difftest.evaluate(dir).each do |base, (status, messages)|
        status, messages = KnownDivergences.apply(Compare.impl_label, base, status, messages)
        label = { match: "ok      ", unsupported: "skip    ", mismatch: "MISMATCH",
                  known: "known   ", error: "ERROR   " }.fetch(status)
        puts "  #{label} #{base}"
        messages.each { |m| puts "    #{m}" } unless status == :match
        failures += 1 if %i[mismatch error].include?(status)
      end
    end
    puts
  end

  unless opts[:fixed_only]
    ops = Generate::OPS + Generate::ITERATOR_OPS
    ops += Generate::OBSERVER_OPS if opts[:observers].to_i.positive?
    ops << "moveBefore" if opts[:move]
    ops = opts[:only] if opts[:only]
    allow = opts[:all] ? nil : Difftest.allow_lambda
    rng = Random.new(opts[:seed])
    generated = Array.new(opts[:count]) do
      Generate.scenario(rng, node_count: opts[:nodes], op_count: opts[:ops],
                             ops: ops, allow: allow, doctype_prob: opts[:doctype],
                             range_count: opts[:ranges], iterator_count: opts[:iterators],
                             observer_count: opts[:observers], walker_count: opts[:walkers],
                             listener_count: opts[:listeners])
    end
    puts "生成 scenario（seed=#{opts[:seed]}, count=#{opts[:count]}）:"
    stats = Hash.new(0)
    Dir.mktmpdir do |dir|
      generated.each_with_index do |sc, i|
        File.write(File.join(dir, format("gen%04d.json", i)), JSON.generate(sc))
      end
      Difftest.evaluate(dir).each do |base, (status, messages)|
        stats[status] += 1
        next unless %i[mismatch error].include?(status)

        failures += 1
        index = base[/\Agen(\d+)\z/, 1].to_i
        shrunk = status == :mismatch ? Difftest.shrink(generated[index]) : generated[index]
        name = format("failing-%s-%04d.json", opts[:seed].to_s[-6..] || opts[:seed], index)
        File.write(File.join(scenarios_dir, name), JSON.pretty_generate(shrunk))
        puts "  #{status.to_s.upcase} -> test/scenarios/#{name}"
        messages.each { |m| puts "    #{m}" }
      end
    end
    puts "  " + stats.map { |k, v| "#{k}=#{v}" }.join(" ")
  end

  exit(failures.zero? ? 0 : 1)
end
