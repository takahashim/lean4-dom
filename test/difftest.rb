# frozen_string_literal: true

# Lean の model と Dommy の differential testing の driver（PLAN §7）。
#
#   ruby test/difftest.rb [--count N] [--seed N] [--nodes N] [--ops N]
#                         [--move] [--all-ops] [--fixed-only]
#
# この script 自身は Dommy を読み込まない。Dommy 側の評価は別 process に投げる。
# makiri を AddressSanitizer 付きで build している環境では、
# Dommy を読み込んだ process から fork できないためである。
#
# 環境変数
#   DOM_MODEL  Lean の oracle を呼ぶ command
#              （既定は .lake/build/bin/dom-model があればそれ、無ければ "lake exe dom-model"）
#   DOMMY_CMD  Dommy の runner を呼ぶ command
#              （既定 "bundle exec ruby test/dommy_runner.rb"）
#              ASan 付きの makiri を使う環境では次のように指定する。
#                DOMMY_CMD="env LD_PRELOAD=/usr/lib/x86_64-linux-gnu/libasan.so.8 \
#                           ASAN_OPTIONS=detect_leaks=0 bundle exec ruby test/dommy_runner.rb"
#
# 既定では、Dommy が実装している (kind, 操作) の組だけを生成する。
# `--all-ops` を付けると仕様上の全 API を生成するので、未実装の箇所が可視化される。
# 不一致が見つかった scenario は最小化して `test/scenarios/` に保存する（PLAN §7.3）。

require "json"
require "optparse"
require "open3"
require "tmpdir"
require "fileutils"
require "set"
require_relative "generate"
require_relative "compare"

module Difftest
  ROOT = File.expand_path("..", __dir__)

  module_function

  def lean_command
    return ENV["DOM_MODEL"].split if ENV["DOM_MODEL"]

    built = File.join(ROOT, ".lake/build/bin/dom-model")
    File.executable?(built) ? [built] : ["lake", "exe", "dom-model"]
  end

  def dommy_command
    (ENV["DOMMY_CMD"] || "bundle exec ruby #{File.join(__dir__, 'dommy_runner.rb')}").split
  end

  def run!(cmd, allow_failure: false)
    out, err, status = Open3.capture3(*cmd)
    unless status.success? || allow_failure
      raise "command failed: #{cmd.join(' ')}\n#{err}"
    end

    [out, err]
  end

  def capabilities
    @capabilities ||= JSON.parse(run!(dommy_command + ["--capabilities"]).first)
  end

  def allow_lambda
    caps = capabilities
    ->(op, kind) { !kind.nil? && caps.fetch(kind, []).include?(op["op"]) }
  end

  # DIR の scenario を両方の実装で評価して比較する。
  def evaluate(dir)
    run!(lean_command + ["--batch", dir], allow_failure: true)
    run!(dommy_command + ["--batch", dir], allow_failure: true)
    Compare.compare_dir(dir)
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

  # 操作を一つずつ落として、まだ不一致なら落としたままにする。
  # 候補をまとめて評価するので、1 round につき process 起動は 2 回で済む。
  def shrink(scenario)
    current = scenario
    loop do
      candidates = current["operations"].each_index.map do |i|
        current.merge("operations" => current["operations"].reject.with_index { |_, j| j == i })
      end
      break if candidates.empty?

      hits = mismatching(candidates)
      break if hits.empty?

      current = candidates[hits.first]
    end

    used = current["operations"]
           .flat_map { |op| op.values_at("parent", "node", "child", "target") }.compact.to_set
    loop do
      removable = current["nodes"].select do |n|
        !used.include?(n["id"]) && current["nodes"].none? { |m| m["parent"] == n["id"] }
      end
      break if removable.empty?

      candidates = removable.map { |n| current.merge("nodes" => current["nodes"] - [n]) }
      hits = mismatching(candidates)
      break if hits.empty?

      current = candidates[hits.first]
    end
    current
  end

  def report_capabilities
    puts "Dommy が実装している操作（kind ごとに、仕様にあって Dommy に無いもの）:"
    all = Compare::UNSUPPORTED # placeholder to keep requires honest
    op_names = %w[appendChild insertBefore replaceChild removeChild replaceChildren
                  before after replaceWith remove moveBefore]
    capabilities.each do |kind, ops|
      missing = op_names - ops
      puts format("  %-22s %s", kind, missing.empty? ? "(なし)" : missing.join(", "))
    end
    puts
    all
  end
end

if $PROGRAM_NAME == __FILE__
  # doctype を初期状態に置く確率。既定は 0。
  # `document.appendChild(doctype)` が Dommy では何もしないため
  # （test/scenarios/doctype-append-to-empty-document.json に記録）、
  # 既定で混ぜると初期状態の時点でほぼ全部が不一致になり、
  # 操作の意味論の比較ができなくなる。
  opts = { count: 50, seed: Random.new_seed, nodes: 8, ops: 6,
           move: false, all: false, fixed_only: false, doctype: 0.0 }
  OptionParser.new do |o|
    o.on("--count N", Integer) { |v| opts[:count] = v }
    o.on("--seed N", Integer) { |v| opts[:seed] = v }
    o.on("--nodes N", Integer) { |v| opts[:nodes] = v }
    o.on("--ops N", Integer) { |v| opts[:ops] = v }
    o.on("--move") { opts[:move] = true }
    o.on("--all-ops") { opts[:all] = true }
    o.on("--fixed-only") { opts[:fixed_only] = true }
    o.on("--doctype-prob F", Float) { |v| opts[:doctype] = v }
  end.parse!

  Difftest.report_capabilities

  scenarios_dir = File.join(__dir__, "scenarios")
  fixed = Dir[File.join(scenarios_dir, "*.json")].reject do |p|
    p.end_with?(".lean.json", ".dommy.json")
  end.sort
  failures = 0

  unless fixed.empty?
    puts "固定 scenario:"
    Dir.mktmpdir do |dir|
      fixed.each { |p| FileUtils.cp(p, dir) }
      Difftest.evaluate(dir).each do |base, (status, messages)|
        label = { match: "ok      ", unsupported: "skip    ", mismatch: "MISMATCH",
                  error: "ERROR   " }.fetch(status)
        puts "  #{label} #{base}"
        messages.each { |m| puts "    #{m}" } unless status == :match
        failures += 1 if %i[mismatch error].include?(status)
      end
    end
    puts
  end

  unless opts[:fixed_only]
    ops = Generate::OPS.dup
    ops << "moveBefore" if opts[:move]
    allow = opts[:all] ? nil : Difftest.allow_lambda
    rng = Random.new(opts[:seed])
    generated = Array.new(opts[:count]) do
      Generate.scenario(rng, node_count: opts[:nodes], op_count: opts[:ops],
                             ops: ops, allow: allow, doctype_prob: opts[:doctype])
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
