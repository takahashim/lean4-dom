# frozen_string_literal: true

# 複数の DOM 実装を、同じ scenario で横に並べる。
#
#   ruby test/compare_impls.rb [--count N] [--seed N] --impl NAME=COMMAND ...
#
# **oracle は Lean の model だけである。** ここで並ぶ実装はどれも準拠度を
# 測られる側であって、食い違いを多数決で決めることはしない。
# 並べる意味は別のところにある。**model だけが孤立している行**が見えることである。
# そこは仕様の読み違いを疑う場所で、`docs/threats-to-validity.md` §5 が言う危険が
# 実際に出るとしたらそこである。
#
# scenario は全実装で同じものを使う。実装ごとの capabilities で生成を絞ると
# 集合が変わって横に並べられないので、ここでは絞らない。
# 実装が持っていない操作はその step で `__unsupported__` になり、skip として数える。
#
# 例:
#
#   BUNDLE_GEMFILE=/path/to/dommy/Gemfile ruby test/compare_impls.rb --count 80 --seed 7 \
#     --impl "dommy=bundle exec ruby test/dommy_runner.rb" \
#     --impl "jsdom=node test/js_runner.mjs --impl /path/to/jsdom/lib/api.js" \
#     --impl "happy-dom=node test/js_runner.mjs --impl /path/to/happy-dom/packages/happy-dom/lib/index.js"

require "json"
require "optparse"
require "open3"
require "tmpdir"
require "fileutils"
require_relative "generate"
require_relative "compare"
require_relative "known_divergences"

module CompareImpls
  ROOT = File.expand_path("..", __dir__)

  module_function

  def lean_command
    return ENV["DOM_MODEL"].split if ENV["DOM_MODEL"]

    built = File.join(ROOT, ".lake/build/bin/dom-model")
    _, err, status = Open3.capture3("lake", "build", "dom-model", chdir: ROOT)
    abort "oracle の build に失敗した:\n#{err}" unless status.success?

    [built]
  end

  # 比較の土台になる scenario を dir に並べる。
  # 固定 scenario のうち `_basis.comparable` が false のものは model 固有なので外す。
  def collect_scenarios(dir, count, seed)
    Dir[File.join(ROOT, "test/scenarios/*.json")].sort.each do |path|
      next if path.end_with?(".lean.json", ".impl.json")
      next if model_only?(path)

      FileUtils.cp(path, dir)
    end
    return unless count.positive?

    rng = Random.new(seed)
    ops = Generate::OPS + Generate::ITERATOR_OPS + Generate::OBSERVER_OPS + Generate::WALKER_OPS
    count.times do |i|
      sc = Generate.scenario(rng, node_count: 8, op_count: 6, ops: ops, allow: nil,
                             doctype_prob: 0.0, range_count: 3, iterator_count: 1,
                             observer_count: 1, walker_count: 1, listener_count: 1)
      File.write(File.join(dir, format("gen%04d.json", i)), JSON.generate(sc))
    end
  end

  def model_only?(path)
    JSON.parse(File.read(path)).dig("_basis", "comparable") == false
  rescue StandardError
    false
  end

  # 実装ごとに scenario を複製して評価する。出力は `<base>.impl.json` 固定なので、
  # 同じ dir で二つの実装を走らせることはできない。
  def evaluate(src, impls)
    impls.to_h do |name, command|
      Dir.mktmpdir("impl-#{name}") do |dir|
        Dir[File.join(src, "*.json")].each { |p| FileUtils.cp(p, dir) }
        run(lean_command + ["--batch", dir], "Lean")
        run(command.split + ["--batch", dir], name)
        ENV["IMPL_NAME"] = name
        [name, Compare.compare_dir(dir).transform_values { |(st, msg)| [st, msg] }
                      .to_h { |base, (st, msg)| [base, KnownDivergences.apply(name, base, st, msg)] }]
      end
    end
  end

  def run(cmd, label)
    _, err, status = Open3.capture3(*cmd)
    return if status.success?

    warn "警告: #{label} の --batch が exit #{status.exitstatus} を返した"
    warn err.lines.first(3).join unless err.to_s.empty?
  end

  SYMBOL = { match: "o", unsupported: "s", mismatch: "X", known: "k", error: "E" }.freeze

  def report(results)
    names = results.values.first.keys.sort
    impls = results.keys
    puts "== 集計（#{names.size} scenario）"
    printf("%-14s %6s %6s %6s %9s %6s\n", "", "ok", "skip", "known", "mismatch", "error")
    impls.each do |impl|
      c = Hash.new(0)
      names.each { |n| c[results[impl][n][0]] += 1 }
      printf("%-14s %6d %6d %6d %9d %6d\n", impl, c[:match], c[:unsupported], c[:known],
             c[:mismatch], c[:error])
    end
    puts
    puts "== 一致しない scenario（o=一致 s=比較不可 k=記録済み X=不一致 E=評価できず）"
    width = impls.map { |i| [i.size, 9].max }
    printf("%-52s %s\n", "scenario", impls.each_with_index.map { |i, k| i.rjust(width[k]) }.join(" "))
    outnumbered = []
    names.each do |n|
      row = impls.map { |impl| SYMBOL[results[impl][n][0]] }
      next if row.all? { |c| c == "o" }

      printf("%-52s %s\n", n, row.each_with_index.map { |c, k| c.rjust(width[k]) }.join(" "))
      outnumbered << [n, row.count("o")] if row.count("X") >= 2
    end
    return if outnumbered.empty?

    puts
    puts "== 二つ以上の実装が model と違う scenario"
    puts "多数決ではない。仕様の読み直しに値する場所、という印である。"
    puts "差分テストで直した実装は model の写しになっているので、"
    puts "その一致を独立した証拠として数えてはいけない。"
    outnumbered.each do |n, agreed|
      puts "  #{n}#{agreed.zero? ? "（一致した実装は無い）" : ""}"
    end
  end
end

if $PROGRAM_NAME == __FILE__
  opts = { count: 0, seed: 1, impls: {} }
  OptionParser.new do |o|
    o.on("--count N", Integer) { |v| opts[:count] = v }
    o.on("--seed N", Integer) { |v| opts[:seed] = v }
    o.on("--impl SPEC", "NAME=COMMAND") do |v|
      name, command = v.split("=", 2)
      abort "--impl は NAME=COMMAND の形で渡す" if command.nil?
      opts[:impls][name] = command
    end
  end.parse!
  abort "--impl を一つ以上渡す" if opts[:impls].empty?

  Dir.mktmpdir("scenarios") do |src|
    CompareImpls.collect_scenarios(src, opts[:count], opts[:seed])
    CompareImpls.report(CompareImpls.evaluate(src, opts[:impls]))
  end
end
