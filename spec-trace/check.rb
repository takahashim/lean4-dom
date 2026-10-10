# frozen_string_literal: true

# 仕様の step と Lean の対応表（`Trace/`）を、`spec-trace/dom.json` と突き合わせる。
#
#   ruby spec-trace/check.rb                       # 全体を検査する（`lake exe spec-trace` を走らせる）
#   ruby spec-trace/check.rb --write               # 加えて docs/spec-coverage.md と spec-trace/map.json を書き直す
#   ruby spec-trace/check.rb --check-doc           # docs/spec-coverage.md と spec-trace/map.json が最新かも検査する
#
# spec-trace/map.json は `lake exe spec-trace` の出力そのもので、`spec-trace/drift.rb` が
# build せずに表を読めるように commit しておく。
#   ruby spec-trace/check.rb --file Trace/Dom/Range.lean   # 一つのファイルだけを検査する
#
# 失敗にするもの：
#
#   * 表にある algorithm や step が仕様に無い
#   * 表に載せた algorithm に、どの entry も引き受けていない step がある
#   * `dom.json` の algorithm で、表にも対象外の一覧にも無いものがある（全体の検査のときだけ）
#   * 対象外の一覧の entry が何にも当たらない

require "json"
require "open3"
require "set"
require "tempfile"

ROOT = File.expand_path("..", __dir__)

module Trace
  class Check
    attr_reader :errors

    def initialize(snapshot, mapping, partial: false)
      @snap = snapshot
      @algs = snapshot["algorithms"].to_h { |a| [a["key"], a] }
      @entries = mapping["entries"]
      @exclusions = mapping["exclusions"]
      @partial = partial
      @errors = []
    end

    # selector を step 番号の集合にする。
    def select(alg, sel, where)
      nums = alg["steps"].map { |s| s["n"] }
      return nums.to_set if sel == "*"
      return error("#{where}: #{alg['key']} は step を持たない（\"*\" だけが書ける）: #{sel}") if nums.empty?

      lo, hi = sel.split("-", 2)
      hi ||= lo
      pl = lo.split(".")
      ph = hi.split(".")
      unless pl.size == ph.size && pl[0..-2] == ph[0..-2] && nums.include?(lo) && nums.include?(hi) &&
             pl.last.to_i <= ph.last.to_i
        return error("#{where}: #{alg['key']} に step #{sel} は無い（step は #{nums.first}〜#{nums.last}）")
      end

      prefix = pl[0..-2]
      (pl.last.to_i..ph.last.to_i).flat_map do |k|
        head = (prefix + [k.to_s]).join(".")
        nums.select { |n| n == head || n.start_with?("#{head}.") }
      end.to_set
    end

    def error(msg)
      @errors << msg
      Set.new
    end

    # algorithm ごとの step の状態を組む。
    def run
      @status = {}
      @entries.group_by { |e| e["alg"] }.each do |key, es|
        alg = @algs[key]
        unless alg
          error("表の algorithm #{key} は dom.json に無い")
          next
        end
        nums = alg["steps"].map { |s| s["n"] }
        st = { impl: Set.new, omit: {}, approx: {}, entries: es }
        es.each do |e|
          where = "#{key}（#{e['impl'].first}）"
          mine = e["steps"].map { |s| select(alg, s, where) }.reduce(Set.new, :|)
          st[:impl] |= mine
          e["omit"].each do |o|
            sel = select(alg, o["steps"], where)
            error("#{where}: omit の #{o['steps']} は steps の外") unless sel.subset?(mine) || sel.empty? && nums.empty?
            sel.each { |n| st[:omit][n] = o["why"] }
            st[:omit]["*"] = o["why"] if nums.empty?
          end
          e["approx"].each do |o|
            sel = select(alg, o["steps"], where)
            error("#{where}: approx の #{o['steps']} は steps の外") unless sel.subset?(mine) || nums.empty?
            sel.each { |n| st[:approx][n] = o["what"] }
            st[:approx]["*"] = o["what"] if nums.empty?
          end
        end
        missing = nums.reject { |n| st[:impl].include?(n) }
        unless missing.empty?
          error("#{key}: どの entry も引き受けていない step がある: #{compress(missing)}")
        end
        @status[key] = st
      end

      @excluded = {}
      @exclusions.each do |x|
        t = x["target"]
        hits = @algs.values.select { |a| a["key"] == t || a["headings"].include?(t) }
        error("対象外の #{t} は dom.json のどの algorithm にも見出しにも当たらない") if hits.empty?
        hits.each do |a|
          if @status.key?(a["key"])
            error("#{a['key']} は表にあるのに対象外にもされている") if a["key"] == t
            next
          end
          @excluded[a["key"]] = x["why"]
        end
      end

      unless @partial
        rest = @algs.keys.reject { |k| @status.key?(k) || @excluded.key?(k) }
        rest.each { |k| error("#{k}（§#{@algs[k]['section']}、line #{@algs[k]['line']}）は表にも対象外にも無い") }
      end
      self
    end

    # 連続する step 番号を範囲にまとめて表示する。
    def compress(nums)
      nums.chunk_while { |a, b| a.split(".")[0..-2] == b.split(".")[0..-2] && a.split(".").last.to_i + 1 == b.split(".").last.to_i }
          .map { |c| c.size == 1 ? c.first : "#{c.first}-#{c.last}" }.join(", ")
    end

    # step ごとの状態。入れ子の step がすべて外れている親の step も外れたと数える
    # （「各 descendant について」のような枠だけの step を実装済みと数えないため）。
    def states(key)
      alg = @algs[key]
      st = @status[key]
      if alg["steps"].empty?
        return { "*" => st[:omit]["*"] ? :omit : st[:approx]["*"] ? :approx : :impl }
      end
      out = {}
      alg["steps"].reverse_each do |s|
        n = s["n"]
        kids = alg["steps"].select { |c| c["n"].start_with?("#{n}.") && c["n"].count(".") == n.count(".") + 1 }
        out[n] =
          if st[:omit][n] || (kids.any? && kids.all? { |c| out[c["n"]] == :omit })
            :omit
          elsif st[:approx][n]
            :approx
          else
            :impl
          end
      end
      out
    end

    def counts(key)
      c = Hash.new(0)
      states(key).each_value do |v|
        c[:total] += 1
        c[v] += 1
      end
      c
    end

    def snapshot_url(key)
      "https://dom.spec.whatwg.org/commit-snapshots/#{@snap['commit']}/##{key.sub(%r{/setter\z}, '')}"
    end

    def reason_text(why)
      why["detail"].to_s.empty? ? why["reason"] : "#{why['reason']}：#{why['detail']}"
    end

    def section_key(sec)
      (sec || "0").split(".").map(&:to_i)
    end

    def summary
      algs = @algs.values
      mapped = algs.count { |a| @status.key?(a["key"]) }
      excluded = algs.count { |a| @excluded.key?(a["key"]) }
      tot = Hash.new(0)
      @status.each_key { |k| counts(k).each { |kk, v| tot[kk] += v } }
      { algorithms: algs.size, mapped: mapped, excluded: excluded, steps: tot }
    end

    def markdown
      s = summary
      out = +""
      out << "# 仕様の step との対応（自動生成）\n\n"
      out << "このファイルは `ruby spec-trace/check.rb --write` が `Trace/` の対応表と `spec-trace/dom.json` から作る。手で編集しない。\n\n"
      out << "対象は `dom.bs` commit `#{@snap['commit']}` である。"
      out << "algorithm の鍵は描画された仕様の anchor で、各行はその commit の snapshot に張ってある。\n\n"
      out << "| 項目 | 数 |\n| --- | --- |\n"
      out << "| `dom.bs` の algorithm | #{s[:algorithms]} |\n"
      out << "| 表に載せたもの | #{s[:mapped]} |\n"
      out << "| 対象外としたもの | #{s[:excluded]} |\n"
      out << "| 表に載せた algorithm の step | #{s[:steps][:total]} |\n"
      out << "| そのうち実装したもの | #{s[:steps][:impl]} |\n"
      out << "| そのうち近似したもの | #{s[:steps][:approx]} |\n"
      out << "| そのうち外したもの | #{s[:steps][:omit]} |\n\n"
      out << "step の数は入れ子の step も一つと数える。step を持たない一文の algorithm は一つと数える。\n"
      out << "「関係」の列は `Dom/Spec/` にある、仕様本文から独立に書いた関係である。\n\n"

      out << "## 表に載せた algorithm\n\n"
      @algs.values.select { |a| @status.key?(a["key"]) }.group_by { |a| a["section"] }
           .sort_by { |sec, _| section_key(sec) }.each do |sec, as|
        out << "### §#{sec}（`#{as.first['heading']}`）\n\n"
        out << "| algorithm | step | 実行関数 | 関係 |\n| --- | --- | --- | --- |\n"
        as.each do |a|
          st = @status[a["key"]]
          c = counts(a["key"])
          steps = "#{c[:impl]}/#{c[:total]}"
          steps += "（近似 #{c[:approx]}）" if c[:approx].positive?
          impl = st[:entries].flat_map { |e| e["impl"] }.uniq.map { |n| "`#{n}`" }.join("<br>")
          spec = st[:entries].flat_map { |e| e["spec"] }.uniq.map { |n| "`#{n}`" }.join("<br>")
          out << "| [#{a['key']}](#{snapshot_url(a['key'])}) | #{steps} | #{impl} | #{spec} |\n"
        end
        out << "\n"
      end

      out << "## 外した step\n\n"
      out << "| algorithm | step | 理由 |\n| --- | --- | --- |\n"
      @status.sort_by { |k, _| [section_key(@algs[k]["section"]), @algs[k]["line"]] }.each do |k, st|
        st[:entries].each do |e|
          e["omit"].each { |o| out << "| #{k} | #{o['steps']} | #{reason_text(o['why'])} |\n" }
        end
      end
      out << "\n## 近似した step\n\n"
      out << "| algorithm | step | 仕様との違い |\n| --- | --- | --- |\n"
      @status.sort_by { |k, _| [section_key(@algs[k]["section"]), @algs[k]["line"]] }.each do |k, st|
        st[:entries].each do |e|
          e["approx"].each { |o| out << "| #{k} | #{o['steps']} | #{o['what']} |\n" }
        end
      end

      out << "\n## 対象外とした algorithm\n\n"
      out << "| 理由 | algorithm |\n| --- | --- |\n"
      @excluded.group_by { |_, why| reason_text(why) }.sort.each do |why, ks|
        out << "| #{why} | #{ks.map { |k, _| k }.sort.join(', ')} |\n"
      end
      out
    end
  end
end

def lean_json_for_file(path)
  rel = path.sub(%r{\A#{Regexp.escape(ROOT)}/}, "")
  ns = rel.sub(/\.lean\z/, "").tr("/", ".")
  src = File.read(File.join(ROOT, rel))
  Tempfile.create(["trace", ".lean"]) do |f|
    f.write(src)
    f.write("\n#eval IO.println (Trace.render #{ns}.entries #{ns}.exclusions)\n")
    f.flush
    out, err, st = Open3.capture3("lake", "env", "lean", f.path, chdir: ROOT)
    abort("lean failed for #{rel}:\n#{out}#{err}") unless st.success?
    JSON.parse(out[out.index("{\"entries\"")..])
  end
end

def lean_json_all
  out, err, st = Open3.capture3("lake", "exe", "spec-trace", chdir: ROOT)
  abort("lake exe spec-trace failed:\n#{out}#{err}") unless st.success?
  JSON.parse(out)
end

if $PROGRAM_NAME == __FILE__
  file = nil
  write = false
  check_doc = false
  snapshot = File.join(ROOT, "spec-trace/dom.json")
  doc = File.join(ROOT, "docs/spec-coverage.md")
  map_path = File.join(ROOT, "spec-trace/map.json")
  while (a = ARGV.shift)
    case a
    when "--file" then file = ARGV.shift
    when "--write" then write = true
    when "--check-doc" then check_doc = true
    when "--snapshot" then snapshot = ARGV.shift
    else abort "unknown option #{a}"
    end
  end
  snap = JSON.parse(File.read(snapshot))
  mapping = file ? lean_json_for_file(File.expand_path(file)) : lean_json_all
  chk = Trace::Check.new(snap, mapping, partial: !file.nil?).run
  s = chk.summary
  puts "algorithms: #{s[:algorithms]} / mapped #{s[:mapped]} / excluded #{s[:excluded]}"
  puts "steps of mapped algorithms: #{s[:steps][:total]} / implemented #{s[:steps][:impl]} / " \
       "approximated #{s[:steps][:approx]} / omitted #{s[:steps][:omit]}"
  unless chk.errors.empty?
    chk.errors.each { |e| warn "error: #{e}" }
    abort "#{chk.errors.size} error(s)"
  end
  md = chk.markdown
  map = "#{JSON.pretty_generate(mapping)}\n"
  if write && !file
    File.write(doc, md)
    File.write(map_path, map)
    puts "wrote #{doc} and #{map_path}"
  end
  if check_doc
    [[doc, md], [map_path, map]].each do |path, want|
      next if File.exist?(path) && File.read(path) == want

      abort "#{path.sub("#{ROOT}/", '')} が古い。ruby spec-trace/check.rb --write で作り直す"
    end
  end
end
