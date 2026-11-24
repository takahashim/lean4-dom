# frozen_string_literal: true

# 固定 scenario の `_basis.refs`（期待結果の根拠にした仕様の step）を、固定版の snapshot と突き合わせる。
#
#   ruby spec-trace/basis.rb                  # test/scenarios/*.json を検査する
#   ruby spec-trace/basis.rb --fill FILE ...  # refs の text・last を snapshot から埋める（書くときに使う）
#   ruby spec-trace/basis.rb --fix            # 版を上げて番号がずれた ref を、本文の一致で付け直す
#   ruby spec-trace/basis.rb --since REV      # REV の時点から、根拠の step の本文が変わった scenario を挙げる
#
# ref の形：
#
#   {"alg": "concept-node-remove", "step": "15", "text": "Add transient registered observers"}
#   {"alg": "concept-node-remove", "step": "1-17", "text": "Let parent be node's parent", "last": "Run the children changed steps for parent"}
#   {"spec": "webidl", "alg": "abstract-opdef-converttoint", "step": "4", "text": "Let x be ? ToNumber(V)"}
#   {"alg": "concept-node-append"}            # 番号付きの step の無い algorithm、または algorithm 全体
#
# `spec` は dom（既定）・webidl・ecma262、`alg` は snapshot の key。`text` は step の本文の冒頭で、`last` は範囲の
# 最後の step の本文の冒頭。Bikeshed の link（`[=for/term|text=]`、`{{Interface/member}}`）は描画された語に読み替え、
# 大文字小文字と、英数字以外の文字（Bikeshed・ecmarkup の markup を含む）を無視して比べる。
#
# 失敗にするもの：
#
#   * snapshot に無い algorithm・step
#   * `text`（`last`）が、その番号の step の本文の冒頭と合わない（版を上げて改番されたときもここで落ちる）
#   * `text`（`last`）で、同じ親を持つ step から一つに決まらない（下の「step の決め方」）。`--fill` は決まるまで語を足す
#   * ref に spec・alg・step・text・last 以外の key がある
#   * 固定した仕様（DOM・Web IDL・ECMA-262）を `_basis.spec` の URL で指している（`refs` に書く。版は
#     `docs/spec-version.md` の一か所で決まる）
#   * 一つの step を指す ref に `last` がある
#   * `_note` と `_basis.note` に書いた step 番号が、step を書いたどの ref の範囲にも入らない（範囲は両端が同じ ref
#     に入る）。`step` の無い ref は数えない
#   * 注記が番号で始まる、または「/ 番号」を含む（番号は「step N」と書く。そうでないと上の検査に掛からない）
#
# step の決め方：`text` で始まる step のうち、本文全体が `text` と同じものがあればそれだけを候補にする。
# 「Otherwise:」と「Otherwise, if …:」のように、本文が別の step の冒頭になっている step を区別するためである。
# 検査では、番号の step と同じ親を持つ step の中で、候補がその step ちょうど一つでなければならない。

require "json"
require "pathname"
require_relative "specs"

ROOT = File.expand_path("..", __dir__)

module Trace
  class Basis
    PINNED_URL = %r{github\.com/(whatwg/dom|whatwg/webidl|tc39/ecma262)/|dom\.spec\.whatwg\.org|webidl\.spec\.whatwg\.org|tc39\.es/ecma262|262\.ecma-international\.org}
    # 本文の中で step 番号を書いた所（"step 3.2"、"step 4-11"、"steps 1-5"、"step 2 と 4"、"step 4、9-10"）。
    # 直前が日本語でも拾う（`\b` は日本語の文字も語の文字に数えるので使わない）。
    STEP_NUM = /\d+(?:\.\d+)*/
    REF_KEYS = %w[spec alg step text last].freeze
    # 「step」を付けずに書いた番号（"1 Document なら … / 3 adopt"）。
    # 区切りの「 / 」の前後と、注記の頭を見る（URL の「/」は見ない）。
    BARE_NUM = %r{\A\s*\d|\s/\s*\d|\d\s+/\s}
    NOTE_STEP = /(?<![A-Za-z])[Ss]teps? (#{STEP_NUM}(?:\s*[-–〜～]\s*#{STEP_NUM})?(?:\s*(?:,|、|・|と|and|or)\s*#{STEP_NUM}(?:\s*[-–〜～]\s*#{STEP_NUM})?)*)/
    ENTITIES = { "&minus;" => "−", "&amp;" => "&", "&quot;" => "\"", "&hellip;" => "…", "&infin;" => "∞" }.freeze

    attr_reader :errors, :fixed

    def initialize
      @algs = Hash.new do |h, sp|
        h[sp] = JSON.parse(File.read(File.join(ROOT, Trace.spec(sp)[:snapshot])))["algorithms"].to_h { |a| [a["key"], a] }
      end
      @errors = []
      @fixed = 0
    end

    # Bikeshed の link（`[=for/term|text=]`、`{{Interface/member}}`）を描画された語に、entity を文字にする。
    def self.unlink(s)
      s.gsub(/\[=([^\]]*?)=\]|\{\{([^}]*?)\}\}/) do
        inner = Regexp.last_match(1) || Regexp.last_match(2)
        inner.include?("|") ? inner.split("|", 2).last : inner.split("/").last.to_s
      end.gsub(/&[a-z]+;/) { |e| ENTITIES.fetch(e, e) }
    end

    # 比べる形。`lead` が落とす markup の文字は消し（`FILTER_ACCEPT` と `FILTERACCEPT` を同じにする）、
    # ほかの英数字以外は区切りにする。
    def self.norm(s) = unlink(s).downcase.delete("|*_\\").gsub(/[^a-z0-9]+/, " ").strip

    # snapshot の本文から、人が読む冒頭（markup を落とした最初の数語）を作る。
    def self.lead(s, words = 8)
      plain = unlink(s).gsub(/\[\[|\]\]|[|*_\\]/, "").gsub(/\s+/, " ").strip
      w = plain.split(" ")
      w.size <= words ? plain.sub(/[.:]\z/, "") : w.first(words).join(" ")
    end

    def self.prefix?(text, full)
      t = norm(text)
      f = norm(full)
      !t.empty? && (f == t || f.start_with?("#{t} "))
    end

    def step_of(alg, n) = alg["steps"].find { |s| s["n"] == n }

    # "4-17" を両端に分ける。両端は同じ深さで、同じ親を持つ。
    def ends(sel)
      lo, hi = sel.split("-", 2)
      return nil if lo.to_s.empty?

      hi ||= lo
      pl = lo.split(".")
      ph = hi.split(".")
      return nil unless pl.size == ph.size && pl[0..-2] == ph[0..-2] && pl.last.to_i <= ph.last.to_i

      [lo, hi]
    end

    def check_file(path, fill: false, fix: false)
      data = JSON.parse(File.read(path))
      basis = data["_basis"]
      where = File.basename(path)
      return error("#{where}: _basis が無い") unless basis

      if basis["spec"].to_s.match?(PINNED_URL)
        error("#{where}: 固定した仕様を _basis.spec の URL で指している。refs に書く")
      end
      refs = basis["refs"] || []
      changed = false
      covered = []
      # ref が読めなかったときは、注記の検査を飛ばす（範囲が分からないので、同じ原因の error が重なるだけになる）。
      broken = false
      refs.each_with_index do |ref, i|
        at = "#{where}: refs[#{i}]"
        unless (extra = ref.keys - REF_KEYS).empty?
          error("#{at}: 未知の key #{extra.join('・')}（#{REF_KEYS.join('・')} のどれか）")
          broken = true
        end
        sp = ref["spec"] || "dom"
        unless Trace::SPECS.key?(sp)
          error("#{at}: 未知の仕様 #{sp}")
          broken = true
          next
        end
        alg = @algs[sp][ref["alg"]]
        unless alg
          error("#{at}: #{sp} に algorithm #{ref['alg']} が無い")
          broken = true
          next
        end
        unless ref["step"]
          error("#{at}: step が無いのに text がある") if ref["text"] || ref["last"]
          next
        end
        unless ref["step"].is_a?(String)
          error("#{at}: step は文字列で書く（#{ref['step'].inspect}）")
          broken = true
          next
        end
        pair = ends(ref["step"])
        unless pair
          error("#{at}: step の範囲 #{ref['step']} の両端は同じ深さで、昇順でなければならない")
          broken = true
          next
        end
        lo, hi = pair
        range = lo == hi ? [lo] : [lo, hi]
        error("#{at}: step #{lo} は範囲でないのに last がある") if lo == hi && ref["last"]
        if fill
          [["text", lo], ["last", hi]].each do |key, n|
            next if key == "last" && lo == hi
            next unless (s = step_of(alg, n))
            # 書いてある冒頭は、その step に合うのに一つに決まらないときだけ書き直す。
            next if ref[key] && (!Basis.prefix?(ref[key], s["text"]) || unique?(alg, n, ref[key]))

            new = unique_lead(alg, n)
            next if new == ref[key]

            ref[key] = new
            changed = true
          end
        end
        mark = @errors.size
        ok = check_end(alg, lo, ref["text"], "#{at}（#{ref['alg']} step #{lo}）")
        ok &&= check_end(alg, hi, ref["last"], "#{at}（#{ref['alg']} step #{hi}）") if lo != hi
        if !ok && fix
          nl = relocate(alg, ref["text"])
          nh = lo == hi ? nl : relocate(alg, ref["last"])
          if nl && nh && ends(nl == nh ? nl : "#{nl}-#{nh}")
            @errors.slice!(mark..)
            ref["step"] = nl == nh ? nl : "#{nl}-#{nh}"
            range = nl == nh ? [nl] : [nl, nh]
            @fixed += 1
            changed = true
          end
        end
        covered << range
      end
      check_notes(where, data, basis, covered) unless broken
      return unless changed

      replace_basis(path, basis)
    end

    # 番号 n の step があり、本文が text で始まり、同じ親を持つ step の中で text から n に決まるか。
    def check_end(alg, n, text, at)
      s = step_of(alg, n)
      problem =
        if !s then "step が snapshot に無い"
        elsif !text then "text が無い（--fill で埋める）"
        elsif !Basis.prefix?(text, s["text"]) then "本文の冒頭が合わない。snapshot は「#{unique_lead(alg, n)}」"
        elsif !unique?(alg, n, text)
          others = candidates(siblings(alg, n), text).map { |c| c["n"] } - [n]
          "冒頭が step #{others.join('、')} にも合う（--fill で長くする）"
        end
      error("#{at}: #{problem}") if problem
      problem.nil?
    end

    # text で始まる step。本文全体が text と同じ step があれば、それだけにする。
    def candidates(steps, text)
      c = steps.select { |s| Basis.prefix?(text, s["text"]) }
      exact = c.select { |s| Basis.norm(s["text"]) == Basis.norm(text) }
      exact.empty? ? c : exact
    end

    # n と同じ親を持つ step（n を含む）。
    def siblings(alg, n)
      parent = n.split(".")[0..-2]
      alg["steps"].select do |s|
        p = s["n"].split(".")
        p.size == parent.size + 1 && p[0..-2] == parent
      end
    end

    def unique?(alg, n, text) = candidates(siblings(alg, n), text).map { |c| c["n"] } == [n]

    # step n の冒頭。同じ親を持つ step の中で n に決まるまで語を足す（決まらなければ本文全体）。
    def unique_lead(alg, n)
      full = step_of(alg, n)["text"]
      words = 8
      loop do
        t = Basis.lead(full, words)
        return t if unique?(alg, n, t) || t == Basis.lead(full, words + 1)

        words += 1
      end
    end

    # algorithm 全体で text から一つに決まる step の番号。
    def relocate(alg, text)
      return nil unless text

      c = candidates(alg["steps"], text)
      c.size == 1 ? c[0]["n"] : nil
    end

    # 注記の step 番号は、refs のどれかの範囲に入らなければならない（refs と一緒に直す）。
    # 注記の範囲（"step 4-11"）は、両端が同じ ref の範囲に入らなければならない。
    def check_notes(where, data, basis, covered)
      [data["_note"], basis["note"]].compact.each do |note|
        if (m = note.match(BARE_NUM))
          error("#{where}: 注記に「step」を付けない番号がある。「step N」と書く（「#{note[[m.begin(0) - 15, 0].max, 30]}」）")
        end
        note.scan(NOTE_STEP).each do |(list)|
          list.scan(/(#{STEP_NUM})(?:\s*[-–〜～]\s*(#{STEP_NUM}))?/).each do |lo, hi|
            next if covered.any? { |r| within?(lo, r) && (hi.nil? || within?(hi, r)) }

            error("#{where}: 注記の step #{hi ? "#{lo}-#{hi}" : lo} が refs のどの範囲にも無い")
          end
        end
      end
    end

    # n が範囲 [lo] / [lo, hi] の step か、その下の step である。
    def within?(n, r)
      lo, hi = r
      hi ||= lo
      pl = lo.split(".")
      head = n.split(".")
      return false if head.size < pl.size

      cut = head.first(pl.size)
      cut[0..-2] == pl[0..-2] && cut.last.to_i.between?(pl.last.to_i, hi.split(".").last.to_i)
    end

    def error(msg)
      @errors << msg
    end

    # `_basis` の塊だけを書き直す（ほかの部分の整形はそのまま）。
    def replace_basis(path, basis)
      src = File.read(path)
      start = src.index(/^  "_basis": \{\n/)
      stop = start && src.index(/^  \}/, start)
      return error("#{File.basename(path)}: _basis の塊が見つからないので書き直せない") unless stop

      body = JSON.pretty_generate(basis).gsub("\n", "\n  ")
      File.write(path, src[0...start] + "  \"_basis\": #{body}" + src[(stop + 3)..])
    end

    # 版を上げたあと、根拠の step の本文が変わった scenario を挙げる（期待結果を読み直す一覧）。
    # 古い版は git の rev の時点の snapshot と scenario、新しい版は working tree のもの。
    # step は本文の hash で対応させるので、改番だけの step は挙げない。範囲の ref は、範囲の中の step と
    # その下の step をすべて見る。`step` の無い ref は algorithm 全体の hash を比べる。
    def changes_since(rev, files)
      old_algs = Hash.new do |h, sp|
        src = git_show(rev, Trace.spec(sp)[:snapshot])
        h[sp] = src ? JSON.parse(src)["algorithms"].to_h { |a| [a["key"], a] } : {}
      end
      files.filter_map do |path|
        rel = Basis.repo_path(path)
        new_refs = JSON.parse(File.read(path)).dig("_basis", "refs") || []
        old_src = git_show(rev, rel)
        old_refs = old_src ? (JSON.parse(old_src).dig("_basis", "refs") || []) : []
        lines = []
        # 新しい版で引いている step のうち、古い版に同じ本文の step が無いもの（変わったか加わった）。
        new_refs.each { |r| lines.concat(diff_ref(r, @algs, old_algs, "新しい版")) }
        # 古い版で引いていた step のうち、新しい版に同じ本文の step が無いもの（変わったか無くなった）。
        old_refs.each { |r| lines.concat(diff_ref(r, old_algs, @algs, "古い版")) }
        [File.basename(path), lines.uniq] unless lines.empty?
      end
    end

    # ref が `from` の版で指す step のうち、`to` の版の同じ algorithm に同じ本文の step が無いもの。
    def diff_ref(ref, from, to, label)
      sp = ref["spec"] || "dom"
      return [] unless Trace::SPECS.key?(sp)

      a = from[sp][ref["alg"]]
      b = to[sp][ref["alg"]]
      return [] unless a
      return ["#{sp} #{ref['alg']}：#{label}にしか無い algorithm"] unless b

      unless ref["step"].is_a?(String) && (pair = ends(ref["step"]))
        return a["hash"] == b["hash"] ? [] : ["#{sp} #{ref['alg']}：algorithm の本文が変わった"]
      end

      have = b["steps"].map { |s| s["hash"] }
      gone = a["steps"].select { |s| within?(s["n"], pair.uniq) && !have.include?(s["hash"]) }
      gone.map { |s| "#{sp} #{ref['alg']} step #{s['n']}（#{label}の番号）：「#{Basis.lead(s['text'])}」" }
    end

    # repo の root からの path（git show に渡す形）。symlink を解いてから比べる。repo の外なら nil。
    def self.repo_path(path)
      rel = Pathname(File.realpath(path)).relative_path_from(Pathname(File.realpath(ROOT))).to_s
      rel.start_with?("../") ? nil : rel
    end

    def git_show(rev, rel)
      out = IO.popen(["git", "-C", ROOT, "show", "#{rev}:#{rel}"], err: File::NULL, &:read)
      $?.success? ? out : nil
    end
  end
end

if $PROGRAM_NAME == __FILE__
  fill = ARGV.delete("--fill")
  fix = ARGV.delete("--fix")
  since = nil
  if (i = ARGV.index("--since"))
    since = ARGV.delete_at(i + 1) or abort "--since には git の rev を渡す"
    ARGV.delete_at(i)
  end
  abort "--fill・--fix・--since は一緒に使えない" if [fill, fix, since].compact.size > 1
  if (bad = ARGV.find { |a| a.start_with?("--") })
    abort "未知の option #{bad}"
  end
  mode = fill ? :fill : (fix ? :fix : :check)
  files =
    if ARGV.empty?
      Dir[File.join(ROOT, "test/scenarios/*.json")].sort.reject { |f| File.basename(f).start_with?("failing-") || f.end_with?(".lean.json", ".impl.json", ".dommy.json") }
    else
      ARGV
    end
  if (missing = files.find { |f| !File.file?(f) })
    abort "file が無い：#{missing}"
  end
  b = Trace::Basis.new
  files.each { |f| b.check_file(f, fill: mode == :fill, fix: mode == :fix) }
  puts "直した ref：#{b.fixed}" if mode == :fix
  if since
    abort "git の rev #{since} が無い" unless system("git", "-C", ROOT, "rev-parse", "--verify", "--quiet", "#{since}^{commit}", out: File::NULL)

    if (outside = files.find { |f| Trace::Basis.repo_path(f).nil? })
      abort "repo の外の file は --since で比べられない：#{outside}"
    end

    changed = b.changes_since(since, files)
    if changed.empty?
      puts "#{since} から、根拠の step の本文が変わった scenario は無い"
    else
      puts "#{since} から根拠の step の本文が変わった scenario（期待結果を読み直す）："
      changed.each do |name, lines|
        puts "  #{name}"
        lines.each { |l| puts "    #{l}" }
      end
      puts "#{changed.size} 本"
    end
  end
  if b.errors.empty?
    puts "scenario #{files.size} 本の _basis は固定版の snapshot と合う"
  else
    warn b.errors.map { |e| "error: #{e}" }.join("\n")
    warn "#{b.errors.size} 件"
    exit 1
  end
end
