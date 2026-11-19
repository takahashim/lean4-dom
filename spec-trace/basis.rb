# frozen_string_literal: true

# 固定 scenario の `_basis.refs`（期待結果の根拠にした仕様の step）を、固定版の snapshot と突き合わせる。
#
#   ruby spec-trace/basis.rb                  # test/scenarios/*.json を検査する
#   ruby spec-trace/basis.rb --fill FILE ...  # refs の text・last を snapshot から埋める（書くときに使う）
#   ruby spec-trace/basis.rb --fix            # 版を上げて番号がずれた ref を、本文の一致で付け直す
#
# ref の形：
#
#   {"alg": "concept-node-remove", "step": "15", "text": "Add transient registered observers"}
#   {"alg": "concept-node-remove", "step": "1-17", "text": "Let parent be node's parent", "last": "Run the children changed steps for parent"}
#   {"spec": "webidl", "alg": "abstract-opdef-converttoint", "step": "4", "text": "Let x be ? ToNumber(V)"}
#   {"alg": "concept-node-append"}            # 番号付きの step の無い algorithm、または algorithm 全体
#
# `spec` は dom（既定）・webidl・ecma262、`alg` は snapshot の key。`text` は step の本文の冒頭で、`last` は範囲の
# 最後の step の本文の冒頭。大文字小文字と、英数字以外の文字（Bikeshed・ecmarkup の markup を含む）を無視して比べる。
#
# 失敗にするもの：
#
#   * snapshot に無い algorithm・step
#   * `text`（`last`）が、その番号の step の本文の冒頭と合わない（版を上げて改番されたときもここで落ちる）
#   * 固定した仕様（DOM・Web IDL・ECMA-262）を `_basis.spec` の URL で指している（`refs` に書く。版は
#     `docs/spec-version.md` の一か所で決まる）
#   * `_note` と `_basis.note` に書いた step 番号が、どの ref の範囲にも入らない

require "json"
require_relative "specs"

ROOT = File.expand_path("..", __dir__)

module Trace
  class Basis
    PINNED_URL = %r{github\.com/(whatwg/dom|whatwg/webidl|tc39/ecma262)/|dom\.spec\.whatwg\.org|webidl\.spec\.whatwg\.org|tc39\.es/ecma262}
    # 本文の中で step 番号を書いた所（"step 3.2"、"step 4-11"、"steps 1-5"）。
    NOTE_STEP = /\bsteps? (\d+(?:\.\d+)*)(?:\s*-\s*(\d+(?:\.\d+)*))?/

    attr_reader :errors, :fixed

    def initialize
      @algs = Hash.new do |h, sp|
        h[sp] = JSON.parse(File.read(File.join(ROOT, Trace.spec(sp)[:snapshot])))["algorithms"].to_h { |a| [a["key"], a] }
      end
      @errors = []
      @fixed = 0
    end

    # 比べる形。`lead` が落とす markup の文字は消し（`FILTER_ACCEPT` と `FILTERACCEPT` を同じにする）、
    # ほかの英数字以外は区切りにする。
    def self.norm(s) = s.downcase.gsub(/&minus;/, "-").delete("|*_\\").gsub(/[^a-z0-9]+/, " ").strip

    # snapshot の本文から、人が読む冒頭（markup を落とした最初の数語）を作る。
    def self.lead(s, words = 8)
      plain = s.gsub(/\[=|=\]|\[\[|\]\]|[|*_\\]|\{\{|\}\}/, "").gsub(/&minus;/, "−").gsub(/\s+/, " ").strip
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
      refs.each_with_index do |ref, i|
        at = "#{where}: refs[#{i}]"
        sp = ref["spec"] || "dom"
        unless Trace::SPECS.key?(sp)
          error("#{at}: 未知の仕様 #{sp}")
          next
        end
        alg = @algs[sp][ref["alg"]]
        unless alg
          error("#{at}: #{sp} に algorithm #{ref['alg']} が無い")
          next
        end
        unless ref["step"]
          error("#{at}: step が無いのに text がある") if ref["text"] || ref["last"]
          next
        end
        pair = ends(ref["step"])
        unless pair
          error("#{at}: step の範囲 #{ref['step']} の両端は同じ深さで、昇順でなければならない")
          next
        end
        lo, hi = pair
        range = lo == hi ? [lo] : [lo, hi]
        if fill
          ref["text"] ||= (s = step_of(alg, lo)) && Basis.lead(s["text"])
          ref["last"] ||= (s = step_of(alg, hi)) && Basis.lead(s["text"]) if lo != hi
          changed = true
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
      check_notes(where, data, basis, covered)
      return unless changed

      replace_basis(path, basis)
    end

    # 番号 n の step があり、本文が text で始まるか。
    def check_end(alg, n, text, at)
      s = step_of(alg, n)
      problem =
        if !s then "step が snapshot に無い"
        elsif !text then "text が無い（--fill で埋める）"
        elsif !Basis.prefix?(text, s["text"]) then "本文の冒頭が合わない。snapshot は「#{Basis.lead(s['text'])}」"
        end
      error("#{at}: #{problem}") if problem
      problem.nil?
    end

    # text で始まる step がちょうど一つなら、その番号。
    def relocate(alg, text)
      return nil unless text

      c = alg["steps"].select { |s| Basis.prefix?(text, s["text"]) }
      c.size == 1 ? c[0]["n"] : nil
    end

    # 注記の step 番号は、refs のどれかの範囲に入らなければならない（refs と一緒に直す）。
    def check_notes(where, data, basis, covered)
      [data["_note"], basis["note"]].compact.each do |note|
        note.scan(NOTE_STEP).each do |a, b|
          [a, b].compact.each do |n|
            next if covered.any? { |r| within?(n, r) }

            error("#{where}: 注記の step #{n} が refs のどの範囲にも無い")
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
      start = src.index(/^  "_basis": \{\n/) or abort "#{path}: _basis の塊が見つからない"
      stop = src.index(/^  \}/, start) or abort "#{path}: _basis の終わりが見つからない"
      body = JSON.pretty_generate(basis).gsub("\n", "\n  ")
      File.write(path, src[0...start] + "  \"_basis\": #{body}" + src[(stop + 3)..])
    end
  end
end

if $PROGRAM_NAME == __FILE__
  mode = ARGV.delete("--fill") ? :fill : (ARGV.delete("--fix") ? :fix : :check)
  files = ARGV.empty? ? Dir[File.join(ROOT, "test/scenarios/*.json")].sort : ARGV
  files.reject! { |f| File.basename(f).start_with?("failing-") }
  b = Trace::Basis.new
  files.each { |f| b.check_file(f, fill: mode == :fill, fix: mode == :fix) }
  puts "直した ref：#{b.fixed}" if mode == :fix
  if b.errors.empty?
    puts "scenario #{files.size} 本の _basis は固定版の snapshot と合う"
  else
    warn b.errors.map { |e| "error: #{e}" }.join("\n")
    warn "#{b.errors.size} 件"
    exit 1
  end
end
