# frozen_string_literal: true

# ECMA-262（tc39/ecma262 の `spec.html`、ecmarkup）から、algorithm と番号付き step を抜き出す。
#
# ecmarkup は節を `<emu-clause id=…>` の入れ子で書き、step を `<emu-alg>` の中の番号付きリスト（`1. …` の行、入れ子は
# 字下げ）で書く。出力の形は `extract.rb` と同じで、`check.rb` と `drift.rb` がそのまま読む。
#
# 本文は大きいので、`roots` に挙げた節の部分木だけを抜き出す（model が使う抽象操作の節）。
#
# algorithm の単位は節の直下の `<emu-alg>` である。鍵は節の id で、一つの節に `<emu-alg>` が複数ある
# （syntax-directed operation が生成規則ごとに algorithm を書く）ときは `<id>/<k>`（k は 1 始まり）とし、題に
# 直前の `<emu-grammar>` の生成規則を書く。見出しの列（`headings`）は祖先の節の id である。

require "json"
require "digest"
require_relative "extract" unless defined?(Trace::Extract)
require_relative "extract_md" unless defined?(Trace::ExtractMd)

module Trace
  module ExtractEcma
    module_function

    # 固定した版で model が使う節。
    ROOTS = %w[sec-type-conversion sec-numeric-types-number-tostring sec-array.prototype.join].freeze

    def scrub(src)
      blank = ->(m) { m.gsub(/[^\n]/, " ") }
      src = src.gsub(/<!--.*?-->/m, &blank)
      src.gsub(%r{<emu-note\b.*?</emu-note>}m, &blank)
    end

    # ecmarkup の書き方（`_x_`、`*x*`、`|X|`）を落とした文。
    def text(s)
      Extract.strip_tags(s).gsub(/(?<![\w])_(\w+)_/, '\1').gsub(/\*([^*\s][^*]*)\*/, '\1')
    end

    def run(src, roots: ROOTS)
      clean = scrub(src)
      line_of = ->(off) { clean[0...off].count("\n") + 1 }
      algorithms = []
      stack = [] # [id, number, active]
      counters = [0]
      tok = %r{<(emu-clause|emu-annex)\b([^>]*)>|</(emu-clause|emu-annex)>|<emu-alg\b[^>]*>(.*?)</emu-alg>|<emu-grammar\b[^>]*>(.*?)</emu-grammar>}m
      i = 0
      last_grammar = nil
      per_clause = Hash.new { |h, k| h[k] = [] }
      while (m = tok.match(clean, i))
        if m[1]
          a = Extract.attrs(m[2])
          depth = stack.size
          counters[depth] = (counters[depth] || 0) + 1
          counters = counters[0..depth]
          num = counters.join(".")
          active = stack.any? { |s| s[2] } || roots.include?(a["id"])
          h1 = clean.match(%r{<h1>(.*?)</h1>}m, m.end(0))
          stack << [a["id"], num, active, h1 ? text(h1[1]) : ""]
          last_grammar = nil
        elsif m[3]
          stack.pop
          last_grammar = nil
        elsif m[5]
          last_grammar = text(m[5])
        elsif m[4] && stack.any? && stack.last[2] && stack.last[0]
          id, num, _, title = stack.last
          lines = m[4].lines(chomp: true)
          _, roots_items = ExtractMd.parse_list(lines)
          per_clause[id] << {
            "key" => id, "section" => num, "heading" => id,
            "headings" => stack[0..-2].map(&:first).compact,
            "line" => line_of.call(m.begin(0)),
            "title" => (last_grammar ? "#{title}：#{last_grammar}" : title)[0, 160],
            "steps" => ExtractMd.flatten(roots_items),
            "hash" => Digest::SHA256.hexdigest(Extract.normalize(m[4]))[0, 16]
          }
          last_grammar = nil
        end
        i = m.end(0)
      end
      per_clause.each_value do |algs|
        if algs.size > 1
          algs.each_with_index { |x, k| x["key"] = "#{x['key']}/#{k + 1}" }
        end
        algorithms.concat(algs)
      end
      algorithms.sort_by { |x| x["line"] }
    end
  end
end

if $PROGRAM_NAME == __FILE__
  puts JSON.pretty_generate({ "algorithms" => Trace::ExtractEcma.run(File.read(ARGV.fetch(0))) })
end
