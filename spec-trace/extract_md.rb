# frozen_string_literal: true

# Bikeshed の markdown で step を書いた仕様（WebIDL の `webidl.bs`）から、algorithm と番号付き step を抜き出す。
#
# DOM の `dom.bs` は step を `<ol>` で書くが、`webidl.bs` は `<div algorithm>` の中に markdown の番号付きリスト
# （`1.  …` の行。入れ子は字下げ）で書く。出力の形は `extract.rb` と同じで、`check.rb` と `drift.rb` がそのまま読む。
#
# algorithm の単位は `<div ... algorithm ...>` である。鍵は描画された仕様の anchor で、次の順に決める。
#
#   * div の `id`
#   * div の中の最初の `<dfn>` の id（abstract-op なら `abstract-opdef-<名前>`）
#   * どちらも無ければ `algorithm:<algorithm 属性の値>`
#
# step の本文の hash は `extract.rb` と同じく、注記を落として空白を詰めた markup の SHA-256 である。
# 注記は `<div class=note>` などの block（`Extract.scrub` が落とす）と、`Note:` で始まる段落である。

require "json"
require "digest"
require_relative "extract" unless defined?(Trace::Extract)

module Trace
  module ExtractMd
    module_function

    ITEM = /\A( *)\d+\.\s+(.*)\z/

    # Bikeshed が `<dfn>` に振る id。abstract-op は `abstract-opdef-` を前に付ける。
    def dfn_id(tag, inner)
      a = Extract.attrs(tag)
      return a["id"] if a["id"].is_a?(String)

      text = a["lt"].is_a?(String) ? a["lt"].split("|").first : Extract.strip_tags(inner)
      return "abstract-opdef-#{Extract.slug(text)}" if a.key?("abstract-op")

      a["for"].is_a?(String) ? "#{Extract.slug(a['for'])}-#{Extract.slug(text)}" : Extract.slug(text)
    end

    # `Note:` で始まる段落（空行まで）を空白にする。行数は保つ。
    def drop_note_paragraphs(lines)
      out = []
      in_note = false
      lines.each do |l|
        in_note = true if l =~ /\A\s*Note:/
        in_note = false if l.strip.empty?
        out << (in_note ? "" : l)
      end
      out
    end

    # div の中の行を、題（最初の項目より前の文）と step の木に分ける。
    def parse_list(lines)
      title = []
      roots = []
      stack = [] # [indent, item]
      seen_item = false
      lines.each do |l|
        if (m = ITEM.match(l))
          indent = m[1].size
          item = { body: +m[2], children: [] }
          stack.pop while stack.any? && stack.last[0] >= indent
          if stack.empty?
            # 最初の list が終わった後の list は、別の algorithm の書き方なので読まない。
            break if seen_item && roots.any? && !continuation_of_roots?(roots, indent)

            roots << item
            @root_indent = indent
          else
            stack.last[1][:children] << item
          end
          stack << [indent, item]
          seen_item = true
        elsif !seen_item
          title << l
        elsif stack.any? && !l.strip.empty?
          ind = l[/\A */].size
          stack.pop while stack.size > 1 && stack.last[0] >= ind
          stack.last[1][:body] << " " << l.strip if ind > stack.last[0]
        end
      end
      [title.join("\n"), roots]
    end

    def continuation_of_roots?(_roots, indent)
      indent == @root_indent
    end

    def flatten(items, prefix = nil, out = [])
      items.each_with_index do |it, k|
        n = prefix ? "#{prefix}.#{k + 1}" : (k + 1).to_s
        out << { "n" => n, "hash" => Digest::SHA256.hexdigest(Extract.normalize(it[:body]))[0, 16],
                 "text" => Extract.strip_tags(it[:body])[0, 160] }
        flatten(it[:children], n, out)
      end
      out
    end

    def run(src)
      clean = Extract.scrub(src)
      line_of = ->(off) { clean[0...off].count("\n") + 1 }
      algorithms = []
      heading = [] # [[level, number, id, text]]
      counters = [0, 0, 0, 0, 0, 0]
      tok = /<h([2-6])\b([^>]*)>(.*?)<\/h\1>|<div\b([^>]*)>/m
      i = 0
      while (m = tok.match(clean, i))
        if m[1]
          a = Extract.attrs(m[2])
          level = m[1].to_i
          if a["class"].to_s.include?("no-num")
            num = nil
          else
            counters[level - 2] += 1
            (level - 1...counters.size).each { |k| counters[k] = 0 }
            num = counters[0..level - 2].join(".")
          end
          heading.reject! { |h| h[0] >= level }
          heading << [level, num, a["id"], Extract.strip_tags(m[3])]
          i = m.end(0)
          next
        end
        a = Extract.attrs(m[4] || "")
        unless a.key?("algorithm")
          i = m.end(0)
          next
        end
        # 対応する </div> を数えて探す。
        depth = 1
        j = m.end(0)
        while depth.positive? && (t = /<(\/?)div\b[^>]*>/.match(clean, j))
          depth += t[1].empty? ? 1 : -1
          j = t.end(0)
        end
        body = clean[m.end(0)...(j - "</div>".size)]
        lines = drop_note_paragraphs(body.lines(chomp: true))
        title, roots = parse_list(lines)
        key =
          if a["id"].is_a?(String)
            a["id"]
          elsif (d = body.match(/(<dfn\b[^>]*>)(.*?)<\/dfn>/m))
            dfn_id(d[1], d[2])
          elsif a["algorithm"].is_a?(String)
            "algorithm:#{a['algorithm']}"
          end
        if key
          sec = heading.reverse.find { |h| h[1] }
          algorithms << { "key" => key, "section" => sec && sec[1], "heading" => sec && sec[2],
                          "headings" => heading.map { |h| h[2] }.compact,
                          "line" => line_of.call(m.begin(0)),
                          "title" => Extract.strip_tags(title)[0, 160],
                          "steps" => flatten(roots),
                          "hash" => Digest::SHA256.hexdigest(Extract.normalize(lines.join("\n")))[0, 16] }
        end
        i = j
      end
      dup = algorithms.group_by { |x| x["key"] }.select { |_, v| v.size > 1 }
      unless dup.empty?
        msg = dup.map { |k, v| "#{k} (lines #{v.map { |x| x['line'] }.join(', ')})" }.join("\n  ")
        raise "duplicate keys:\n  #{msg}"
      end
      algorithms
    end
  end
end

if $PROGRAM_NAME == __FILE__
  src = File.read(ARGV.fetch(0))
  puts JSON.pretty_generate({ "algorithms" => Trace::ExtractMd.run(src) })
end
