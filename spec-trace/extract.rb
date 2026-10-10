# frozen_string_literal: true

# Bikeshed source（`dom.bs`）から algorithm と、その番号付き step を抜き出す。
#
#   ruby spec-trace/extract.rb --fetch SHA > spec-trace/dom.json      # whatwg/dom から取って抜き出す
#   ruby spec-trace/extract.rb --check-snapshot spec-trace/dom.json   # 固定した snapshot を作り直して比べる
#   ruby spec-trace/extract.rb dom.bs --verify-ids rendered.html # 鍵が描画された仕様の id にあるか
#
# algorithm の単位は次のどれかで始まる段落（`<ol>` の外にあるもの）である。
#
#   * `<div algorithm>` の最初の段落
#   * `To <dfn>…</dfn>` で始まる段落
#   * `method steps` / `getter steps` / `setter steps` / `constructor steps` を述べる段落
#
# 段落が `:` で終わるなら、直後の `<ol>` がその step である。番号は Bikeshed の
# 描画と同じく 1 始まりで、入れ子は `5.13` のように書く。
#
# 鍵は描画された仕様の anchor（https://dom.spec.whatwg.org/#<key>）である。
# 一つの anchor に getter と setter がぶら下がる attribute は、setter のほうに
# `/setter` を付ける。
#
# step の比較には、注記（`<p class=note>`）・例・comment を落として空白を
# 詰めた markup の SHA-256 を使う。`<a for=tree>parent</a>` と `<a>parent</a>` の
# 違いも意味の違いなので、tag は落とさない。

require "json"
require "digest"

module Trace
  module Extract
    module_function

    # comment と非規範の block を、行数を保ったまま空白に置き換える。
    def scrub(src)
      blank = ->(m) { m.gsub(/[^\n]/, " ") }
      src = src.gsub(/<!--.*?-->/m, &blank)
      src = src.gsub(/<pre[^>]*>.*?<\/pre>/m, &blank)
      # domintro・example・note の block は入れ子の div を持ちうるので数えて閉じる。
      out = +""
      i = 0
      opener = /<(div|dl|section|aside)\b[^>]*class=["']?(?:[\w-]+ )*(domintro|example|note|warning)\b[^>]*>/m
      while (m = opener.match(src, i))
        out << src[i...m.begin(0)]
        tag = m[1]
        depth = 1
        j = m.end(0)
        re = /<(\/?)#{tag}\b[^>]*>/
        while depth.positive? && (t = re.match(src, j))
          depth += t[1].empty? ? 1 : -1
          j = t.end(0)
        end
        out << blank.call(src[m.begin(0)...j])
        i = j
      end
      out << src[i..]
      # step の中の注記段落は、次の block の始まりまでを落とす。
      out.gsub(/<p class=["']?note["']?>.*?(?=<p\b|<li\b|<\/li>|<ol\b|<\/ol>|<div\b|<\/div>|<dl\b|\n\s*\n)/m, &blank)
    end

    def strip_tags(s)
      s.gsub(/<[^>]+>/, "").gsub("&amp;", "&").gsub("&lt;", "<").gsub("&gt;", ">")
       .gsub(/\{\{([^}]+)\}\}/) { Regexp.last_match(1).sub(%r{.*/}, "").sub(/!!.*/, "") }
       .gsub(/\s+/, " ").strip
    end

    def normalize(s)
      s.gsub(/\s+/, " ").strip
    end

    def slug(s)
      strip_tags(s).downcase.gsub(/[^a-z0-9]+/, "-").gsub(/\A-|-\z/, "")
    end

    def attrs(tag)
      h = {}
      tag.scan(/([\w-]+)(?:=("[^"]*"|'[^']*'|[^\s>]+))?/) do |k, v|
        h[k] = v ? v.delete_prefix('"').delete_suffix('"').delete_prefix("'").delete_suffix("'") : true
      end
      h
    end

    IDL_TYPES = %w[method attribute constructor dict-member].freeze

    # Bikeshed が `<dfn>` に振る id。
    def dfn_id(tag, inner)
      a = attrs(tag)
      return a["id"] if a["id"].is_a?(String)

      text = a["lt"].is_a?(String) ? a["lt"].split("|").first : strip_tags(inner)
      type = IDL_TYPES.find { |t| a.key?(t) }
      if type
        name = text.sub(/\(.*\z/m, "")
        name = a["for"] if type == "constructor"
        return "dom-#{a['for'].downcase}-#{name.downcase.gsub(/[^a-z0-9_-]+/, '')}"
      end
      a["for"].is_a?(String) ? "#{slug(a['for'])}-#{slug(text)}" : slug(text)
    end

    # `{{Interface/member}}` の参照から anchor を作る。
    def ref_id(ref)
      iface, member = ref.split("/", 2)
      name = member.sub(/\(.*\z/, "").sub(/!!.*/, "")
      name = iface if name == "constructor"
      "dom-#{iface.downcase}-#{name.downcase}"
    end

    HEAD_STEPS = /\b(method|getter|setter|constructor)\s+steps\b/

    # 段落が algorithm の頭なら、その鍵（複数ありうる）を返す。
    def head_keys(para, in_div, div_name, heading_id = nil)
      keys = []
      dfns = para.scan(/(<dfn\b[^>]*>)(.*?)<\/dfn>/m)
      if (m = para.match(HEAD_STEPS))
        kind = m[1]
        idl = dfns.select { |t, _| IDL_TYPES.any? { |x| attrs(t).key?(x) } }
        if idl.any?
          idl.each { |t, inner| keys << (kind == "setter" ? "#{dfn_id(t, inner)}/setter" : dfn_id(t, inner)) }
        elsif (r = para.match(/\{\{([^}]+)\}\}\s*(?:<\/code>)?\s*(method|getter|setter|constructor)\s+steps/))
          id = ref_id(r[1])
          keys << (kind == "setter" ? "#{id}/setter" : id)
        elsif (r = para.match(%r{<a (?:attribute|method) for=([\w-]+)>(?:<code>)?(\w+)(?:</code>)?</a>\s*(?:method|getter|setter)\s+steps}))
          id = "dom-#{r[1].downcase}-#{r[2].downcase}"
          keys << (kind == "setter" ? "#{id}/setter" : id)
        end
      end
      return keys if keys.any?

      if para =~ /\A<p>\s*(?:To|When asked to)\s+<dfn/ || (in_div && dfns.any?) ||
            (dfns.any? && para =~ /\bthese\s+(?:getter\s+and\s+setter\s+)?steps\b/)
        t, inner = dfns.first
        keys << dfn_id(t, inner)
      elsif in_div && div_name.is_a?(String)
        keys << "algorithm:#{div_name}"
      elsif para =~ /<a>supported property names<\/a>.*\bthese\s+steps\b/m && heading_id
        keys << "#{heading_id}/supported-property-names"
      end
      keys
    end

    # `<ol>` の中を step の木に組む。`</li>` は省略されうる。
    def parse_ol(src, pos)
      steps = []
      stack = [[steps, nil]] # [list, current item]
      tok = /<(\/?)(ol|ul|li)\b[^>]*>/
      start = pos
      ul_depth = 0 # `<ul>` の箇条は step ではなく、それを含む step の本文である
      text_from = nil
      flush = lambda do |upto|
        item = stack.last[1]
        item[:body] << src[text_from...upto] if item && text_from
        text_from = nil
      end
      raise "expected <ol> at #{pos}" unless (first = tok.match(src, pos)) && first[2] == "ol" && first[1].empty?

      i = first.end(0)
      while (t = tok.match(src, i))
        closing = !t[1].empty?
        if t[2] == "ul"
          ul_depth += closing ? -1 : 1
          i = t.end(0)
          next
        elsif ul_depth.positive?
          i = t.end(0)
          next
        end
        case [t[2], closing]
        when ["li", false]
          flush.call(t.begin(0))
          item = { body: +"", children: [] }
          stack.last[0] << item
          stack[-1] = [stack.last[0], item]
          text_from = t.end(0)
        when ["li", true]
          flush.call(t.begin(0))
        when ["ol", false]
          flush.call(t.begin(0))
          parent = stack.last[1] or raise "nested <ol> outside <li> at #{t.begin(0)}"
          stack << [parent[:children], nil]
        when ["ol", true]
          flush.call(t.begin(0))
          stack.pop
          if stack.empty?
            return [steps, t.end(0), src[start...t.end(0)]]
          end
          text_from = t.end(0)
        end
        i = t.end(0)
      end
      raise "unterminated <ol> at #{pos}"
    end

    def flatten(items, prefix = nil, out = [])
      items.each_with_index do |it, k|
        n = prefix ? "#{prefix}.#{k + 1}" : (k + 1).to_s
        out << { "n" => n, "hash" => Digest::SHA256.hexdigest(normalize(it[:body]))[0, 16],
                 "text" => strip_tags(it[:body])[0, 160] }
        flatten(it[:children], n, out)
      end
      out
    end

    def run(src)
      clean = scrub(src)
      line_of = ->(off) { clean[0...off].count("\n") + 1 }
      algorithms = []
      heading = []  # [[level, number, id, text]]
      counters = [0, 0, 0, 0, 0, 0]
      numbered = false
      div_stack = []

      # 走査する token：見出し、div、段落、ol。
      tok = /<h([2-6])\b([^>]*)>(.*?)<\/h\1>|<div\b([^>]*)>|<\/div>|<p\b[^>]*>|<ol\b[^>]*>/m
      i = 0
      pending = nil # 直前の頭（`:` で終わり、次の <ol> を待つ）
      while (m = tok.match(clean, i))
        if m[1]
          a = attrs(m[2])
          level = m[1].to_i
          if a["class"].to_s.include?("no-num")
            num = nil
          else
            numbered = true
            counters[level - 2] += 1
            (level - 1...counters.size).each { |k| counters[k] = 0 }
            num = counters[0..level - 2].join(".")
          end
          heading.reject! { |h| h[0] >= level }
          heading << [level, num, a["id"], strip_tags(m[3])]
          pending = nil
          i = m.end(0)
        elsif m[0].start_with?("<div")
          a = attrs(m[4] || "")
          div_stack << (a.key?("algorithm") ? { name: a["algorithm"], first: true } : nil)
          i = m.end(0)
        elsif m[0] == "</div>"
          div_stack.pop
          pending = nil
          i = m.end(0)
        elsif m[0].start_with?("<ol")
          if pending
            steps, j, raw = parse_ol(clean, m.begin(0))
            pending.each do |alg|
              alg["steps"] = flatten(steps)
              alg["hash"] = Digest::SHA256.hexdigest(normalize(alg.delete(:head_raw) + raw))[0, 16]
            end
            pending = nil
            i = j
          else
            # 頭を持たない <ol>（概念の定義の条件列など）は読み飛ばす。
            _, j, = parse_ol(clean, m.begin(0))
            i = j
          end
        else # <p>
          stop = /<p\b|<ol\b|<\/?div\b|<h[2-6]\b|<dl\b|\n\s*\n/.match(clean, m.end(0))
          para_end = stop ? stop.begin(0) : clean.size
          para = clean[m.begin(0)...para_end]
          div = div_stack.reverse.find { |d| d } if div_stack.last
          in_div = div && div[:first]
          div[:first] = false if div
          keys = head_keys(para, in_div, div && div[:name], heading.last && heading.last[2])
          if keys.any?
            sec = heading.reverse.find { |h| h[1] }
            alg = keys.map do |k|
              { "key" => k, "section" => sec && sec[1], "heading" => sec && sec[2],
                "headings" => heading.map { |h| h[2] }.compact,
                "line" => line_of.call(m.begin(0)), "title" => strip_tags(para)[0, 160],
                "steps" => [], "hash" => Digest::SHA256.hexdigest(normalize(para))[0, 16],
                :head_raw => para }
            end
            algorithms.concat(alg)
            if strip_tags(para).end_with?(":") || clean[para_end..] =~ /\A\s*<ol\b/
              pending = alg
            else
              alg.each { |x| x.delete(:head_raw) }
              pending = nil
            end
          end
          i = para_end
        end
      end
      algorithms.each { |x| x.delete(:head_raw) }
      raise "no numbered headings" unless numbered

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
  require_relative "fetch"
  usage = <<~USAGE
    usage: extract.rb dom.bs [--commit SHA] [--verify-ids rendered.html]
           extract.rb --fetch REF                 # whatwg/dom の REF を取って抜き出す
           extract.rb --check-snapshot spec-trace/dom.json
  USAGE
  args = ARGV.dup
  path = nil
  commit = nil
  verify = nil
  check = nil
  while (a = args.shift)
    case a
    when "--commit" then commit = args.shift
    when "--verify-ids" then verify = args.shift
    when "--fetch" then commit = Trace::Fetch.resolve(args.shift)
    when "--check-snapshot" then check = args.shift
    when /\A--/ then abort usage
    else path = a
    end
  end

  if check
    # 固定した snapshot が、記録した commit の dom.bs から作り直したものと一致し、
    # その commit が test/pinned-versions.json と docs/spec-version.md の commit と一致することを確かめる。
    root = File.expand_path("..", __dir__)
    snap = JSON.parse(File.read(check))
    pinned = JSON.parse(File.read(File.join(root, "test/pinned-versions.json")))["spec"]["commit"]
    abort "#{check} の commit #{snap['commit']} が test/pinned-versions.json の #{pinned} と違う" if snap["commit"] != pinned
    unless File.read(File.join(root, "docs/spec-version.md")).include?(pinned)
      abort "docs/spec-version.md に commit #{pinned} が無い"
    end
    fresh = Trace::Extract.run(Trace::Fetch.dom_bs(snap["commit"]))
    if fresh != snap["algorithms"]
      abort "#{check} が dom.bs #{snap['commit']} から作り直したものと一致しない。ruby spec-trace/extract.rb --fetch #{snap['commit']} > #{check}"
    end
    puts "#{check}: #{fresh.size} algorithms, dom.bs #{snap['commit']} と一致"
    exit 0
  end

  src = path ? File.read(path) : (commit ? Trace::Fetch.dom_bs(commit) : abort(usage))
  algs = Trace::Extract.run(src)
  if verify
    ids = File.read(verify).scan(/\bid="?([^"\s>]+)/).flatten.to_set
    missing = algs.map { |x| x["key"].sub(%r{/setter\z}, "") }
                  .reject { |k| k.start_with?("algorithm:") || k.include?("/supported-property-names") || ids.include?(k) }
    warn "#{algs.size} algorithms, #{missing.size} keys not in rendered ids"
    missing.each { |k| warn "  #{k}" }
    exit(missing.empty? ? 0 : 1)
  end
  puts JSON.pretty_generate({ "spec" => "dom", "commit" => commit, "algorithms" => algs })
end
