# frozen_string_literal: true

# 名前空間の囮の sweep の結果を並べる。
#
#   ruby test/decoy_compare.rb DIR
#
# DIR には `out-<impl>.json` が並んでいる（`test/decoy_sweep.mjs` と `test/decoy_dommy.rb` の出力）。
# browser は oracle ではないが、**三つが揃っている行**だけを基準にする。
# 揃っていない行は仕様の読み直しが要る場所なので、別に数えるだけにする。
#
# 拾うもの：
#
# * dommy-only    — 囮で Dommy の値だけが変わった（browser は三つとも変わらない）
# * dommy-missing — browser が三つとも変わったのに Dommy が変わらない
# * fast-path     — Dommy の JS の速い経路と Ruby の経路で、変わったものが違う
# * write         — setter が attribute list に与えた差が、揃った browser と違う
# * write-decoy   — setter が namespace 付きの attribute（囮）を消した・書き換えた
#
# 同じ不具合は element ごとに何度も出るので、key の element の部分を落として束ねる。

require "json"

BROWSERS = %w[chromium firefox webkit].freeze
DECOY_NS = "urn:x-decoy"

dir = ARGV.fetch(0)
load_impl = lambda do |name|
  path = File.join(dir, "out-#{name}.json")
  next nil unless File.exist?(path)

  JSON.parse(File.read(path))["results"].to_h { |r| [r["id"], r] }
end
impls = (BROWSERS + %w[dommy dommy-ruby]).to_h { |n| [n, load_impl.(n)] }.compact
missing = BROWSERS - impls.keys
abort "browser の結果が足りない: #{missing.join(', ')}" unless missing.empty?
abort "dommy の結果が無い" unless impls["dommy"]

def changes_of(result)
  return nil if result.nil? || result["error"]&.start_with?("host:")

  (result["changes"] || []).to_h { |k, b, a| [k, [b, a]] }
end

# `d1.hidden` → `<el>.hidden`。document 側と method の probe はそのまま。
def pattern(key)
  key.sub(/\A[^.()\[\]]+\.(?=[A-Za-z(])/) { |m| m.start_with?("document.") ? m : "<el>." }
end

def case_kind(id)
  id.split(":").first(2).join(":")
end

groups = Hash.new { |h, k| h[k] = [] }
split = Hash.new(0)

dommy = impls["dommy"]
dommy.each do |id, dres|
  next if id.start_with?("write:", "frag:")

  dc = changes_of(dres)
  bcs = BROWSERS.map { |b| changes_of(impls[b][id]) }
  next if dc.nil? || bcs.any?(&:nil?)

  keys = (dc.keys + bcs.flat_map(&:keys)).uniq
  keys.each do |k|
    changed = bcs.map { |c| c.key?(k) }
    d = dc.key?(k)
    if changed.none? && d
      groups[["dommy-only", case_kind(id), pattern(k)]] << [id, k, dc[k]]
    elsif changed.all? && !d
      groups[["dommy-missing", case_kind(id), pattern(k)]] << [id, k, bcs[0][k]]
    elsif changed.any? && !changed.all? && d
      split[[case_kind(id), pattern(k)]] += 1
    end
  end

  if (rres = impls["dommy-ruby"]&.[](id)) && (rc = changes_of(rres))
    (dc.keys | rc.keys).each do |k|
      next if dc[k] == rc[k]

      groups[["fast-path", case_kind(id), pattern(k)]] << [id, k, [dc[k], rc[k]]]
    end
  end
end

dommy.each do |id, dres|
  next unless id.start_with?("write:")

  bws = BROWSERS.map { |b| impls[b][id]&.dig("writes") }
  next if bws.any?(&:nil?) || dres["writes"].nil?

  by_what = ->(ws) { ws.to_h { |w, err, rem, add| [w, [err ? "throw" : nil, rem, add]] } }
  d = by_what.(dres["writes"])
  bs = bws.map(&by_what)
  d.each do |what, dv|
    prop = what.sub(/=.*/, "")
    if dv[1].any? { |a| a.start_with?(DECOY_NS) }
      groups[["write-decoy", "write", prop]] << [id, what, dv]
    end
    bv = bs.map { |b| b[what] }
    next if bv.any?(&:nil?) || bv.uniq.size != 1 || bv[0] == dv

    groups[["write", "write", prop]] << [id, what, { "dommy" => dv, "browsers" => bv[0] }]
  end
end

# 断片の解釈。作られた element の (namespace, local name) の列を、揃った browser と比べる。
dommy.each do |id, dres|
  next unless id.start_with?("frag:")

  bs = BROWSERS.map { |b| impls[b][id] }
  next if bs.any?(&:nil?)

  view = ->(r) { [r["error"], r["fragment"]] }
  bv = bs.map(&view)
  next if bv.uniq.size != 1 || bv[0] == view.(dres)

  groups[["fragment", "frag", id.split(":")[1]]] << [id, "fragment", { "dommy" => view.(dres), "browsers" => bv[0] }]
end

order = %w[write-decoy fast-path dommy-only write fragment dommy-missing]
groups.keys.sort_by { |cat, kind, pat| [order.index(cat), kind, pat] }.chunk_while { |a, b| a[0] == b[0] }.each do |chunk|
  puts "## #{chunk[0][0]}（#{chunk.size} 種類）"
  chunk.each do |key|
    rows = groups[key]
    id, k, v = rows.first
    puts "- #{key[1]}  #{key[2]}  × #{rows.size}"
    puts "    例: #{id}  #{k}  #{JSON.generate(v)[0, 220]}"
  end
  puts
end
puts "## browser が割れた行（Dommy は変わった）: #{split.size} 種類"
split.sort_by { |_, n| -n }.first(30).each { |(kind, pat), n| puts "- #{kind}  #{pat}  × #{n}" }
