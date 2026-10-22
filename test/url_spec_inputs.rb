# frozen_string_literal: true

# `url-model --spec-batch` に渡す乱数の入力を作る。
#
#   ruby test/url_spec_inputs.rb [--count N] [--seed N] [--schemes file,http] [--base] > inputs.json
#   lake exe url-model --spec-batch inputs.json test/url/uts46-table.json
#
# basic URL parser と関数的な仕様（`Url/Spec/Parse.lean`）が一致することは
# `Url.Spec.basicUrlParse_eq_specParse` が証明している。この入力は、仕様を書き換えたときに
# 証明より先に食い違いを安く見つけるためのものである。
# 区切り（`/` `?` `#` `@` `:` `[` `]`）、percent-encode、空白、dot segment を混ぜた片を並べる。

require "json"
require "optparse"

options = { count: 20_000, seed: 1, schemes: nil, base: false }
OptionParser.new do |o|
  o.on("--count N", Integer) { |v| options[:count] = v }
  o.on("--seed N", Integer) { |v| options[:seed] = v }
  o.on("--schemes LIST", "使う scheme をカンマ区切りで（既定は全部）") { |v| options[:schemes] = v.split(",") }
  o.on("--base", "base を付け、scheme の無い参照も混ぜる") { options[:base] = true }
end.parse!

rng = Random.new(options[:seed])
schemes = options[:schemes] ||
          %w[sc SC a+b web+demo x data javascript mailto non-spec blob http HTTP https ws wss ftp file]
atoms = ["/", "//", "///", "?", "#", "@", "@@", ":", "::", "[", "]", "[::1]", "[::1]:8", "%", "%2e",
         "%2E", ".", "..", "%40", " ", "  ", "\\", "\t", "\n", "a", "b", "h", "user", "pass", "u:p@",
         "80", "65535", "65536", "0x1", "1.2.3.4", "é", "日本", "%e2%98%83", "|", "c:", "c|", "^", "{",
         "}", "`", "\"", "<", ">", "'", "x y", "%zz", "&", "=", ";", "localhost", "LOCALHOST", "c:/", "C|", "/c:", "//c:"]

bases = ["http://h/a/b?q#f", "https://u:p@h:8/a/b/", "ws://h", "sc://h/a/b", "sc:/a/b", "sc:x", "about:blank",
         "file:///c:/a/b", "file:///C:", "file://host/x/y", "file:///a/b", "file:", "data:,x", "blob:http://h/u",
         "non-special://h:1/a/", "sc:/", "sc://"]

cases = Array.new(options[:count]) do
  s = options[:base] && rng.rand < 0.6 ? "" : "#{schemes.sample(random: rng)}:"
  rng.rand(0..8).times { s += atoms.sample(random: rng) }
  s = " #{s} " if rng.rand < 0.1
  c = { "input" => s }
  c["base"] = bases.sample(random: rng) if options[:base]
  c
end
puts JSON.generate(cases)
