# frozen_string_literal: true

# URL Standard の basic URL parser（`URL(input, base)`）を model と実装で突き合わせる。
#
# model の側は `url-model --parse-batch`（`parseUrl`）。実装は Dommy（`Dommy::URL.parse`）と、
# `test/url_js.mjs` を通した JS の実装（Node の組み込みの URL = Ada、whatwg-url、jsdom、Playwright の browser）である。
# 比べるのは失敗するかどうかと、成功したときの IDL attribute（href から hash まで）と origin。
#
#   lake build url-model
#   BUNDLE_GEMFILE=/path/to/Gemfile bundle exec ruby test/url_diff.rb [--count N] [--seed N]
#       [--js node] [--js whatwg-url=/path/to/whatwg-url/index.js] [--js webkit] [--no-dommy] [--dump FILE]
#
# 入力は WPT の表（`test/url/wpt-ascii.json`）の全 case と、その変形、部品から組み立てた乱数の URL である。
# 非 ASCII の domain を含むので、model には UTS #46 の表（`test/url/uts46-table.json`）を渡す。
#
# 一致は多数決ではない。model と一致しない実装を数えて、割れた case を全実装の結果と並べて出す。
# どちらが仕様どおりかは、出力を見て仕様の本文で決める（`docs/threats-to-validity.md` §5）。

require "json"
require "optparse"
require "tempfile"

ROOT = File.expand_path("..", __dir__)
MODEL = File.join(ROOT, ".lake/build/bin/url-model")
IDNA = File.join(ROOT, "test/url/uts46-table.json")
WPT = File.join(ROOT, "test/url/wpt-ascii.json")
FIELDS = %w[href protocol username password host hostname port pathname search hash origin].freeze

options = { count: 3000, seed: 1, show: 15, js: [], dommy: true, dump: nil }
OptionParser.new do |o|
  o.on("--count N", Integer) { |v| options[:count] = v }
  o.on("--seed N", Integer) { |v| options[:seed] = v }
  o.on("--show N", Integer) { |v| options[:show] = v }
  o.on("--js SPEC", "node / whatwg-url=PATH / jsdom=PATH（何度でも）") { |v| options[:js] << v }
  o.on("--no-dommy") { options[:dommy] = false }
  o.on("--dump FILE", "case と全実装の結果を JSON で書き出す") { |v| options[:dump] = v }
end.parse!

# ------------------------------------------------------------------ 入力の生成

SCHEMES = ["http", "https", "ws", "wss", "ftp", "file", "sc", "mailto", "javascript", "data",
           "blob", "HTTP", "Http", "a+b-c.d", "x"].freeze
AFTER_SCHEME = ["", "/", "//", "///", "\\", "\\\\", "/\\", "////"].freeze
USERINFO = ["", "", "", "u@", "u:p@", ":@", "@", "u@@", "a%40b@", "u:p:q@", "@@", "ü:é@"].freeze
HOSTS = ["h", "example.com", "EXAMPLE.com", "1.2.3.4", "0x7f.1", "127.1", "0177.0.0.1", "1.2.3.256",
         "4294967296", "1.2.3.4.", "[::1]", "[1:2::3:4]", "[::ffff:1.2.3.4]", "[::", "[]", "%41.com",
         "xn--ls8h", "a b", "a%20b", "", "localhost", "LOCALHOST", "日本.jp", "é.com", "c:", "c|", "h.",
         "..", "a^b", "0", "09", "0x", "1.2.3.09"].freeze
PORTS = ["", "", ":", ":80", ":443", ":0", ":65535", ":65536", ":8a", ":21"].freeze
SEGMENTS = [".", "..", "%2e", "%2E%2e", "a", "b c", "c|", "C:", "%2F", "é", "x?", "`{}", ""].freeze
QUERIES = ["", "", "?", "?a=b", "?'\"<>", "?a b", "?é"].freeze
FRAGMENTS = ["", "", "#", "#f", "#a b", "#`<>"].freeze
BASES = [nil, nil, nil, "http://h/a/b?q#f", "https://u:p@h:81/x", "file:///C:/a/b", "file://host/a",
         "sc://h/a", "sc:opaque", "mailto:x", "about:blank", "http://[::1]/"].freeze
NOISE = ["/", "\\", ":", "@", "?", "#", "%", "[", "]", ".", " ", "\t", "\n", "a", "1", "é"].freeze

def built_input(rng)
  path = Array.new(rng.rand(0..3)) { SEGMENTS.sample(random: rng) }
  sep = rng.rand(4).zero? ? "\\" : "/"
  scheme = rng.rand(6).zero? ? "" : "#{SCHEMES.sample(random: rng)}:"
  s = scheme + AFTER_SCHEME.sample(random: rng) + USERINFO.sample(random: rng) +
      HOSTS.sample(random: rng) + PORTS.sample(random: rng) +
      path.map { |p| sep + p }.join + QUERIES.sample(random: rng) + FRAGMENTS.sample(random: rng)
  s = " #{s} " if rng.rand(10).zero?
  s
end

def mutated(rng, s)
  chars = s.chars
  rng.rand(1..3).times do
    i = rng.rand(0..chars.size)
    case rng.rand(3)
    when 0 then chars.insert(i, NOISE.sample(random: rng))
    when 1 then chars.delete_at(i) unless chars.empty?
    else chars[i] = NOISE.sample(random: rng) if i < chars.size
    end
  end
  chars.join
end

wpt = JSON.parse(File.read(WPT))["cases"].map { |c| { "input" => c["input"], "base" => c["base"] } }
rng = Random.new(options[:seed])
random = Array.new(options[:count]) do
  if rng.rand(3).zero?
    c = wpt.sample(random: rng)
    { "input" => mutated(rng, c["input"]), "base" => c["base"] }
  else
    { "input" => built_input(rng), "base" => BASES.sample(random: rng) }
  end
end
cases = (wpt + random).uniq

# ------------------------------------------------------------------ 実行

def with_cases_file(cases)
  Tempfile.create(["url-cases", ".json"]) do |f|
    f.write(JSON.generate(cases))
    f.flush
    yield f.path
  end
end

results = {}
with_cases_file(cases) do |path|
  out = IO.popen([MODEL, "--parse-batch", path, IDNA], &:read)
  abort "url-model が失敗した" unless $?.success?
  results["model"] = JSON.parse(out)
  unless options[:js].empty?
    out = IO.popen(["node", File.join(ROOT, "test/url_js.mjs"), path, *options[:js]], &:read)
    abort "url_js.mjs が失敗した" unless $?.success?
    results.merge!(JSON.parse(out))
  end
end

if options[:dommy]
  require "dommy"
  results["dommy"] = cases.map do |c|
    u = Dommy::URL.parse(c["input"], c["base"])
    u && FIELDS.to_h { |f| [f, u.public_send(f).to_s] }
  rescue StandardError => e
    "#{e.class}: #{e.message}"
  end
end

# ------------------------------------------------------------------ 比較

# `file:` の origin は実装依存である（§4.7「読者への課題として残す。迷ったら opaque origin を返す」）。
# model は opaque（"null"）にし、browser には "file://" を返すものがある。`blob:` の中身が `file:` の
# ときも同じなので、この二つでは origin を比べない。
def comparable(r)
  return r unless r.is_a?(Hash)
  return r unless r["href"].start_with?("file:", "blob:file:")

  r.reject { |k, _| k == "origin" }
end

results.each_value { |rs| rs.map! { |r| comparable(r) } }

if options[:dump]
  File.write(options[:dump], JSON.generate({ "cases" => cases, "results" => results }))
end

impls = results.keys - ["model"]
ok = results["model"].count { |r| !r.nil? }
puts "URL parser: #{cases.size} 件（WPT #{wpt.size}、乱数 seed=#{options[:seed]}）、model が成功 #{ok} 件"
divergent = []
impls.each do |impl|
  bad = cases.each_index.reject { |i| results[impl][i] == results["model"][i] }
  puts "  #{impl.ljust(12)} 一致 #{cases.size - bad.size} / 不一致 #{bad.size}"
  divergent.concat(bad)
end

def summarize(r)
  return "failure" if r.nil?
  return r if r.is_a?(String)

  r["href"]
end

divergent.uniq.sort.first(options[:show]).each do |i|
  c = cases[i]
  puts "DIFF input=#{c['input'].inspect} base=#{c['base'].inspect}"
  ref = results["model"][i]
  results.each do |name, rs|
    r = rs[i]
    mark = r == ref ? " " : "*"
    detail = if r.is_a?(Hash) && ref.is_a?(Hash) && r != ref
               " (" + FIELDS.reject { |f| r[f] == ref[f] }.map { |f| "#{f}=#{r[f].inspect}" }.join(", ") + ")"
             else
               ""
             end
    puts "  #{mark} #{name.ljust(12)} #{summarize(r)}#{detail}"
  end
end
exit(divergent.empty? ? 0 : 1)
