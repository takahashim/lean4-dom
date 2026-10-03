# frozen_string_literal: true

# URL Standard の basic URL parser（`URL(input, base)`）を model と実装で突き合わせる。
#
# model の側は `url-model --parse-batch`（`parseUrl`）。実装は Dommy（`Dommy::URL.parse`）と、
# `test/url_js.mjs` を通した JS の実装（Node の組み込みの URL = Ada、whatwg-url、jsdom、Playwright の browser）である。
# 比べるのは失敗するかどうかと、成功したときの IDL attribute（href から hash まで）と origin。
#
# `--setters` を付けると、§6.1 の setter を突き合わせる。parse した URL の IDL attribute に値を
# 代入してから同じものを比べる。`href` の setter は parse そのもの（失敗すると TypeError）なので外す。
#
#   lake build url-model
#   BUNDLE_GEMFILE=/path/to/Gemfile bundle exec ruby test/url_diff.rb [--count N] [--seed N]
#       [--js node] [--js whatwg-url=/path/to/whatwg-url/index.js] [--js webkit] [--no-dommy] [--dump FILE]
#       [--setters]
#
# 入力は WPT の表（`test/url/wpt-ascii.json`）の全 case と、その変形、部品から組み立てた乱数の URL である。
# setter では WPT の `setters_tests.json`（`test/url/wpt-setters.json`）の全 case と、乱数の URL に
# setter ごとの値（とその変形）を当てたものである。
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
WPT_SETTERS = File.join(ROOT, "test/url/wpt-setters.json")
FIELDS = %w[href protocol username password host hostname port pathname search hash origin].freeze

options = { count: 3000, seed: 1, show: 15, js: [], dommy: true, dump: nil, setters: false }
OptionParser.new do |o|
  o.on("--count N", Integer) { |v| options[:count] = v }
  o.on("--seed N", Integer) { |v| options[:seed] = v }
  o.on("--show N", Integer) { |v| options[:show] = v }
  o.on("--js SPEC", "node / whatwg-url=PATH / jsdom=PATH（何度でも）") { |v| options[:js] << v }
  o.on("--no-dommy") { options[:dommy] = false }
  o.on("--dump FILE", "case と全実装の結果を JSON で書き出す") { |v| options[:dump] = v }
  o.on("--setters", "parser ではなく setter を突き合わせる") { options[:setters] = true }
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

# setter ごとの値。区切り文字、percent、port の境界、`file:`、IDNA など、setter の state override が
# 途中で止まる形を多めに入れてある。
SETTER_VALUES = {
  "protocol" => ["http", "https", "HTTPS", "file", "ws", "wss", "ftp", "sc", "x", "mailto", "javascript",
                 "a+b", "1a", "http:", "https://x", ":", "", "blob", "data", "FiLe:", "é", "h t"],
  "username" => ["", "u", "a b", "é", "a:b", "a@b", "%40", "a/b", "\t", "%zz", "a?b#c"],
  "password" => ["", "p", "a b", "é", "a:b", "a@b", "%3A", "a/b", "%zz", "a?b#c"],
  "host" => HOSTS + ["h:81", "h:", "example.com:65536", "[::1]:2", "a/b", "a?b", "a#b", "a\\b", "h:8a",
                     "é.com:1", "u@h", "h:80", "h:443", "0x7f.1:21"],
  "hostname" => HOSTS + ["h:81", "a/b", "a?b", "a#b", "u@h", "[::1]:2"],
  "port" => ["", "0", "80", "443", "8080", "65535", "65536", "1a", "a1", " 1", "-1", "00080", "21",
             "\t8", "8/", "8?", "8#", "4294967296"],
  "pathname" => ["", "/", "a", "/a/b", "..", "/../x", "a b", "%2e%2E", "c|", "/C:/x", "\\a\\b", "é",
                 "?x", "#x", "//x", "/./", "a/..", "`{}"],
  "search" => ["", "?", "a=b", "?a=b", "a b", "é", "'\"<>", "#x", "??", "%zz", "a+b"],
  "hash" => ["", "#", "f", "#f", "a b", "é", "`<>", "##", "%zz", "\u0000"]
}.freeze
SETTER_HREFS = ["http://h/a?q#f", "https://u:p@h:81/x", "file:///C:/a/b", "file://host/a", "sc://h/a",
                "sc:opaque", "mailto:x", "about:blank", "http://[::1]/", "ws://h", "data:,x", "x://u@h:1/",
                "javascript:alert(1)", "blob:http://h/u", "sc://", "sc:/a", "file:///", "http://1.2.3.4/"].freeze

rng = Random.new(options[:seed])
if options[:setters]
  wpt = JSON.parse(File.read(WPT_SETTERS))["cases"].reject { |c| c["setter"] == "href" }.map do |c|
    { "input" => c["href"], "base" => nil, "setter" => c["setter"], "value" => c["new_value"] }
  end
  wpt_values = wpt.group_by { |c| c["setter"] }.transform_values { |cs| cs.map { |c| c["value"] } }
  hrefs = wpt.map { |c| c["input"] }.uniq + SETTER_HREFS
  random = Array.new(options[:count]) do
    setter = SETTER_VALUES.keys.sample(random: rng)
    href = rng.rand(3).zero? ? built_input(rng) : hrefs.sample(random: rng)
    value = case rng.rand(4)
            when 0 then wpt_values.fetch(setter, [""]).sample(random: rng)
            when 1 then mutated(rng, SETTER_VALUES[setter].sample(random: rng))
            else SETTER_VALUES[setter].sample(random: rng)
            end
    { "input" => href, "base" => nil, "setter" => setter, "value" => value }
  end
else
  wpt = JSON.parse(File.read(WPT))["cases"].map { |c| { "input" => c["input"], "base" => c["base"] } }
  random = Array.new(options[:count]) do
    if rng.rand(3).zero?
      c = wpt.sample(random: rng)
      { "input" => mutated(rng, c["input"]), "base" => c["base"] }
    else
      { "input" => built_input(rng), "base" => BASES.sample(random: rng) }
    end
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
    u.public_send("#{c['setter']}=", c["value"]) if u && c["setter"]
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
what = options[:setters] ? "URL setter" : "URL parser"
puts "#{what}: #{cases.size} 件（WPT #{wpt.size}、乱数 seed=#{options[:seed]}）、model が成功 #{ok} 件"
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
  setter = c["setter"] ? " #{c['setter']}=#{c['value'].inspect}" : ""
  puts "DIFF input=#{c['input'].inspect} base=#{c['base'].inspect}#{setter}"
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
