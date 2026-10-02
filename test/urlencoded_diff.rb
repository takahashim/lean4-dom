# frozen_string_literal: true

# application/x-www-form-urlencoded parser（URL Standard §5.1）を model と Dommy で突き合わせる。
#
# model の側は `url-model --urlencoded-batch` で、§5.1 の parser（`parseUrlencodedString`）に
# 文字列の列をまとめて通す。関係仕様との一致は `Url/Spec/Urlencoded.lean` の
# `parseUrlencoded_iff` が証明している。
#
# Dommy の側は `Dommy::URLSearchParams` の文字列の parse である。公開の constructor は
# 先頭の `?` を一つ落とすが（`URLSearchParams` の constructor の step で、§5.1 ではない）、
# owner 付きで作るとその手前の §5.1 だけになるので、そちらを使う。
#
#   lake build url-model
#   BUNDLE_GEMFILE=/path/to/Gemfile bundle exec ruby test/urlencoded_diff.rb [--count N] [--seed N]
#
# 固定の case と、乱数で作った入力（区切り・`+`・percent-encode・不正な UTF-8 の列・非 ASCII を混ぜる）を流す。
# 不一致があれば入力と両者の出力を表示して終了コード 1 で終わる。

require "json"
require "optparse"
require "tempfile"
require "dommy"

ROOT = File.expand_path("..", __dir__)
MODEL = File.join(ROOT, ".lake/build/bin/url-model")

options = { count: 2000, seed: 1, show: 20 }
OptionParser.new do |o|
  o.on("--count N", Integer) { |v| options[:count] = v }
  o.on("--seed N", Integer) { |v| options[:seed] = v }
  o.on("--show N", Integer) { |v| options[:show] = v }
end.parse!

# 区切りの扱い、`+`、percent-decode、UTF-8 の復号の境目を一つずつ狙う。
FIXED = [
  "", "&", "&&", "=", "==", "a", "a=", "=b", "a=b", "a=b=c", "a&b", "a=1&&b=2&",
  "a+b=c+d", "%2B=%20", "a%3Db=c", "%26=%3D", "+", "%", "%2", "%G1", "%zz=1",
  "?a=b", "??a=b", "a=%",
  # 不正な UTF-8。Encoding Standard は maximal subpart ごとに U+FFFD を一つ出す。
  "%FF", "%C3", "%C3%28", "%E0%A0", "%E0%A0A", "%E0%80%80", "%ED%A0%80", "%F0%80%80",
  "%F0%90%80", "%F4%90%80%80", "%C0%AF", "%E2%82", "%E2%82%AC", "%80", "%80%80",
  # BOM。§5.1 は「UTF-8 decode without BOM」なので、先頭の BOM は落とさない。
  "%EF%BB%BF", "%EF%BB%BFa=b", "a=%EF%BB%BF",
  # 非 ASCII はそのまま UTF-8 として通る。
  "é=日", "\u{1F600}=%F0%9F%98%80", "a= "
].freeze

PLAIN = ["a", "b", "c", "=", "&", "+", "?", ";", "~", "*", "-", ".", "_", " ",
         "é", "日", "\u{1F600}", " ", "0", "9"].freeze
HEX = %w[0 1 2 3 7 8 9 A B C D E F a b c d e f].freeze
BYTES = %w[%E0 %A0 %80 %BF %C3 %FF %ED %F0 %90 %F4 %8F %EF %BB %C0 %AF %26 %3D %2B %20 %25].freeze

def random_input(rng)
  Array.new(rng.rand(0..12)) do
    case rng.rand(10)
    when 0..4 then PLAIN.sample(random: rng)
    when 5..6 then "%" + HEX.sample(random: rng) + HEX.sample(random: rng)
    when 7..8 then BYTES.sample(random: rng)
    else ["%", "%" + HEX.sample(random: rng), "%G" + HEX.sample(random: rng)].sample(random: rng)
    end
  end.join
end

def dommy_parse(input)
  Dommy::URLSearchParams.new(input, owner: Object.new).instance_variable_get(:@pairs)
end

def model_parse(inputs)
  Tempfile.create(["urlencoded", ".json"]) do |f|
    f.write(JSON.generate(inputs))
    f.flush
    out = IO.popen([MODEL, "--urlencoded-batch", f.path], &:read)
    abort "url-model が失敗した" unless $?.success?
    JSON.parse(out)
  end
end

rng = Random.new(options[:seed])
inputs = FIXED + Array.new(options[:count]) { random_input(rng) }
inputs = inputs.uniq

expected = model_parse(inputs)
mismatches = inputs.each_with_index.filter_map do |input, i|
  got = begin
    dommy_parse(input)
  rescue StandardError => e
    "#{e.class}: #{e.message}"
  end
  [input, expected[i], got] unless got == expected[i]
end

puts "urlencoded: #{inputs.size} 件（固定 #{FIXED.size}、乱数 seed=#{options[:seed]}）、" \
     "一致 #{inputs.size - mismatches.size} / 不一致 #{mismatches.size}"
mismatches.first(options[:show]).each do |input, model, dommy|
  puts "MISMATCH input=#{input.inspect}"
  puts "  model=#{model.inspect}"
  puts "  dommy=#{dommy.inspect}"
end
exit(mismatches.empty? ? 0 : 1)
