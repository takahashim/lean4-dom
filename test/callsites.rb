# frozen_string_literal: true

# **guard が仕様より厳しい primitive の呼び出し元**を機械的に固定する。
#
#   ruby test/callsites.rb
#
# model の primitive には、仕様が algorithm 側に置いている検査を primitive 側に
# 持たせているものがある。`insertAt` の「`child` は `parent` の子」がそれで、
# 仕様はこれを `pre-insert` の validity（step 3）に置き、`move` の側には置いていない。
#
# そのため `move` を `child = node` で呼ぶと、仕様は「先頭に入れる」（外した後の
# `node` の index は 0 だから）のに対し、model は `notFoundError` を返す。
# **この差が観測できないことの根拠は「その呼び方をする経路が無い」ことだけ**なので、
# 呼び出し元をここで固定する。破れたら差が観測できるようになる。
#
# Lean 側の対になる定理は `Dom.moveBefore_reference_ne`
# （`moveBefore` が `move` に渡す reference child は `node` 自身にならない）である。
# 二つ合わせて「`move` の `child = node` の枝に届く経路は無い」になる。

ROOT = File.expand_path("..", __dir__)

# primitive => 呼んでよい実行定義（`def`）の名前。自分自身（再帰）は常に許す。
EXPECTED = {
  "move" => ["moveBefore"]
}.freeze

DEF_RE = /^(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:noncomputable\s+)?def\s+([A-Za-z_][A-Za-z0-9_'!?.]*)/

# `def` の本体（次の `def` / `theorem` / doc comment まで）を切り出す。
def each_def_body
  Dir[File.join(ROOT, "Dom/**/*.lean")].sort.each do |path|
    src = File.read(path)
    starts = src.enum_for(:scan, DEF_RE).map { Regexp.last_match }
    starts.each_with_index do |m, i|
      stop = i + 1 < starts.size ? starts[i + 1].begin(0) : src.length
      body = src[m.end(0)...stop]
      cut = body.index(/^(?:theorem|example|end|\/--|\/-!)/)
      body = body[0...cut] if cut
      yield path.delete_prefix("#{ROOT}/"), m[1].split(".").last, body
    end
  end
end

def calls?(body, name)
  body.match?(/(?<![A-Za-z0-9_])#{Regexp.escape(name)}(?![A-Za-z0-9_'])/)
end

actual = Hash.new { |h, k| h[k] = [] }
each_def_body do |path, name, body|
  EXPECTED.each_key do |prim|
    next if name == prim

    actual[prim] << [name, path] if calls?(body, prim)
  end
end

failed = false
EXPECTED.each do |prim, allowed|
  callers = actual[prim].map(&:first).uniq.sort
  extra = callers - allowed
  missing = allowed - callers
  if extra.empty? && missing.empty?
    puts "#{prim} を呼ぶ実行定義: #{callers.join(', ')}（想定どおり）"
  else
    failed = true
    puts "#{prim} を呼ぶ実行定義が想定と違う"
    puts "  想定: #{allowed.join(', ')}"
    puts "  実際: #{callers.join(', ')}"
    extra.each { |c| puts "  増えた: #{c}（#{actual[prim].find { |n, _| n == c }&.last}）" }
    missing.each { |c| puts "  消えた: #{c}" }
  end
end

exit(failed ? 1 : 0)
