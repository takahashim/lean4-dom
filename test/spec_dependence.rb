# frozen_string_literal: true

# 関係意味論（`Dom/Spec/`）が実行側の algorithm に寄りかかっていないかを見る。
#
#   ruby test/spec_dependence.rb
#
# 実行関数そのものを意味論にすると、仕様の翻訳を誤ってもその誤った関数についての
# 定理は証明できてしまう。だから `Dom/Spec/` の関係は仕様本文から独立に書く
# （`Dom/Spec/Remove.lean` の冒頭を見よ）。この script はその規約が守られているかを、
# **関係の定義が実行側の名前を触っているか**で機械的に見る。
#
# §4.2.3 の関係（`Insert` / `Remove` / `Replace` / `Adopt` / `Move` / `Record`）は
# `Dom.Basic.*` しか import していないので、実行関数を呼びようがない。
# import graph がそのまま保証になっている。
#
# Selectors の関係（`Dom/Spec/Selector.lean`）は照合の実装と同じ module を見るので、
# import では守れない。触っているものが出たら、それが仕様の語彙として妥当か
# （`elementChildrenOf` のような薄い補助か、それとも照合そのものか）を人が判断する。
# 判断の結果は同 file の doc comment に書く。

ROOT = File.expand_path("..", __dir__)

def defs(globs)
  globs.flat_map { |g| Dir[File.join(ROOT, g)] }.flat_map do |path|
    File.readlines(path, chomp: true).filter_map do |line|
      # `def Tree.withNode` のような名前は最後の成分だけを見る。
      # 全体を拾うと `Tree` が実行側の名前として数えられてしまう。
      m = line.match(/\A\s*(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:noncomputable\s+)?(?:def|abbrev)\s+([A-Za-z_][A-Za-z0-9_'!?.]*)/)
      m && m[1].split(".").last
    end
  end.to_set
end

IMPL = defs(["Dom/Mutation/*.lean", "Dom/Range/Api.lean", "Dom/Selector/Match.lean",
             "Dom/Selector/Api.lean", "Dom/CharacterData/*.lean", "Dom/Observer/*.lean",
             "Dom/Traversal/*.lean"])
VOCAB = defs(["Dom/Basic/*.lean", "Infra/*.lean", "Dom/Range/BoundaryPoint.lean"])
ALGORITHMS = IMPL - VOCAB

require "set"

rows = []
Dir[File.join(ROOT, "Dom/Spec/*.lean")].sort.each do |path|
  src = File.read(path)
  src.scan(/^def\s+([A-Za-z_][A-Za-z0-9_']*)\s*(.*?)$(.*?)(?=^(?:def|theorem|end|\/--|\/-!)|\z)/m) do
    name, sig, body = Regexp.last_match(1), Regexp.last_match(2), Regexp.last_match(3)
    used = body.scan(/[A-Za-z_][A-Za-z0-9_'!?]*/).uniq.select { |w| ALGORITHMS.include?(w) }.sort
    next if used.empty?

    rows << [File.basename(path), name, sig.include?("Prop") ? "Prop" : "", used]
  end
end

if rows.empty?
  puts "関係の定義が実行側に触れている箇所は無い。"
else
  puts "関係の定義が触れている実行側の名前:"
  rows.each { |f, n, k, u| puts format("  %-22s %-32s %-5s %s", f, n, k, u.join(", ")) }
  puts
  puts "触れていること自体は誤りではない。仕様が「S に当たるもの」のように"
  puts "照合を使って定義している箇所はあるので、妥当かどうかは人が判断して"
  puts "同 file の doc comment に書く。"
end
