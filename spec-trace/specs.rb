# frozen_string_literal: true

# 対応表を作る仕様ごとの設定。`--spec NAME` で選ぶ（既定は dom）。
#
#   repo      取得元の GitHub の repository
#   file      Bikeshed の source の file 名
#   parser    :html は step を `<ol>` で書く仕様（`extract.rb`）、:md は markdown の番号付きリストで書く仕様（`extract_md.rb`）
#   pinned    test/pinned-versions.json の鍵
#   snapshot  固定した版から抜き出した algorithm の一覧
#   map       `lake exe spec-trace NAME` の出力（対応表）
#   doc       生成する文書
#   site      描画された仕様の URL（commit snapshot と anchor の前に付ける）
#   link      :snapshot は描画された commit snapshot の anchor、:source は固定した commit の source の行に張る

module Trace
  SPECS = {
    "dom" => {
      title: "DOM Standard", repo: "whatwg/dom", file: "dom.bs", parser: :html, pinned: "spec",
      snapshot: "spec-trace/dom.json", map: "spec-trace/map.json", doc: "docs/spec-coverage.md",
      site: "https://dom.spec.whatwg.org"
    },
    "webidl" => {
      title: "Web IDL Standard", repo: "whatwg/webidl", file: "index.bs", parser: :md, pinned: "webidl",
      snapshot: "spec-trace/webidl.json", map: "spec-trace/webidl-map.json",
      doc: "docs/spec-coverage-webidl.md", site: "https://webidl.spec.whatwg.org"
    },
    "ecma262" => {
      title: "ECMA-262", repo: "tc39/ecma262", file: "spec.html", parser: :ecma, pinned: "ecma262",
      snapshot: "spec-trace/ecma262.json", map: "spec-trace/ecma262-map.json",
      doc: "docs/spec-coverage-ecma262.md", site: "https://tc39.es/ecma262", link: :source
    }
  }.freeze

  def self.spec(name)
    SPECS.fetch(name) { abort "未知の仕様 #{name}（#{SPECS.keys.join(', ')}）" }
  end

  # source から algorithm を抜き出す。
  def self.extract(name, src)
    case spec(name)[:parser]
    when :html then Extract.run(src)
    when :md
      require_relative "extract_md"
      ExtractMd.run(src)
    when :ecma
      require_relative "extract_ecma"
      ExtractEcma.run(src)
    end
  end
end
