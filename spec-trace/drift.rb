# frozen_string_literal: true

# 固定した `dom.bs`（spec-trace/dom.json）と whatwg/dom の新しい版を比べ、
# 対応表（`Trace/`）が引き受けている step のうち、本文が変わったものを挙げる。
#
#   ruby spec-trace/drift.rb                    # main と比べる
#   ruby spec-trace/drift.rb --ref <sha|branch>
#   ruby spec-trace/drift.rb --bs path/to/dom.bs
#   ruby spec-trace/drift.rb --mapping map.json # 表（既定は spec-trace/map.json。`lake exe spec-trace` の出力）
#
# 終了コードは、表に載せた algorithm に変化があるか、どこにも分類されない新しい
# algorithm が現れたときに 1 になる。対象外の algorithm の変化は報告だけする。
#
# step の対応は hash で取る。同じ本文の step が別の番号に移ったものは「改番」、
# 本文が変わったものは「変更」として分けて出す。改番だけなら表の step 番号を
# 直せば済み、変更なら model の読み直しが要る。

require "json"
require_relative "extract"
require_relative "fetch"

ROOT = File.expand_path("..", __dir__)

def load_mapping(path)
  JSON.parse(File.read(path || File.join(ROOT, "spec-trace/map.json")))
end

def diff_steps(old, new)
  old_by_hash = old["steps"].group_by { |s| s["hash"] }
  new_by_hash = new["steps"].group_by { |s| s["hash"] }
  changed = []
  moved = []
  old["steps"].each do |s|
    if (cand = new_by_hash[s["hash"]])
      to = cand.map { |c| c["n"] }
      moved << [s["n"], to.join("/")] unless to.include?(s["n"])
    else
      changed << s
    end
  end
  added = new["steps"].reject { |s| old_by_hash.key?(s["hash"]) }
  { changed: changed, moved: moved, added: added }
end

ref = "main"
bs = nil
mapping_path = nil
while (a = ARGV.shift)
  case a
  when "--ref" then ref = ARGV.shift
  when "--bs" then bs = ARGV.shift
  when "--mapping" then mapping_path = ARGV.shift
  else abort "unknown option #{a}"
  end
end

snap = JSON.parse(File.read(File.join(ROOT, "spec-trace/dom.json")))
base = snap["commit"]
if bs
  head = "(#{bs})"
  src = File.read(bs)
else
  head = Trace::Fetch.resolve(ref)
  src = Trace::Fetch.dom_bs(head)
end
new_algs = Trace::Extract.run(src).to_h { |x| [x["key"], x] }
old_algs = snap["algorithms"].to_h { |x| [x["key"], x] }
mapping = load_mapping(mapping_path)
mapped = mapping["entries"].map { |e| e["alg"] }.to_set
exclusions = mapping["exclusions"].map { |x| x["target"] }

excluded = lambda do |alg|
  exclusions.include?(alg["key"]) || (alg["headings"] & exclusions).any?
end

report = +""
report << "# dom.bs の改訂と対応表\n\n"
report << "固定版 `#{base[0, 12]}` と `#{head[0, 12]}`（#{ref}）を比べた。\n\n"
unless bs || base == head
  commits = Trace::Fetch.commits_between(base, head)
  unless commits.empty?
    report << "その間の whatwg/dom の commit：\n\n"
    commits.each { |sha, msg| report << "* `#{sha}` #{msg}\n" }
    report << "\n"
  end
end

affected = 0
sections = { mapped: +"", excluded: +"" }
(old_algs.keys | new_algs.keys).each do |k|
  o = old_algs[k]
  n = new_algs[k]
  next if o && n && o["hash"] == n["hash"]

  bucket = mapped.include?(k) ? :mapped : :excluded
  text = +""
  if o.nil?
    link = "[#{k}](https://dom.spec.whatwg.org/##{k.sub(%r{/setter\z}, '')})"
    if excluded.call(n)
      sections[:excluded] << "* 新しい algorithm #{link}（§#{n['section']}）：対象外の見出しの下にある\n"
    else
      sections[:mapped] << "* **新しい algorithm** #{link}（§#{n['section']}）：表にも対象外にも無い。分類が要る。\n"
      affected += 1
    end
    next
  end
  if n.nil?
    text << "* **消えた algorithm** #{k}（§#{o['section']}）\n"
  else
    d = diff_steps(o, n)
    text << "* #{k}（§#{n['section']}）\n"
    text << "  * 見出しの段落が変わった\n" if d.values.all?(&:empty?)
    d[:changed].each { |s| text << "  * 変更：step #{s['n']}「#{s['text'][0, 80]}」\n" }
    d[:added].each { |s| text << "  * 追加：step #{s['n']}「#{s['text'][0, 80]}」\n" }
    d[:moved].each { |from, to| text << "  * 改番：step #{from} → #{to}\n" }
  end
  affected += 1 if bucket == :mapped
  sections[bucket] << text
end

report << "## 表に載せた algorithm\n\n"
report << (sections[:mapped].empty? ? "変化なし。\n" : sections[:mapped])
report << "\n## 対象外の algorithm（報告だけ）\n\n"
report << (sections[:excluded].empty? ? "変化なし。\n" : sections[:excluded])

puts report
if (summary = ENV["GITHUB_STEP_SUMMARY"])
  File.write(summary, report, mode: "a")
end
exit(affected.zero? ? 0 : 1)
