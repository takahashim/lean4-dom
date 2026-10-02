# frozen_string_literal: true

# 名前空間の囮の sweep を Dommy（QuickJS）で走らせる。
#
#   BUNDLE_GEMFILE=/path/to/dommy-js-quickjs/Gemfile \
#     bundle exec ruby test/decoy_dommy.rb NAMES.json OUT.json [CASE_PREFIX] [--ruby-path]
#
# `--ruby-path` は JS 側の attribute の snapshot（`__rb_host_attrs`）を外して、
# reflect の読みを必ず Ruby の getter に通す。既定はふつうの速い経路である。
# 二つを走らせて食い違えば、それだけで速い経路の不具合である。

require "json"
require "dommy"
require "dommy/js/quickjs"

ROOT = File.expand_path(__dir__)
SOURCE = File.read(File.join(ROOT, "js/decoy.js"))
FIXTURE = File.read(File.join(ROOT, "decoy/fixture.html"))

ruby_path = ARGV.delete("--ruby-path")
names_path, out_path, prefix = ARGV
prefix ||= ""
names_json = File.read(names_path)

def runtime
  win = Dommy.parse(FIXTURE)
  rt = Dommy::Js::Quickjs::Runtime.new
  rt.install_window(win)
  rt.define_host_object("document", win.document)
  rt.execute(SOURCE)
  rt
end

def evaluate_json(rt, expr)
  JSON.parse(rt.evaluate("JSON.stringify(#{expr})"))
end

disable = ruby_path ? "globalThis.__rb_host_attrs = undefined;" : ""
ids = evaluate_json(runtime, "__decoySweep.caseIds()")
results = ids.select { |id| id.start_with?(prefix) }.map do |id|
  rt = runtime
  rt.execute("#{disable} globalThis.__names = #{names_json};")
  evaluate_json(rt, "__decoySweep.runCase(#{id.to_json}, __names)")
rescue StandardError, ScriptError => e
  { "id" => id, "error" => "host:#{e.class}: #{e.message.lines.first}" }
end
File.write(out_path, JSON.generate({ "impl" => ruby_path ? "dommy-ruby" : "dommy", "results" => results }))
