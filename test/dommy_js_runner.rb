# frozen_string_literal: true

# Dommy を JavaScript の側から動かす scenario runner。
#
# `test/dommy_runner.rb` は Dommy の Ruby の API を直接呼ぶので、Dommy が JS の層（`js/host_runtime.js`）で行う
# WebIDL の変換（DOMString・boolean・可変長の引数の変換、引数の個数の検査ほか）を通らない。この runner は
# dommy-js-quickjs の QuickJS の中で、ブラウザ・jsdom と同じ `test/js/scenario.js` を Dommy の window に対して
# 走らせる。JavaScript から見た Dommy を測るので、変換の層まで含めて比べられる。
#
#   bundle exec ruby test/dommy_js_runner.rb --capabilities
#   bundle exec ruby test/dommy_js_runner.rb --batch DIR      # DIR/<base>.impl.json に書く
#   bundle exec ruby test/dommy_js_runner.rb SCENARIO.json
#
# Gemfile には dommy、makiri、dommy-js-quickjs、quickjs が要る（`test/README.md`）。
#
# **oracle は Lean の model だけである。** ここで動かす Dommy は準拠度を測られる側である。

require "json"
require "dommy"
require "dommy/js/quickjs"

module DommyJsRunner
  SCENARIO_JS = File.read(File.join(__dir__, "js/scenario.js"))
  BLANK = "<!DOCTYPE html><html><head></head><body></body></html>"

  module_function

  # scenario ごとに window と JS の実行環境を作り直す。使い回すと、前の scenario が document に付けた
  # listener や MutationObserver が残る（`js_runner.mjs` と同じ理由）。
  def runtime
    win = Dommy.parse(BLANK)
    rt = Dommy::Js::Quickjs::Runtime.new
    rt.define_host_object("document", win.document)
    rt.install_window(win)
    rt.execute(SCENARIO_JS)
    rt
  end

  # scenario を走らせ、結果を JSON の文字列で返す。値を JSON の文字列にしてから渡すのは、
  # JS の object が Ruby に渡るときの変換（node の wrapper など）を避けるためである。
  def run(scenario_json)
    rt = runtime
    rt.evaluate("JSON.stringify(globalThis.__domScenario.run(window, #{scenario_json}))")
  end

  def capabilities
    runtime.evaluate("JSON.stringify(globalThis.__domScenario.capabilities(window), null, 2)")
  end

  def scenario_file?(path)
    path.end_with?(".json") && !path.end_with?(".lean.json") && !path.end_with?(".impl.json")
  end

  def run_batch(dir)
    failed = 0
    Dir.children(dir).sort.each do |name|
      path = File.join(dir, name)
      next unless scenario_file?(path)

      out =
        begin
          run(File.read(path))
        rescue StandardError, ScriptError => e
          failed = 1
          JSON.generate({ "error" => "#{e.class}: #{e.message}" })
        end
      File.write(File.join(dir, "#{File.basename(name, '.json')}.impl.json"), out)
    end
    failed
  end
end

if $PROGRAM_NAME == __FILE__
  case ARGV[0]
  when "--capabilities"
    puts DommyJsRunner.capabilities
  when "--batch"
    dir = ARGV[1] or abort "usage: dommy_js_runner.rb --batch DIR"
    exit DommyJsRunner.run_batch(dir)
  when nil
    abort "usage: dommy_js_runner.rb [--capabilities|--batch DIR] SCENARIO.json"
  else
    begin
      puts DommyJsRunner.run(File.read(ARGV[0]))
    rescue StandardError, ScriptError => e
      warn "#{ARGV[0]}: 初期状態を組み立てられない: #{e.class}: #{e.message}"
      exit 1
    end
  end
end
