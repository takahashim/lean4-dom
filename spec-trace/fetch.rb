# frozen_string_literal: true

# whatwg の仕様の Bikeshed source（`dom.bs`・WebIDL の `index.bs`）を取ってくる。

require "net/http"
require "json"
require "uri"

module Trace
  module Fetch
    REPO = "whatwg/dom"

    module_function

    def get(url)
      uri = URI(url)
      req = Net::HTTP::Get.new(uri)
      req["User-Agent"] = "lean4-dom-trace"
      token = ENV["GITHUB_TOKEN"]
      req["Authorization"] = "Bearer #{token}" if token && uri.host == "api.github.com"
      res = Net::HTTP.start(uri.host, uri.port, use_ssl: true) { |h| h.request(req) }
      raise "GET #{url}: #{res.code}" unless res.is_a?(Net::HTTPSuccess)

      res.body.force_encoding(Encoding::UTF_8)
    end

    # branch 名や短い sha を、完全な commit sha にする。
    def resolve(ref, repo = REPO)
      return ref if ref.match?(/\A\h{40}\z/)

      JSON.parse(get("https://api.github.com/repos/#{repo}/commits/#{ref}"))["sha"]
    end

    def dom_bs(commit)
      get("https://raw.githubusercontent.com/#{REPO}/#{commit}/dom.bs")
    end

    # 仕様（`specs.rb` の設定）の source。
    def source(spec, commit)
      get("https://raw.githubusercontent.com/#{spec[:repo]}/#{commit}/#{spec[:file]}")
    end

    # commit の範囲の commit（新しい順）。
    def commits_between(base, head, repo = REPO)
      cmp = JSON.parse(get("https://api.github.com/repos/#{repo}/compare/#{base}...#{head}"))
      cmp["commits"].map { |c| [c["sha"][0, 7], c["commit"]["message"].lines.first.strip] }.reverse
    rescue StandardError => e
      warn "commit の一覧を取れなかった: #{e.message}"
      []
    end
  end
end
