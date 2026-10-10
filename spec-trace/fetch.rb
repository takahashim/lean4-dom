# frozen_string_literal: true

# whatwg/dom の `dom.bs` を取ってくる。

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
    def resolve(ref)
      return ref if ref.match?(/\A\h{40}\z/)

      JSON.parse(get("https://api.github.com/repos/#{REPO}/commits/#{ref}"))["sha"]
    end

    def dom_bs(commit)
      get("https://raw.githubusercontent.com/#{REPO}/#{commit}/dom.bs")
    end

    # commit の範囲で dom.bs に触れた commit（新しい順）。
    def commits_between(base, head)
      cmp = JSON.parse(get("https://api.github.com/repos/#{REPO}/compare/#{base}...#{head}"))
      cmp["commits"].map { |c| [c["sha"][0, 7], c["commit"]["message"].lines.first.strip] }.reverse
    rescue StandardError => e
      warn "commit の一覧を取れなかった: #{e.message}"
      []
    end
  end
end
