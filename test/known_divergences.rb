# frozen_string_literal: true

# 実装が仕様から離れていて、こちらの findings ではないもの。
#
# `test/known-divergences.yml` を読み、(実装, scenario) で引く。
# 記録に当たった不一致は `:known` として報告し、失敗に数えない。
#
# **記録してよいのは「実装が仕様本文から離れていて、model が本文に従っている」場合だけ**
# である。model のほうが怪しいなら記録ではなく調査が要る。判断の拠り所は
# `docs/threats-to-validity.md` §5 にある。
#
# 各 entry は、記録したときの不一致の**形**を digest で固定する。
# 黙って形が変わったら当たらなくなり、ふつうの不一致として出る。
# 消えた divergence も報告する（記録を外す合図である）。

require "yaml"
require "digest"

module KnownDivergences
  PATH = File.join(__dir__, "known-divergences.yml")

  module_function

  def entries
    @entries ||=
      begin
        File.exist?(PATH) ? (YAML.safe_load_file(PATH, aliases: true) || []) : []
      rescue StandardError => e
        warn "警告: #{PATH} を読めない: #{e.message}"
        []
      end
  end

  # 不一致の「形」。messages をそのまま固定する。
  def digest(messages)
    Digest::SHA256.hexdigest(Array(messages).join("\n"))[0, 16]
  end

  def find(impl, scenario)
    entries.find { |e| e["impl"] == impl && e["scenario"] == scenario }
  end

  # [status, messages] を、記録に照らして読み替える。
  #
  # 戻り値の status は :known が増えるほかは元のままである。
  def apply(impl, scenario, status, messages)
    entry = find(impl, scenario)
    if status == :mismatch && entry
      d = digest(messages)
      return [:known, ["記録済みの divergence: #{entry['reason'].to_s.lines.first&.strip}"]] \
        if entry["digest"] == d

      return [:mismatch,
              messages + ["※ 記録済みの divergence と形が違う（記録 #{entry['digest']} / 今回 #{d}）。" \
                          "直ったか、別の理由で割れている。"]]
    end
    if status != :mismatch && entry
      return [status, messages + ["※ 記録済みの divergence が出なくなっている。" \
                                  "`test/known-divergences.yml` から外す。"]]
    end

    [status, messages]
  end
end
