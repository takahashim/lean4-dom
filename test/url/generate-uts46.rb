# frozen_string_literal: true

# `test/url/uts46-table.json` を Unicode の配布ファイルから作り直す。
#
#   ruby test/url/generate-uts46.rb DIR > test/url/uts46-table.json
#
# DIR に次の五つを置いておく（版は `docs/url-spec-version.md` に固定してある）。
#
#   IdnaMappingTable.txt          https://www.unicode.org/Public/17.0.0/idna/
#   DerivedCombiningClass.txt     https://www.unicode.org/Public/17.0.0/ucd/extracted/
#   DerivedBidiClass.txt          https://www.unicode.org/Public/17.0.0/ucd/extracted/
#   DerivedGeneralCategory.txt    https://www.unicode.org/Public/17.0.0/ucd/extracted/
#   DerivedNormalizationProps.txt https://www.unicode.org/Public/17.0.0/ucd/
#
# 表は証明の中には入れない（`docs/url-status.md` の「表は証明の外に置く」）。
# `Url/Idna.lean` の `IdnaTable` が interface で、これはその実装を与える data である。
# 読み込み側（`url-model`）が `checkResolved` で `IdnaTable.Resolved` を確かめる。

require "json"

VERSION = "Unicode 17.0.0"

# `Url.IdnaStatus` の値。`Url/Idna.lean` の `IdnaStatus` と対応させる。
VALID = 0
IGNORED = 1
MAPPED = 2
DISALLOWED = 4

# 各項の 4 番目の欄は bit の和。`url-model` の `idnaRangeOfJson` と対応させる。
# OUT_OF_MODEL は NFC・CheckBidi・CheckJoiners が効きうる code point（この model の対象外）。
# MARK は General_Category=Mark（Mn・Mc・Me）。UTS #46 §4.1 の validity criterion 6
# （label は Mark で始まってはならない）に使う。
OUT_OF_MODEL = 1
MARK = 2

# NFC の合成が効きうる Hangul。`Url/Idna.lean` は正規化を持たないので対象外にする。
HANGUL = [
  0x1100..0x11FF,  # Jamo
  0xA960..0xA97F,  # Jamo Extended-A
  0xAC00..0xD7A3,  # Syllables
  0xD7B0..0xD7FF   # Jamo Extended-B
].freeze

# `# ...` を落として `;` で切る。先頭欄は `XXXX` か `XXXX..YYYY`。
def each_entry(path)
  File.foreach(path) do |line|
    body = line.split("#", 2).first.to_s.strip
    next if body.empty?

    fields = body.split(";").map(&:strip)
    lo, _, hi = fields[0].partition("..")
    yield(lo.to_i(16), (hi.empty? ? lo : hi).to_i(16), fields[1..])
  end
end

# UseSTD3ASCIIRules = false、Transitional_Processing = false で読む。
# URL Standard の domain to ASCII は beStrict = false で呼ぶので、
# `disallowed_STD3_*` は STD3 の制限を外した側に倒れる。
def read_mapping(dir)
  table = {}
  each_entry(File.join(dir, "IdnaMappingTable.txt")) do |lo, hi, rest|
    status = rest[0]
    mapping = (rest[1] || "").split(/\s+/).reject(&:empty?).map { |h| h.to_i(16) }

    entry =
      case status
      when "valid" then [VALID, nil]
      when "ignored" then [IGNORED, nil]
      when "mapped" then [MAPPED, mapping]
      when "disallowed" then [DISALLOWED, nil]
      when "disallowed_STD3_valid" then [VALID, nil]
      when "disallowed_STD3_mapped" then [MAPPED, mapping]
      # Transitional_Processing = false では deviation は valid だが、
      # 版によって振る舞いが変わる code point なので対象外の印を付ける。
      when "deviation" then [VALID, nil, :deviation]
      else raise "未知の status: #{status}"
      end

    (lo..hi).each { |cp| table[cp] = entry }
  end
  table
end

# 正規化と Bidi が効きうる code point を集める。
def read_out_of_model(dir)
  oom = {}

  # 結合クラス ≠ 0。NFC の並べ替えが効く。
  each_entry(File.join(dir, "DerivedCombiningClass.txt")) do |lo, hi, rest|
    next if rest[0].to_i.zero?

    (lo..hi).each { |cp| oom[cp] = true }
  end

  # NFC_Quick_Check ≠ Yes。合成・分解が効く。
  each_entry(File.join(dir, "DerivedNormalizationProps.txt")) do |lo, hi, rest|
    next unless rest[0] == "NFC_QC"
    next if rest[1] == "Y"

    (lo..hi).each { |cp| oom[cp] = true }
  end

  # Bidi_Class が R / AL / AN。CheckBidi が効く。
  each_entry(File.join(dir, "DerivedBidiClass.txt")) do |lo, hi, rest|
    next unless %w[R AL AN].include?(rest[0])

    (lo..hi).each { |cp| oom[cp] = true }
  end

  HANGUL.each { |r| r.each { |cp| oom[cp] = true } }

  oom
end

# General_Category が Mark（Mn・Mc・Me）の code point を集める。
def read_marks(dir)
  marks = {}
  each_entry(File.join(dir, "DerivedGeneralCategory.txt")) do |lo, hi, rest|
    next unless %w[Mn Mc Me].include?(rest[0])

    (lo..hi).each { |cp| marks[cp] = true }
  end
  marks
end

def build_ranges(mapping, oom, marks)
  ranges = []
  (0..0x10FFFF).each do |cp|
    status, mapped, deviation = mapping.fetch(cp, [DISALLOWED, nil])
    flag = 0
    flag |= OUT_OF_MODEL if oom[cp] || deviation == :deviation
    flag |= MARK if marks[cp]
    key = [status, flag, mapped]

    last = ranges.last
    if last && last[:key] == key && last[:hi] == cp - 1
      last[:hi] = cp
    else
      ranges << { lo: cp, hi: cp, key: key }
    end
  end

  ranges.map do |r|
    status, flag, mapped = r[:key]
    row = [r[:lo], r[:hi], status, flag]
    row << mapped if status == MAPPED
    row
  end
end

dir = ARGV[0] or abort("使い方: ruby test/url/generate-uts46.rb DIR")
ranges = build_ranges(read_mapping(dir), read_out_of_model(dir), read_marks(dir))

note = "UTS #46 の写像表と、この model の対象外の印。" \
       "`UseSTD3ASCIIRules = false`、`Transitional_Processing = false` で解釈してある" \
       "（URL Standard の domain to ASCII が beStrict = false で呼ぶため）。" \
       "各項は [開始, 終了, status, flags] で、status が 2（mapped）のときだけ写像先が続く。" \
       "status は 0=valid, 1=ignored, 2=mapped, 4=disallowed。" \
       "flags は bit の和で、1 は outOfModel、2 は General_Category=Mark。" \
       "outOfModel は NFC・CheckBidi・CheckJoiners が効きうる code point の印で、" \
       "この model はそれらを扱わないので拒否する。" \
       "Mark は UTS #46 §4.1 の validity criterion 6（label は Mark で始まらない）に使う。"

puts JSON.generate(
  "_note" => note,
  "_source" => {
    "IdnaMappingTable" => "https://www.unicode.org/Public/idna/latest/IdnaMappingTable.txt",
    "version" => VERSION,
    "derived" => ["DerivedCombiningClass.txt", "DerivedBidiClass.txt", "DerivedNormalizationProps.txt",
                  "DerivedGeneralCategory.txt"]
  },
  "ranges" => ranges
)
