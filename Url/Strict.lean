import Url.Record

/-!
# §4.1 のうち `ValidUrl` に入れていない条件

`ValidUrl` は URL Standard §4.1 が並べている条件の一部である。
残りをここに boolean として書き、WPT と setter の全 case で実行時に検査する。
証明に上げていないものを「無い」ことにしないための交差検証である。

なぜ入れていないかは `ValidUrl` の doc comment に書いてある。要点は二つ。

* 「host が空、または scheme が `file` なら credentials も port も持てない」を
  不変条件にするには、`PInv` が `ctx.atSignSeen` を持つ必要がある。
  成り立つ根拠が parser の guard（authority state の `atSignSeen && buffer.isEmpty`）に
  あるためで、いまの `PInv` は `ctx.url` しか見ていない。
* 「special な URL の host は null でない」は終端でしか成り立たない。
  parse の途中では scheme が決まって host がまだ null の状態を必ず通る。

scheme と host の組み合わせ表（`hostKindOkOf`）は不変条件にできるが、
そのためには `freshHost` を `relative` まで広げ、`fileHost` state では scheme が
`file` であることを足し、`hostParser` が返す host の種類の補題を用意する必要がある。
着手して芋づるになったので、いまは実行時の検査にとどめてある。
-/

namespace Url

/-- §4.1 の scheme と host の組み合わせ表。 -/
def hostKindOkOf (scheme : String) (host : Option Host) : Bool :=
  match host with
  | none => true
  | some (.ipv6 _) => true
  | some (.domain _) => isSpecialScheme scheme
  | some (.ipv4 _) => isSpecialScheme scheme
  | some (.opaque _) => !isSpecialScheme scheme
  | some .empty => !isSpecialScheme scheme || scheme == "file"

/-- §4.1「URL path segments never contain U+002F (/)」。 -/
def pathSegsOk (u : Url) : Bool :=
  match u.path with
  | .opaque _ => true
  | .list segs => segs.all fun s => !s.toList.contains '/'

/--
IPv6 address が 8 piece で各 piece が 16 bit に収まること。

長さは `ipv6Parser_length` で証明してあるが、piece の範囲は証明していない
（`ipv4InIpv6` の `let afterDot` が guard を隠すので、`ipv4InIpv6.induct` から
取り直したうえで `numbersSeen` の偶奇を記帳する必要がある）。ここで実行時に見る。
-/
def ipv6Ok (u : Url) : Bool :=
  match u.host with
  | some (.ipv6 a) => a.length == 8 && a.all (fun p => p < 65536)
  | _ => true

/--
§4.1 のうち `ValidUrl` に入れていない条件。

* host が空、または scheme が `file` なら credentials も port も持てない。
* scheme と host の組み合わせは表に従う。
* special な URL の host は null でない。
* path segment に `/` は含まれない。
* IPv6 address は 8 piece で各 piece は 16 bit。
-/
def checkStrictUrl (u : Url) : Bool :=
  let emptyHost := match u.host with | some .empty => true | _ => false
  let noCredPort := !u.includesCredentials && u.port.isNone
  (!emptyHost || noCredPort)
    && (!(u.scheme == "file") || noCredPort)
    && hostKindOkOf u.scheme u.host
    && (!u.isSpecial || u.host.isSome)
    && pathSegsOk u
    && ipv6Ok u

end Url
