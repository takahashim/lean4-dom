import Url.Record

/-!
# §4.1 のうち `ValidUrl` に入れていない条件

`ValidUrl` は URL Standard §4.1 が並べている条件の一部である。
残りをここに boolean として書き、WPT と setter の全 case で実行時に検査する。
証明に上げていないものを「無い」ことにしないための交差検証である。

なぜ入れていないかは `ValidUrl` の doc comment に書いてある。要点は二つ。

* 「host が**空**なら credentials も port も持てない」を不変条件にするには、
  `PInv` が残りの入力を見る必要がある。成り立つ根拠が parser の guard
  （authority state の `atSignSeen && buffer.isEmpty`）にあり、その情報は
  host state へ**入力として**渡るためで、いまの `PInv` は `ctx.url` しか見ていない。
  同じ条文の「scheme が `file` なら」の側は `ValidUrl` に入れてある
  （state について「credentials や port を書く state では scheme が `file` でない」を
  `PInv.notFile` として持ち回れば済むので、入力を見る必要が無い）。
* 「special な URL の host は null でない」は終端でしか成り立たない。
  parse の途中では scheme が決まって host がまだ null の状態を必ず通る。

scheme と host の組み合わせ表（`hostKindOkOf`）は `ValidUrl` に入れた。
残りのうち path segment の `/` は、`PInv` が buffer を見れば不変条件にできる見込みがある。
-/

namespace Url

/-- §4.1「URL path segments never contain U+002F (/)」。 -/
def pathSegsOk (u : Url) : Bool :=
  match u.path with
  | .opaque _ => true
  | .list segs => segs.all fun s => !s.toList.contains '/'

/--
IPv6 address が 8 piece で各 piece が 16 bit に収まること。

どちらも parser については証明してある（`ipv6Parser_length`、`ipv6Parser_lt`）。
残っているのは、URL record の host に入っている `Ipv6` がその parser の出力だという
ところで、`hostParser` の spec が無いとつながらない。ここで実行時に見る。
-/
def ipv6Ok (u : Url) : Bool :=
  match u.host with
  | some (.ipv6 a) => a.length == 8 && a.all (fun p => p < 65536)
  | _ => true

/--
§4.1 のうち `ValidUrl` に入れていない条件。

* host が空なら credentials も port も持てない（`file` の側は `ValidUrl` に入れた）。
* special な URL の host は null でない。
* path segment に `/` は含まれない。
* IPv6 address は 8 piece で各 piece は 16 bit。
-/
def checkStrictUrl (u : Url) : Bool :=
  let emptyHost := match u.host with | some .empty => true | _ => false
  let noCredPort := !u.includesCredentials && u.port.isNone
  (!emptyHost || noCredPort)
    && (!u.isSpecial || u.host.isSome)
    && pathSegsOk u
    && ipv6Ok u

end Url
