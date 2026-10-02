import Url.Record

/-!
# §4.1 のうち `ValidUrl` に入れていない条件

`ValidUrl` は URL Standard §4.1 が並べている条件の一部である。
残りをここに boolean として書き、WPT と setter の全 case で実行時に検査する。
Prop の側は `Url/StrictValid.lean` の `StrictConds` で、`checkStrictUrl_iff` が両者の一致を言う。
parse が返す record と setter を通した record がこれを満たすことは、そこで証明してある
（`basicUrlParse_strict`、`setAttr_strict`）。実行時の検査は、実装と証明が同じ定義を見ていることの
交差検証として残してある。

なぜ入れていないかは `ValidUrl` の doc comment に書いてある。要点は二つ。

* 「host が**空**なら **credentials** は持てない」を不変条件にするには、
  `PInv` が残りの入力を見る必要がある。成り立つ根拠が parser の guard
  （authority state の `atSignSeen && buffer.isEmpty`）にあり、その情報は
  host state へ**入力として**渡るためで、いまの `PInv` は `ctx.url` しか見ていない。
  同じ条文の **port** の側は `ValidUrl` に入れてある。port state へ入るのは
  host state の `:` の分岐だけで、そこは buffer が空なら失敗する
  （`hostParser_empty`：host parser が empty host を返すのは入力が空のときだけ）。
  「scheme が `file` なら」の側も入れてある（`PInv.notFile`）。
* 「special な URL の host は null でない」は終端でしか成り立たない。
  parse の途中では scheme が決まって host がまだ null の状態を必ず通る。

scheme と host の組み合わせ表（`hostKindOkOf`）と path segment の `/`（`pathSegsOk`）は
`ValidUrl` に入れた。後者は `PInv` が buffer を見るようにして通した
（path state が segment にするのは buffer で、そこに `/` は積まれない）。
-/

namespace Url

/--
IPv6 address が 8 piece で各 piece が 16 bit に収まること。

parser については `ipv6Parser_length` と `ipv6Parser_lt` が言う。URL record の host に入っている
`Ipv6` がその parser の出力であることは、parse の側は `canonicalUrl` の host の条件から、
setter の側は host state が host parser の出力を書くことから出る（`Url/StrictValid.lean`）。
-/
def ipv6Ok (u : Url) : Bool :=
  match u.host with
  | some (.ipv6 a) => a.length == 8 && a.all (fun p => p < 65536)
  | _ => true

/--
§4.1 のうち `ValidUrl` に入れていない条件。

* host が空なら credentials は持てない（port と `file` の側は `ValidUrl` に入れた）。
* special な URL の host は null でない。
* IPv6 address は 8 piece で各 piece は 16 bit。
-/
def checkStrictUrl (u : Url) : Bool :=
  let emptyHost := match u.host with | some .empty => true | _ => false
  (!emptyHost || !u.includesCredentials)
    && (!u.isSpecial || u.host.isSome)
    && ipv6Ok u

end Url
