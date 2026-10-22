import Url.Eval
import Url.Strict

/-!
# 仕様が定める、直感に反する振る舞い

URL Standard には、読み違えやすく、実装が実際に割れている振る舞いがある。
どれも「もっともらしい別の振る舞い」で書いても差分テスト以外では気づけない。
ここでは仕様どおりの結果を具体的な入力で固定する。

証明は `url_eval`（`Url/Eval.lean`）で、parser をその入力について計算して閉じる。
`native_decide` は使っていない。

各例の doc comment に、根拠になる本文の場所と、割れた実装を書く
（`docs/url-status.md` の「実装との突き合わせ」）。
-/

namespace Url

set_option maxRecDepth 8000

/-! ## state override 付きの失敗は、そこまでの書き換えを残す -/

/--
**`host` setter が port で失敗しても、host は書き換わったまま残る。**

host state が host を書いてから port state へ渡り、port state が 65536 で失敗する。
setter は basic URL parser の返り値を見ずに record をその場で書き換えるので、
port は元のまま、host だけが変わる（§6.1 host setter、§4.4 port state 2.1.2）。
WebKit は `https:` で port を消す。
-/
example : (({ scheme := "http", host := some (.domain "a"), port := some 8080,
                path := .list [""] } : Url).setHost "example.com:65536")
    = { scheme := "http", host := some (.domain "example.com"), port := some 8080,
        path := .list [""] } := by url_eval

/--
**`host` setter に `:80` を渡しても何も変わらない。**

host state は buffer が空のまま `:` に来たら失敗する（§4.4 host state 2.1）。
Node は host を空にして port を入れる。
-/
example : (({ scheme := "http", host := some (.domain "a"), path := .list [""] } : Url).setHost
      ":80") = { scheme := "http", host := some (.domain "a"), path := .list [""] } := by
  url_eval

/--
**`port` setter に空白だけを渡しても port は消えない。**

§6.1 port setter の「空文字列なら port を null に」は、tab と newline を取り除く**前**の値で判定する。
取り除いた後は空文字列なので、port state は何も書かずに終わる。Node は port を消す。
-/
example : (({ scheme := "http", host := some (.domain "a"), port := some 8080,
                path := .list [""] } : Url).setPort "\n\n\t\t")
    = { scheme := "http", host := some (.domain "a"), port := some 8080,
        path := .list [""] } := by url_eval

/--
**`hostname` setter に空文字列を渡すと、host の無い非 special な URL に空の host が付く。**

§6.1 hostname setter は host state を override 付きで走らせ、非 special なら空の buffer から
empty host を作る（§4.4 host state 3.1 の失敗は special だけに掛かる）。
`sc:/a` が `sc:///a` になる。Node は何も変えない。
-/
example : (({ scheme := "sc", path := .list ["a"] } : Url).setHostname "")
    = { scheme := "sc", host := some .empty, path := .list ["a"] } := by url_eval

/--
**empty host の URL には username を置けない。**

§4.2「cannot have a username/password/port」は host が null か空のとき真になる。
`sc:///` の `.empty` を `.opaque ""` で表していると、ここをすり抜けて `sc://u@/` ができる
（WPT が見つけた model 側の読み違い 4）。
-/
example : (({ scheme := "sc", host := some .empty, path := .list [""] } : Url).setUsername "u")
    = { scheme := "sc", host := some .empty, path := .list [""] } := by url_eval

/-! ## 区切りの読み方 -/

/--
**`#` は authority の中でも終端である。** `@` が後ろにあっても credentials にならない。

§4.4 authority state 2 は `#` を見たら buffer を host として読み直させる。
-/
example : basicUrlParse "http://a#b@c" none
    = some { scheme := "http", host := some (.domain "a"), path := .list [""],
             fragment := some "b@c" } := by url_eval

/--
**非 special な URL では、path が空のまま query へ進める。** `/` は足さない。

§4.4 path start state は、非 special で `?` なら path を空のまま query state へ渡す。
WebKit は `x://u:p@localhost/?a` にする。
-/
example : basicUrlParse "x://u:p@localhost?a" none
    = some { scheme := "x", username := "u", password := "p",
             host := some (.opaque "localhost"), path := .list [], query := some "a" } := by
  url_eval

/--
**素の相対参照は scheme state を EOF で抜けて no scheme state へやり直す。**

scheme state では EOF も「alphanumeric でも `+` `-` `.` でも `:` でもない」に当たる
（WPT が見つけた model 側の読み違い 2）。
-/
example : basicUrlParse "test"
      (some { scheme := "http", host := some (.domain "a"), path := .list ["b", "c"] })
    = some { scheme := "http", host := some (.domain "a"), path := .list ["b", "test"] } := by
  url_eval

/--
**"start over" は scheme state だけのものである。** host が壊れていても base に対する相対参照にはならない。

`http://[]` は host parser が失敗し、parse 全体が失敗する（WPT が見つけた model 側の読み違い 1）。
-/
example : basicUrlParse "http://[]"
      (some { scheme := "http", host := some (.domain "a"), path := .list [""] }) = none := by
  url_eval

/-! ## 正規化 -/

/--
**ASCII だけの domain には UTS #46 を掛けない。** `xn--8i7caa` は復号すると全角の `ｗｗｗ` で
UTS #46 の validity criteria を満たさないが、domain parser は ASCII の domain を小文字にして返すだけである
（§3.3 domain parser 5 と、その注記）。Node は ASCII の `xn--` label を失敗にする。
-/
example : basicUrlParse "http://xn--8i7caa/" none
    = some { scheme := "http", host := some (.domain "xn--8i7caa"), path := .list [""] } := by
  url_eval

/--
**`..` で path が空になった後の `c|` も drive letter として正規化する。**

§4.4 path state 1.4.1：scheme が `file` で path が空、buffer が Windows drive letter なら二文字目を `:` に。
「path が空」は `..` の後でも成り立つ。WebKit は `c|` のまま残す。
-/
example : basicUrlParse "file:///a/../c|" none
    = some { scheme := "file", host := some .empty, path := .list ["c:"] } := by url_eval

/-! ## `ValidUrl` だけでは往復しない

§4.1 は禁じていないが parser が作らない record は、serialize して parse し直すと別の record になる。
`roundtrip_canonical` が `canonicalUrl` を仮定に取るのはこのためである。
-/

/-- query の末尾の space は、前処理（§4.4 step 1）が落とす。 -/
example : basicUrlParse (urlSerializer { scheme := "sc", path := .opaque "", query := some " " })
      none = some { scheme := "sc", path := .opaque "", query := some "" } := by
  simp only [urlSerializer, serializerTail, pathSerializer]; url_eval

/-- 既定の port は、port state が null にする（§4.4 port state 2.1.3）。 -/
example : basicUrlParse (urlSerializer
      { scheme := "http", host := some (.domain "a"), port := some 80, path := .list [""] })
      none = some { scheme := "http", host := some (.domain "a"), path := .list [""] } := by
  rw [show urlSerializer { scheme := "http", host := some (.domain "a"), port := some 80,
                                path := .list [""] } = "http://a:80/" by decide]
  url_eval

/-- `..` の segment は、path state が畳む（§4.4 path state 1.2）。 -/
example : basicUrlParse (urlSerializer { scheme := "sc", path := .list [".."] }) none
    = some { scheme := "sc", path := .list [""] } := by
  simp only [urlSerializer, serializerTail, pathSerializer]; url_eval

end Url
