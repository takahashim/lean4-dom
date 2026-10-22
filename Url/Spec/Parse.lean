import Url.Spec.Resolve

/-!
# basic URL parser の関数的な仕様（§4.4、base 無し・special でない scheme）

state も pointer も buffer も持たない形で、入力を成分に切り分け、成分ごとに正規化する
（RFC 3986 §3 と同じ発想）。parser と構造が違うので、同じ読み違いが両方に入りにくい。

1. scheme を切り出す（`splitScheme`）。
2. 残りを fragment（最初の `#` の後）、query（その手前の最初の `?` の後）、hier-part に分ける（`splitRef`）。
   `?` と `#` は authority でも host でも path でも終端なので、先に切ってよい。
3. hier-part が `//` で始まれば authority と path、`/` で始まれば path だけ、それ以外は opaque path。
4. authority は**最後の** `@` で userinfo と host-port に分け、host-port は bracket の外の最初の `:` で分ける。
5. 成分ごとに正規化する。

parser の `run`・`step`・`PCtx`・`userinfoStep`・`portDone`・`queryOf`・`pathStepUrl`・`shortenPath` は呼ばない。
共有するのは前処理（`preprocess`、§4.4 step 1-3）、host parser（§3.2）、percent-encode（§1.3）、
§4.2 の special scheme と既定の port、§4.4 冒頭の定義である。

ここでは special でない scheme だけを扱う（計画の M1）。special な scheme、base、`file` は後の段階である。
-/

namespace Url.Spec

open Infra Url

/-! ## 切り分け -/

/--
§4.4 scheme start state と scheme state。先頭が ASCII alpha で、scheme の文字が続いて `:` に至れば、
小文字にした scheme と `:` の後ろを返す。
-/
def splitScheme : List Char → Option (String × List Char)
  | a :: rest =>
    if isAsciiAlpha a then
      match rest.dropWhile isSchemeTail with
      | ':' :: r => some (String.ofList ((a :: rest.takeWhile isSchemeTail).map asciiLowerChar), r)
      | _ => none
    else none
  | [] => none

/-- 最後の `d` で分ける。`d` が無ければ前は null。 -/
def splitLast (d : Char) (l : List Char) : Option (List Char) × List Char :=
  match splitFirst d l.reverse with
  | (a, some r) => (some r.reverse, a.reverse)
  | (_, none) => (none, l)

/--
host と port を分ける。bracket の外の最初の `:` で分ける。

§4.4 host state 3 は `[` で bracket の中に入り、`]` で出る（入れ子は数えない）。
`inside` はいま bracket の中にいるか。
-/
def splitHostPort (inside : Bool) : List Char → List Char × Option (List Char)
  | [] => ([], none)
  | c :: t =>
    if c == ':' && !inside then ([], some t)
    else
      let ib := if c == '[' then true else if c == ']' then false else inside
      (c :: (splitHostPort ib t).1, (splitHostPort ib t).2)

/-! ## 成分の正規化 -/

/--
§4.4 authority state 1：userinfo を最初の `:` で username と password に分け、
どちらも userinfo percent-encode set で encode する。

userinfo の中の `@` は userinfo set に入るので `%40` になる。parser が二つ目以降の `@` の前に
`%40` を足すのと同じ結果である。
-/
def userinfoParts : Option (List Char) → String × String
  | none => ("", "")
  | some ui =>
    let (u, p) := splitFirst ':' ui
    (String.ofList (utf8PercentEncode userinfoSet u),
     String.ofList (utf8PercentEncode userinfoSet (p.getD [])))

/--
§4.4 port state 2.1：10 進の数字だけなら値、65535 を超えれば失敗、既定 port なら null。
数字でない文字があれば失敗（port state 3）。外側の `none` が失敗。
-/
def specPort (scheme : String) : Option (List Char) → Option (Option Nat)
  | none => some none
  | some p =>
    if p.all isAsciiDigit then
      if p.isEmpty then some none
      else if decimalOf p < 65536 then
        some (if defaultPort scheme = some (decimalOf p) then none else some (decimalOf p))
      else none
    else none

/--
§4.4 opaque path state。c0 control percent-encode set で encode する。
最後の文字が space で、その後に query か fragment が続くなら、その space は `%20`（opaque path state 3）。
-/
def opaqueText (hier : List Char) (terminated : Bool) : String :=
  if terminated && hier.getLast? == some ' ' then
    String.ofList (utf8PercentEncode c0ControlSet hier.dropLast) ++ "%20"
  else String.ofList (utf8PercentEncode c0ControlSet hier)

/-- path 部分（先頭の `/` の後ろ）を空の path から畳む。無ければ空の path。 -/
def pathFrom (special : Bool) : Option (List Char) → List String
  | none => []
  | some pp => resolveSegs false [] (pathSegments special pp)

/-! ## 組み立て -/

/--
**special でない scheme の URL の、base 無しの parse。** `rest` は scheme の `:` の後ろ。

| hier-part | 結果 | 本文 |
| --- | --- | --- |
| `//` authority path | userinfo・host・port・path | path or authority state 1、authority state、host state、port state、path start state |
| `/` path | path だけ（host は null） | path or authority state 2、path state |
| それ以外 | opaque path | scheme state 2.8、opaque path state |
-/
def specParseNonSpecial (toAscii : List Char → Option String) (scheme : String)
    (rest : List Char) : Option Url :=
  let r := splitRef rest
  let base : Url :=
    { scheme, query := r.2.1.map (queryText false), fragment := r.2.2.map fragmentText }
  match r.1 with
  | '/' :: '/' :: ap =>
    let (auth, pathPart) := splitFirst '/' ap
    let (ui, hp) := splitLast '@' auth
    -- authority state 2.1：`@` の後に host が無ければ失敗。
    if ui.isSome && hp.isEmpty then none
    else
      let (h, p) := splitHostPort false hp
      -- host state 2.1：host が空のまま `:` に来れば失敗。
      if h.isEmpty && p.isSome then none
      else
        match hostParser toAscii h true, specPort scheme p with
        | some host, some port =>
          some { base with username := (userinfoParts ui).1, password := (userinfoParts ui).2,
                           host := some host, port, path := .list (pathFrom false pathPart) }
        | _, _ => none
  | '/' :: pp => some { base with path := .list (pathFrom false (some pp)) }
  | hier => some { base with path := .opaque (opaqueText hier (r.2.1.isSome || r.2.2.isSome)) }

/-- special な URL の区切り（`/` と `\`）。 -/
def isSlashBS (c : Char) : Bool := c == '/' || c == '\\'

/-- 最初の区切り（`p` を満たす文字）で分ける。区切りが無ければ後ろは null。 -/
def splitFirstBy (p : Char → Bool) : List Char → List Char × Option (List Char)
  | [] => ([], none)
  | c :: t => if p c then ([], some t) else (c :: (splitFirstBy p t).1, (splitFirstBy p t).2)

/--
**special な scheme（`file` を除く）の URL の、base 無しの parse。** `rest` は scheme の `:` の後ろ。

* special authority slashes state と special authority ignore slashes state は、先頭の `/` と `\` を
  いくつでも読み飛ばす（二つでなくてもよい。validation error になるだけ）。
* authority は最初の `/` か `\` まで。最後の `@` で userinfo と host-port に分ける。
* host が空なら失敗する（host state 2.1・3.1）。host は domain か IPv4 か IPv6（opaque host ではない）。
* path は `/` と `\` を区切りにして畳む。path が無くても空の segment が一つ残る（path start state 1）。
-/
def specParseSpecial (toAscii : List Char → Option String) (scheme : String)
    (rest : List Char) : Option Url :=
  let r := splitRef (rest.dropWhile isSlashBS)
  let base : Url :=
    { scheme, query := r.2.1.map (queryText true), fragment := r.2.2.map fragmentText }
  let (auth, pathPart) := splitFirstBy isSlashBS r.1
  let (ui, hp) := splitLast '@' auth
  -- authority state 2.1：`@` の後に host が無ければ失敗。
  if ui.isSome && hp.isEmpty then none
  else
    let (h, p) := splitHostPort false hp
    -- host state 2.1・3.1：special な URL の host は空にできない。
    if h.isEmpty then none
    else
      match hostParser toAscii h false, specPort scheme p with
      | some host, some port =>
        some { base with username := (userinfoParts ui).1, password := (userinfoParts ui).2,
                         host := some host, port,
                         path := .list (resolveSegs false [] (pathSegments true (pathPart.getD []))) }
      | _, _ => none

/--
**`file` URL の、base 無しの parse。** `rest` は `file:` の後ろ。

* hier-part が区切りを二つ続けて始まれば、次の区切りまでが host（file host state）。
  * それが Windows drive letter なら host ではなく path の先頭 segment で、host は空のまま（file host state 1.1）。
  * 空なら host は空。`localhost` も空の host にする（file host state 1.3.3）。
* 区切りが一つだけなら host は空で、残りが path（file slash state 2）。
* 区切りで始まらなければ host は空で、hier-part 全体が path（file state 4）。

path は special な URL と同じく `/` と `\` で区切り、`file` の規則（先頭の drive letter の正規化と、
drive letter を shorten で落とさないこと）で畳む。
-/
def specParseFile (toAscii : List Char → Option String) (rest : List Char) : Option Url :=
  let r := splitRef rest
  let base : Url :=
    { scheme := "file", host := some .empty, query := r.2.1.map (queryText true),
      fragment := r.2.2.map fragmentText }
  let pathOf (l : List Char) : Path := .list (resolveSegs true [] (pathSegments true l))
  match r.1 with
  | s1 :: s2 :: X =>
    if isSlashBS s1 && isSlashBS s2 then
      let (hs, pathPart) := splitFirstBy isSlashBS X
      if isWindowsDrive hs then some { base with path := pathOf X }
      else if hs.isEmpty then some { base with path := pathOf (pathPart.getD []) }
      else
        match hostParser toAscii hs false with
        | none => none
        | some h =>
          some { base with host := some (if hostSerializer h = "localhost" then .empty else h),
                           path := pathOf (pathPart.getD []) }
    else if isSlashBS s1 then some { base with path := pathOf (s2 :: X) }
    else some { base with path := pathOf (s1 :: s2 :: X) }
  | [s1] => some { base with path := pathOf (if isSlashBS s1 then [] else [s1]) }
  | [] => some { base with path := pathOf [] }

/-- scheme を持つ入力の parse（base 無し）。 -/
def specParse (toAscii : List Char → Option String) (input : List Char) : Option Url :=
  match splitScheme input with
  | some (s, rest) =>
    if s = "file" then specParseFile toAscii rest
    else if isSpecialScheme s then specParseSpecial toAscii s rest
    else specParseNonSpecial toAscii s rest
  | none => none

/-! ## base を持つ入力 -/

/--
**相対参照の解決**（base `b` は opaque path を持たず、`file` でもない）。`l` は scheme を除いた参照。

| 参照 | 結果 | 本文 |
| --- | --- | --- |
| 空、`?q`、`#f` | base の path を残し、query は `?` があれば差し替え、fragment は参照のもの | relative state 2.3-2.5 |
| 区切り二つ（special なら `/` か `\\`、そうでなければ `//`） | base の scheme で authority から読み直す | relative slash state 1-2 |
| 区切り一つ | base の credentials・host・port と、空の path から畳んだ path | relative slash state 3 |
| それ以外 | base の path を shorten したところから畳んだ path | relative state 2.8 |
-/
def relRef (toAscii : List Char → Option String) (b : Url) (l : List Char) : Option Url :=
  match b.path with
  | .opaque _ => none
  | .list Pb =>
    let sp := b.isSpecial
    let r := splitRef l
    let absRef (x : List Char) : Option Url :=
      some (refResolved b (resolveSegs false [] (pathSegments sp (splitRef x).1))
        (splitRef x).2.1 (splitRef x).2.2)
    match l with
    | [] => some { b with fragment := none }
    | c :: x =>
      if c = '?' ∨ c = '#' then
        some { b with query := if r.2.1.isSome then r.2.1.map (queryText sp) else b.query,
                      fragment := r.2.2.map fragmentText }
      else if isPathSep sp c then
        match x with
        | d :: x' =>
          if sp && isSlashBS d then specParseSpecial toAscii b.scheme x'
          else if !sp && d == '/' then specParseNonSpecial toAscii b.scheme ('/' :: '/' :: x')
          else absRef x
        | [] => absRef []
      else
        some (refResolved b (resolveSegs false (shorten false Pb) (pathSegments sp r.1)) r.2.1 r.2.2)

/--
`file` URL の parse で、base も `file` のとき。区切り二つで始まれば base を使わない（file host state）。

* 区切り一つなら base の host を引き継ぎ、base の path の先頭が正規化された drive letter で、
  参照が drive letter で始まらなければ、その drive letter を path の先頭に残す（file slash state 2.1）。
* 区切りで始まらず、空か `?` か `#` で始まれば、base の host と path を引き継ぐ（file state 4.1-4.3）。
* それ以外は base の host を引き継ぎ、参照が drive letter で始まれば空の path から、
  そうでなければ base の path を shorten したところから畳む（file state 4.4）。
-/
def specParseFileBase (toAscii : List Char → Option String) (b : Url) (l : List Char) : Option Url :=
  let r := splitRef l
  let fileUrl (host : Option Host) (path : List String) (q : Option String) : Url :=
    { scheme := "file", host, path := .list path, query := q, fragment := r.2.2.map fragmentText }
  match l with
  | c1 :: x =>
    if isSlashBS c1 then
      match x with
      | c2 :: _ =>
        if isSlashBS c2 then specParseFile toAscii l
        else
          some (fileUrl b.host (resolveSegs true (driveOf b x) (pathSegments true (splitRef x).1))
            ((splitRef x).2.1.map (queryText true)))
      | [] => some (fileUrl b.host (resolveSegs true (driveOf b []) (pathSegments true [])) none)
    else if c1 = '?' ∨ c1 = '#' then
      some (fileUrl b.host (match b.path with | .list P => P | .opaque _ => [])
        (if r.2.1.isSome then r.2.1.map (queryText true) else b.query))
    else
      some (fileUrl b.host
        (resolveSegs true (if startsWithWindowsDrive l then [] else shorten true (pathList b))
          (pathSegments true r.1))
        (r.2.1.map (queryText true)))
  | [] => some (fileUrl b.host (pathList b) b.query)
where
  /-- base の path の segment の列（opaque なら空）。 -/
  pathList (b : Url) : List String := match b.path with | .list P => P | .opaque _ => []
  /-- file slash state 2.1：base の先頭の drive letter を残すかどうか。 -/
  driveOf (b : Url) (x : List Char) : List String :=
    match b.path with
    | .list (s :: _) => if !startsWithWindowsDrive x && isNormalizedWindowsDrive s.toList then [s] else []
    | _ => []

/-- **base `b` を持つ入力の parse。** -/
def specParseBase (toAscii : List Char → Option String) (b : Url) (input : List Char) : Option Url :=
  match splitScheme input with
  | some (s, rest) =>
    if s = "file" then
      if b.scheme = "file" then specParseFileBase toAscii b rest else specParseFile toAscii rest
    else if isSpecialScheme s && b.scheme == s then
      match rest with
      | '/' :: '/' :: _ => specParseSpecial toAscii s rest
      | _ => relRef toAscii b rest
    else if isSpecialScheme s then specParseSpecial toAscii s rest
    else specParseNonSpecial toAscii s rest
  | none =>
    match b.path with
    | .opaque _ =>
      match input with
      | '#' :: f => some { scheme := b.scheme, path := b.path, query := b.query,
                           fragment := some (fragmentText f) }
      | _ => none
    | .list _ => if b.scheme = "file" then specParseFileBase toAscii b input else relRef toAscii b input

/-- **`URL(input, base)` の関数的な仕様。** base も同じ仕様で parse し、失敗すれば全体が失敗する（API URL parser）。 -/
def specParseUrl (toAscii : List Char → Option String) (input : String) (base : Option String) :
    Option Url :=
  match base with
  | none => specParse toAscii (preprocess input)
  | some b => (specParse toAscii (preprocess b)).bind fun bu => specParseBase toAscii bu (preprocess input)

end Url.Spec
