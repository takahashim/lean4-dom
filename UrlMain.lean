import Url
import Lean.Data.Json

/-!
# `url-model`

URL Standard の oracle。

`url-model --wpt FILE` は WPT の `urltestdata.json` から作った表
（`test/url/wpt-ascii.json`）を読み、各 case を model で parse して
期待される `href`（または failure）と突き合わせる。
-/

open Lean (Json)
open Url
open Infra

structure Case where
  input : String
  base : Option String
  failure : Bool
  href : Option String
  origin : Option String

def caseOfJson (j : Json) : Except String Case := do
  let input ← (← j.getObjVal? "input").getStr?
  let base ← match j.getObjVal? "base" with
    | .ok v => if v.isNull then pure none else (v.getStr?).map some
    | .error _ => pure none
  let failure ← match j.getObjVal? "failure" with
    | .ok v => v.getBool?
    | .error _ => pure false
  let href ← match j.getObjVal? "href" with
    | .ok v => if v.isNull then pure none else (v.getStr?).map some
    | .error _ => pure none
  let origin ← match j.getObjVal? "origin" with
    | .ok v => if v.isNull then pure none else (v.getStr?).map some
    | .error _ => pure none
  return { input, base, failure, href, origin }

def runWpt (path : String) : IO UInt32 := do
  let text ← IO.FS.readFile path
  let .ok json := Json.parse text | do IO.eprintln s!"{path}: JSON を読めない"; return 1
  let .ok casesJson := json.getObjVal? "cases"
    | do IO.eprintln s!"{path}: `cases` がない"; return 1
  let .ok arr := casesJson.getArr? | do IO.eprintln s!"{path}: `cases` が配列ではない"; return 1
  let mut ok := 0
  let mut bad := 0
  let mut skipped := 0
  let mut invalid := 0
  let mut originOk := 0
  let mut originBad := 0
  let mut shown := 0
  for j in arr do
    match caseOfJson j with
    | .error e => IO.eprintln s!"case を読めない: {e}"; bad := bad + 1
    | .ok c =>
      -- host が非 ASCII に decode される case は IDNA（UTS #46）が要る。
      -- `asciiDomainToASCII` は構造的にそれを断るので、model の対象外として数える。
      let needsIdna :=
        (percentDecodeToString c.input.toList).any (fun ch => !isAscii ch) ||
          ((c.base.getD "").toList.any (fun ch => !isAscii ch))
      let got := parseUrl c.input c.base
      let expected : Option String := if c.failure then none else c.href
      let actual : Option String := got.map (fun u => urlSerializer u)
      -- parse が成功したなら、結果の record は `ValidUrl` を満たすはずである
      -- （証明は未着手。`docs/url-status.md`）。DOM 側の `--check` と同じ役割。
      match got with
      | some u =>
        if !checkValidUrl u then
          invalid := invalid + 1
          IO.println s!"INVALID input={repr c.input} base={repr c.base} -> {urlSerializer u}"
      | none => pure ()
      -- §4.7 origin。WPT の表が期待値を持っている case だけ見る。
      match got, c.origin with
      | some u, some expectedOrigin =>
        if originSerializer (Url.origin u) == expectedOrigin then originOk := originOk + 1
        else
          originBad := originBad + 1
          if shown < 20 then
            shown := shown + 1
            IO.println s!"ORIGIN input={repr c.input} base={repr c.base}"
            IO.println s!"  expected={repr expectedOrigin}"
            IO.println s!"  actual  ={repr (originSerializer (Url.origin u))}"
      | _, _ => pure ()
      if actual == expected then ok := ok + 1
      else if needsIdna && actual == none then skipped := skipped + 1
      else
        bad := bad + 1
        if shown < 20 then
          shown := shown + 1
          IO.println s!"MISMATCH input={repr c.input} base={repr c.base}"
          IO.println s!"  expected={repr expected}"
          IO.println s!"  actual  ={repr actual}"
  IO.println s!"WPT: 一致 {ok} / 不一致 {bad} / IDNA が要る（model の対象外） {skipped}"
  IO.println s!"ValidUrl: 違反 {invalid}"
  IO.println s!"origin: 一致 {originOk} / 不一致 {originBad}"
  return if bad == 0 && invalid == 0 && originBad == 0 then 0 else 1

/--
`application/x-www-form-urlencoded` の固定 case。

WPT 側は JS のテストなので機械可読の表が無い。仕様 §5 の記述と
その例（`≡` → `%E2%89%A1`、`‽` → `%E2%80%BD`）から作った。
-/
def urlencodedCases : List (String × List (String × String)) :=
  [ ("a=b&c=d", [("a", "b"), ("c", "d")])
  , ("a=b&c=d&", [("a", "b"), ("c", "d")])
  , ("&&&a=b&&&&c=d&", [("a", "b"), ("c", "d")])
  , ("a", [("a", "")])
  , ("a=", [("a", "")])
  , ("=b", [("", "b")])
  , ("=", [("", "")])
  , ("a=b=c", [("a", "b=c")])
  , ("a+b=c+d", [("a b", "c d")])
  , ("a%20b=c%20d", [("a b", "c d")])
  , ("a=%2B", [("a", "+")])
  , ("%E2%89%A1=%E2%80%BD", [("≡", "‽")])
  , ("a=%zz", [("a", "%zz")])
  ]

def runUrlencoded : IO UInt32 := do
  let mut ok := 0
  let mut bad := 0
  for (input, expected) in urlencodedCases do
    let got := parseUrlencodedString input
    if got == expected then ok := ok + 1
    else
      bad := bad + 1
      IO.println s!"URLENCODED parse {repr input}"
      IO.println s!"  expected={repr expected}"
      IO.println s!"  actual  ={repr got}"
    -- serialize したものを読み直すと元に戻る（`urlencodedEncode_no_separator` が
    -- 区切りを作らないことを保証している）。
    let round := parseUrlencodedString (serializeUrlencoded expected)
    if round == expected then ok := ok + 1
    else
      bad := bad + 1
      IO.println s!"URLENCODED round-trip {repr expected}"
      IO.println s!"  serialized={repr (serializeUrlencoded expected)}"
      IO.println s!"  reparsed  ={repr round}"
  IO.println s!"urlencoded: 一致 {ok} / 不一致 {bad}"
  return if bad == 0 then 0 else 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--wpt", path] => do
    let a ← runWpt path
    let b ← runUrlencoded
    return if a == 0 && b == 0 then 0 else 1
  | ["--urlencoded"] => runUrlencoded
  | _ =>
    IO.println "usage: url-model --wpt FILE | url-model --urlencoded"
    return 1
