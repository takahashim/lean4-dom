/-!
# 仕様の step と Lean の定義の対応表

`dom.bs` の algorithm ごとに、どの step を model のどの定義が実装しているか、
どの step を何の理由で外したかを、機械で検査できる形で持つ。

* algorithm は描画された仕様の anchor で指す（`https://dom.spec.whatwg.org/#<alg>`）。
  一つの anchor に getter と setter がある attribute は、setter のほうを `<anchor>/setter` と書く。
  鍵の一覧は `spec-trace/extract.rb` が固定 commit の `dom.bs` から作った `spec-trace/dom.json` にある。
* step は Bikeshed の描画と同じ番号で書く。`"5"` は step 5 とその下の step 全部、
  `"5.13-5.14"` は兄弟の範囲、`"*"` は algorithm 全体である。
* Lean の定義は `` ``Dom.remove `` の形で書く。名前が無ければこの module の elaboration が失敗する。

`spec-trace/check.rb` が `lake exe spec-trace` の出力と `spec-trace/dom.json` を突き合わせ、
次を検査する。

* 表に書いた algorithm と step が仕様にある。
* 表に載せた algorithm の step は、どれも「実装した」か「外した（理由付き）」のどちらかに入る。
* `dom.bs` の algorithm は、どれも表に載るか、理由付きで対象外とされる。
-/

namespace Trace

/-- step や algorithm を model に入れない理由。 -/
inductive Reason where
  /-- Shadow DOM（shadow root・slot・assigned slot・retarget）。 -/
  | shadow
  /-- custom element（reaction・registry・upgrade）。 -/
  | customElements
  /-- 他の仕様が中身を定める拡張点（insertion steps、removing steps ほか）。model は呼ぶ位置だけを保つ。 -/
  | hook
  /-- script の実行・event loop・global object が要るもの。 -/
  | host
  /-- 歴史的な理由で残っている API。 -/
  | legacy
  /-- 対象範囲に入りうるが、まだ model に入れていないもの。何が欠けているかを書く。 -/
  | todo (what : String)
  /-- そのほか。何を外したかを書く。 -/
  | other (why : String)
  deriving Repr, Inhabited

def Reason.label : Reason → String
  | .shadow => "shadow"
  | .customElements => "custom-elements"
  | .hook => "hook"
  | .host => "host"
  | .legacy => "legacy"
  | .todo _ => "todo"
  | .other _ => "other"

def Reason.detail : Reason → String
  | .todo what => what
  | .other why => why
  | _ => ""

/-- 一つの algorithm（の一部の step）を実装する定義。 -/
structure Entry where
  /-- 仕様の anchor。 -/
  alg : String
  /-- 実装している step。 -/
  steps : List String := ["*"]
  /-- 実行関数。 -/
  impl : List Lean.Name
  /-- 仕様本文から独立に書いた関係（`Dom/Spec/`）。 -/
  spec : List Lean.Name := []
  /-- `steps` のうち、model が外した step と理由。 -/
  omitted : List (String × Reason) := []
  /-- `steps` のうち、仕様と違う形で近似している step と、その違い。 -/
  approx : List (String × String) := []
  deriving Inhabited

/-- 表に載せない algorithm、または見出しの下の algorithm 全部。 -/
structure Exclusion where
  /-- algorithm の anchor か、見出しの id。 -/
  target : String
  reason : Reason
  deriving Inhabited

/-! ## JSON への書き出し（`spec-trace/check.rb` が読む） -/

private def jsonStr (s : String) : String :=
  let body := s.foldl (fun acc c =>
    match c with
    | '"' => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\t' => acc ++ "\\t"
    | c => acc.push c) ""
  "\"" ++ body ++ "\""

private def jsonArr (xs : List String) : String :=
  "[" ++ ", ".intercalate xs ++ "]"

private def jsonReason (r : Reason) : String :=
  "{\"reason\": " ++ jsonStr r.label ++ ", \"detail\": " ++ jsonStr r.detail ++ "}"

def Entry.toJson (e : Entry) : String :=
  "{\"alg\": " ++ jsonStr e.alg ++
  ", \"steps\": " ++ jsonArr (e.steps.map jsonStr) ++
  ", \"impl\": " ++ jsonArr (e.impl.map (jsonStr ∘ toString)) ++
  ", \"spec\": " ++ jsonArr (e.spec.map (jsonStr ∘ toString)) ++
  ", \"omit\": " ++ jsonArr (e.omitted.map fun (st, r) =>
      "{\"steps\": " ++ jsonStr st ++ ", \"why\": " ++ jsonReason r ++ "}") ++
  ", \"approx\": " ++ jsonArr (e.approx.map fun (st, w) =>
      "{\"steps\": " ++ jsonStr st ++ ", \"what\": " ++ jsonStr w ++ "}") ++ "}"

def Exclusion.toJson (x : Exclusion) : String :=
  "{\"target\": " ++ jsonStr x.target ++ ", \"why\": " ++ jsonReason x.reason ++ "}"

def render (es : List Entry) (xs : List Exclusion) : String :=
  "{\"entries\": " ++ jsonArr (es.map Entry.toJson) ++
  ",\n \"exclusions\": " ++ jsonArr (xs.map Exclusion.toJson) ++ "}"

end Trace
