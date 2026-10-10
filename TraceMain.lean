import Trace

/--
対応表を JSON で書き出す。`ruby spec-trace/check.rb` と `ruby spec-trace/drift.rb` が読む。

引数は仕様の名前（`dom`・`webidl`・`ecma262`）で、省略すると `dom` である。
-/
def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["dom"] => IO.println (Trace.render Trace.Dom.entries Trace.Dom.exclusions); pure 0
  | ["webidl"] => IO.println (Trace.render Trace.Webidl.entries Trace.Webidl.exclusions); pure 0
  | ["ecma262"] => IO.println (Trace.render Trace.Ecma.entries Trace.Ecma.exclusions); pure 0
  | _ => IO.eprintln "usage: spec-trace [dom|webidl|ecma262]"; pure 1
