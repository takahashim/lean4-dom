import Trace

/-- 対応表を JSON で書き出す。`ruby spec-trace/check.rb` と `ruby spec-trace/drift.rb` が読む。 -/
def main : IO Unit :=
  IO.println (Trace.render Trace.Dom.entries Trace.Dom.exclusions)
