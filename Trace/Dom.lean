import Trace.Dom.Infra
import Trace.Dom.Event
import Trace.Dom.Mutation
import Trace.Dom.ParentNode
import Trace.Dom.Observer
import Trace.Dom.Node
import Trace.Dom.Document
import Trace.Dom.Element
import Trace.Dom.CharacterData
import Trace.Dom.Range
import Trace.Dom.Traversal
import Trace.Dom.Sets

/-!
# DOM Standard の対応表の全体

節ごとの表を一つにまとめる。`lake exe spec-trace` がこれを JSON で書き出し、
`ruby spec-trace/check.rb` が `spec-trace/dom.json`（固定 commit の `dom.bs` から抜き出した algorithm）と突き合わせる。
-/

namespace Trace.Dom

def entries : List Entry :=
  Infra.entries ++ Event.entries ++ Mutation.entries ++ ParentNode.entries ++ Observer.entries ++
  Node.entries ++ Document.entries ++ Element.entries ++ CharacterData.entries ++
  Range.entries ++ Traversal.entries ++ Sets.entries

def exclusions : List Exclusion :=
  Infra.exclusions ++ Event.exclusions ++ Mutation.exclusions ++ ParentNode.exclusions ++
  Observer.exclusions ++ Node.exclusions ++ Document.exclusions ++ Element.exclusions ++
  CharacterData.exclusions ++ Range.exclusions ++ Traversal.exclusions ++ Sets.exclusions

end Trace.Dom
