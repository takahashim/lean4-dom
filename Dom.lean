import Dom.Util.List
import Dom.Basic.NodeId
import Dom.Basic.Store
import Dom.Basic.Tree
import Dom.Basic.Order
import Dom.Basic.WellFormed
import Dom.Basic.Exception
import Dom.Basic.State
import Dom.Mutation.Detach
import Dom.Mutation.Insert
import Dom.Mutation.Adopt
import Dom.Range.BoundaryPoint
import Dom.Range.Adjust
import Dom.Traversal.NodeIterator
import Dom.Observer.Record
import Dom.CharacterData.ReplaceData
import Dom.Mutation.Algorithms
import Dom.Mutation.Api
import Dom.Properties.Tree
import Dom.Properties.Mutation
import Dom.Properties.Algorithms
import Dom.Properties.Path
import Dom.Properties.Range
import Dom.Properties.Iterator
import Dom.Properties.CharacterData

/-!
# Lean 4 による WHATWG DOM Standard の形式化

`PLAN.md` の Phase 1（node tree）、Phase 2（primitive mutation）、
Phase 3（WHATWG の mutation algorithm）、Phase 5（Range）、Phase 6（NodeIterator）、
Phase 7（CharacterData）、Phase 8（MutationObserver の record）に対応する module を re-export する。
-/
