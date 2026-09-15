import Dom.Util.List
import Dom.Basic.Utf16
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
import Dom.Range.Api
import Dom.Traversal.NodeIterator
import Dom.Traversal.TreeWalker
import Dom.Query.NodeQuery
import Dom.Observer.Record
import Dom.Observer.Deliver
import Dom.CharacterData.ReplaceData
import Dom.CharacterData.Normalize
import Dom.Attribute.Name
import Dom.Attribute.Algorithms
import Dom.Mutation.Algorithms
import Dom.Mutation.Api
import Dom.Validity.Structural
import Dom.Validity.NodeDocument
import Dom.Validity.DocumentTree
import Dom.Validity.AttributeList
import Dom.Validity.State
import Dom.Properties.Tree
import Dom.Properties.TreeOrder
import Dom.Properties.Mutation
import Dom.Properties.Algorithms
import Dom.Properties.Path
import Dom.Properties.Range
import Dom.Properties.Iterator
import Dom.Properties.Walker
import Dom.Properties.CharacterData
import Dom.Validity.Derived
import Dom.Validity.Preservation
import Dom.Validity.AlgorithmPreservation
import Dom.Validity.Iterators
import Dom.Validity.Observers
import Dom.Validity.Attributes
import Dom.Validity.Admissible
import Dom.Validity.Normalize
import Dom.Validity.RangeApi
import Dom.Validity.Walkers
import Dom.Properties.Record
import Dom.Properties.Contract
import Dom.Spec.Remove
import Dom.Spec.RemoveSound
import Dom.Spec.RemoveDeterministic
import Dom.Spec.Record
import Dom.Spec.RecordSound
import Dom.Spec.Adopt
import Dom.Spec.AdoptSound
import Dom.Spec.Insert
import Dom.Spec.InsertSound
import Dom.Spec.ReplaceData
import Dom.Spec.ReplaceDataSound
import Dom.Properties.Counterexample
import Dom.Observation

/-!
# Lean 4 による WHATWG DOM Standard の形式化

`PLAN.md` の Phase 1（node tree）、Phase 2（primitive mutation）、
Phase 3（WHATWG の mutation algorithm）、Phase 5（Range）、Phase 6（NodeIterator）、
Phase 7（CharacterData）、Phase 8（MutationObserver の record）に対応する module を re-export する。
-/
