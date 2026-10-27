import Trace.Basic
import Dom

/-!
# §4.2.3 Mutation algorithms
-/

namespace Trace.Dom.Mutation

open Trace

def entries : List Entry := [
  { alg := "concept-node-ensure-pre-insertion-validity"
    impl := [``Dom.ensurePreInsertionValidity]
    spec := [``Dom.Spec.PreInsertValidity] },
  { alg := "concept-node-pre-insert"
    impl := [``Dom.preInsert, ``Dom.preInsertReferenceChild]
    spec := [``Dom.Spec.PreInsertResult] },
  { alg := "concept-node-insert"
    impl := [``Dom.insert, ``Dom.insertNodesAt, ``Dom.insertEachAt, ``Dom.insertEach,
             ``Dom.insertPrevSibling]
    spec := [``Dom.Spec.InsertSpec]
    omitted := [("7.4-7.6", .shadow), ("7.7.1", .hook), ("7.7.2-7.7.4", .customElements),
             ("9", .hook), ("10-12", .hook)] },
  { alg := "concept-node-append"
    impl := [``Dom.append]
    spec := [``Dom.Spec.append_result_sound] },
  { alg := "move"
    impl := [``Dom.move, ``Dom.moveValidity, ``Dom.detachWithLiveAdjust, ``Dom.addTransientObservers]
    spec := [``Dom.Spec.MoveSpec, ``Dom.Spec.MoveValidity]
    omitted := [("14-16", .shadow), ("22-24", .shadow), ("25.1-25.2", .hook),
             ("25.3", .customElements)]
    approx := [("1", "shadow-including root ではなく root で比べる（shadow tree が無いので同じ値）")] },
  { alg := "concept-node-replace"
    impl := [``Dom.replace]
    spec := [``Dom.Spec.ReplaceSpec, ``Dom.Spec.ReplaceResult] },
  { alg := "concept-node-replace-all"
    impl := [``Dom.replaceAll, ``Dom.replaceAllNodes]
    spec := [``Dom.Spec.ReplaceAllSpec] },
  { alg := "concept-node-pre-remove"
    impl := [``Dom.preRemove]
    spec := [``Dom.Spec.PreRemoveResult, ``Dom.Spec.preRemove_result_sound] },
  { alg := "concept-node-remove"
    impl := [``Dom.remove, ``Dom.detachWithLiveAdjust, ``Dom.addTransientObservers]
    spec := [``Dom.Spec.RemoveSpec, ``Dom.Spec.RemoveResult]
    omitted := [("8-10", .shadow), ("11", .hook), ("12-13", .customElements), ("14.1", .hook),
             ("14.2", .customElements), ("17", .hook)] }
]

def exclusions : List Exclusion := [
  { target := "concept-node-insert-ext", reason := .hook },
  { target := "concept-node-post-connection-ext", reason := .hook },
  { target := "concept-node-children-changed-ext", reason := .hook },
  { target := "concept-node-move-ext", reason := .hook },
  { target := "concept-node-remove-ext", reason := .hook }
]

end Trace.Dom.Mutation
