import Dom.Spec.ObserverCongr
import Dom.Spec.Complete
import Dom.Spec.CharacterDataResult
import Dom.Spec.AttributeCongr

/-!
# completeness から配送結果の一致を導く

`ObsEq` は pending mutation observers の列と node ごとの registered observer list の順まで含む。
そのため、関係を満たす状態と実行関数の結果が `ObsEq` で一致すれば、続けて notify したときに
observer へ配送される record の列（observer の順と各 observer の records の順）も一致する
（`notifyMutationObservers_delivered_congr`）。

ここでは、その合成を結果の形（`ResultObsEq`）と主要な mutation の completeness について書く。
-/

namespace Dom.Spec

open Dom

/-- 結果が `ResultObsEq` で一致すれば、成功した側を notify したときの配送も一致する。 -/
theorem ResultObsEq.delivered {r r' : Except DOMException DOMState} (h : ResultObsEq r r') :
    r'.map (fun s => (notifyMutationObservers s).2) = r.map (fun s => (notifyMutationObservers s).2) := by
  cases r <;> cases r'
  · rw [ResultObsEq.of_error h]
  · exact h.elim
  · exact h.elim
  · exact congrArg Except.ok (notifyMutationObservers_delivered_congr (ResultObsEq.of_ok h))

/-- **`remove` の関係を満たす状態は、実行関数の結果と同じ record の列を配送する。** -/
theorem remove_complete_delivered {s s' : DOMState} {n : NodeId} {b : Bool} (hwf : WellFormed s.tree)
    (h : RemoveSpec s n b s') :
    ∃ out, remove s n b = .ok out ∧
      (notifyMutationObservers out).2 = (notifyMutationObservers s').2 := by
  obtain ⟨out, hout, hobs⟩ := remove_complete hwf h
  exact ⟨out, hout, notifyMutationObservers_delivered_congr hobs⟩

/-- **`insert` の関係を満たす状態は、実行関数の結果と同じ record の列を配送する。** -/
theorem insert_complete_delivered {s s' : DOMState} {node parent : NodeId}
    {child : Option NodeId} {b : Bool} (hwf : WellFormed s.tree)
    (hacyc : ∀ ns : List NodeId, NodesToInsert s.tree node ns →
      ∀ m ∈ ns, ¬ InclusiveAncestor s.tree m parent)
    (h : InsertSpec s node parent child b s') :
    ∃ out, insert s node parent child b = .ok out ∧
      (notifyMutationObservers out).2 = (notifyMutationObservers s').2 := by
  obtain ⟨out, hout, hobs⟩ := insert_complete hwf hacyc h
  exact ⟨out, hout, notifyMutationObservers_delivered_congr hobs⟩

/-- **`replaceData` の結果の関係を満たす結果は、実行関数の結果と同じ record の列を配送する。** -/
theorem replaceData_result_complete_delivered {s : DOMState} (hwf : WellFormed s.tree) {node : NodeId}
    {offset count : Nat} {data : String} {r : Except DOMException DOMState}
    (h : ReplaceDataResult s node offset count data r) :
    (replaceData s node offset count data).map (fun s => (notifyMutationObservers s).2) =
      r.map (fun s => (notifyMutationObservers s).2) :=
  (replaceData_result_complete hwf h).delivered

/-- **`setAttribute` の結果の関係を満たす結果は、実行関数の結果と同じ record の列を配送する。** -/
theorem setAttribute_result_complete_delivered {s : DOMState} (hwf : WellFormed s.tree)
    (hav : AttributesValid s.tree) {element : NodeId} {qn value : String}
    {r : Except DOMException DOMState} (h : SetAttributeResult s element qn value r) :
    (setAttribute s element qn value).map (fun s => (notifyMutationObservers s).2) =
      r.map (fun s => (notifyMutationObservers s).2) :=
  (setAttribute_result_complete hwf hav h).delivered

end Dom.Spec
