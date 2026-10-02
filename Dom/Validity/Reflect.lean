import Dom.Validity.Admissible
import Dom.Attribute.Reflect

/-!
# reflect と `DOMTokenList` の admissibility

どれも "set an attribute value"（namespace も prefix も null）に落ちるので、
`attrOpResult_setAttributeValue` から従う。
-/

namespace Dom

theorem attrOpResult_tokenListUpdate {s s' : DOMState} {element : NodeId} {d : NodeData}
    {set : List String} (hr : tokenListUpdate s element d set = .ok s') : AttrOpResult s s' := by
  unfold tokenListUpdate at hr
  split at hr
  · rw [← Except.ok.inj hr]; exact AttrOpResult.refl s
  · exact attrOpResult_setAttributeValue (by simp) hr

theorem attrOpResult_classListAdd {s s' : DOMState} {element : NodeId} {tokens : List String}
    (hr : classListAdd s element tokens = .ok s') : AttrOpResult s s' := by
  unfold classListAdd at hr
  simp only [bind, Except.bind] at hr
  split at hr
  · simp at hr
  · split at hr
    · simp [throw, throwThe, MonadExceptOf.throw] at hr
    · exact attrOpResult_tokenListUpdate hr

theorem attrOpResult_classListRemove {s s' : DOMState} {element : NodeId}
    {tokens : List String} (hr : classListRemove s element tokens = .ok s') :
    AttrOpResult s s' := by
  unfold classListRemove at hr
  simp only [bind, Except.bind] at hr
  split at hr
  · simp at hr
  · split at hr
    · simp [throw, throwThe, MonadExceptOf.throw] at hr
    · exact attrOpResult_tokenListUpdate hr

/-- `Except` の `do` で、`tokenListUpdate` の結果に値を添えて返したものを剥がす。 -/
private theorem attrOpResult_of_update_pair {s s' : DOMState} {element : NodeId}
    {d : NodeData} {set : List String} {b b' : Bool}
    (hr : (do let s₁ ← tokenListUpdate s element d set; pure (s₁, b) :
      Except DOMException (DOMState × Bool)) = .ok (s', b')) : AttrOpResult s s' := by
  simp only [bind, Except.bind, pure, Except.pure] at hr
  split at hr
  · simp at hr
  · rename_i s₁ hu
    have : s₁ = s' := (Prod.mk.inj (Except.ok.inj hr)).1
    subst this
    exact attrOpResult_tokenListUpdate hu

theorem attrOpResult_classListToggle {s s' : DOMState} {element : NodeId} {token : String}
    {force : Option Bool} {b : Bool} (hr : classListToggle s element token force = .ok (s', b)) :
    AttrOpResult s s' := by
  unfold classListToggle at hr
  simp only [bind, Except.bind] at hr
  split at hr
  · simp at hr
  · split at hr
    · simp [throw, throwThe, MonadExceptOf.throw] at hr
    · split at hr
      · split at hr
        · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
          rw [← hr.1]; exact AttrOpResult.refl s
        · exact attrOpResult_of_update_pair hr
      · split at hr
        · exact attrOpResult_of_update_pair hr
        · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
          rw [← hr.1]; exact AttrOpResult.refl s

theorem attrOpResult_classListReplace {s s' : DOMState} {element : NodeId}
    {token newToken : String} {b : Bool}
    (hr : classListReplace s element token newToken = .ok (s', b)) : AttrOpResult s s' := by
  unfold classListReplace at hr
  simp only [bind, Except.bind] at hr
  split at hr
  · simp at hr
  · split at hr
    · simp [throw, throwThe, MonadExceptOf.throw] at hr
    · split at hr
      · simp [throw, throwThe, MonadExceptOf.throw] at hr
      · split at hr
        · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
          rw [← hr.1]; exact AttrOpResult.refl s
        · exact attrOpResult_of_update_pair hr

theorem attrOpResult_setReflectedProp {s s' : DOMState} {element : NodeId} {r : ReflectSpec}
    {v : String} (hr : setReflectedProp s element r v = .ok s') : AttrOpResult s s' := by
  unfold setReflectedProp at hr
  simp only [bind, Except.bind] at hr
  split at hr
  · simp at hr
  · exact attrOpResult_setAttributeValue (by simp) hr

theorem attrOpResult_setReflectedBool {s s' : DOMState} {element : NodeId} {r : ReflectSpec}
    {b : Bool} (hr : setReflectedBool s element r b = .ok s') : AttrOpResult s s' := by
  unfold setReflectedBool at hr
  simp only [bind, Except.bind] at hr
  split at hr
  · simp at hr
  · split at hr
    · exact attrOpResult_setAttributeValue (by simp) hr
    · exact attrOpResult_removeAttributeNS hr

theorem attrOpResult_datasetSet {s s' : DOMState} {element : NodeId} {name v : String}
    (hr : datasetSet s element name v = .ok s') : AttrOpResult s s' := by
  unfold datasetSet at hr
  simp only [bind, Except.bind] at hr
  split at hr
  · simp at hr
  · split at hr
    · simp [throw, throwThe, MonadExceptOf.throw] at hr
    · split at hr
      · simp [throw, throwThe, MonadExceptOf.throw] at hr
      · exact attrOpResult_setAttributeValue (by simp) hr

theorem attrOpResult_datasetDelete {s s' : DOMState} {element : NodeId} {name : String}
    (hr : datasetDelete s element name = .ok s') : AttrOpResult s s' := by
  unfold datasetDelete at hr
  simp only [bind, Except.bind] at hr
  split at hr
  · simp at hr
  · split at hr
    · simp only [pure, Except.pure, Except.ok.injEq] at hr
      rw [← hr]; exact AttrOpResult.refl s
    · exact attrOpResult_removeAttribute hr

theorem admissible_setReflectedProp {s s' : DOMState} {element : NodeId} {r : ReflectSpec}
    {v : String} (h : AdmissibleDOMState s) (hr : setReflectedProp s element r v = .ok s') :
    AdmissibleDOMState s' :=
  admissible_of_attrOp h (attrOpResult_setReflectedProp hr)

theorem admissible_setReflectedBool {s s' : DOMState} {element : NodeId} {r : ReflectSpec}
    {b : Bool} (h : AdmissibleDOMState s) (hr : setReflectedBool s element r b = .ok s') :
    AdmissibleDOMState s' :=
  admissible_of_attrOp h (attrOpResult_setReflectedBool hr)

theorem admissible_datasetSet {s s' : DOMState} {element : NodeId} {name v : String}
    (h : AdmissibleDOMState s) (hr : datasetSet s element name v = .ok s') :
    AdmissibleDOMState s' :=
  admissible_of_attrOp h (attrOpResult_datasetSet hr)

theorem admissible_datasetDelete {s s' : DOMState} {element : NodeId} {name : String}
    (h : AdmissibleDOMState s) (hr : datasetDelete s element name = .ok s') :
    AdmissibleDOMState s' :=
  admissible_of_attrOp h (attrOpResult_datasetDelete hr)

theorem admissible_classListAdd {s s' : DOMState} {element : NodeId} {tokens : List String}
    (h : AdmissibleDOMState s) (hr : classListAdd s element tokens = .ok s') :
    AdmissibleDOMState s' :=
  admissible_of_attrOp h (attrOpResult_classListAdd hr)

theorem admissible_classListRemove {s s' : DOMState} {element : NodeId} {tokens : List String}
    (h : AdmissibleDOMState s) (hr : classListRemove s element tokens = .ok s') :
    AdmissibleDOMState s' :=
  admissible_of_attrOp h (attrOpResult_classListRemove hr)

theorem admissible_classListToggle {s s' : DOMState} {element : NodeId} {token : String}
    {force : Option Bool} {b : Bool} (h : AdmissibleDOMState s)
    (hr : classListToggle s element token force = .ok (s', b)) : AdmissibleDOMState s' :=
  admissible_of_attrOp h (attrOpResult_classListToggle hr)

theorem admissible_classListReplace {s s' : DOMState} {element : NodeId}
    {token newToken : String} {b : Bool} (h : AdmissibleDOMState s)
    (hr : classListReplace s element token newToken = .ok (s', b)) : AdmissibleDOMState s' :=
  admissible_of_attrOp h (attrOpResult_classListReplace hr)

end Dom
