import Dom.Validity.Attributes
import Dom.Query.Lookup
import Dom.Attribute.Reflect

/-!
# null namespace の attribute だけを見るもの

DOM と HTML には、attribute を「namespace が null で、その local name を持つもの」として
読む箇所が多い。element の ID と classes（DOM §4.9）、`getElementsByName()`（HTML §3.1.5）、
selector の `[att]`（Selectors §6.4）、HTML の reflect がそうである。
これらは `setAttributeNS("urn:x", "id", …)` のような namespace 付きの attribute を見てはいけない。

逆に `getAttribute` / `setAttribute` / `removeAttribute` / `toggleAttribute` は
**qualified name** で引くので、prefix の無い namespace 付きの attribute も見る。
直感で「名前で引くものは namespace 付きを見ない」と決めると、ここを取り違える。

この module は前者を一つの性質として述べる。

* `NodeData.nullNsView` — node data から namespace 付きの attribute を落としたもの。
* `SameNullNsView t t'` — どの node も `nullNsView` を通して見れば同じ。
* 上の読み方は `SameNullNsView` で変わらない（`SameNullNsView.getElementById` ほか）。
* namespace が null でない `setAttributeNS` / `removeAttributeNS` は `SameNullNsView` を保つ
  （`setAttributeNS_sameNullNsView`、`removeAttributeNS_sameNullNsView`）。

二つを合わせると、**namespace 付きの attribute を足しても消しても、ID・classes・
`getElementsByName()` の答えは変わらない**。実装がこれを破るなら、attribute を
local name か qualified name で引いている。差分テストでは
`test/decoy_compare.rb` がこの性質を model の外の API にまで広げて検査する。

## preorder は木の形だけで決まる

list を返す method は `preorder` を通る。`preorder` の fuel は store の entry 数なので、
attribute だけを差し替えた木でも fuel が同じとは限らない。そこで先に
「well-formed な木では fuel が entry 数以上なら `preorderFuel` は変わらない」を示し
（`preorderFuel_eq_preorder`）、`preorder` が parent と children だけで決まることを導く
（`preorder_of_attributesOnly`）。
-/

namespace Dom

/-! ## preorder の fuel -/

section Fuel

private theorem flatMap_sublist {α β : Type _} {A B : α → List β} :
    ∀ {l : List α}, (∀ x ∈ l, (A x).Sublist (B x)) → (l.flatMap A).Sublist (l.flatMap B)
  | [], _ => by simp
  | x :: rest, h => by
    simp only [List.flatMap_cons]
    exact (h x (List.mem_cons_self ..)).append
      (flatMap_sublist fun y hy => h y (List.mem_cons_of_mem _ hy))

private theorem flatMap_congr_mem {α β : Type _} {A B : α → List β} :
    ∀ {l : List α}, (∀ x ∈ l, A x = B x) → l.flatMap A = l.flatMap B
  | [], _ => rfl
  | x :: rest, h => by
    simp only [List.flatMap_cons, h x (List.mem_cons_self ..),
      flatMap_congr_mem fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- 部分列が要素ごとに成り立ち、つないだ長さが等しいなら、要素ごとに等しい。 -/
private theorem flatMap_eq_of_sublist_of_length {α β : Type _} {A B : α → List β} :
    ∀ {l : List α}, (∀ x ∈ l, (A x).Sublist (B x)) →
      (l.flatMap A).length = (l.flatMap B).length → ∀ x ∈ l, A x = B x
  | [], _, _ => by simp
  | x :: rest, h, hl => by
    simp only [List.flatMap_cons, List.length_append] at hl
    have h1 := (h x (List.mem_cons_self ..)).length_le
    have h2 := (flatMap_sublist (l := rest) fun y hy => h y (List.mem_cons_of_mem _ hy)).length_le
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact (h y (List.mem_cons_self ..)).eq_of_length (by omega)
    · exact flatMap_eq_of_sublist_of_length (fun z hz => h z (List.mem_cons_of_mem _ hz))
        (by omega) y hy

/-- fuel を一つ増やすと、列は伸びるだけである。 -/
theorem preorderFuel_sublist_succ (t : Tree) :
    ∀ (f : Nat) (n : NodeId), (preorderFuel t f n).Sublist (preorderFuel t (f + 1) n) := by
  intro f
  induction f with
  | zero => intro n; simp
  | succ f ih =>
    intro n
    cases hn : t.get? n with
    | none => simp [preorderFuel_succ_neg hn]
    | some d =>
      rw [preorderFuel_succ_pos hn, preorderFuel_succ_pos hn]
      exact (flatMap_sublist fun c _ => ih c).cons_cons n

/-- 一度 fuel を増やしても変わらなかったなら、次に増やしても変わらない。 -/
theorem preorderFuel_succ_stable (t : Tree) :
    ∀ (f : Nat) (n : NodeId), preorderFuel t f n = preorderFuel t (f + 1) n →
      preorderFuel t (f + 1) n = preorderFuel t (f + 1 + 1) n := by
  intro f
  induction f with
  | zero =>
    intro n h
    cases hn : t.get? n with
    | none => rw [preorderFuel_succ_neg hn, preorderFuel_succ_neg hn]
    | some d => rw [preorderFuel_succ_pos hn] at h; simp at h
  | succ f ih =>
    intro n h
    cases hn : t.get? n with
    | none => rw [preorderFuel_succ_neg hn, preorderFuel_succ_neg hn]
    | some d =>
      rw [preorderFuel_succ_pos hn, preorderFuel_succ_pos hn] at h
      rw [preorderFuel_succ_pos hn, preorderFuel_succ_pos hn]
      have hl := congrArg List.length (List.cons.inj h).2
      have heach := flatMap_eq_of_sublist_of_length
        (fun c _ => preorderFuel_sublist_succ t f c) hl
      congr 1
      exact flatMap_congr_mem fun c hc => ih c (heach c hc)

private theorem preorderFuel_step_of (t : Tree) {f₀ : Nat} {n : NodeId}
    (h : preorderFuel t f₀ n = preorderFuel t (f₀ + 1) n) :
    ∀ k, preorderFuel t (f₀ + k) n = preorderFuel t (f₀ + k + 1) n
  | 0 => h
  | k + 1 => preorderFuel_succ_stable t (f₀ + k) n (preorderFuel_step_of t h k)

private theorem preorderFuel_eq_of_fixed (t : Tree) {f₀ : Nat} {n : NodeId}
    (h : preorderFuel t f₀ n = preorderFuel t (f₀ + 1) n) :
    ∀ k, preorderFuel t (f₀ + k) n = preorderFuel t f₀ n
  | 0 => rfl
  | k + 1 => (preorderFuel_step_of t h k).symm.trans (preorderFuel_eq_of_fixed t h k)

private theorem preorderFuel_length_le_size {t : Tree} (hwf : WellFormed t) (f : Nat)
    (n : NodeId) : (preorderFuel t f n).length ≤ t.size := by
  have hsub : preorderFuel t f n ⊆ t.nodes.keys := by
    intro x hx
    obtain ⟨d, hd⟩ := exists_data_of_mem_preorderFuel f n x hx
    exact NodeStore.mem_keys_of_get?_eq_some hd
  have hle := Dom.ListUtil.length_le_of_nodup_subset (preorderFuel_nodup hwf f n) hsub
  rw [NodeStore.length_keys] at hle
  exact hle

/-- fuel が entry 数に届く前に、列は伸びなくなる。伸び続けると entry 数を超えるからである。 -/
theorem exists_preorderFuel_fixed {t : Tree} (hwf : WellFormed t) (n : NodeId) :
    ∃ f₀, f₀ ≤ t.size ∧ preorderFuel t f₀ n = preorderFuel t (f₀ + 1) n := by
  apply Classical.byContradiction
  intro hne
  have grow : ∀ f, f ≤ t.size + 1 → f ≤ (preorderFuel t f n).length := by
    intro f
    induction f with
    | zero => intro _; exact Nat.zero_le _
    | succ f ih =>
      intro hf
      have hsub := preorderFuel_sublist_succ t f n
      have hneq : preorderFuel t f n ≠ preorderFuel t (f + 1) n :=
        fun heq => hne ⟨f, by omega, heq⟩
      have hlt : (preorderFuel t f n).length < (preorderFuel t (f + 1) n).length := by
        rcases Nat.lt_or_ge (preorderFuel t f n).length (preorderFuel t (f + 1) n).length
          with h | h
        · exact h
        · exact absurd (hsub.eq_of_length (Nat.le_antisymm hsub.length_le h)) hneq
      have := ih (by omega)
      omega
  have h1 := grow (t.size + 1) (Nat.le_refl _)
  have h2 := preorderFuel_length_le_size hwf (t.size + 1) n
  omega

/-- **well-formed な木では、fuel が entry 数以上なら `preorderFuel` は `preorder` と同じ。** -/
theorem preorderFuel_eq_preorder {t : Tree} (hwf : WellFormed t) (n : NodeId) {f : Nat}
    (hf : t.size ≤ f) : preorderFuel t f n = preorder t n := by
  obtain ⟨f₀, hle, hfix⟩ := exists_preorderFuel_fixed hwf n
  have e1 := preorderFuel_eq_of_fixed t hfix (f - f₀)
  have e2 := preorderFuel_eq_of_fixed t hfix (t.size - f₀)
  rw [show f₀ + (f - f₀) = f by omega] at e1
  rw [show f₀ + (t.size - f₀) = t.size by omega] at e2
  unfold preorder
  rw [e1, e2]

/-- 木にあるかと children が同じなら、同じ fuel の `preorderFuel` は同じ。 -/
theorem preorderFuel_congr {t t' : Tree} (hc : ∀ m, t'.contains m = t.contains m)
    (hch : ∀ m, childrenOf t' m = childrenOf t m) :
    ∀ f n, preorderFuel t' f n = preorderFuel t f n
  | 0, _ => rfl
  | f + 1, n => by
    have ih : preorderFuel t' f = preorderFuel t f := funext (preorderFuel_congr hc hch f)
    simp only [preorderFuel, hc n, hch n, ih]

theorem AttributesOnly.contains {t t' : Tree} (h : AttributesOnly t t') (m : NodeId) :
    t'.contains m = t.contains m := by
  have hm := congrArg Option.isSome (h m)
  simp only [Option.isSome_map] at hm
  exact hm

/-- **attribute だけを変えた木の `preorder` は元と同じ。** -/
theorem preorder_of_attributesOnly {t t' : Tree} (h : AttributesOnly t t') (hwf : WellFormed t)
    (n : NodeId) : preorder t' n = preorder t n := by
  have hwf' := wellFormed_of_attributesOnly h hwf
  have hc := preorderFuel_congr (fun m => h.contains m) (fun m => h.childrenOf m)
  rw [← preorderFuel_eq_preorder hwf' n (Nat.le_max_left t'.size t.size),
    ← preorderFuel_eq_preorder hwf n (Nat.le_max_right t'.size t.size), hc]

theorem descendantElements_of_attributesOnly {t t' : Tree} (h : AttributesOnly t t')
    (hwf : WellFormed t) (n : NodeId) : descendantElements t' n = descendantElements t n := by
  unfold descendantElements isElementNode
  rw [preorder_of_attributesOnly h hwf]
  simp only [h.kindOf]

end Fuel

/-! ## null namespace の attribute だけを見た node data -/

/-- namespace 付きの attribute を落とした node data。 -/
def NodeData.nullNsView (d : NodeData) : NodeData :=
  { d with attributes := d.attributes.filter (·.namespace.isNone) }

/-- どの node も、namespace 付きの attribute を落とせば同じ。 -/
def SameNullNsView (t t' : Tree) : Prop :=
  ∀ m, (t'.get? m).map NodeData.nullNsView = (t.get? m).map NodeData.nullNsView

private theorem find?_filter_of_imp {α : Type _} (p q : α → Bool)
    (hq : ∀ a, q a = true → p a = true) :
    ∀ l : List α, (l.filter p).find? q = l.find? q
  | [] => rfl
  | a :: l => by
    have ih := find?_filter_of_imp p q hq l
    by_cases hqa : q a = true
    · simp [hq a hqa, hqa]
    · by_cases hpa : p a = true
      · simp [hpa, hqa, ih]
      · simp [hpa, hqa, ih]

/-- **`plainAttr` は namespace 付きの attribute を見ない。** -/
@[simp] theorem plainAttr_nullNsView (d : NodeData) (name : String) :
    plainAttr d.nullNsView name = plainAttr d name := by
  unfold plainAttr NodeData.nullNsView
  simp only
  rw [find?_filter_of_imp _ _ (fun a h => by simp at h; simp [h.2])]

/-- **"get an attribute value" を namespace null で呼んだものは、namespace 付きの attribute を見ない。** -/
@[simp] theorem getAttributeValue_nullNsView (d : NodeData) (ln : String) :
    getAttributeValue d.nullNsView none ln = getAttributeValue d none ln := by
  unfold getAttributeValue getAttributeByKey NodeData.nullNsView
  simp only
  rw [find?_filter_of_imp _ _ (fun a h => by
    simp only [normalizeNamespace, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1])]

namespace SameNullNsView

variable {t t' : Tree}

theorem refl (t : Tree) : SameNullNsView t t := fun _ => rfl

theorem trans {t'' : Tree} (h₁ : SameNullNsView t t') (h₂ : SameNullNsView t' t'') :
    SameNullNsView t t'' := fun m => (h₂ m).trans (h₁ m)

/-- `nullNsView` を通しても変わらない読み方は、`SameNullNsView` で変わらない。 -/
theorem get?_map {α : Type _} {F : NodeData → α} (hF : ∀ d, F d.nullNsView = F d)
    (h : SameNullNsView t t') (m : NodeId) : (t'.get? m).map F = (t.get? m).map F := by
  have := congrArg (Option.map F) (h m)
  simpa [Option.map_map, Function.comp_def, hF] using this

theorem attributesOnly (h : SameNullNsView t t') : AttributesOnly t t' := by
  intro m
  exact h.get?_map (F := fun d => { d with attributes := ([] : List Attr) })
    (fun d => by cases d; rfl) m

theorem elementIdOf (h : SameNullNsView t t') (e : NodeId) :
    Dom.elementIdOf t' e = Dom.elementIdOf t e := by
  have hm := h.get?_map (F := fun d => plainAttr d "id") (fun d => plainAttr_nullNsView d "id") e
  unfold Dom.elementIdOf
  cases h1 : t'.get? e <;> cases h2 : t.get? e <;>
    simp only [h1, h2, Option.map_some, Option.map_none, reduceCtorEq,
      Option.some.injEq] at hm ⊢
  rw [hm]

theorem elementClassesOf (h : SameNullNsView t t') (e : NodeId) :
    Dom.elementClassesOf t' e = Dom.elementClassesOf t e := by
  have hm := h.get?_map (F := fun d => plainAttr d "class")
    (fun d => plainAttr_nullNsView d "class") e
  unfold Dom.elementClassesOf
  cases h1 : t'.get? e <;> cases h2 : t.get? e <;>
    simp only [h1, h2, Option.map_some, Option.map_none, reduceCtorEq,
      Option.some.injEq] at hm ⊢
  rw [hm]

theorem receiverInQuirksMode (h : SameNullNsView t t') (n : NodeId) :
    Dom.receiverInQuirksMode t' n = Dom.receiverInQuirksMode t n := by
  have ho := h.get?_map (F := NodeData.ownerDocument) (fun _ => rfl) n
  unfold Dom.receiverInQuirksMode inQuirksModeOf
  cases h1 : t'.get? n <;> cases h2 : t.get? n <;>
    simp only [h1, h2, Option.map_some, Option.map_none, reduceCtorEq,
      Option.some.injEq] at ho ⊢
  rename_i d' d
  have hm := h.get?_map (F := NodeData.mode) (fun _ => rfl) d.ownerDocument
  rw [ho]
  cases h3 : t'.get? d.ownerDocument <;> cases h4 : t.get? d.ownerDocument <;>
    simp only [h3, h4, Option.map_some, Option.map_none, reduceCtorEq,
      Option.some.injEq] at hm ⊢
  rw [hm]

theorem kind (h : SameNullNsView t t') (m : NodeId) :
    (t'.get? m).map NodeData.kind = (t.get? m).map NodeData.kind :=
  h.get?_map (fun _ => rfl) m

private theorem requireNonElementParentNode_eq (h : SameNullNsView t t') (n : NodeId) :
    requireNonElementParentNode t' n = requireNonElementParentNode t n := by
  have hk := h.kind n
  unfold requireNonElementParentNode
  cases h1 : t'.get? n <;> cases h2 : t.get? n <;>
    simp only [h1, h2, Option.map_some, Option.map_none, reduceCtorEq,
      Option.some.injEq] at hk ⊢
  rw [hk]

private theorem requireDocumentOrElement_eq (h : SameNullNsView t t') (n : NodeId) :
    requireDocumentOrElement t' n = requireDocumentOrElement t n := by
  have hk := h.kind n
  unfold requireDocumentOrElement
  cases h1 : t'.get? n <;> cases h2 : t.get? n <;>
    simp only [h1, h2, Option.map_some, Option.map_none, reduceCtorEq,
      Option.some.injEq] at hk ⊢
  rw [hk]

/-- `requireDocument` は kind しか見ないが、返す node data には attribute が入っている。 -/
private theorem requireDocument_isOk (h : SameNullNsView t t') (n : NodeId) :
    (requireDocument t' n).toOption.isSome = (requireDocument t n).toOption.isSome ∧
      (∀ e, requireDocument t' n = .error e ↔ requireDocument t n = .error e) := by
  have hk := h.kind n
  unfold requireDocument
  cases h1 : t'.get? n <;> cases h2 : t.get? n <;>
    simp only [h1, h2, Option.map_some, Option.map_none, reduceCtorEq,
      Option.some.injEq] at hk ⊢
  · simp
  · rw [hk]
    split <;> simp [Except.toOption]

/-- **namespace 付きの attribute は `getElementById()` の答えを変えない。** -/
theorem getElementById (h : SameNullNsView t t') (hwf : WellFormed t) (n : NodeId) (i : String) :
    Dom.getElementById t' n i = Dom.getElementById t n i := by
  unfold Dom.getElementById
  rw [requireNonElementParentNode_eq h, descendantElements_of_attributesOnly h.attributesOnly hwf]
  simp only [h.elementIdOf]

/-- **namespace 付きの attribute は `getElementsByClassName()` の答えを変えない。** -/
theorem getElementsByClassName (h : SameNullNsView t t') (hwf : WellFormed t) (n : NodeId)
    (cs : String) :
    Dom.getElementsByClassName t' n cs = Dom.getElementsByClassName t n cs := by
  unfold Dom.getElementsByClassName
  rw [requireDocumentOrElement_eq h, descendantElements_of_attributesOnly h.attributesOnly hwf,
    h.receiverInQuirksMode]
  simp only [h.elementClassesOf]

/-- **namespace 付きの attribute は `getElementsByName()` の答えを変えない。** -/
theorem getElementsByName (h : SameNullNsView t t') (hwf : WellFormed t) (n : NodeId)
    (name : String) :
    Dom.getElementsByName t' n name = Dom.getElementsByName t n name := by
  have hpred : ∀ e, (match t'.get? e with
        | none => false
        | some d => d.namespace == some htmlNamespace && plainAttr d "name" == some name) =
      (match t.get? e with
        | none => false
        | some d => d.namespace == some htmlNamespace && plainAttr d "name" == some name) := by
    intro e
    have hm := h.get?_map
      (F := fun d => d.namespace == some htmlNamespace && plainAttr d "name" == some name)
      (fun d => by rw [plainAttr_nullNsView]; rfl) e
    cases h1 : t'.get? e <;> cases h2 : t.get? e <;>
      simp only [h1, h2, Option.map_some, Option.map_none, reduceCtorEq,
        Option.some.injEq] at hm ⊢
    exact hm
  obtain ⟨hok, herr⟩ := requireDocument_isOk h n
  unfold Dom.getElementsByName
  rw [descendantElements_of_attributesOnly h.attributesOnly hwf]
  cases h1 : requireDocument t' n <;> cases h2 : requireDocument t n <;>
    simp only [h1, h2, Except.toOption, Option.isSome_some, Option.isSome_none,
      Bool.false_eq_true, Bool.true_eq_false] at hok ⊢
  · rename_i e' e
    have := (herr e').mp h1
    rw [h2] at this
    rw [Except.error.inj this]
  · congr 1
    exact List.filter_congr fun e _ => hpred e

/-- **reflect の getter（`id` / `className` / `slot`）は namespace 付きの attribute を見ない。** -/
theorem getReflected (h : SameNullNsView t t') (e : NodeId) (ln : String) :
    Dom.getReflected t' e ln = Dom.getReflected t e ln := by
  have hm := h.get?_map (F := fun d => (d.kind, getAttributeValue d none ln))
    (fun d => by simp only [getAttributeValue_nullNsView]; rfl) e
  unfold Dom.getReflected requireElementData
  cases h1 : t'.get? e <;> cases h2 : t.get? e <;>
    simp only [h1, h2, Option.map_some, Option.map_none, reduceCtorEq,
      Option.some.injEq, Prod.mk.injEq] at hm ⊢
  rw [hm.1]
  split <;> simp [Except.map, hm.2]

/-- **`classList.contains` は namespace 付きの `class` を見ない。** -/
theorem classListContains (h : SameNullNsView t t') (e : NodeId) (tok : String) :
    Dom.classListContains t' e tok = Dom.classListContains t e tok := by
  have hm := h.get?_map (F := fun d => (d.kind, getAttributeValue d none "class"))
    (fun d => by simp only [getAttributeValue_nullNsView]; rfl) e
  unfold Dom.classListContains requireElementData classTokenSet
  cases h1 : t'.get? e <;> cases h2 : t.get? e <;>
    simp only [h1, h2, Option.map_some, Option.map_none, reduceCtorEq,
      Option.some.injEq, Prod.mk.injEq] at hm ⊢
  rw [hm.1]
  split <;> simp [Except.map, hm.2]

/-- **`children.namedItem` は namespace 付きの `id` / `name` を見ない。** -/
theorem childrenNamedItem (h : SameNullNsView t t') (n : NodeId) (key : String) :
    Dom.childrenNamedItem t' n key = Dom.childrenNamedItem t n key := by
  have hk := h.kind n
  have hreq : requireParentNode t' n = requireParentNode t n := by
    unfold requireParentNode
    cases h1 : t'.get? n <;> cases h2 : t.get? n <;>
      simp only [h1, h2, Option.map_some, Option.map_none, reduceCtorEq,
        Option.some.injEq] at hk ⊢
    rw [hk]
  have hch : elementChildrenOf t' n = elementChildrenOf t n := by
    unfold elementChildrenOf isElementNode
    rw [h.attributesOnly.childrenOf]
    simp only [h.attributesOnly.kindOf]
  have hname : ∀ e, (match t'.get? e with
        | none => false
        | some d => d.namespace == some htmlNamespace && plainAttr d "name" == some key) =
      (match t.get? e with
        | none => false
        | some d => d.namespace == some htmlNamespace && plainAttr d "name" == some key) := by
    intro e
    have hm := h.get?_map
      (F := fun d => d.namespace == some htmlNamespace && plainAttr d "name" == some key)
      (fun d => by rw [plainAttr_nullNsView]; rfl) e
    cases h1 : t'.get? e <;> cases h2 : t.get? e <;>
      simp only [h1, h2, Option.map_some, Option.map_none, reduceCtorEq,
        Option.some.injEq] at hm ⊢
    exact hm
  unfold Dom.childrenNamedItem
  rw [hreq, hch]
  simp only [h.elementIdOf]
  congr 1
  funext _
  split
  · rfl
  · congr 1
    funext e
    exact congrArg (Dom.elementIdOf t e == some key || ·) (hname e)

end SameNullNsView

/-! ## namespace 付きの attribute を書く操作 -/

section Ops

private theorem filter_updateFirst {p : Attr → Bool} {f : Attr → Attr}
    (hp : ∀ b, p b = true → b.namespace.isSome = true)
    (hf : ∀ b, (f b).namespace = b.namespace) :
    ∀ l : List Attr, (Dom.ListUtil.updateFirst p f l).filter (·.namespace.isNone) =
      l.filter (·.namespace.isNone)
  | [] => rfl
  | a :: l => by
    by_cases hpa : p a = true
    · have hs := hp a hpa
      have hs' : (f a).namespace.isSome = true := by rw [hf]; exact hs
      simp [Dom.ListUtil.updateFirst, hpa, Option.isNone_iff_eq_none,
        Option.isSome_iff_ne_none.mp hs, Option.isSome_iff_ne_none.mp hs']
    · simp [Dom.ListUtil.updateFirst, hpa, List.filter_cons, filter_updateFirst hp hf l]

private theorem filter_eraseFirst {p : Attr → Bool}
    (hp : ∀ b, p b = true → b.namespace.isSome = true) :
    ∀ l : List Attr, (Dom.ListUtil.eraseFirst p l).filter (·.namespace.isNone) =
      l.filter (·.namespace.isNone)
  | [] => rfl
  | a :: l => by
    by_cases hpa : p a = true
    · have hs := hp a hpa
      simp [Dom.ListUtil.eraseFirst, hpa, Option.isNone_iff_eq_none,
        Option.isSome_iff_ne_none.mp hs]
    · simp [Dom.ListUtil.eraseFirst, hpa, List.filter_cons, filter_eraseFirst hp l]

/-- attribute list の null namespace の部分を変えない差し替えは、`SameNullNsView` を保つ。 -/
theorem sameNullNsView_setAttributes {t : Tree} {n : NodeId} {d : NodeData} {as : List Attr}
    (hd : t.get? n = some d)
    (hview : as.filter (·.namespace.isNone) = d.attributes.filter (·.namespace.isNone)) :
    SameNullNsView t (setAttributes t n d as) := by
  intro m
  rw [get?_setAttributes hd]
  by_cases hm : m = n
  · subst hm
    simp [hd, NodeData.nullNsView, hview]
  · rw [if_neg hm]

/-- 見つけた attribute の namespace は、探した namespace（正規化済み）である。 -/
private theorem getAttributeByKey_namespace {d : NodeData} {ns : Option String} {ln : String}
    {a : Attr} (h : getAttributeByKey d ns ln = some a) :
    a.namespace = normalizeNamespace ns := by
  unfold getAttributeByKey at h
  have := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact this.1

private theorem key_namespace {a b : Attr} (h : (b.key == a.key) = true) :
    b.namespace = a.namespace := by
  simp only [beq_iff_eq, Attr.key, Prod.mk.injEq] at h
  exact h.1

/--
**namespace が null でない `setAttributeNS` は、null namespace の attribute を変えない。**

append の枝では足す attribute が、change の枝では書き換える attribute が、
どちらも namespace を持つからである。
-/
theorem setAttributeNS_sameNullNsView {s s' : DOMState} {e : NodeId} {ns : Option String}
    {qn v : String} (hns : normalizeNamespace ns ≠ none)
    (h : setAttributeNS s e ns qn v = .ok s') : SameNullNsView s.tree s'.tree := by
  unfold setAttributeNS at h
  split at h
  · simp at h
  · rename_i ns' pfx ln hv
    obtain ⟨hns', _⟩ := validateAndExtractAttribute_ok hv
    subst hns'
    unfold setAttributeValue at h
    split at h
    · simp at h
    · rename_i d hd
      split at h
      · simp at h
      · split at h
        · rename_i hnone
          have hs := (Except.ok.inj h).symm
          subst hs
          rw [appendAttribute_tree]
          refine sameNullNsView_setAttributes hd ?_
          simp [normalizeNamespace_idem, Option.isNone_iff_eq_none, hns]
        · rename_i a ha
          have hs := (Except.ok.inj h).symm
          subst hs
          rw [changeAttribute_tree]
          refine sameNullNsView_setAttributes hd (filter_updateFirst (f := fun b => { b with value := v }) ?_ (fun _ => rfl) _)
          intro b hb
          rw [key_namespace hb, getAttributeByKey_namespace ha, normalizeNamespace_idem]
          exact Option.isSome_iff_ne_none.mpr hns

/-- **namespace が null でない `removeAttributeNS` は、null namespace の attribute を変えない。** -/
theorem removeAttributeNS_sameNullNsView {s s' : DOMState} {e : NodeId} {ns : Option String}
    {ln : String} (hns : normalizeNamespace ns ≠ none)
    (h : removeAttributeNS s e ns ln = .ok s') : SameNullNsView s.tree s'.tree := by
  unfold removeAttributeNS at h
  split at h
  · simp at h
  · rename_i d hd
    split at h
    · simp at h
    · split at h
      · have hs := (Except.ok.inj h).symm
        subst hs
        exact SameNullNsView.refl _
      · rename_i a ha
        have hs := (Except.ok.inj h).symm
        subst hs
        rw [removeAttributeFrom_tree]
        refine sameNullNsView_setAttributes hd (filter_eraseFirst ?_ _)
        intro b hb
        rw [key_namespace hb, getAttributeByKey_namespace ha]
        exact Option.isSome_iff_ne_none.mpr hns

end Ops

/-! ## 合わせたもの -/

/--
**namespace 付きの attribute を足しても、`getElementById()` の答えは変わらない。**

`getElementsByClassName()` と `getElementsByName()` も同じ形で出る
（`SameNullNsView.getElementsByClassName`、`SameNullNsView.getElementsByName`）。
-/
theorem setAttributeNS_getElementById {s s' : DOMState} {e : NodeId} {ns : Option String}
    {qn v : String} (hwf : WellFormed s.tree) (hns : normalizeNamespace ns ≠ none)
    (h : setAttributeNS s e ns qn v = .ok s') (n : NodeId) (i : String) :
    getElementById s'.tree n i = getElementById s.tree n i :=
  (setAttributeNS_sameNullNsView hns h).getElementById hwf n i

end Dom
