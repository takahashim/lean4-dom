import Dom.Properties.NodeQuery
import Dom.Properties.Clone

/-!
# `equals` の関係仕様（§4.4）

本文の "A node A equals a node B if all of the following conditions are true" を、条件の並びのまま
帰納的な関係 `NodeEquals` に書く。children の条件（同じ数で、同じ index の子どうしが equals）が
再帰になるので、`inductive` の構成子の前提に置く。

* `nodeEquals_iff`：実行関数 `nodeEquals`（fuel 付きの再帰）は、木の上でちょうどこの関係である。
* `cloneOf_nodeEquals`：clone の関係 `CloneOf`（`Dom/Properties/Clone.lean`）で結ばれた node は equals である。
  したがって deep clone は原本と equals である（`cloneNode_nodeEquals`）。
-/

namespace Dom.Spec

open Dom

/-- §4.4 equals の attribute の条件：namespace・local name・value が同じ。 -/
def AttrEquals (x y : Attr) : Prop :=
  x.namespace = y.namespace ∧ x.localName = y.localName ∧ x.value = y.value

/-- §4.4 equals の、node の種類ごとの条件。 -/
def OwnPropertiesEqual (a b : NodeData) : Prop :=
  match a.kind with
  | .documentType =>
    a.doctypeName = b.doctypeName ∧ a.publicId = b.publicId ∧ a.systemId = b.systemId
  | .element =>
    a.namespace = b.namespace ∧ a.prefix = b.prefix ∧ a.localName = b.localName ∧
      a.attributes.length = b.attributes.length ∧
      ∀ x ∈ a.attributes, ∃ y ∈ b.attributes, AttrEquals x y
  | .processingInstruction => a.piTarget = b.piTarget ∧ a.data = b.data
  | .text | .cdataSection | .comment => a.data = b.data
  | .document | .documentFragment => True

/-- §4.4 "A equals B"。 -/
inductive NodeEquals (t : Tree) : NodeId → NodeId → Prop where
  | intro {a b : NodeId} {da db : NodeData} :
      t.get? a = some da → t.get? b = some db →
      da.kind = db.kind → OwnPropertiesEqual da db →
      da.children.length = db.children.length →
      (∀ (i : Nat) (x y : NodeId), da.children[i]? = some x → db.children[i]? = some y →
        NodeEquals t x y) →
      NodeEquals t a b

/-! ## 実行関数との一致 -/

theorem nodeOwnPropertiesEqual_iff (a b : NodeData) :
    nodeOwnPropertiesEqual a b = true ↔ OwnPropertiesEqual a b := by
  unfold nodeOwnPropertiesEqual OwnPropertiesEqual
  cases a.kind <;>
    simp [List.all_eq_true, List.any_eq_true, attrEquals, AttrEquals, and_assoc]

theorem all_zip_iff {f : NodeId → NodeId → Bool} :
    ∀ (l₁ l₂ : List NodeId), (l₁.zip l₂).all (fun p => f p.1 p.2) = true ↔
      ∀ (i : Nat) (x y : NodeId), l₁[i]? = some x → l₂[i]? = some y → f x y = true
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: l₁, b :: l₂ => by
    rw [List.zip_cons_cons, List.all_cons, Bool.and_eq_true, all_zip_iff l₁ l₂]
    constructor
    · rintro ⟨h0, hrest⟩ i x y hx hy
      cases i with
      | zero => simp at hx hy; subst hx; subst hy; exact h0
      | succ i => exact hrest i x y (by simpa using hx) (by simpa using hy)
    · intro h
      exact ⟨h 0 a b rfl rfl, fun i x y hx hy => h (i + 1) x y (by simpa using hx) (by simpa using hy)⟩

/-- fuel 付きの比較が真なら、関係が成り立つ。 -/
theorem nodeEquals_of_fuel {t : Tree} :
    ∀ (f : Nat) (a b : NodeId), nodeEqualsFuel t f a b = true → NodeEquals t a b
  | 0, _, _, h => by simp [nodeEqualsFuel] at h
  | f + 1, a, b, h => by
    cases ha : t.get? a with
    | none => rw [nodeEqualsFuel_succ_none_left f ha] at h; cases h
    | some da =>
      cases hb : t.get? b with
      | none => rw [nodeEqualsFuel_succ_none_right f ha hb] at h; cases h
      | some db =>
        rw [nodeEqualsFuel_succ_pos f ha hb] at h
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨⟨hk, hown⟩, hlen⟩, hall⟩ := h
        refine NodeEquals.intro ha hb hk ((nodeOwnPropertiesEqual_iff da db).mp hown) hlen ?_
        intro i x y hx hy
        exact nodeEquals_of_fuel f x y ((all_zip_iff da.children db.children).mp hall i x y hx hy)

/-- 関係が成り立てば、深さに見合う fuel で比較は真になる。 -/
theorem fuel_of_nodeEquals {t : Tree} (hwf : WellFormed t) :
    ∀ (k : Nat) (a b : NodeId) (d : NodeData), t.get? a = some d → t.size - depth t a ≤ k →
      NodeEquals t a b → nodeEqualsFuel t k a b = true := by
  intro k
  induction k with
  | zero =>
    intro a b d ha hk _
    exfalso
    have := depth_lt_size hwf ha
    omega
  | succ k ih =>
    intro a b d ha hk h
    cases h with
    | @intro _ _ da db ha' hb hkind hown hlen hch =>
      rw [ha] at ha'
      cases ha'
      rw [nodeEqualsFuel_succ_pos k ha hb]
      simp only [Bool.and_eq_true, beq_iff_eq]
      refine ⟨⟨⟨hkind, (nodeOwnPropertiesEqual_iff _ _).mpr hown⟩, hlen⟩, ?_⟩
      refine (all_zip_iff _ _).mpr fun i x y hx hy => ?_
      have hmem : x ∈ childrenOf t a := by
        rw [childrenOf_eq ha]; exact List.mem_of_getElem? hx
      have hpar : parentOf t x = some a := parentOf_of_mem_childrenOf hwf hmem
      obtain ⟨cd, hcd, -⟩ := parentOf_eq_some hpar
      have hdep : depth t x = depth t a + 1 := depth_parent hwf hpar
      exact ih x y cd hcd (by omega) (hch i x y hx hy)

/-- **`isEqualNode` の比較 `nodeEquals` は、木の上でちょうど §4.4 の equals である。** -/
theorem nodeEquals_iff {t : Tree} (hwf : WellFormed t) (a b : NodeId) :
    nodeEquals t a b = true ↔ NodeEquals t a b := by
  constructor
  · exact nodeEquals_of_fuel _ a b
  · intro h
    cases h with
    | @intro _ _ da db ha hb hkind hown hlen hch =>
      exact fuel_of_nodeEquals hwf t.size a b da ha (Nat.sub_le _ _)
        (NodeEquals.intro ha hb hkind hown hlen hch)

/-! ## clone は equals -/

/-- id と node document を落として同じ attribute は、equals の条件を満たす。 -/
theorem ownPropertiesEqual_of_shapeAnon {a b : NodeData} (h : a.shapeAnon = b.shapeAnon)
    (hd : a.data = b.data) : OwnPropertiesEqual a b := by
  have hk : a.kind = b.kind := by
    have := congrArg NodeData.kind h; simpa using this
  have hattrs : (a.attributes.map Attr.dropDoc).map Attr.anon =
      (b.attributes.map Attr.dropDoc).map Attr.anon := by
    have := congrArg NodeData.attributes h
    simpa [NodeData.shapeAnon] using this
  have hfield : ∀ (f : Attr → String × Option String × String),
      (∀ x, f (Attr.anon x) = f x) → (∀ x, f (Attr.dropDoc x) = f x) →
      a.attributes.map f = b.attributes.map f := by
    intro f hf hg
    have := congrArg (List.map f) hattrs
    simpa [List.map_map, Function.comp_def, hf, hg] using this
  have hlen : a.attributes.length = b.attributes.length := by
    have := congrArg List.length hattrs; simpa using this
  have hmatch : ∀ x ∈ a.attributes, ∃ y ∈ b.attributes, AttrEquals x y := by
    intro x hx
    have := hfield (fun z => (z.localName, z.namespace, z.value)) (fun _ => rfl) (fun _ => rfl)
    have hm : (x.localName, x.namespace, x.value) ∈
        b.attributes.map (fun z => (z.localName, z.namespace, z.value)) := by
      rw [← this]; exact List.mem_map_of_mem hx
    obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hm
    simp only [Prod.mk.injEq] at hxy
    exact ⟨y, hy, hxy.2.1.symm, hxy.1.symm, hxy.2.2.symm⟩
  have g := fun {α : Type} (f : NodeData → α) (hf : ∀ d, f d.shapeAnon = f d) =>
    (show f a = f b by rw [← hf a, ← hf b, h])
  unfold OwnPropertiesEqual
  cases hka : a.kind <;> simp only
  · exact ⟨g NodeData.doctypeName (fun _ => rfl), g NodeData.publicId (fun _ => rfl),
      g NodeData.systemId (fun _ => rfl)⟩
  · exact ⟨g NodeData.namespace (fun _ => rfl), g NodeData.prefix (fun _ => rfl),
      g NodeData.localName (fun _ => rfl), hlen, hmatch⟩
  · exact hd
  · exact hd
  · exact ⟨g NodeData.piTarget (fun _ => rfl), hd⟩
  · exact hd

/-- **clone の関係で結ばれた node は equals である。** -/
theorem cloneOf_nodeEquals {t : Tree} (hwf : WellFormed t) {c n : NodeId} (h : CloneOf t c n) :
    NodeEquals t c n := by
  obtain ⟨R, hcn, hstep⟩ := h
  have key : ∀ (k : Nat) (a b : NodeId) (ad : NodeData), t.get? a = some ad →
      t.size - depth t a ≤ k → R a b → NodeEquals t a b := by
    intro k
    induction k with
    | zero =>
      intro a b ad ha hk _
      exfalso
      have := depth_lt_size hwf ha
      omega
    | succ k ih =>
      intro a b ad ha hk hab
      obtain ⟨cd, d, hcd, hd, hsh, hdata, hlen, hch⟩ := hstep a b hab
      rw [ha] at hcd
      cases hcd
      have hk' : ad.kind = d.kind := by
        have := congrArg NodeData.kind hsh; simpa using this
      refine NodeEquals.intro ha hd hk' (ownPropertiesEqual_of_shapeAnon hsh hdata) hlen ?_
      intro i x y hx hy
      have hmem : x ∈ childrenOf t a := by
        rw [childrenOf_eq ha]; exact List.mem_of_getElem? hx
      have hpar : parentOf t x = some a := parentOf_of_mem_childrenOf hwf hmem
      obtain ⟨xd, hxd, -⟩ := parentOf_eq_some hpar
      have hdep : depth t x = depth t a + 1 := depth_parent hwf hpar
      exact ih x y xd hxd (by omega) (hch i x y hx hy)
  obtain ⟨cd, -, hcd, -⟩ := hstep c n hcn
  exact key t.size c n cd hcd (Nat.sub_le _ _) hcn

/-- **deep clone は原本と equals である。** `isEqualNode` が真を返す。 -/
theorem cloneNode_nodeEquals {s s' : DOMState} {n c : NodeId} (hv : AdmissibleDOMState s)
    (h : cloneNode s n true = .ok (c, s')) : nodeEquals s'.tree c n = true :=
  have hwf' := (admissible_cloneNode hv h).wellFormed
  (nodeEquals_iff hwf' c n).mpr (cloneOf_nodeEquals hwf' (cloneNode_cloneOf hv h))

end Dom.Spec
