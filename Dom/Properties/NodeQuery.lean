import Dom.Query.NodeQuery
import Dom.Properties.Tree

/-!
# `Dom/Query/NodeQuery.lean` の契約

いまのところ `isEqualNode` の fuel についてだけ書いてある。

`nodeEqualsFuel` は fuel が尽きると **例外ではなく `false`** を返す。`isEqualNode`
が `false` を返すのは正常な場合でもあるので、fuel 切れは差分テストでも
「等しくないと判定した」と区別がつかない。だから足りることは証明で押さえる。
-/

namespace Dom

variable {t : Tree}

/-- 要素ごとに一致するなら `all` の値も一致する。 -/
theorem all_congr {α : Type _} : ∀ (l : List α) {p q : α → Bool},
    (∀ x ∈ l, p x = q x) → l.all p = l.all q
  | [], _, _, _ => rfl
  | x :: rest, p, q, h => by
    simp only [List.all_cons]
    rw [h x (List.mem_cons_self ..), all_congr rest fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- zip の要素の第一成分は元の list の要素である。 -/
theorem fst_mem_of_mem_zip {α β : Type _} :
    ∀ {l₁ : List α} {l₂ : List β} {p : α × β}, p ∈ l₁.zip l₂ → p.1 ∈ l₁
  | [], _, _, h => by simp [List.zip] at h
  | _ :: _, [], _, h => by simp [List.zip] at h
  | x :: r₁, y :: r₂, p, h => by
    rw [List.zip_cons_cons] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (fst_mem_of_mem_zip h)

/-! ## `nodeEqualsFuel` の interface -/

theorem nodeEqualsFuel_succ_pos {a b : NodeId} {da db : NodeData} (f : Nat)
    (ha : t.get? a = some da) (hb : t.get? b = some db) :
    nodeEqualsFuel t (f + 1) a b =
      (da.kind == db.kind && nodeOwnPropertiesEqual da db &&
        da.children.length == db.children.length &&
        (da.children.zip db.children).all fun p => nodeEqualsFuel t f p.1 p.2) := by
  show (match t.get? a, t.get? b with
    | some da, some db =>
      da.kind == db.kind && nodeOwnPropertiesEqual da db &&
        da.children.length == db.children.length &&
        (da.children.zip db.children).all fun p => nodeEqualsFuel t f p.1 p.2
    | _, _ => false) = _
  rw [ha, hb]

theorem nodeEqualsFuel_succ_none_left {a b : NodeId} (f : Nat) (ha : t.get? a = none) :
    nodeEqualsFuel t (f + 1) a b = false := by
  show (match t.get? a, t.get? b with
    | some da, some db =>
      da.kind == db.kind && nodeOwnPropertiesEqual da db &&
        da.children.length == db.children.length &&
        (da.children.zip db.children).all fun p => nodeEqualsFuel t f p.1 p.2
    | _, _ => false) = _
  rw [ha]

theorem nodeEqualsFuel_succ_none_right {a b : NodeId} {da : NodeData} (f : Nat)
    (ha : t.get? a = some da) (hb : t.get? b = none) :
    nodeEqualsFuel t (f + 1) a b = false := by
  show (match t.get? a, t.get? b with
    | some da, some db =>
      da.kind == db.kind && nodeOwnPropertiesEqual da db &&
        da.children.length == db.children.length &&
        (da.children.zip db.children).all fun p => nodeEqualsFuel t f p.1 p.2
    | _, _ => false) = _
  rw [ha, hb]

/-! ## fuel は足りる -/

/--
**`nodeEqualsFuel` は fuel が「store の要素数 − 深さ」以上なら答えが変わらない。**

`mem_preorderFuel_of_inclusive_descendant` と同じ形の induction である。
一段降りると深さが一つ増えるので、必要な fuel は一つ減る。
-/
theorem nodeEqualsFuel_eq_of_le (hwf : WellFormed t) :
    ∀ (k : Nat) (a b : NodeId) (d : NodeData), t.get? a = some d →
      t.size - depth t a ≤ k → ∀ g, k ≤ g →
      nodeEqualsFuel t k a b = nodeEqualsFuel t g a b := by
  intro k
  induction k with
  | zero =>
    intro a b d ha hk _ _
    exfalso
    have := depth_lt_size hwf ha
    omega
  | succ k ih =>
    intro a b d ha hk g hg
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    have hkg : k ≤ g := by omega
    cases hb : t.get? b with
    | none => rw [nodeEqualsFuel_succ_none_right k ha hb, nodeEqualsFuel_succ_none_right g ha hb]
    | some db =>
      have hall : (d.children.zip db.children).all (fun p => nodeEqualsFuel t k p.1 p.2)
          = (d.children.zip db.children).all (fun p => nodeEqualsFuel t g p.1 p.2) := by
        refine all_congr _ fun p hp => ?_
        have hmem : p.1 ∈ childrenOf t a := by
          rw [childrenOf_eq ha]; exact fst_mem_of_mem_zip hp
        have hpar : parentOf t p.1 = some a := parentOf_of_mem_childrenOf hwf hmem
        obtain ⟨cd, hcd, -⟩ := parentOf_eq_some hpar
        have hdep : depth t p.1 = depth t a + 1 := depth_parent hwf hpar
        exact ih p.1 p.2 cd hcd (by omega) g hkg
      rw [nodeEqualsFuel_succ_pos k ha hb, nodeEqualsFuel_succ_pos g ha hb, hall]

/--
**fuel `t.size` で足りる。**

`nodeEquals` はそれ以上 fuel を増やしても答えが変わらない。
`isEqualNode` が fuel 切れで `false` を返すことは無い。
-/
theorem nodeEqualsFuel_eq_nodeEquals (hwf : WellFormed t) (a b : NodeId) {g : Nat}
    (hg : t.size ≤ g) : nodeEqualsFuel t g a b = nodeEquals t a b := by
  cases ha : t.get? a with
  | none =>
    cases hs : t.size with
    | zero =>
      cases g with
      | zero =>
        show _ = nodeEqualsFuel t t.size a b
        rw [hs]
      | succ g =>
        rw [nodeEqualsFuel_succ_none_left g ha]
        show _ = nodeEqualsFuel t t.size a b
        rw [hs]
        rfl
    | succ m =>
      obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
      rw [nodeEqualsFuel_succ_none_left g ha]
      show _ = nodeEqualsFuel t t.size a b
      rw [hs, nodeEqualsFuel_succ_none_left m ha]
  | some d =>
    exact (nodeEqualsFuel_eq_of_le hwf t.size a b d ha (by omega) g hg).symm

end Dom
