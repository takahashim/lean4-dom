import Dom.Properties.Mutation
import Dom.Range.Adjust

/-!
# boundary point の位置を数列で表す

DOM Standard §5.3 の boundary point position は、tree order と `childTowards` を使って
場合分けで定義されている。ここではそれと同値な、より扱いやすい表現を与える。

root から node へ至る経路上の各段の index を並べた列（`pathIndices`）の末尾に
offset を付けたものを boundary point の **key** とし、boundary point position が
key の辞書式比較に一致することを示す（`bpPosition_eq_lexCmp`）。

この表現があると、mutation が `BoundaryLE` を保つことを
「key の上の単調写像である」という形で示せる。`Dom/Properties/Range.lean` で使う。
-/

namespace Dom

variable {t : Tree}

/-! ## root からの経路 -/

/-- root から `n` までの経路。root が先頭、`n` が末尾。 -/
def pathNodes (t : Tree) (n : NodeId) : List NodeId :=
  (n :: ancestors t n).reverse

/-- root から `n` までの経路上の、root を除く各 node の index の列。 -/
def pathIndices (t : Tree) (n : NodeId) : List Nat :=
  ((pathNodes t n).drop 1).map fun x => (index t x).getD 0

theorem pathNodes_ne_nil (t : Tree) (n : NodeId) : pathNodes t n ≠ [] := by
  unfold pathNodes
  simp

theorem pathNodes_of_parent_none {t : Tree} {n : NodeId} (h : parentOf t n = none) :
    pathNodes t n = [n] := by
  unfold pathNodes ancestors
  cases hs : t.size with
  | zero => simp [ancestorChain]
  | succ f => rw [ancestorChain_succ_none h]; simp

theorem pathNodes_eq_append (hwf : WellFormed t) {n p : NodeId} (hp : parentOf t n = some p) :
    pathNodes t n = pathNodes t p ++ [n] := by
  unfold pathNodes
  rw [ancestors_eq_cons hwf hp]
  simp

theorem pathIndices_of_parent_none {t : Tree} {n : NodeId} (h : parentOf t n = none) :
    pathIndices t n = [] := by
  unfold pathIndices
  rw [pathNodes_of_parent_none h]
  simp

theorem pathIndices_eq_append (hwf : WellFormed t) {n p : NodeId} (hp : parentOf t n = some p) :
    pathIndices t n = pathIndices t p ++ [(index t n).getD 0] := by
  unfold pathIndices
  rw [pathNodes_eq_append hwf hp]
  obtain ⟨x, l, hxl⟩ : ∃ x l, pathNodes t p = x :: l := by
    cases hl : pathNodes t p with
    | nil => exact absurd hl (pathNodes_ne_nil t p)
    | cons x l => exact ⟨x, l, rfl⟩
  rw [hxl]
  simp

/-- inclusive ancestor の経路は、経路の prefix になる。 -/
theorem pathNodes_prefix_of_inclusiveAncestor (hwf : WellFormed t) {a n : NodeId}
    (h : InclusiveAncestor t a n) : ∃ l, pathNodes t n = pathNodes t a ++ l := by
  rcases h with rfl | h
  · exact ⟨[], by simp⟩
  · induction h with
    | @step m hp => exact ⟨[m], pathNodes_eq_append hwf hp⟩
    | @trans m b hp _ ih =>
      obtain ⟨l, hl⟩ := ih
      exact ⟨l ++ [b], by rw [pathNodes_eq_append hwf hp, hl, List.append_assoc]⟩

/-- `p` の子 `c` の下にある node の経路 index は、`p` までの列 ++ `c` の index ++ 残り。 -/
theorem pathIndices_split (hwf : WellFormed t) {p c x : NodeId}
    (hc : parentOf t c = some p) (hx : InclusiveAncestor t c x) :
    ∃ rest, pathIndices t x = pathIndices t p ++ (index t c).getD 0 :: rest := by
  obtain ⟨l, hl⟩ := pathNodes_prefix_of_inclusiveAncestor hwf hx
  refine ⟨l.map fun y => (index t y).getD 0, ?_⟩
  unfold pathIndices
  rw [hl, pathNodes_eq_append hwf hc]
  obtain ⟨y, m, hym⟩ : ∃ y m, pathNodes t p = y :: m := by
    cases hm : pathNodes t p with
    | nil => exact absurd hm (pathNodes_ne_nil t p)
    | cons y m => exact ⟨y, m, rfl⟩
  rw [hym]
  simp

/-! ## childTowards -/

theorem mem_inclusiveAncestors_iff (hwf : WellFormed t) (n x : NodeId) :
    x ∈ n :: ancestors t n ↔ InclusiveAncestor t x n := by
  rw [List.mem_cons, mem_ancestors_iff hwf]

theorem childTowards_eq_none (hwf : WellFormed t) {a b : NodeId} (h : ¬ Ancestor t a b) :
    childTowards t a b = none := by
  cases hc : childTowards t a b with
  | none => rfl
  | some c =>
    exfalso
    unfold childTowards at hc
    have hmem : c ∈ b :: ancestors t b := List.mem_of_find?_eq_some hc
    have hp : parentOf t c = some a := by
      have := List.find?_some hc
      simpa using this
    have hac : Ancestor t a c := Ancestor.step hp
    rcases (mem_inclusiveAncestors_iff hwf b c).mp hmem with rfl | hcb
    · exact h hac
    · exact h (hac.trans_ancestor hcb)

theorem childTowards_eq_some (hwf : WellFormed t) {a b : NodeId} (h : Ancestor t a b) :
    ∃ c, childTowards t a b = some c ∧ parentOf t c = some a ∧ InclusiveAncestor t c b := by
  obtain ⟨c₀, hc₀, hc₀b⟩ := h.exists_child
  have hmem : c₀ ∈ b :: ancestors t b := (mem_inclusiveAncestors_iff hwf b c₀).mpr hc₀b
  cases hc : childTowards t a b with
  | none =>
    exfalso
    unfold childTowards at hc
    rw [List.find?_eq_none] at hc
    have := hc c₀ hmem
    simp [hc₀] at this
  | some c =>
    refine ⟨c, rfl, ?_, ?_⟩
    · unfold childTowards at hc
      have := List.find?_some hc
      simpa using this
    · unfold childTowards at hc
      exact (mem_inclusiveAncestors_iff hwf b c).mp (List.mem_of_find?_eq_some hc)

/-! ## 辞書式比較 -/

/-- 自然数列の辞書式比較。短いほうが prefix なら短いほうが小さい。 -/
def lexCmp : List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys =>
    match compare x y with
    | .eq => lexCmp xs ys
    | o => o

@[simp] theorem lexCmp_nil_nil : lexCmp [] [] = .eq := rfl
@[simp] theorem lexCmp_nil_cons (y : Nat) (ys : List Nat) : lexCmp [] (y :: ys) = .lt := rfl
@[simp] theorem lexCmp_cons_nil (x : Nat) (xs : List Nat) : lexCmp (x :: xs) [] = .gt := rfl

theorem lexCmp_cons_cons (x y : Nat) (xs ys : List Nat) :
    lexCmp (x :: xs) (y :: ys) =
      match compare x y with
      | .eq => lexCmp xs ys
      | o => o := rfl

theorem lexCmp_cons_lt {x y : Nat} (h : x < y) (xs ys : List Nat) :
    lexCmp (x :: xs) (y :: ys) = .lt := by
  rw [lexCmp_cons_cons, Nat.compare_eq_lt.mpr h]

theorem lexCmp_cons_gt {x y : Nat} (h : y < x) (xs ys : List Nat) :
    lexCmp (x :: xs) (y :: ys) = .gt := by
  rw [lexCmp_cons_cons, Nat.compare_eq_gt.mpr h]

theorem lexCmp_cons_eq (x : Nat) (xs ys : List Nat) :
    lexCmp (x :: xs) (x :: ys) = lexCmp xs ys := by
  rw [lexCmp_cons_cons, Nat.compare_eq_eq.mpr rfl]

/-- 共通の prefix を落としても比較結果は変わらない。 -/
theorem lexCmp_append_left : ∀ (l xs ys : List Nat), lexCmp (l ++ xs) (l ++ ys) = lexCmp xs ys
  | [], _, _ => rfl
  | x :: l, xs, ys => by
    simp only [List.cons_append, lexCmp_cons_eq]
    exact lexCmp_append_left l xs ys

/-- 引数を入れ替えると結果も入れ替わる。 -/
theorem lexCmp_swap : ∀ (xs ys : List Nat), lexCmp ys xs = (lexCmp xs ys).swap
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    simp only [lexCmp_cons_cons]
    rcases Nat.lt_trichotomy x y with h | h | h
    · rw [Nat.compare_eq_lt.mpr h, Nat.compare_eq_gt.mpr h]; rfl
    · subst h
      rw [Nat.compare_eq_eq.mpr rfl]
      exact lexCmp_swap xs ys
    · rw [Nat.compare_eq_gt.mpr h, Nat.compare_eq_lt.mpr h]; rfl

/-! ## boundary point の key -/

/-- boundary point の key。root からの index の列に offset を付けたもの。 -/
def bpKey (t : Tree) (bp : BoundaryPoint) : List Nat :=
  pathIndices t bp.node ++ [bp.offset]

theorem bpPositionDown_eq_lexCmp (hwf : WellFormed t) {a b : BoundaryPoint}
    (hs : PrecedesStruct t a.node b.node) :
    bpPositionDown t a b = lexCmp (bpKey t a) (bpKey t b) := by
  rcases hs with hanc | ⟨p, cx, cy, i, j, hcx, hcy, hi, hj, hij, hxa, hyb⟩
  · -- a.node が b.node の ancestor
    obtain ⟨c, hct, hcp, hcb⟩ := childTowards_eq_some hwf hanc
    obtain ⟨rest, hrest⟩ := pathIndices_split hwf hcp hcb
    have hkey : bpKey t b = pathIndices t a.node ++ (index t c).getD 0 :: (rest ++ [b.offset]) := by
      unfold bpKey
      rw [hrest]
      simp
    unfold bpPositionDown
    rw [hct, hkey]
    show (if (index t c).getD 0 < a.offset then Ordering.gt else Ordering.lt) = _
    unfold bpKey
    rw [lexCmp_append_left]
    rcases Nat.lt_trichotomy a.offset ((index t c).getD 0) with h | h | h
    · rw [if_neg (by omega), lexCmp_cons_lt h]
    · rw [if_neg (by omega), h, lexCmp_cons_eq]
      cases rest <;> rfl
    · rw [if_pos h, lexCmp_cons_gt h]
  · -- 兄弟の部分木に分かれている
    have hne : cx ≠ cy := by
      intro he
      subst he
      rw [hi] at hj
      have : i = j := Option.some.inj hj
      omega
    have hnotanc : ¬ Ancestor t a.node b.node := by
      intro hanc
      exact sibling_subtrees_disjoint hwf hcx hcy hne
        (hxa.trans_inclusive (InclusiveAncestor.of_ancestor hanc)) hyb
    obtain ⟨r1, hr1⟩ := pathIndices_split hwf hcx hxa
    obtain ⟨r2, hr2⟩ := pathIndices_split hwf hcy hyb
    unfold bpPositionDown
    rw [childTowards_eq_none hwf hnotanc]
    show Ordering.lt = _
    unfold bpKey
    rw [hr1, hr2]
    simp only [List.append_assoc, List.cons_append, lexCmp_append_left]
    rw [hi, hj]
    exact (lexCmp_cons_lt hij _ _).symm

/-- DOM Standard §5.3 の boundary point position は、key の辞書式比較に一致する。 -/
theorem bpPosition_eq_lexCmp (hwf : WellFormed t) {a b : BoundaryPoint} {ad bd : NodeData}
    (ha : t.get? a.node = some ad) (hb : t.get? b.node = some bd)
    (hroot : root t a.node = root t b.node) :
    bpPosition t a b = lexCmp (bpKey t a) (bpKey t b) := by
  unfold bpPosition
  by_cases hn : a.node = b.node
  · rw [if_pos hn]
    unfold bpKey
    rw [hn, lexCmp_append_left]
    show compare a.offset b.offset = _
    rcases Nat.lt_trichotomy a.offset b.offset with h | h | h
    · rw [Nat.compare_eq_lt.mpr h, lexCmp_cons_lt h]
    · rw [h, Nat.compare_eq_eq.mpr rfl, lexCmp_cons_eq]; rfl
    · rw [Nat.compare_eq_gt.mpr h, lexCmp_cons_gt h]
  · rw [if_neg hn]
    cases hp : precedes t b.node a.node with
    | true =>
      have hs : PrecedesStruct t b.node a.node :=
        (precedes_iff_struct hwf hb hroot.symm (fun he => hn he.symm)).mp hp
      rw [if_pos (by rfl)]
      rw [bpPositionDown_eq_lexCmp hwf hs, lexCmp_swap (bpKey t b) (bpKey t a)]
    | false =>
      have hs : PrecedesStruct t a.node b.node :=
        (precedes_eq_false_iff hwf ha hroot hn).mp hp
      rw [if_neg (by simp)]
      exact bpPositionDown_eq_lexCmp hwf hs

/-! ## 部分木を外したときの key の付け替え -/

/-- 位置 `i` の子を取り除いたときの index / offset の付け替え。 -/
def shiftDown (i x : Nat) : Nat := if i < x then x - 1 else x

theorem shiftDown_mono {i x y : Nat} (h : x ≤ y) : shiftDown i x ≤ shiftDown i y := by
  unfold shiftDown
  split <;> split <;> omega

theorem shiftDown_eq_of_lt {i x y : Nat} (hxy : x < y) (h : shiftDown i x = shiftDown i y) :
    x = i := by
  unfold shiftDown at h
  split at h <;> split at h <;> omega

/--
取り除く子の parent 以下の key の付け替え。

先頭は「その段の index（あるいは parent 自身を指す boundary point の offset）」なので
`shiftDown` でずらす。先頭がちょうど取り除く子の位置 `i` だったときは、
その boundary point は取り除かれる部分木の中にあったので、`(parent, i)` へ移される。
-/
def shiftTail (i : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs => shiftDown i x :: (if x = i then [] else xs)

/-- key が `P` で始まるかを見て、始まるならその後ろを付け替える。 -/
def dropPrefixNat : List Nat → List Nat → Option (List Nat)
  | [], k => some k
  | _ :: _, [] => none
  | x :: p, y :: k => if x = y then dropPrefixNat p k else none

theorem dropPrefixNat_eq_some : ∀ (P key rest : List Nat),
    dropPrefixNat P key = some rest → key = P ++ rest
  | [], key, rest, h => by simp only [dropPrefixNat, Option.some.injEq] at h; rw [h]; simp
  | _ :: _, [], _, h => by simp [dropPrefixNat] at h
  | x :: p, y :: k, rest, h => by
    unfold dropPrefixNat at h
    split at h
    · next he => rw [he, List.cons_append, dropPrefixNat_eq_some p k rest h]
    · simp at h

@[simp] theorem dropPrefixNat_append (P rest : List Nat) :
    dropPrefixNat P (P ++ rest) = some rest := by
  induction P with
  | nil => rfl
  | cons x p ih => simp only [List.cons_append, dropPrefixNat]; exact ih

/-- 部分木を外したときの key の付け替え。`P` は外す node の parent までの index 列。 -/
def shiftKey (P : List Nat) (i : Nat) (key : List Nat) : List Nat :=
  match dropPrefixNat P key with
  | none => key
  | some rest => P ++ shiftTail i rest

theorem shiftKey_of_append (P : List Nat) (i : Nat) (rest : List Nat) :
    shiftKey P i (P ++ rest) = P ++ shiftTail i rest := by
  unfold shiftKey
  rw [dropPrefixNat_append]

theorem shiftKey_of_none {P : List Nat} {i : Nat} {key : List Nat}
    (h : dropPrefixNat P key = none) : shiftKey P i key = key := by
  unfold shiftKey
  rw [h]

/-- `P` で始まらない列との比較は、`P` の後ろに何が続くかに依らない。 -/
theorem lexCmp_append_of_dropPrefix_none : ∀ (P w : List Nat), dropPrefixNat P w = none →
    ∀ (u v : List Nat), lexCmp (P ++ u) w = lexCmp (P ++ v) w
  | [], w, h, _, _ => by simp [dropPrefixNat] at h
  | x :: p, [], _, u, v => by simp
  | x :: p, y :: w, h, u, v => by
    unfold dropPrefixNat at h
    simp only [List.cons_append, lexCmp_cons_cons]
    split at h
    · next he =>
      subst he
      rw [Nat.compare_eq_eq.mpr rfl]
      exact lexCmp_append_of_dropPrefix_none p w h u v
    · next hne =>
      rcases Nat.lt_trichotomy x y with hlt | he | hgt
      · rw [Nat.compare_eq_lt.mpr hlt]
      · exact absurd he hne
      · rw [Nat.compare_eq_gt.mpr hgt]

/-- `shiftTail` は辞書式順序を保つ。 -/
theorem shiftTail_mono (i : Nat) : ∀ (u v : List Nat), lexCmp u v ≠ .gt →
    lexCmp (shiftTail i u) (shiftTail i v) ≠ .gt
  | [], v, _ => by cases v <;> simp [shiftTail]
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
    rw [lexCmp_cons_cons] at h
    rcases Nat.lt_trichotomy x y with hlt | he | hgt
    · rw [shiftTail, shiftTail]
      rcases Nat.lt_or_ge (shiftDown i x) (shiftDown i y) with hs | hs
      · rw [lexCmp_cons_lt hs]; simp
      · have hxy : shiftDown i x = shiftDown i y :=
          Nat.le_antisymm (shiftDown_mono (Nat.le_of_lt hlt)) hs
        have hxi : x = i := shiftDown_eq_of_lt hlt hxy
        rw [if_pos hxi, if_neg (by omega : ¬ y = i), hxy, lexCmp_cons_eq]
        cases ys <;> simp
    · subst he
      rw [Nat.compare_eq_eq.mpr rfl] at h
      rw [shiftTail, shiftTail]
      by_cases hxi : x = i
      · rw [if_pos hxi, if_pos hxi, lexCmp_cons_eq]; simp
      · rw [if_neg hxi, if_neg hxi, lexCmp_cons_eq]
        exact h
    · rw [Nat.compare_eq_gt.mpr hgt] at h
      exact absurd rfl h

/-- `shiftKey` は辞書式順序を保つ。これが `BoundaryLE` 保存の中心。 -/
theorem shiftKey_mono (P : List Nat) (i : Nat) {u v : List Nat} (h : lexCmp u v ≠ .gt) :
    lexCmp (shiftKey P i u) (shiftKey P i v) ≠ .gt := by
  cases hu : dropPrefixNat P u with
  | none =>
    cases hv : dropPrefixNat P v with
    | none => rw [shiftKey_of_none hu, shiftKey_of_none hv]; exact h
    | some rv =>
      have hveq : v = P ++ rv := dropPrefixNat_eq_some P v rv hv
      rw [shiftKey_of_none hu, hveq, shiftKey_of_append]
      rw [lexCmp_swap, lexCmp_append_of_dropPrefix_none P u hu (shiftTail i rv) rv,
        ← lexCmp_swap, ← hveq]
      exact h
  | some ru =>
    have hueq : u = P ++ ru := dropPrefixNat_eq_some P u ru hu
    cases hv : dropPrefixNat P v with
    | none =>
      rw [shiftKey_of_none hv, hueq, shiftKey_of_append]
      rw [lexCmp_append_of_dropPrefix_none P v hv (shiftTail i ru) ru, ← hueq]
      exact h
    | some rv =>
      have hveq : v = P ++ rv := dropPrefixNat_eq_some P v rv hv
      rw [hueq, hveq, shiftKey_of_append, shiftKey_of_append, lexCmp_append_left]
      rw [hueq, hveq, lexCmp_append_left] at h
      exact shiftTail_mono i ru rv h

/-! ## key は node を決める -/

theorem pathIndices_length (t : Tree) (n : NodeId) : (pathIndices t n).length = depth t n := by
  unfold pathIndices pathNodes depth
  simp

theorem parentOf_eq_none_of_depth_zero (hwf : WellFormed t) {n : NodeId}
    (h : depth t n = 0) : parentOf t n = none := by
  cases hp : parentOf t n with
  | none => rfl
  | some q =>
    exfalso
    have := ancestors_eq_cons hwf hp
    unfold depth at h
    rw [this] at h
    simp at h

theorem depth_eq_zero_of_parent_none {t : Tree} {n : NodeId} (h : parentOf t n = none) :
    depth t n = 0 := by
  unfold depth ancestors
  cases hs : t.size with
  | zero => simp [ancestorChain]
  | succ f => rw [ancestorChain_succ_none h]; rfl

theorem exists_parentOf_of_depth_ne_zero {t : Tree} {n : NodeId} (h : depth t n ≠ 0) :
    ∃ q, parentOf t n = some q := by
  cases hp : parentOf t n with
  | none => exact absurd (depth_eq_zero_of_parent_none hp) h
  | some q => exact ⟨q, rfl⟩

theorem root_eq_self_of_parent_none {t : Tree} {n : NodeId} (h : parentOf t n = none) :
    root t n = n := by
  unfold root
  exact rootFuel_of_parent_none h

/-- 同じ parent を持ち同じ index を持つ子は同じ node。 -/
theorem eq_of_index_eq (hwf : WellFormed t) {x y p : NodeId}
    (hx : parentOf t x = some p) (hy : parentOf t y = some p)
    (h : (index t x).getD 0 = (index t y).getD 0) : x = y := by
  obtain ⟨i, hi⟩ := index_isSome hwf hx
  obtain ⟨j, hj⟩ := index_isSome hwf hy
  rw [hi, hj] at h
  simp only [Option.getD_some] at h
  subst h
  obtain ⟨u, v, hsplit, hlen, _⟩ := (index_eq_some_iff_split hx).mp hi
  obtain ⟨u', v', hsplit', hlen', _⟩ := (index_eq_some_iff_split hy).mp hj
  exact Dom.ListUtil.append_cons_inj (by rw [← hsplit, hsplit']) (by omega)

/-- 同じ root にある node は、key（index の列）で一意に定まる。 -/
theorem eq_of_pathIndices_eq (hwf : WellFormed t) :
    ∀ (d : Nat) (x y : NodeId), depth t x = d → root t x = root t y →
      pathIndices t x = pathIndices t y → x = y := by
  intro d
  induction d with
  | zero =>
    intro x y hdx hroot hpath
    have hdy : depth t y = 0 := by
      have := congrArg List.length hpath
      rw [pathIndices_length, pathIndices_length, hdx] at this
      omega
    have hpx := parentOf_eq_none_of_depth_zero hwf hdx
    have hpy := parentOf_eq_none_of_depth_zero hwf hdy
    rw [root_eq_self_of_parent_none hpx, root_eq_self_of_parent_none hpy] at hroot
    exact hroot
  | succ d ih =>
    intro x y hdx hroot hpath
    have hdy : depth t y = d + 1 := by
      have := congrArg List.length hpath
      rw [pathIndices_length, pathIndices_length, hdx] at this
      omega
    obtain ⟨px, hpx⟩ : ∃ px, parentOf t x = some px := by
      exact exists_parentOf_of_depth_ne_zero (by omega)
    obtain ⟨py, hpy⟩ : ∃ py, parentOf t y = some py := by
      exact exists_parentOf_of_depth_ne_zero (by omega)
    rw [pathIndices_eq_append hwf hpx, pathIndices_eq_append hwf hpy] at hpath
    have hlen : (pathIndices t px).length = (pathIndices t py).length := by
      rw [pathIndices_length, pathIndices_length, depth_parent hwf hpx,
        depth_parent hwf hpy] at *
      omega
    obtain ⟨hpre, hlast⟩ := List.append_inj hpath hlen
    have hidx : (index t x).getD 0 = (index t y).getD 0 := by simpa using hlast
    have hrootp : root t px = root t py := by
      rw [← root_eq_of_ancestor hwf (Ancestor.step hpx), ← root_eq_of_ancestor hwf
        (Ancestor.step hpy)]
      exact hroot
    have hdpx : depth t px = d := by
      have := depth_parent hwf hpx; omega
    have := ih px py hdpx hrootp hpre
    subst this
    exact eq_of_index_eq hwf hpx hpy hidx

/-- 深さ `m` の inclusive ancestor。 -/
theorem exists_inclusiveAncestor_at_depth (hwf : WellFormed t) :
    ∀ (d : Nat) (x : NodeId), depth t x = d → ∀ (m : Nat), m ≤ d →
      ∃ z, InclusiveAncestor t z x ∧ pathIndices t z = (pathIndices t x).take m := by
  intro d
  induction d with
  | zero =>
    intro x hdx m hm
    have : m = 0 := Nat.le_zero.mp hm
    subst this
    have hnil : pathIndices t x = [] :=
      List.eq_nil_of_length_eq_zero (by rw [pathIndices_length, hdx])
    exact ⟨x, Or.inl rfl, by rw [hnil]; rfl⟩
  | succ d ih =>
    intro x hdx m hm
    rcases Nat.lt_or_ge m (d + 1) with hlt | hge
    · obtain ⟨px, hpx⟩ : ∃ px, parentOf t x = some px := by
        exact exists_parentOf_of_depth_ne_zero (by omega)
      have hdpx : depth t px = d := by have := depth_parent hwf hpx; omega
      obtain ⟨z, hz, hzp⟩ := ih px hdpx m (by omega)
      refine ⟨z, hz.trans_inclusive (InclusiveAncestor.of_ancestor (Ancestor.step hpx)), ?_⟩
      rw [hzp, pathIndices_eq_append hwf hpx,
        List.take_append_of_le_length (by rw [pathIndices_length, hdpx]; omega)]
    · have : m = d + 1 := by omega
      subst this
      refine ⟨x, Or.inl rfl, ?_⟩
      rw [List.take_of_length_le (Nat.le_of_eq (by rw [pathIndices_length, hdx]))]

/--
`p` までの key が `x` の key の真の prefix なら、`p` は `x` の inclusive ancestor。

`shiftKey` の適用範囲を押さえるために使う。
-/
theorem inclusiveAncestor_of_dropPrefix (hwf : WellFormed t) {p x : NodeId} {o : Nat}
    (hroot : root t p = root t x) {rest : List Nat}
    (h : dropPrefixNat (pathIndices t p) (pathIndices t x ++ [o]) = some rest)
    (hrest : rest ≠ []) : InclusiveAncestor t p x := by
  have heq := dropPrefixNat_eq_some _ _ _ h
  have hlen : (pathIndices t p).length ≤ (pathIndices t x).length := by
    have h1 := congrArg List.length heq
    simp only [List.length_append, List.length_cons, List.length_nil] at h1
    have : rest.length ≠ 0 := fun he => hrest (List.eq_nil_of_length_eq_zero he)
    omega
  obtain ⟨z, hz, hzp⟩ := exists_inclusiveAncestor_at_depth hwf (depth t x) x rfl
    ((pathIndices t p).length) (by rw [← pathIndices_length]; exact hlen)
  have hzeq : pathIndices t z = pathIndices t p := by
    rw [hzp, ← List.take_append_of_le_length (l₂ := [o]) hlen, heq, List.take_left]
  have hrz : root t z = root t p := by
    rcases hz with rfl | hz
    · exact hroot.symm
    · rw [← root_eq_of_ancestor hwf hz]; exact hroot.symm
  have : z = p := eq_of_pathIndices_eq hwf (depth t z) z p rfl hrz hzeq
  subst this
  exact hz

/-! ## detach と key -/

section Detach

variable {t t' : Tree} {n p : NodeId} {i : Nat}

/-- `detach` は旧 parent 以外の children を変えない。 -/
theorem detach_childrenOf_ne (hpar : parentOf t n = some p) (hd : detach t n = .ok t')
    {q : NodeId} (hq : q ≠ p) : childrenOf t' q = childrenOf t q := by
  by_cases hqn : q = n
  · subst hqn
    rcases detach_ok_cases hd with ⟨d, hdd, hdp, rfl⟩ | ⟨d, p', pd, hdd, hdp, hpd, rfl⟩
    · rfl
    · rw [childrenOf, childrenOf, get?_detachFrom_self, hdd]
  · exact childrenOf_congr (detach_frame hd hqn (fun p' hp' => by
      rw [hpar] at hp'; rw [Option.some.inj hp'] at hq; exact hq))

/-- 旧 parent の子でない node の index は変わらない。 -/
theorem index_detach_ne (hpar : parentOf t n = some p) (hd : detach t n = .ok t')
    {c : NodeId} (hcn : c ≠ n) (hcp : parentOf t c ≠ some p) : index t' c = index t c := by
  unfold index
  rw [parentOf_detach hd, if_neg hcn]
  cases hq : parentOf t c with
  | none => rfl
  | some q =>
    have hqp : q ≠ p := fun he => hcp (by rw [hq, he])
    simp only [Option.bind_some, detach_childrenOf_ne hpar hd hqp]

/-- 旧 parent の子の index は、取り除いた位置より後ろなら 1 減る。 -/
theorem index_detach_at (hwf : WellFormed t) (hpar : parentOf t n = some p)
    (hi : index t n = some i) (hd : detach t n = .ok t')
    {c : NodeId} {k : Nat} (hcn : c ≠ n) (hcp : parentOf t c = some p)
    (hk : index t c = some k) : index t' c = some (shiftDown i k) := by
  obtain ⟨pd, hpd⟩ := exists_data_of_parentOf hwf hpar
  have hnd : (childrenOf t p).Nodup := by
    rw [childrenOf_eq hpd]; exact hwf.children_nodup p pd hpd
  have hpar' : parentOf t' c = some p := by rw [parentOf_detach hd, if_neg hcn]; exact hcp
  have hi' : (childrenOf t p).findIdx? (fun x => decide (x = n)) = some i := by
    unfold index at hi; rw [hpar] at hi; simpa using hi
  have hk' : (childrenOf t p).findIdx? (fun x => decide (x = c)) = some k := by
    unfold index at hk; rw [hcp] at hk; simpa using hk
  unfold index
  rw [hpar']
  simp only [Option.bind_some]
  rw [detach_childrenOf hwf hpar hd]
  rw [Dom.ListUtil.findIdx?_removeAll hnd hcn hi' hk']
  rfl

/-! ### detach の後の ancestor 列 -/

theorem ancestorChain_detach_eq (hd : detach t n = .ok t') :
    ∀ (f : Nat) (x : NodeId), ¬ InclusiveAncestor t n x →
      ancestorChain t' f x = ancestorChain t f x := by
  intro f
  induction f with
  | zero => intro x _; rfl
  | succ f ih =>
    intro x hx
    have hxn : x ≠ n := fun he => hx (Or.inl he.symm)
    have hpe : parentOf t' x = parentOf t x := by rw [parentOf_detach hd, if_neg hxn]
    cases hq : parentOf t x with
    | none => rw [ancestorChain_succ_none (by rw [hpe, hq]), ancestorChain_succ_none hq]
    | some q =>
      have hq' : ¬ InclusiveAncestor t n q := by
        intro hnq
        exact hx (Or.inr (Ancestor.of_parent_inclusive hq hnq))
      rw [ancestorChain_succ_some (by rw [hpe, hq]), ancestorChain_succ_some hq, ih q hq']

theorem ancestors_detach_eq (hwf : WellFormed t) (hwf' : WellFormed t')
    (hd : detach t n = .ok t') {x : NodeId} {xd xd' : NodeData}
    (hx : t.get? x = some xd) (hx' : t'.get? x = some xd')
    (h : ¬ InclusiveAncestor t n x) : ancestors t' x = ancestors t x := by
  have h1 : ancestorChain t (t.size + t'.size) x = ancestors t x :=
    ancestorChain_eq_of_length_lt (ancestorChain_length_lt_size hwf hx t.size) _ (by omega)
  have h2 : ancestorChain t' (t.size + t'.size) x = ancestors t' x :=
    ancestorChain_eq_of_length_lt (ancestorChain_length_lt_size hwf' hx' t'.size) _ (by omega)
  rw [← h1, ← h2, ancestorChain_detach_eq hd _ x h]

theorem pathNodes_detach_eq (hwf : WellFormed t) (hwf' : WellFormed t')
    (hd : detach t n = .ok t') {x : NodeId} {xd xd' : NodeData}
    (hx : t.get? x = some xd) (hx' : t'.get? x = some xd')
    (h : ¬ InclusiveAncestor t n x) : pathNodes t' x = pathNodes t x := by
  unfold pathNodes
  rw [ancestors_detach_eq hwf hwf' hd hx hx' h]

/-- 部分木の外にある node の root は変わらない。 -/
theorem root_detach_eq (hwf : WellFormed t) (hwf' : WellFormed t')
    (hd : detach t n = .ok t') {x : NodeId} (h : ¬ InclusiveAncestor t n x) :
    root t' x = root t x := by
  refine root_unique hwf' (inclusiveAncestor_detach_of_not_below hd
    (root_inclusive_ancestor t x) (fun hc => h hc.1)) ?_
  rw [parentOf_detach hd]
  split
  · rfl
  · exact root_parent_eq_none hwf x

/-! ### detach の後の pathIndices -/

/-- 旧 parent の下に無い node の key は変わらない。 -/
theorem pathIndices_detach_of_not_below (hwf : WellFormed t) (hwf' : WellFormed t')
    (hpar : parentOf t n = some p) (hd : detach t n = .ok t') :
    ∀ (dd : Nat) (x : NodeId), depth t x = dd → ¬ Ancestor t p x → ¬ InclusiveAncestor t n x →
      pathIndices t' x = pathIndices t x := by
  intro dd
  induction dd with
  | zero =>
    intro x hdx _ hnx
    have hxn : x ≠ n := fun he => hnx (Or.inl he.symm)
    have hp := parentOf_eq_none_of_depth_zero hwf hdx
    rw [pathIndices_of_parent_none (by rw [parentOf_detach hd, if_neg hxn, hp]),
      pathIndices_of_parent_none hp]
  | succ dd ih =>
    intro x hdx hpx hnx
    have hxn : x ≠ n := fun he => hnx (Or.inl he.symm)
    obtain ⟨q, hq⟩ := exists_parentOf_of_depth_ne_zero (by omega : depth t x ≠ 0)
    have hqp : q ≠ p := by
      intro he; exact hpx (Ancestor.step (he ▸ hq))
    have hpq : ¬ Ancestor t p q := fun h => hpx (Ancestor.trans hq h)
    have hnq : ¬ InclusiveAncestor t n q := by
      intro h
      exact hnx (Or.inr (Ancestor.of_parent_inclusive hq h))
    have hq' : parentOf t' x = some q := by rw [parentOf_detach hd, if_neg hxn]; exact hq
    have hdq : depth t q = dd := by have := depth_parent hwf hq; omega
    rw [pathIndices_eq_append hwf' hq', pathIndices_eq_append hwf hq,
      ih q hdq hpq hnq, index_detach_ne hpar hd hxn (by rw [hq]; simpa using hqp)]

/-- 旧 parent 自身の key は変わらない。 -/
theorem pathIndices_detach_parent (hwf : WellFormed t) (hwf' : WellFormed t')
    (hpar : parentOf t n = some p) (hd : detach t n = .ok t') :
    pathIndices t' p = pathIndices t p := by
  have hnp : ¬ InclusiveAncestor t n p := by
    rintro (he | ha)
    · exact hwf.acyclic n (by rw [he] at hpar ⊢; exact Ancestor.step hpar)
    · exact hwf.acyclic n (ha.trans_ancestor (Ancestor.step hpar))
  exact pathIndices_detach_of_not_below hwf hwf' hpar hd (depth t p) p rfl (hwf.acyclic p) hnp

/-- 旧 parent の下にあり、外す部分木の中には無い node の key は、一段目だけがずれる。 -/
theorem pathIndices_detach_below (hwf : WellFormed t) (hwf' : WellFormed t')
    (hpar : parentOf t n = some p) (hi : index t n = some i) (hd : detach t n = .ok t') :
    ∀ (dd : Nat) (x : NodeId), depth t x = dd → Ancestor t p x → ¬ InclusiveAncestor t n x →
      ∃ k rest, k ≠ i ∧ pathIndices t x = pathIndices t p ++ k :: rest ∧
        pathIndices t' x = pathIndices t p ++ shiftDown i k :: rest := by
  intro dd
  induction dd with
  | zero =>
    intro x hdx hpx _
    exfalso
    obtain ⟨q, hq⟩ := hpx.parent_isSome
    exact absurd (parentOf_eq_none_of_depth_zero hwf hdx) (by rw [hq]; simp)
  | succ dd ih =>
    intro x hdx hpx hnx
    have hxn : x ≠ n := fun he => hnx (Or.inl he.symm)
    obtain ⟨q, hq⟩ := exists_parentOf_of_depth_ne_zero (by omega : depth t x ≠ 0)
    have hq' : parentOf t' x = some q := by rw [parentOf_detach hd, if_neg hxn]; exact hq
    have hdq : depth t q = dd := by have := depth_parent hwf hq; omega
    by_cases hqp : q = p
    · subst hqp
      obtain ⟨k, hk⟩ := index_isSome hwf hq
      have hki : k ≠ i := index_ne_of_ne hq hpar hk hi hxn
      refine ⟨k, [], hki, ?_, ?_⟩
      · rw [pathIndices_eq_append hwf hq, hk]; rfl
      · rw [pathIndices_eq_append hwf' hq', pathIndices_detach_parent hwf hwf' hpar hd,
          index_detach_at hwf hpar hi hd hxn hq hk]
        rfl
    · have hpq : Ancestor t p q :=
        (inclusiveAncestor_of_ancestor_parent hpx hq).resolve_left (fun he => hqp he.symm)
      have hnq : ¬ InclusiveAncestor t n q := by
        intro h
        exact hnx (Or.inr (Ancestor.of_parent_inclusive hq h))
      obtain ⟨k, rest, hki, hkt, hkt'⟩ := ih q hdq hpq hnq
      refine ⟨k, rest ++ [(index t x).getD 0], hki, ?_, ?_⟩
      · rw [pathIndices_eq_append hwf hq, hkt]; simp
      · rw [pathIndices_eq_append hwf' hq', hkt',
          index_detach_ne hpar hd hxn (by rw [hq]; simpa using hqp)]
        simp

/-! ### live range pre-remove steps と key -/

/--
DOM Standard §5.5 の live range pre-remove steps は、key の上では `shiftKey` として働く。

これと `shiftKey_mono` から、remove が `BoundaryLE` を保つことが従う。
-/
theorem bpKey_detach (hwf : WellFormed t) (hwf' : WellFormed t')
    (hpar : parentOf t n = some p) (hi : index t n = some i) (hd : detach t n = .ok t')
    {bp : BoundaryPoint} (hroot : root t bp.node = root t p) :
    bpKey t' (liveRangePreRemoveBP t n p i bp) = shiftKey (pathIndices t p) i (bpKey t bp) := by
  have hpp : pathIndices t' p = pathIndices t p := pathIndices_detach_parent hwf hwf' hpar hd
  unfold liveRangePreRemoveBP rangeMoveOutOfSubtree
  by_cases hin : InclusiveAncestor t n bp.node
  · -- 外す部分木の中：(parent, index) へ移される
    rw [if_pos (by rw [isInclusiveAncestorOf_iff hwf]; exact hin)]
    obtain ⟨rest, hrest⟩ := pathIndices_split hwf hpar hin
    rw [hi] at hrest
    simp only [Option.getD_some] at hrest
    have hshift : rangeShiftAfterRemove p i { node := p, offset := i }
        = { node := p, offset := i } := by
      unfold rangeShiftAfterRemove
      rw [if_neg (by simp)]
    rw [hshift]
    show pathIndices t' p ++ [i] = _
    rw [hpp]
    unfold bpKey
    rw [hrest, show (pathIndices t p ++ i :: rest) ++ [bp.offset]
      = pathIndices t p ++ i :: (rest ++ [bp.offset]) by simp, shiftKey_of_append]
    simp [shiftTail, shiftDown]
  · rw [if_neg (by rw [isInclusiveAncestorOf_iff hwf]; exact hin)]
    by_cases hbp : bp.node = p
    · -- parent 自身を指す：offset だけずれる
      have hshift : rangeShiftAfterRemove p i bp = { node := p, offset := shiftDown i bp.offset } := by
        unfold rangeShiftAfterRemove shiftDown
        by_cases hlt : i < bp.offset
        · rw [if_pos ⟨hbp, hlt⟩, if_pos hlt, hbp]
        · rw [if_neg (fun hc => hlt hc.2), if_neg hlt, ← hbp]
      rw [hshift]
      show pathIndices t' p ++ [shiftDown i bp.offset] = _
      rw [hpp]
      unfold bpKey
      rw [hbp, shiftKey_of_append]
      simp [shiftTail]
    · have hshift : rangeShiftAfterRemove p i bp = bp := by
        unfold rangeShiftAfterRemove
        rw [if_neg (fun hc => hbp hc.1)]
      rw [hshift]
      by_cases hanc : Ancestor t p bp.node
      · -- parent の下：一段目だけずれる
        obtain ⟨k, rest, hki, hkt, hkt'⟩ :=
          pathIndices_detach_below hwf hwf' hpar hi hd (depth t bp.node) bp.node rfl hanc hin
        unfold bpKey
        rw [hkt', hkt, show (pathIndices t p ++ k :: rest) ++ [bp.offset]
          = pathIndices t p ++ k :: (rest ++ [bp.offset]) by simp, shiftKey_of_append]
        simp [shiftTail, hki]
      · -- parent と無関係：何も変わらない
        have hnb : pathIndices t' bp.node = pathIndices t bp.node :=
          pathIndices_detach_of_not_below hwf hwf' hpar hd (depth t bp.node) bp.node rfl hanc hin
        unfold bpKey
        rw [hnb]
        cases hdp : dropPrefixNat (pathIndices t p) (pathIndices t bp.node ++ [bp.offset]) with
        | none => rw [shiftKey_of_none hdp]
        | some rest =>
          have hrest : rest = [] := by
            cases rest with
            | nil => rfl
            | cons a l =>
              exfalso
              rcases inclusiveAncestor_of_dropPrefix hwf hroot.symm hdp (by simp) with he | ha
              · exact hbp he.symm
              · exact hanc ha
          subst hrest
          have := dropPrefixNat_eq_some _ _ _ hdp
          rw [this, shiftKey_of_append]
          simp [shiftTail]

/-! ### remove が BoundaryLE を保つこと -/

theorem exists_get?_detach {t t' : Tree} {n : NodeId} (hd : detach t n = .ok t')
    {x : NodeId} {xd : NodeData} (h : t.get? x = some xd) : ∃ xd', t'.get? x = some xd' := by
  rcases detach_ok_cases hd with ⟨d, hdd, hdp, rfl⟩ | ⟨d, q, qd, hdd, hdp, hqd, rfl⟩
  · exact ⟨xd, h⟩
  · rw [get?_detachFrom]
    split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · exact ⟨xd, h⟩

@[simp] theorem liveRangePreRemoveBP_node (t : Tree) (n p : NodeId) (i : Nat)
    (bp : BoundaryPoint) :
    (liveRangePreRemoveBP t n p i bp).node =
      if isInclusiveAncestorOf t n bp.node then p else bp.node := by
  unfold liveRangePreRemoveBP rangeMoveOutOfSubtree rangeShiftAfterRemove
  split <;> split <;> rfl

/-- 外す node の root は旧 parent の root。 -/
theorem root_eq_of_parentOf (hwf : WellFormed t) (hpar : parentOf t n = some p) :
    root t n = root t p := root_eq_of_ancestor hwf (Ancestor.step hpar)

/-- 部分木の中に無い node は、外す node の inclusive descendant ではない。 -/
theorem not_inclusiveAncestor_of_parentOf (hwf : WellFormed t) (hpar : parentOf t n = some p) :
    ¬ InclusiveAncestor t n p := by
  rintro (he | ha)
  · exact hwf.acyclic n (by rw [he] at hpar ⊢; exact Ancestor.step hpar)
  · exact hwf.acyclic n (ha.trans_ancestor (Ancestor.step hpar))

theorem liveRangePreRemoveBP_not_below (hwf : WellFormed t) (hpar : parentOf t n = some p)
    (bp : BoundaryPoint) :
    ¬ InclusiveAncestor t n (liveRangePreRemoveBP t n p i bp).node := by
  rw [liveRangePreRemoveBP_node]
  split
  · exact not_inclusiveAncestor_of_parentOf hwf hpar
  · next h => exact fun hc => h (by rw [isInclusiveAncestorOf_iff hwf]; exact hc)

/-- 別の木にある boundary point は、live range pre-remove steps でも detach でも変わらない。 -/
theorem liveRangePreRemoveBP_of_other_root (hwf : WellFormed t) (hpar : parentOf t n = some p)
    {bp : BoundaryPoint} (hroot : root t bp.node ≠ root t p) :
    liveRangePreRemoveBP t n p i bp = bp ∧ ¬ Ancestor t p bp.node ∧
      ¬ InclusiveAncestor t n bp.node ∧ bp.node ≠ p := by
  have hnp : bp.node ≠ p := fun he => hroot (by rw [he])
  have hna : ¬ Ancestor t p bp.node := fun ha => hroot (root_eq_of_ancestor hwf ha)
  have hnn : ¬ InclusiveAncestor t n bp.node := by
    rintro (he | ha)
    · exact hroot (by rw [← he, root_eq_of_parentOf hwf hpar])
    · exact hroot (by rw [root_eq_of_ancestor hwf ha, root_eq_of_parentOf hwf hpar])
  refine ⟨?_, hna, hnn, hnp⟩
  unfold liveRangePreRemoveBP rangeMoveOutOfSubtree
  rw [if_neg (by rw [isInclusiveAncestorOf_iff hwf]; exact hnn)]
  unfold rangeShiftAfterRemove
  rw [if_neg (fun hc => hnp hc.1)]

/--
PLAN §8.2。remove（の木を変える部分と live range pre-remove steps）は
boundary point の順序を保つ。両端が別の node を指す場合も含む。
-/
theorem boundaryLE_detach (hwf : WellFormed t) (hwf' : WellFormed t')
    (hpar : parentOf t n = some p) (hi : index t n = some i) (hd : detach t n = .ok t')
    {a b : BoundaryPoint} {ad bd : NodeData}
    (ha : t.get? a.node = some ad) (hb : t.get? b.node = some bd)
    (hab : BoundaryLE t a b) :
    BoundaryLE t' (liveRangePreRemoveBP t n p i a) (liveRangePreRemoveBP t n p i b) := by
  obtain ⟨hroot, hpos⟩ := hab
  have hna : ¬ InclusiveAncestor t n (liveRangePreRemoveBP t n p i a).node :=
    liveRangePreRemoveBP_not_below hwf hpar a
  have hnb : ¬ InclusiveAncestor t n (liveRangePreRemoveBP t n p i b).node :=
    liveRangePreRemoveBP_not_below hwf hpar b
  obtain ⟨fad, hfad⟩ : ∃ d, t.get? (liveRangePreRemoveBP t n p i a).node = some d := by
    rw [liveRangePreRemoveBP_node]
    split
    · exact exists_data_of_parentOf hwf hpar
    · exact ⟨ad, ha⟩
  obtain ⟨fbd, hfbd⟩ : ∃ d, t.get? (liveRangePreRemoveBP t n p i b).node = some d := by
    rw [liveRangePreRemoveBP_node]
    split
    · exact exists_data_of_parentOf hwf hpar
    · exact ⟨bd, hb⟩
  obtain ⟨fad', hfad'⟩ := exists_get?_detach hd hfad
  obtain ⟨fbd', hfbd'⟩ := exists_get?_detach hd hfbd
  have hposkey : lexCmp (bpKey t a) (bpKey t b) ≠ .gt := by
    rw [← bpPosition_eq_lexCmp hwf ha hb hroot]; exact hpos
  by_cases hsame : root t a.node = root t p
  · -- 外す部分木と同じ木にある場合
    have hrootb : root t b.node = root t p := by rw [← hroot]; exact hsame
    have hrfa : root t (liveRangePreRemoveBP t n p i a).node = root t p := by
      rw [liveRangePreRemoveBP_node]
      split
      · rfl
      · exact hsame
    have hrfb : root t (liveRangePreRemoveBP t n p i b).node = root t p := by
      rw [liveRangePreRemoveBP_node]
      split
      · rfl
      · exact hrootb
    have hr' : root t' (liveRangePreRemoveBP t n p i a).node
        = root t' (liveRangePreRemoveBP t n p i b).node := by
      rw [root_detach_eq hwf hwf' hd hna, root_detach_eq hwf hwf' hd hnb, hrfa, hrfb]
    refine ⟨hr', ?_⟩
    rw [bpPosition_eq_lexCmp hwf' hfad' hfbd' hr',
      bpKey_detach hwf hwf' hpar hi hd (bp := a) hsame,
      bpKey_detach hwf hwf' hpar hi hd (bp := b) hrootb]
    exact shiftKey_mono _ i hposkey
  · -- 別の木にある場合
    obtain ⟨hfae, hnaa, hnna, hnpa⟩ := liveRangePreRemoveBP_of_other_root (i := i) hwf hpar hsame
    have hsameb : root t b.node ≠ root t p := by rw [← hroot]; exact hsame
    obtain ⟨hfbe, hnab, hnnb, hnpb⟩ := liveRangePreRemoveBP_of_other_root (i := i) hwf hpar hsameb
    have hpa : pathIndices t' a.node = pathIndices t a.node :=
      pathIndices_detach_of_not_below hwf hwf' hpar hd (depth t a.node) a.node rfl hnaa hnna
    have hpb : pathIndices t' b.node = pathIndices t b.node :=
      pathIndices_detach_of_not_below hwf hwf' hpar hd (depth t b.node) b.node rfl hnab hnnb
    have hra : root t' a.node = root t a.node := root_detach_eq hwf hwf' hd hnna
    have hrb : root t' b.node = root t b.node := root_detach_eq hwf hwf' hd hnnb
    obtain ⟨ad', had'⟩ := exists_get?_detach hd ha
    obtain ⟨bd', hbd'⟩ := exists_get?_detach hd hb
    rw [hfae, hfbe]
    refine ⟨by rw [hra, hrb]; exact hroot, ?_⟩
    rw [bpPosition_eq_lexCmp hwf' had' hbd' (by rw [hra, hrb]; exact hroot)]
    unfold bpKey
    rw [hpa, hpb]
    exact hposkey

end Detach

end Dom
