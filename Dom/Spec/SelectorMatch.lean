import Dom.Spec.Selector
import Dom.Properties.Selector
import Dom.Validity.AttributeList

/-!
# selector の照合の関係意味論（全体）

`Dom/Spec/Selector.lean` は照合を部品ごとに仕様と結んだ（`An+B` の index、combinator の候補、
attribute の演算子、`:nth-*()` の位置、type selector、`:root`、`:empty`、`:has()` の候補）。
この module はそれらを組み上げて、**selector list・complex・compound・simple の照合全体**を
一つの関係として書き、`matchSelList` ほかがそれにちょうど一致することを示す。

## 書き方の制約

関係は照合の実行関数を呼ばない。`combCandidates`・`elementSiblings`・`indexOfNode`・
`splitWsAux`・`attrTestHolds`・`selectorAttrOk` のような実装の道具は使わず、
`Dom/Spec/Selector.lean` の仕様側の語彙（`Ancestor`・`ElementSiblingBefore`・`AnBIndex`・
`WordIn`・`SelectorAttrMatches`・`AttrOpHolds`・`TypeSelectorMatches` ほか）だけで書く。

再帰は selector の大きさで止まる（実行側と同じ測度）。`:not()` は否定を含むので帰納的な関係
ではなく、selector に沿った再帰で定義した Prop にしてある。

## 仕様の語彙での読み替え

| selector | 関係 |
| --- | --- |
| combinator | `Combines`：`E F` は ancestor、`E > F` は parent、`E ~ F` と `E + F` は element の並びでの前後 |
| `.cls` | class 属性の値に、空白で区切られた語として現れる（`ClassToken`）。quirks mode なら ASCII case-insensitive に比べる（`ClassIdMatches`） |
| `#id` | id 属性の値と、quirks mode なら ASCII case-insensitive に、そうでなければ identical に一致する |
| `:first-child` ほか | 前（後）に element の sibling（同じ type のもの）が無い |
| `:nth-*()` | 前（後）にあって数える対象になる element の数に 1 を足したものが `An+B` の index（`NthCount`） |
| featureless な node | `:scope` だけが当たる |
-/

namespace Dom.Spec

open Dom Selectors Infra

/-- §16 の combinator が結ぶ二つの node。`E` は featureless な scoping root でもよい。 -/
def Combines (t : Tree) : Combinator → NodeId → NodeId → Prop
  | .descendant, e, f => Ancestor t e f
  | .child, e, f => parentOf t f = some e
  | .nextSibling, e, f => ElementSiblingImmediatelyBefore t e f
  | .subsequentSibling, e, f => ElementSiblingBefore t e f

/-- namespace を持たない attribute `name` の値が `v`。class と id はこれである（§6.5・§6.6）。 -/
def PlainAttrValue (d : NodeData) (name v : String) : Prop :=
  ∃ a ∈ d.attributes, a.localName = name ∧ a.namespace = none ∧ a.value = v

/-- §6.6 の class selector。class 属性の値に、空白で区切られた語として `v` が現れる。 -/
def ClassToken (classes v : String) : Prop :=
  v.toList ≠ [] ∧ NoWhitespace v.toList ∧ WordIn classes.toList v.toList

/-- element の node document が quirks mode である（DOM §4.5 の mode）。 -/
def InQuirksMode (t : Tree) (d : NodeData) : Prop :=
  ∃ doc, t.get? d.ownerDocument = some doc ∧ doc.mode = .quirks

/--
HTML §"Case-sensitivity of selectors"。class selector と id selector は、element の document が
quirks mode なら ASCII case-insensitive に、そうでなければ identical に比べる。
-/
def ClassIdMatches (t : Tree) (d : NodeData) (a b : String) : Prop :=
  (InQuirksMode t d ∧ asciiLowercase a = asciiLowercase b) ∨ (¬ InQuirksMode t d ∧ a = b)

/-- §6.3 の値の照合。値を持たない `[att]` は名前だけで当たる。 -/
def AttrTestOk (test : Option AttrTest) (value : String) : Prop :=
  match test with
  | none => True
  | some tst =>
    AttrOpHolds tst.op (caseFold tst.case value.toList) (caseFold tst.case tst.value.toList)

/--
§14.4 の `:nth-*()`。数える対象 `member` のうち、`n` より前（`fromEnd` なら後）にある
element の数に 1 を足したものが `An+B` の index であること。`n` 自身も数える対象でなければならない。

「前にある数」は、その element をちょうど一度ずつ並べた list の長さで言う。
-/
def NthCount (t : Tree) (member : NodeId → Prop) (fromEnd : Bool) (ab : AnB) (n : NodeId) :
    Prop :=
  member n ∧ ∃ others : List NodeId, others.Nodup ∧
    (∀ m, m ∈ others ↔ member m ∧
      (if fromEnd then ElementSiblingBefore t n m else ElementSiblingBefore t m n)) ∧
    AnBIndex ab (others.length + 1)

mutual

/-- §17.1 "match a selector against an element"。どれか一つの complex selector に当たる。 -/
def SelectorListMatches (ctx : MatchCtx) (l : List Complex) (n : NodeId) : Prop :=
  ∃ c ∈ l.attach, ComplexMatches ctx c.1 n
termination_by lSize l
decreasing_by
  simp_wf
  exact cxSize_lt_lSize _ _ c.2

/--
complex selector。右端の compound が `n` に当たり、combinator が結ぶ node のどれかに
残りの complex selector が当たる。
-/
def ComplexMatches (ctx : MatchCtx) (c : Complex) (n : NodeId) : Prop :=
  match c with
  | .one parts => CompoundMatches ctx parts n
  | .seq parts comb left =>
    CompoundMatches ctx parts n ∧ ∃ m, Combines ctx.tree comb m n ∧ ComplexMatches ctx left m
termination_by cxSize c
decreasing_by
  all_goals simp_wf
  all_goals simp only [cxSize]
  all_goals omega

/-- compound selector。含む simple selector のすべてに当たる。 -/
def CompoundMatches (ctx : MatchCtx) (parts : List Simple) (n : NodeId) : Prop :=
  ∀ s ∈ parts.attach, SimpleMatches ctx s.1 n
termination_by cpSize parts
decreasing_by
  simp_wf
  exact sSize_lt_cpSize _ _ s.2

/--
simple selector。element でない node は featureless で、`:scope` だけが当たる（§3.6）。
-/
def SimpleMatches (ctx : MatchCtx) (s : Simple) (n : NodeId) : Prop :=
  ∃ d, ctx.tree.get? n = some d ∧
    if d.kind = NodeKind.element then
      match s with
      | .typeSel name => TypeSelectorMatches ctx.tree d name
      | .univ => True
      | .id v => ∃ av, PlainAttrValue d "id" av ∧ ClassIdMatches ctx.tree d av v
      | .cls v => ∃ av, PlainAttrValue d "class" av ∧ ∃ w, ClassToken av w ∧ ClassIdMatches ctx.tree d w v
      | .attr name anyNs test =>
        ∃ a ∈ d.attributes, SelectorAttrMatches ctx.tree d anyNs name a ∧ AttrTestOk test a.value
      | .root => IsDocumentRoot ctx.tree n
      | .empty => ∀ c ∈ childrenOf ctx.tree n, EmptyIgnorable ctx.tree c
      | .firstChild => ¬ ∃ m, ElementSiblingBefore ctx.tree m n
      | .lastChild => ¬ ∃ m, ElementSiblingBefore ctx.tree n m
      | .onlyChild =>
        (¬ ∃ m, ElementSiblingBefore ctx.tree m n) ∧ ¬ ∃ m, ElementSiblingBefore ctx.tree n m
      | .firstOfType => ¬ ∃ m, ElementSiblingBefore ctx.tree m n ∧ SameType ctx.tree d m
      | .lastOfType => ¬ ∃ m, ElementSiblingBefore ctx.tree n m ∧ SameType ctx.tree d m
      | .onlyOfType =>
        (¬ ∃ m, ElementSiblingBefore ctx.tree m n ∧ SameType ctx.tree d m) ∧
          ¬ ∃ m, ElementSiblingBefore ctx.tree n m ∧ SameType ctx.tree d m
      | .nth kind ab ofSel =>
        match kind, ofSel with
        | .ofType, _ => NthCount ctx.tree (SameType ctx.tree d) false ab n
        | .lastOfType, _ => NthCount ctx.tree (SameType ctx.tree d) true ab n
        | .child, none => NthCount ctx.tree (fun _ => True) false ab n
        | .lastChild, none => NthCount ctx.tree (fun _ => True) true ab n
        | .child, some l => NthCount ctx.tree (fun m => SelectorListMatches ctx l m) false ab n
        | .lastChild, some l => NthCount ctx.tree (fun m => SelectorListMatches ctx l m) true ab n
      | .isSel l => SelectorListMatches ctx l n
      | .whereSel l => SelectorListMatches ctx l n
      | .notSel l => ¬ SelectorListMatches ctx l n
      | .has l =>
        ∃ c, InclusiveDescendant ctx.tree c (root ctx.tree n) ∧
          SelectorListMatches { ctx with anchor := some n } l c
      | .scope => ctx.scope = some n
      | .anchor => ctx.anchor = some n
    else s = .scope ∧ ctx.scope = some n
termination_by sSize s
decreasing_by
  all_goals simp_wf
  all_goals simp only [sSize, oSize]
  all_goals omega

end


/-! ## element の sibling の並び -/

/-- 重複の無い list で、同じ要素の位置で二通りに分けたら、分け方は一つである。 -/
theorem split_unique {α : Type} {x : α} : ∀ {a b c d : List α},
    a ++ x :: b = c ++ x :: d → x ∉ a → x ∉ c → a = c ∧ b = d
  | [], b, [], d, h, _, _ => by simp at h; exact ⟨rfl, h⟩
  | [], b, y :: c, d, h, _, hc => by
    simp at h; exact absurd (h.1 ▸ List.mem_cons_self) hc
  | y :: a, b, [], d, h, ha, _ => by
    simp at h; exact absurd (h.1 ▸ List.mem_cons_self) ha
  | y :: a, b, z :: c, d, h, ha, hc => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨h1, h2⟩ := split_unique h (fun hm => ha (List.mem_cons_of_mem _ hm))
      (fun hm => hc (List.mem_cons_of_mem _ hm))
    exact ⟨by rw [h1], h2⟩

theorem parentOf_of_mem_elementChildrenOf {t : Tree} (hwf : WellFormed t) {n p : NodeId}
    (h : n ∈ elementChildrenOf t p) : parentOf t n = some p := by
  simp only [elementChildrenOf, List.mem_filter] at h
  exact (mem_childrenOf_iff hwf n p).mpr h.1

/--
**element の sibling の並びを `n` の位置で分ける。** 前にある element が `pre`、後ろにある
element が `post` で、仕様の `ElementSiblingBefore` はちょうどその所属である。
-/
theorem elementSiblings_split {t : Tree} (hwf : WellFormed t) {n : NodeId}
    (hn : isElementNode t n = true) :
    ∃ pre post, elementSiblings t n = pre ++ n :: post ∧ n ∉ pre ∧ n ∉ post ∧
      (elementSiblings t n).Nodup ∧
      (∀ m, ElementSiblingBefore t m n ↔ m ∈ pre) ∧
      (∀ m, ElementSiblingBefore t n m ↔ m ∈ post) := by
  cases hp : parentOf t n with
  | none =>
    have hno : ∀ m, ¬ ElementSiblingBefore t m n ∧ ¬ ElementSiblingBefore t n m := by
      intro m
      constructor
      · rintro ⟨q, a, b, c, hq⟩
        have : n ∈ elementChildrenOf t q := by rw [hq]; simp
        rw [parentOf_of_mem_elementChildrenOf hwf this] at hp; cases hp
      · rintro ⟨q, a, b, c, hq⟩
        have : n ∈ elementChildrenOf t q := by rw [hq]; simp
        rw [parentOf_of_mem_elementChildrenOf hwf this] at hp; cases hp
    refine ⟨[], [], by simp [elementSiblings, hp], by simp, by simp, by simp [elementSiblings, hp],
      fun m => ⟨fun h => absurd h (hno m).1, by simp⟩,
      fun m => ⟨fun h => absurd h (hno m).2, by simp⟩⟩
  | some p =>
    have hmem := mem_elementChildrenOf hwf hp hn
    have hnd := elementChildrenOf_nodup hwf p
    obtain ⟨pre, post, hsplit, hnotin⟩ := List.eq_append_cons_of_mem hmem
    have hnotpost : n ∉ post := by
      intro h
      rw [hsplit, List.nodup_append] at hnd
      exact (List.nodup_cons.mp hnd.2.1).1 h
    have hsib : elementSiblings t n = elementChildrenOf t p := by simp [elementSiblings, hp]
    refine ⟨pre, post, by rw [hsib, hsplit], hnotin, hnotpost, by rw [hsib]; exact hnd, ?_, ?_⟩
    · intro m
      constructor
      · rintro ⟨q, a, b, c, hq⟩
        have hnq : n ∈ elementChildrenOf t q := by rw [hq]; simp
        have hqp := parentOf_of_mem_elementChildrenOf hwf hnq
        rw [hp] at hqp; cases hqp
        rw [hsplit] at hq
        have hnab : n ∉ a ++ m :: b := by
          intro hm
          have hnd' := hnd
          rw [hsplit, hq, List.nodup_append] at hnd'
          exact hnd'.2.2 n hm n List.mem_cons_self rfl
        have := (split_unique (by simpa using hq) hnotin hnab).1
        rw [this]; simp
      · intro hm
        obtain ⟨a, b, rfl⟩ := List.append_of_mem hm
        exact ⟨p, a, b, post, by simp [hsplit]⟩
    · intro m
      constructor
      · rintro ⟨q, a, b, c, hq⟩
        have hnq : n ∈ elementChildrenOf t q := by rw [hq]; simp
        have hqp := parentOf_of_mem_elementChildrenOf hwf hnq
        rw [hp] at hqp; cases hqp
        rw [hsplit] at hq
        have hq' : pre ++ n :: post = a ++ n :: (b ++ m :: c) := by simpa using hq
        have hna : n ∉ a := by
          intro hm
          have hnd' := hnd
          rw [hsplit, hq', List.nodup_append] at hnd'
          exact hnd'.2.2 n hm n List.mem_cons_self rfl
        have := (split_unique hq' hnotin hna).2
        rw [this]; simp
      · intro hm
        obtain ⟨a, b, rfl⟩ := List.append_of_mem hm
        exact ⟨p, pre, a, b, by simp [hsplit]⟩

/-! ## `:nth-*()` と構造の pseudo-class -/

theorem filter_split_of_mem {p : NodeId → Bool} {pre post : List NodeId} {n : NodeId}
    (hpn : p n = true) :
    (pre ++ n :: post).filter p = pre.filter p ++ n :: post.filter p := by
  simp [List.filter_append, hpn]

/--
**数える対象を `p` で絞った sibling の列での位置の条件は、`NthCount` にちょうど一致する。**
-/
theorem nth_generic {t : Tree} (hwf : WellFormed t) {n : NodeId} (hn : isElementNode t n = true)
    (p : NodeId → Bool) (P : NodeId → Prop) (hp : ∀ m, p m = true ↔ P m) (fromEnd : Bool)
    (ab : AnB) :
    (match indexOfNode (if fromEnd then ((elementSiblings t n).filter p).reverse
        else (elementSiblings t n).filter p) n with
      | none => false
      | some i => anbMatches ab (i + 1)) = true ↔ NthCount t P fromEnd ab n := by
  obtain ⟨pre, post, hs, hnpre, hnpost, hnd, hbefore, hafter⟩ := elementSiblings_split hwf hn
  have hpoolnd : ((elementSiblings t n).filter p).Nodup := hnd.filter p
  refine (nth_index_iff hpoolnd fromEnd).trans ?_
  have hprend : (pre.filter p).Nodup := by
    rw [hs] at hnd; exact (List.nodup_append.mp hnd).1.filter p
  have hpostnd : (post.filter p).Nodup := by
    rw [hs] at hnd; exact (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).2.filter p
  have hmempre : ∀ m, m ∈ pre.filter p ↔ P m ∧ ElementSiblingBefore t m n := by
    intro m; rw [List.mem_filter, hp, hbefore]; exact And.comm
  have hmempost : ∀ m, m ∈ post.filter p ↔ P m ∧ ElementSiblingBefore t n m := by
    intro m; rw [List.mem_filter, hp, hafter]; exact And.comm
  constructor
  · rintro ⟨a, b, hpool, hab⟩
    have hnin : n ∈ (elementSiblings t n).filter p := by rw [hpool]; simp
    have hpn : p n = true := (List.mem_filter.mp hnin).2
    rw [hs, filter_split_of_mem hpn] at hpool
    have hna : n ∉ a := by
      intro h
      have hnd' := hpoolnd
      rw [hs, filter_split_of_mem hpn, hpool, List.nodup_append] at hnd'
      exact hnd'.2.2 n h n List.mem_cons_self rfl
    obtain ⟨rfl, rfl⟩ := split_unique hpool
      (fun h => hnpre (List.mem_filter.mp h).1) hna
    refine ⟨(hp n).mp hpn, ?_⟩
    cases fromEnd with
    | false => exact ⟨pre.filter p, hprend, fun m => by simp only [if_false, Bool.false_eq_true]; exact hmempre m, by simpa using hab⟩
    | true => exact ⟨post.filter p, hpostnd, fun m => by simp only [if_true]; exact hmempost m, by simpa using hab⟩
  · rintro ⟨hPn, others, hond, hmem, hidx⟩
    have hpn : p n = true := (hp n).mpr hPn
    refine ⟨pre.filter p, post.filter p, by rw [hs, filter_split_of_mem hpn], ?_⟩
    cases fromEnd with
    | false =>
      have hperm : others.Perm (pre.filter p) :=
        (List.perm_ext_iff_of_nodup hond hprend).mpr (fun m => by
          rw [hmempre]; simpa using hmem m)
      simpa [hperm.length_eq] using hidx
    | true =>
      have hperm : others.Perm (post.filter p) :=
        (List.perm_ext_iff_of_nodup hond hpostnd).mpr (fun m => by
          rw [hmempost]; simpa using hmem m)
      simpa [hperm.length_eq] using hidx

/-- 絞った sibling の列で先頭・末尾・唯一であることを、前後の element の不在で言う。 -/
theorem structural_generic {t : Tree} (hwf : WellFormed t) {n : NodeId}
    (hn : isElementNode t n = true) (p : NodeId → Bool) (P : NodeId → Prop)
    (hp : ∀ m, p m = true ↔ P m) (hpn : p n = true) :
    (((elementSiblings t n).filter p).head? = some n ↔
        ¬ ∃ m, ElementSiblingBefore t m n ∧ P m) ∧
      (((elementSiblings t n).filter p).getLast? = some n ↔
        ¬ ∃ m, ElementSiblingBefore t n m ∧ P m) ∧
      (((elementSiblings t n).filter p).length = 1 ↔
        (¬ ∃ m, ElementSiblingBefore t m n ∧ P m) ∧ ¬ ∃ m, ElementSiblingBefore t n m ∧ P m) := by
  obtain ⟨pre, post, hs, hnpre, hnpost, hnd, hbefore, hafter⟩ := elementSiblings_split hwf hn
  rw [hs, filter_split_of_mem hpn]
  have hpre : (¬ ∃ m, ElementSiblingBefore t m n ∧ P m) ↔ pre.filter p = [] := by
    rw [List.filter_eq_nil_iff]
    constructor
    · intro h m hm hpm; exact h ⟨m, (hbefore m).mpr hm, (hp m).mp hpm⟩
    · rintro h ⟨m, hm, hPm⟩; exact h m ((hbefore m).mp hm) ((hp m).mpr hPm)
  have hpost : (¬ ∃ m, ElementSiblingBefore t n m ∧ P m) ↔ post.filter p = [] := by
    rw [List.filter_eq_nil_iff]
    constructor
    · intro h m hm hpm; exact h ⟨m, (hafter m).mpr hm, (hp m).mp hpm⟩
    · rintro h ⟨m, hm, hPm⟩; exact h m ((hafter m).mp hm) ((hp m).mpr hPm)
  have hnfpre : n ∉ pre.filter p := fun h => hnpre (List.mem_filter.mp h).1
  have hnfpost : n ∉ post.filter p := fun h => hnpost (List.mem_filter.mp h).1
  rw [hpre, hpost]
  refine ⟨?_, ?_, ?_⟩
  · cases h : pre.filter p with
    | nil => simp
    | cons x xs =>
      simp only [List.cons_append, List.head?_cons, Option.some.injEq, reduceCtorEq, iff_false]
      rintro rfl; exact hnfpre (by rw [h]; simp)
  · rw [List.getLast?_append, List.getLast?_cons]
    cases h : post.filter p with
    | nil => simp
    | cons x xs =>
      have hlast : (x :: xs).getLast? = some ((x :: xs).getLast (by simp)) := List.getLast?_eq_some_getLast _
      have hmem : (x :: xs).getLast (by simp) ∈ post.filter p := by rw [h]; exact List.getLast_mem _
      simp only [hlast, Option.getD_some, Option.some_or, Option.some.injEq, reduceCtorEq, iff_false]
      intro heq; exact hnfpost (heq ▸ hmem)
  · simp only [List.length_append, List.length_cons]
    constructor
    · intro h
      exact ⟨List.length_eq_zero_iff.mp (by omega), List.length_eq_zero_iff.mp (by omega)⟩
    · rintro ⟨h1, h2⟩; simp [h1, h2]

/-! ## class と id -/

theorem attr_eq_of_key_eq : ∀ {l : List Attr}, (l.map Attr.key).Nodup →
    ∀ {a b : Attr}, a ∈ l → b ∈ l → a.key = b.key → a = b
  | [], _, _, _, ha, _, _ => absurd ha (by simp)
  | x :: rest, hnd, a, b, ha, hb, hk => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact absurd ⟨b, hb', hk.symm⟩ hnd.1
    · exact absurd ⟨a, ha', hk⟩ hnd.1
    · exact attr_eq_of_key_eq hnd.2 ha' hb' hk

/-- **attribute の組が一意なら、`plainAttr` は仕様の「その attribute の値」をちょうど返す。** -/
theorem plainAttr_eq_some_iff {d : NodeData} (hkeys : (d.attributes.map Attr.key).Nodup)
    (name v : String) : plainAttr d name = some v ↔ PlainAttrValue d name v := by
  constructor
  · intro h; exact plainAttr_some h
  · rintro ⟨a, ha, hn, hns, hv⟩
    cases hp : plainAttr d name with
    | none => exact absurd ⟨hn, hns⟩ (plainAttr_none hp a ha)
    | some w =>
      obtain ⟨b, hb, hbn, hbns, hbv⟩ := plainAttr_some hp
      have : a = b := attr_eq_of_key_eq hkeys ha hb (by simp [Attr.key, hn, hns, hbn, hbns])
      subst this; rw [← hv, hbv]

theorem splitWsAux_words : ∀ (l acc : List Char), NoWhitespace acc →
    ∀ w ∈ splitWsAux acc l, w ≠ [] ∧ NoWhitespace w
  | [], acc, hacc, w, hw => by
    simp only [splitWsAux] at hw
    split at hw
    · simp at hw
    · next hne =>
      simp only [List.mem_singleton] at hw; subst hw
      refine ⟨by simpa using hne, fun c hc => hacc c (List.mem_reverse.mp hc)⟩
  | c :: rest, acc, hacc, w, hw => by
    simp only [splitWsAux] at hw
    split at hw
    · rcases List.mem_append.mp hw with hw | hw
      · split at hw
        · simp at hw
        · next hne =>
          simp only [List.mem_singleton] at hw; subst hw
          exact ⟨by simpa using hne, fun c hc => hacc c (List.mem_reverse.mp hc)⟩
      · exact splitWsAux_words rest [] (by simp [NoWhitespace]) w hw
    · next hc =>
      refine splitWsAux_words rest (c :: acc) ?_ w hw
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simpa using hc
      · exact hacc x hx

/-- **class selector は、class 属性の値の空白区切りの語にちょうど当たる。** -/
theorem classWord_iff (av v : String) :
    (splitWsAux [] av.toList).any (fun w => w == v.toList) = true ↔ ClassToken av v := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨w, hw, heq⟩
    have heq : w = v.toList := by simpa using heq
    subst heq
    obtain ⟨hne, hnw⟩ := splitWsAux_words _ [] (by simp [NoWhitespace]) _ hw
    exact ⟨hne, hnw, (mem_splitWs_iff av.toList.length av.toList (Nat.le_refl _) _ hne hnw).mp hw⟩
  · rintro ⟨hne, hnw, hword⟩
    exact ⟨v.toList, (mem_splitWs_iff av.toList.length av.toList (Nat.le_refl _) _ hne hnw).mpr hword,
      by simp⟩

theorem inQuirksModeOf_iff (t : Tree) (d : NodeData) :
    inQuirksModeOf t d = true ↔ InQuirksMode t d := by
  unfold inQuirksModeOf InQuirksMode
  cases t.get? d.ownerDocument <;> simp

/-- **quirks mode に合わせた比較は、`ClassIdMatches` にちょうど当たる。** -/
theorem quirksFold_eq_iff (t : Tree) (d : NodeData) (a b : String) :
    (quirksFold (inQuirksModeOf t d) a.toList == quirksFold (inQuirksModeOf t d) b.toList) = true ↔
      ClassIdMatches t d a b := by
  unfold ClassIdMatches
  rw [← inQuirksModeOf_iff]
  cases inQuirksModeOf t d with
  | false => simp [quirksFold, String.toList_inj]
  | true =>
    simp only [quirksFold, if_true, beq_iff_eq, true_and, not_true_eq_false,
      false_and, or_false, asciiLowercase]
    exact ⟨fun h => by rw [h], fun h => by simpa using congrArg String.toList h⟩

/-- **class selector は、空白区切りの語のどれかと quirks mode に合わせて一致する。** -/
theorem classWordIn_iff (t : Tree) (d : NodeData) (av v : String) :
    (splitWsAux [] av.toList).any (fun w =>
        quirksFold (inQuirksModeOf t d) w == quirksFold (inQuirksModeOf t d) v.toList) = true ↔
      ∃ w, ClassToken av w ∧ ClassIdMatches t d w v := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨x, hx, heq⟩
    refine ⟨String.ofList x, (classWord_iff av _).mp ?_, (quirksFold_eq_iff t d _ _).mp ?_⟩
    · exact List.any_eq_true.mpr ⟨x, hx, by simp⟩
    · simpa using heq
  · rintro ⟨w, hw, hm⟩
    obtain ⟨x, hx, hxw⟩ := List.any_eq_true.mp ((classWord_iff av w).mpr hw)
    have hxw : x = w.toList := by simpa using hxw
    subst hxw
    exact ⟨w.toList, hx, (quirksFold_eq_iff t d _ _).mpr hm⟩

/-! ## combinator -/

theorem mem_elementChildren_facts {t : Tree} (hwf : WellFormed t) {n q : NodeId}
    (h : n ∈ elementChildrenOf t q) : isElementNode t n = true ∧ parentOf t n = some q :=
  ⟨(List.mem_filter.mp h).2, parentOf_of_mem_elementChildrenOf hwf h⟩

/-- **combinator の候補は、どの node についても仕様の `Combines` にちょうど一致する。** -/
theorem mem_combCandidates_iff {t : Tree} (hwf : WellFormed t) (comb : Combinator)
    (e n : NodeId) : e ∈ combCandidates t comb n ↔ Combines t comb e n := by
  cases comb with
  | descendant => exact mem_combCandidates_descendant hwf e n
  | child => exact mem_combCandidates_child e n
  | nextSibling =>
    cases hp : parentOf t n with
    | some p =>
      by_cases hn : isElementNode t n = true
      · exact mem_combCandidates_nextSibling hwf hp hn e
      · simp only [combCandidates, hp, hn, Bool.false_eq_true, if_false, List.not_mem_nil,
          false_iff, Combines]
        rintro ⟨q, a, b, hq⟩
        exact hn (mem_elementChildren_facts hwf (show n ∈ elementChildrenOf t q by rw [hq]; simp)).1
    | none =>
      simp only [combCandidates, hp, List.not_mem_nil, false_iff, Combines]
      rintro ⟨q, a, b, hq⟩
      have := (mem_elementChildren_facts hwf (show n ∈ elementChildrenOf t q by rw [hq]; simp)).2
      rw [hp] at this; cases this
  | subsequentSibling =>
    cases hp : parentOf t n with
    | some p =>
      by_cases hn : isElementNode t n = true
      · exact mem_combCandidates_subsequentSibling hwf hp hn e
      · simp only [combCandidates, hp, hn, Bool.false_eq_true, if_false, List.not_mem_nil,
          false_iff, Combines]
        rintro ⟨q, a, b, c, hq⟩
        exact hn (mem_elementChildren_facts hwf (show n ∈ elementChildrenOf t q by rw [hq]; simp)).1
    | none =>
      simp only [combCandidates, hp, List.not_mem_nil, false_iff, Combines]
      rintro ⟨q, a, b, c, hq⟩
      have := (mem_elementChildren_facts hwf (show n ∈ elementChildrenOf t q by rw [hq]; simp)).2
      rw [hp] at this; cases this

/-! ## 全体の一致 -/

theorem filter_const_true (l : List NodeId) : l.filter (fun _ => true) = l :=
  List.filter_eq_self.mpr (by simp)

theorem sameTypeAs_self {t : Tree} {n : NodeId} {d : NodeData} (hd : t.get? n = some d) :
    sameTypeAs t d n = true := by
  simp [sameTypeAs, hd]

/--
**照合の実行関数は、関係 `SelectorListMatches` ほかにちょうど一致する。**

大きさ `k` 以下の selector について、四つの段（simple・compound・complex・list）を同時に示す。
-/
theorem match_iff_bounded {t : Tree} (hwf : WellFormed t)
    (hkeys : ∀ n d, t.get? n = some d → (d.attributes.map Attr.key).Nodup) :
    ∀ k : Nat,
      (∀ ctx : MatchCtx, ctx.tree = t → ∀ (s : Simple) (n : NodeId), sSize s ≤ k →
        (matchSimple ctx s n = true ↔ SimpleMatches ctx s n)) ∧
      (∀ ctx : MatchCtx, ctx.tree = t → ∀ (parts : List Simple) (n : NodeId), cpSize parts ≤ k →
        (matchCompound ctx parts n = true ↔ CompoundMatches ctx parts n)) ∧
      (∀ ctx : MatchCtx, ctx.tree = t → ∀ (c : Complex) (n : NodeId), cxSize c ≤ k →
        (matchComplex ctx c n = true ↔ ComplexMatches ctx c n)) ∧
      (∀ ctx : MatchCtx, ctx.tree = t → ∀ (l : List Complex) (n : NodeId), lSize l ≤ k →
        (matchSelList ctx l n = true ↔ SelectorListMatches ctx l n))
  | 0 => by
    refine ⟨fun _ _ s _ h => absurd h (by have := sSize_pos s; omega),
      fun _ _ p _ h => absurd h (by have := cpSize_pos p; omega),
      fun _ _ c _ h => absurd h (by have := cxSize_pos c; omega),
      fun _ _ l _ h => absurd h (by have := lSize_pos l; omega)⟩
  | k + 1 => by
    obtain ⟨ihS, ihP, ihC, ihL⟩ := match_iff_bounded hwf hkeys k
    refine ⟨?simple, ?compound, ?complex, ?list⟩
    case list =>
      intro ctx hctx l n hl
      rw [matchSelList, SelectorListMatches, List.any_eq_true]
      constructor
      · rintro ⟨c, hc, h⟩
        exact ⟨c, hc, (ihC ctx hctx c.1 n (by have := cxSize_lt_lSize l c.1 c.2; omega)).mp h⟩
      · rintro ⟨c, hc, h⟩
        exact ⟨c, hc, (ihC ctx hctx c.1 n (by have := cxSize_lt_lSize l c.1 c.2; omega)).mpr h⟩
    case compound =>
      intro ctx hctx parts n hp
      rw [matchCompound, CompoundMatches, List.all_eq_true]
      constructor
      · intro h s hs
        exact (ihS ctx hctx s.1 n (by have := sSize_lt_cpSize parts s.1 s.2; omega)).mp (h s hs)
      · intro h s hs
        exact (ihS ctx hctx s.1 n (by have := sSize_lt_cpSize parts s.1 s.2; omega)).mpr (h s hs)
    case complex =>
      intro ctx hctx c n hc
      cases c with
      | one parts =>
        rw [matchComplex, ComplexMatches]
        exact ihP ctx hctx parts n (by simp only [cxSize] at hc; omega)
      | seq parts comb left =>
        simp only [cxSize] at hc
        rw [matchComplex, ComplexMatches, Bool.and_eq_true, List.any_eq_true,
          ihP ctx hctx parts n (by omega)]
        apply and_congr_right
        intro _
        constructor
        · rintro ⟨m, hm, h⟩
          exact ⟨m, (mem_combCandidates_iff (hctx ▸ hwf) comb m n).mp hm,
            (ihC ctx hctx left m (by omega)).mp h⟩
        · rintro ⟨m, hm, h⟩
          exact ⟨m, (mem_combCandidates_iff (hctx ▸ hwf) comb m n).mpr hm,
            (ihC ctx hctx left m (by omega)).mpr h⟩
    case simple =>
      intro ctx hctx s n hs
      have hwf' : WellFormed ctx.tree := hctx ▸ hwf
      have hkeys' : ∀ n d, ctx.tree.get? n = some d → (d.attributes.map Attr.key).Nodup :=
        hctx ▸ hkeys
      cases hget : ctx.tree.get? n with
      | none =>
        rw [matchSimple, hget, SimpleMatches]; simp [hget]
      | some d =>
        by_cases hel : d.kind = NodeKind.element
        · have hn : isElementNode ctx.tree n = true := by simp [isElementNode, kindOf, hget, hel]
          have hne : (d.kind != NodeKind.element) = false := by simp [hel]
          rw [SimpleMatches]
          simp only [hget, Option.some.injEq, exists_eq_left', hel, if_true]
          cases s with
          | typeSel name =>
            rw [matchSimple, hget]; simp only [hne, Bool.false_eq_true, if_false]
            exact typeHolds_iff ctx.tree d name
          | univ => rw [matchSimple, hget]; simp [hne]
          | id v =>
            rw [matchSimple, hget]; simp only [hne, Bool.false_eq_true, if_false]
            cases hpa : plainAttr d "id" with
            | none =>
              simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
              intro av hav; rw [← plainAttr_eq_some_iff (hkeys' n d hget)] at hav
              rw [hpa] at hav; cases hav
            | some av =>
              simp only
              rw [quirksFold_eq_iff]
              constructor
              · intro h; exact ⟨av, (plainAttr_eq_some_iff (hkeys' n d hget) _ _).mp hpa, h⟩
              · rintro ⟨av', hav', h⟩
                rw [← plainAttr_eq_some_iff (hkeys' n d hget), hpa] at hav'
                cases hav'; exact h
          | cls v =>
            rw [matchSimple, hget]; simp only [hne, Bool.false_eq_true, if_false]
            cases hpa : plainAttr d "class" with
            | none =>
              simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
              intro av hav; rw [← plainAttr_eq_some_iff (hkeys' n d hget)] at hav
              rw [hpa] at hav; cases hav
            | some av =>
              simp only
              rw [classWordIn_iff]
              constructor
              · intro h; exact ⟨av, (plainAttr_eq_some_iff (hkeys' n d hget) _ _).mp hpa, h⟩
              · rintro ⟨av', hav', h⟩
                rw [← plainAttr_eq_some_iff (hkeys' n d hget), hpa] at hav'
                cases hav'; exact h
          | attr name anyNs test =>
            rw [matchSimple_attr_iff hget hel]
            cases test <;> rfl
          | root => exact matchSimple_root_iff hget hel
          | empty => exact matchSimple_empty_iff hget hel
          | firstChild =>
            rw [matchSimple, hget]; simp only [hne, Bool.false_eq_true, if_false, beq_iff_eq]
            have := (structural_generic hwf' hn (fun _ => true) (fun _ => True) (by simp) rfl).1
            simpa [filter_const_true] using this
          | lastChild =>
            rw [matchSimple, hget]; simp only [hne, Bool.false_eq_true, if_false, beq_iff_eq]
            have := (structural_generic hwf' hn (fun _ => true) (fun _ => True) (by simp) rfl).2.1
            simpa [filter_const_true] using this
          | onlyChild =>
            rw [matchSimple, hget]; simp only [hne, Bool.false_eq_true, if_false, beq_iff_eq]
            have := (structural_generic hwf' hn (fun _ => true) (fun _ => True) (by simp) rfl).2.2
            simpa [filter_const_true] using this
          | firstOfType =>
            rw [matchSimple, hget]; simp only [hne, Bool.false_eq_true, if_false, beq_iff_eq]
            exact (structural_generic hwf' hn _ _ (sameTypeAs_iff ctx.tree d) (sameTypeAs_self hget)).1
          | lastOfType =>
            rw [matchSimple, hget]; simp only [hne, Bool.false_eq_true, if_false, beq_iff_eq]
            exact (structural_generic hwf' hn _ _ (sameTypeAs_iff ctx.tree d) (sameTypeAs_self hget)).2.1
          | onlyOfType =>
            rw [matchSimple, hget]; simp only [hne, Bool.false_eq_true, if_false, beq_iff_eq]
            exact (structural_generic hwf' hn _ _ (sameTypeAs_iff ctx.tree d) (sameTypeAs_self hget)).2.2
          | nth kind ab ofSel =>
            rw [matchSimple, hget]; simp only [hne, Bool.false_eq_true, if_false]
            have hsize : ∀ l, ofSel = some l → lSize l ≤ k := by
              intro l hl; subst hl; simp only [sSize, oSize] at hs; omega
            have hT := fun fromEnd =>
              nth_generic hwf' hn (fun _ => true) (fun _ => True) (by simp) fromEnd ab
            have hTy := fun fromEnd =>
              nth_generic hwf' hn _ _ (sameTypeAs_iff ctx.tree d) fromEnd ab
            simp only [filter_const_true] at hT
            cases kind <;> cases ofSel
            · exact hT false
            · rename_i l
              exact nth_generic hwf' hn (fun m => matchSelList ctx l m)
                (fun m => SelectorListMatches ctx l m)
                (fun m => ihL ctx hctx l m (hsize l rfl)) false ab
            · exact hT true
            · rename_i l
              exact nth_generic hwf' hn (fun m => matchSelList ctx l m)
                (fun m => SelectorListMatches ctx l m)
                (fun m => ihL ctx hctx l m (hsize l rfl)) true ab
            · exact hTy false
            · exact hTy false
            · exact hTy true
            · exact hTy true
          | isSel l =>
            rw [matchSimple, hget]; simp only [hne, Bool.false_eq_true, if_false]
            exact ihL ctx hctx l n (by simp only [sSize] at hs; omega)
          | whereSel l =>
            rw [matchSimple, hget]; simp only [hne, Bool.false_eq_true, if_false]
            exact ihL ctx hctx l n (by simp only [sSize] at hs; omega)
          | notSel l =>
            rw [matchSimple, hget]; simp only [hne, Bool.false_eq_true, if_false,
              Bool.not_eq_eq_eq_not, Bool.not_true]
            rw [← ihL ctx hctx l n (by simp only [sSize] at hs; omega)]
            simp
          | has l =>
            rw [matchSimple_has_iff hwf' hget hel l]
            constructor
            · rintro ⟨c, hc, h⟩
              exact ⟨c, hc, (ihL { ctx with anchor := some n } hctx l c
                (by simp only [sSize] at hs; omega)).mp h⟩
            · rintro ⟨c, hc, h⟩
              exact ⟨c, hc, (ihL { ctx with anchor := some n } hctx l c
                (by simp only [sSize] at hs; omega)).mpr h⟩
          | scope => rw [matchSimple, hget]; simp [hne]
          | anchor => rw [matchSimple, hget]; simp [hne]
        · have hne : (d.kind != NodeKind.element) = true := by simp [hel]
          rw [matchSimple, hget, SimpleMatches]
          simp only [hne, if_true, hget, Option.some.injEq, exists_eq_left', hel, if_false,
            Bool.and_eq_true, beq_iff_eq]
          cases s <;> simp [isScopeSelector]

/-! ## まとめ -/

/-- **selector list の照合は `SelectorListMatches` にちょうど一致する。** -/
theorem matchSelList_iff_spec {t : Tree} (hwf : WellFormed t) (hav : AttributesValid t)
    {ctx : MatchCtx} (hctx : ctx.tree = t) (l : List Complex) (n : NodeId) :
    matchSelList ctx l n = true ↔ SelectorListMatches ctx l n :=
  (match_iff_bounded hwf hav.keysNodup (lSize l)).2.2.2 ctx hctx l n (Nat.le_refl _)

/-- **complex selector の照合は `ComplexMatches` にちょうど一致する。** -/
theorem matchComplex_iff_spec {t : Tree} (hwf : WellFormed t) (hav : AttributesValid t)
    {ctx : MatchCtx} (hctx : ctx.tree = t) (c : Complex) (n : NodeId) :
    matchComplex ctx c n = true ↔ ComplexMatches ctx c n :=
  (match_iff_bounded hwf hav.keysNodup (cxSize c)).2.2.1 ctx hctx c n (Nat.le_refl _)

/-- **simple selector の照合は `SimpleMatches` にちょうど一致する。** -/
theorem matchSimple_iff_spec {t : Tree} (hwf : WellFormed t) (hav : AttributesValid t)
    {ctx : MatchCtx} (hctx : ctx.tree = t) (s : Simple) (n : NodeId) :
    matchSimple ctx s n = true ↔ SimpleMatches ctx s n :=
  (match_iff_bounded hwf hav.keysNodup (sSize s)).1 ctx hctx s n (Nat.le_refl _)

/--
**`querySelectorAll()` が返すのは、scoping root の descendant である element のうち、
仕様の関係で selector に当たるものである。**

並び（tree order）は `Dom/Properties/Selector.lean` の `matchTree` の側が押さえている。
-/
theorem mem_matchTree_iff_spec {t : Tree} (hwf : WellFormed t) (hav : AttributesValid t)
    {node : NodeId} {d : NodeData} (hn : t.get? node = some d) (sel : SelectorList)
    (e : NodeId) :
    e ∈ matchTree t sel node ↔
      Descendant t e node ∧ isElementNode t e = true ∧
        SelectorListMatches { tree := t, scope := some node } sel e := by
  rw [mem_matchTree_iff hwf hn sel e, matchSelList_iff_spec hwf hav rfl]

end Dom.Spec
