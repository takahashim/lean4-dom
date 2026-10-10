import Dom.Spec.Lookup
import Dom.Attribute.Reflect

/-!
# DOMTokenList の token set を状態に持たなくてよいこと（§7.1）

本文の DOMTokenList は token set を状態に持ち、update steps が class attribute に
ordered set serializer の結果を書き、attribute change steps がそれを ordered set parser で読み直して token set にする。
model は token set を持たず、使うたびに class attribute の値を読み直す（`classTokenSet`）。

二つが同じになるのは、update steps に渡す set を serialize してから parse すると元に戻るときである。
ここでは次を示す。

* `orderedSetParse_serialize`：token が空でなく空白を含まず、重複が無い（`TokenSetOk`）なら、parse は serialize の逆である。
* `tokenSetOk_classTokenSet` ほか：`add`・`remove`・`toggle`・`replace` が update steps に渡す set は、
  token の検査を通ったあとでは、いつも `TokenSetOk` である。

したがって、method のあとで model が class attribute から読み直す token set は、本文が状態として持つ token set と同じである。
-/

namespace Dom.Spec

open Dom Infra

/-- token が空でなく、ASCII whitespace を含まない。 -/
def TokenOk (x : String) : Prop := x.toList ≠ [] ∧ NoWhitespace x.toList

/-- update steps に渡してよい token set：どの token も `TokenOk` で、重複が無い。 -/
def TokenSetOk (l : List String) : Prop := (∀ x ∈ l, TokenOk x) ∧ l.Nodup

/-! ## 列の補題 -/

theorem eraseDups_of_nodup : ∀ {l : List String}, l.Nodup → l.eraseDups = l
  | [], _ => rfl
  | a :: as, h => by
    have h' := List.nodup_cons.mp h
    rw [List.eraseDups_cons]
    have hf : as.filter (fun b => !b == a) = as := by
      rw [List.filter_eq_self]
      intro b hb
      have : b ≠ a := fun he => h'.1 (he ▸ hb)
      simpa using this
    rw [hf, eraseDups_of_nodup h'.2]

theorem nodup_eraseDups : ∀ (n : Nat) (l : List String), l.length ≤ n → l.eraseDups.Nodup
  | _, [], _ => List.nodup_nil
  | 0, _ :: _, h => by simp at h
  | n + 1, a :: as, h => by
    rw [List.eraseDups_cons]
    refine List.nodup_cons.mpr ⟨?_, nodup_eraseDups n _ ?_⟩
    · intro hm
      have := List.mem_eraseDups.mp hm
      simp at this
    · have := List.length_filter_le (fun b => !b == a) as
      simp at h; omega

/-! ## serialize と parse -/

/-- 語を空白一つでつないだもの。 -/
def joinWs : List (List Char) → List Char
  | [] => []
  | [w] => w
  | w :: rest => w ++ ' ' :: joinWs rest

theorem intercalate_toList : ∀ (l : List String),
    (" ".intercalate l).toList = joinWs (l.map String.toList)
  | [] => rfl
  | [a] => by simp [joinWs]
  | a :: b :: l => by
    rw [String.intercalate_cons_cons, String.toList_append, String.toList_append,
      intercalate_toList (b :: l)]
    simp [joinWs]

theorem splitWsAux_joinWs : ∀ (ws : List (List Char)), (∀ w ∈ ws, w ≠ [] ∧ NoWhitespace w) →
    splitWsAux [] (joinWs ws) = ws
  | [], _ => rfl
  | [w], h => by
    have hw := h w (by simp)
    rw [show joinWs [w] = w from rfl, splitWsAux_no_ws w [] hw.2]
    simp [hw.1]
  | w :: v :: rest, h => by
    have hw := h w (by simp)
    rw [show joinWs (w :: v :: rest) = w ++ ' ' :: joinWs (v :: rest) from rfl,
      splitWsAux_split w [] hw.2 ' ' (by decide) _,
      splitWsAux_joinWs (v :: rest) (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    simp [hw.1]

/-- **token set を serialize してから parse すると、元の set に戻る。** -/
theorem orderedSetParse_serialize {l : List String} (h : TokenSetOk l) :
    orderedSetParse (" ".intercalate l) = l := by
  unfold orderedSetParse
  rw [intercalate_toList, splitWsAux_joinWs _ (by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hw
    exact h.1 x hx)]
  rw [List.map_map]
  have : (String.ofList ∘ String.toList) = id := by funext s; simp
  rw [this, List.map_id, eraseDups_of_nodup h.2]

/-! ## method が渡す set -/

/-- parse した token set は `TokenSetOk` である。 -/
theorem tokenSetOk_orderedSetParse (s : String) : TokenSetOk (orderedSetParse s) := by
  refine ⟨?_, nodup_eraseDups _ _ (Nat.le_refl _)⟩
  intro x hx
  have hm := List.mem_eraseDups.mp hx
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hm
  have := splitWsAux_words s.toList [] (by simp [NoWhitespace]) w hw
  exact ⟨by simpa using this.1, by simpa using this.2⟩

theorem tokenSetOk_classTokenSet (d : NodeData) : TokenSetOk (classTokenSet d) :=
  tokenSetOk_orderedSetParse _

theorem validateToken_eq_none_iff (x : String) : validateToken x = none ↔ TokenOk x := by
  unfold validateToken TokenOk NoWhitespace
  by_cases he : x.isEmpty = true
  · have : x.toList = [] := by simpa [String.isEmpty_iff] using he
    simp [he, this]
  · have hne : x.toList ≠ [] := by
      intro h; apply he; simp [String.isEmpty_iff, ← String.toList_inj, h]
    simp only [he, Bool.false_eq_true, if_false, hne, ne_eq, not_false_eq_true, true_and]
    split
    · next h =>
      simp only [reduceCtorEq, false_iff]
      intro hall
      obtain ⟨c, hc, hw⟩ := List.any_eq_true.mp h
      rw [hall c hc] at hw
      cases hw
    · next h =>
      simp only [true_iff]
      intro c hc
      have := List.any_eq_false.mp (by simpa using h) c hc
      simpa using this

theorem validateTokens_eq_none_iff : ∀ (l : List String), validateTokens l = none ↔ ∀ x ∈ l, TokenOk x
  | [] => by simp [validateTokens]
  | x :: xs => by
    unfold validateTokens
    cases hx : validateToken x with
    | some e =>
      simp only [Option.orElse_some, reduceCtorEq, false_iff]
      intro hall
      rw [(validateToken_eq_none_iff x).mpr (hall x (by simp))] at hx
      cases hx
    | none =>
      simp only [Option.orElse_none, validateTokens_eq_none_iff xs, List.mem_cons, forall_eq_or_imp]
      exact ⟨fun h => ⟨(validateToken_eq_none_iff x).mp hx, h⟩, fun h => h.2⟩

theorem tokenSetOk_orderedSetAppend {l : List String} {x : String} (hl : TokenSetOk l)
    (hx : TokenOk x) : TokenSetOk (orderedSetAppend l x) := by
  unfold orderedSetAppend
  split
  · exact hl
  · next hc =>
    have hxl : x ∉ l := by simpa using hc
    refine ⟨fun y hy => ?_, List.nodup_append.mpr ⟨hl.2, by simp, fun a ha b hb => ?_⟩⟩
    · rcases List.mem_append.mp hy with hy | hy
      · exact hl.1 y hy
      · simp at hy; subst hy; exact hx
    · simp at hb; subst hb; exact fun he => hxl (he ▸ ha)

/-- `add(tokens...)` が update steps に渡す set。 -/
theorem tokenSetOk_add : ∀ (tokens : List String) {l : List String}, TokenSetOk l →
    (∀ x ∈ tokens, TokenOk x) → TokenSetOk (tokens.foldl orderedSetAppend l)
  | [], _, hl, _ => hl
  | x :: xs, _, hl, hx => tokenSetOk_add xs (tokenSetOk_orderedSetAppend hl (hx x (by simp)))
      (fun y hy => hx y (by simp [hy]))

/-- `remove(tokens...)`・`toggle()` の削除が update steps に渡す set。 -/
theorem tokenSetOk_filter {l : List String} (hl : TokenSetOk l) (p : String → Bool) :
    TokenSetOk (l.filter p) :=
  ⟨fun x hx => hl.1 x ((List.mem_filter.mp hx).1), hl.2.filter p⟩

/-- `toggle()` の追加が update steps に渡す set（token はまだ set に無い）。 -/
theorem tokenSetOk_append_new {l : List String} {x : String} (hl : TokenSetOk l) (hx : TokenOk x)
    (hxl : x ∉ l) : TokenSetOk (l ++ [x]) := by
  have := tokenSetOk_orderedSetAppend hl hx
  unfold orderedSetAppend at this
  rwa [if_neg (by simpa using hxl)] at this

theorem mem_orderedSetReplace {item r : String} :
    ∀ {l : List String} {y : String}, y ∈ orderedSetReplace item r l → y ∈ l ∨ y = r
  | [], _, h => by simp [orderedSetReplace] at h
  | x :: xs, y, h => by
    unfold orderedSetReplace at h
    split at h
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr rfl
      · exact Or.inl (List.mem_cons_of_mem _ (List.mem_filter.mp h).1)
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl (by simp)
      · rcases mem_orderedSetReplace h with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr h

/-- `replace(token, newToken)` が update steps に渡す set。 -/
theorem tokenSetOk_replace {item r : String} (hr : TokenOk r) :
    ∀ {l : List String}, TokenSetOk l → TokenSetOk (orderedSetReplace item r l)
  | [], _ => ⟨by simp [orderedSetReplace], by simp [orderedSetReplace]⟩
  | x :: xs, hl => by
    have hnd := List.nodup_cons.mp hl.2
    have hxs : TokenSetOk xs := ⟨fun y hy => hl.1 y (by simp [hy]), hnd.2⟩
    unfold orderedSetReplace
    split
    · refine ⟨?_, List.nodup_cons.mpr ⟨?_, hxs.2.filter _⟩⟩
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hr
        · exact hxs.1 y ((List.mem_filter.mp hy).1)
      · intro hm
        have := (List.mem_filter.mp hm).2
        simp at this
    · next hc =>
      have hrec := tokenSetOk_replace (item := item) hr hxs
      refine ⟨?_, List.nodup_cons.mpr ⟨?_, hrec.2⟩⟩
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hl.1 _ (by simp)
        · exact hrec.1 y hy
      · intro hm
        rcases mem_orderedSetReplace hm with h | h
        · exact hnd.1 h
        · exact hc (by simp [h])

end Dom.Spec
