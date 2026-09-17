import Dom.Util.List

/-!
# UTF-16 の code unit

WebIDL の `DOMString` は **16-bit code unit の列** で、DOM の offset はすべてその
code unit の index である（`CharacterData.length`、CharacterData の offset と count、
CharacterData node を指す Range の boundary point）。

Lean の `String` は `Char`（surrogate を除いた Unicode scalar value）の列なので、
* 長さは code unit で数え直せるが、
* surrogate pair の **途中で切った結果**（lone surrogate を含む列）は表せない。

そこで本 model は「UTF-16 として正しく動く範囲を明示した部分モデル」にする。
長さと offset は code unit で数え、切断は scalar 境界でだけ定義する。
境界でない切断を求められた操作は `DOMException.outsideModel` を返す。
これは **仕様の例外ではなく model の対象外を表す印** であり、
差分テストはその step 以降を比較しない（roadmap §13.1）。

boundary point が pair の途中を指すこと自体は扱える。
仕様の boundary point は offset が node の長さ以下であることしか要求しておらず、
scalar 境界であることは求めていない。数値として持ち回るだけなら文字列を切らないので、
この model でもそのまま表せる。
-/

namespace Dom.Utf16

/-- 一つの code point が占める UTF-16 code unit 数。BMP なら 1、それ以外は surrogate pair で 2。 -/
def unitsOf (c : Char) : Nat := if c.toNat ≥ 0x10000 then 2 else 1

theorem unitsOf_pos (c : Char) : 0 < unitsOf c := by unfold unitsOf; split <;> omega

/-- `List Char` の UTF-16 code unit 数。 -/
def lengthOfList : List Char → Nat
  | [] => 0
  | c :: rest => unitsOf c + lengthOfList rest

/-- `String` の UTF-16 code unit 数。仕様の `CharacterData.length` はこれである。 -/
def length (s : String) : Nat := lengthOfList s.toList

@[simp] theorem lengthOfList_nil : lengthOfList [] = 0 := rfl

@[simp] theorem lengthOfList_cons (c : Char) (l : List Char) :
    lengthOfList (c :: l) = unitsOf c + lengthOfList l := rfl

theorem lengthOfList_append : ∀ (a b : List Char),
    lengthOfList (a ++ b) = lengthOfList a + lengthOfList b
  | [], _ => by simp
  | c :: a, b => by
    show unitsOf c + lengthOfList (a ++ b) = (unitsOf c + lengthOfList a) + lengthOfList b
    rw [lengthOfList_append a b]; omega

/--
先頭から code unit `n` 個ぶんで分ける。

`n` が surrogate pair の途中に落ちるか、文字が尽きるなら `none`。
`none` は「model の対象外」であって、仕様がその切り出しを禁じているわけではない。
-/
def splitAt? : List Char → Nat → Option (List Char × List Char)
  | l, 0 => some ([], l)
  | [], _ + 1 => none
  | c :: rest, n + 1 =>
    if n + 1 < unitsOf c then none
    else (splitAt? rest (n + 1 - unitsOf c)).map fun p => (c :: p.1, p.2)

/--
逆向き。**scalar 境界で切れる分け方があるなら、`splitAt?` はそれを返す。**

`DataSpliced`（`Dom/Spec/ReplaceData.lean`）のように「そう切れる」という関係から
実行関数の成功を取り出すときに使う。
-/
theorem splitAt?_of_split : ∀ (a b : List Char), splitAt? (a ++ b) (lengthOfList a) = some (a, b)
  | [], b => by simp [splitAt?]
  | c :: a, b => by
    have hpos := unitsOf_pos c
    obtain ⟨m, hm⟩ : ∃ m, unitsOf c + lengthOfList a = m + 1 := by
      exact ⟨unitsOf c + lengthOfList a - 1, by omega⟩
    show splitAt? (c :: (a ++ b)) (unitsOf c + lengthOfList a) = _
    rw [hm]
    simp only [splitAt?]
    rw [if_neg (by omega)]
    rw [show m + 1 - unitsOf c = lengthOfList a from by omega]
    rw [splitAt?_of_split a b]
    rfl

/-- 分けられたなら、繋ぎ直すと元に戻り、前半の長さはちょうど `n` である。 -/
theorem splitAt?_spec : ∀ {l : List Char} {n : Nat} {a b : List Char},
    splitAt? l n = some (a, b) → a ++ b = l ∧ lengthOfList a = n
  | l, 0, a, b, h => by
    simp only [splitAt?, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1, ← h.2]; exact ⟨rfl, rfl⟩
  | [], _ + 1, _, _, h => by simp [splitAt?] at h
  | c :: rest, n + 1, a, b, h => by
    simp only [splitAt?] at h
    split at h
    · simp at h
    · next hge =>
      obtain ⟨p, hp, hab⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨h1, h2⟩ := splitAt?_spec hp
      simp only [Prod.mk.injEq] at hab
      rw [← hab.1, ← hab.2]
      refine ⟨by simp [h1], ?_⟩
      show unitsOf c + lengthOfList p.1 = n + 1
      rw [h2]
      omega

/-- 分けられたなら、`n` は全体の長さ以下である。 -/
theorem splitAt?_le {l : List Char} {n : Nat} {a b : List Char}
    (h : splitAt? l n = some (a, b)) : n + lengthOfList b = lengthOfList l := by
  obtain ⟨h1, h2⟩ := splitAt?_spec h
  rw [← h1, lengthOfList_append, h2]

/-- BMP だけの列では、code unit 数は code point 数と一致する。 -/
theorem lengthOfList_eq_length_of_bmp : ∀ {l : List Char},
    (∀ c ∈ l, c.toNat < 0x10000) → lengthOfList l = l.length
  | [], _ => rfl
  | c :: rest, h => by
    have hc : unitsOf c = 1 := by
      unfold unitsOf
      rw [if_neg (by have := h c List.mem_cons_self; omega)]
    show unitsOf c + lengthOfList rest = rest.length + 1
    rw [hc, lengthOfList_eq_length_of_bmp (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    omega

end Dom.Utf16
