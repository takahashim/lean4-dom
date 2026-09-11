import Url.Api
import Url.Urlencoded
import Infra.Utf16

/-!
# `URLSearchParams`

WHATWG URL Standard §6.2 の `URLSearchParams`。

中身は name/value の組の list で、操作はすべてその list の上の純関数である。
parse と serialize は §5（`Url/Urlencoded.lean`）のものをそのまま使う。

## object identity を持たない

仕様の `URLSearchParams` は URL object を指していて、`append` などが
その URL の query を書き換える。この model は object identity を持たないので、
その連動は `Url.withParams`（list を URL に書き戻す）として外に出してある。
-/

namespace Url

open Infra

/-- §6.2 の `URLSearchParams` が持つ list。 -/
abbrev Params := List (String × String)

namespace Params

/-- §6.2 `get`。最初に名前が一致する組の値。 -/
def get : Params → String → Option String
  | [], _ => none
  | p :: rest, name => if p.1 == name then some p.2 else get rest name

/-- §6.2 `getAll`。名前が一致する組の値を list の順に並べたもの。 -/
def getAll : Params → String → List String
  | [], _ => []
  | p :: rest, name => if p.1 == name then p.2 :: getAll rest name else getAll rest name

/-- §6.2 `has`。 -/
def has : Params → String → Bool
  | [], _ => false
  | p :: rest, name => (p.1 == name) || has rest name

/-- §6.2 `has`（値も指定する形）。 -/
def hasValue : Params → String → String → Bool
  | [], _, _ => false
  | p :: rest, name, value => (p.1 == name && p.2 == value) || hasValue rest name value

/-- §6.2 `size`。 -/
def size (l : Params) : Nat := l.length

/-- §6.2 `append`。末尾に足す。 -/
def append (l : Params) (name value : String) : Params := l ++ [(name, value)]

/-- §6.2 `delete`。名前が一致する組をすべて落とす。 -/
def delete : Params → String → Params
  | [], _ => []
  | p :: rest, name => if p.1 == name then delete rest name else p :: delete rest name

/-- §6.2 `delete`（値も指定する形）。 -/
def deleteValue : Params → String → String → Params
  | [], _, _ => []
  | p :: rest, name, value =>
    if p.1 == name && p.2 == value then deleteValue rest name value
    else p :: deleteValue rest name value

/-- `set` の本体。最初の一致だけ値を差し替え、それ以降の一致は落とす。 -/
def setFirst (name value : String) : Params → Params
  | [] => []
  | p :: rest =>
    if p.1 == name then (name, value) :: delete rest name
    else p :: setFirst name value rest

/-- §6.2 `set`。名前が無ければ末尾に足す。 -/
def set (l : Params) (name value : String) : Params :=
  if has l name then setFirst name value l else append l name value

/--
`sort` の挿入。

名前が自分以上の最初の要素の**手前**に入れる。後から来たものが前に出ないので、
名前が等しい組どうしの相対順序が変わらない。
-/
def insert (p : String × String) : Params → Params
  | [] => [p]
  | q :: rest => if strLt q.1 p.1 then q :: insert p rest else p :: q :: rest

/--
§6.2 `sort`。名前の **code unit 順**で並べ替える。

code point 順ではない。BMP の外の code point は surrogate pair になるので、
U+E000 以上の BMP 文字より前に来る（`Infra/Utf16.lean`）。
名前が等しい組どうしの相対順序は変えない。
-/
def sort : Params → Params
  | [] => []
  | p :: rest => insert p (sort rest)

/-- §6.2 stringifier。 -/
def serialize (l : Params) : String := serializeUrlencoded l

/-- §6.2 constructor の文字列版。先頭の `?` は一つだけ落とす。 -/
def ofString (s : String) : Params :=
  parseUrlencodedString (String.ofList (match s.toList with | '?' :: t => t | l => l))

end Params

/-- §6.1 `searchParams`。URL の query を list として読む。 -/
def Url.searchParams (u : Url) : Params := parseUrlencodedString (u.query.getD "")

/--
§6.2「update a URLSearchParams object」。

list を serialize して URL の query に書き戻す。空になったら query は null にして、
opaque path の末尾の空白を落とす（`search` setter に空文字列を入れるのと同じ扱い）。
-/
def Url.withParams (u : Url) (l : Params) : Url :=
  if (Params.serialize l).isEmpty then stripTrailingSpaces { u with query := none }
  else { u with query := some (Params.serialize l) }

/-! ## 性質 -/

namespace Params

/-- `get` は `getAll` の先頭である。 -/
theorem get_eq_head : ∀ (l : Params) (name : String), get l name = (getAll l name).head?
  | [], _ => rfl
  | p :: rest, name => by
    rw [get, getAll]
    split <;> simp [get_eq_head rest name]

/-- `has` は「`getAll` が空でない」と同じ。 -/
theorem has_eq : ∀ (l : Params) (name : String), has l name = !(getAll l name).isEmpty
  | [], _ => rfl
  | p :: rest, name => by
    rw [has, getAll]
    split <;> simp_all [has_eq rest name]

/-- 名前を落とした後にその名前は残らない。 -/
theorem getAll_delete : ∀ (l : Params) (name : String), getAll (delete l name) name = []
  | [], _ => rfl
  | p :: rest, name => by
    rw [delete]
    split
    · exact getAll_delete rest name
    · next h => rw [getAll, if_neg h]; exact getAll_delete rest name

/-- 末尾に足すと、その名前の値が一つ増える。 -/
theorem getAll_snoc : ∀ (l : Params) (name value n : String),
    getAll (l ++ [(name, value)]) n = getAll l n ++ (if name == n then [value] else [])
  | [], name, value, n => by
    rw [List.nil_append, getAll, getAll]
    split <;> simp_all [getAll]
  | p :: rest, name, value, n => by
    rw [List.cons_append, getAll, getAll, getAll_snoc rest name value n]
    split <;> simp

theorem getAll_append (l : Params) (name value n : String) :
    getAll (append l name value) n = getAll l n ++ (if name == n then [value] else []) :=
  getAll_snoc l name value n

theorem getAll_setFirst : ∀ (l : Params) (name value : String), has l name = true →
    getAll (setFirst name value l) name = [value]
  | [], name, _, h => by rw [has] at h; exact absurd h (by simp)
  | p :: rest, name, value, h => by
    rw [setFirst]
    split
    · rw [getAll, if_pos (by simp), getAll_delete]
    · next hp =>
      rw [getAll, if_neg hp]
      refine getAll_setFirst rest name value ?_
      rw [has] at h
      simpa [hp] using h

/-- `set` した名前の値はちょうど一つになる。 -/
theorem getAll_set (l : Params) (name value : String) :
    getAll (set l name value) name = [value] := by
  rw [set]
  split
  · next h => exact getAll_setFirst l name value h
  · next h =>
    have h' : has l name = false := by simpa using h
    have he := has_eq l name
    rw [h'] at he
    have hempty : getAll l name = [] := by
      cases hg : getAll l name with
      | nil => rfl
      | cons a t => rw [hg] at he; simp at he
    rw [getAll_append, hempty]
    simp

/-- 挿入は長さを 1 増やす。 -/
theorem length_insert (p : String × String) : ∀ s : Params, (insert p s).length = s.length + 1
  | [] => rfl
  | q :: rest => by
    rw [insert]
    split
    · simp [length_insert p rest]
    · simp

/-- `sort` は組を落とさない。 -/
theorem length_sort : ∀ l : Params, (sort l).length = l.length
  | [] => rfl
  | p :: rest => by rw [sort, length_insert, length_sort rest]; simp

/-- 名前の違う隣り合う二つは、入れ替えても名前ごとの値の並びを変えない。 -/
theorem getAll_swap (a b : String × String) (rest : Params) (name : String) (h : a.1 ≠ b.1) :
    getAll (a :: b :: rest) name = getAll (b :: a :: rest) name := by
  rw [getAll, getAll, getAll, getAll]
  by_cases ha : (a.1 == name) = true <;> by_cases hb : (b.1 == name) = true
  · simp only [beq_iff_eq] at ha hb
    exact absurd (ha.trans hb.symm) h
  · simp [ha, hb]
  · simp [ha, hb]
  · simp [ha, hb]

/-- 挿入しても、名前ごとに見た値の並びは「先頭に足した」ものと同じ。 -/
theorem getAll_insert (p : String × String) : ∀ (s : Params) (name : String),
    getAll (insert p s) name = getAll (p :: s) name
  | [], _ => rfl
  | q :: rest, name => by
    rw [insert]
    split
    · next h =>
      show getAll (q :: insert p rest) name = getAll (p :: q :: rest) name
      rw [getAll, getAll_insert p rest name]
      exact getAll_swap q p rest name (ne_of_strLt h)
    · rfl

/--
**`sort` は安定である。**

名前ごとに見ると値の並びが変わらない。仕様の
「名前が等しい組どうしの相対順序を保つ」がこれである。
-/
theorem getAll_sort : ∀ (l : Params) (name : String), getAll (sort l) name = getAll l name
  | [], _ => rfl
  | p :: rest, name => by
    show getAll (insert p (sort rest)) name = _
    rw [getAll_insert, getAll, getAll, getAll_sort rest name]

end Params

end Url
