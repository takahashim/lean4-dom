import Url.StrictValid

/-!
# origin の契約（§4.7）

`origin`（`Url/Parser.lean`）は scheme で四つに分かれる。

* `ftp` / `http` / `https` / `ws` / `wss`：scheme・host・port の tuple origin。
* `blob`：path を URL として読み直し、それが `http` / `https` ならその origin。
* `file`：実装依存の opaque origin（model は opaque にする）。
* それ以外：opaque origin。

`Url/Parser.lean` には「tuple を返すならその成分は URL のもの」（`origin_of_special`）までしか無い。
**parse の結果なら tuple が必ず返る**ことは、§4.1 の「special な URL の host は null でない」
（`StrictConds.specialHasHost`）から出る。それをここで示す。
`blob` の枝は、読み直した URL の origin にちょうど一致する。
-/

namespace Url

/-- tuple origin を持つ scheme。§4.7 の最初の分岐。 -/
def tupleScheme (s : String) : Prop :=
  s = "ftp" ∨ s = "http" ∨ s = "https" ∨ s = "ws" ∨ s = "wss"

theorem tupleScheme_special {s : String} (h : tupleScheme s) : isSpecialScheme s = true := by
  rcases h with h | h | h | h | h <;> subst h <;> decide

/--
**§4.1 を満たす URL の scheme が tuple を持つものなら、origin は tuple である。**
その成分は URL の scheme と host と port である。
-/
theorem origin_tuple_of_strict {t : List Char → Option String} {u : Url} (hs : StrictUrl u)
    (ht : tupleScheme u.scheme) :
    ∃ h, u.host = some h ∧ origin u t = some (u.scheme, h, u.port) := by
  have hh := hs.specialHasHost (tupleScheme_special ht)
  obtain ⟨h, hh⟩ := Option.isSome_iff_exists.mp hh
  refine ⟨h, hh, ?_⟩
  unfold origin
  rw [if_pos (by rcases ht with e | e | e | e | e <;> simp [e]), hh]

/-- **parse の結果の special URL（`file` を除く）は、必ず tuple origin を持つ。** -/
theorem parseUrl_origin_tuple {t : List Char → Option String} (htok : ToAsciiOk t)
    {input : String} {base : Option String} {u : Url} (h : parseUrl input base t = some u)
    (ht : tupleScheme u.scheme) :
    ∃ hst, u.host = some hst ∧ origin u t = some (u.scheme, hst, u.port) :=
  origin_tuple_of_strict (parseUrl_strict htok h) ht

/--
**`blob` URL の origin は、path を読み直した URL の origin である**（読み直した scheme が `http` か `https` のとき）。
-/
theorem origin_blob {t : List Char → Option String} {u p' : Url} {p : String}
    (hs : u.scheme = "blob") (hp : u.path = .opaque p) (hr : basicUrlParse p none t = some p')
    (hsc : p'.scheme = "http" ∨ p'.scheme = "https") :
    origin u t = origin p' t := by
  have hn : ¬(u.scheme == "ftp" || u.scheme == "http" || u.scheme == "https" ||
      u.scheme == "ws" || u.scheme == "wss") = true := by rw [hs]; decide
  conv => lhs; unfold origin
  rw [if_neg hn, if_pos (by rw [hs]; rfl), hp]
  simp only [hr]
  rw [if_pos (by rcases hsc with e | e <;> simp [e])]
  conv => rhs; unfold origin
  rw [if_pos (by rcases hsc with e | e <;> simp [e])]

/-- 読み直した URL が `http` でも `https` でもなければ、`blob` の origin は opaque である。 -/
theorem origin_blob_other {t : List Char → Option String} {u p' : Url} {p : String}
    (hs : u.scheme = "blob") (hp : u.path = .opaque p) (hr : basicUrlParse p none t = some p')
    (hsc : p'.scheme ≠ "http" ∧ p'.scheme ≠ "https") : origin u t = none := by
  have hn : ¬(u.scheme == "ftp" || u.scheme == "http" || u.scheme == "https" ||
      u.scheme == "ws" || u.scheme == "wss") = true := by rw [hs]; decide
  unfold origin
  rw [if_neg hn, if_pos (by rw [hs]; rfl), hp]
  simp only [hr]
  rw [if_neg (by simp [hsc.1, hsc.2])]

/-- path を読み直せなければ、`blob` の origin は opaque である。 -/
theorem origin_blob_failure {t : List Char → Option String} {u : Url} {p : String}
    (hs : u.scheme = "blob") (hp : u.path = .opaque p) (hr : basicUrlParse p none t = none) :
    origin u t = none := by
  have hn : ¬(u.scheme == "ftp" || u.scheme == "http" || u.scheme == "https" ||
      u.scheme == "ws" || u.scheme == "wss") = true := by rw [hs]; decide
  unfold origin
  rw [if_neg hn, if_pos (by rw [hs]; rfl), hp]
  simp only [hr]

/--
**`blob:` の中身が `http(s)` URL として読めるなら、origin は必ず tuple である。**

読み直した結果も parse の結果なので、§4.1 によって host を持つ。
-/
theorem origin_blob_tuple {t : List Char → Option String} (htok : ToAsciiOk t)
    {u p' : Url} {p : String}
    (hs : u.scheme = "blob") (hp : u.path = .opaque p) (hr : basicUrlParse p none t = some p')
    (hsc : p'.scheme = "http" ∨ p'.scheme = "https") :
    ∃ h, p'.host = some h ∧ origin u t = some (p'.scheme, h, p'.port) := by
  rw [origin_blob hs hp hr hsc]
  have hstrict := basicUrlParse_strict htok (fun _ h => absurd h (by simp))
    (fun _ h => absurd h (by simp)) hr
  exact origin_tuple_of_strict hstrict (by rcases hsc with e | e <;> simp [tupleScheme, e])

end Url
