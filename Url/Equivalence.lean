import Url.ParseImage

/-!
# URL equivalence と `URL` の static method（§4.5、§6.1）

§4.5 の「URL A equals URL B」は、二つを serialize して文字列として比べる。
record を成分ごとに比べるのではない。

serializer は record の上で単射ではない（`ValidUrl` だけを満たす record なら、
`Url/Behavior.lean` の三例のように別の record が同じ文字列になる）。
それでも parse の像（`ValidUrl ∧ canonicalUrl`）の上では単射で、
**parse の結果どうしなら「equals」は record の等しさと一致する**（`equals_iff_eq`）。
証明は往復（`roundtrip_canonical_of`）から出る。同じ文字列を parse し直すと、両方に戻るからである。

exclude fragments を付けたときは、fragment を null にした record の等しさと一致する
（`equals_excludeFragments_iff`）。

§4.5 の「URL path equals」は、path を serialize せずに比べる。
本文の注記のとおり、`web+demo:` の path（空の opaque path）と `web+demo://host` の path
（空の列）は同じ文字列に serialize されるが、等しくない。
-/

namespace Url

/-- §4.5「URL A equals URL B」。`excludeFragments` は既定で false。 -/
def Url.equals (a b : Url) (excludeFragments : Bool := false) : Bool :=
  urlSerializer a excludeFragments == urlSerializer b excludeFragments

/--
§4.5「URL path A equals URL path B」。

step 1：どちらかが opaque path（文字列）なら、文字列として等しいか。列と文字列は等しくない。
step 2-4：どちらも列なら、長さが同じで各 segment が等しいか。
-/
def Path.equals : Path → Path → Bool
  | .opaque a, .opaque b => a == b
  | .opaque _, .list _ => false
  | .list _, .opaque _ => false
  | .list a, .list b => a.length == b.length && (List.zip a b).all fun (x, y) => x == y

/-- §6.1 API URL parser。base を parse し、失敗したら失敗、そうでなければ base に対して parse する。 -/
def apiUrlParser (input : String) (base : Option String := none)
    (toAscii : List Char → Option String := asciiDomainToASCII) : Option Url :=
  parseUrl input base toAscii

/-- §6.1 `URL.canParse(url, base)`。 -/
def canParse (input : String) (base : Option String := none)
    (toAscii : List Char → Option String := asciiDomainToASCII) : Bool :=
  (apiUrlParser input base toAscii).isSome

/-- §6.1 `URL.prototype.toJSON()`。serialize した文字列で、`href` getter と同じである。 -/
def Url.toJSON (u : Url) : String := urlSerializer u

/-! ## API URL parser と static method -/

/-- **API URL parser は base の失敗を伝える。** base が parse できなければ何を渡しても失敗する。 -/
theorem apiUrlParser_base_failure {toAscii : List Char → Option String} {b : String}
    (hb : basicUrlParse b none toAscii = none) (input : String) :
    apiUrlParser input (some b) toAscii = none := by
  simp [apiUrlParser, parseUrl, hb]

/-- base を parse した record に対して basic URL parser を走らせたものである。 -/
theorem apiUrlParser_base {toAscii : List Char → Option String} {b : String} {bu : Url}
    (hb : basicUrlParse b none toAscii = some bu) (input : String) :
    apiUrlParser input (some b) toAscii = basicUrlParse input (some bu) toAscii := by
  simp [apiUrlParser, parseUrl, hb]

/-- `canParse` は API URL parser が成功するかどうかである。 -/
theorem canParse_iff {toAscii : List Char → Option String} {input : String}
    {base : Option String} :
    canParse input base toAscii = true ↔ ∃ u, apiUrlParser input base toAscii = some u := by
  simp [canParse, Option.isSome_iff_exists]

theorem toJSON_eq_href (u : Url) : u.toJSON = u.href := rfl

/-! ## path equality -/

/-- **path equality は record の等しさそのものである。** 列と文字列が混ざれば等しくない。 -/
theorem Path.equals_iff : ∀ (a b : Path), a.equals b = true ↔ a = b
  | .opaque a, .opaque b => by simp [Path.equals]
  | .opaque _, .list _ => by simp [Path.equals]
  | .list _, .opaque _ => by simp [Path.equals]
  | .list a, .list b => by
    simp only [Path.equals, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Path.list.injEq]
    constructor
    · rintro ⟨hl, hz⟩
      apply List.ext_getElem hl
      intro i h1 h2
      have hm : (a[i], b[i]) ∈ List.zip a b := by
        rw [List.mem_iff_getElem]
        exact ⟨i, by simp; omega, by simp⟩
      simpa using hz _ hm
    · rintro rfl
      refine ⟨rfl, ?_⟩
      intro p hp
      obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hp
      simp at he
      rw [← he]

/-- **path を比べるのに serialize してはいけない**（§4.5 の注記）。空の opaque path と空の列は同じ文字列になる。 -/
example : pathSerializer (.opaque "") = pathSerializer (.list []) ∧
    (Path.opaque "").equals (.list []) = false := by decide

/-! ## path starts with -/

/--
§4.5「URL path A starts with URL path B」。

step 1：どちらかが opaque path（文字列）なら false。
step 2：B の長さが A の長さより大きければ false。
step 3-4：B の各添字で A と B の segment が等しいか。
-/
def Path.startsWith : Path → Path → Bool
  | .list a, .list b => decide (b.length ≤ a.length) && (List.zip a b).all fun (x, y) => x == y
  | _, _ => false

theorem startsWith_list_iff : ∀ (a b : List String),
    (decide (b.length ≤ a.length) && (List.zip a b).all fun (x, y) => x == y) = true ↔ b <+: a
  | a, [] => by simp
  | [], _ :: _ => by simp
  | x :: a, y :: b => by
    have ih := startsWith_list_iff a b
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ih
    simp only [List.length_cons, Nat.add_le_add_iff_right, List.zip_cons_cons, List.all_cons,
      Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.cons_prefix_cons]
    constructor
    · rintro ⟨hl, hxy, hz⟩; exact ⟨hxy.symm, ih.mp ⟨hl, hz⟩⟩
    · rintro ⟨hxy, hp⟩; exact ⟨(ih.mpr hp).1, hxy.symm, (ih.mpr hp).2⟩

/-- **path starts with は、どちらも列で B が A の先頭の部分列であることである。** -/
theorem Path.startsWith_iff (A B : Path) :
    A.startsWith B = true ↔ ∃ a b, A = .list a ∧ B = .list b ∧ b <+: a := by
  cases A with
  | «opaque» => cases B <;> simp [Path.startsWith]
  | list a =>
    cases B with
    | «opaque» => simp [Path.startsWith]
    | list b =>
      rw [show (Path.list a).startsWith (.list b)
          = (decide (b.length ≤ a.length) && (List.zip a b).all fun (x, y) => x == y) from rfl,
        startsWith_list_iff]
      simp

theorem Path.startsWith_refl (a : List String) : (Path.list a).startsWith (.list a) = true :=
  (Path.startsWith_iff _ _).mpr ⟨a, a, rfl, rfl, List.prefix_refl a⟩

theorem Path.startsWith_trans {A B C : Path} (h1 : A.startsWith B = true)
    (h2 : B.startsWith C = true) : A.startsWith C = true := by
  obtain ⟨a, b, rfl, rfl, hab⟩ := (Path.startsWith_iff _ _).mp h1
  obtain ⟨b', c, hb, rfl, hbc⟩ := (Path.startsWith_iff _ _).mp h2
  cases hb
  exact (Path.startsWith_iff _ _).mpr ⟨a, c, rfl, rfl, hbc.trans hab⟩

/-- 互いに starts with なら等しい。 -/
theorem Path.startsWith_antisymm {A B : Path} (h1 : A.startsWith B = true)
    (h2 : B.startsWith A = true) : A = B := by
  obtain ⟨a, b, rfl, rfl, hab⟩ := (Path.startsWith_iff _ _).mp h1
  obtain ⟨b', a', hb, ha, hba⟩ := (Path.startsWith_iff _ _).mp h2
  cases hb; cases ha
  rw [List.IsPrefix.eq_of_length hab (Nat.le_antisymm hab.length_le hba.length_le)]

/-- 列どうしなら、等しい path は starts with である。opaque path は自分自身にも starts with でない。 -/
theorem Path.startsWith_of_equals {a b : List String} (h : (Path.list a).equals (.list b) = true) :
    (Path.list a).startsWith (.list b) = true := by
  rw [(Path.equals_iff _ _).mp h]; exact Path.startsWith_refl b

theorem Path.startsWith_opaque_self (o : String) : (Path.opaque o).startsWith (.opaque o) = false :=
  rfl

/-! ### serialize との関係（§4.5 の注記）-/

/-- 列の path の serialize を文字の列で書いたもの。 -/
def segChars : List String → List Char
  | [] => []
  | s :: rest => '/' :: (s.toList ++ segChars rest)

theorem pathSerializer_segChars : ∀ (l : List String),
    (pathSerializer (.list l)).toList = segChars l
  | [] => rfl
  | s :: rest => by
    rw [pathSerializer_cons]
    have hrec : rest.foldl (fun a x => a ++ "/" ++ x) "" = pathSerializer (.list rest) := rfl
    rw [hrec]
    simp [segChars, pathSerializer_segChars rest]

theorem segChars_append (a b : List String) : segChars (a ++ b) = segChars a ++ segChars b := by
  induction a with
  | nil => rfl
  | cons s r ih => simp [segChars, ih]

/-- 空か `/` で始まる。 -/
def SlashHead (l : List Char) : Prop := l = [] ∨ l.head? = some '/'

theorem slashHead_segChars : ∀ (l : List String), SlashHead (segChars l)
  | [] => Or.inl rfl
  | _ :: _ => Or.inr rfl

/-- `/` を含まない片の後ろに空か `/` で始まる列が続くなら、片は読み分けられる。 -/
theorem noSlash_append_inj : ∀ {x y X Y : List Char}, noSlash x = true → noSlash y = true →
    SlashHead X → SlashHead Y → x ++ X = y ++ Y → x = y ∧ X = Y
  | [], [], _, _, _, _, _, _, h => ⟨rfl, h⟩
  | [], c :: y, X, Y, _, hy, hX, _, h => by
    simp only [List.nil_append, List.cons_append] at h
    subst h
    have hc : c ≠ '/' := by simpa [noSlash] using (List.all_eq_true.mp hy c (by simp))
    rcases hX with h | h
    · cases h
    · simp at h; exact absurd h hc
  | c :: x, [], X, Y, hx, _, _, hY, h => by
    simp only [List.nil_append, List.cons_append] at h
    subst h
    have hc : c ≠ '/' := by simpa [noSlash] using (List.all_eq_true.mp hx c (by simp))
    rcases hY with h | h
    · cases h
    · simp at h; exact absurd h hc
  | c :: x, d :: y, X, Y, hx, hy, hX, hY, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    have hx' : noSlash x = true := by
      simp only [noSlash, List.all_cons, Bool.and_eq_true] at hx ⊢; exact hx.2
    have hy' : noSlash y = true := by
      simp only [noSlash, List.all_cons, Bool.and_eq_true] at hy ⊢; exact hy.2
    obtain ⟨h1, h2⟩ := noSlash_append_inj hx' hy' hX hY h.2
    exact ⟨by rw [h.1, h1], h2⟩

theorem prefix_of_segChars : ∀ {a b : List String} {r : List Char},
    (∀ s ∈ a, noSlash s.toList = true) → (∀ s ∈ b, noSlash s.toList = true) → SlashHead r →
    segChars a = segChars b ++ r → b <+: a
  | _, [], _, _, _, _, _ => List.nil_prefix
  | [], _ :: _, _, _, _, _, h => by simp [segChars] at h
  | x :: a, y :: b, r, ha, hb, hr, h => by
    simp only [segChars, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
    have hY : SlashHead (segChars b ++ r) := by
      cases b with
      | nil => simpa [segChars] using hr
      | cons _ _ => exact Or.inr rfl
    obtain ⟨hxy, hrest⟩ := noSlash_append_inj (ha x (by simp)) (hb y (by simp))
      (slashHead_segChars a) hY h
    have := prefix_of_segChars (fun s hs => ha s (by simp [hs])) (fun s hs => hb s (by simp [hs]))
      hr hrest
    rw [String.toList_inj.mp hxy]
    exact List.cons_prefix_cons.mpr ⟨rfl, this⟩

/--
**列の path では、A が B で始まることは、serialize した B の後ろに「何も無いか `/`」が続いて
serialize した A になることである**（§4.5 の注記）。

segment が `/` を含まないこと（§4.1、`ValidUrl.pathSegs`）を仮定する。
文字列として前方一致を見るだけでは足りないことは、下の `example` に固定した。
-/
theorem Path.startsWith_iff_serialize {a b : List String}
    (ha : pathSegsOk (.list a) = true) (hb : pathSegsOk (.list b) = true) :
    (Path.list a).startsWith (.list b) = true ↔
      ∃ r, (pathSerializer (.list a)).toList = (pathSerializer (.list b)).toList ++ r ∧
        (r = [] ∨ r.head? = some '/') := by
  simp only [pathSegsOk, List.all_eq_true] at ha hb
  rw [Path.startsWith_iff, pathSerializer_segChars, pathSerializer_segChars]
  constructor
  · rintro ⟨a', b', ha', hb', ⟨c, rfl⟩⟩
    cases ha'; cases hb'
    exact ⟨segChars c, segChars_append _ _, slashHead_segChars c⟩
  · rintro ⟨r, h, hr⟩
    exact ⟨a, b, rfl, rfl, prefix_of_segChars ha hb hr h⟩

/--
**serialize した文字列の前方一致では足りない**（§4.5 の注記）。
« "foobar" » の serialize は « "foo" » の serialize で始まるが、path としては始まらない。
-/
example : (pathSerializer (.list ["foo"])).toList <+: (pathSerializer (.list ["foobar"])).toList ∧
    (Path.list ["foobar"]).startsWith (.list ["foo"]) = false := by decide

/-! ## URL equality -/

/--
**parse の像の上では、equals は record の等しさに一致する。**

`a` と `b` が同じ文字列に serialize されるなら、その文字列を parse し直したものは
往復により `a` にも `b` にもなる。
-/
theorem equals_iff_eq {t : List Char → Option String} (htok : ToAsciiOk t) {a b : Url}
    (hav : ValidUrl a) (hac : canonicalUrl a t = true)
    (hbv : ValidUrl b) (hbc : canonicalUrl b t = true) :
    a.equals b = true ↔ a = b := by
  constructor
  · intro h
    have hs : urlSerializer a = urlSerializer b := by simpa [Url.equals] using h
    have ha := roundtrip_canonical_of htok.noForbidden hav hac
    have hb := roundtrip_canonical_of htok.noForbidden hbv hbc
    rw [hs, hb] at ha
    exact (Option.some.inj ha).symm
  · rintro rfl
    simp [Url.equals]

/-- parse の結果どうしなら、equals は record の等しさに一致する。 -/
theorem parseUrl_equals_iff {t : List Char → Option String} (htok : ToAsciiOk t)
    {i j : String} {bi bj : Option String} {a b : Url}
    (ha : parseUrl i bi t = some a) (hb : parseUrl j bj t = some b) :
    a.equals b = true ↔ a = b :=
  equals_iff_eq htok (parseUrl_valid ha) (parseUrl_canonical htok ha)
    (parseUrl_valid hb) (parseUrl_canonical htok hb)

/-- exclude fragment を付けて serialize するのは、fragment を null にして serialize するのと同じである。 -/
theorem urlSerializer_excludeFragment (u : Url) :
    urlSerializer u true = urlSerializer { u with fragment := none } := by
  simp only [urlSerializer, serializerTail]
  cases u.fragment <;> rfl

theorem ValidUrl.dropFragment {u : Url} (h : ValidUrl u) : ValidUrl { u with fragment := none } :=
  ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12⟩

theorem canonicalUrl_dropFragment {t : List Char → Option String} {u : Url}
    (h : canonicalUrl u t = true) : canonicalUrl { u with fragment := none } t = true := by
  simp only [canonicalUrl, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, _⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := h
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, trivial⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩

/--
**exclude fragments を付けた equals は、fragment を除いた record の等しさに一致する**（parse の像の上で）。
-/
theorem equals_excludeFragments_iff {t : List Char → Option String} (htok : ToAsciiOk t)
    {a b : Url} (hav : ValidUrl a) (hac : canonicalUrl a t = true)
    (hbv : ValidUrl b) (hbc : canonicalUrl b t = true) :
    a.equals b true = true ↔ { a with fragment := none } = { b with fragment := none } := by
  have h := equals_iff_eq htok hav.dropFragment (canonicalUrl_dropFragment hac)
    hbv.dropFragment (canonicalUrl_dropFragment hbc)
  simp only [Url.equals, urlSerializer_excludeFragment] at h ⊢
  exact h

end Url
