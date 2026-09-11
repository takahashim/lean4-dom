/-!
# UTF-16 の code unit

WebIDL の `DOMString` は 16-bit code unit の列で、仕様が「文字列を比較する」と言うとき
その順序は **code unit の辞書式**である（URL Standard §6.2 の `sort` がそれを名指ししている）。

code point 順と一致しない。BMP の外の code point は surrogate pair
（U+D800..U+DBFF, U+DC00..U+DFFF）になるので、code unit では U+E000 以上の BMP 文字より
**小さく**なる。たとえば U+1F308（🌈）は D83C DF08 で、U+FB03（ﬃ）より code unit では前に来るが、
code point では後ろである。
-/

namespace Infra

/-- code point が占める UTF-16 code unit。BMP なら 1 つ、それ以外は surrogate pair。 -/
def codeUnits (c : Char) : List UInt16 :=
  if c.toNat < 0x10000 then [UInt16.ofNat c.toNat]
  else
    let m := c.toNat - 0x10000
    [UInt16.ofNat (0xD800 + m / 0x400), UInt16.ofNat (0xDC00 + m % 0x400)]

/-- 文字列の UTF-16 code unit 列。 -/
def utf16Units (s : String) : List UInt16 := s.toList.flatMap codeUnits

/-- code unit 列の辞書式比較。 -/
def lexLt : List UInt16 → List UInt16 → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a == b then lexLt as bs else a < b

/-- WebIDL の `DOMString` としての大小（code unit 順）。 -/
def strLt (a b : String) : Bool := lexLt (utf16Units a) (utf16Units b)

/-! ## 性質 -/

/-- 同じ列どうしは小さくない。 -/
@[simp] theorem lexLt_self : ∀ l : List UInt16, lexLt l l = false
  | [] => rfl
  | a :: rest => by simp [lexLt, lexLt_self rest]

/-- 同じ文字列どうしは小さくない。 -/
@[simp] theorem strLt_self (a : String) : strLt a a = false := by
  simp [strLt]

/-- 小さいなら等しくない。`sort` の安定性の証明で使う。 -/
theorem ne_of_strLt {a b : String} (h : strLt a b = true) : a ≠ b := by
  intro he
  rw [he, strLt_self] at h
  exact absurd h (by simp)

end Infra
