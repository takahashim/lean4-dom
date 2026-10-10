import Dom.Idl.Value

/-!
# §2.7 の options の flatten

`addEventListener` と `removeEventListener` の options は、WebIDL が union に変換した後で
DOM の "flatten" と "flatten more" にかける（`Dom/Idl/Value.lean` が変換を行う）。
-/

namespace Dom

open Idl

/-- **DOM Standard §2.7 "flatten"。** boolean ならそれ、dictionary なら `capture`。 -/
def flattenOptions : EventListenerOptionsOrBoolean → Bool
  | .boolean b => b
  | .dict capture => capture

/--
**DOM Standard §2.7 "flatten more"。** capture・passive・once を返す（signal は model に無い）。

1. capture は flatten の結果。2. once は false、3. passive は null。
4. dictionary なら、once は `once`、passive は `passive` があればそれ。
-/
def flattenMoreOptions : AddEventListenerOptionsOrBoolean → Bool × Option Bool × Bool
  | .boolean b => (b, none, false)
  | .dict capture once passive => (capture, passive, once)

end Dom
