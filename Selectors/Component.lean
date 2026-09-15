import Selectors.Token

/-!
# component value（CSS Syntax Level 3 §5）

token 列をそのまま文法に当てると、`:is(a, b)` の `,` が外側の selector list の
区切りに見えてしまう。仕様は先に括弧の対応を取って **component value** の木にし、
文法はその木に対して書く。ここでも同じ順序にする。

木にしておくと、`:is()` の中身は元の列の真の部分列になる。おかげで
selector の parser は入れ子の再帰を構造的に書ける。

## 仕様との差

* **閉じ括弧が無いまま入力が尽きたら失敗にする。** 仕様は parse error として
  その場で block を閉じるが、`querySelector("a[href")` は実装では例外になる。
-/

namespace Selectors

/-- §5.4 の component value。 -/
inductive Component where
  /-- preserved token。括弧と function-token 以外。 -/
  | tok (t : Token)
  /-- `name(...)`。 -/
  | func (name : String) (args : List Component)
  /-- `(...)` `[...]` `{...}`。`opener` は開き括弧の token。 -/
  | block (opener : Token) (items : List Component)
deriving Repr, Inhabited

/-- block を開く token と、それを閉じる token。 -/
def closerOf : Token -> Option Token
  | .lparen => some .rparen
  | .function _ => some .rparen
  | .lbracket => some .rbracket
  | .lbrace => some .rbrace
  | _ => none

/--
対応する閉じ括弧までを切り出す。`stack` は閉じ待ちの括弧（内側が先頭）。

対応しない閉じ括弧はただの token として通す（§5.4.7 と同じ扱い）。
-/
def splitBlock (stack : List Token) (acc : List Token) : List Token ->
    Option (List Token × List Token)
  | [] => none
  | t :: rest =>
    match closerOf t with
    | some cl => splitBlock (cl :: stack) (t :: acc) rest
    | none =>
      if stack.head? == some t then
        if stack.tail.isEmpty then some (acc.reverse, rest)
        else splitBlock stack.tail (t :: acc) rest
      else splitBlock stack (t :: acc) rest

/-- 切り出した中身と残りを合わせても、閉じ括弧のぶんだけ短い。 -/
theorem splitBlock_size : ∀ (stack acc l inside after : List Token),
    splitBlock stack acc l = some (inside, after) ->
    inside.length + after.length < acc.length + l.length
  | _, _, [], _, _, h => by simp [splitBlock] at h
  | stack, acc, t :: rest, inside, after, h => by
    rw [splitBlock] at h
    split at h
    · have := splitBlock_size _ (t :: acc) rest inside after h
      simp only [List.length_cons] at *; omega
    · split at h
      · split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.1, ← h.2]
          simp only [List.length_reverse, List.length_cons]
          omega
        · have := splitBlock_size stack.tail (t :: acc) rest inside after h
          simp only [List.length_cons] at *; omega
      · have := splitBlock_size stack (t :: acc) rest inside after h
        simp only [List.length_cons] at *; omega

theorem splitBlock_inside_lt {stack l inside after : List Token}
    (h : splitBlock stack [] l = some (inside, after)) : inside.length < l.length := by
  have := splitBlock_size stack [] l inside after h
  simp only [List.length_nil] at this; omega

theorem splitBlock_after_lt {stack l inside after : List Token}
    (h : splitBlock stack [] l = some (inside, after)) : after.length < l.length := by
  have := splitBlock_size stack [] l inside after h
  simp only [List.length_nil] at this; omega

/-- §5.4.6 "consume a list of component values"。括弧が閉じていなければ失敗する。 -/
def toComponents : List Token -> Option (List Component)
  | [] => some []
  | t :: rest =>
    match _hc : closerOf t with
    | some cl =>
      match _hs : splitBlock [cl] [] rest with
      | none => none
      | some (inside, after) =>
        match toComponents inside, toComponents after with
        | some a, some b =>
          match t with
          | .function name => some (Component.func name a :: b)
          | _ => some (Component.block t a :: b)
        | _, _ => none
    | none =>
      match toComponents rest with
      | some b => some (Component.tok t :: b)
      | none => none
termination_by l => l.length
decreasing_by
  · exact Nat.lt_trans (splitBlock_inside_lt _hs) (Nat.lt_succ_self _)
  · exact Nat.lt_trans (splitBlock_after_lt _hs) (Nat.lt_succ_self _)
  · simp_wf

/-- 文字列を component value の列にする。 -/
def parseComponents (input : String) : Option (List Component) :=
  toComponents (tokenize input)

end Selectors
