import Dom.Basic.State
import Dom.Basic.Order

/-!
# observer に関わる順序（§4.3）

MutationObserver の配送は順序が観測に出る。notify は pending mutation observers を creation index の順に
並べ直してから回る（§4.3 notify step 2、6）ので、配送の順に出るのは pending の所属である。model は pending の列
そのものも本文どおりに保つ。どの observer が pending に入るかの順は "queue a mutation record" が決める。
その順は次の二つから決まる。

* **interested observers の順**（"queue a mutation record" step 3-4）：target の inclusive ancestor を
  下から上へ、各 node の registered observer list を list の順に見て、条件を満たす registered の observer を
  初めて出てきた順に並べる（interestedObservers は ordered map である）。
* **pending mutation observers への append**（step 5.3）：ordered set への append なので、既にあれば何もしない。

registered observer list は node ごとにあり、異なる node の list のあいだの順は本文に無い。
model は registration を一つの列（`DOMState.registrations`）で持つので、観測に出るのは
その列を node ごとに絞った列（`regsOn`）である。

| 定義 | 本文 |
| --- | --- |
| `InclusiveAncestorsUp t n l` | `n` の inclusive ancestor を下から上へ並べた列 |
| `regsOn regs n` | `n` の registered observer list |
| `appendNew acc xs` | ordered set への append を `xs` の順に繰り返す |
| `interestedOrder` | "queue a mutation record" の interestedObservers の key の順 |
| `PendingAppended` | step 4-6 の後の pending mutation observers と microtask |
| `RegistrationsObsEq` | node ごとの registered observer list がどれも等しい |
-/

namespace Dom.Spec

open Dom

/-- `n` の inclusive ancestor を、`n` から root へ向かって並べた列。 -/
inductive InclusiveAncestorsUp (t : Tree) : NodeId → List NodeId → Prop where
  | top {n : NodeId} : parentOf t n = none → InclusiveAncestorsUp t n [n]
  | up {n p : NodeId} {l : List NodeId} : parentOf t n = some p → InclusiveAncestorsUp t p l →
      InclusiveAncestorsUp t n (n :: l)

/-- node `n` の registered observer list。 -/
def regsOn (regs : List Registration) (n : NodeId) : List Registration :=
  regs.filter fun r => r.node == n

/-- ordered set への append を `xs` の順に行う。既にある値は足さない。 -/
def appendNew (acc xs : List Nat) : List Nat :=
  xs.foldl (fun a x => if x ∈ a then a else a ++ [x]) acc

/--
"queue a mutation record" step 3 の interestedObservers の key の順。`nodes` の順に、各 node の
registered observer list のうち `P` を満たすものの observer を、初めて出てきた順に並べる。
-/
def interestedOrder (regs : List Registration) (nodes : List NodeId) (P : Registration → Bool) :
    List Nat :=
  appendNew [] (nodes.flatMap fun n => ((regsOn regs n).filter P).map (·.observer))

/-- childList の record について、registered が step 3.2 の条件を通るか（target は record の target）。 -/
def childListInterest (target : NodeId) (r : Registration) : Bool :=
  r.childList && (r.node == target || r.subtree)

/-- characterData の record について、registered が step 3.2 の条件を通るか。 -/
def characterDataInterest (target : NodeId) (r : Registration) : Bool :=
  r.characterData && (r.node == target || r.subtree)

/-- attributes の record について、registered が step 3.2 の条件を通るか。 -/
def attributeInterest (target : NodeId) (name : String) (ns : Option String) (r : Registration) :
    Bool :=
  r.attributes && (r.node == target || r.subtree) &&
    (match r.attributeFilter with
     | none => true
     | some f => f.contains name && ns.isNone)

/--
**step 4-6 の後の pending mutation observers と microtask。** target の inclusive ancestor の列で
interested observers の順を決め、その順に pending mutation observers へ append する（step 5.3）。
interested observers が空なら step 4 で返るので、microtask は予約しない（step 6）。
-/
def PendingAppended (s s' : DOMState) (target : NodeId) (P : Registration → Bool) : Prop :=
  ∃ nodes, InclusiveAncestorsUp s.tree target nodes ∧
    s'.pendingObservers = appendNew s.pendingObservers (interestedOrder s.registrations nodes P) ∧
    s'.microtaskQueued =
      (s.microtaskQueued || !(interestedOrder s.registrations nodes P).isEmpty)

/-- node ごとの registered observer list がどれも等しい。 -/
def RegistrationsObsEq (regs regs' : List Registration) : Prop :=
  ∀ n, regsOn regs' n = regsOn regs n

/-! ## 一意性と congruence -/

theorem inclusiveAncestorsUp_unique {t : Tree} :
    ∀ {n : NodeId} {l₁ l₂ : List NodeId},
      InclusiveAncestorsUp t n l₁ → InclusiveAncestorsUp t n l₂ → l₁ = l₂
  | _, _, _, .top h₁, .top _ => rfl
  | _, _, _, .top h₁, .up h₂ _ => by rw [h₁] at h₂; cases h₂
  | _, _, _, .up h₁ _, .top h₂ => by rw [h₁] at h₂; cases h₂
  | _, _, _, .up h₁ r₁, .up h₂ r₂ => by
    rw [h₁] at h₂
    cases h₂
    rw [inclusiveAncestorsUp_unique r₁ r₂]

/-- 親の関係が等しい木では、inclusive ancestor の列も同じである。 -/
theorem inclusiveAncestorsUp_congr {t t' : Tree} (h : ∀ m, parentOf t' m = parentOf t m) :
    ∀ {n : NodeId} {l : List NodeId}, InclusiveAncestorsUp t n l → InclusiveAncestorsUp t' n l
  | _, _, .top hp => .top (by rw [h]; exact hp)
  | _, _, .up hp r => .up (by rw [h]; exact hp) (inclusiveAncestorsUp_congr h r)

theorem RegistrationsObsEq.refl (regs : List Registration) : RegistrationsObsEq regs regs :=
  fun _ => rfl

theorem RegistrationsObsEq.symm {regs regs' : List Registration} (h : RegistrationsObsEq regs regs') :
    RegistrationsObsEq regs' regs := fun n => (h n).symm

theorem RegistrationsObsEq.trans {a b c : List Registration} (h : RegistrationsObsEq a b)
    (h' : RegistrationsObsEq b c) : RegistrationsObsEq a c := fun n => (h' n).trans (h n)

theorem RegistrationsObsEq.of_eq {regs regs' : List Registration} (h : regs' = regs) :
    RegistrationsObsEq regs regs' := by subst h; exact RegistrationsObsEq.refl _

/-- node ごとの list が等しければ、registration の所属も等しい。 -/
theorem RegistrationsObsEq.mem_iff {regs regs' : List Registration} (h : RegistrationsObsEq regs regs')
    (r : Registration) : r ∈ regs' ↔ r ∈ regs := by
  have hr := h r.node
  have : ∀ l : List Registration, r ∈ l ↔ r ∈ regsOn l r.node := by
    intro l; simp [regsOn]
  rw [this regs', this regs, hr]

/-- 同じ node の列から決まる interested observers の順は、node ごとの list だけで決まる。 -/
theorem interestedOrder_congr {regs regs' : List Registration} (h : RegistrationsObsEq regs regs')
    (nodes : List NodeId) (P : Registration → Bool) :
    interestedOrder regs' nodes P = interestedOrder regs nodes P := by
  unfold interestedOrder
  congr 1
  have : (fun n => ((regsOn regs' n).filter P).map (·.observer)) =
      (fun n => ((regsOn regs n).filter P).map (·.observer)) := by
    funext n; rw [h n]
  rw [this]

/-- 入力の木の親の関係・registration の node ごとの list・pending が等しければ、pending の結果も等しい。 -/
theorem pendingAppended_unique {s sb o₁ o₂ : DOMState} {target : NodeId} {P : Registration → Bool}
    (ht : ∀ m, parentOf sb.tree m = parentOf s.tree m)
    (hr : RegistrationsObsEq s.registrations sb.registrations)
    (hp : sb.pendingObservers = s.pendingObservers)
    (h₁ : PendingAppended s o₁ target P) (h₂ : PendingAppended sb o₂ target P) :
    o₂.pendingObservers = o₁.pendingObservers := by
  obtain ⟨n₁, hn₁, he₁, -⟩ := h₁
  obtain ⟨n₂, hn₂, he₂, -⟩ := h₂
  have := inclusiveAncestorsUp_unique (inclusiveAncestorsUp_congr ht hn₁) hn₂
  subst this
  rw [he₁, he₂, hp, interestedOrder_congr hr]

/-- 同じく、microtask の結果も等しい。 -/
theorem pendingAppended_microtask_unique {s sb o₁ o₂ : DOMState} {target : NodeId}
    {P : Registration → Bool}
    (ht : ∀ m, parentOf sb.tree m = parentOf s.tree m)
    (hr : RegistrationsObsEq s.registrations sb.registrations)
    (hm : sb.microtaskQueued = s.microtaskQueued)
    (h₁ : PendingAppended s o₁ target P) (h₂ : PendingAppended sb o₂ target P) :
    o₂.microtaskQueued = o₁.microtaskQueued := by
  obtain ⟨n₁, hn₁, -, he₁⟩ := h₁
  obtain ⟨n₂, hn₂, -, he₂⟩ := h₂
  have := inclusiveAncestorsUp_unique (inclusiveAncestorsUp_congr ht hn₁) hn₂
  subst this
  rw [he₁, he₂, hm, interestedOrder_congr hr]

/-- 親の関係・node ごとの registration・pending・microtask が等しい入力へ、`PendingAppended` を差し替える。 -/
theorem pendingAppended_transport {s s' out : DOMState} {target : NodeId} {P : Registration → Bool}
    (ht : ∀ m, parentOf s'.tree m = parentOf s.tree m)
    (hr : RegistrationsObsEq s.registrations s'.registrations)
    (hp : s'.pendingObservers = s.pendingObservers)
    (hm : s'.microtaskQueued = s.microtaskQueued)
    (h : PendingAppended s' out target P) : PendingAppended s out target P := by
  obtain ⟨nodes, hn, he, hme⟩ := h
  refine ⟨nodes, inclusiveAncestorsUp_congr (fun m => (ht m).symm) hn, ?_, ?_⟩
  · rw [he, hp, interestedOrder_congr hr]
  · rw [hme, hm, interestedOrder_congr hr]

end Dom.Spec
