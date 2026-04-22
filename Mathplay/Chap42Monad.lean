

instance : Monad Option where
  pure x := some x
  bind x? f :=
    match x? with
    | none => none
    | some x => f x

def lookup (xs : List α) (n : Nat) : Option α := xs[n]?

def f1357 [Monad m]
  (lookup : List α → Nat → m α)
  (xs : List α)
  : m (α × α × α × α) :=
  lookup xs 0 >>= λ v1 =>
  lookup xs 2 >>= λ v3 =>
  lookup xs 4 >>= λ v5 =>
  lookup xs 6 >>= λ v7 =>
  pure (v1, v3, v5, v7)

#eval f1357 lookup [5, 2, 8, 4, 9, 1, 4, 2]
example : f1357 lookup [5, 2, 8, 4, 9, 1, 4, 2] = some (5, 8, 9, 4) := by rfl
example : f1357 lookup [5, 2, 8, 4, 9, 1, 4] = some (5, 8, 9, 4) := by rfl
example : f1357 lookup [5, 2, 8, 4, 9, 1] = none := by rfl
example : f1357 lookup ["c"] = none := by rfl
example : f1357 lookup [
"H", "e", "l", "l", "o", "w", "o", "r", "l", "d",
] = some ("H", "l", "o", "o") := by rfl

-- State Monad : A stateful computation
def State (σ : Type) (α : Type) : Type :=
  σ → (σ × α)

def State.ok (x : α) : State σ α :=
  fun s => (s, x)

def State.get : State σ σ :=
  fun s => (s, s)

def State.set (s : σ) : State σ Unit :=
  fun _ => (s, ())

instance : Monad (State σ) where
  pure x := State.ok x
  bind f1 f2 :=
    fun s =>
    let (s', v) := f1 s -- Run the first computation, extract value and state
    let (s'', v') := f2 v s' -- Run the second computation with the new state
    (s'', v') -- Just return the result of the second computation

def mapM [Monad m] (f : α → m β) : List α  → m (List β)
  | [] => pure []
  | x :: xs =>
      f x >>= fun hd =>
      mapM f xs >>= fun tl =>
      pure (hd :: tl)

def increment (howMuch : Int) : State Int Int :=
  open State in
  -- get current sum so far
  get >>= λ sum =>
  -- add to the sum
  set (sum + howMuch) >>= λ () =>
  -- return cur sum so far
  pure sum

def increment' (howMuch : Int) : State Int Int :=
  open State in do
  let sum ← get
  let () ← set (sum + howMuch)
  return sum

#eval mapM increment [1, 2, 3, 4, 5] 0
example : mapM increment [1, 2, 3, 4, 5] 0 = (15, [0, 1, 3, 6, 10]) := by rfl

(* ANKI : memorize fibonnacci ? *)
(* ANKI : goal of writer monad ?
Move the concatenation of logs concern out of the user functions
Separate the logging concern from the main computation
*)


#print Option

namespace toy

def inv (x : Float ) : Option Float :=
  if x == 0 then none else some (1 / x)

def sqrt (x : Float) : Option Float :=
  if x < 0 then none else Float.sqrt x

def sqrt_inv (x : Float) : Option Float :=
  match inv x with
  | none => none
  | some y => (
    match sqrt y with
    | none => none
    | some z => some z
  )

def pure (x : α) := some x
def bind (x : Option α) (f : α → Option β) : Option β :=
  match x with
  | none => none
  | some y => f y

def sqrt_inv_v2 (x : Float) : Option Float :=
  bind (inv x) sqrt

def sqrt_inv_v3 (x : Float) : Option Float :=
  bind (bind (some x) inv) sqrt

infixl:55 " ~~> " => bind

def sqrt_inv_v4 (x : Float) : Option Float :=
  pure x ~~> inv ~~> sqrt

#eval sqrt_inv_v4 42
#eval sqrt_inv 42

def fish (f1 : α → Option β) (f2 : β → Option γ) : α → Option γ :=
  λ a => pure a ~~> f1 ~~> f2

infixl:55 " >==> " => fish

def sqrt_inv_v5 : Float → Option Float :=
  inv >==> sqrt

#eval sqrt_inv_v5 42

theorem left_id : ∀ f : α → Option β, pure >==> f = f := by
  intro f
  rfl

theorem right_id : ∀ f : α → Option β, f >==> pure = f := by
  intro f
  funext a
  simp [fish, bind, pure]
  cases (f a) <;> simp

theorem assoc :
  ∀ (f : α → Option β)
    (g : β → Option γ)
    (h : γ → Option ε),
  (f >==> g) >==> h = f >==> (g >==> h) := by
  intros f g h
  funext a
  simp [fish, bind, pure]
  cases (f a) <;> simp


example : (sqrt_inv_v4 42) = (sqrt_inv 42) := by
  unfold sqrt_inv
  unfold sqrt_inv_v4
  unfold pure
  unfold bind
  simp
  cases (inv 42)
  case none => simp
  case some v => simp ; cases (sqrt v) <;> simp


end toy
