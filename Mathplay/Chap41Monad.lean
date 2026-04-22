

namespace S411

def first (xs : List α) : Option α :=
  xs[0]?

-- V1 : Annoying
def f1357 (xs : List α) : Option (α × α × α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third =>
      match xs[4]? with
      | none => none
      | some fifth =>
        match xs[6]? with
        | none => none
        | some seventh =>
          some (first, third, fifth, seventh)

-- V2 : CPS with andThen
def andThen (opt : Option α) (next : α → Option β) : Option β :=
  match opt with
  | none => none
  | some x => next x

def f1357_v2 (xs : List α) : Option (α × α × α × α) :=
  andThen xs[0]? fun first =>
  andThen xs[2]? fun third =>
  andThen xs[4]? fun fifth =>
  andThen xs[6]? fun seventh =>
  some (first, third, fifth, seventh)

-- V3 : With the infix
infixl:55 " ~~> " => andThen

def f1357_v3 (xs : List α) : Option (α × α × α × α) :=
  xs[0]? ~~> fun first =>
  xs[2]? ~~> fun third =>
  xs[4]? ~~> fun fifth =>
  xs[6]? ~~> fun seventh =>
  some (first, third, fifth, seventh)

end S411

/- ---------------------------------------------------------------------------- -/
/- ---------------------------------------------------------------------------- -/
/- ---------------------------------------------------------------------------- -/

namespace S412

inductive Except (ε : Type) (α : Type) where
  | error : ε → Except ε α
  | ok : α → Except ε α
deriving BEq, Hashable, Repr

def get (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none => Except.error s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x => Except.ok x

def ediblePlants : List String :=
  ["ramsons", "sea plantain", "sea buckthorn", "garden nasturtium"]

-- V1 : Annoying

def f1357_v1 (xs : List α) : Except String (α × α × α × α) :=
  match get xs 0 with
  | Except.error msg => Except.error msg
  | Except.ok first =>
    match get xs 2 with
    | Except.error msg => Except.error msg
    | Except.ok third =>
      match get xs 4 with
      | Except.error msg => Except.error msg
      | Except.ok fifth =>
        match get xs 6 with
        | Except.error msg => Except.error msg
        | Except.ok seventh =>
          Except.ok (first, third, fifth, seventh)


def andThen (attempt : Except e α) (next : α → Except e β) : Except e β :=
  match attempt with
  | Except.error msg => Except.error msg
  | Except.ok x => next x

infixl:55 " ~~> " => andThen

-- V2.1 : With andThen

def f1357_v2_1 (xs : List α) : Except String (α × α × α × α) :=
  andThen (get xs 0) (fun first =>
  andThen (get xs 2) (fun third =>
  andThen (get xs 4) (fun fifth =>
  andThen (get xs 6) (fun seventh =>
  Except.ok (first, third, fifth, seventh)
  ))))


-- V2.2 : No need for parentheses !
def f1357_v2_2 (xs : List α) : Except String (α × α × α × α) :=
  andThen (get xs 0) fun first =>
  andThen (get xs 2) fun third =>
  andThen (get xs 4) fun fifth =>
  andThen (get xs 6) fun seventh =>
  Except.ok (first, third, fifth, seventh)


-- V2.3 : With infix ~~>
def f1357_v2_3 (xs : List α) : Except String (α × α × α × α) :=
  get xs 0 ~~> fun first =>
  get xs 2 ~~> fun third =>
  get xs 4 ~~> fun fifth =>
  get xs 6 ~~> fun seventh =>
  Except.ok (first, third, fifth, seventh)


-- V2.4 : Refactoring success/failure handling
def fail (err : ε) : Except ε α :=
  Except.error err

def ok (a : α) : Except ε α :=
  Except.ok a

def get_v2_4 (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none => fail s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x => ok x

def f1357_v2_4 (xs : List α) : Except String (α × α × α × α) :=
  get_v2_4 xs 0 ~~> fun first =>
  get_v2_4 xs 2 ~~> fun third =>
  get_v2_4 xs 4 ~~> fun fifth =>
  get_v2_4 xs 6 ~~> fun seventh =>
  ok (first, third, fifth, seventh)


end S412

/- ---------------------------------------------------------------------------- -/
/- ---------------------------------------------------------------------------- -/
/- ---------------------------------------------------------------------------- -/

namespace S413

def isEven (n : Nat) : Bool :=
  n % 2 == 0

def sumAndFindEvens : List Nat → Nat × List Nat
  | [] => (0, [])
  | x :: xs =>
    let (sum, evens) := sumAndFindEvens xs
    let evens := if isEven x then x :: evens else evens
    (sum + x, evens)

-- V2 : Exhibit the structure of the code as
--      a pipe of operations on the (sum, events) tuple
def sumAndFindEvens_v2 : List Nat → Nat × List Nat
  | [] => (0, [])
  | x :: xs =>
    -- Recursive call to "what to do next"
    let (sum, evens) := sumAndFindEvens xs
    -- Pattern-matching the result to know what to do (even or not even)
    let (sum, evens) := (sum + x, if isEven x then x :: evens else evens)
    (sum, evens)


structure withLog (logged α : Type) where
  val : α
  log : List logged


def andThen (result : withLog β α) (next : α → withLog β γ) : withLog β γ :=
  let {val := v, log := l} := result
  -- Recursive call "what to do next"
  -- Here it's the log that's accumulated, we don't care about the previous value
  -- We just care about returning the last value of the chain of computations,
  -- while accumulating the logs of all computations
  let {val := v',log := l'} := next v
  -- Pattern-match the result to know what to do (log or don't log)
  {val := v', log := l ++ l'}

-- In case of error (above), `ok` represents a function that does not error
-- In case of logging (here), `ok` represents a function that does not log
-- You have a result ready to return ? Use `ok` to return it, no logging
def ok (val : α) : withLog β α :=
  {val := val, log := []}

-- In case of error (above), `fail` represents a function that errors
-- In case of logging (here), `save` represents a function that logs
-- You want to log something ? Use `save` for it, there is no computation here so no val
def save (data : β) : withLog β Unit :=
  {val := (), log := [data]}


def sumAndFindEvens_v3 : List Nat → withLog Nat Nat
  | [] => ok 0
  | x :: xs =>
    -- Logging (no summing)
    andThen (if isEven x then save x else ok ()) fun () =>
    -- Recursive call
    andThen (sumAndFindEvens_v3 xs) fun sum =>
    -- Summing (no logging)
    ok (x + sum)

infixl:55 " ~~> " => andThen

def sumAndFindEvens_v4 : List Nat → withLog Nat Nat
  | [] => ok 0
  | x :: xs =>
    -- Logging (no summing)
    (if isEven x then save x else ok ()) ~~> fun () =>
    -- Recursive call
    sumAndFindEvens_v3 xs ~~> fun sum =>
    -- Summing (no logging)
    ok (x + sum)




inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α

def eqBinTree [BEq α] : BinTree α → BinTree α → Bool
  | BinTree.leaf, BinTree.leaf =>
    true
  | BinTree.branch l x r, BinTree.branch l2 x2 r2 =>
    x == x2 && eqBinTree l l2 && eqBinTree r r2
  | _, _ =>
    false

open BinTree in
def aTree : BinTree Int :=
  branch
    (branch
       (branch leaf 3 (branch leaf 2 leaf))
       1
       leaf)
    4
    (branch leaf 5 leaf)

/-


-/


def inorderSum_v0 : BinTree Int → withLog Int Int
  | BinTree.leaf => ok 0
  | BinTree.branch l x r =>
    let {val := lv, log := llog} := inorderSum_v0 l
    let {val := _ , log := mlog} :withLog Int Unit := {val := (), log := [x]}
    let {val := rv, log := rlog} := inorderSum_v0 r
    {val := lv + x + rv, log := llog ++ mlog ++ rlog}

example : inorderSum_v0 aTree = { val := 15, log := [3, 2, 1, 4, 5]} := by rfl


def inorderSum_v1 : BinTree Int → withLog Int Int
  | BinTree.leaf => ok 0
  | BinTree.branch l x r =>
    let {val := lv, log := llog} := inorderSum_v0 l
    let {val := _ , log := mlog} : withLog Int Unit := {val := (), log := [x]}
    let {val := rv, log := rlog} := inorderSum_v0 r
    {val := lv + x + rv, log := llog ++ mlog ++ rlog}


def inorderSum : BinTree Int → withLog Int Int
  | BinTree.leaf => ok 0
  | BinTree.branch l x r =>
    andThen (inorderSum l) fun leftSum =>
    andThen (save x) fun () =>
    andThen (inorderSum r) fun rightSum =>
    ok (leftSum + x + rightSum)

example : inorderSum aTree = { val := 15, log := [3, 2, 1, 4, 5]} := by rfl

end S413

/-
andThen does :
- A. Intercept and extract value (computation result) + metadata (control flow)
- B. Decorticate metadata to know what to do
  Full freedom on what to do next :
  - Stop the pipeline and return now (e.g. None or Except)
  - Call the next thing to do (CPS style enables that)
- C. If calling `next`, extract the value and pass it to `next`

In the case of Option :
A. Extract the value 'a' and the control flow Some/None
B. If it's None, return now (return None)
   If it's Some `a`, `next`
C. Pass `a` to `next`

In the case of Exception, almost the same :
A. Extract the value 'v' and the control flow ok/except
B. If it's Exception `msg`, return now with `msg`
   IF it's ok `v`, run `next`
C. Passing `v` to `next`

In the case of Log :
A.  Extract computation `v` and metadata `log`
C. Call `next` with `v` anyway (returning `v'` and more `log'`)
B.  Accumulate the logs (`log ++ log'`)
B. Return the last computation `v'`

(in the SumAndFindEvens application of the Log monad,
the user decides when to log (i.e. when it finds an even number)
but doesn't handle the logging boilerplate)

In the InOrderSum application of the Log monad,
The user does :
- recursive call on left and right subtree :
  - on computation : saving left subtree log, right subtree log
  - on values : getting the sub of the two subtrees
- the the manual bit :
  - on computation : adding lsum rsum and node
    by calling `lsum + x + rsum`
  - logging the node
    by calling `save`


When reading the `inOrderSum` function,
I first imagined the logging was accumated topdown
But then I was confused how the "log so far" was passed round.
But the logging really happens bottom up.
The innermost function logs nothing.
THen the function with after that (the bottom-est `andTHen` )
intercepts the log so far and adds its log to that.
THen the second bottom-est `andThen` intercepts that first piece of log
and adds its log to that...
Up the the outermost function call, who gets the whole logs
and final value and return all that

-/
