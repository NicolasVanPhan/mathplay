import Mathlib
import Lean
import Std
open Lean
open Std

/-
  Adder.lean

  Goal of this session - figure out how to reason about small hardware circuits.

  Roadmap:
  - [ ] Write a 1-bit adder (a_i, b_i, c_i, res_o, c_o)
  - [ ] Prove it (prove its behaviour matches the spec of an adder)
  - [ ] Write an N-bit adder out of 1-bit adders (propagating the carries)
  - [ ] Lemma : Prove that a N-bit adder ↔ (N-1)-bit adder feeding a 1-bit adder
  - [ ] Use the lemma to prove correctness of the N-bit adder by N-induction

  I would like to explore how a piece of hardware described in a SystemVerilog-like fashion
  could be translated to Lean definition to reason about.

  The example cases here is a N-bit ripple-carry adder
  but the question extends to any piece of hardware in general.

  The model-checker approach would be to describe the N-bit adder in SystemVerilog,
  write SVA properties ensuring the adder does perform an addition,
  and feed that to a model checker.
  However the number of bits of the addder is typically a SystemVerilog module parameter,
  so it's fixed to a given constant when fed to the model checker,
  and it ignores the "symmetry" of the design.
  The proof for a 2048-bits adder will be longer than for a 4-bit adder,
  becuase there is more logic involved.
  It's a shame, because reasoning on the adder correctness doesn't depend on the adder size.
  It's basically an induction over N. With 2 cases :
  - the bit 0
  - given (N-1)-adder is correct, prove N-adder is correct.
  The size of the reasoning doesn't grow with the size of the adder,
  and this is key to reason in a scalable way.

  However such issues are common, so that in practice, in the industry,
  all design containing repetition (fifo/queues/buffer of N entries) need to be shrunk down,
  reducing N as much as possible, to help model checkers.
  In principle, it shouldn't be needed since the reasoning shouldn't depend on N.

  Here we want to study how to prove our N-bit whatever the value of N.
  Getting a scalable proof.
  But before that, we need to see how to "describe hardware in Lean",
  how SystemVerilog constructs could be "mapped" to Lean constructs, as smoothly as possible.

-/

namespace Adder

/-! ## 1-bit full adder -/

/-
We'll start with a tiny circuit : a 1-bit full adder

It's truth table is describe below :
```
ci a b  |  co r
 0 0 0  |   0 0      // 0 + 0 + 0   = 0 = 0b00
 0 0 1  |   0 1      // 0 + 0 + 1   = 1 = 0b01
 0 1 0  |   0 1      // 0 + 1 + 0   = 1 = 0b01
 0 1 1  |   1 0      // 0 + 1 + 1   = 2 = 0b10
 1 0 0  |   0 1      // 1 + 0 + 0   = 1 = 0b01
 1 0 1  |   1 0      // 1 + 0 + 1   = 2 = 0b10
 1 1 0  |   1 0      // 1 + 1 + 0   = 2 = 0b10
 1 1 1  |   1 1      // 1 + 1 + 1   = 3 = 0b11
```

From the truth table we can extract the logic to compute `r` and `co` :
```
r = a ^ b ^ c  (r == 1 when the concatenation {a, b, c} has an odd number of hot bits)
co = a & b | a & c | b & c
```

The SystemVerilog circuit should look like this :

```verilog
module add_1bit
( input  logic a_i
, input  logic b_i
, input  logic c_i
, output logic r_o
, output logic c_o
)
  assign res_o  = a_i ^ b_i ^ c_i;
  assign c_o    = a_i & b_i | a_i & c_i | b_i & c_i;
endmodule
```

All combinatory hardware circuit is basically a DAG, connecting signals with logic gates.
If we see a logic gate as a pure function, then in principle we should be able to describe
any piece of combinatory logic with a series of Lean pure function definitions.

We could thus see every SV `assign` as a Lean function `def`.
An SV `module` as a larger Lean function taking a `structure` describing all declared inputs,
and returning another one listing all the outputs.
SV `module` input/output declaration will be Lean `structure` declaration.
SV `module` will be a function from input structure to output structure.

-/

namespace Adder_1bit

/- SV module input declaration -/
structure Inputs where
  a : Bool
  b : Bool
  c : Bool
deriving Repr, DecidableEq

/- SV module output declaration -/
structure Outputs where
  r : Bool
  c : Bool
deriving Repr, DecidableEq

/- SV module body -/
def body (i : Inputs) : Outputs :=
  let r := i.a ^^ i.b  ^^ i.c
  let c := i.a && i.b  || i.a && i.c || i.b && i.c
  ⟨r, c⟩

/- Proof : The 1-bit adder really computes `a + b + c`. -/
theorem adder_correct (i : Inputs) :
  let a := i.a.toNat
  let b := i.b.toNat
  let ci := i.c.toNat
  let r := (body i).r.toNat
  let co := (body i).c.toNat
  a + b + ci = r + 2 * co := by
  -- Break i into its components (a b c)
  cases i with | mk a b c =>
  -- Normalize the expression to the shortest boolean equation
  simp only [body]
  -- Solve the decidable bool/nat equation
  decide +revert


/- Now what if we want to reason not on the whole module but on inner signals ?
   It's quite common to check properties of some inner signals rather than just the I/O.
   We can't write properties on the inner `let` inside the `def`,
   so we'd need to have an explicit `def` for them too.

   e.g. let's imagine we want to prove an SVA on inner signals, like :

   ```verilog
   a_i == 1'b0 && c_i = 1'b0 |-> r_o = c_i
   ```
-/

def wire.r (i : Inputs) : Bool := i.a ^^ i.b  ^^ i.c

/- SV module body -/
def body' (i : Inputs) : Outputs :=
  let r := wire.r i
  let c := i.a && i.b  || i.a && i.c || i.b && i.c
  ⟨r, c⟩

  /- Now we can talk about `r` -/
example : ∀ (i : Inputs), (not i.a) && (not i.c) → (i.b = (body' i).r) := by
  intro i
  cases i with | mk a b c =>
  simp only [body']
  decide +revert



namespace toto
-- Use `decide` for decidable propositions
-- For universally quantified things, it needs `Fintype α`
example (a b : Bool) : (a && b) = (b && a) := by
  try simp -- Simp won't work on boolean logic
  decide +revert -- But decide will do the job

-- Use `omega` for linear int/nat arithmetic
example (a b : Nat) (h : a ≤ b) : a + 3 ≤ b + 3 := by
  try decide -- decide won't deal with linear arithmetic
  omega -- but use omega for that

-- Use `ring` for polynomial/ring equalities
example (x y : Int) : (x + y)^2 = x^2 + 2*x*y + y^2 := by
  try omega
  ring

end toto

/-- Output of the 1-bit full adder: sum bit `res_o` and carry-out `c_o`. -/
structure FA.Out where
  res_o : Bool
  c_o   : Bool
  deriving Repr, DecidableEq

def fa (a b c : Bool) : FA.Out :=
  let r := a ^^ b  ^^ c
  let c' := a && b  || a && c || b && c
  ⟨r, c'⟩

/-- The 1-bit adder really computes `a + b + c`. -/
theorem fa_correct (a b c : Bool) :
    a.toNat + b.toNat + c.toNat
      = (fa a b c).res_o.toNat + 2 * (fa a b c).c_o.toNat := by
  decide +revert -- THis passes !! What's wrong with the first one ?

/- -------------------------------------------------------------------------------- -/
/- -------------------------------------------------------------------------------- -/
/- -------------------------------------------------------------------------------- -/

/-! ## N-bit ripple-carry adder -/

structure FAN.Params where
  N : Nat

structure FAN.In (p : FAN.Params) where
  a : BitVec p.N
  b : BitVec p.N
  c : BitVec p.N

-- /-- Output of the N-bit adder. -/
-- structure FAN.Out (p : FAN.Params) where
--   r : BitVec p.size
--   c : Bool


/-
  Finding a way to mimick the below SV code but with a big Lean function definition.
  So that we can reason on it using rfl/bv_decide.
  However the handling of the carry is where we're stuck.

  logic [N-1:0] ci;
  logic [N:0]   co;

  assign ci[0] = 1'b0;

  generate
    for k=0; k<N; k++ begin
      fa u_fa ( .c (ci[k])
              , .a (a[k])
              , .b (b[k])
              , .r (r[k])
              , .c'(co[k])
      );
    endfor

    for k=0+1; k<N+1; k++ begin
      assign ci[k] = co[k-1];
    endfor
  endgenerate
-/

def FAN.co
  (p : FAN.Params)
  (i : FAN.In p)
  (k : Nat)
  (k_bound : 0 ≤ k ∧ k < p.N)
  : Bool :=
  fa (i.a.getLsbD k) (i.b.getLsbD k) (FAN.ci.getLsbD k)

def FAN.ci (p : FAN.Params) (k : Nat)  : Bool :=
  if _h0 : k = 0 then
    false
  else if _h1 : k < p.N then
    FAN.co (k-1)
  else
    false




/-- The N-bit ripple-carry adder, built by chaining 1-bit full adders.
    The head bit is the LSB and is processed first; its carry-out is
    fed into the recursive call on the tail. -/
def fan : (n : Nat) → BitVec n → BitVec n → Bool → FAN.Out n :=
/-
  logic [N-1:0] ci;
  logic [N:0]   co;

  assign ci[0] = 1'b0;

  generate
    for k=0; k<N; k++ begin
      fa u_fa ( .c (ci[k])
              , .a (a[k])
              , .b (b[k])
              , .r (r[k])
              , .c'(co[k])
      );
    endfor

    for k=0+1; k<N+1; k++ begin
      assign ci[k] = co[k-1];
    endfor
  endgenerate

-/
  let out : BitVec n := 0x0
  let carry : BitVec (n+1) := 0x0
  -- What would the for generate module instantiation look like ?
  -- I guess for generate loop translate into 'map' in Lean i guess ?
  -- What about module instantiation ? function call ?
  sorry


/-
SV        |   Lean
& | ~     |   &&& ||| ~~~
struct    |   structure
enum      |   inductive
assign    |   def
module    |   namespaces and structures for signature ?
module instantiation | function evaluation
generate  |   k-indexing of inner assign
-/

def FAN.

def FAN.r (k : Nat) := fa FAN.







/-! ## Decomposition lemma

    The N-bit adder = (N-1)-bit adder feeding a 1-bit adder.

    The most useful form is usually a rewrite that exposes one call to
    `fa` (on the head bits) and one recursive call to `fan` (on the
    tails). Replace `True` below with whatever statement makes
    `fan_correct` go through cleanly. -/
theorem fan_split (n : Nat) (a b : BV (n+1)) (cin : Bool) :
    True := by   -- TODO: replace `True` with the real statement
  sorry


/-! ## Correctness of the N-bit adder

    Proof by induction on `n`, using `fa_correct` and `fan_split`. -/
theorem fan_correct (n : Nat) (a b : BV n) (cin : Bool) :
    a.toNat + b.toNat + cin.toNat
      = (fan n a b cin).res_o.toNat + 2^n * (fan n a b cin).c_o.toNat := by
  sorry

end Adder
