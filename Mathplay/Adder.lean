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
  It doesn't reason on an abstract size `N` but a concrete value (e.g. `4`),
  bruteforcing its way to prove results on 4-bit signals.
  The proof for a 2048-bits adder will be longer than for a 4-bit adder,
  becuase there is more logic involved.
  It's a shame, because **the reasoning does not depend on the size**.
  The size and complexity of the proof on adder correctness is independent of its size.
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

  If we manage that, we could then imagine writing a small DSL almost equal to SystemVerilog,
  from which we could generate both SystemVerilog and Lean4 definitions to reason about.

  With that in mind, we won't just describe an adder in Lean, we'll explore how an adder
  originally described in typical SystemVerilog constructs
  could be systematically mapped to Lean constructs,
  thus preparing the ground for a quasi-SystemVerilog DSL that would trivially generate SV
  and - thanks to the explored constructs mapping - generate a Lean description.

  TODO : At the end, explain that we showed an example of 'structural' induction
  but there's another common room for optimization which is 'temporal' induction.
  e.g. COM proofs by induction on incoming event.
  Brainstorm a mini-COM example showing the scaling difference

-/


/-! ## 1-bit full adder -/

/-
We'll start with a tiny circuit : a 1-bit full adder

Its truth table is describe below :
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
deriving Repr, DecidableEq, Fintype

/- SV module output declaration -/
structure Outputs where
  r : Bool
  c : Bool
deriving Repr, DecidableEq, Fintype

/- SV module body -/
def v1.body (i : Inputs) : Outputs :=
  let r := i.a ^^ i.b  ^^ i.c
  let c := i.a && i.b  || i.a && i.c || i.b && i.c
  ⟨r, c⟩

/- Proof : The 1-bit adder really computes `a + b + c`. -/
theorem adder_correct (i : Inputs) :
  let a := i.a.toNat
  let b := i.b.toNat
  let ci := i.c.toNat
  let r := (v1.body i).r.toNat
  let co := (v1.body i).c.toNat
  a + b + ci = r + 2 * co := by
  -- Break i into its components (a b c)
  cases i with | mk a b c =>
  -- Normalize the expression to the shortest boolean equation
  simp only [v1.body]
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

   In that case, instead of letting it hidden in a `let` inside `def body ...`
   we can write an explicit `def r...`.
   All definitions like this, corresponding to a SV module's internal wires,
   can be put in a `wire` namespace for clarify.
   So we have `def wire.r ...`
-/

def wire.r (i : Inputs) : Bool := i.a ^^ i.b  ^^ i.c

/- SV module body -/
def v2.body (i : Inputs) : Outputs :=
  let r := wire.r i
  let c := i.a && i.b  || i.a && i.c || i.b && i.c
  ⟨r, c⟩

/- Now we reason about `r` -/
example : ∀ (i : Inputs), (not i.a) && (not i.c) → (i.b = (v2.body i).r) := by
  intro i
  cases i with | mk a b c =>
  simp only [v2.body]
  decide +revert

/- And the proof still holds -/
theorem v2.adder_correct (i : Inputs) :
  let a := i.a.toNat
  let b := i.b.toNat
  let ci := i.c.toNat
  let r := (v2.body i).r.toNat
  let co := (v2.body i).c.toNat
  a + b + ci = r + 2 * co := by
  -- Break i into its components (a b c)
  cases i with | mk a b c =>
  -- Normalize the expression to the shortest boolean equation
  simp only [v2.body]
  -- Solve the decidable bool/nat equation
  decide +revert

-- For later use, let's pick the first version
def body := v1.body

end Adder_1bit

/- -------------------------------------------------------------------------------- -/
/- -------------------------------------------------------------------------------- -/
/- -------------------------------------------------------------------------------- -/

/-! ## 4-bit ripple-carry adder

Before going to the N-bit adder, let's consider the particular instance N=4,
to highlight how the 1-bit adders are chained.
We won't introduce `N` as a parameter for now, we'll do that in next section.
For now let's just have a small several-bits adder and prove it.

In SystemVerilog, we'll could write the 4-bits adder as follows

```
module adder_4bit (
  input  logic [3:0]  a_i;
  input  logic [3:0]  b_i;
  output logic [3:0]  r_o;
  output logic        c_o;
)

  logic [4:0]  c;

  assign ci[0] = 1'b0;

  adder_1bit  u_add_b0 ( .c (c[0]) , .a (a_i[0]) , .b (b_i[0]) , .r (r_o[0]) , .c'(c[1]));
  adder_1bit  u_add_b1 ( .c (c[1]) , .a (a_i[1]) , .b (b_i[1]) , .r (r_o[1]) , .c'(c[2]));
  adder_2bit  u_add_b2 ( .c (c[2]) , .a (a_i[2]) , .b (b_i[2]) , .r (r_o[2]) , .c'(c[3]));
  adder_3bit  u_add_b3 ( .c (c[3]) , .a (a_i[3]) , .b (b_i[3]) , .r (r_o[3]) , .c'(c[4]));

  assign c_o = c[4];

endmodule
```
-/

namespace Adder_4bits

/- Equivalent of a SystemVerilog parameter declaration -/
structure Params where
  N : Nat

/- And its value -/
def params : Params where
  N := 4

/- Equivalent of a SystemVerilog module I/O declaration -/
structure Inputs where
  a : BitVec params.N
  b : BitVec params.N
deriving Repr, DecidableEq

/- SV module output declaration -/
structure Outputs where
  r : BitVec params.N
  c : Bool
deriving Repr, DecidableEq

def body (i : Inputs) : Outputs :=
  -- Hardwiring first carry bit to 0
  let c0 := 0
  -- Instantiating the 4 1-bit adder modules and propagating the carry
  let ⟨ r0 , c1 ⟩ := Adder_1bit.body ⟨ i.a.getLsbD 0, i.b.getLsbD 0, c0 ⟩
  let ⟨ r1 , c2 ⟩ := Adder_1bit.body ⟨ i.a.getLsbD 1, i.b.getLsbD 1, c1 ⟩
  let ⟨ r2 , c3 ⟩ := Adder_1bit.body ⟨ i.a.getLsbD 2, i.b.getLsbD 2, c2 ⟩
  let ⟨ r3 , c4 ⟩ := Adder_1bit.body ⟨ i.a.getLsbD 3, i.b.getLsbD 3, c3 ⟩
  -- Forge outputs
  let r := BitVec.cons r3 (BitVec.cons r2 (BitVec.cons r1 (BitVec.cons r0 0#0)))
  let c := c4
  ⟨r, c⟩

theorem v2.adder_correct (i : Inputs) :
  let a := i.a.toNat
  let b := i.b.toNat
  let r := (body i).r.toNat
  let c := (body i).c.toNat
  a + b == r + (2 ^ params.N) * c := by
  cases i with | mk a b =>
  simp only [body, Adder_1bit.body, Adder_1bit.v1.body, params]
  decide +revert

theorem v2.adder_correct_alt (i : Inputs) :
  BitVec.cons (body i).c (body i).r
    =
  (BitVec.zeroExtend (params.N + 1) i.a)
    +
  (BitVec.zeroExtend (params.N + 1) i.b) := by
  cases i with | mk a b =>
  simp only [body]
  decide +revert

end Adder_4bits

/- -------------------------------------------------------------------------------- -/
/- -------------------------------------------------------------------------------- -/
/- -------------------------------------------------------------------------------- -/


/-! ## Interlude : Range assignment
Before we can jump to the N-bit adder, we'll need to see how to map indexed signals.

The idea is :
If a SV signal maps to a Lean definition
An indexed signal maps to an indexed Lean definition.
`logic [N-1:0] c = ...;` ↔ `def c (k : Fin N) := ...`

The SV range selection simply maps to `c` function call :
`assign toto = c[42];` ↔ `def toto := c 42`

Problem 1 :
The main problem will be, how to generate `def c` ?
In general, assignment of `c` will be scattered across the code.
While Lean needs a single grouped definition for `c`.
The compiler will need to gather the spread assignments

```
assign c[0] = 1'b0; // assignment of some range
/* some code... then later on :*/
assign c[N-1:1] = 0xdeadbeef; // assignment of another range
```

Problem 2 :
2.1. Assigned ranges need to form a partition of the whole range.
```
assign c[2:0] = ...;
assign c[4:1] = ...;
```
Is incorrect as it concurrently drives `c[2:1]` twice.

2.2. Also we want to be sure all bits are assigned.
```
assign c[N-1:1] = 0xdeadbeef;
```
There is no driver for `c[0]`.

We could imagine the compiler to gather range assignment,
generate a description of all ranges `k_range1`, `k_range2` etc.
Also generate the range of the whole signal `k_range_whole` as ⟦0:N-1⟧.

Then generate a proof that :
- union of the ranges form the whole range (solves 2.2)
- intersection of any two ranges is empty (solves 2.1)
As we're staying in linear algebra here, such proofs
should easily be automated with `omega`.

Now the definition for `c` should look ideally like below :

```lean
def c (k : Fin N) :=
  match k with
  | /* range 1 */ => c_rhs1 k
  | /* range 2 */ => c_rhs2 k
  | /* ... */
  | /* range n */ => c_rhs2 n
```

Below is an attempt at reproducing this,
while we couldn't reach this exact form,
the result is pretty much similar.

We'll work on a dummy example, multiplying a value by 2,
which is trivally done by right-shifting the bit vector.

-/

namespace Mult2

/- Equivalent of a SystemVerilog parameter declaration -/
structure Params where
  N : Nat

/- And its value -/
def params : Params where
  N := 4

/- Equivalent of a SystemVerilog module I/O declaration -/
structure Inputs where
  n : BitVec params.N
deriving Repr, DecidableEq

/- SV module output declaration -/
structure Outputs where
  n : BitVec (params.N + 1)
deriving Repr, DecidableEq

/-
module Mult2 (
input  logic [N-1:0] n_i
output logic [N:0]   n_o
)
  logic [N:0] n;
  assign n[0]   = 1'b0;
  assign n[N:1] = n_i[N-1:0];
  assign n_o    = n;
endmodule

The internal signal `n` is an SV indexed signal, driven by *two* separate
`assign` statements on disjoint sub-ranges :
  - n[0]   = 0
  - n[N:1] = n_i[N-1:0]

Following the principle :
    SV indexed signal = Lean indexed function
the wire `n` becomes a Lean function
    `n : Inputs → Fin (N+1) → Bool`

When several `assign` statements drive disjoint sub-ranges of the same signal,
we map each `assign` to its own rhs function defined on the relevant sub-range
(modeled as a subtype of the whole index range), then combine all the per-range
rhs into the single indexed function.

For the construct to make sense, the sub-ranges must form a *partition* of the
whole range — we prove that explicitly below.
-/

/- ------------------------------------------------------------------ -/
/- 1. Whole range and per-`assign` sub-range predicates                -/
/- ------------------------------------------------------------------ -/

/- The whole index range of `n` (SV `logic [N:0] n;` → N+1 indices) -/
abbrev k_whole : Type := Fin (params.N + 1)

/- One predicate per SV `assign` describing the sub-range it covers.
   These predicates are the *single source of truth* for the ranges :
   every subtype, theorem and dispatch below derives from them. -/
abbrev range1 (k : k_whole) : Prop := 0 ≤ k.val ∧ k.val ≤ 0        -- SV `[0:0]`
abbrev range2 (k : k_whole) : Prop := 1 ≤ k.val ∧ k.val ≤ params.N -- SV `[N:1]`

/- Sub-range types - derived from the predicates -/
abbrev k_range1 : Type := { k : k_whole // range1 k }
abbrev k_range2 : Type := { k : k_whole // range2 k }

/- ------------------------------------------------------------------ -/
/- 2. Partition proofs - referencing only the predicates above         -/
/- ------------------------------------------------------------------ -/

/- 1. The ranges cover the whole index space -/
theorem k_range_cover (k : k_whole) : range1 k ∨ range2 k := by omega
/- 2. The ranges are pairwise disjoint -/
theorem k_range_disjoint (k : k_whole) : ¬ (range1 k ∧ range2 k) := by omega

/- ------------------------------------------------------------------ -/
/- 3. Per-`assign` rhs functions - one Lean def per SV `assign`        -/
/- ------------------------------------------------------------------ -/

/- RHS for `assign n[0] = 1'b0;` -/
def n_rhs1 (_k : k_range1) : Bool := false

/- RHS for `assign n[k] = n_i[k-1];` (for k in [1, N]) -/
def n_rhs2 (i : Inputs) (k : k_range2) : Bool :=
  i.n.getLsbD (k.val.val - 1)

/- ------------------------------------------------------------------ -/
/- 4. Dispatch & assembly into the indexed signal                      -/
/- ------------------------------------------------------------------ -/

/-
The grail for the assembly would be a syntax like :
    match k with
    | k in range1 => n_rhs1 k
    | k in range2 => n_rhs2 i k
Lean doesn't have that directly, but we can recover it cleanly by tagging
every `k` with evidence of *which* range it falls into, then matching on
the tag. The pattern scales to any number of ranges of any shape :
  - add one predicate `range_i` to (1)
  - extend the partition proofs in (2)
  - add one rhs `n_rhs_i` to (3)
  - add one constructor / arm to `RangeMatch` / `range_of` / `n` below.
-/

/- Tagged disjoint union of all sub-range subtypes - one constructor per range -/
inductive RangeMatch : Type
  | r1 : k_range1 → RangeMatch
  | r2 : k_range2 → RangeMatch

/- Dispatch : determines which range each `k` belongs to.
   Mechanical : one dependent-if per range, with the trailing `else` discharged
   by `k_range_cover` (the partition guarantees the chain is exhaustive). -/
def range_of (k : k_whole) : RangeMatch :=
  if h : range1 k
    then .r1 ⟨k, h⟩
    else .r2 ⟨k, (k_range_cover k).resolve_left h⟩

/- The indexed signal - one rhs call per range arm.
   Reads exactly like the "match k in range_i => rhs_i" form we wanted. -/
def n (i : Inputs) (k : k_whole) : Bool :=
  match range_of k with
  | .r1 k => n_rhs1 k
  | .r2 k => n_rhs2 i k

/- The module body : `assign n_o = n;` — drive the output bit-by-bit from `n`.
   `BitVec.ofFnLE` (from Batteries) is the generic indexed-function-to-BitVec
   converter : `(f : Fin n → Bool) → BitVec n`, little-endian (so `f 0` is LSB),
   which is exactly the convention `n` follows. -/
def body (i : Inputs) : Outputs :=
  ⟨BitVec.ofFnLE (n i)⟩

/- Behavioural correctness : the module doubles its input. -/
theorem out_is_2x_in (i : Inputs) :
    (body i).n.toNat = 2 * i.n.toNat := by
  cases i with | mk n_in =>
  decide +revert

end Mult2




/- -------------------------------------------------------------------------------- -/
/- -------------------------------------------------------------------------------- -/
/- -------------------------------------------------------------------------------- -/




/-! ## N-bit ripple-carry adder

Alright, we saw how 1-bit adders compose to form a several-bit adder.
But we took 4 as a hardcoded value (there are 4 calls in above `body`)
Of course we want to replace that with a more generic N-bit adder.

First, here's what we'd like to map :

```
module adder_4bit (
#( parameter int N )
( input  logic [N-1:0]  a_i;
  input  logic [N-1:0]  b_i;
  output logic [N-1:0]  r_o;
  output logic          c_o;
)
  logic [N:0]   c;

  assign ci[0] = 1'b0;

  generate
    for k=0; k<N; k++ begin
      adder_1bit u_add1
      ( .c (c[k])
      , .a (a[k])
      , .b (b[k])
      , .r (r[k])
      , .c'(c[k+1])
      );
    endfor
  endgenerate

  assign c_o = c[N];
endmodule
```

-/

namespace Adder_Nbits

/-

### Handling SV module parameters
The module I/O definition doesn't change much,
the main addition is the parameter, which becomes an input
to other constructs (`In`/`Out`/`body` etc.)
-/
structure Params where
  N : Nat

structure In (p : Params) where
  a : BitVec p.N
  b : BitVec p.N
  c : BitVec p.N

/-- Output of the N-bit adder. -/
structure Out (p : Params) where
  r : BitVec p.N
  c : Bool

/- Now for the body, the main question is,
Which Lean construct should the `generate for` SV construct should map to ?

First let's look at what we have inside the loop body :
- SV module instantiation
- SV assign

More generally, what we want to map is :
```
generate
  for (k = X, k < Y, k++)
    assign some_sig[f(k)] = some_SV_expr(k)
  end
endgenerate
```
The module instantiation is in essence equivalent to signal assignation.
You feed a bunch of signals with the module's output.
And you feed the module's input with another bunch of signals.

assign outputs = f_module inputs


### Handling SV generate-for loops

Let's take a trivial use of `for` loops
and see how it could systematically translate to Lean.

```
module toto
#(parameter int N)
( input logic [N-1:0] a_i
, input logic [N-1:0] b_o
);

// Should be equivalent to 'assign b_o = a_i;'
generate
  for (k = 0, k < N, k++)
    assign b_o[k] = a_i[k];
  end
endgenerate

endmodule
```
-/

namespace Toto

structure Params where
  N : Nat

structure In (p : Params) where
  a : BitVec p.N

/-- Output of the N-bit adder. -/
structure Out (p : Params) where
  b : BitVec p.N

-- `assign o = i;` maps to :
def v1.body (p : Params) (i : In p) : Out p :=
  let b := i.a
  ⟨b⟩

-- And the proof that output == input is really trivial
theorem v1.out_eq_in (p : Params) (i : In p) :
  let o := v1.body p i
  o.b = i.a := by rfl

-- Now for the `generate-for` could map to :
def v2.body (p : Params) (i : In p) : Out p :=
  -- The assignment of 'b' now depend on index 'k' so the trivial mapping is a function,
  -- `b` is not just a variable but a function taking `k` as a parameter.
  -- and the range of `k` is embedded in its type (0 to N)
  --
  -- We could introduce a `k` parameter of type ℕ but there are two problems with that :
  -- 1. We lose the notion of bounds (we must ask for a proof of `k ≤ N`)
  -- 2. The `decide` works better with finite types
  -- So instead, we'll use the `Fin` type family)
  -- `Fin 42` represents the set of naturals between `0` and `41`,
  -- it embeds the bounds in the type and is `decide`-friendly.
  -- It works in 3 steps :
  --
  -- 1. declare the 'range', [0, 1, 2, 3, ..., N-1, N].
  let b_range := Fin p.N
  -- 2. declare `b_rhs` - the expression to assign to `b`, function of `k`.
  let b_rhs := fun (k : b_range) => i.a[k]
  -- 3. Drive `b` - fold `b_rhs` over `Fin N` to assign all bits of `b`.
  let b : BitVec p.N :=
    -- List.ofFn evaluates the `b_rhs` function
    -- with each element of `b_range`
    -- and yields all the results in a `List`.
    -- e.g. `List.ofFn (fun (k : Fin 3) => f k)`
    -- produces `[f 3, f 2, f 1, f 0]`
    let l : List Bool := List.ofFn b_rhs
    -- Concatenate them
    let bv : BitVec l.length := BitVec.ofBoolListLE l
    -- This boilerplate cast is needed
    -- to justify `BitVec l.length == BitVec p.N` to the prover
    BitVec.cast (by simp [l]) bv
  ⟨b⟩

-- And the proof that the second module behaves as the first
theorem v2.out_eq_in (p : Params) (i : In p) :
    (v2.body p i).b = i.a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i H_bound
  -- NOTE : strangely, `simp [v2.body, H] doesn't work here
  -- but `simp [v2.body] ; simp [H]` does
  simp [v2.body]
  simp [H_bound]

end Toto


/-

TODO : Graph with adder 1-bit modules showing the need for recursion.
TODO : What about mutually recursive modules ??
       Can we avoid mutually recursive functions ?

In principle, there are no combinational loops, so no infinite recursive calls.
However we'd need to justify that to the prover.


         +--------+
   a0--->|a      r|---->  r0
   b0--->|b       |
   c0--->|ci    co|---+>
         +--------+   |
                      |
 +--------------------+
 |       +--------+
 | a1--->|a      r|---->  r1
 | b1--->|b       |
 +-c1--->|ci    co|---+>
         +--------+   |
                      |
 +--------------------+
 |       +--------+
 | a2--->|a      r|---->  r2
 | b2--->|b       |
 +-c2--->|ci    co|---->
         +--------+

Here, we see that (add_1bit 2) calls (add_1bit 1), which itself calls (add_1bit 0).
So we cannot get our way with a `map` only.

The module instances `k` needs the input carry `k`,
and the input carry `k` needs the module instance `k-1`,
there's a mutual recursive pattern here so we'll map it to mutually recursive `def`s.

-/
mutual

-- module instantiation : performs `r[k] := u_add1.r` and `c[k+1] := u_add1.c`
def v1.u_add1 (p : Params) (i : In p) (k : Fin p.N) : Adder_1bit.Outputs :=
  Adder_1bit.body ⟨i.a[k], i.b[k], v1.ci p i k.castSucc⟩

-- carry signal : combines `assign c[0] := 1'b0` and `c[k+1] := u_add1[k].c`.
-- Indexed by `Fin (p.N + 1)` because `c` has `N+1` bits (0 to N).
def v1.ci (p : Params) (i : In p) (k : Fin (p.N + 1)) : Bool :=
  match k with
  | ⟨0, _⟩ => false
  | ⟨n+1, h⟩ => (v1.u_add1 p i ⟨n, by omega⟩).c

end

def v1.body (p : Params) (i : In p) : Out p :=
  -- generate-for: for k in [0, N), assign `r[k] := u_add1[k].r`
  let r : BitVec p.N :=
    let r_rhs := fun (k : Fin p.N) => (v1.u_add1 p i k).r
    let l : List Bool := List.ofFn r_rhs
    let bv : BitVec l.length := BitVec.ofBoolListLE l
    BitVec.cast (by simp [l]) bv
  -- assign c_o := c[N]
  let c : Bool := v1.ci p i (Fin.last p.N)
  ⟨r, c⟩


/-
Fundamentally :
It's the `c` assignment that is a `scan`
c 0 = 0
c k = f_add(a k-1, b k-1, c k-1).c
Then the `r` assignment is just a classic function call, a call to the recursive `c` function
r k = f_add(a k, b k, c k).r

-/

-- carry signal : combines `assign c[0] := 1'b0` and `c[k+1] := u_add1[k].c`.
-- Indexed by `Fin (p.N + 1)` because `c` has `N+1` bits (0 to N).
def v1.c (p : Params) (i : In p) (k : Fin (p.N + 1)) : Bool :=
  match k with
  | ⟨0, _⟩  /- ⟨range 0:0, H_proof_it_is_in_0:0 -/ => false
  | ⟨k, H⟩  /- ⟨range 1:p.N, H_proof_it_is_in_1:p.N -/ =>
    let u_add1 (p : Params) (i : In p) (k : Fin p.N) : Adder_1bit.Outputs :=
      Adder_1bit.body ⟨i.a[k], i.b[k], v1.ci p i k.castSucc⟩
    (v1.u_add1 p i ⟨k, by omega⟩).c





/-

This style works but there's a some logic that is not
mechanically generatable for a transpiler :
- the `k.castSucc`
- the `match k with 0, n+1..`
- the `Fin.last` too

The problem is that Lean fundamentally needs to know about
cross-instances calls (for a termination guarantee)
while SV doesn't provide that at all.
So we can't bring more information during transpilation.

The other solution is to ask the use for that information upfront :
- for independent loops : a DSL `map` will lead to a Lean `map`
- for cascaded loops (like here ): a DSL `scan` will lead to a Lean `scan/fold`
  The `scan` will be like a `map` but with memory, where instance `k`
  can access information from previous instances (`0..k-1`)
- for arbitrary dependent loops : Can't guarantee there's no combinatory loops, forbid.

The adder DSL code would look like :

```
scan k in 0..N
  state c : Bool init false
  output r[k] : Bool
  step:
    let fa = add_1bit(a[k], b[k], c)
    r[k] := fa.r
    c    := fa.c
return r, c
```


One thing is, if we want the freedom to assign c[0] and c[k] (1<k<N) separately,
- we need either partial functions (but not proof friendly at all so it's a no go)
- or we need the transpiler to gather the various assigned ranges
  into a single function assigning `c`, not transpiler friendly.
- or we constrain the user to define the whole range in a single block, not user friendly.


```
Fundamentally :
It's the `c` assignment that is a `scan`
c 0 = 0
c k = f_add(a k-1, b k-1, c k-1).c
Then the `r` assignment is just a classic function call, a call to the recursive `c` function
r k = f_add(a k, b k, c k).r
```

```
module adder_4bit (
#( parameter int N )
( input  logic [N-1:0]  a_i;
  input  logic [N-1:0]  b_i;
  output logic [N-1:0]  r_o;
  output logic          c_o;
)
  logic [N:0]   c;

  generate
    // mechanical module instantiation
    // it's the assignment of all o_xxx signals
    for k=0; k<N; k++ begin
      i_c[k] = c[k];
      i_a[k] = a[k];
      i_b[k] = b[k];
      adder_1bit u_add1
      ( .c (i_c[k])
      , .a (i_a[k])
      , .b (i_b[k])
      , .r (o_r[k])
      , .c'(o_c[k])
      );
    endfor

    // driving of c
    assign ci[0] = 1'b0;
    for k=1; k<N+1; k++ begin
      assign ci[k] = o_c[k-1];
    enfor

    // driving of r output
    for k=0; k<N; k++ begin
      r[k] = o_r[k];
    endfor

    // driving of c output
    assign c_o = c[N];

  endgenerate

endmodule
```

It seems to me the main difficulty here is information gain/loss.
I want my DSL to be as close as possible to SV, while being able to transpile to proof-friendly Lean code.

But in terms of information expressed in the code, SV has less than proof-friendly Lean.
1. SV description just loops and plug wires together
2. Lean description explicits inter-instance dependencies and the recursion scheme at play (map, scan, arbitrary)

Going from 2. to 1. involves a loss of information, no problem at all, we just map all the recursion schemes to a generate-for
Going from 1. to 2. is the problem. We need to get the information somewhere :
- either upfront (asking the user for an explicit scheme)
- midway, inferring it in the transpiler (which is not trivial at all)
- downstream, getting a raw Lean description and manually proving it equivalent to an abstract scan/fold etc.

I think I've hit a key problem for this kind of projects.
Here I mention retrieving the 'map/scan/fold' structure but the problem applies much more broadly,
we need to reconstruct the proof-relevant abstraction boundary to get a proof-friendly Lean code.

The real problem is not transpilation, but abstraction recovery.
SV and Lean are not just two different syntaxes for the same object, they encourage two different notions for what the object is.
SV is used to elaborate HW, it just wants to know the netlist connections.
Lean is used for proofs (at least that's the goal), it needs extra information on the design's symmetries (here, the recursion scheme at play) to enable smooth proof automation.

The SV->Lean transpilation is a decompilation problem, it requires to recover a high-level explanation from a low level structural description.

This is the central danger for this DSL project.
If it is too close to SV, it may be comfortable for hardware designers but impoverished for proofs.
If it is too close to Lean, it may be elegant for theorem proving but alien to hardware designers.
The project lives exactly in that tension.

Transpiling isn't the right word, it makes it look like a syntax-only problem.
The real deal is recovering *structure* absent from SV and needed for proofs.



-/
