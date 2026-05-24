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
The `generate for` SV construct should map to which Lean construct ?

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
(The module instantiation is in essence equivalent to signal assignation.)


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
  -- First :
  -- 1. generate the 'range', [0, 1, 2, 3, ..., N-1, N], it should be finite
  -- 2. generate the b_rhs for a given element of the range
  -- 3. fold the whole thing to finally assign b
  let b_rhs := fun (k : Fin p.N) => i.a[k]
  let b : BitVec p.N :=
    -- Build your vector as a list of Bool
    let l : List Bool := List.ofFn b_rhs
    -- Concatenate them (there's the library built-in `ofBoolListLE`/`ofBoolListGE` for that)
    let bv := BitVec.ofBoolListLE l
    -- Justify BitVec l.length == BitVec p.N to the prover
    BitVec.cast (by simp [l]) bv
  ⟨b⟩

theorem v2.out_eq_in (p : Params) (i : In p) :
    (v2.body p i).b = i.a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i H_bound
  -- NOTE : strangely, `simp [v2.body, H] doesn't work here
  -- but `simp [v2.body] ; simp [H]` does
  simp [v2.body]
  simp [H_bound]


/-
```

IGNORE BELOW

From what we saw before, these two constructs lead to Lean definition and Lean function call.
With the `for generate` loop, these constucts are now :
- indexes by a parameter `k`, known at elaboration time
- replicated for a range over `k` (from `0` to `N-1` here)



-/

/-
  Finding a way to mimick the below SV code but with a big Lean function definition.
  So that we can reason on it using rfl/bv_decide.
  However the handling of the carry is where we're stuck.

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

-/
