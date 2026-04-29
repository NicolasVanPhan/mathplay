
import Mathlib
import Lean
import Std
open Lean
open Std

namespace SV

/- ---------------------------------------------------------------------------------------------- -/
-- Helpers
/- ---------------------------------------------------------------------------------------------- -/

abbrev Bit := Bool
abbrev Val := BitVec

def vec_range {w : Nat} (v : BitVec w) (hi lo : Nat)
  (_hi_lt_w : hi < w := by omega)
  (_hle : lo ≤ hi := by omega)
  : BitVec (hi - lo + 1) :=
  let v' := BitVec.ushiftRight v lo
  BitVec.truncate (hi - lo + 1) v'

example : vec_range 0xdeadbeef#32 23 8 = 0xadbe#16 := by rfl
example : vec_range 0xdeadbeef#32 31 0 = 0xdeadbeef#32 := by rfl
example : vec_range 0xdeadbeef#32 7 0  = 0xef#8 := by rfl
example : vec_range 0xdeadbeef#32 15 8 = 0xbe#8 := by rfl
example : vec_range 0xdeadbeef#32 0 0  = 0x1#1 := by rfl
example : vec_range 0xdeadbeef#32 4 4  = 0x0#1 := by rfl

/- ===============================================================================================-/
-- Untyped AST
/- ===============================================================================================-/

abbrev Width := Nat

/- ---------------------------------------------------------------------------------------------- -/
-- The AST
/- ---------------------------------------------------------------------------------------------- -/

inductive Expr : Type where
| const {w}   : Val w → Expr
| ident       : String → Expr
| concat      : Expr → Expr → Expr
| range       : Expr → (hi lo : Nat) → Expr
| and         : Expr → Expr → Expr
deriving Repr

/- ---------------------------------------------------------------------------------------------- -/
-- Notation
/- ---------------------------------------------------------------------------------------------- -/

declare_syntax_cat sv_scope
syntax ident : sv_scope
-- Constant: width#value (value can be decimal, 0xHEX, or 0bBIN)
syntax num "#" ident : sv_scope
syntax num "#" num : sv_scope
syntax num : sv_scope                                  -- Numeric constant
syntax sv_scope "[" num ":" num "]" : sv_scope         -- Range
syntax "{" sv_scope "," sv_scope "}" : sv_scope        -- Concat
syntax sv_scope "&" sv_scope : sv_scope                -- And

-- Toplevel wrapper
syntax "sv{" sv_scope "}" : term

partial def sv_parse : Syntax → MacroM (TSyntax `term) := fun stx =>
  match stx with
  /- Identifier -/
  | `(sv_scope| $id:ident) => do
      let s := Syntax.mkStrLit id.getId.toString
      `(Expr.ident $s)
  /- Constant with width: width#value -/
  | `(sv_scope| $w:num#$val:num) => do
      `(Expr.const (BitVec.ofNat $w $val))
  /- Constant with width and ident (for hex/binary): width#valueIdent -/
  | `(sv_scope| $w:num#$val:ident) => do
      -- Just use the ident directly as a Nat - Lean will parse 0xHEX and 0bBIN
      `(Expr.const (BitVec.ofNat $w ($val : Nat)))
  /- Range -/
  | `(sv_scope| $base:sv_scope[$hi:num:$lo:num]) => do
      let base' ← sv_parse base
      `(Expr.range $base' $hi $lo)
  /- Concat -/
  | `(sv_scope| { $x:sv_scope , $y:sv_scope }) => do
      let x' ← sv_parse x
      let y' ← sv_parse y
      `(Expr.concat $x' $y')
  /- And -/
  | `(sv_scope| $x:sv_scope & $y:sv_scope) => do
      let x' ← sv_parse x
      let y' ← sv_parse y
      `(Expr.and $x' $y')
  /- _ -/
  | _ => Macro.throwError s!"unexpected sv_scope syntax: {stx}"

macro_rules
| `(sv{ $e:sv_scope }) => sv_parse e

#eval sv{ tititi }
#eval sv{ foo[7:0] }
#eval sv{ foo[7:0][4:0] }
#eval sv{ {foo, bar} }
#eval sv{ {foo[3:0], bar[4:0]} }
#eval sv{ 8#240 }
#eval sv{ 8#240 & 8#240 }


-- Unit tests for notation
example : sv{ tititi } = Expr.ident "tititi" := by rfl
example : sv{ foo[7:0] } = Expr.range (SV.Expr.ident "foo") 7 0 := by rfl
example : sv{ foo[7:0][4:0] } = Expr.range (SV.Expr.range (SV.Expr.ident "foo") 7 0) 4 0 := by rfl
example : sv{ {foo, bar} } = Expr.concat (SV.Expr.ident "foo") (SV.Expr.ident "bar") := by rfl
example : sv{ foo & bar } = Expr.and (SV.Expr.ident "foo") (SV.Expr.ident "bar") := by rfl

/- Constants with convenience notation -/
-- Test: sv{ 8#240 } should be Expr.const (0xf0#8)
example : sv{ 8#240 } = Expr.const (240 : BitVec 8) := by rfl
example : sv{ 4#15 } = Expr.const (15 : BitVec 4) := by rfl
example : sv{ 8#240 & 8#240 } =
  Expr.and (Expr.const (240 : BitVec 8)) (Expr.const (240 : BitVec 8)) := by rfl

/- Hex and binary constants -/
-- 0xf0 = 240 in decimal
example : sv{ 8#0xf0 } = Expr.const (240 : BitVec 8) := by rfl
-- 0b11110000 = 240 in decimal
example : sv{ 8#0b11110000 } = Expr.const (240 : BitVec 8) := by rfl
-- 0xdeadbeef
example : sv{ 32#0xdeadbeef } = Expr.const (0xdeadbeef : BitVec 32) := by rfl

example : sv{ 8#0xf0 & a } = Expr.and (Expr.const (240 : BitVec 8)) (Expr.ident "a") := by rfl

/- ===============================================================================================-/
-- Typed AST
/- ===============================================================================================-/

/- ---------------------------------------------------------------------------------------------- -/
-- Context
--
-- We need to define a context type, a mapping from name to length
-- so we can determine the width of signals depending on previous signals' widths
/- ---------------------------------------------------------------------------------------------- -/

abbrev Context := List (String × Width)

def Context.empty : Context := []

def Context.get? (Γ : Context) (ident : String) : Option Width :=
  match Γ with
  | [] => none
  | (s, w) :: tl => if s == ident then some w else get? tl ident

def Context.insert (Γ : Context) (id : String) (w : Width) : Context :=
  (id, w) :: Γ

def ctx : Context := open Context in
  Context.empty
  |>.insert "a" 8
  |>.insert "b" 16

example : ctx.get? "a" = some 8 := by rfl
example : ctx.get? "z" = none := by rfl

/- ---------------------------------------------------------------------------------------------- -/
-- AST
/- ---------------------------------------------------------------------------------------------- -/

inductive TExpr (Γ : Context) : Nat → Type where
| const {w} : Val w → TExpr Γ w
| ident {w} : (s : String) → Γ.get? s = some w → TExpr Γ w
| concat : {w1 w2 : Nat} → TExpr Γ w1 → TExpr Γ w2 → TExpr Γ (w1 + w2)
| range : {w : Nat} → (hi lo : Nat)
    → (hw : hi < w)
    → (hle : lo ≤ hi)
    → TExpr Γ w → TExpr Γ (hi - lo + 1)
| and : {w : Nat} → TExpr Γ w → TExpr Γ w → TExpr Γ w
deriving Repr

def TExpr.mk_range {w : Nat} {Γ : Context} (e : @TExpr Γ w) (hi lo : Nat)
  (hw : hi < w := by decide) (hle : lo ≤ hi := by decide) :=
  TExpr.range hi lo hw hle e

/- ---------------------------------------------------------------------------------------------- -/
-- Typer
/- ---------------------------------------------------------------------------------------------- -/

/-- Compute output width from expression structure alone. -/
def inferWidth (Γ : Context) : Expr → Width
  | @Expr.const w _   => w
  | Expr.ident s      => (Γ.get? s).getD 0
  | Expr.concat e1 e2 => inferWidth Γ e1 + inferWidth Γ e2
  | Expr.range _ hi lo => hi - lo + 1
  | Expr.and e1 _     => inferWidth Γ e1

/-- Type inference: always returns a `TExpr` indexed by the inferred width.
    - Well-typed input  → correct typed AST.
    - Ill-typed input   → zero-constant junk (your theorem won't typecheck anyway). -/
def infer (Γ : Context) : (e : Expr) → TExpr Γ (inferWidth Γ e)
  | @Expr.const _ val => TExpr.const val
  | Expr.ident s =>
      match h : Γ.get? s with
      | some _ => by simp only [inferWidth, h]; exact TExpr.ident s h
      | none   => by simp only [inferWidth, h]; exact TExpr.const 0
  | Expr.concat e1 e2 =>
      TExpr.concat (infer Γ e1) (infer Γ e2)
  | Expr.range base hi lo =>
      if hle : lo ≤ hi then
        if hw : hi < inferWidth Γ base
        then TExpr.range hi lo hw hle (infer Γ base)
        else TExpr.const (0 : BitVec (hi - lo + 1))  -- junk for bad bounds
      else   TExpr.const (0 : BitVec (hi - lo + 1))  -- junk for lo > hi
  | Expr.and e1 e2 =>
      if h : inferWidth Γ e1 = inferWidth Γ e2
      then TExpr.and (infer Γ e1) (by rw [inferWidth, h]; exact infer Γ e2)
      else infer Γ e1  -- junk for width mismatch


/- ===============================================================================================-/
-- Evaluator
/- ===============================================================================================-/

-- A valuation assigns actual BitVec values to identifiers
abbrev Valuation (Γ : Context) := (s : String) → {w : Nat} → (h : Γ.get? s = some w) → Val w

def eval {Γ : Context} (val : Valuation Γ) (e : @TExpr Γ n) : Val n :=
  open TExpr in
  match e with
  | TExpr.const v => v
  | @ident _ w s h => val s h
  | concat e1 e2 => (eval val e1) ++ (eval val e2)
  | range hi lo hw hle e => vec_range (eval val e) hi lo hw hle
  | TExpr.and e1 e2 => (eval val e1) &&& (eval val e2)


/- Testing const and concat -/

def myctx : Context :=
  Context.empty
  |>.insert "a" 8
  |>.insert "b" 16

example : myctx.get? "a" = some 8 := by rfl
example : myctx.get? "z" = none := by rfl


def dead := TExpr.const (Γ := myctx) (0xdead#16)
def beef := TExpr.const (Γ := myctx) (0xbeef#16)

-- Create a simple valuation for myctx
def myValuation : Valuation myctx := fun s {w} h => by
  -- h : myctx.get? s = some w
  -- We need to determine w from the fact that s is in myctx
  dsimp only [myctx, Context.empty, Context.get?, Context.insert] at h
  -- Now h should be a concrete conditional we can split on
  split at h
  · -- First case: "b" = s, so w = 16
    injection h with eq_w
    exact eq_w ▸ (0xbbbb : BitVec 16)
  · -- Second case: "b" != s, so need to check "a" = s
    split at h
    · -- When "a" = s, so w = 8
      injection h with eq_w
      exact eq_w ▸ (0xaa : BitVec 8)
    · -- Neither "a" nor "b" matches
      cases h

example : eval myValuation dead = 0xdead#16 := by rfl
example : eval myValuation beef = 0xbeef#16 := by rfl

example : eval myValuation (TExpr.concat dead beef) = 0xdeadbeef#32 := by rfl

-- Test with the existing ctx which maps "a" to 8 bits
def ctx_val : Valuation ctx := fun s {w} h => by
  dsimp only [ctx, Context.empty, Context.get?, Context.insert] at h
  -- First split handles the outer if on "b" = s
  split at h
  · -- When "b" = s, h : some 16 = some w
    injection h with eq_w
    exact eq_w ▸ (0xbbbb : BitVec 16)
  · -- When "b" != s, h : (if "a" = s then some 8 else none) = some w
    -- Split again to handle the inner if on "a" = s
    split at h
    · -- When "a" = s, h : some 8 = some w
      injection h with eq_w
      exact eq_w ▸ (0xaa : BitVec 8)
    · -- When "a" != s either, h : none = some w (impossible)
      cases h

#eval eval ctx_val (TExpr.ident (Γ := ctx) "a" (by
  simp [ctx, Context.empty, Context.get?, Context.insert]; rfl
))

-- Test range extraction
example : eval myValuation (TExpr.mk_range dead 15 8 ) = 0xde#8 := by decide
example : eval myValuation (TExpr.mk_range dead 7  0 ) = 0xad#8 := by decide
example : eval myValuation (TExpr.mk_range dead 11 4 ) = 0xea#8 := by decide
example : eval myValuation (TExpr.mk_range dead 0  0 ) = 0x1#1 := by decide

/- Testing and -/

def aval := TExpr.const (Γ := myctx) (0xff00#16)
def bval := TExpr.const (Γ := myctx) (0x00ff#16)
example : eval myValuation (TExpr.and dead dead) = 0xdead#16 := by rfl
example : eval myValuation (TExpr.and dead aval) = 0xde00#16 := by rfl
example : eval myValuation (TExpr.and dead bval) = 0x00ad#16 := by rfl
example : eval myValuation (TExpr.and aval bval) = 0x0000#16 := by rfl


/- ===============================================================================================-/
-- Proof: trivial_circuit always outputs 0
/- ===============================================================================================-/

def trivial_circuit := sv{ 8#0x0f & a & 8#0xf0 }

theorem trivial_circuit_always_zero :
    ∀ (val : Valuation myctx), eval val (infer myctx trivial_circuit) = 0x00#8 := by
  intro val
  -- `infer myctx trivial_circuit` reduces definitionally; expose the bitvector goal
  -- TODO : Put this automatically so we don't need to mention them in simp
  simp [infer, myctx, trivial_circuit, inferWidth, Context.empty, Context.insert, Context.get?]
  simp [eval]
  -- TODO : Fix warning on bv_decide
  bv_decide



end SV
