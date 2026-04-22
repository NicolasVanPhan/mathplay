
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

def TExpr.mk_range {w : Nat} {Γ : Context} (e : @TExpr Γ w) (hi lo : Nat)
  (hw : hi < w := by decide) (hle : lo ≤ hi := by decide) :=
  TExpr.range hi lo hw hle e

/- ---------------------------------------------------------------------------------------------- -/
-- Typer
/- ---------------------------------------------------------------------------------------------- -/

def infer (e : Expr) (Γ : Context) : Option (Sigma (fun w => TExpr Γ w)) :=
  match e with
  | @Expr.const w (val : Val w) =>
      some (Sigma.mk w (TExpr.const val))
  | Expr.ident (s : String) =>
      match h: Γ.get? s with
      | none => none
      | some w => some (Sigma.mk w (TExpr.ident s h))
  | Expr.concat e1 e2 =>
     let te1 := infer e1 Γ
     let te2 := infer e2 Γ
     match te1, te2 with
     | some ⟨w1, te1⟩, some ⟨w2, te2⟩ =>
       some ⟨w1 + w2, TExpr.concat te1 te2⟩
     | _, _ => none
  | Expr.range e hi lo => do
      match infer e Γ with
      | none => none
      | some ⟨w, te⟩ =>
        if hle : lo ≤ hi then
          if hw : hi < w then
            some ⟨hi - lo + 1, TExpr.range hi lo hw hle te⟩
          else none
        else none
  | Expr.and e1 e2 =>
     let te1 := infer e1 Γ
     let te2 := infer e2 Γ
     match te1, te2 with
     | some ⟨w1, te1⟩, some ⟨w2, te2⟩ =>
       if h : w1 = w2 then
         some ⟨w1, TExpr.and te1 (h ▸ te2)⟩
       else
         none
     | _, _ => none


/- ===============================================================================================-/
-- Evaluator
/- ===============================================================================================-/

def eval {Γ : Context} (e : @TExpr Γ n) : Val n :=
  open TExpr in
  match e with
  | TExpr.const v => v
  | @ident _ w _ _ => w
  | concat e1 e2 => (eval e1) ++ (eval e2)
  | range hi lo hw hle e => vec_range (eval e) hi lo hw hle
  | TExpr.and e1 e2 => (eval e1) &&& (eval e2)


/- Testing const and concat -/

def myctx : Context :=
  Context.empty
  |>.insert "a" 8
  |>.insert "b" 16

example : myctx.get? "a" = some 8 := by rfl
example : myctx.get? "z" = none := by rfl


def dead := TExpr.const (Γ := myctx) (0xdead#16)
def beef := TExpr.const (Γ := myctx) (0xbeef#16)

example : eval dead = 0xdead#16 := by rfl
example : eval beef = 0xbeef#16 := by rfl

example : eval (TExpr.concat dead beef) = 0xdeadbeef#32 := by rfl

#eval eval (TExpr.ident (Γ := ctx) "a" (by
  simp [ctx, Context.empty, Context.get?, Context.insert]; rfl
))


#eval BitVec.ushiftRight (eval dead) 8
#eval BitVec.truncate 8 (eval dead)


example : eval (TExpr.mk_range dead 15 8 ) = 0xde#8 := by decide
example : eval (TExpr.mk_range dead 15 8 ) = 0xde#8 := by decide

example : eval (TExpr.mk_range dead 7  0 ) = 0xad#8 := by decide
example : eval (TExpr.mk_range dead 11 4 ) = 0xea#8 := by decide
example : eval (TExpr.mk_range dead 0  0 ) = 0x1#1 := by decide

/- Testing and -/

def aval := TExpr.const (Γ := myctx) (0xff00#16)
def bval := TExpr.const (Γ := myctx) (0x00ff#16)
example : eval (TExpr.and dead dead) = 0xdead#16 := by rfl
example : eval (TExpr.and dead aval) = 0xde00#16 := by rfl
example : eval (TExpr.and dead bval) = 0x00ad#16 := by rfl
example : eval (TExpr.and aval bval) = 0x0000#16 := by rfl


end SV
