
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

/- ---------------------------------------------------------------------------------------------- -/
-- Untyped AST
/- ---------------------------------------------------------------------------------------------- -/

abbrev Width := Nat

inductive Expr : Type where
| const {w}   : Val w → Expr
| ident       : String → Expr
| concat      : Expr → Expr → Expr
| range       : Expr → (hi lo : Nat) → Expr


declare_syntax_cat sv_scope
syntax ident : sv_scope
-- Range
syntax sv_scope "[" num ":" num "]" : sv_scope
-- Toplevel wrapper
syntax "sv{" sv_scope "}" : term

partial def sv_parse : Syntax → MacroM (TSyntax `term) := fun stx =>
  match stx with
  /- Identifier -/
  | `(sv_scope| $id:ident) => do
      let s := Syntax.mkStrLit id.getId.toString
      `(Expr.ident $s)
  /- Range -/
  | `(sv_scope| $base:sv_scope[$hi:num:$lo:num]) => do
      let base' ← sv_parse base
      `(Expr.range $base' $hi $lo)
  /- _ -/
  | _ => Macro.throwError s!"unexpected sv_scope syntax: {stx}"

macro_rules
| `(sv{ $e:sv_scope }) => sv_parse e

#eval sv{ tititi }
#eval sv{ foo[7:0] }
#eval sv{ foo[7:0][4:0] }


example : sv{ tititi } = Expr.ident "tititi" := by rfl
example : sv{ foo[7:0] } = Expr.range (SV.Expr.ident "foo") 7 0 := by rfl
example : sv{ foo[7:0][4:0] } = Expr.range (SV.Expr.range (SV.Expr.ident "foo") 7 0) 4 0 := by rfl


/- ---------------------------------------------------------------------------------------------- -/
-- Typed AST
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

inductive TExpr (Γ : Context) : Nat → Type where
| const {w} : Val w → TExpr Γ w
| ident {w} : (s : String) → Γ.get? s = some w → TExpr Γ w
| concat : {w1 w2 : Nat} → TExpr Γ w1 → TExpr Γ w2 → TExpr Γ (w1 + w2)
| range : {w : Nat} → (hi lo : Nat)
    → (hw : hi < w)
    → (hle : lo ≤ hi)
    → TExpr Γ w → TExpr Γ (hi - lo + 1)

def TExpr.mk_range {w : Nat} {Γ : Context} (e : @TExpr Γ w) (hi lo : Nat)
  (hw : hi < w := by decide) (hle : lo ≤ hi := by decide) :=
  TExpr.range hi lo hw hle e


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
  | Expr.range e hi lo =>
      match infer e Γ with
      | none => none
      | some ⟨w, te⟩ =>
        if hle : lo ≤ hi then
          if hw : hi < w then
            some ⟨hi - lo + 1, TExpr.range hi lo hw hle te⟩
          else none
        else none


/- ---------------------------------------------------------------------------------------------- -/


def eval {Γ : Context} (e : @TExpr Γ n) : Val n :=
  open TExpr in
  match e with
  | TExpr.const v => v
  | @ident _ w _ _ => w
  | concat e1 e2 => (eval e1) ++ (eval e2)
  | range hi lo hw hle e => vec_range (eval e) hi lo hw hle


/- Testing const and concat -/

def dead := TExpr.const (Γ := ctx) (0xdead#16)
def beef := TExpr.const (Γ := ctx) (0xbeef#16)

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
