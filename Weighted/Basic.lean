import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.ENNReal.Operations
import Mathlib.Order.FixedPoints
import Mathlib.Order.Notation
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Order

/- Boolean arithmetic operators -/
inductive BAOp where
  | Lt | Le
  | Gt | Ge
  | Eq | Ne
deriving Lean.ToExpr

/- Boolean operators -/
inductive BOp where
  | And | Or
  | Imp | BImp
deriving Lean.ToExpr

/- Arithmetic operators -/
inductive AOp where
  | Add | Sub
  | Mul | Div
deriving Lean.ToExpr

inductive BUOp where
  | Not
deriving Lean.ToExpr

inductive AUOp where
  | Neg
deriving Lean.ToExpr

inductive AExpr (Var : Type) where
  | Const : Nat → AExpr Var
  | Var : Var → AExpr Var
  | Bin : AOp → AExpr Var → AExpr Var → AExpr Var
  | Uni : AUOp → AExpr Var → AExpr Var
deriving Lean.ToExpr

inductive BExpr (Var : Type) where
  | Const : Bool → BExpr Var
  | ABin : BAOp → AExpr Var → AExpr Var → BExpr Var
  | BBin : BOp → BExpr Var → BExpr Var → BExpr Var
  | Uni : BUOp → BExpr Var → BExpr Var
deriving Lean.ToExpr

inductive wGCL (W : Type) (Var : Type) where
  | Branch : wGCL W Var → wGCL W Var → wGCL W Var
  | Weighting : W → wGCL W Var
  | Assign : Var → AExpr Var → wGCL W Var
  | Ite : BExpr Var → wGCL W Var → wGCL W Var → wGCL W Var
  | Seq : wGCL W Var → wGCL W Var → wGCL W Var
  | While : BExpr Var → wGCL W Var → wGCL W Var
deriving Lean.ToExpr

def Mem (W : Type) (Var : Type) := Var → W

variable {W Var : Type}

declare_syntax_cat cwgcl_bexpr
syntax "wgcl_bexpr " "{" cwgcl_bexpr "}" : term
declare_syntax_cat cwgcl_aexpr
syntax "wgcl_aexpr " "{" cwgcl_aexpr "}" : term
declare_syntax_cat cwgcl_progr
syntax "wgcl " ppHardSpace "{" cwgcl_progr "}" : term

syntax ident : cwgcl_bexpr

syntax ident : cwgcl_aexpr
syntax num : cwgcl_aexpr

syntax:70 cwgcl_aexpr:70 " * " cwgcl_aexpr:71 : cwgcl_aexpr
syntax:70 cwgcl_aexpr:70 " / " cwgcl_aexpr:71 : cwgcl_aexpr

syntax:65 cwgcl_aexpr:65 " + " cwgcl_aexpr:66 : cwgcl_aexpr
syntax:65 cwgcl_aexpr:65 " - " cwgcl_aexpr:66 : cwgcl_aexpr

syntax:75 "-" cwgcl_aexpr:75 : cwgcl_aexpr

syntax:75 "¬" cwgcl_bexpr:75 : cwgcl_bexpr

syntax:50 cwgcl_aexpr:50 " < " cwgcl_aexpr:51 : cwgcl_bexpr
syntax:50 cwgcl_aexpr:50 " ≤ " cwgcl_aexpr:51 : cwgcl_bexpr
syntax:50 cwgcl_aexpr:50 " <= " cwgcl_aexpr:51 : cwgcl_bexpr
syntax:50 cwgcl_aexpr:50 " >= " cwgcl_aexpr:51 : cwgcl_bexpr
syntax:50 cwgcl_aexpr:50 " ≥ " cwgcl_aexpr:51 : cwgcl_bexpr
syntax:50 cwgcl_aexpr:50 " > " cwgcl_aexpr:51 : cwgcl_bexpr
syntax:45 cwgcl_aexpr:45 " = " cwgcl_aexpr:46 : cwgcl_bexpr
syntax:45 cwgcl_aexpr:45 " != " cwgcl_aexpr:46 : cwgcl_bexpr
syntax:45 cwgcl_aexpr:45 " ≠ " cwgcl_aexpr:46 : cwgcl_bexpr

syntax:35 cwgcl_bexpr:35 " ∧ " cwgcl_bexpr:36 : cwgcl_bexpr
syntax:35 cwgcl_bexpr:35 " ∨ " cwgcl_bexpr:36 : cwgcl_bexpr

syntax:35 cwgcl_bexpr:35 " → " cwgcl_bexpr:36 : cwgcl_bexpr
syntax:33 cwgcl_bexpr:33 " ↔ " cwgcl_bexpr:34 : cwgcl_bexpr

syntax:75 "⊙" num : cwgcl_progr
syntax:75 "⊙" "~" term:max : cwgcl_progr
syntax ident " := " cwgcl_aexpr : cwgcl_progr
syntax "{ " cwgcl_progr " }" " ⊕ " "{ " cwgcl_progr " }" : cwgcl_progr
syntax cwgcl_progr ";" ppHardSpace cwgcl_progr : cwgcl_progr
syntax "if " "(" cwgcl_bexpr ")" ppHardSpace "{"
    ppLine cwgcl_progr
  ppDedent(ppLine "}" ppHardSpace "else" ppHardSpace "{")
    ppLine cwgcl_progr
  ppDedent(ppLine "}") : cwgcl_progr
syntax "if " "(" cwgcl_bexpr ")" ppHardSpace "{" ppLine cwgcl_progr ppDedent(ppLine "}") : cwgcl_progr
syntax "while " "(" cwgcl_bexpr ")" ppHardSpace "{" ppLine cwgcl_progr ppDedent(ppLine "}") : cwgcl_progr
syntax "skip" : cwgcl_progr

open Lean in
macro_rules
-- bexpr
| `(wgcl_bexpr { true }) => `(BExpr.Const true)
| `(wgcl_bexpr { false }) => `(BExpr.Const false)
-- aexpr
| `(wgcl_aexpr { $n:num }) => `(AExpr.Const $n)
| `(wgcl_aexpr { $x:ident }) => `(AExpr.Var $(quote x.getId.toString))
-- arithmetic
| `(wgcl_aexpr { -$l }) => `(AExpr.Uni .Neg wgcl_aexpr {$l})
| `(wgcl_aexpr { $l * $r }) => `(AExpr.Bin .Mul wgcl_aexpr {$l} wgcl_aexpr {$r})
| `(wgcl_aexpr { $l / $r }) => `(AExpr.Bin .Div wgcl_aexpr {$l} wgcl_aexpr {$r})
| `(wgcl_aexpr { $l + $r }) => `(AExpr.Bin .Add wgcl_aexpr {$l} wgcl_aexpr {$r})
| `(wgcl_aexpr { $l - $r }) => `(AExpr.Bin .Sub wgcl_aexpr {$l} wgcl_aexpr {$r})
-- relational
| `(wgcl_bexpr { $l:cwgcl_aexpr < $r  }) => `(BExpr.ABin .Lt wgcl_aexpr {$l} wgcl_aexpr {$r})
| `(wgcl_bexpr { $l:cwgcl_aexpr ≤ $r  }) => `(BExpr.ABin .Le wgcl_aexpr {$l} wgcl_aexpr {$r})
| `(wgcl_bexpr { $l:cwgcl_aexpr <= $r }) => `(BExpr.ABin .Le wgcl_aexpr {$l} wgcl_aexpr {$r})
| `(wgcl_bexpr { $l:cwgcl_aexpr >= $r }) => `(BExpr.ABin .Gt wgcl_aexpr {$l} wgcl_aexpr {$r})
| `(wgcl_bexpr { $l:cwgcl_aexpr ≥ $r  }) => `(BExpr.ABin .Ge wgcl_aexpr {$l} wgcl_aexpr {$r})
| `(wgcl_bexpr { $l:cwgcl_aexpr > $r  }) => `(BExpr.ABin .Gt wgcl_aexpr {$l} wgcl_aexpr {$r})
| `(wgcl_bexpr { $l:cwgcl_aexpr = $r  }) => `(BExpr.ABin .Eq wgcl_aexpr {$l} wgcl_aexpr {$r})
| `(wgcl_bexpr { $l:cwgcl_aexpr != $r }) => `(BExpr.ABin .Ne wgcl_aexpr {$l} wgcl_aexpr {$r})
| `(wgcl_bexpr { $l:cwgcl_aexpr ≠ $r  }) => `(BExpr.ABin .Ne wgcl_aexpr {$l} wgcl_aexpr {$r})
-- logic
| `(wgcl_bexpr { $l:cwgcl_bexpr ∧ $r  }) => `(BExpr.BBin .And wgcl_bexpr {$l} wgcl_bexpr {$r})
| `(wgcl_bexpr { $l:cwgcl_bexpr ∨ $r  }) => `(BExpr.BBin .Or wgcl_bexpr {$l} wgcl_bexpr {$r})
| `(wgcl_bexpr { $l:cwgcl_bexpr → $r  }) => `(BExpr.BBin .Imp wgcl_bexpr {$l} wgcl_bexpr {$r})
| `(wgcl_bexpr { $l:cwgcl_bexpr ↔ $r  }) => `(BExpr.BBin .BImp wgcl_bexpr {$l} wgcl_bexpr {$r})
-- prog
| `(wgcl { skip }) => `(wGCL.Weighting 0)
| `(wgcl { ⊙ $b:num }) => `(wGCL.Weighting $b)
| `(wgcl { ⊙ ~ $b }) => `(wGCL.Weighting $b)
| `(wgcl { $x:ident := $e }) => `(wGCL.Assign $(quote x.getId.toString) wgcl_aexpr {$e})
| `(wgcl { {$l} ⊕ {$r} }) => `(wGCL.Branch wgcl {$l} wgcl {$r})
| `(wgcl { $l ; $r }) => `(wGCL.Seq wgcl {$l} wgcl {$r})
| `(wgcl { if ($b) {$l} else {$r} }) => `(wGCL.Ite wgcl_bexpr {$b} wgcl {$l} wgcl {$r})
| `(wgcl { if ($b) {$l} }) => `(wGCL.Ite wgcl_bexpr {$b} wgcl {$l} wgcl {skip})
| `(wgcl { while ($b) {$l} }) => `(wGCL.While wgcl_bexpr {$b} wgcl {$l})

syntax:max "~" term:max " := " cwgcl_aexpr : cwgcl_progr
syntax:max "~" term:max : cwgcl_aexpr
syntax:max "~" term:max : cwgcl_bexpr
syntax:max "~" term:max : cwgcl_progr
macro_rules
| `(wgcl_aexpr {~$E}) => `($E)
| `(wgcl_bexpr {~$E}) => `($E)
| `(wgcl {~$t := $E}) => `(wGCL.Assign $t (wgcl_aexpr {$E}))
| `(wgcl {~$C}) => `($C)

/-- info: (wGCL.Weighting 0).Branch (wGCL.Weighting 1) : wGCL ℕ Unit -/
#guard_msgs in
#check (wgcl { { ⊙0 } ⊕ { ⊙1 } } : wGCL _ Unit)

section

open Lean PrettyPrinter Delaborator SubExpr

@[app_unexpander BExpr.Const]
def BExpr.unexpandConst : Unexpander
| `($(_) true) => let t := mkIdent $ Name.mkSimple "true"; `(wgcl_bexpr { $t:ident })
| `($(_) false) => let t := mkIdent $ Name.mkSimple "false"; `(wgcl_bexpr { $t:ident })
| _ => throw ()

@[app_unexpander AExpr.Const]
def AExpr.unexpandConst : Unexpander
| `($(_) $n:num) => `(wgcl_aexpr { $n:num })
| _ => throw ()
@[app_unexpander AExpr.Var]
def AExpr.unexpandVar : Unexpander
| `($(_) $x:str) =>
  let name := mkIdent $ Name.mkSimple x.getString
  `(wgcl_aexpr { $name:ident })
| _ => throw ()
@[app_unexpander AExpr.Bin]
def AExpr.unexpandBin : Unexpander
| `($(_) AOp.Add wgcl_aexpr{$l} wgcl_aexpr{$r}) => `(wgcl_aexpr { $l + $r })
| `($(_) AOp.Sub wgcl_aexpr{$l} wgcl_aexpr{$r}) => `(wgcl_aexpr { $l - $r })
| `($(_) AOp.Mul wgcl_aexpr{$l} wgcl_aexpr{$r}) => `(wgcl_aexpr { $l * $r })
| `($(_) AOp.Div wgcl_aexpr{$l} wgcl_aexpr{$r}) => `(wgcl_aexpr { $l / $r })
| _ => throw ()
@[app_unexpander AExpr.Uni]
def AExpr.unexpandUni : Unexpander
| `($(_) AUOp.Neg wgcl_aexpr{$l}) => `(wgcl_aexpr { - $l })
| _ => throw ()

@[app_unexpander BExpr.ABin]
def BExpr.unexpandABin : Unexpander
| `($(_) BAOp.Lt wgcl_aexpr{$l} wgcl_aexpr{$r}) => `(wgcl_bexpr { $l:cwgcl_aexpr < $r })
| `($(_) BAOp.Le wgcl_aexpr{$l} wgcl_aexpr{$r}) => `(wgcl_bexpr { $l:cwgcl_aexpr ≤ $r })
| `($(_) BAOp.Gt wgcl_aexpr{$l} wgcl_aexpr{$r}) => `(wgcl_bexpr { $l:cwgcl_aexpr > $r })
| `($(_) BAOp.Ge wgcl_aexpr{$l} wgcl_aexpr{$r}) => `(wgcl_bexpr { $l:cwgcl_aexpr ≥ $r })
| `($(_) BAOp.Eq wgcl_aexpr{$l} wgcl_aexpr{$r}) => `(wgcl_bexpr { $l:cwgcl_aexpr = $r })
| `($(_) BAOp.Ne wgcl_aexpr{$l} wgcl_aexpr{$r}) => `(wgcl_bexpr { $l:cwgcl_aexpr ≠ $r })
| _ => throw ()

/-- info: wgcl_aexpr {1 + 2} -/
#guard_msgs in
#eval (wgcl_aexpr { 1 + 2 } : AExpr Unit)

/-- info: wgcl_aexpr {1 * 2} -/
#guard_msgs in
#eval (wgcl_aexpr { 1 * 2 } : AExpr Unit)

@[app_unexpander wGCL.Weighting]
def wGCL.unexpandWeighting : Unexpander
| `($(_) 0) => `(wgcl {skip})
| `($(_) $w:num) => `(wgcl {⊙ $w})
| `($(_) $_ $w:num) => `(wgcl {⊙ $w})
| _ => throw ()
@[app_unexpander wGCL.Branch]
def wGCL.unexpandBranch : Unexpander
| `($(_) wgcl {$l} wgcl {$r}) => `(wgcl { { $l } ⊕ { $r } })
| _ => throw ()
@[app_unexpander wGCL.Seq]
def wGCL.unexpandSeq : Unexpander
| `($(_) wgcl {$l} wgcl {$r})
| `($(_) $_ wgcl {$l} wgcl {$r}) => `(wgcl { $l  ; $r })
| _ => throw ()
@[app_unexpander wGCL.Ite]
def wGCL.unexpandIte : Unexpander
| `($(_) wgcl_bexpr {$b} wgcl {$l} wgcl {skip})
| `($(_) $_ wgcl_bexpr {$b} wgcl {$l} wgcl {skip}) => `(wgcl { if ($b) { $l } })
| `($(_) wgcl_bexpr {$b} wgcl {$l} wgcl {$r})
| `($(_) $_ wgcl_bexpr {$b} wgcl {$l} wgcl {$r}) => `(wgcl { if ($b) { $l } else { $r } })
| _ => throw ()
@[app_unexpander wGCL.While]
def wGCL.unexpandWhile : Unexpander
| `($(_) wgcl_bexpr {$b} wgcl {$l})
| `($(_) $_ wgcl_bexpr {$b} wgcl {$l}) => `(wgcl { while ($b) { $l } })
| _ => throw ()
@[app_unexpander wGCL.Assign]
def wGCL.unexpandAssign : Unexpander
| `($(_) $x:str wgcl_aexpr {$e})
| `($(_) $(_) $x:str wgcl_aexpr {$e}) =>
  let name := mkIdent $ Name.mkSimple x.getString
  `(wgcl {$name:ident := $e})
| _ => throw ()

/-- info: wgcl {{ skip } ⊕ { ⊙1 }} -/
#guard_msgs in
#eval (wgcl { { ⊙0 } ⊕ { ⊙1 } } : wGCL _ Unit)

/--
info: wgcl {if (true) {
    skip
  } else {
    ⊙1
  }}
-/
#guard_msgs in
#eval (wgcl { if (true) { ⊙0 } else { ⊙1 } } : wGCL _ Unit)

/--
info: wgcl {while (true) {
    ⊙1
  }}
-/
#guard_msgs in
#eval (wgcl { while (true) { ⊙1 } } : wGCL _ Unit)

/-- info: wgcl {⊙1; ⊙1} -/
#guard_msgs in
#eval (wgcl { ⊙1 ; ⊙1 } : wGCL _ Unit)

/-- info: wgcl {x := 32} -/
#guard_msgs in
#eval (wgcl { x := 32 } : wGCL Unit _)

/--
info: wgcl {if (true) {
    ⊙1
  }}
-/
#guard_msgs in
#eval (wgcl { if (true) { ⊙1 } } : wGCL Nat Unit)

class Subst (W Var E : Type) where
  /-- Written using `a[x ↦ e]`. Substitutes all `x` in `a` with `e`. -/
  subst : W → Var → E → W

@[inherit_doc Subst.subst]
syntax:max term noWs "[" withoutPosition(term) ppHardSpace "↦" ppHardSpace withoutPosition(term) "]" : term
macro_rules | `($x[$i ↦ $j]) => `(Subst.subst $x $i $j)

open Lean PrettyPrinter Delaborator SubExpr in
@[app_unexpander Subst.subst]
def Subst.substUnexpander : Unexpander
| `($(_) $m $x $v) => `($m[$x ↦ $v])
| _ => throw ()

instance [BEq α] [Hashable α] : Subst (Std.HashMap α β) α β where
  subst m x v := m.insert x v

abbrev Transf W Var := Mem W Var → W

variable [Semiring W]
variable [CompleteLattice W]

set_option linter.unusedVariables false in
def AExpr.eval (E : AExpr Var) (σ : Mem W Var) : W :=
  match E with
  | .Const n => n
  | .Var x => σ x
  | wgcl_aexpr {~l + ~ r} => l.eval σ + r.eval σ
  | wgcl_aexpr {~l - ~ r} => 0 -- TODO: l.eval σ - r.eval σ
  | wgcl_aexpr {~l * ~ r} => l.eval σ * r.eval σ
  | wgcl_aexpr {~l / ~ r} => 0 -- TODO: l.eval σ / r.eval σ
  | wgcl_aexpr {-~l} => 0 -- TODO: -l.eval σ
def BExpr.eval (B : BExpr Var) (σ : Mem W Var) : Prop :=
  match B with
  | .Const b => b
  | wgcl_bexpr { ~l ∧ ~ r } => l.eval σ ∧ r.eval σ
  | wgcl_bexpr { ~l ∨ ~ r } => l.eval σ ∨ r.eval σ
  | wgcl_bexpr { ~l → ~ r } => l.eval σ → r.eval σ
  | wgcl_bexpr { ~l ↔ ~ r } => l.eval σ ↔ r.eval σ
  | wgcl_bexpr { ~l < ~ r } => l.eval σ < r.eval σ
  | wgcl_bexpr { ~l ≤ ~ r } => l.eval σ ≤ r.eval σ
  | wgcl_bexpr { ~l ≥ ~ r } => l.eval σ ≥ r.eval σ
  | wgcl_bexpr { ~l > ~ r } => l.eval σ > r.eval σ
  | wgcl_bexpr { ~l = ~ r } => l.eval σ = r.eval σ
  | wgcl_bexpr { ~l ≠ ~ r } => l.eval σ ≠ r.eval σ
  | .Uni .Not l => ¬l.eval σ

def BExpr.not (B : BExpr Var) : BExpr Var := .Uni .Not B

variable [DecidableEq Var]

instance : Subst (Mem W Var) Var W where
  subst σ x v := fun y ↦ if x = y then v else σ y

instance : Subst (Transf W Var) Var (AExpr Var) where
  subst f x E := fun σ ↦ f σ[x ↦ E.eval σ]

theorem Transf.subst_mono {f₁ f₂ : Transf W Var} (h : f₁ ≤ f₂) (x : Var) (y : AExpr Var) :
    f₁[x ↦ y] ≤ f₂[x ↦ y] := by
  intro σ
  exact h fun y_1 => if x = y_1 then y.eval σ else σ y_1

variable [∀ (B : BExpr Var) (σ : Mem W Var), Decidable (B.eval σ)]

def BExpr.iver (B : BExpr Var) : Transf W Var := fun σ ↦ if B.eval σ then 1 else 0

/-- A version of `OrderHom.lfp` that does not require `f` the `Monotone` upfront. -/
protected def wp.lfp {α} [CompleteLattice α] (f : α → α) : α := sInf {a | f a ≤ a}

namespace wp.lfp

variable [CompleteLattice α]

theorem monotone : Monotone (wp.lfp (α:=α)) := by
  intro f g h
  simp_all [wp.lfp]
  intro x h'
  apply sInf_le
  simp [le_trans (h x) h']

@[simp] theorem wp_lfp_eq_lfp (f : α → α) (h : Monotone f) : wp.lfp f = OrderHom.lfp ⟨f, h⟩ := rfl
@[simp] theorem wp_lfp_eq_lfp_OrderHom (f : α →o α) : wp.lfp f = OrderHom.lfp f := rfl

end wp.lfp

instance : Semiring (Transf W Var) := Pi.semiring
instance : CompleteLattice (Transf W Var) := Pi.instCompleteLattice

instance : HMul W (Transf W Var) (Transf W Var) where
  hMul w f := fun σ ↦ w * f σ

@[simp]
def wGCL.wp (C : wGCL W Var) (f : Transf W Var) : Transf W Var := match C with
| wgcl { ~x := ~E }                     => f[x ↦ E]
| wgcl { ~C₁; ~C₂ }                     => C₁.wp (C₂.wp f)
| wgcl { if (~φ) { ~C₁ } else { ~C₂ } } => φ.iver * C₁.wp f + φ.not.iver * C₂.wp f
| wgcl { { ~C₁ } ⊕ { ~C₂ } }            => C₁.wp f + C₂.wp f
| wgcl { ⊙ ~a }                         => a * f
| wgcl { while (~φ) { ~C' } }           => wp.lfp fun X ↦ φ.not.iver * f + φ.iver * C'.wp X

variable [AddRightMono W] [AddLeftMono W] [MulLeftMono W]

attribute [local simp] Function.swap
instance : AddRightMono (Transf W Var) := ⟨by intro f₁ f₂ f₃ h σ; simp; gcongr; apply_assumption⟩
instance : AddLeftMono  (Transf W Var) := ⟨by intro f₁ f₂ f₃ h σ; simp; gcongr; apply_assumption⟩
instance : MulLeftMono  (Transf W Var) := ⟨by intro f₁ f₂ f₃ h σ; simp; gcongr; apply_assumption⟩

theorem wGCL.wp_monotone (C : wGCL W Var) : Monotone C.wp := by
  induction C with (intro f₁ f₂ h; simp only [wp])
  | Branch C₁ C₂ ih₁ ih₂ => gcongr <;> (apply_assumption; assumption)
  | Weighting => gcongr
  | Assign => apply Transf.subst_mono h
  | Ite => gcongr <;> apply_assumption <;> assumption
  | Seq => repeat (first | apply_assumption | assumption)
  | While => exact wp.lfp.monotone fun f ↦ by gcongr

def P₁ : wGCL Nat String := wgcl {
  x := 0; y := 1;
  while (x ≠ p) {
    if (x < y) { ⊙1; x := x + 1 }
    else { ⊙1; x := x - 1 };
    if (x = y) { y := -2 * y }
  }
}

/--
info: wgcl {x := 0; y := 1; while (x ≠ p) {
        if (x < y) {
            ⊙1; x := x + 1
          } else {
            ⊙1; x := x - 1
          }; if (x = y) {
            y := -2 * y
          }
      }}
-/
#guard_msgs in
#eval P₁

inductive Act | N | L | R deriving Lean.ToExpr

structure Conf (W : Type) (Var : Type) where
  C : WithBot (wGCL W Var)
  σ : Mem W Var
  n : W
  β : List Act

syntax "conf" ppHardSpace "⟨" cwgcl_progr "," term "," term "," term "⟩" : term
syntax "conf" ppHardSpace "⟨" "⊥" "," term "," term "," term "⟩" : term

macro_rules
| `(conf ⟨⊥, $σ, $n, $β⟩) => `(({C:=⊥,σ:=$σ,n:=$n,β:=$β} : Conf _ _))
| `(conf ⟨$C, $σ, $n, $β⟩) => `(({C:=some wgcl{$C},σ:=$σ,n:=$n,β:=$β} : Conf _ _))

@[app_unexpander Conf.mk]
def Conf.unexpand : Unexpander
| `($(_) ⊥ $σ $n $β) => `(conf ⟨⊥, $σ, $n, $β⟩)
| `($(_) $C $σ $n $β) =>
  match C with
  | `($_ wgcl {$C}) => `(conf ⟨$C, $σ, $n, $β⟩)
  | _ => throw ()
-- | `($(_) (some (wgcl{$C})) $σ $n $β) => `(conf ⟨$C, $σ, $n, $β⟩)
| _ => throw ()

/-- info: fun σ n β => conf ⟨⊥,σ,n,β⟩ : Mem W String → W → List Act → Conf W String -/
#guard_msgs in
#check fun (σ : Mem W String) n β ↦ conf ⟨⊥, σ, n, β⟩

/-- info: fun σ n β => conf ⟨x := E,σ,n,β⟩ : Mem W String → W → List Act → Conf W String -/
#guard_msgs in
#check fun (σ : Mem W String) n β ↦ conf ⟨x := E, σ, n, β⟩

syntax "op" ppHardSpace
  "⟨" cwgcl_progr "," term "," term "," term "⟩"
  "⊢[" term "]"
  "⟨" cwgcl_progr "," term "," term "," term "⟩"
  : term
syntax "⊥" : cwgcl_progr

inductive Op : Conf W Var → W → Conf W Var → Prop where
  | Assign : Op (conf ⟨~x := ~E, σ, n, β⟩) 1 (conf ⟨⊥, σ[x ↦ E.eval σ], n+1, β⟩)
  | Weight : Op (conf ⟨⊙ ~a, σ, n, β⟩) a (conf ⟨⊥, σ, n+1, β⟩)
  | Seq₁ :
      Op (conf ⟨~C₁, σ, n, β⟩) a (conf ⟨⊥, σ', n+1, β⟩) →
    Op (conf ⟨~C₁ ; ~C₂, σ, n, β⟩) a (conf ⟨~C₂, σ', n+1, β⟩)
  | Seq₂ :
      Op (conf ⟨~C₁, σ, n, β⟩) a (conf ⟨~C₁', σ', n+1, β⟩) →
    Op (conf ⟨~C₁ ; ~C₂, σ, n, β⟩) a (conf ⟨~C₁' ; ~C₂, σ', n+1, β⟩)
  | If : (h : φ.eval σ) →
    Op (conf ⟨if (~φ) {~C₁} else {~C₂}, σ, n, β⟩) 1 (conf ⟨~C₁, σ, n+1, β⟩)
  | Else : (h : ¬φ.eval σ) →
    Op (conf ⟨if (~φ) {~C₁} else {~C₂}, σ, n, β⟩) 1 (conf ⟨~C₂, σ, n+1, β⟩)
  | BranchL :
    Op (conf ⟨{~C₁} ⊕ {~C₂}, σ, n, β⟩) 1 (conf ⟨~C₁, σ, n+1, .L::β⟩)
  | BranchR :
    Op (conf ⟨{~C₁} ⊕ {~C₂}, σ, n, β⟩) 1 (conf ⟨~C₂, σ, n+1, .R::β⟩)
  | While : (h : φ.eval σ) →
    Op (conf ⟨while (~φ) {~C}, σ, n, β⟩) 1 (conf ⟨~C ; while (~φ) {~C}, σ, n+1, β⟩)
  | Break : (h : ¬φ.eval σ) →
    Op (conf ⟨while (~φ) {~C}, σ, n, β⟩) 1 (conf ⟨⊥, σ, n+1, β⟩)

set_option quotPrecheck false in
macro_rules
| `(wgcl {⊥}) => `(⊥)
| `(op ⟨$C, $σ, $n, $β⟩ ⊢[$a] ⟨$C', $σ', $n', $β'⟩) =>
  `(Op (conf ⟨$C,$σ,$n,$β⟩) $a (conf ⟨$C',$σ',$n',$β'⟩))

structure Paths (𝒦₀ : Conf W Var) where
  states : List (Conf W Var)
  h_pos : 0 < states.length
  h_first : states[0] = 𝒦₀

variable {𝒦₀ : Conf W Var}

@[simp] def Paths.length_pos (π : Paths 𝒦₀) : 0 < π.states.length := π.h_pos
@[simp] def Paths.nonempty (π : Paths 𝒦₀) : π.states ≠ [] :=
  List.ne_nil_of_length_pos (π.length_pos)
def Paths.last (π : Paths 𝒦₀) : Conf W Var := π.states.getLast (by simp)
def Paths.IsTerminal (π : Paths 𝒦₀) : Prop := π.last.C = ⊥

def TPaths (𝒦₀ : Conf W Var) : Set (Paths 𝒦₀) := ⋃ n, {π | π.states.length = n ∧ π.IsTerminal}

def Conf.wgt (𝒦₁ 𝒦₂ : Conf W Var) : W := sorry

def List.pairs (l : List α) : List (α × α) := match l with
  | a :: b :: tail => (a, b) :: (b :: tail).pairs
  | _ => []


def Paths.wgt (π : Paths 𝒦₀) : W := π.states.pairs.map (fun (𝒦₁, 𝒦₂) ↦ 𝒦₁.wgt 𝒦₂) |>.sum

variable [TopologicalSpace W]

noncomputable def wGCL.op (C : wGCL W Var) (f : Transf W Var) : Transf W Var :=
  fun σ ↦ ∑' π : TPaths (conf ⟨~C, σ, 0, []⟩), π.val.wgt * f π.val.last.σ

def Succs (C : wGCL W Var) (σ : Mem W Var) := { (a, C', σ') | ∃ n β β', op ⟨~C, σ, n, β⟩ ⊢[a] ⟨~C', σ', n+1, β'⟩ }

noncomputable def wGCL.Φ (c : wGCL W Var → Transf W Var → Transf W Var) (C : wGCL W Var) (f : Transf W Var) : Transf W Var :=
  fun σ ↦ ∑' X : Succs C σ, let ⟨a, C', σ'⟩ := X.val; a * c C' f σ'

end

open OrderHom

variable [DecidableEq Var]
variable [Semiring W]
variable [instTopologicalSpace : TopologicalSpace W] [instOrderedAddCommMonoid : OrderedAddCommMonoid W] [@OrderClosedTopology W instTopologicalSpace instCompleteLattice.toPreorder]

variable [(B : BExpr Var) → (σ : Mem W Var) → Decidable (B.eval σ)]

def wGCL.Φ_mono : Monotone (Φ (W:=W) (Var:=Var)) := by
  intro v₁ v₂ h C f σ
  simp [Φ]
  have : @OrderClosedTopology W instTopologicalSpace instCompleteLattice.toPreorder := inferInstance
  have := @tsum_le_tsum (Succs C σ) W instOrderedAddCommMonoid instTopologicalSpace this
  apply @tsum_le_tsum _ W NonUnitalNonAssocSemiring.toAddCommMonoid

  sorry

theorem wGCL.op_eq_lfp_Φ (C : wGCL W Var) : C.op = lfp ⟨Φ, Φ_mono⟩ C := sorry

theorem wGCL.wp.soundness (C : wGCL W Var) :
    C.wp = fun f σ ↦ ∑' π : TPaths (conf ⟨~C, σ, n, β⟩), π.val.wgt * f π.val.last.σ := by
  induction C with
  | Branch C₁ C₂ ih₁ ih₂ => sorry
  | Weighting => sorry
  | Assign x E =>
    ext f σ
    simp [TPaths]
    sorry
  | Ite => sorry
  | Seq => sorry
  | While => sorry

end
