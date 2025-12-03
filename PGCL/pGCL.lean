import Lean.PrettyPrinter.Delaborator
import PGCL.Exp

open pGCL

variable {ϖ : Type*}

inductive pGCL (ϖ : Type*) where
  | skip : pGCL ϖ
  | assign : ϖ → Exp ϖ → pGCL ϖ
  | seq : pGCL ϖ → pGCL ϖ → pGCL ϖ
  | prob : pGCL ϖ → ProbExp ϖ → pGCL ϖ → pGCL ϖ
  | nonDet : pGCL ϖ → pGCL ϖ → pGCL ϖ
  | loop : BExpr ϖ → pGCL ϖ → pGCL ϖ
  | tick : Exp ϖ → pGCL ϖ
  | observe : BExpr ϖ → pGCL ϖ
deriving Inhabited

def pGCL.ite (b : BExpr ϖ) (C₁ C₂ : pGCL ϖ) : pGCL ϖ := .prob C₁ p[b] C₂

noncomputable instance pGCL.decidableEq [DecidableEq ϖ] : DecidableEq (pGCL ϖ)
  | a, b => by exact Classical.propDecidable (a = b)

namespace pGCL

section Syntax

open Lean PrettyPrinter Delaborator SubExpr

declare_syntax_cat cpgcl_var
syntax "pgcl_var " "{" cpgcl_var "}" : term
declare_syntax_cat cpgcl_bexp
syntax "pgcl_bexp " "{" cpgcl_bexp "}" : term
declare_syntax_cat cpgcl_aexp
syntax "pgcl_aexp " "{" cpgcl_aexp "}" : term
declare_syntax_cat cpgcl_pexp
syntax "pgcl_pexp " "{" cpgcl_pexp "}" : term
declare_syntax_cat cpgcl_prog
syntax "pgcl" ppHardSpace "{" cpgcl_prog "}" : term

syntax:max "~" term:max : cpgcl_var
syntax:max "~" term:max : cpgcl_bexp
syntax:max "~" term:max : cpgcl_aexp
syntax:max "~" term:max : cpgcl_pexp
syntax:max "~" term:max : cpgcl_prog
macro_rules
| `(pgcl_var { ~$c }) => `($c)
| `(pgcl_bexp { ~$c }) => `($c)
| `(pgcl_aexp { ~$c }) => `($c)
| `(pgcl_pexp { ~$c }) => `($c)
| `(pgcl { ~$c }) => `($c)

syntax ident : cpgcl_var

syntax num : cpgcl_aexp
syntax ident : cpgcl_aexp
syntax cpgcl_aexp " + " cpgcl_aexp : cpgcl_aexp
syntax cpgcl_aexp " - " cpgcl_aexp : cpgcl_aexp
syntax cpgcl_aexp " * " cpgcl_aexp : cpgcl_aexp
syntax cpgcl_aexp " / " cpgcl_aexp : cpgcl_aexp
syntax "[" cpgcl_bexp "]" : cpgcl_aexp
syntax "(" cpgcl_aexp ")" : cpgcl_aexp

-- syntax num "⁻¹" : cpgcl_pexp
syntax cpgcl_aexp "⁻¹" : cpgcl_pexp

syntax ident : cpgcl_bexp
syntax cpgcl_aexp " < " cpgcl_aexp : cpgcl_bexp
syntax cpgcl_aexp " ≤ " cpgcl_aexp : cpgcl_bexp
syntax cpgcl_aexp " = " cpgcl_aexp : cpgcl_bexp
syntax cpgcl_bexp " ∧ " cpgcl_bexp : cpgcl_bexp
syntax cpgcl_bexp " ∨ " cpgcl_bexp : cpgcl_bexp
syntax "¬" cpgcl_bexp : cpgcl_bexp
syntax "(" cpgcl_bexp ")" : cpgcl_bexp

syntax ident : cpgcl_prog
syntax cpgcl_var " := " cpgcl_aexp : cpgcl_prog
syntax cpgcl_prog " ; " cpgcl_prog : cpgcl_prog
syntax "{ " cpgcl_prog " }" " [" cpgcl_pexp "] "  "{ " cpgcl_prog " }" : cpgcl_prog
syntax "{ " cpgcl_prog " }" " [" "] "  "{ " cpgcl_prog " }" : cpgcl_prog
syntax "while " cpgcl_bexp " { " cpgcl_prog " }" : cpgcl_prog
syntax "tick(" cpgcl_aexp ")"  : cpgcl_prog
syntax "observe(" cpgcl_bexp ")" : cpgcl_prog
syntax "if " cpgcl_bexp " then " cpgcl_prog " else " cpgcl_prog " end" : cpgcl_prog

def Exp.const (c : ϖ) : Exp ϖ := (· c)

macro_rules
-- vars
| `(pgcl_var { $v:ident }) => `(term|$(quote v.getId.toString))
-- pexp
| `(pgcl_pexp { $n:cpgcl_aexp ⁻¹ }) => `(ProbExp.inv pgcl_aexp {$n})
-- aexp
| `(pgcl_aexp { $n:num }) => `(($n : Exp _))
| `(pgcl_aexp { $v:ident }) => `(term|Exp.const $(quote v.getId.toString))
| `(pgcl_aexp { $l:cpgcl_aexp + $r }) => `(pgcl_aexp {$l} + pgcl_aexp {$r})
| `(pgcl_aexp { $l:cpgcl_aexp - $r }) => `(pgcl_aexp {$l} - pgcl_aexp {$r})
| `(pgcl_aexp { $l:cpgcl_aexp * $r }) => `(pgcl_aexp {$l} * pgcl_aexp {$r})
| `(pgcl_aexp { $l:cpgcl_aexp / $r }) => `(pgcl_aexp {$l} / pgcl_aexp {$r})
| `(pgcl_aexp { [$b:cpgcl_bexp] }) => `(BExpr.iver pgcl_bexp {$b})
| `(pgcl_aexp { ($a:cpgcl_aexp) }) => `(pgcl_aexp {$a})
-- bexp
| `(pgcl_bexp { true }) => `(true)
| `(pgcl_bexp { false }) => `(false)
| `(pgcl_bexp { $l:cpgcl_aexp < $r }) => `(BExpr.lt (pgcl_aexp {$l}) (pgcl_aexp {$r}))
| `(pgcl_bexp { $l:cpgcl_aexp ≤ $r }) => `(BExpr.le (pgcl_aexp {$l}) (pgcl_aexp {$r}))
| `(pgcl_bexp { $l:cpgcl_aexp = $r }) => `(BExpr.eq (pgcl_aexp {$l}) (pgcl_aexp {$r}))
| `(pgcl_bexp { $l:cpgcl_bexp ∧ $r }) => `(BExpr.and (pgcl_bexp {$l}) (pgcl_bexp {$r}))
| `(pgcl_bexp { $l:cpgcl_bexp ∨ $r }) => `(BExpr.or (pgcl_bexp {$l}) (pgcl_bexp {$r}))
| `(pgcl_bexp { ¬$l:cpgcl_bexp }) => `(BExpr.not (pgcl_bexp {$l}))
| `(pgcl_bexp { ($l:cpgcl_bexp) }) => `(pgcl_bexp {$l})
-- pGCL
| `(pgcl { skip }) => `(pGCL.skip)
| `(pgcl { $v:cpgcl_var := $e }) => `(pGCL.assign pgcl_var {$v} pgcl_aexp {$e})
| `(pgcl { $C₁ ; $C₂ }) => `(pGCL.seq pgcl {$C₁} pgcl {$C₂})
| `(pgcl { { $C₁:cpgcl_prog } [ $p ] { $C₂ } }) => `(pGCL.prob pgcl {$C₁} pgcl_pexp {$p} pgcl {$C₂})
| `(pgcl { { $C₁:cpgcl_prog } [] { $C₂ } }) => `(pGCL.nonDet pgcl {$C₁} pgcl {$C₂})
| `(pgcl { while $b { $C:cpgcl_prog } }) => `(pGCL.loop pgcl_bexp {$b} pgcl {$C})
| `(pgcl { tick($r) }) => `(pGCL.tick (pgcl_aexp {$r} : Exp _))
| `(pgcl { observe($b) }) => `(pGCL.observe pgcl_bexp {$b})
| `(pgcl { if $b then $C₁ else $C₂ end }) => `(pGCL.ite pgcl_bexp {$b} pgcl {$C₁} pgcl {$C₂})

#check (pgcl_bexp { x ≤ y } : BExpr String)

set_option linter.style.setOption false
set_option pp.mvars false
set_option linter.style.setOption true

partial def unexpandAexp : TSyntax `term → UnexpandM (TSyntax `cpgcl_aexp)
| `(pgcl_aexp { $c }) => pure c
| `($a:num) => `(cpgcl_aexp|$a:num)
| `(fun $_ ↦ $a:num) => `(cpgcl_aexp|$a:num)
| `(Exp.const $x:str) =>
    let name := mkIdent <| Name.mkSimple x.getString
    `(cpgcl_aexp|$name:ident)
| `(fun $σ ↦ $σ' $x:str) =>
  if σ.raw == σ'.raw then
    let name := mkIdent <| Name.mkSimple x.getString
    `(cpgcl_aexp|$name:ident)
  else
    throw ()
| `(fun $σ ↦ Nat.cast ($σ' $x:str)) =>
  if σ.raw == σ'.raw then
    let name := mkIdent <| Name.mkSimple x.getString
    `(cpgcl_aexp|$name:ident)
  else
    throw ()
| `($a + $b) => do
  let a ← unexpandAexp a; let b ← unexpandAexp b
  `(cpgcl_aexp|$a + $b)
| `($a - $b) => do
  let a ← unexpandAexp a; let b ← unexpandAexp b
  `(cpgcl_aexp|$a - $b)
| `($a * $b) => do
  let a ← unexpandAexp a; let b ← unexpandAexp b
  `(cpgcl_aexp|$a * $b)
| `($a / $b) => do
  let a ← unexpandAexp a; let b ← unexpandAexp b
  `(cpgcl_aexp|$a / $b)
| c => `(cpgcl_aexp|~ $c)

def unexpandBExp : TSyntax `term → UnexpandM (TSyntax `cpgcl_bexp)
| `(pgcl_bexp { $c }) => pure c
| `(↑true) =>
  let name := mkIdent <| Name.mkSimple "true"
  `(cpgcl_bexp| $name:ident)
| `(↑false) =>
  let name := mkIdent <| Name.mkSimple "false"
  `(cpgcl_bexp| $name:ident)
| `(fun $σ ↦ $σ' $x:str) =>
  if σ.raw == σ'.raw then
    let name := mkIdent <| Name.mkSimple x.getString
    `(cpgcl_bexp|$name:ident)
  else
    throw ()
| `(fun $σ ↦ $a $σ' < $b $σ'') => do
  if σ.raw == σ'.raw ∧ σ'.raw == σ''.raw then
    let a ← unexpandAexp a; let b ← unexpandAexp b
    `(cpgcl_bexp|$a:cpgcl_aexp < $b)
  else
    throw ()
| `(fun $σ ↦ $a $σ' ≤ $b $σ'') => do
  if σ.raw == σ'.raw ∧ σ'.raw == σ''.raw then
    let a ← unexpandAexp a; let b ← unexpandAexp b
    `(cpgcl_bexp|$a:cpgcl_aexp ≤ $b)
  else
    throw ()
| `(fun $σ ↦ $a $σ' = $b $σ'') => do
  if σ.raw == σ'.raw ∧ σ'.raw == σ''.raw then
    let a ← unexpandAexp a; let b ← unexpandAexp b
    `(cpgcl_bexp|$a:cpgcl_aexp = $b)
  else
    throw ()
| c => `(cpgcl_bexp|~ $c)

@[app_unexpander pGCL.BExpr.eq]
def BExpr.eqUnexpander : Unexpander
| `($_ $l $r) => do
  let l ← unexpandAexp l; let r ← unexpandAexp r
  `(pgcl_bexp { $l:cpgcl_aexp = $r })
| _ => throw ()

/-- info: pgcl_bexp {1 = 2} : BExpr ?_ -/
#guard_msgs in
#check pgcl_bexp { 1 = 2 }

@[app_unexpander pGCL.ProbExp.inv]
def probExpUnexpander : Unexpander
| `($_ $e) => do
  let e ← unexpandAexp e
  `(pgcl_pexp { $e:cpgcl_aexp ⁻¹ })
| `($(_)) => throw ()

/-- info: pgcl_pexp {2⁻¹} : ProbExp ?_ -/
#guard_msgs in
#check pgcl_pexp { 2⁻¹ }

@[app_unexpander pGCL.skip]
def skipUnexpander : Unexpander
| `($(_)) =>
  let name := mkIdent <| Name.mkSimple "skip"
  `(pgcl { $name:ident })

/-- info: pgcl {skip} : pGCL ?_ -/
#guard_msgs in
#check pgcl { skip }

@[app_unexpander pGCL.assign]
def assignUnexpander : Unexpander
| `($(_) $name:str $e) => do
  let name := mkIdent <| Name.mkSimple name.getString
  let e ← unexpandAexp e
  `(pgcl { $name:ident := $e })
| `($(_) $name $e) => do
  let e ← match e with | `(pgcl_aexp {$e}) => pure e | _ => `(cpgcl_aexp| ~ $e)
  `(pgcl { ~$name := $e })
| _ => throw ()

/-- info: pgcl {x := x} : pGCL String -/
#guard_msgs in
#check pgcl { x := x }

/-- info: pgcl {x := x - 1} : pGCL String -/
#guard_msgs in
#check pgcl { x := x - 1 }

/-- info: pgcl {x := 1} : pGCL String -/
#guard_msgs in
#check pgcl { x := 1 }

@[app_unexpander pGCL.seq]
def seqUnexpander : Unexpander
| `($(_) $l $r) => do
  let l ← match l with | `(pgcl {$l}) => pure l | _ => `(cpgcl_prog| ~ $l)
  let r ← match r with | `(pgcl {$r}) => pure r | _ => `(cpgcl_prog| ~ $r)
  `(pgcl { $l ; $r })
| _ => throw ()

/-- info: pgcl {x := 1 ; skip} : pGCL String -/
#guard_msgs in
#check pgcl { x := 1 ; skip }

@[app_unexpander pGCL.prob]
def probUnexpander : Unexpander
| `($(_) $l $p $r) => do
  let l ← match l with | `(pgcl {$l}) => pure l | _ => `(cpgcl_prog| ~ $l)
  let p ← match p with | `(pgcl_pexp {$p}) => pure p | _ => `(cpgcl_pexp| ~ $p)
  let r ← match r with | `(pgcl {$r}) => pure r | _ => `(cpgcl_prog| ~ $r)
  `(pgcl { { $l } [$p] {$r} })
| _ => throw ()

/-- info: pgcl {{ x := 1 } [1⁻¹] { skip }} : pGCL String -/
#guard_msgs in
#check pgcl { { x := 1 } [1⁻¹] { skip } }

@[app_unexpander pGCL.nonDet]
def nonDetUnexpander : Unexpander
| `($(_) $l $r) => do
  let l ← match l with | `(pgcl {$l}) => pure l | _ => `(cpgcl_prog| ~ $l)
  let r ← match r with | `(pgcl {$r}) => pure r | _ => `(cpgcl_prog| ~ $r)
  `(pgcl { { $l } [] {$r} })
| _ => throw ()

/-- info: pgcl {{ x := 1 } [] { skip }} : pGCL String -/
#guard_msgs in
#check pgcl { { x := 1 } [] { skip } }

@[app_unexpander pGCL.loop]
def loopUnexpander : Unexpander
| `($(_) $b $C) => do
  -- let b ← match b with | `(pgcl_bexp {$b}) => pure b | _ => `(cpgcl_bexp| ~ $b)
  let b ← unexpandBExp b
  let C ← match C with | `(pgcl {$C}) => pure C | _ => `(cpgcl_prog| ~ $C)
  `(pgcl { while $b {$C} })
| _ => throw ()

/-- info: pgcl {while x = 1 { skip }} : pGCL String -/
#guard_msgs in
#check pgcl { while x = 1 { skip } }

@[app_unexpander pGCL.tick]
def tickUnexpander : Unexpander
| `($(_) $r) => do
  let r ← unexpandAexp r
  `(pgcl { tick($r) })
| _ => throw ()

/-- info: pgcl {tick(1)} : pGCL ?_ -/
#guard_msgs in
#check pgcl { tick(1) }

/-- info: fun r ↦ pgcl {tick(~r)} : Exp ?_ → pGCL ?_ -/
#guard_msgs in
#check fun r ↦ pgcl { tick(~r) }

@[app_unexpander pGCL.observe]
def observeUnexpander : Unexpander
| `($(_) $r) => do
  let r ← unexpandBExp r
  `(pgcl { observe($r) })
| _ => throw ()

/-- info: pgcl {observe(false) ; observe(true)} : pGCL ?_ -/
#guard_msgs in
#check pgcl { observe(false) ; observe(true) }

@[app_unexpander pGCL.ite]
def iteUnexpander : Unexpander
| `($(_) $b $l $r) => do
  let b ← unexpandBExp b
  let l ← match l with | `(pgcl {$l}) => pure l | _ => `(cpgcl_prog| ~ $l)
  let r ← match r with | `(pgcl {$r}) => pure r | _ => `(cpgcl_prog| ~ $r)
  `(pgcl { if $b then $l else $r end })
| _ => throw ()

/-- info: pgcl {if false then skip else tick(1) end} : pGCL ?_ -/
#guard_msgs in
#check pgcl { if false then skip else tick(1) end }

end Syntax

end pGCL
