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
  | assert : BExpr ϖ → pGCL ϖ
deriving Inhabited

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
declare_syntax_cat cpgcl_prog
syntax "pgcl" ppHardSpace "{" cpgcl_prog "}" : term

syntax:max "~" term:max : cpgcl_var
syntax:max "~" term:max : cpgcl_bexp
syntax:max "~" term:max : cpgcl_aexp
syntax:max "~" term:max : cpgcl_prog
macro_rules
| `(pgcl_var { ~$c }) => `($c)
| `(pgcl_bexp { ~$c }) => `($c)
| `(pgcl_aexp { ~$c }) => `($c)
| `(pgcl { ~$c }) => `($c)

syntax ident : cpgcl_var

syntax num : cpgcl_aexp
syntax ident : cpgcl_aexp

syntax ident : cpgcl_bexp

syntax ident : cpgcl_prog
syntax cpgcl_var " := " cpgcl_aexp : cpgcl_prog
syntax cpgcl_prog " ; " cpgcl_prog : cpgcl_prog
syntax "{ " cpgcl_prog " }" " [" cpgcl_aexp "] "  "{ " cpgcl_prog " }" : cpgcl_prog
syntax "{ " cpgcl_prog " }" " [" "] "  "{ " cpgcl_prog " }" : cpgcl_prog
syntax "while " cpgcl_bexp " { " cpgcl_prog " }" : cpgcl_prog
syntax "tick(" cpgcl_aexp ")"  : cpgcl_prog
syntax "assert(" cpgcl_bexp ")" : cpgcl_prog

macro_rules
-- vars
| `(pgcl_var { $v:ident }) => `(term|$(quote v.getId.toString))
-- aexp
| `(pgcl_aexp { $n:num }) => `($n)
| `(pgcl_aexp { $v:ident }) => `(term|$(quote v.getId.toString))
-- bexp
| `(pgcl_bexp { true }) => `(fun _ ↦ true)
| `(pgcl_bexp { false }) => `(fun _ ↦ false)
| `(pgcl_bexp { $v:ident }) => `(term|$(quote v.getId.toString))
-- pGCL
| `(pgcl { skip }) => `(pGCL.skip)
| `(pgcl { $v:cpgcl_var := $e }) => `(pGCL.assign pgcl_var {$v} pgcl_aexp {$e})
| `(pgcl { $C₁ ; $C₂ }) => `(pGCL.seq pgcl {$C₁} pgcl {$C₂})
| `(pgcl { { $C₁:cpgcl_prog } [ $p ] { $C₂ } }) => `(pGCL.prob pgcl {$C₁} pgcl_aexp {$p} pgcl {$C₂})
| `(pgcl { { $C₁:cpgcl_prog } [] { $C₂ } }) => `(pGCL.nonDet pgcl {$C₁} pgcl {$C₂})
| `(pgcl { while $b { $C:cpgcl_prog } }) => `(pGCL.loop pgcl_bexp {$b} pgcl {$C})
| `(pgcl { tick($r) }) => `(pGCL.tick pgcl_aexp {$r})
| `(pgcl { assert($b) }) => `(pGCL.assert pgcl_bexp {$b})

set_option linter.style.setOption false
set_option pp.mvars false
set_option linter.style.setOption true

def unexpandAexp : TSyntax `term → UnexpandM (TSyntax `cpgcl_aexp)
| `($a:num) => `(cpgcl_aexp|$a:num)
| `(fun $σ ↦ $σ' $x:str) =>
  if σ.raw == σ'.raw then
    let name := mkIdent <| Name.mkSimple x.getString
    `(cpgcl_aexp|$name:ident)
  else
    throw ()
| c => `(cpgcl_aexp|~ $c)

def unexpandBExp : TSyntax `term → UnexpandM (TSyntax `cpgcl_bexp)
| `(fun $_ ↦ true) =>
  let name := mkIdent <| Name.mkSimple "true"
  `(cpgcl_bexp| $name:ident)
| `(fun $_ ↦ false) =>
  let name := mkIdent <| Name.mkSimple "false"
  `(cpgcl_bexp| $name:ident)
| `(fun $σ ↦ $σ' $x:str) =>
  if σ.raw == σ'.raw then
    let name := mkIdent <| Name.mkSimple x.getString
    `(cpgcl_bexp|$name:ident)
  else
    throw ()
| c => `(cpgcl_bexp|~ $c)

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

/-- info: pgcl {x := 1} : pGCL String -/
#guard_msgs in
#check pgcl { x := 1 }

@[app_unexpander pGCL.seq]
def seqUnexpander : Unexpander
| `($(_) $l $r) => do
  let l := ← match l with | `(pgcl {$l}) => pure l | _ => `(cpgcl_prog| ~ $l)
  let r := ← match r with | `(pgcl {$r}) => pure r | _ => `(cpgcl_prog| ~ $r)
  `(pgcl { $l ; $r })
| _ => throw ()

/-- info: pgcl {x := 1 ; skip} : pGCL String -/
#guard_msgs in
#check pgcl { x := 1 ; skip }

@[app_unexpander pGCL.prob]
def probUnexpander : Unexpander
| `($(_) $l $p $r) => do
  let l := ← match l with | `(pgcl {$l}) => pure l | _ => `(cpgcl_prog| ~ $l)
  let p := ← match p with | `(pgcl_aexp {$p}) => pure p | _ => `(cpgcl_aexp| ~ $p)
  let r := ← match r with | `(pgcl {$r}) => pure r | _ => `(cpgcl_prog| ~ $r)
  `(pgcl { { $l } [$p] {$r} })
| _ => throw ()

/-- info: pgcl {{ x := 1 } [~⟨1, ⋯⟩] { skip }} : pGCL String -/
#guard_msgs in
#check pgcl { { x := 1 } [~⟨1, by simp⟩] { skip } }

@[app_unexpander pGCL.nonDet]
def nonDetUnexpander : Unexpander
| `($(_) $l $r) => do
  let l := ← match l with | `(pgcl {$l}) => pure l | _ => `(cpgcl_prog| ~ $l)
  let r := ← match r with | `(pgcl {$r}) => pure r | _ => `(cpgcl_prog| ~ $r)
  `(pgcl { { $l } [] {$r} })
| _ => throw ()

/-- info: pgcl {{ x := 1 } [] { skip }} : pGCL String -/
#guard_msgs in
#check pgcl { { x := 1 } [] { skip } }

@[app_unexpander pGCL.loop]
def loopUnexpander : Unexpander
| `($(_) $b $C) => do
  let b := ← match b with | `(pgcl_bexp {$b}) => pure b | _ => `(cpgcl_bexp| ~ $b)
  let C := ← match C with | `(pgcl {$C}) => pure C | _ => `(cpgcl_prog| ~ $C)
  `(pgcl { while $b {$C} })
| _ => throw ()

/-- info: pgcl {while ~fun σ ↦ decide (σ "x" = 1) { skip }} : pGCL String -/
#guard_msgs in
#check pgcl { while ~(fun σ ↦ σ "x" = 1) { skip } }

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

@[app_unexpander pGCL.assert]
def assertUnexpander : Unexpander
| `($(_) $r) => do
  let r ← unexpandBExp r
  `(pgcl { assert($r) })
| _ => throw ()

/-- info: pgcl {assert(false) ; assert(true)} : pGCL ?_ -/
#guard_msgs in
#check pgcl { assert(false) ; assert(true) }

end Syntax

end pGCL
