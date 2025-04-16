import Mathlib.Data.ENNReal.Operations
import Lean.ToExpr

namespace WGCL

variable (D : Type) (W : Type) (Var : Type)

def Mem := Var → D

abbrev Weighting := Mem D Var → W
abbrev AExpr := Mem D Var → D
abbrev BExpr := Mem D Var → Prop

inductive wGCL where
  | Branch : wGCL → wGCL → wGCL
  | Weight : Weighting D W Var → wGCL
  | Assign : Var → AExpr D Var → wGCL
  | Ite : BExpr D Var → wGCL → wGCL → wGCL
  | Seq : wGCL → wGCL → wGCL
  | While : BExpr D Var → wGCL → wGCL

section Syntax

open Lean PrettyPrinter Delaborator SubExpr

declare_syntax_cat cwgcl_var
syntax "wgcl_var " "{" cwgcl_var "}" : term
declare_syntax_cat cwgcl_bexp
syntax "wgcl_bexp " "{" cwgcl_bexp "}" : term
declare_syntax_cat cwgcl_aexp
syntax "wgcl_aexp " "{" cwgcl_aexp "}" : term
declare_syntax_cat cwgcl_wght
syntax "wght " "{" cwgcl_wght "}" : term
declare_syntax_cat cwgcl_prog
syntax "wgcl" ppHardSpace "{" cwgcl_prog "}" : term

syntax:max "~" term:max : cwgcl_var
syntax:max "~" term:max : cwgcl_bexp
syntax:max "~" term:max : cwgcl_aexp
syntax:max "~" term:max : cwgcl_wght
syntax:max "~" term:max : cwgcl_prog

syntax ident : cwgcl_var

-- TODO: limited to only true and false
syntax ident : cwgcl_bexp

syntax num : cwgcl_aexp

syntax num : cwgcl_wght
syntax ident : cwgcl_wght


syntax:75 "⊙" cwgcl_wght : cwgcl_prog
syntax cwgcl_var " := " cwgcl_aexp : cwgcl_prog
syntax "{ " cwgcl_prog " }" " ⊕ " "{ " cwgcl_prog " }" : cwgcl_prog
syntax cwgcl_prog ";" ppHardSpace cwgcl_prog : cwgcl_prog
syntax "if " "(" cwgcl_bexp ")" ppHardSpace "{"
    ppLine cwgcl_prog
  ppDedent(ppLine "}" ppHardSpace "else" ppHardSpace "{")
    ppLine cwgcl_prog
  ppDedent(ppLine "}") : cwgcl_prog
syntax "if " "(" cwgcl_bexp ")" ppHardSpace "{" ppLine cwgcl_prog ppDedent(ppLine "}")
  : cwgcl_prog
syntax "while " "(" cwgcl_bexp ")" ppHardSpace "{" ppLine cwgcl_prog ppDedent(ppLine "}")
  : cwgcl_prog
syntax "skip" : cwgcl_prog

open Lean in
macro_rules
-- var
| `(wgcl_var { ~ $v }) => `($v)
| `(wgcl_var { $v:ident }) => `(term|$(quote v.getId.toString))
-- bexp
| `(wgcl_bexp { ~ $b }) => `($b)
| `(wgcl_bexp { true }) => `(term|fun _ ↦ True)
| `(wgcl_bexp { false }) => `(term|fun _ ↦ False)
-- aexp
| `(wgcl_aexp { ~ $x }) => `($x)
| `(wgcl_aexp { $n:num }) => `($n)
-- wght
| `(wght { ~ $x }) => `($x)
| `(wght { $x:num }) => `($x)
| `(wght { $x:ident }) => `(term|fun σ ↦ σ $(quote x.getId.toString))
-- prog
| `(wgcl { ~ $c }) => `($c)
| `(wgcl { ⊙ $b }) => `(wGCL.Weight wght {$b})
| `(wgcl { skip }) => `(wgcl { ⊙ 0 })
| `(wgcl { $x:cwgcl_var := $e }) => `(wGCL.Assign (wgcl_var {$x}) (wgcl_aexp {$e}))
| `(wgcl { {$l} ⊕ {$r} }) => `(wGCL.Branch wgcl {$l} wgcl {$r})
| `(wgcl { $l ; $r }) => `(wGCL.Seq wgcl {$l} wgcl {$r})
| `(wgcl { if ($b) {$l} else {$r} }) => `(wGCL.Ite wgcl_bexp {$b} wgcl {$l} wgcl {$r})
| `(wgcl { if ($b) {$l} }) => `(wGCL.Ite wgcl_bexp {$b} wgcl {$l} wgcl {skip})
| `(wgcl { while ($b) {$l} }) => `(wGCL.While wgcl_bexp {$b} wgcl {$l})

set_option linter.style.setOption false
set_option pp.mvars false
set_option linter.style.setOption true

def unexpandWeighting : TSyntax `term → UnexpandM (TSyntax `cwgcl_wght)
| `($a:num) => `(cwgcl_wght|$a:num)
| `(fun $σ ↦ $σ' $x:str) =>
  if σ.raw == σ'.raw then
    let name := mkIdent <| Name.mkSimple x.getString
    `(cwgcl_wght|$name:ident)
  else
    throw ()
| c => `(cwgcl_wght|~ $c)

@[app_unexpander wGCL.Weight]
def wGCL.unexpandWeight : Unexpander
| `($(_) 0) => `(wgcl { skip })
| `($(_) $x) => do let x ← unexpandWeighting x; `(wgcl {⊙ $x})
| _ => throw ()

/-- info: wgcl {skip} : wGCL ?_ ?_ ?_ -/
#guard_msgs in
#check wgcl {⊙ 0}
/-- info: wgcl {⊙1} : wGCL ?_ ?_ ?_ -/
#guard_msgs in
#check wgcl {⊙ 1}
/-- info: wgcl {⊙x} : wGCL ?_ ?_ String -/
#guard_msgs in
#check wgcl {⊙ x}
/-- info: fun x ↦ wgcl {⊙~x} : Weighting ?_ ?_ ?_ → wGCL ?_ ?_ ?_ -/
#guard_msgs in
#check fun x ↦ wgcl {⊙ ~x}

@[app_unexpander wGCL.Branch]
def wGCL.unexpandBranch : Unexpander
| `($(_) $l $r) => do
  let l := ← match l with | `(wgcl {$l}) => pure l | _ => `(cwgcl_prog| ~ $l)
  let r := ← match r with | `(wgcl {$r}) => pure r | _ => `(cwgcl_prog| ~ $r)
  `(wgcl { {$l} ⊕ {$r} })
| _ => throw ()
@[app_unexpander wGCL.Seq]
def wGCL.unexpandSeq : Unexpander
| `($(_) $l $r) => do
  let l := ← match l with | `(wgcl {$l}) => pure l | _ => `(cwgcl_prog| ~ $l)
  let r := ← match r with | `(wgcl {$r}) => pure r | _ => `(cwgcl_prog| ~ $r)
  `(wgcl { $l; $r })
| _ => throw ()
def wGCL.unexpandBExpr : TSyntax `term → UnexpandM (TSyntax `cwgcl_bexp)
| `(fun $_ ↦ True) => let i := mkIdent <| Name.mkSimple "true"; `(cwgcl_bexp| $i:ident)
| `(fun $_ ↦ False) => let i := mkIdent <| Name.mkSimple "false"; `(cwgcl_bexp| $i:ident)
| c => `(cwgcl_bexp| ~ $c)
def wGCL.unexpandAExpr : TSyntax `term → UnexpandM (TSyntax `cwgcl_aexp)
| `($a:num) => `(cwgcl_aexp| $a:num)
| c => `(cwgcl_aexp| ~ $c)
@[app_unexpander wGCL.Ite]
def wGCL.unexpandIte : Unexpander
| `($(_) $c $l $r) => do
  let c : TSyntax `cwgcl_bexp := ← unexpandBExpr c
  let l := ← match l with | `(wgcl {$l}) => pure l | _ => `(cwgcl_prog| ~ $l)
  match r with
  | `(wgcl {skip}) => `(wgcl { if ($c) { $l } })
  | _ =>
    let r := ←match r with | `(wgcl {$r}) => pure r | _ => `(cwgcl_prog| ~ $r)
    `(wgcl { if ($c) { $l } else { $r } })
| _ => throw ()
@[app_unexpander wGCL.While]
def wGCL.unexpandWhile : Unexpander
| `($(_) $c $l) => do
  let c ← unexpandBExpr c
  let l := ← match l with | `(wgcl {$l}) => pure l | _ => `(cwgcl_prog| ~ $l)
  `(wgcl { while ($c) { $l } })
| _ => throw ()
@[app_unexpander wGCL.Assign]
def wGCL.unexpandAssign : Unexpander
| `($(_) $x:str $E) => do
  let E ← unexpandAExpr E
  let name := mkIdent <| Name.mkSimple x.getString
  `(wgcl { $name:ident := $E })
| _ => throw ()

/-- info: wgcl {skip; x := 0} : wGCL ?_ ?_ String -/
#guard_msgs in
#check wgcl { skip; x := 0 }

/--
info: wgcl {if (true) {
    skip
  }} : wGCL ?_ ?_ ?_
-/
#guard_msgs in
#check wgcl { if (true) { skip } else { skip } }

/--
info: wgcl {if (false) {
    skip
  }} : wGCL ?_ ?_ ?_
-/
#guard_msgs in
#check wgcl { if (false) { skip } }

/-- info: wgcl {⊙x} : wGCL ?_ ?_ String -/
#guard_msgs in
#check wgcl {⊙ x}

end Syntax

end WGCL
