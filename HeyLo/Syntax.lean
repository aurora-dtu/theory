import HeyLo.Expr
import HeyLo.pGCL'
import Lean.PrettyPrinter.Delaborator

namespace HeyLo

section Syntax

open Lean PrettyPrinter Delaborator SubExpr

declare_syntax_cat cheylo_var
syntax "heylo_var" ppHardSpace "{" cheylo_var "}" : term
declare_syntax_cat cheylo
syntax "heylo" ppHardSpace "{" cheylo "}" : term
declare_syntax_cat cheyvl
syntax "heyvl" ppHardSpace "{" cheyvl "}" : term
declare_syntax_cat cpgcl'
syntax "pgcl'" ppHardSpace "{" cpgcl' "}" : term

syntax:max "~" term:max : cheylo_var
syntax:max "~" term:max : cheylo
syntax:max "~" term:max : cpgcl'
macro_rules
| `(heylo_var { ~$c }) => `($c)
| `(heylo { ~$c }) => `($c)
| `(pgcl' { ~$c }) => `($c)

syntax ident : cheylo_var

syntax num : cheylo
syntax ident cheylo* : cheylo
syntax "[" cheylo "]" : cheylo
syntax "(" cheylo ")" : cheylo

-- syntax num "⁻¹" : cpgcl_pexp
-- syntax cheylo "⁻¹" : cpgcl_pexp


syntax:70 cheylo:70 " * " cheylo:71 : cheylo
syntax:70 cheylo:70 " / " cheylo:71 : cheylo

syntax:65 cheylo:65 " + " cheylo:66 : cheylo
syntax:65 cheylo:65 " - " cheylo:66 : cheylo

syntax:40 "¬" cheylo:40 : cheylo

syntax:50 cheylo:50 " < " cheylo:51 : cheylo
syntax:50 cheylo:50 " ≤ " cheylo:51 : cheylo
syntax:50 cheylo:50 " <= " cheylo:51 : cheylo
syntax:50 cheylo:50 " >= " cheylo:51 : cheylo
syntax:50 cheylo:50 " ≥ " cheylo:51 : cheylo
syntax:50 cheylo:50 " > " cheylo:51 : cheylo
syntax:45 cheylo:45 " = " cheylo:46 : cheylo
syntax:45 cheylo:45 " != " cheylo:46 : cheylo
syntax:45 cheylo:45 " ≠ " cheylo:46 : cheylo

syntax:35 cheylo:35 " ∧ " cheylo:36 : cheylo
syntax:35 cheylo:35 " ∨ " cheylo:36 : cheylo
syntax:35 cheylo:35 " → " cheylo:36 : cheylo


-- syntax cheylo " + " cheylo : cheylo
-- syntax cheylo " - " cheylo : cheylo
-- syntax cheylo " * " cheylo : cheylo
-- syntax cheylo " / " cheylo : cheylo
-- syntax cheylo " < " cheylo : cheylo
-- syntax cheylo " ≤ " cheylo : cheylo
-- syntax cheylo " = " cheylo : cheylo
-- syntax cheylo " ∧ " cheylo : cheylo
-- syntax cheylo " ∨ " cheylo : cheylo
syntax "(" cheylo ")" : cheylo

syntax ident : cpgcl'
syntax cheylo_var " := " cheylo : cpgcl'
syntax cpgcl' " ; " cpgcl' : cpgcl'
syntax "{ " cpgcl' " }" " [" cheylo "] "  "{ " cpgcl' " }" : cpgcl'
syntax "{ " cpgcl' " }" " [" "] "  "{ " cpgcl' " }" : cpgcl'
syntax "while " cheylo ppHardSpace "inv " cheylo " { " cpgcl' " }" : cpgcl'
syntax "tick(" cheylo ")"  : cpgcl'
syntax "observe(" cheylo ")" : cpgcl'
syntax "if " cheylo " then " cpgcl' " else " cpgcl' " end" : cpgcl'


macro_rules
-- vars
| `(heylo_var { $v:ident }) => `(term|$(quote v.getId.toString))
-- pexp
-- | `(pgcl_pexp { $n:cheylo ⁻¹ }) => `(ProbExp.inv heylo {$n})
| `(heylo { $n:num }) => `(($n : HeyLo _ .ENNReal))
| `(heylo { true }) => `(HeyLo.Lit (.Bool true))
| `(heylo { false }) => `(HeyLo.Lit (.Bool false))
| `(heylo { nfloor $x }) => `(term|HeyLo.Call .NFloor heylo {$x} )
| `(heylo { nlog₂ $x }) => `(term|HeyLo.Call .NLog₂ heylo {$x} )
| `(heylo { isNat $x }) => `(term|HeyLo.Call .IsNat heylo {$x} )
| `(heylo { $v:ident }) => `(term|HeyLo.Var $(quote v.getId.toString))
| `(heylo { $l:cheylo + $r }) => `(heylo {$l} + heylo {$r})
| `(heylo { $l:cheylo - $r }) => `(heylo {$l} - heylo {$r})
| `(heylo { $l:cheylo * $r }) => `(heylo {$l} * heylo {$r})
| `(heylo { $l:cheylo / $r }) => `(heylo {$l} / heylo {$r})
| `(heylo { [$b:cheylo] }) => `(i[heylo {$b}])
| `(heylo { ($a:cheylo) }) => `(heylo {$a})
| `(heylo { $l:cheylo < $r }) => `(HeyLo.Binary .Lt (heylo {$l}) (heylo {$r}))
| `(heylo { $l:cheylo ≤ $r }) => `(HeyLo.Binary .Le (heylo {$l}) (heylo {$r}))
| `(heylo { $l:cheylo = $r }) => `(HeyLo.Binary .Eq (heylo {$l}) (heylo {$r}))
| `(heylo { $l:cheylo ∧ $r }) => `(HeyLo.Binary .And (heylo {$l}) (heylo {$r}))
| `(heylo { $l:cheylo ∨ $r }) => `(HeyLo.Binary .Or (heylo {$l}) (heylo {$r}))
| `(heylo { ¬$l:cheylo }) => `(HeyLo.Unary .Not (heylo {$l}))
-- pGCL'
| `(pgcl' { skip }) => `(pGCL'.skip)
| `(pgcl' { $v:cheylo_var := $e }) => `(pGCL'.assign heylo_var {$v} heylo {$e})
| `(pgcl' { $C₁ ; $C₂ }) => `(pGCL'.seq pgcl' {$C₁} pgcl' {$C₂})
-- | `(pgcl' { { $C₁:cpgcl' } [ $p ] { $C₂ } }) => `(pGCL'.prob pgcl' {$C₁} heylo {$p} pgcl' {$C₂})
| `(pgcl' { { $C₁:cpgcl' } [ $p ] { $C₂ } }) => `(pGCL'.prob pgcl' {$C₁} heylo {$p} pgcl' {$C₂})
| `(pgcl' { { $C₁:cpgcl' } [] { $C₂ } }) => `(pGCL'.nonDet pgcl' {$C₁} pgcl' {$C₂})
| `(pgcl' { while $b inv $i { $C:cpgcl' } }) => `(pGCL'.loop heylo {$b} heylo {$i} pgcl' {$C})
| `(pgcl' { tick($r) }) => `(pGCL'.tick heylo {$r})
| `(pgcl' { observe($b) }) => `(pGCL'.observe heylo {$b})
| `(pgcl' { if $b then $C₁ else $C₂ end }) => `(pGCL'.ite heylo {$b} pgcl' {$C₁} pgcl' {$C₂})

#check (pgcl' { y := nlog₂ (nfloor y) / 2 } : pGCL' String).pGCL

#check pgcl' { while n < 10 inv [n ≤ 10] { {n := n + 2} [1/2] {n := n + 1} } }

set_option linter.style.setOption false
set_option pp.mvars false
set_option linter.style.setOption true

partial def unexpandAexp : TSyntax `term → UnexpandM (TSyntax `cheylo)
| `(heylo { $c }) => pure c
| `($a:num) => `(cheylo|$a:num)
| `(fun $_ ↦ $a:num) => `(cheylo|$a:num)
| `(HeyLo.Var $x:str) =>
    let name := mkIdent <| Name.mkSimple x.getString
    `(cheylo|$name:ident)
| `(fun $σ ↦ $σ' $x:str) =>
  if σ.raw == σ'.raw then
    let name := mkIdent <| Name.mkSimple x.getString
    `(cheylo|$name:ident)
  else
    throw ()
| `(fun $σ ↦ Nat.cast ($σ' $x:str)) =>
  if σ.raw == σ'.raw then
    let name := mkIdent <| Name.mkSimple x.getString
    `(cheylo|$name:ident)
  else
    throw ()
| `($a + $b) => do
  let a ← unexpandAexp a; let b ← unexpandAexp b
  `(cheylo|$a + $b)
| `($a - $b) => do
  let a ← unexpandAexp a; let b ← unexpandAexp b
  `(cheylo|$a - $b)
| `($a * $b) => do
  let a ← unexpandAexp a; let b ← unexpandAexp b
  `(cheylo|$a * $b)
| `($a / $b) => do
  let a ← unexpandAexp a; let b ← unexpandAexp b
  `(cheylo|$a / $b)
| `($a = $b) => do
  let a ← unexpandAexp a; let b ← unexpandAexp b
  `(cheylo|$a = $b)
| `($a < $b) => do
  let a ← unexpandAexp a; let b ← unexpandAexp b
  `(cheylo|$a < $b)
| `($a ≤ $b) => do
  let a ← unexpandAexp a; let b ← unexpandAexp b
  `(cheylo|$a ≤ $b)
| c => `(cheylo|~ $c)

@[app_unexpander HeyLo.Binary]
def BinaryUnexpander : Unexpander
| `($_ $op:ident $l $r) => do
  let l ← unexpandAexp l; let r ← unexpandAexp r
  dbg_trace "{op}"
  match op.getId with
  | `BinOp.Add => `(heylo { $l:cheylo + $r })
  | `BinOp.And => `(heylo { $l:cheylo ∧ $r })
  | `BinOp.Eq => `(heylo { $l:cheylo = $r })
  | `BinOp.Lt => `(heylo { $l:cheylo < $r })
  | `BinOp.Le => `(heylo { $l:cheylo ≤ $r })
  | _ => throw ()
| _ => throw ()

@[app_unexpander HeyLo.Var]
def VarUnexpander : Unexpander
| `($_ $x:str) => do
  let name := mkIdent <| Name.mkSimple x.getString
  `(heylo { $name:ident })
| _ => throw ()

@[app_unexpander HeyLo.Lit]
def LitUnexpander : Unexpander
| `($_ $b) => do
  match b with
  | `($_ $b) => `($b)
  | _ => `(idk)
| _ => throw ()

/-- info: heylo {~true ∧ ~true} : 𝔼b[String] -/
#guard_msgs in
#check (heylo { true ∧ true } : HeyLo String .Bool)

/-- info: heylo {1 + 2 = 2 ∧ ~true} : 𝔼b[String] -/
#guard_msgs in
#check (heylo { ((1 + 2) = 2) ∧ true } : HeyLo String .Bool)

@[app_unexpander pGCL'.skip]
def skipUnexpander : Unexpander
| `($(_)) =>
  let name := mkIdent <| Name.mkSimple "skip"
  `(pgcl' { $name:ident })

/-- info: pgcl' {skip} : pGCL' ?_ -/
#guard_msgs in
#check pgcl' { skip }

@[app_unexpander pGCL'.assign]
def assignUnexpander : Unexpander
| `($(_) $name:str $e) => do
  let name := mkIdent <| Name.mkSimple name.getString
  let e ← unexpandAexp e
  `(pgcl' { $name:ident := $e })
| `($(_) $name $e) => do
  let e ← match e with | `(heylo {$e}) => pure e | _ => `(cheylo| ~ $e)
  `(pgcl' { ~$name := $e })
| _ => throw ()

/-- info: pgcl' {x := x} : pGCL' String -/
#guard_msgs in
#check pgcl' { x := x }

/-- info: pgcl' {x := x - 1} : pGCL' String -/
#guard_msgs in
#check pgcl' { x := x - 1 }

/-- info: pgcl' {x := 1} : pGCL' String -/
#guard_msgs in
#check pgcl' { x := 1 }

@[app_unexpander pGCL'.seq]
def seqUnexpander : Unexpander
| `($(_) $l $r) => do
  let l ← match l with | `(pgcl' {$l}) => pure l | _ => `(cpgcl'| ~ $l)
  let r ← match r with | `(pgcl' {$r}) => pure r | _ => `(cpgcl'| ~ $r)
  `(pgcl' { $l ; $r })
| _ => throw ()

/-- info: pgcl' {x := 1 ; skip} : pGCL' String -/
#guard_msgs in
#check pgcl' { x := 1 ; skip }

@[app_unexpander pGCL'.prob]
def probUnexpander : Unexpander
| `($(_) $l $p $r) => do
  let l ← match l with | `(pgcl' {$l}) => pure l | _ => `(cpgcl'| ~ $l)
  let p ← unexpandAexp p
  let r ← match r with | `(pgcl' {$r}) => pure r | _ => `(cpgcl'| ~ $r)
  `(pgcl' { { $l } [$p] {$r} })
| _ => throw ()

/-- info: pgcl' {{ x := 1 } [1] { skip }} : pGCL' String -/
#guard_msgs in
#check pgcl' { { x := 1 } [1] { skip } }

@[app_unexpander pGCL'.nonDet]
def nonDetUnexpander : Unexpander
| `($(_) $l $r) => do
  let l ← match l with | `(pgcl' {$l}) => pure l | _ => `(cpgcl'| ~ $l)
  let r ← match r with | `(pgcl' {$r}) => pure r | _ => `(cpgcl'| ~ $r)
  `(pgcl' { { $l } [] {$r} })
| _ => throw ()

/-- info: pgcl' {{ x := 1 } [] { skip }} : pGCL' String -/
#guard_msgs in
#check pgcl' { { x := 1 } [] { skip } }

@[app_unexpander pGCL'.loop]
def loopUnexpander : Unexpander
| `($(_) $b $i $C) => do
  -- let b ← match b with | `(heylo {$b}) => pure b | _ => `(cheylo| ~ $b)
  let b ← unexpandAexp b
  let i ← unexpandAexp i
  let C ← match C with | `(pgcl' {$C}) => pure C | _ => `(cpgcl'| ~ $C)
  `(pgcl' { while $b inv $i {$C} })
| _ => throw ()

/-- info: pgcl' {while x = 1 inv ~i[true] { skip }} : pGCL' String -/
#guard_msgs in
#check pgcl' { while x = 1 inv [true] { skip } }

@[app_unexpander pGCL'.tick]
def tickUnexpander : Unexpander
| `($(_) $r) => do
  let r ← unexpandAexp r
  `(pgcl' { tick($r) })
| _ => throw ()

/-- info: pgcl' {tick(1)} : pGCL' ?_ -/
#guard_msgs in
#check pgcl' { tick(1) }

/-- info: fun r ↦ pgcl' {tick(~ r)} : 𝔼r[?_] → pGCL' ?_ -/
#guard_msgs in
#check fun r ↦ pgcl' { tick(~ r) }

@[app_unexpander pGCL'.observe]
def observeUnexpander : Unexpander
| `($(_) $r) => do
  let r ← unexpandAexp r
  `(pgcl' { observe($r) })
| _ => throw ()

/-- info: pgcl' {observe(~false) ; observe(~true)} : pGCL' ?_ -/
#guard_msgs in
#check pgcl' { observe(false) ; observe(true) }

@[app_unexpander pGCL'.ite]
def iteUnexpander : Unexpander
| `($(_) $b $l $r) => do
  let b ← unexpandAexp b
  let l ← match l with | `(pgcl' {$l}) => pure l | _ => `(cpgcl'| ~ $l)
  let r ← match r with | `(pgcl' {$r}) => pure r | _ => `(cpgcl'| ~ $r)
  `(pgcl' { if $b then $l else $r end })
| _ => throw ()

/-- info: pgcl' {if ~false then skip else tick(1) end} : pGCL' ?_ -/
#guard_msgs in
#check pgcl' { if false then skip else tick(1) end }

end Syntax

end HeyLo
