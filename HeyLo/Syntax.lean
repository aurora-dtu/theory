import HeyLo.Expr
import HeyLo.pGCL'
import Lean.PrettyPrinter.Delaborator

namespace HeyLo

namespace Syntax

open Lean PrettyPrinter Delaborator SubExpr

declare_syntax_cat cheylo_var
syntax "heylo_var" ppHardSpace "{" cheylo_var "}" : term
declare_syntax_cat cheylo_vars
syntax "heylo_vars" ppHardSpace "{" cheylo_vars "}" : term
declare_syntax_cat cheylo_dist
syntax "heylo_dist" ppHardSpace "{" cheylo_dist "}" : term
declare_syntax_cat cheylo
syntax "heylo" ppHardSpace "{" cheylo "}" : term
declare_syntax_cat cheyvl
syntax "heyvl" ppHardSpace "{" cheyvl "}" : term
declare_syntax_cat cpgcl'
syntax "pgcl'" ppHardSpace "{" cpgcl' "}" : term

syntax:max "~" term:max : cheylo_var
syntax:max "~" term:max : cheylo_vars
syntax:max "~" term:max : cheylo_dist
syntax:max "~" term:max : cheylo
syntax:max "~" term:max : cheyvl
syntax:max "~" term:max : cpgcl'
macro_rules
| `(heylo_var { ~$c }) => `($c)
| `(heylo_vars { ~$c }) => `($c)
| `(heylo_dist { ~$c }) => `($c)
| `(heylo { ~$c }) => `($c)
| `(heyvl { ~$c }) => `($c)
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
syntax:80 "↑" cheylo:80 : cheylo

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
syntax "while " cheylo ppHardSpace "inv(" cheylo ")" " { " cpgcl' " }" : cpgcl'
syntax "tick(" cheylo ")"  : cpgcl'
syntax "observe(" cheylo ")" : cpgcl'
syntax "if " cheylo " then " cpgcl' " else " cpgcl' " end" : cpgcl'

syntax ident : cheyvl
syntax cheylo_var " :≈ " cheylo_dist : cheyvl
syntax "reward(" cheylo ")" : cheyvl
syntax cheyvl " ; " cheyvl : cheyvl
  --
syntax "if" ppHardSpace "(⊓)" ppHardSpace "{" cheyvl "}" " else " "{" cheyvl "}" : cheyvl
syntax "assert(" cheylo ")" : cheyvl
syntax "assume(" cheylo ")" : cheyvl
syntax "havoc(" cheylo_var ")" : cheyvl
syntax "havocs(" cheylo_vars ")" : cheyvl
-- syntax "validate" : cheyvl
--
syntax "if" ppHardSpace "(⊔)" ppHardSpace "{" cheyvl "}" " else " "{" cheyvl "}" : cheyvl
syntax "coassert(" cheylo ")" : cheyvl
syntax "coassume(" cheylo ")" : cheyvl
syntax "cohavoc(" cheylo_var ")" : cheyvl
syntax "cohavocs(" cheylo_vars ")" : cheyvl
-- syntax "covalidate" : cheyvl
--
syntax "if" ppHardSpace "(" cheylo ")" ppHardSpace "{" cheyvl "}" " else " "{" cheyvl "}" : cheyvl
syntax "if" ppHardSpace "(" cheylo ")" ppHardSpace "{" cheyvl "}" : cheyvl

macro_rules
-- vars
| `(heylo_var { $v:ident }) => `(term|$(quote v.getId.toString))
-- pexp
| `(heylo { $n:num }) => `(($n : HeyLo _))
| `(heylo { true }) => `(HeyLo.Lit (.Bool true))
| `(heylo { false }) => `(HeyLo.Lit (.Bool false))
| `(heylo { nfloor $x }) => `(term|HeyLo.Call .NFloor heylo {$x} )
| `(heylo { nlog₂ $x }) => `(term|HeyLo.Call .NLog₂ heylo {$x} )
| `(heylo { isNat $x }) => `(term|HeyLo.Call .IsNat heylo {$x} )
| `(heylo { $v:ident }) => `(term|HeyLo.Var ($v).name ($v).type)
| `(heylo { $l:cheylo + $r }) => `(heylo {$l} + heylo {$r})
| `(heylo { $l:cheylo - $r }) => `(heylo {$l} - heylo {$r})
| `(heylo { $l:cheylo * $r }) => `(heylo {$l} * heylo {$r})
| `(heylo { $l:cheylo / $r }) => `(heylo {$l} / heylo {$r})
| `(heylo { [$b:cheylo] }) => `(i[heylo {$b}])
| `(heylo { ($a:cheylo) }) => `(heylo {$a})
| `(heylo { $l:cheylo < $r }) => `(HeyLo.Binary (.Lt Yes.yes) (heylo {$l}) (heylo {$r}))
| `(heylo { $l:cheylo ≤ $r }) => `(HeyLo.Binary (.Le Yes.yes) (heylo {$l}) (heylo {$r}))
| `(heylo { $l:cheylo = $r }) => `(HeyLo.Binary .Eq (heylo {$l}) (heylo {$r}))
| `(heylo { $l:cheylo ≠ $r }) => `(HeyLo.Binary (.Ne Yes.yes) (heylo {$l}) (heylo {$r}))
| `(heylo { $l:cheylo ∧ $r }) => `(HeyLo.Binary .And (heylo {$l}) (heylo {$r}))
| `(heylo { $l:cheylo ∨ $r }) => `(HeyLo.Binary .Or (heylo {$l}) (heylo {$r}))
| `(heylo { ¬$l:cheylo }) => `(HeyLo.Unary .Not (heylo {$l}))
| `(heylo { ↑ $l:cheylo }) => `(HeyLo.Unary .NatToENNReal (heylo {$l}))
-- pGCL'
| `(pgcl' { skip }) => `(pGCL'.skip)
| `(pgcl' { $v:ident := $e }) => `(pGCL'.assign $v heylo {$e})
| `(pgcl' { $C₁ ; $C₂ }) => `(pGCL'.seq pgcl' {$C₁} pgcl' {$C₂})
-- | `(pgcl' { { $C₁:cpgcl' } [ $p ] { $C₂ } }) => `(pGCL'.prob pgcl' {$C₁} heylo {$p} pgcl' {$C₂})
| `(pgcl' { { $C₁:cpgcl' } [ $p ] { $C₂ } }) => `(pGCL'.prob pgcl' {$C₁} heylo {$p} pgcl' {$C₂})
| `(pgcl' { { $C₁:cpgcl' } [] { $C₂ } }) => `(pGCL'.nonDet pgcl' {$C₁} pgcl' {$C₂})
| `(pgcl' { while $b inv($i) { $C:cpgcl' } }) => `(pGCL'.loop heylo {$b} heylo {$i} pgcl' {$C})
| `(pgcl' { tick($r) }) => `(pGCL'.tick heylo {$r})
| `(pgcl' { observe($b) }) => `(pGCL'.observe heylo {$b})
| `(pgcl' { if $b then $C₁ else $C₂ end }) => `(pGCL'.ite heylo {$b} pgcl' {$C₁} pgcl' {$C₂})
-- HeyVL
| `(heyvl { $x:cheylo_var :≈ $μ }) => `(HeyVL.Assign heylo_var {$x} heylo_dist {$μ})
| `(heyvl { reward($a) }) => `(HeyVL.Reward heylo {$a})
| `(heyvl { $S₁:cheyvl ; $S₂ }) => `(HeyVL.Seq heyvl {$S₁} heyvl {$S₂})
| `(heyvl { if (⊓) { $S₁:cheyvl } else { $S₂ } }) => `(HeyVL.IfInf heyvl {$S₁} heyvl {$S₂})
| `(heyvl { assert($φ) }) => `(HeyVL.Assert heylo {$φ})
| `(heyvl { assume($φ) }) => `(HeyVL.Assume heylo {$φ})
| `(heyvl { havoc($x:cheylo_var) }) => `(HeyVL.Havoc heylo_var {$x})
| `(heyvl { havocs($xs:cheylo_vars) }) => `(HeyVL.Havocs heylo_vars {$xs})
| `(heyvl { validate }) => `(HeyVL.Validate)
| `(heyvl { if (⊔) { $S₁:cheyvl } else { $S₂ } }) => `(HeyVL.IfSup heyvl {$S₁} heyvl {$S₂})
| `(heyvl { coassert($φ) }) => `(HeyVL.Coassert heylo {$φ})
| `(heyvl { coassume($φ) }) => `(HeyVL.Coassume heylo {$φ})
| `(heyvl { cohavoc($x:cheylo_var) }) => `(HeyVL.Cohavoc heylo_var {$x})
| `(heyvl { cohavocs($xs:cheylo_vars) }) => `(HeyVL.Cohavocs heylo_vars {$xs})
| `(heyvl { covalidate }) => `(HeyVL.Covalidate)
-- Sugar
| `(heyvl { skip }) => `(HeyVL.Skip)
| `(heyvl { if ($b:cheylo) {$S₁:cheyvl} else {$S₂}}) =>
    `(HeyVL.If heylo {$b} heyvl {$S₁} heyvl {$S₂})
| `(heyvl { if ($b:cheylo) {$S₁:cheyvl} }) => `(HeyVL.If heylo {$b} heyvl {$S₁} heyvl {skip})

abbrev y : Ident := ⟨"y", .ENNReal⟩
abbrev z : Ident := ⟨"z", .Nat⟩
abbrev n : Ident := ⟨"n", .Nat⟩

set_option linter.style.setOption false
set_option pp.mvars false
set_option linter.style.setOption true

@[app_unexpander HeyLo.Var]
def VarUnexpander : Unexpander
| `($_ $x $_) => do
  match x with
  | `($a:ident.$_) => `(heylo {$a:ident})
  | _ => throw ()
| _ => throw ()

/-- info: heylo {y} : HeyLo y.type -/
#guard_msgs in
#check heylo { y }

partial def unexpandAexp : TSyntax `term → UnexpandM (TSyntax `cheylo)
| `(heylo { $c }) => pure c
| `($a:num) => `(cheylo|$a:num)
| `(fun $_ ↦ $a:num) => `(cheylo|$a:num)
| c@`(HeyLo.Var $x $_) =>
    match x with
    | `($a:ident.$_) => `(cheylo| $a:ident)
    | _ => `(cheylo|~ $c)
    -- let name := mkIdent <| Name.mkSimple x.getString
    -- `(cheylo|$name:ident)
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
| `(true) => do
  let name := mkIdent <| Name.mkSimple "true"
  `(cheylo|$name:ident)
| `(false) => do
  let name := mkIdent <| Name.mkSimple "false"
  `(cheylo|$name:ident)
| `(i[$a]) => do
  let a ← unexpandAexp a
  `(cheylo|[$a])
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
| `($a ≠ $b) => do
  let a ← unexpandAexp a; let b ← unexpandAexp b
  `(cheylo|$a ≠ $b)
| `($a < $b) => do
  let a ← unexpandAexp a; let b ← unexpandAexp b
  `(cheylo|$a < $b)
| `($a ≤ $b) => do
  let a ← unexpandAexp a; let b ← unexpandAexp b
  `(cheylo|$a ≤ $b)
| c => `(cheylo|~ $c)

@[app_unexpander HeyLo.Binary]
def BinaryUnexpander : Unexpander
| `($_ $op $l $r) => do
  dbg_trace "{op}"
  let op ←
    match op with
    | `($op:ident $_) => pure op
    | `($op:ident) => pure op
    | _ => throw ()
  let l ← unexpandAexp l; let r ← unexpandAexp r
  dbg_trace "{op}"
  match op.getId with
  | `BinOp.Add => `(heylo { $l:cheylo + $r })
  | `BinOp.And => `(heylo { $l:cheylo ∧ $r })
  | `BinOp.Eq => `(heylo { $l:cheylo = $r })
  | `BinOp.Ne => `(heylo { $l:cheylo ≠ $r })
  | `BinOp.Lt => `(heylo { $l:cheylo < $r })
  | `BinOp.Le => `(heylo { $l:cheylo ≤ $r })
  | _ => throw ()
| _ => throw ()

/-- info: heylo {1 < y} : 𝔼b -/
#guard_msgs in
#check heylo { 1 < y }

@[app_unexpander HeyLo.Lit]
def LitUnexpander : Unexpander
| `($_ $b) => do
  match b with
  | `($_ $b) => `($b)
  | _ => `(idk)
| _ => throw ()

/-- info: heylo {true ∧ true} : 𝔼b -/
#guard_msgs in
#check (heylo { true ∧ true } : HeyLo .Bool)

/-- info: heylo {1 + 2 = 2 ∧ true} : 𝔼b -/
#guard_msgs in
#check (heylo { ((1 + 2) = 2) ∧ true } : HeyLo .Bool)

/-- info: Call Fun.NLog₂ (Call Fun.NFloor (heylo {y})) : HeyLo Ty.Nat -/
#guard_msgs in
#check (heylo { nlog₂ (nfloor y) } : HeyLo .Nat)
/-- info: heylo {y ≤ y} : 𝔼b -/
#guard_msgs in
#check (heylo { y ≤ y } : HeyLo .Bool)

@[app_unexpander pGCL'.skip]
def skipUnexpander : Unexpander
| `($(_)) =>
  let name := mkIdent <| Name.mkSimple "skip"
  `(pgcl' { $name:ident })

/-- info: pgcl' {skip} : pGCL' -/
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

abbrev x : Ident := ⟨"x", .ENNReal⟩

/-- info: pgcl' {~x := x} : pGCL' -/
#guard_msgs in
#check pgcl' { x := x }

/-- info: pgcl' {~x := ~(heylo {x} - 1)} : pGCL' -/
#guard_msgs in
#check pgcl' { x := x - 1 }

/-- info: pgcl' {~x := ~1} : pGCL' -/
#guard_msgs in
#check pgcl' { x := 1 }

@[app_unexpander pGCL'.seq]
def seqUnexpander : Unexpander
| `($(_) $l $r) => do
  let l ← match l with | `(pgcl' {$l}) => pure l | _ => `(cpgcl'| ~ $l)
  let r ← match r with | `(pgcl' {$r}) => pure r | _ => `(cpgcl'| ~ $r)
  `(pgcl' { $l ; $r })
| _ => throw ()

/-- info: pgcl' {~x := ~1 ; skip} : pGCL' -/
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

/-- info: pgcl' {{ ~x := ~1 } [1] { skip }} : pGCL' -/
#guard_msgs in
#check pgcl' { { x := 1 } [1] { skip } }

@[app_unexpander pGCL'.nonDet]
def nonDetUnexpander : Unexpander
| `($(_) $l $r) => do
  let l ← match l with | `(pgcl' {$l}) => pure l | _ => `(cpgcl'| ~ $l)
  let r ← match r with | `(pgcl' {$r}) => pure r | _ => `(cpgcl'| ~ $r)
  `(pgcl' { { $l } [] {$r} })
| _ => throw ()

/-- info: pgcl' {{ ~x := ~1 } [] { skip }} : pGCL' -/
#guard_msgs in
#check pgcl' { { x := 1 } [] { skip } }

@[app_unexpander pGCL'.loop]
def loopUnexpander : Unexpander
| `($(_) $b $i $C) => do
  let b ← unexpandAexp b
  let i ← unexpandAexp i
  let C ← match C with | `(pgcl' {$C}) => pure C | _ => `(cpgcl'| ~ $C)
  `(pgcl' { while $b inv($i) {$C} })
| _ => throw ()

/-- info: pgcl' {while x = 1 inv([true]) { skip }} : pGCL' -/
#guard_msgs in
#check pgcl' { while x = 1 inv([true]) { skip } }

@[app_unexpander pGCL'.tick]
def tickUnexpander : Unexpander
| `($(_) $r) => do
  let r ← unexpandAexp r
  `(pgcl' { tick($r) })
| _ => throw ()

/-- info: pgcl' {tick(1)} : pGCL' -/
#guard_msgs in
#check pgcl' { tick(1) }

/-- info: fun r ↦ pgcl' {tick(~ r)} : 𝔼r → pGCL' -/
#guard_msgs in
#check fun r ↦ pgcl' { tick(~ r) }

@[app_unexpander pGCL'.observe]
def observeUnexpander : Unexpander
| `($(_) $r) => do
  let r ← unexpandAexp r
  `(pgcl' { observe($r) })
| _ => throw ()

/-- info: pgcl' {observe(false) ; observe(true)} : pGCL' -/
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

/-- info: pgcl' {if false then skip else tick(1) end} : pGCL' -/
#guard_msgs in
#check pgcl' { if false then skip else tick(1) end }

/--
info: pgcl' {~z := ~(Call Fun.NLog₂ (Call Fun.NFloor (heylo {y})))}.pGCL : pGCL fun x ↦ x.type.lit
-/
#guard_msgs in
#check (pgcl' { z := nlog₂ (nfloor y) } : pGCL').pGCL

/--
info: pgcl' {while n < 10 inv([n ≤ 10]) { { ~n := ~(heylo {n} + 2) } [1 / 2] { ~n := ~(heylo {n} + 1) } }} : pGCL'
-/
#guard_msgs in
#check pgcl' { while n < 10 inv([n ≤ 10]) { {n := n + 2} [1/2] {n := n + 1} } }

@[app_unexpander HeyVL.Skip]
def HeyVL.skipUnexpander : Unexpander
| `($(_)) => do
  let name := mkIdent <| Name.mkSimple "skip"
  `(heyvl { $name:ident })

@[app_unexpander HeyVL.If]
def ifUnexpander : Unexpander
| `($(_) $b $S₁ $S₂) => do
  let b ← unexpandAexp b
  let S₁ ← match S₁ with | `(heyvl {$S₁}) => pure S₁ | _ => `(cheyvl| ~ $S₁)
  match S₂ with
  | `(heyvl {skip}) => `(heyvl { if ($b) { $S₁ } })
  | S₂ =>
    let S₂ ← match S₂ with | `(heyvl {$S₂}) => pure S₂ | _ => `(cheyvl| ~ $S₂)
    `(heyvl { if ($b) { $S₁ } else { $S₂ } })
| _ => throw ()

/-- info: heyvl {if (true) {skip}} : HeyVL -/
#guard_msgs in
#check heyvl { if (true) {skip} else {skip} }

@[app_unexpander HeyVL.Reward]
def rewardUnexpander : Unexpander
| `($(_) $a) => do
  let a ← unexpandAexp a
  `(heyvl { reward($a) })
| _ => throw ()

@[app_unexpander HeyVL.Seq]
def heyvlSeqUnexpander : Unexpander
| `($(_) $S₁ $S₂) => do
  let S₁ ← match S₁ with | `(heyvl {$S₁}) => pure S₁ | _ => `(cheyvl| ~ $S₁)
  let S₂ ← match S₂ with | `(heyvl {$S₂}) => pure S₂ | _ => `(cheyvl| ~ $S₂)
  `(heyvl { $S₁ ; $S₂ })
| _ => throw ()

@[app_unexpander HeyVL.IfInf]
def ifInfUnexpander : Unexpander
| `($(_) $S₁ $S₂) => do
  let S₁ ← match S₁ with | `(heyvl {$S₁}) => pure S₁ | _ => `(cheyvl| ~ $S₁)
  let S₂ ← match S₂ with | `(heyvl {$S₂}) => pure S₂ | _ => `(cheyvl| ~ $S₂)
  `(heyvl { if (⊓) { $S₁ } else { $S₂ } })
| _ => throw ()

@[app_unexpander HeyVL.Assert]
def assertUnexpander : Unexpander
| `($(_) $φ) => do
  let φ ← unexpandAexp φ
  `(heyvl { assert($φ) })
| _ => throw ()

@[app_unexpander HeyVL.Assume]
def assumeUnexpander : Unexpander
| `($(_) $φ) => do
  let φ ← unexpandAexp φ
  `(heyvl { assume($φ) })
| _ => throw ()

@[app_unexpander HeyVL.Havoc]
def havocUnexpander : Unexpander
| `($(_) $x) => do
  let x ← match x with | `(heylo_var {$x}) => pure x | _ => `(cheylo_var| ~ $x)
  `(heyvl { havoc($x) })
| _ => throw ()

@[app_unexpander HeyVL.Validate]
def validateUnexpander : Unexpander
| `($(_)) =>
  let name := mkIdent <| Name.mkSimple "validate"
  `(heyvl { $name:ident })

@[app_unexpander HeyVL.IfSup]
def ifSupUnexpander : Unexpander
| `($(_) $S₁ $S₂) => do
  let S₁ ← match S₁ with | `(heyvl {$S₁}) => pure S₁ | _ => `(cheyvl| ~ $S₁)
  let S₂ ← match S₂ with | `(heyvl {$S₂}) => pure S₂ | _ => `(cheyvl| ~ $S₂)
  `(heyvl { if (⊔) { $S₁ } else { $S₂ } })
| _ => throw ()

@[app_unexpander HeyVL.Coassert]
def coassertUnexpander : Unexpander
| `($(_) $φ) => do
  let φ ← unexpandAexp φ
  `(heyvl { coassert($φ) })
| _ => throw ()

@[app_unexpander HeyVL.Coassume]
def coassumeUnexpander : Unexpander
| `($(_) $φ) => do
  let φ ← unexpandAexp φ
  `(heyvl { coassume($φ) })
| _ => throw ()

@[app_unexpander HeyVL.Cohavoc]
def cohavocUnexpander : Unexpander
| `($(_) $x) => do
  let x ← match x with | `(heylo_var {$x}) => pure x | _ => `(cheylo_var| ~ $x)
  `(heyvl { cohavoc($x) })
| _ => throw ()

@[app_unexpander HeyVL.Covalidate]
def covalidateUnexpander : Unexpander
| `($(_)) =>
  let name := mkIdent <| Name.mkSimple "covalidate"
  `(heyvl { $name:ident })
-- | _ => throw ()
/-- info: heyvl {reward(1)} : HeyVL -/
#guard_msgs in
#check heyvl { reward(1) }

/-- info: heyvl {reward(y)} : HeyVL -/
#guard_msgs in
#check heyvl { reward(y) }

/-- info: heyvl {validate} : HeyVL -/
#guard_msgs in
#check heyvl { validate }

/-- info: heyvl {assert([y ≤ 10])} : HeyVL -/
#guard_msgs in
#check heyvl { assert([y ≤ 10]) }

/-- info: heyvl {assume([0 < y])} : HeyVL -/
#guard_msgs in
#check heyvl { assume([0 < y]) }

/-- info: heyvl {covalidate} : HeyVL -/
#guard_msgs in
#check heyvl { covalidate }

/-- info: heyvl {coassert([y ≤ 100])} : HeyVL -/
#guard_msgs in
#check heyvl { coassert([y ≤ 100]) }

/-- info: heyvl {coassume([y ≠ 0])} : HeyVL -/
#guard_msgs in
#check heyvl { coassume([y ≠ 0]) }

/-- info: heyvl {reward(1) ; validate} : HeyVL -/
#guard_msgs in
#check heyvl { reward(1) ; validate }

/-- info: heyvl {assert([y ≤ 10]) ; reward(y)} : HeyVL -/
#guard_msgs in
#check heyvl { assert([y ≤ 10]) ; reward(y) }

/-- info: heyvl {if (⊓) {reward(1)} else {reward(2)}} : HeyVL -/
#guard_msgs in
#check heyvl { if (⊓) { reward(1) } else { reward(2) } }

/-- info: heyvl {if (⊔) {assert([0 < y])} else {assume([y ≤ 0])}} : HeyVL -/
#guard_msgs in
#check heyvl { if (⊔) { assert([0 < y]) } else { assume([y ≤ 0]) } }

/-- info: heyvl {validate ; reward(5) ; validate} : HeyVL -/
#guard_msgs in
#check heyvl { validate ; reward(5) ; validate }

/-- info: heyvl {if (1 = 2) {skip}} : HeyVL -/
#guard_msgs in
#check heyvl { if (1 = 2) {skip} else {skip} }

end Syntax

end HeyLo
