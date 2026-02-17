import HeyLo.HeyVL
import HeyLo.spGCL
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
declare_syntax_cat cspGCL
syntax "spgcl" ppHardSpace "{" cspGCL "}" : term

syntax:max "@" term:max : cheylo_var
syntax:max "@" term:max : cheylo_vars
syntax:max "@" term:max : cheylo_dist
syntax:max "@" term:max : cheylo
syntax:max "@" term:max : cheyvl
syntax:max "@" term:max : cspGCL
macro_rules
| `(heylo_var { @$c }) => `($c)
| `(heylo_vars { @$c }) => `($c)
| `(heylo_dist { @$c }) => `($c)
| `(heylo { @$c }) => `($c)
| `(heyvl { @$c }) => `($c)
| `(spgcl { @$c }) => `($c)

syntax ident : cheylo_var

syntax num : cheylo
syntax "⊤" : cheylo
syntax ident cheylo* : cheylo
syntax "[" cheylo "]" : cheylo
syntax "(" cheylo ")" : cheylo

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

syntax "⨅ " cheylo_var ", " cheylo : cheylo
syntax "⨆ " cheylo_var ", " cheylo : cheylo
syntax "∀ " cheylo_var ", " cheylo : cheylo
syntax "∃ " cheylo_var ", " cheylo : cheylo

syntax "(" cheylo ")" : cheylo

syntax "flip(" cheylo ")" : cheylo_dist
syntax "bin(" cheylo ", " cheylo ", " cheylo ")" : cheylo_dist

syntax ident : cspGCL
syntax cheylo_var " := " cheylo : cspGCL
syntax cspGCL " ; " cspGCL : cspGCL
syntax "{ " cspGCL " }" " [" cheylo "] "  "{ " cspGCL " }" : cspGCL
syntax "{ " cspGCL " }" " [" "] "  "{ " cspGCL " }" : cspGCL
syntax "while " cheylo ppHardSpace "inv(" cheylo ")" " { " cspGCL " }" : cspGCL
syntax "tick(" cheylo ")"  : cspGCL
syntax "observe(" cheylo ")" : cspGCL
syntax "if " cheylo " then " cspGCL " else " cspGCL " end" : cspGCL

syntax ident : cheyvl
syntax cheylo_var " :≈ " cheylo_dist : cheyvl
syntax "reward(" cheylo ")" : cheyvl
syntax cheyvl " ; " cheyvl : cheyvl

syntax "if" ppHardSpace "(⊓)" ppHardSpace "{" cheyvl "}" " else " "{" cheyvl "}" : cheyvl
syntax "assert(" cheylo ")" : cheyvl
syntax "assume(" cheylo ")" : cheyvl
syntax "havoc(" cheylo_var ")" : cheyvl
syntax "havocs(" cheylo_vars ")" : cheyvl

syntax "if" ppHardSpace "(⊔)" ppHardSpace "{" cheyvl "}" " else " "{" cheyvl "}" : cheyvl
syntax "coassert(" cheylo ")" : cheyvl
syntax "coassume(" cheylo ")" : cheyvl
syntax "cohavoc(" cheylo_var ")" : cheyvl
syntax "cohavocs(" cheylo_vars ")" : cheyvl

syntax "if" ppHardSpace "(" cheylo ")" ppHardSpace "{" cheyvl "}" " else " "{" cheyvl "}" : cheyvl
syntax "if" ppHardSpace "(" cheylo ")" ppHardSpace "{" cheyvl "}" : cheyvl

macro_rules
-- vars
| `(heylo_var { $v:ident }) => `(term|$v)
-- heylo
| `(heylo { $n:num }) => `(($n : HeyLo _))
| `(heylo { ⊤ }) => `(⊤)
| `(heylo { true }) => `(HeyLo.Lit (.Bool true))
| `(heylo { false }) => `(HeyLo.Lit (.Bool false))
| `(heylo { nfloor $x }) => `(term|HeyLo.Call .nfloor heylo {$x} )
| `(heylo { nlog2 $x }) => `(term|HeyLo.Call .nlog2 heylo {$x} )
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
| `(heylo {⨅ $x, $y}) => `(HeyLo.Quant QuantOp.Inf heylo_var {$x} heylo {$y})
| `(heylo {⨆ $x, $y}) => `(HeyLo.Quant QuantOp.Sup heylo_var {$x} heylo {$y})
| `(heylo {∀ $x, $y}) => `(HeyLo.Quant QuantOp.Forall heylo_var {$x} heylo {$y})
| `(heylo {∃ $x, $y}) => `(HeyLo.Quant QuantOp.Exists heylo_var {$x} heylo {$y})
-- dists
| `(heylo_dist { flip($p) }) => `(HeyLo.Distribution.flip heylo {$p})
| `(heylo_dist { bin($l, $p, $r) }) => `(HeyLo.Distribution.bin heylo {$l} heylo {$p} heylo {$r})
-- spGCL
| `(spgcl { skip }) => `(spGCL.skip)
| `(spgcl { $v:cheylo_var := $e }) => `(spGCL.assign heylo_var {$v} heylo {$e})
| `(spgcl { $C₁ ; $C₂ }) => `(spGCL.seq spgcl {$C₁} spgcl {$C₂})
| `(spgcl { { $C₁:cspGCL } [ $p ] { $C₂ } }) => `(spGCL.prob spgcl {$C₁} heylo {$p} spgcl {$C₂})
| `(spgcl { { $C₁:cspGCL } [] { $C₂ } }) => `(spGCL.nonDet spgcl {$C₁} spgcl {$C₂})
| `(spgcl { while $b inv($i) { $C:cspGCL } }) => `(spGCL.loop heylo {$b} heylo {$i} spgcl {$C})
| `(spgcl { tick($r) }) => `(spGCL.tick heylo {$r})
| `(spgcl { observe($b) }) => `(spGCL.observe heylo {$b})
| `(spgcl { if $b then $C₁ else $C₂ end }) => `(spGCL.ite heylo {$b} spgcl {$C₁} spgcl {$C₂})
-- HeyVL
| `(heyvl { $x:cheylo_var :≈ $μ }) => `(HeyVL.Assign heylo_var {$x} heylo_dist {$μ})
| `(heyvl { reward($a) }) => `(HeyVL.Reward heylo {$a})
| `(heyvl { $S₁:cheyvl ; $S₂ }) => `(HeyVL.Seq heyvl {$S₁} heyvl {$S₂})
| `(heyvl { if (⊓) { $S₁:cheyvl } else { $S₂ } }) => `(HeyVL.IfInf heyvl {$S₁} heyvl {$S₂})
| `(heyvl { assert($φ) }) => `(HeyVL.Assert heylo {$φ})
| `(heyvl { assume($φ) }) => `(HeyVL.Assume heylo {$φ})
| `(heyvl { havoc($x:cheylo_var) }) => `(HeyVL.Havoc heylo_var {$x})
| `(heyvl { havocs($xs:cheylo_vars) }) => `(HeyVL.Havocs (heylo_vars {$xs}).sort)
| `(heyvl { validate }) => `(HeyVL.Validate)
| `(heyvl { if (⊔) { $S₁:cheyvl } else { $S₂ } }) => `(HeyVL.IfSup heyvl {$S₁} heyvl {$S₂})
| `(heyvl { coassert($φ) }) => `(HeyVL.Coassert heylo {$φ})
| `(heyvl { coassume($φ) }) => `(HeyVL.Coassume heylo {$φ})
| `(heyvl { cohavoc($x:cheylo_var) }) => `(HeyVL.Cohavoc heylo_var {$x})
| `(heyvl { cohavocs($xs:cheylo_vars) }) => `(HeyVL.Cohavocs (heylo_vars {$xs}).sort)
| `(heyvl { covalidate }) => `(HeyVL.Covalidate)
-- Sugar
| `(heyvl { skip }) => `(HeyVL.Skip)
| `(heyvl { if ($b:cheylo) {$S₁:cheyvl} else {$S₂}}) =>
    `(HeyVL.If heylo {$b} heyvl {$S₁} heyvl {$S₂})
| `(heyvl { if ($b:cheylo) {$S₁:cheyvl} }) => `(HeyVL.If heylo {$b} heyvl {$S₁} heyvl {skip})

abbrev x : Ident := ⟨"x", .ENNReal⟩
abbrev y : Ident := ⟨"y", .ENNReal⟩
abbrev b : Ident := ⟨"b", .Bool⟩
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
    | _ => `(cheylo|@ $c)
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
| c => `(cheylo|@ $c)

@[app_unexpander HeyLo.Binary]
def BinaryUnexpander : Unexpander
| `($_ $op $l $r) => do
  let op ←
    match op with
    | `($op:ident $_) => pure op
    | `($op:ident) => pure op
    | _ => throw ()
  let l ← unexpandAexp l; let r ← unexpandAexp r
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
  | _ => throw ()
| _ => throw ()

/-- info: heylo {true ∧ true} : 𝔼b -/
#guard_msgs in
#check (heylo { true ∧ true } : HeyLo .Bool)

/-- info: heylo {1 + 2 = 2 ∧ true} : 𝔼b -/
#guard_msgs in
#check (heylo { ((1 + 2) = 2) ∧ true } : HeyLo .Bool)

/-- info: Call Fun.nlog2 (Call Fun.nfloor (heylo {y})) : HeyLo Ty.Nat -/
#guard_msgs in
#check (heylo { nlog2 (nfloor y) } : HeyLo .Nat)
/-- info: heylo {y ≤ y} : 𝔼b -/
#guard_msgs in
#check (heylo { y ≤ y } : HeyLo .Bool)

syntax "⟦" cheylo "⟧'" : term

macro_rules
| `(⟦$t:cheylo⟧') => `(HeyLo.sem heylo {$t})

@[app_unexpander HeyLo.sem]
def semUnexpander : Unexpander
| `($_ $t) => do
  let t ← unexpandAexp t
  `(⟦$t⟧')
| _ => throw ()

/-- info: ⟦1 + [true ∧ false]⟧' : Ty.ENNReal.expr -/
#guard_msgs in #check (⟦1 + [true ∧ false]⟧')

@[app_unexpander spGCL.skip]
def skipUnexpander : Unexpander
| `($(_)) =>
  let name := mkIdent <| Name.mkSimple "skip"
  `(spgcl { $name:ident })

/-- info: spgcl {skip} : spGCL -/
#guard_msgs in
#check spgcl { skip }

@[app_unexpander spGCL.assign]
def assignUnexpander : Unexpander
| `($(_) $name:str $e) => do
  let name := mkIdent <| Name.mkSimple name.getString
  let e ← unexpandAexp e
  `(spgcl { $name:ident := $e })
| `($(_) $name $e) => do
  let name : TSyntax `cheylo_var ←
    match name with
    | `($x:ident) => `(cheylo_var|$x:ident)
    | `($n) => `(cheylo_var|@$n)
  let e ← match e with | `(heylo {$e}) => pure e | _ => `(cheylo|@ $e)
  `(spgcl { $name:cheylo_var := $e })
| _ => throw ()

/-- info: spgcl {x := x} : spGCL -/
#guard_msgs in
#check spgcl { x := x }

/-- info: spgcl {x := @(heylo {x} - 1)} : spGCL -/
#guard_msgs in
#check spgcl { @x := x - 1 }

/-- info: spgcl {x := @1} : spGCL -/
#guard_msgs in
#check spgcl { @x := 1 }

@[app_unexpander spGCL.seq]
def seqUnexpander : Unexpander
| `($(_) $l $r) => do
  let l ← match l with | `(spgcl {$l}) => pure l | _ => `(cspGCL|@$l)
  let r ← match r with | `(spgcl {$r}) => pure r | _ => `(cspGCL|@$r)
  `(spgcl { $l ; $r })
| _ => throw ()

/-- info: spgcl {x := @1 ; skip} : spGCL -/
#guard_msgs in
#check spgcl { @x := 1 ; skip }

@[app_unexpander spGCL.prob]
def probUnexpander : Unexpander
| `($(_) $l $p $r) => do
  let l ← match l with | `(spgcl {$l}) => pure l | _ => `(cspGCL|@$l)
  let p ← unexpandAexp p
  let r ← match r with | `(spgcl {$r}) => pure r | _ => `(cspGCL|@$r)
  `(spgcl { { $l } [$p] {$r} })
| _ => throw ()

/-- info: spgcl {{ x := @1 } [1] { skip }} : spGCL -/
#guard_msgs in
#check spgcl { { @x := 1 } [1] { skip } }

@[app_unexpander spGCL.nonDet]
def nonDetUnexpander : Unexpander
| `($(_) $l $r) => do
  let l ← match l with | `(spgcl {$l}) => pure l | _ => `(cspGCL|@$l)
  let r ← match r with | `(spgcl {$r}) => pure r | _ => `(cspGCL|@$r)
  `(spgcl { { $l } [] {$r} })
| _ => throw ()

/-- info: spgcl {{ x := @1 } [] { skip }} : spGCL -/
#guard_msgs in
#check spgcl { { @x := 1 } [] { skip } }

@[app_unexpander spGCL.loop]
def loopUnexpander : Unexpander
| `($(_) $b $i $C) => do
  let b ← unexpandAexp b
  let i ← unexpandAexp i
  let C ← match C with | `(spgcl {$C}) => pure C | _ => `(cspGCL|@$C)
  `(spgcl { while $b inv($i) {$C} })
| _ => throw ()

/-- info: spgcl {while x = 1 inv([true]) { skip }} : spGCL -/
#guard_msgs in
#check spgcl { while x = 1 inv([true]) { skip } }

@[app_unexpander spGCL.tick]
def tickUnexpander : Unexpander
| `($(_) $r) => do
  let r ← unexpandAexp r
  `(spgcl { tick($r) })
| _ => throw ()

/-- info: spgcl {tick(1)} : spGCL -/
#guard_msgs in
#check spgcl { tick(1) }

/-- info: fun r ↦ spgcl {tick(@r)} : 𝔼r → spGCL -/
#guard_msgs in
#check fun r ↦ spgcl { tick(@r) }

@[app_unexpander spGCL.observe]
def observeUnexpander : Unexpander
| `($(_) $r) => do
  let r ← unexpandAexp r
  `(spgcl { observe($r) })
| _ => throw ()

/-- info: spgcl {observe(false) ; observe(true)} : spGCL -/
#guard_msgs in
#check spgcl { observe(false) ; observe(true) }

@[app_unexpander spGCL.ite]
def iteUnexpander : Unexpander
| `($(_) $b $l $r) => do
  let b ← unexpandAexp b
  let l ← match l with | `(spgcl {$l}) => pure l | _ => `(cspGCL|@$l)
  let r ← match r with | `(spgcl {$r}) => pure r | _ => `(cspGCL|@$r)
  `(spgcl { if $b then $l else $r end })
| _ => throw ()

/-- info: spgcl {if false then skip else tick(1) end} : spGCL -/
#guard_msgs in
#check spgcl { if false then skip else tick(1) end }

/--
info: spgcl {z := @(Call Fun.nlog2 (Call Fun.nfloor (heylo {y})))}.pGCL : pGCL fun x ↦ x.type.lit
-/
#guard_msgs in
#check (spgcl { @z := nlog2 (nfloor y) } : spGCL).pGCL

/--
info: spgcl {while n < 10 inv([n ≤ 10]) { { n := @(heylo {n} + 2) } [1 / 2] { n := @(heylo {n} + 1) } }} : spGCL
-/
#guard_msgs in
#check spgcl { while n < 10 inv([n ≤ 10]) { {@n := n + 2} [1/2] {@n := n + 1} } }

@[app_unexpander HeyVL.Skip]
def HeyVL.skipUnexpander : Unexpander
| `($(_)) => do
  let name := mkIdent <| Name.mkSimple "skip"
  `(heyvl { $name:ident })

@[app_unexpander HeyVL.If]
def ifUnexpander : Unexpander
| `($(_) $b $S₁ $S₂) => do
  let b ← unexpandAexp b
  let S₁ ← match S₁ with | `(heyvl {$S₁}) => pure S₁ | _ => `(cheyvl|@$S₁)
  match S₂ with
  | `(heyvl {skip}) => `(heyvl { if ($b) { $S₁ } })
  | S₂ =>
    let S₂ ← match S₂ with | `(heyvl {$S₂}) => pure S₂ | _ => `(cheyvl|@$S₂)
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

@[app_unexpander HeyLo.Distribution.flip]
def Distribution.flipUnexpander : Unexpander
| `($(_) $p) => do
  let p ← unexpandAexp p
  `(heylo_dist {flip($p)})
| _ => throw ()
@[app_unexpander HeyLo.Distribution.bin]
def Distribution.binUnexpander : Unexpander
| `($(_) $l $p $r) => do
  let l ← unexpandAexp l
  let p ← unexpandAexp p
  let r ← unexpandAexp r
  `(heylo_dist {bin($l, $p, $r)})
| _ => throw ()

@[app_unexpander HeyVL.Assign]
def heyvlAssignUnexpander : Unexpander
| `($(_) $name $a) => do
  let name : TSyntax `cheylo_var ←
    match name with
    | `($x:ident) => `(cheylo_var|$x:ident)
    | `($n) => `(cheylo_var|@$n)
  let a ← match a with | `(heylo_dist {$a}) => pure a | _ => `(cheylo_dist|@$a)
  `(heyvl { $name:cheylo_var :≈ $a })
| _ => throw ()

@[app_unexpander HeyVL.Seq]
def heyvlSeqUnexpander : Unexpander
| `($(_) $S₁ $S₂) => do
  let S₁ ← match S₁ with | `(heyvl {$S₁}) => pure S₁ | _ => `(cheyvl|@$S₁)
  let S₂ ← match S₂ with | `(heyvl {$S₂}) => pure S₂ | _ => `(cheyvl|@$S₂)
  `(heyvl { $S₁ ; $S₂ })
| _ => throw ()

@[app_unexpander HeyVL.IfInf]
def ifInfUnexpander : Unexpander
| `($(_) $S₁ $S₂) => do
  let S₁ ← match S₁ with | `(heyvl {$S₁}) => pure S₁ | _ => `(cheyvl|@$S₁)
  let S₂ ← match S₂ with | `(heyvl {$S₂}) => pure S₂ | _ => `(cheyvl|@$S₂)
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
  let x ← match x with | `(heylo_var {$x}) => pure x | _ => `(cheylo_var|@$x)
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
  let S₁ ← match S₁ with | `(heyvl {$S₁}) => pure S₁ | _ => `(cheyvl|@$S₁)
  let S₂ ← match S₂ with | `(heyvl {$S₂}) => pure S₂ | _ => `(cheyvl|@$S₂)
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
  let x ← match x with | `(heylo_var {$x}) => pure x | _ => `(cheylo_var|@$x)
  `(heyvl { cohavoc($x) })
| _ => throw ()

@[app_unexpander HeyVL.Covalidate]
def covalidateUnexpander : Unexpander
| `($(_)) =>
  let name := mkIdent <| Name.mkSimple "covalidate"
  `(heyvl { $name:ident })

/-- info: heyvl {b :≈ flip(1 / 2)} : HeyVL -/
#guard_msgs in
#check heyvl { b :≈ flip(1/2) }
/-- info: heyvl {x :≈ bin(15, 1 / 3, 20)} : HeyVL -/
#guard_msgs in
#check heyvl { x :≈ bin(15, 1/3, 20) }

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
