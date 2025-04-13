import WGCL.wGCL

namespace WGCL

open Lean PrettyPrinter Delaborator SubExpr

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
syntax "if " "(" cwgcl_bexpr ")" ppHardSpace "{" ppLine cwgcl_progr ppDedent(ppLine "}")
  : cwgcl_progr
syntax "while " "(" cwgcl_bexpr ")" ppHardSpace "{" ppLine cwgcl_progr ppDedent(ppLine "}")
  : cwgcl_progr
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

@[app_unexpander BExpr.Const]
def BExpr.unexpandConst : Unexpander
| `($(_) true) => let t := mkIdent <| Name.mkSimple "true"; `(wgcl_bexpr { $t:ident })
| `($(_) false) => let t := mkIdent <| Name.mkSimple "false"; `(wgcl_bexpr { $t:ident })
| _ => throw ()

@[app_unexpander AExpr.Const]
def AExpr.unexpandConst : Unexpander
| `($(_) $n:num) => `(wgcl_aexpr { $n:num })
| _ => throw ()
@[app_unexpander AExpr.Var]
def AExpr.unexpandVar : Unexpander
| `($(_) $x:str) =>
  let name := mkIdent <| Name.mkSimple x.getString
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
  let name := mkIdent <| Name.mkSimple x.getString
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

end WGCL
