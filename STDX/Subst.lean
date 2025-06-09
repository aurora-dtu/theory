import Mathlib.Data.Finset.Insert
import Lean.PrettyPrinter.Delaborator.Basic

class Subst (W Var E : Type) where
  /-- Written using `a[x ↦ e]`. Substitutes all `x` in `a` with `e`. -/
  subst : W → Var → E → W

@[inherit_doc Subst.subst]
syntax:max term noWs "[" withoutPosition(term) ppHardSpace "↦" ppHardSpace withoutPosition(term) "]"
  : term
macro_rules | `($x[$i ↦ $j]) => `(Subst.subst $x $i $j)

open Lean PrettyPrinter Delaborator SubExpr in
@[app_unexpander Subst.subst]
def Subst.substUnexpander : Unexpander
| `($(_) $m $x $v) => `($m[$x ↦ $v])
| _ => throw ()

instance [BEq α] [Hashable α] : Subst (Std.HashMap α β) α β where
  subst m x v := m.insert x v
