import WGCL.wGCL

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

namespace WGCL

variable {D : Type} {M : Type} {W : Type} {Var : Type}

variable [DecidableEq Var]

instance : Subst (Mem D Var) Var D where
  subst σ x v := fun y ↦ if x = y then v else σ y

instance : Subst (Weighting D M Var) Var (AExpr D Var) where
  subst f x E := fun σ ↦ f σ[x ↦ E σ]

@[simp]
theorem Weighting.subst_mono [Preorder M] {f₁ f₂ : Weighting D M Var} (h : f₁ ≤ f₂) (x : Var)
    (y : AExpr D Var) : f₁[x ↦ y] ≤ f₂[x ↦ y] := by
  intro σ
  exact h fun y_1 => if x = y_1 then y σ else σ y_1

end WGCL
