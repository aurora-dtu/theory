import STDX.Subst
import WGCL.wGCL

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
