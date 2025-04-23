import WGCL.WeakestPre

namespace WGCL

variable {D : Type} {M : Type} {W : Type} {Var : Type}

variable [DecidableEq Var]

variable [Monoid W] [AddCommMonoid M]

variable [DistribMulAction W M]

variable [∀ (B : BExpr D Var) σ, Decidable (B σ)]

variable [OmegaCompletePartialOrder M] [OrderBot M]

variable [AddLeftMono M]
variable [CovariantClass W M HSMul.hSMul LE.le]

open OmegaCompletePartialOrder

/-- Park induction -/
theorem wGCL.wp_le_of_le {C : wGCL D W Var} (I : Weighting D M Var) (h : Φ φ C f I ≤ I) :
    wp⟦while (~φ) {~C}⟧(~f) ≤ I := by
  rw [wp_loop]; exact lfp_le _ h

end WGCL
