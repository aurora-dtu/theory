import WGCL.OperationalSemantics

namespace WGCL

variable {D : Type} {M : Type} {W : Type} {Var : Type}

variable [DecidableEq Var]
variable [DecidableEq (wGCL D W Var)]

variable [TopologicalSpace M]
variable [Monoid W] [AddCommMonoid M]

variable [DistribMulAction W M]

variable [Zero W]

variable [∀ (B : BExpr D Var) σ, Decidable (B σ)]

variable [OmegaCompletePartialOrder M] [OrderBot M]

variable [AddLeftMono M]
variable [CovariantClass W M HSMul.hSMul LE.le]

theorem wGCL.op_eq_wp {C : wGCL D W Var} : op (D:=D) (M:=M) (W:=W) (Var:=Var) C = C.wp := by
  sorry

end WGCL
