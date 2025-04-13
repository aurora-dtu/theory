import Mathlib.Data.ENNReal.Operations
import Lean.ToExpr

namespace WGCL

/- Boolean arithmetic operators -/
inductive BAOp where
  | Lt | Le
  | Gt | Ge
  | Eq | Ne
deriving Lean.ToExpr

/- Boolean operators -/
inductive BOp where
  | And | Or
  | Imp | BImp
deriving Lean.ToExpr

/- Arithmetic operators -/
inductive AOp where
  | Add | Sub
  | Mul | Div
deriving Lean.ToExpr

inductive BUOp where
  | Not
deriving Lean.ToExpr

inductive AUOp where
  | Neg
deriving Lean.ToExpr

inductive AExpr (Var : Type) where
  | Const : Nat → AExpr Var
  | Var : Var → AExpr Var
  | Bin : AOp → AExpr Var → AExpr Var → AExpr Var
  | Uni : AUOp → AExpr Var → AExpr Var
deriving Lean.ToExpr

inductive BExpr (Var : Type) where
  | Const : Bool → BExpr Var
  | ABin : BAOp → AExpr Var → AExpr Var → BExpr Var
  | BBin : BOp → BExpr Var → BExpr Var → BExpr Var
  | Uni : BUOp → BExpr Var → BExpr Var
deriving Lean.ToExpr

inductive wGCL (W : Type) (Var : Type) where
  | Branch : wGCL W Var → wGCL W Var → wGCL W Var
  | Weighting : W → wGCL W Var
  | Assign : Var → AExpr Var → wGCL W Var
  | Ite : BExpr Var → wGCL W Var → wGCL W Var → wGCL W Var
  | Seq : wGCL W Var → wGCL W Var → wGCL W Var
  | While : BExpr Var → wGCL W Var → wGCL W Var
deriving Lean.ToExpr

def Mem (W : Type) (Var : Type) := Var → W

end WGCL
