import Lean.PrettyPrinter.Delaborator
import PGCL.Exp

open pGCL

variable {ϖ : Type*}

inductive pGCL (ϖ : Type*) where
  | skip : pGCL ϖ
  | assign : ϖ → Exp ϖ → pGCL ϖ
  | seq : pGCL ϖ → pGCL ϖ → pGCL ϖ
  | prob : pGCL ϖ → ProbExp ϖ → pGCL ϖ → pGCL ϖ
  | nonDet : pGCL ϖ → pGCL ϖ → pGCL ϖ
  | loop : BExpr ϖ → pGCL ϖ → pGCL ϖ
  | tick : Exp ϖ → pGCL ϖ
deriving Inhabited

noncomputable instance pGCL.decidableEq [DecidableEq ϖ] : DecidableEq (pGCL ϖ)
  | a, b => by exact Classical.propDecidable (a = b)

infixr:90 " ;; " => pGCL.seq
infixr:90 " ·[] " => pGCL.nonDet
infixr:91 " ::= " => pGCL.assign
notation:89 cmd₁ " ·[" prob "] " cmd₂ => pGCL.prob cmd₁ prob cmd₂
