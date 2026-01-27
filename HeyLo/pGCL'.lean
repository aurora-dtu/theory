import HeyLo.Expr
import PGCL.pGCL

open HeyLo

inductive pGCL' (ϖ : Type) where
  | skip : pGCL' ϖ
  | assign : ϖ → 𝔼r[ϖ] → pGCL' ϖ
  | seq : pGCL' ϖ → pGCL' ϖ → pGCL' ϖ
  | prob : pGCL' ϖ → 𝔼r[ϖ] → pGCL' ϖ → pGCL' ϖ
  | nonDet : pGCL' ϖ → pGCL' ϖ → pGCL' ϖ
  | ite : 𝔼b[ϖ] → pGCL' ϖ → pGCL' ϖ → pGCL' ϖ
  | loop : 𝔼b[ϖ] → 𝔼r[ϖ] → pGCL' ϖ → pGCL' ϖ
  | tick : 𝔼r[ϖ] → pGCL' ϖ
  | observe : 𝔼b[ϖ] → pGCL' ϖ
deriving Inhabited

noncomputable def pGCL'.pGCL [DecidableEq ϖ] (C : pGCL' ϖ) : pGCL ϖ :=
  match C with
  | skip => .skip
  | assign x e => .assign x e.sem
  | seq C₁ C₂ => .seq C₁.pGCL C₂.pGCL
  | prob C₁ p C₂ => .prob C₁.pGCL (pGCL.ProbExp.ofExp p.sem) C₂.pGCL
  | nonDet C₁ C₂ => .nonDet C₁.pGCL C₂.pGCL
  | ite b C₁ C₂ => .ite b.sem C₁.pGCL C₂.pGCL
  | loop b _ C => .loop b.sem C.pGCL
  | tick r => .tick r.sem
  | observe r => .observe r.sem
