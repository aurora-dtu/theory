import HeyLo.Expr
import PGCL.pGCL

open HeyLo

inductive pGCLr where
  | skip : pGCLr
  | assign : (v : Ident) → HeyLo v.type → pGCLr
  | seq : pGCLr → pGCLr → pGCLr
  | prob : pGCLr → 𝔼r → pGCLr → pGCLr
  | nonDet : pGCLr → pGCLr → pGCLr
  | ite : 𝔼b → pGCLr → pGCLr → pGCLr
  | loop : 𝔼b → 𝔼r → pGCLr → pGCLr
  | tick : 𝔼r → pGCLr
  | observe : 𝔼b → pGCLr
deriving Inhabited

noncomputable def pGCLr.pGCL : pGCLr → pGCL fun (x : Ident) ↦ x.type.lit
  | skip => .skip
  | assign x e => .assign x e.sem
  | seq C₁ C₂ => .seq C₁.pGCL C₂.pGCL
  | prob C₁ p C₂ => .prob C₁.pGCL (pGCL.ProbExp.ofExp p.sem) C₂.pGCL
  | nonDet C₁ C₂ => .nonDet C₁.pGCL C₂.pGCL
  | ite b C₁ C₂ => .ite (fun σ ↦ b.sem σ) C₁.pGCL C₂.pGCL
  | loop b _ C => .loop (fun σ ↦ b.sem σ) C.pGCL
  | tick r => .tick r.sem
  | observe b => .observe (fun σ ↦ b.sem σ)
