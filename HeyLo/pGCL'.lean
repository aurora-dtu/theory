import HeyLo.Expr
import PGCL.pGCL

open HeyLo

inductive pGCL' where
  | skip : pGCL'
  | assign : (v : Ident) → HeyLo v.type → pGCL'
  | seq : pGCL' → pGCL' → pGCL'
  | prob : pGCL' → 𝔼r → pGCL' → pGCL'
  | nonDet : pGCL' → pGCL' → pGCL'
  | ite : 𝔼b → pGCL' → pGCL' → pGCL'
  | loop : 𝔼b → 𝔼r → pGCL' → pGCL'
  | tick : 𝔼r → pGCL'
  | observe : 𝔼b → pGCL'
deriving Inhabited

noncomputable def pGCL'.pGCL : pGCL' → pGCL fun (x : Ident) ↦ x.type.lit
  | skip => .skip
  | assign x e => .assign x e.sem
  | seq C₁ C₂ => .seq C₁.pGCL C₂.pGCL
  | prob C₁ p C₂ => .prob C₁.pGCL (pGCL.ProbExp.ofExp p.sem) C₂.pGCL
  | nonDet C₁ C₂ => .nonDet C₁.pGCL C₂.pGCL
  | ite b C₁ C₂ => .ite (fun σ ↦ b.sem σ) C₁.pGCL C₂.pGCL
  | loop b _ C => .loop (fun σ ↦ b.sem σ) C.pGCL
  | tick r => .tick r.sem
  | observe b => .observe (fun σ ↦ b.sem σ)
