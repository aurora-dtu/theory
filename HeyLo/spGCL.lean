import HeyLo.Expr
import PGCL.pGCL

open HeyLo

inductive spGCL where
  | skip : spGCL
  | assign : (v : Ident) → HeyLo v.type → spGCL
  | seq : spGCL → spGCL → spGCL
  | prob : spGCL → 𝔼r → spGCL → spGCL
  | nonDet : spGCL → spGCL → spGCL
  | ite : 𝔼b → spGCL → spGCL → spGCL
  | loop : 𝔼b → 𝔼r → spGCL → spGCL
  | tick : 𝔼r → spGCL
  | observe : 𝔼b → spGCL
deriving Inhabited

noncomputable def spGCL.pGCL : spGCL → pGCL fun (x : Ident) ↦ x.type.lit
  | skip => .skip
  | assign x e => .assign x e.sem
  | seq C₁ C₂ => .seq C₁.pGCL C₂.pGCL
  | prob C₁ p C₂ => .prob C₁.pGCL (pGCL.ProbExp.ofExp p.sem) C₂.pGCL
  | nonDet C₁ C₂ => .nonDet C₁.pGCL C₂.pGCL
  | ite b C₁ C₂ => .ite (fun σ ↦ b.sem σ) C₁.pGCL C₂.pGCL
  | loop b _ C => .loop (fun σ ↦ b.sem σ) C.pGCL
  | tick r => .tick r.sem
  | observe b => .observe (fun σ ↦ b.sem σ)
