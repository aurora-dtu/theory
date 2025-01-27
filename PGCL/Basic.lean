import PGCL.SmallStep

theorem pGCL.iSup_iInf_EC_eq_dwp {ϖ : Type*} [DecidableEq ϖ] (X : Exp ϖ) (C : pGCL ϖ) (σ : States ϖ) :
  ⨅ 𝒮, ⨆ n, OMDP.EC (OMDP.cost X) 𝒮 (·⟨C,σ⟩) n = C.dwp X σ
:= by
  simp [← MDP.iSup_iInf_EC_eq_iInf_iSup_EC, MDP.iSup_iInf_EC_eq_lfp_Φ, ← dop_eq_dwp, dop]
