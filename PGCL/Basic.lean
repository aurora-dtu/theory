import MDP.Cost
import PGCL.OMDP

theorem pGCL.iSup_iInf_EC_eq_wp [DecidableEq ϖ] :
  ⨅ 𝒮, ⨆ n, (OMDP (ϖ:=ϖ)).EC (OMDP.cost X) 𝒮 (·⟨C,σ⟩) n = C.wp X σ
:= by
  simp [← MDP.iSup_iInf_EC_eq_iInf_iSup_EC, MDP.iSup_iInf_EC_eq_lfp_Φ, ← dop_eq_wp, dop]
