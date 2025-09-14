import MDP.OptimalCost
import PGCL.OperationalSemantics
import PGCL.ProofRules

/-!
# _probabilistic Guarded Command Language_ (pGCL)

## Main definitions

* `pGCL`: The definition of a variant of the _pGCL language_.
* `pGCL.SmallStep`: The _small step operations semantics_ of pGCL.
* `pGCL.𝒬`: The _induced operational Markov Decision Process_ (`MDP`) by the small step operational
  semantics.
* `pGCL.dwp`: The _weakest preexpectation transformer_ of a pGCL program.
* `pGCL.op`: The _operational optimal expected cost transformer_ expressed as the optimal expected
  cost of `pGCL.𝒬`.
* `pGCL.dop_eq_dwp`: Theorem stating that the optimal expected cost is equal the weakest
  preexpectation.
* `pGCL.iSup_iInf_EC_eq_wp`: Theorem stating that the `⨅⨆` formulation of the optimal expected cost
  is equal to the weakest preexpectation.
-/

theorem pGCL.iSup_iInf_EC_eq_dwp [DecidableEq ϖ] :
  ⨅ 𝒮, ⨆ n, (𝒪 (ϖ:=ϖ)).EC (instSSS.cost X) 𝒮 n conf[~C,σ] = dwp⟦~C⟧ X σ
:= by
  suffices (⨅ 𝒮, ⨆ n, MDP.EC _ _ _) conf[~C,σ] = _ by
    simpa only [iInf_apply, iSup_apply]
  rw [instDemonicET.det_eq_dop, SmallStepSemantics.dop]
  simp only [OrderHom.coe_mk]
  classical
  rw [← MDP.iSup_iInf_EC_eq_lfp_dΦ, MDP.iSup_iInf_EC_eq_iInf_iSup_EC]
