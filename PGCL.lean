import MDP.OptimalCost
import PGCL.OMDP

/-!
# _probabilistic Guarded Command Language_ (pGCL)

## Main definitions

* `pGCL`: The definition of a variant of the _pGCL language_.
* `pGCL.SmallStep`: The _small step operations semantics_ of pGCL.
* `pGCL.𝒬`: The _induced operational Markov Decision Process_ (`MDP`) by the small step operational
  semantics.
* `pGCL.wp`: The _weakest preexpectation transformer_ of a pGCL program.
* `pGCL.op`: The _operational optimal expected cost transformer_ expressed as the optimal expected
  cost of `pGCL.𝒬`.
* `pGCL.op_eq_wp`: Theorem stating that the optimal expected cost is equal the weakest
  preexpectation.
* `pGCL.iSup_iInf_EC_eq_wp`: Theorem stating that the `⨅⨆` formulation of the optimal expected cost
  is equal to the weakest preexpectation.
-/

theorem pGCL.iSup_iInf_EC_eq_wp [DecidableEq ϖ] :
  ⨅ 𝒮, ⨆ n, (𝒬 (ϖ:=ϖ)).EC (𝒬.cost X) 𝒮 n (·⟨C,σ⟩) = C.wp X σ
:= by
  simp [← MDP.iSup_iInf_EC_eq_lfp_Φ, ← op_eq_wp, op]
  have := congrFun ((𝒬 (ϖ:=ϖ)).iSup_iInf_EC_eq_iInf_iSup_EC (c:=(𝒬.cost X))) (·⟨C,σ⟩) |>.symm
  simp_all
