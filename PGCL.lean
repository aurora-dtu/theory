import MDP.OptimalCost
import MDP.SupSup
import PGCL.OperationalSemantics
import PGCL.ProofRules
import PGCL.IdleInduction

/-!
# _probabilistic Guarded Command Language_ (pGCL)

## Main definitions

* `pGCL`: The definition of a variant of the _pGCL language_.
* `pGCL.SmallStep`: The _small step operations semantics_ of pGCL. semantics.
* `pGCL.wp`: The _weakest preexpectation transformer_ of a pGCL program.
* `pGCL.wp_eq_op`: Theorem stating that the optimal expected cost is equal the weakest
preexpectation.
* `pGCL.iInf_iSup_EC_eq_wp`: Theorem stating that the `⨆⨅` formulation of the optimal expected cost
is equal to the weakest preexpectation.
-/

open scoped Optimization.Notation

theorem pGCL.iSup_iSup_EC_eq_wp [DecidableEq 𝒱] :
      ⨆ 𝒮, ⨆ n, (𝕊 (𝒱:=𝒱) cost_t cost_p).mdp.EC ((𝕊 cost_t cost_p).cost X) 𝒮 n conf[@C,σ]
    = wp[𝒜]⟦@C⟧ X σ := by
  rw [wp_eq_op]
  classical
  have := congrFun ((𝕊 cost_t cost_p).mdp.iSup_iSup_EC_eq_lfp_Φ𝒜 (c:=(𝕊 _ _).cost X)) (.prog C σ)
  simp at this
  simp [this, iSup_comm]
  rfl

theorem pGCL.iInf_iSup_EC_eq_wp [DecidableEq 𝒱] :
      ⨅ 𝒮, ⨆ n, (𝕊 (𝒱:=𝒱) cost_t cost_p).mdp.EC ((𝕊 cost_t cost_p).cost X) 𝒮 n conf[@C,σ]
    = wp[𝒟]⟦@C⟧ X σ := by
  rw [wp_eq_op]
  classical
  have := congrFun ((𝕊 cost_t cost_p).mdp.iInf_iSup_EC_eq_lfp_Φ𝒟 (c:=(𝕊 _ _).cost X)) (.prog C σ)
  simp at this
  simp [this]
  rfl

theorem pGCL.iSup_iSup_EC_eq_wfp [DecidableEq 𝒱] :
      ⨆ 𝒮, ⨆ n, (𝕊 (𝒱:=𝒱) cost_t' cost_p').mdp.EC ((𝕊 cost_t' cost_p').cost X) 𝒮 n conf[@C,σ]
    = wfp[𝒜]⟦@C⟧ X σ := by
  rw [instET'.et_eq_op]
  rw [SmallStepSemantics.op]
  simp only [OrderHom.coe_mk]
  classical
  rw [← MDP.iSup_iSup_EC_eq_lfp_Φ𝒜, iSup_comm]
  simp only [iSup_apply]

theorem pGCL.iInf_iSup_EC_eq_wfp [DecidableEq 𝒱] :
      ⨅ 𝒮, ⨆ n, (𝕊 (𝒱:=𝒱) cost_t' cost_p').mdp.EC ((𝕊 cost_t' cost_p').cost X) 𝒮 n conf[@C,σ]
    = wfp[𝒟]⟦@C⟧ X σ := by
  rw [instET'.et_eq_op]
  rw [SmallStepSemantics.op]
  simp only [OrderHom.coe_mk]
  classical
  rw [← MDP.iSup_iInf_EC_eq_lfp_Φ𝒟, MDP.iSup_iInf_EC_eq_iInf_iSup_EC]
  simp only [iInf_apply, iSup_apply]

/-- info: 'pGCL.iSup_iSup_EC_eq_wp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pGCL.iSup_iSup_EC_eq_wp
/-- info: 'pGCL.iInf_iSup_EC_eq_wp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pGCL.iInf_iSup_EC_eq_wp
/-- info: 'pGCL.iSup_iSup_EC_eq_wfp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pGCL.iSup_iSup_EC_eq_wfp
/-- info: 'pGCL.iInf_iSup_EC_eq_wfp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pGCL.iInf_iSup_EC_eq_wfp
