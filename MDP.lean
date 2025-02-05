import MDP.OptimalCost
import MDP.Counterexample

/-!
# Markov Decision Processes (MDP)

This module consernes itself with countably infinite branching MDPs.

## Main definitions

* `MDP`: Core definition of MDPs.
* `MDP.FiniteBranching`: A class of MDPs where enabled actions and successors of every state is
  finite.
* `MDP.Path`: Finite paths of MDPs.
* `MDP.Scheduler`: Schedulers of paths.
* `MDP.Φ`: The Bellman operator.
* `MDP.EC`: Expected cost.
* `MDP.Complete`: Relation of different formulizations of _optimal expected cost_ equivalent for
  finitely branching MDPs.
-/

namespace MDP

variable {State : Type*} {Act : Type*} {M : MDP State Act}
variable [DecidableEq State]

/-- For finitely branching `MDP`, the optimal expected cost is equivalent under all of the following
  definitions:

* `⨆ n, ⨅ 𝒮 : 𝔖[M], EC c 𝒮 s n`: Consider a potentially history dependent scheduler under bounded
  length, and then push the length to the limit.
* `⨆ n, ⨅ ℒ : 𝔏[M], EC c ℒ s n`: Like the previous but limit to history independent (`Markovian`)
  schedulers.
* `⨅ 𝒮 : 𝔖[M], ⨆ n, EC c 𝒮 s n`: Push the lengths of paths to the limit, and then consider a
  potentially history dependent scheduler.
* `⨅ ℒ : 𝔏[M], ⨆ n, EC c ℒ s n`: Like the previous but limit to history independent (`Markovian`)
  schedulers.
* `M.lfp_Φ c s`: The least fixed point of the Bellman operator `M.Φ`.
-/
theorem Complete [M.FiniteBranching] :
  let S: Set ENNReal := {
    ⨆ n, ⨅ 𝒮 : 𝔖[M], EC c 𝒮 s n,
    ⨆ n, ⨅ ℒ : 𝔏[M], EC c ℒ s n,
    ⨅ 𝒮 : 𝔖[M], ⨆ n, EC c 𝒮 s n,
    ⨅ ℒ : 𝔏[M], ⨆ n, EC c ℒ s n,
    M.lfp_Φ c s
  }
  ∀ v₁ v₂ : S, v₁ = v₂
:= by
  simp [iSup_iInf_EC_eq_iInf_iSup_EC, iInf_iSup_EC_eq_iInf_iSup_ECℒ, iSup_iInf_ECℒ_eq_iInf_iSup_ECℒ,
    ← iSup_iInf_EC_eq_lfp_Φ]

open Counterexample in
/-- There exists a (necessarily infinite branching) MDP such that the two notions of optimization
  order (`⨆⨅` vs. `⨅⨆`) is not equivalent. See `MDP.Counterexample.𝒜` for an instance of such and
  MDP. -/
theorem exists_iSup_iInf_EC_lt_iInf_iSup_EC :
    ∃ (State : Type) (Act : Type) (M : MDP State Act) (c : M.Costs) (s : State),
      ⨆ n, ⨅ 𝒮, M.EC c 𝒮 s n < ⨅ 𝒮, ⨆ n, M.EC c 𝒮 s n := by
  use State, ℕ, 𝒜, 𝒜.cost, State.init; simp

open Counterexample in
/-- There exists a (necessarily infinite branching) MDP such that the two notions of optimization
  order (`⨆⨅` vs. `⨅⨆`) is not equivalent. See `MDP.Counterexample.𝒜` for an instance of such and
  MDP. -/
theorem exists_iSup_iInf_EC_lt_lfp_Φ :
    ∃ (State : Type) (Act : Type) (M : MDP State Act) (c : M.Costs) (s : State),
      ⨆ n, ⨅ 𝒮, M.EC c 𝒮 s n < M.lfp_Φ c s := by
  use State, ℕ, 𝒜, 𝒜.cost, State.init; simp

end MDP
