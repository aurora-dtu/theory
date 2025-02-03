import MDP.OptimalCost
import MDP.Counterexample

namespace MDP

variable {State : Type*} {Act : Type*} {M : MDP State Act}
variable [DecidableEq State]

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
theorem exists_iSup_iInf_EC_lt_iInf_iSup_EC :
    ∃ (State : Type) (Act : Type) (M : MDP State Act) (c : M.Costs) (s : State),
      ⨆ n, ⨅ 𝒮, M.EC c 𝒮 s n < ⨅ 𝒮, ⨆ n, M.EC c 𝒮 s n := by
  use State, ℕ, 𝒜, 𝒜.cost, State.init; simp

end MDP
