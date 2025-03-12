import MDP.Counterexample.A
import MDP.Counterexample.B
import MDP.Counterexample.C
import MDP.Counterexample.D

namespace MDP

variable {State : Type*} {Act : Type*} {M : MDP State Act}
variable [DecidableEq State]

open Counterexample.A in
/-- There exists a (necessarily infinite branching) MDP such that the two notions of optimization
  order (`⨆⨅` vs. `⨅⨆`) is not equivalent. See `MDP.Counterexample.A.𝒜` for an instance of such and
  MDP. -/
theorem exists_iSup_iInf_EC_lt_iInf_iSup_EC :
    ∃ (State : Type) (Act : Type) (M : MDP State Act) (c : M.Costs) (s : State),
      ⨆ n, ⨅ 𝒮, M.EC c 𝒮 n s < ⨅ 𝒮, ⨆ n, M.EC c 𝒮 n s :=
  ⟨_, _, _, 𝒜.cost, State.init, by simp⟩

open Counterexample.A in
/-- There exists a (necessarily infinite branching) MDP such that the `⨅⨆` notions of optimization
  order is not equivalent to the lfp formulation. See `MDP.Counterexample.A.𝒜` for an instance of
  such and MDP. -/
theorem exists_iSup_iInf_EC_lt_lfp_Φ :
    ∃ (State : Type) (Act : Type) (M : MDP State Act) (c : M.Costs) (s : State),
      ⨆ n, ⨅ 𝒮, M.EC c 𝒮 n s < M.lfp_Φ c s :=
  ⟨_, _, _, 𝒜.cost, State.init, by simp⟩

open Counterexample.C in
/-- There exists a (necessarily infinite branching) MDP such that the optimal cost given by `⨅⨆`
  with history is strictly less than that of the memoryless. See `MDP.Counterexample.C.𝒜` for an
  instance of such and MDP. -/
theorem exists_iInf_iSup_EC_lt_iInf_iSup_ECℒ :
    ∃ (State : Type) (Act : Type) (M : MDP State Act) (c : M.Costs) (s : State),
      ⨅ 𝒮, ⨆ n, M.EC c 𝒮 n s < ⨅ ℒ : 𝔏[M], ⨆ n, M.EC c ℒ n s :=
  ⟨_, _, 𝒜 p, 𝒜.cost, .s₁, iInf_iSup_EC_lt_iInf_iSup_ECℒ⟩

open Counterexample.D in
/-- There exists a (necessarily infinite branching) MDP such that there does not exist an optimal
  scheduler for the `⨅⨆` notion of optimization. See `MDP.Counterexample.D.𝒜` for an instance of
  such and MDP.-/
theorem not_exists_optimal_𝒮_for_iSup_iInf_EC :
    ∃ (State : Type) (Act : Type) (M : MDP State Act) (c : M.Costs) (s : State),
      ¬∃ 𝒮, ⨆ n, M.EC c 𝒮 n s = ⨅ 𝒮, ⨆ n, M.EC c 𝒮 n s :=
  ⟨_, _, _, 𝒜.cost, State.init, by simp [ne_of_gt]⟩

open Counterexample.D in
/-- There exists a (necessarily infinite branching) MDP such that there does not exist an optimal
  scheduler for the `⨆⨆` notion of optimization. See `MDP.Counterexample.D.𝒜` for an instance of
  such and MDP.-/
theorem not_exists_optimal_𝒮_for_iSup_iSup_EC :
    ∃ (State : Type) (Act : Type) (M : MDP State Act) (c : M.Costs) (s : State),
      ¬∃ 𝒮, ⨆ n, M.EC c 𝒮 n s = ⨆ 𝒮, ⨆ n, M.EC c 𝒮 n s :=
  ⟨_, _, _, 𝒜.rew, State.init, by simp [ne_of_lt]⟩

end MDP
