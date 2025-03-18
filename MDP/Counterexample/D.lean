import MDP.OptimalCost
import MDP.Relational

namespace MDP.Counterexample.D

inductive State where
  | init
  | node (i : ℕ)
  | term
deriving DecidableEq

@[aesop safe [constructors, cases], mk_iff]
inductive Step : State → ℕ → ENNReal → State → Prop where
| choice : Step .init α 1 (.node α)
| step : Step (.node i) 0 1 .term
| loop : Step .term 0 1 .term

local notation c " ⤳[" α "," p "] " c' => Step c α p c'

noncomputable instance : Decidable (c ⤳[α,p] c') := Classical.propDecidable _

@[simp] theorem init_iff : (.init ⤳[α,p] s') ↔ p = 1 ∧ s' = .node α := by aesop
@[simp] theorem node_iff : (.node i ⤳[α,p] s') ↔ p = 1 ∧ α = 0 ∧ s' = .term := by aesop
@[simp] theorem term_iff : (.term ⤳[α,p] s') ↔ p = 1 ∧ α = 0 ∧ s' = .term := by aesop
@[simp] theorem not_to_init : ¬s ⤳[α,p] .init := by aesop

@[simp]
theorem tsum_p :
    (∑' (p : { p // c ⤳[α,p] c' }), ↑p) = (∑' p, if c ⤳[α,p] c' then p else 0) := by
  apply tsum_eq_tsum_of_ne_zero_bij (fun ⟨x, _⟩ ↦ ⟨x, by simp_all⟩) <;> simp_all
  exact StrictMono.injective fun _ _ a ↦ a

noncomputable def M : MDP State ℕ := ofRelation Step
  (by rintro s α p s' (_ | _) <;> simp_all)
  (by
    intro s α p₀ c₀ h
    cases h
    · rw [tsum_eq_single (.node α)] <;> simp_all [step_iff]
    · rw [tsum_eq_single .term] <;> simp_all
    · rw [tsum_eq_single .term] <;> simp_all
      )
  (by rintro (_ | i | _) <;> simp)

@[simp] noncomputable def M.cost : M.Costs
| .node i => 1 / (i : ENNReal)
| _ => 0
@[simp] noncomputable def M.rew : M.Costs
| .node i => i
| _ => 0

@[simp]
theorem M.act_eq : M.act = fun s ↦ if s = .init then Set.univ else {0} := by
  ext s α
  split_ifs
  · subst_eqs; simp [M]
  · simp [M]; cases s <;> simp_all

variable {𝒮 : 𝔖[M]}

@[simp] theorem 𝒮_node : 𝒮 {.node i} = 0 := by have := 𝒮.mem_act {.node i}; simp_all
@[simp] theorem 𝒮_term : 𝒮 {.term} = 0 := by have := 𝒮.mem_act {.term}; simp_all
@[simp] theorem succs_univ_init : M.succs_univ .init = {.node α | α} := by simp [M, eq_comm]
@[simp] theorem succs_univ_node : M.succs_univ (.node i) = {.term} := by simp [M]
@[simp] theorem succs_univ_term : M.succs_univ .term = {.term} := by simp [M]
@[simp] theorem P_init_node : M.P .init α (.node β) = if α = β then 1 else 0 := by
  simp_all [M, ite_and, eq_comm]
@[simp] theorem P_node_term : M.P (.node i) 0 .term = 1 := by simp_all [M]
@[simp] theorem P_term_term : M.P .term 0 .term = 1 := by simp_all [M]

section EC

@[simp]
theorem EC_term_eq_0 : M.EC M.cost 𝒮 n .term = 0 := by
  rcases n with _ | n <;> simp_all [EC_succ]
  rintro _ ⟨_⟩
  induction n generalizing 𝒮 with
  | zero => simp
  | succ => simp_all [EC_succ]
@[simp] theorem EC_node_i_le_j_eq_top :
    M.EC M.cost 𝒮 n (.node i) = if n = 0 then 0 else 1 / (i : ENNReal) := by
  cases n <;> simp [EC_succ]
  rw [tsum_eq_single ⟨.term, by simp⟩ (by simp_all)]
  simp_all
theorem EC_init :
    M.EC M.cost 𝒮 n .init = if n < 2 then 0 else 1 / (𝒮 {.init} : ENNReal) := by
  rcases n with _ | n <;> simp_all
  rcases n with _ | n
  · simp
  · rw [EC_succ]
    simp
    rw [tsum_eq_single ⟨.node (𝒮 {.init}), by simp⟩]
    · simp_all; split_ifs <;> simp_all; omega
    · simp_all
      rintro _ α ⟨_⟩
      simp_all [eq_comm]

@[simp]
theorem all_𝒮_lt_iSup_iInf_EC (𝒮 : 𝔖[M]) :
      ⨅ 𝒮, ⨆ n, M.EC M.cost 𝒮 n .init < ⨆ n, M.EC M.cost 𝒮 n .init := by
  simp_all [EC_init]
  apply iInf_lt_iff.mpr
  exists ⟨fun π ↦ if π.last = .init then 𝒮 π + 1 else 0, by simp_all⟩
  simp_all
  refine lt_iSup_iff.mpr ?_
  exists 2
  simp_all
  apply iSup_lt_iff.mpr
  exists 1 / ((𝒮 {.init} + 1) : ENNReal)
  simp_all
  constructor
  · apply ENNReal.lt_add_right <;> simp
  · intro n; split_ifs <;> simp

end EC

section ER

@[simp]
theorem ER_term_eq_0 : M.EC M.rew 𝒮 n .term = 0 := by
  rcases n with _ | n <;> simp_all [EC_succ]
  rintro _ ⟨_⟩
  induction n generalizing 𝒮 with
  | zero => simp
  | succ => simp_all [EC_succ]
@[simp] theorem ER_node_i_le_j_eq_top :
    M.EC M.rew 𝒮 n (.node i) = if n = 0 then 0 else i := by
  cases n <;> simp [EC_succ]
  rw [tsum_eq_single ⟨.term, by simp⟩ (by simp_all)]
  simp_all
theorem ER_init :
    M.EC M.rew 𝒮 n .init = if n < 2 then 0 else 𝒮 {.init} := by
  rcases n with _ | n <;> simp_all
  rcases n with _ | n
  · simp
  · rw [EC_succ]
    simp
    rw [tsum_eq_single ⟨.node (𝒮 {.init}), by simp⟩]
    · simp_all; split_ifs <;> simp_all; omega
    · simp_all
      rintro _ α ⟨_⟩
      simp_all [eq_comm]

@[simp]
theorem all_𝒮_iSup_iSup_ER_lt (𝒮 : 𝔖[M]) :
      ⨆ n, M.EC M.rew 𝒮 n .init < ⨆ 𝒮, ⨆ n, M.EC M.rew 𝒮 n .init := by
  simp_all [ER_init]
  apply lt_iSup_iff.mpr
  exists ⟨fun π ↦ if π.last = .init then 𝒮 π + 1 else 0, by simp_all⟩
  simp_all
  refine lt_iSup_iff.mpr ?_
  exists 2
  simp_all
  apply iSup_lt_iff.mpr
  exists ((𝒮 {.init}) : ENNReal)
  constructor
  · apply ENNReal.lt_add_right <;> simp
  · intro n; split_ifs <;> simp

end ER

end MDP.Counterexample.D
