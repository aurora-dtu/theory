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

noncomputable def 𝒜 : MDP State ℕ := ofRelation Step
  (by rintro s α p s' (_ | _) <;> simp_all)
  (by
    intro s α p₀ c₀ h
    cases h
    · rw [tsum_eq_single (.node α)] <;> simp_all [step_iff]
    · rw [tsum_eq_single .term] <;> simp_all
    · rw [tsum_eq_single .term] <;> simp_all
      )
  (by rintro (_ | i | _) <;> simp)

@[simp] noncomputable def 𝒜.cost : 𝒜.Costs
| .node i => 1 / (i : ENNReal)
| _ => 0

@[simp]
theorem 𝒜.act_eq : 𝒜.act = fun s ↦ if s = .init then Set.univ else {0} := by
  ext s α
  split_ifs
  · subst_eqs; simp [𝒜]
  · simp [𝒜]; cases s <;> simp_all

variable {𝒮 : 𝔖[𝒜]}

@[simp] theorem 𝒮_node : 𝒮 {.node i} = 0 := by have := 𝒮.mem_act {.node i}; simp_all
@[simp] theorem 𝒮_term : 𝒮 {.term} = 0 := by have := 𝒮.mem_act {.term}; simp_all
@[simp] theorem succs_univ_init : 𝒜.succs_univ .init = {.node α | α} := by simp [𝒜, eq_comm]
@[simp] theorem succs_univ_node : 𝒜.succs_univ (.node i) = {.term} := by simp [𝒜]
@[simp] theorem succs_univ_term : 𝒜.succs_univ .term = {.term} := by simp [𝒜]
@[simp] theorem P_init_node : 𝒜.P .init α (.node β) = if α = β then 1 else 0 := by
  simp_all [𝒜, ite_and, eq_comm]
@[simp] theorem P_node_term : 𝒜.P (.node i) 0 .term = 1 := by simp_all [𝒜]
@[simp] theorem P_term_term : 𝒜.P .term 0 .term = 1 := by simp_all [𝒜]

@[simp]
theorem EC_term_eq_0 : 𝒜.EC 𝒜.cost 𝒮 n .term = 0 := by
  rcases n with _ | n <;> simp_all [EC_succ]
  rintro _ ⟨_⟩
  induction n generalizing 𝒮 with
  | zero => simp
  | succ => simp_all [EC_succ]
@[simp] theorem EC_node_i_le_j_eq_top :
    𝒜.EC 𝒜.cost 𝒮 n (.node i) = if n = 0 then 0 else 1 / (i : ENNReal) := by
  cases n <;> simp [EC_succ]
  rw [tsum_eq_single ⟨.term, by simp⟩ (by simp_all)]
  simp_all
theorem EC_init :
    𝒜.EC 𝒜.cost 𝒮 n .init = if n < 2 then 0 else 1 / (𝒮 {.init} : ENNReal) := by
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
theorem all_𝒮_lt_iSup_iInf_EC (𝒮 : 𝔖[𝒜]) :
      ⨅ 𝒮, ⨆ n, 𝒜.EC 𝒜.cost 𝒮 n .init < ⨆ n, 𝒜.EC 𝒜.cost 𝒮 n .init := by
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

end MDP.Counterexample.D
