import MDP.OptimalCost
import MDP.Relational

namespace MDP.Counterexample.A

inductive State where
  | init
  | node (i : ℕ) (j : ℕ)
deriving DecidableEq

@[aesop safe [constructors, cases], mk_iff]
inductive Step : State → ℕ → ENNReal → State → Prop where
| choice : Step .init α 1 (.node α 0)
| step : Step (.node i j) 0 1 (.node i (j + 1))

local notation c " ⤳[" α "," p "] " c' => Step c α p c'

noncomputable instance : Decidable (c ⤳[α,p] c') := Classical.propDecidable _

@[simp] theorem init_iff : (.init ⤳[α,p] s') ↔ p = 1 ∧ s' = .node α 0 := by aesop
@[simp] theorem node_iff : (.node i j ⤳[α,p] s') ↔ α = 0 ∧ p = 1 ∧ s' = .node i (j + 1) := by aesop
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
    · rw [tsum_eq_single (.node α 0)] <;> simp_all [step_iff]
    · rename_i i j; rw [tsum_eq_single (.node i (j + 1))] <;> simp_all)
  (by
    rintro (_ | ⟨i, j⟩)
    · use 1, 0, .node 0 0; constructor
    · simp)

@[simp] def 𝒜.cost : 𝒜.Costs
| .node i j => if i ≤ j then ⊤ else 0
| _ => 0

@[simp]
theorem 𝒜.act_eq : 𝒜.act = fun s ↦ if s = .init then Set.univ else {0} := by
  ext s α
  split_ifs
  · subst_eqs; simp [𝒜]
  · simp [𝒜]; cases s <;> simp_all

variable {𝒮 : 𝔖[𝒜]}

@[simp] theorem 𝒮_node : 𝒮 {.node i j} = 0 := by have := 𝒮.mem_act {.node i j}; simp_all
@[simp] theorem succs_univ_init : 𝒜.succs_univ .init = {.node α 0 | α} := by simp [𝒜, eq_comm]
@[simp] theorem succs_univ_node : 𝒜.succs_univ (.node i j) = {.node i (j + 1)} := by simp [𝒜]

theorem EC_node_i_le_j_eq_top (h : i ≤ j) : 𝒜.EC 𝒜.cost 𝒮 n (.node i j) = if n = 0 then 0 else ⊤ :=
  by cases n <;> simp [h, EC_succ]

theorem 𝒮_isMarkovian : 𝒮.IsMarkovian := by
  intro π
  if h : π.last = .init then
    have : ∎|π| = 1 := by by_contra q;  have := π.last_mem_succs (by simp_all); simp_all [𝒜]
    exact DFunLike.congr rfl <| Path.ext this (by by_cases · = 0 <;> simp_all)
  else
    have h₁ := 𝒮.mem_act π; have h₂ := 𝒮.mem_act {π.last}; simp_all

instance : 𝒮.Markovian := ⟨𝒮_isMarkovian⟩

@[simp]
theorem EC_step :
    𝒜.EC 𝒜.cost 𝒮 (n + 2) (.node i j) = 𝒜.EC 𝒜.cost 𝒮 (n + 1) (.node i (j + 1)) := by
  rw [EC_succ]; simp
  split_ifs
  · simp_all; rw [EC_node_i_le_j_eq_top (by omega)]; simp
  · simp; rw [tsum_eq_single ⟨.node i (j + 1), by simp_all [𝒜]⟩] <;> simp_all [𝒜]

@[simp]
theorem EC_node_i_j_n_eq_i_j_add_n :
    𝒜.EC 𝒜.cost 𝒮 (n + 1) (.node i j) = 𝒜.EC 𝒜.cost 𝒮 1 (.node i (j + n)) := by
  induction n generalizing i j <;> simp_all; split_ifs <;> first | rfl | omega

@[simp]
theorem EC_init_eq_EC_node :
    𝒜.EC 𝒜.cost 𝒮 (n + 2) .init = 𝒜.EC 𝒜.cost 𝒮 (n + 1) (.node (𝒮 {.init}) 0) := by
  rw [EC_succ]; simp_all
  split_ifs with h
  · exact ENNReal.tsum_eq_top_of_eq_top ⟨⟨.node (𝒮 {.init}) 0, by simp⟩, by simp_all [𝒜]⟩
  · simp_all [𝒜]; rintro s α ⟨_⟩; apply Decidable.not_or_of_imp; rintro ⟨_⟩; assumption

@[simp]
theorem iInf_iSup_EC_eq_0 : ⨅ 𝒮, ⨆ n, 𝒜.EC 𝒜.cost 𝒮 n .init = ⊤ :=
  iInf_eq_top.mpr fun 𝒮 ↦ le_antisymm (by simp) (le_iSup_of_le (𝒮 {.init} + 2) (by simp))

@[simp]
theorem iSup_iInf_EC_eq_top : ⨆ n, ⨅ 𝒮, 𝒜.EC 𝒜.cost 𝒮 n .init = 0 := by
  refine ENNReal.iSup_eq_zero.mpr fun n ↦ ?_
  rcases n with _ | ⟨_ | n⟩ <;> simp_all
  apply (iInf_le_of_le ⟨(if ·.last = .init then n + 1 else 0), by simp⟩ (by simp)).antisymm bot_le

theorem lfp_Φ_node_eq_add :
    𝒜.lfp_Φ 𝒜.cost (.node α i) = 𝒜.lfp_Φ 𝒜.cost (.node α (i + j)) := by
  induction j with simp_all
  | succ j ih =>
    nth_rw 1 [← map_lfp_Φ]
    simp [Φ, Φf]
    split_ifs <;> (rw [← map_lfp_Φ]; simp_all [Φ, Φf, iInf_subtype])
    · split_ifs
      · simp
      · omega
    · rw [tsum_eq_single ⟨.node α (i + j + 1), by simp⟩ (by simp)]; simp_all [𝒜]; rfl

theorem lfp_Φ_node_zero_eq_top : 𝒜.lfp_Φ 𝒜.cost (.node α 0) = ⊤ := by
  rw [lfp_Φ_node_eq_add (j:=α), ← map_lfp_Φ]; simp [Φ, Φf]

theorem lfp_Φ_node_eq_top : 𝒜.lfp_Φ 𝒜.cost (.node α β) = ⊤ := by
  convert_to lfp_Φ 𝒜.cost (.node α (0 + β)) = ⊤
  · simp
  · exact lfp_Φ_node_eq_add.symm.trans lfp_Φ_node_zero_eq_top

@[simp] theorem lfp_Φ_eq_top : 𝒜.lfp_Φ 𝒜.cost .init = ⊤ := by
  rw [← map_lfp_Φ]; simp [Φ, Φf]
  exact fun α ↦ ENNReal.tsum_eq_top_of_eq_top ⟨⟨.node α 0, by simp⟩, by simp [lfp_Φ_node_eq_top, 𝒜]⟩

end MDP.Counterexample.A
