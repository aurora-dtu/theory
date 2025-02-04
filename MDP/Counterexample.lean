import MDP.Relational
import MDP.OptimalCost

namespace MDP

namespace Counterexample

def PMF_singleton [DecidableEq α] (x : α) : PMF α := ⟨(if · = x then 1 else 0), by
  rw [Summable.hasSum_iff (by simp)]; simp_all⟩

@[simp]
theorem PMF_singleton.apply [DecidableEq α] (x : α) :
    PMF_singleton x y = if y = x then 1 else 0 := by
  simp [PMF_singleton, DFunLike.coe]

inductive State where
  | init
  | branch (i : ℕ) (j : ℕ)
deriving DecidableEq

@[aesop safe [constructors, cases], mk_iff]
inductive Step : State → ℕ → ENNReal → State → Prop where
| init : Step .init α 1 (.branch α 0)
| step : Step (.branch i j) 0 1 (.branch i (j + 1))

notation c " ⤳[" α "," p "] " c' => Step c α p c'

noncomputable instance : Decidable (c ⤳[α,p] c') := Classical.propDecidable _

@[simp]
theorem init_iff : (.init ⤳[α,p] s') ↔ p = 1 ∧ s' = .branch α 0 := by aesop
@[simp]
theorem branch_iff : (.branch i j ⤳[α,p] s') ↔ α = 0 ∧ p = 1 ∧ s' = .branch i (j + 1) := by aesop
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
    · rw [tsum_eq_single (.branch α 0)] <;> simp_all [step_iff]
    · rename_i i j; rw [tsum_eq_single (.branch i (j + 1))] <;> simp_all)
  (by
    rintro (_ | ⟨i, j⟩)
    · use 1, 0, .branch 0 0; constructor
    · simp)

@[simp] def 𝒜.cost : 𝒜.Costs
| .branch i j => if i ≤ j then ⊤ else 0
| _ => 0

@[simp]
theorem 𝒜.act_eq : 𝒜.act = fun s ↦ if s = .init then Set.univ else {0} := by
  ext s α
  split_ifs
  · subst_eqs; simp [𝒜]
  · simp [𝒜]; cases s <;> simp_all

@[simp]
theorem 𝒮_branch {𝒮 : 𝔖[𝒜]} : 𝒮 {.branch i j} = 0 := by
  have := 𝒮.property {.branch i j}
  simp_all

@[simp] theorem succs_univ_init : 𝒜.succs_univ .init = {.branch α 0 | α} := by
  simp [𝒜, eq_comm]

@[simp] theorem succs_univ_branch : 𝒜.succs_univ (.branch i j) = {.branch i (j + 1)} := by
  simp [𝒜]

theorem EC_branch_i_le_j_eq_top (h : i ≤ j) : 𝒜.EC 𝒜.cost 𝒮 (.branch i j) n = ⊤ := by
  cases n <;> simp [h, EC_succ]

theorem 𝒮_isMarkovian {𝒮 : 𝔖[𝒜]} : 𝒮.IsMarkovian := by
  intro π
  if h : π.last = .init then
    have : ∎|π| = 1 := by by_contra q;  have := π.last_mem_succs (by simp_all); simp_all [𝒜]
    exact DFunLike.congr rfl <| Path.ext this (by by_cases · = 0 <;> simp_all)
  else
    have h₁ := 𝒮.mem_act (π:=π); have h₂ := 𝒮.mem_act (π:={π.last})
    simp_all

instance {𝒮 : 𝔖[𝒜]} : 𝒮.Markovian := ⟨𝒮_isMarkovian⟩

@[simp]
theorem EC_step :
    𝒜.EC 𝒜.cost 𝒮 (.branch i j) (n + 1) = 𝒜.EC 𝒜.cost 𝒮 (.branch i (j + 1)) n := by
  simp [EC_succ]
  split_ifs
  · simp_all; rw [EC_branch_i_le_j_eq_top (by omega)]
  · rw [tsum_eq_single ⟨.branch i (j + 1), by simp_all [𝒜, PMF_singleton]⟩] <;> simp_all [𝒜]

@[simp]
theorem EC_branch_i_j_n_eq_i_j_add_n :
    𝒜.EC 𝒜.cost 𝒮 (.branch i j) n = 𝒜.EC 𝒜.cost 𝒮 (.branch i (j + n)) 0 := by
  simp
  split_ifs with h
  all_goals
  induction n generalizing i j with
  | zero => simp_all
  | succ n ih => simp_all; rw [ih]; omega

@[simp]
theorem EC_init_eq_EC_branch :
    𝒜.EC 𝒜.cost 𝒮 .init (n + 1) = 𝒜.EC 𝒜.cost 𝒮 (.branch (𝒮 {.init}) 0) n := by
  simp_all [EC_succ]
  split_ifs with h
  · rw [succs_univ_init]; simp_all
    rw [tsum_eq_single ⟨.branch (𝒮 {.init}) 0, by simp⟩] <;> simp_all [𝒜]
  · simp_all [𝒜]; rintro s α ⟨_⟩; apply Decidable.not_or_of_imp; rintro ⟨_⟩; assumption

@[simp]
theorem 𝒜.iInf_iSup_eq_eq_0 : ⨅ 𝒮, ⨆ n, 𝒜.EC 𝒜.cost 𝒮 .init n = ⊤ :=
  iInf_eq_top.mpr fun 𝒮 ↦ le_antisymm (by simp) (le_iSup_of_le (𝒮 {.init} + 1) (by simp))

@[simp]
theorem 𝒜.iSup_iInf_eq_eq_top : ⨆ n, ⨅ 𝒮, 𝒜.EC 𝒜.cost 𝒮 .init n = 0 := by
  refine ENNReal.iSup_eq_zero.mpr fun n ↦ ?_
  rcases n with _ | n <;> simp_all
  apply (iInf_le_of_le ⟨(if ·.last = .init then n + 1 else 0), by simp⟩ (by simp)).antisymm bot_le

end MDP.Counterexample
