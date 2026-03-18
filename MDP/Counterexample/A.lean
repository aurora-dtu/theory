import MDP.OptimalCost
import MDP.Relational

namespace MDP.Counterexample.A

/-!
# Counterexample exhibiting `⨆ n, ⨅ 𝒮, EC c 𝒮 n < ⨅ 𝒮, ⨆ n, EC c 𝒮 n`

```
  s⋆-----+-----+·····+·····
  |      |     |     |
s₀,₀   s₀,₁  s₀,₂  s₀,ᵢ
  ⋮      |     |     ⋮
  ∞    s₁,₁  s₁,₂    ⋮
         ⋮     |     ⋮
         ∞   s₂,₂    ⋮
               ⋮   sᵢ,ᵢ
               ∞     ⋮
                     ∞
```

**Setup**: ([instance](#MDP.Counterexample.A.M))
- The MDP consists of states `s⋆` and `sᵢ,ⱼ` for all `i` and `j` with actions in `ℕ`.
- In the initial state `s⋆` has all actions enabled (that is all `ℕ`).
- Every other state only has the action `0` enabled.
- There is a transition from `s⋆` to all `s₀,ᵢ` for all `i ∈ ℕ` with action `i`.
- For all states `sᵢ,ⱼ` there is a transition to `sᵢ₊₁,ⱼ`.
- Every transition is non-probabilistic (i.e. probability = 1).
- The cost of states are either `0` or `⊤`.
  - `s⋆` and `sᵢ,ⱼ` where `i < j` has cost `0`.
  - `sᵢ,ⱼ` where `i ≥ j` has cost `⊤`.

Now consider the two order of optimization `⨆ n, ⨅ 𝒮, EC c 𝒮 n` and `⨅ 𝒮, ⨆ n, EC c 𝒮 n`.

In the first case we the scheduler gets to make its choice based on `n`, and thus can choose a an
action where the depth will not reach a state like `sᵢ,ᵢ` with `⊤` cost. Thus the expected cost for
the `⨆⨅` order will be `0`.

In the second case we consider first a scheduler and then a depth. That means that we can pick a
depth, say `i+1`, where the action the scheduler picked in `s⋆` was `i`. In this case we will
_always_ be able to pick a depth that reaches a state with `⊤` cost. Thus the expected cost for
the `⨅⨆` order will be `⊤`.

This leads to `iSup_iInf_EC_lt_iInf_iSup_EC`.

Additionally we can show the same for `MDP.lfp_Φ𝒟` giving us `iSup_iInf_EC_lt_lfp_Φ𝒟`.

-/

inductive State where
  | init
  | node (i : ℕ) (j : ℕ)
deriving DecidableEq

@[aesop safe [constructors, cases], mk_iff]
inductive Step : State → ℕ → ENNReal → State → Prop where
| choice : Step .init α 1 (.node 0 α)
| step : Step (.node i j) 0 1 (.node (i + 1) j)

local notation c " ⤳[" α "," p "] " c' => Step c α p c'

noncomputable instance : Decidable (c ⤳[α,p] c') := Classical.propDecidable _

@[simp] theorem init_iff : (.init ⤳[α,p] s') ↔ p = 1 ∧ s' = .node 0 α := by aesop
@[simp] theorem node_iff : (.node i j ⤳[α,p] s') ↔ α = 0 ∧ p = 1 ∧ s' = .node (i + 1) j := by aesop
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
    · rw [tsum_eq_single (.node 0 α)] <;> simp_all [step_iff]
    · rename_i i j; rw [tsum_eq_single (.node (i + 1) j)] <;> simp_all)
  (by
    rintro (_ | ⟨i, j⟩)
    · use 1, 0, .node 0 0; constructor
    · simp)

@[simp] def M.cost : M.Costs
| .node i j => if j ≤ i then ⊤ else 0
| _ => 0

@[simp]
theorem M.act_eq : M.act = fun s ↦ if s = .init then Set.univ else {0} := by
  ext s α
  split_ifs
  · subst_eqs; simp [M]
  · simp [M]; cases s <;> simp_all

variable {𝒮 : 𝔖[M]}

@[simp] theorem 𝒮_node : 𝒮 {.node i j} = 0 := by have := 𝒮.mem_act {.node i j}; simp_all
@[simp] theorem succs_univ_init : M.succs_univ .init = {.node 0 α | α} := by simp [M, eq_comm]
@[simp] theorem succs_univ_node : M.succs_univ (.node i j) = {.node (i + 1) j} := by simp [M]

theorem EC_node_i_le_j_eq_top (h : j ≤ i) : M.EC M.cost 𝒮 n (.node i j) = if n = 0 then 0 else ⊤ :=
  by cases n <;> simp [h, EC_succ]

theorem 𝒮_isMarkovian : 𝒮.IsMarkovian := by
  intro π
  if h : π.last = .init then
    have : ‖π‖ = 1 := by by_contra q;  have := π.last_mem_succs (by simp_all); simp_all [M]
    exact DFunLike.congr rfl <| Path.ext this (by by_cases · = 0 <;> simp_all)
  else
    have h₁ := 𝒮.mem_act π; have h₂ := 𝒮.mem_act {π.last}; simp_all

instance : 𝒮.Markovian := ⟨𝒮_isMarkovian⟩

@[simp]
theorem EC_step :
    M.EC M.cost 𝒮 (n + 2) (.node i j) = M.EC M.cost 𝒮 (n + 1) (.node (i + 1) j) := by
  rw [EC_succ]; simp
  split_ifs
  · simp_all; rw [EC_node_i_le_j_eq_top (by omega)]; simp
  · simp; rw [tsum_eq_single ⟨.node (i + 1) j, by simp_all [M]⟩] <;> simp_all [M]

@[simp]
theorem EC_node_i_j_n_eq_i_j_add_n :
    M.EC M.cost 𝒮 (n + 1) (.node i j) = M.EC M.cost 𝒮 1 (.node (i + n) j) := by
  induction n generalizing i j <;> simp_all; split_ifs <;> first | rfl | omega

@[simp]
theorem EC_init_eq_EC_node :
    M.EC M.cost 𝒮 (n + 2) .init = M.EC M.cost 𝒮 (n + 1) (.node 0 (𝒮 {.init})) := by
  rw [EC_succ]; simp_all
  split_ifs with h
  · exact ENNReal.tsum_eq_top_of_eq_top ⟨⟨.node 0 (𝒮 {.init}), by simp⟩, by simp_all; simp [M]⟩
  · simp_all; simp [M]; grind

@[simp]
theorem iInf_iSup_EC_eq_0 : ⨅ 𝒮, ⨆ n, M.EC M.cost 𝒮 n .init = ⊤ :=
  iInf_eq_top.mpr fun 𝒮 ↦ le_antisymm (by simp) (le_iSup_of_le (𝒮 {.init} + 2) (by simp))

@[simp]
theorem iSup_iInf_EC_eq_top : ⨆ n, ⨅ 𝒮, M.EC M.cost 𝒮 n .init = 0 := by
  refine ENNReal.iSup_eq_zero.mpr fun n ↦ ?_
  rcases n with _ | ⟨_ | n⟩ <;> simp_all
  apply (iInf_le_of_le ⟨(if ·.last = .init then n + 1 else 0), by simp⟩ (by simp)).antisymm bot_le

@[simp]
theorem iInf_iSup_ECℒ_eq_0 : ⨅ ℒ : 𝔏[M], ⨆ n, M.EC M.cost ℒ n .init = ⊤ :=
  iInf_eq_top.mpr fun ℒ ↦ le_antisymm (by simp) (le_iSup_of_le (ℒ {.init} + 2) (by simp))

@[simp]
theorem iSup_iInf_ECℒ_eq_top : ⨆ n, ⨅ ℒ : 𝔏[M], M.EC M.cost ℒ n .init = 0 := by
  refine ENNReal.iSup_eq_zero.mpr fun n ↦ ?_
  rcases n with _ | ⟨_ | n⟩ <;> simp_all
  apply (iInf_le_of_le ⟨⟨(if ·.last = .init then n + 1 else 0), by simp⟩,
      by constructor; intro; simp_all⟩ (by simp [DFunLike.coe])).antisymm bot_le

open OrderHom Optimization.Notation

theorem lfp_Φ𝒟_node_eq_add :
    lfp (Φ 𝒟 M.cost) (.node i α) = lfp (Φ 𝒟 M.cost) (.node (i + j) α) := by
  induction j with simp_all
  | succ j ih =>
    nth_rw 1 [← map_lfp]
    simp only [Φ, M.cost, M.act_eq, Φf, coe_mk, reduceCtorEq, ↓reduceIte,
      Optimization.sOpt_singleton]
    split_ifs <;> (rw [← map_lfp]; simp_all [Φ, Φf, -map_lfp])
    · split_ifs
      · simp only [top_add]
      · omega
    · rw [tsum_eq_single ⟨.node (i + j + 1) α, by simp⟩ (by simp)]; simp_all only [M,
      ofRelation_P, tsum_p, node_iff, and_true, true_and, tsum_ite_eq, reduceCtorEq,
      not_false_eq_true, forall_const, iInf_iInf_eq_left, one_mul]; rfl

theorem lfp_Φ𝒟_node_zero_eq_top : lfp (Φ 𝒟 M.cost) (.node 0 α) = ⊤ := by
  rw [lfp_Φ𝒟_node_eq_add (j:=α), ← map_lfp]; simp [Φ, Φf, -map_lfp]

theorem lfp_Φ𝒟_node_eq_top : lfp (Φ 𝒟 M.cost) (.node α β) = ⊤ := by
  convert_to lfp (Φ 𝒟 M.cost) (.node (0 + α) β) = ⊤
  · simp
  · exact lfp_Φ𝒟_node_eq_add.symm.trans lfp_Φ𝒟_node_zero_eq_top

@[simp] theorem lfp_Φ𝒟_eq_top : lfp (Φ 𝒟 M.cost) .init = ⊤ := by
  rw [← map_lfp]; simp [Φ, Φf, -map_lfp]
  exact fun α ↦ ENNReal.tsum_eq_top_of_eq_top ⟨⟨.node 0 α, by simp⟩, by
    simp_all only [M, ofRelation_P, tsum_p, init_iff, and_true, tsum_ite_eq, one_mul]
    convert lfp_Φ𝒟_node_eq_top with h h'
    simp [Φ, Φf]
    congr!
    simp only [M, ofRelation_P, tsum_p]
    grind⟩

theorem iSup_iInf_EC_lt_iInf_iSup_EC :
    ⨆ n, ⨅ 𝒮, M.EC M.cost 𝒮 n .init < ⨅ 𝒮, ⨆ n, M.EC M.cost 𝒮 n .init := by simp

theorem iSup_iInf_ECℒ_lt_iInf_iSup_ECℒ :
    ⨆ n, ⨅ ℒ : 𝔏[M], M.EC M.cost ℒ n .init < ⨅ ℒ : 𝔏[M], ⨆ n, M.EC M.cost ℒ n .init := by
  simp

theorem iSup_iInf_EC_lt_lfp_Φ𝒟 :
    ⨆ n,  ⨅ 𝒮, M.EC M.cost 𝒮 n .init < lfp (Φ 𝒟 M.cost) .init := by simp

end MDP.Counterexample.A
