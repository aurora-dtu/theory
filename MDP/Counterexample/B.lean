import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import MDP.OptimalCost
import MDP.Relational
import MDP.SupSup

namespace MDP.Counterexample.B

inductive State where | s₁ | s₂ | s₃
deriving DecidableEq

structure P where
  toFun : ℕ → ENNReal
  property : ∀ n, 0 < toFun n ∧ toFun n < 1

instance : DFunLike P ℕ (fun _ ↦ ENNReal) where
  coe := P.toFun
  coe_injective' := by rintro ⟨a, _⟩ ⟨b, _⟩ h; congr

variable (𝓅 : P)

@[simp] theorem P.zero_lt (α) : 0 < 𝓅 α := (𝓅.property α).left
@[simp] theorem P.lt_one (α) : 𝓅 α < 1 := (𝓅.property α).right
@[simp] theorem P.ne_zero (α) : ¬𝓅 α = 0 := pos_iff_ne_zero.mp (𝓅.zero_lt α)
@[simp] theorem P.ne_one (α) : ¬𝓅 α = 1 := (𝓅.lt_one α).ne
@[simp] theorem P.le_one (α) : 𝓅 α ≤ 1 := (𝓅.lt_one α).le
@[simp] theorem P.one_sub_ne_zero (α) : ¬1 - 𝓅 α = 0 := by simp [tsub_eq_zero_iff_le]
@[simp] theorem P.add_one_sub (α) : 𝓅 α + (1 - 𝓅 α) = 1 := add_tsub_cancel_of_le (𝓅.le_one α)
@[simp] theorem P.ne_top (α) : ¬𝓅 α = ⊤ := (𝓅.lt_one α).ne_top

@[aesop safe [constructors, cases], mk_iff]
inductive Step : State → Option ℕ → ENNReal → State → Prop where
| first : Step .s₁ (some α) (𝓅 α) .s₁
| leave : Step .s₁ (some α) (1 - 𝓅 α) .s₂
| loose : Step .s₂ none 1 .s₃
| loop : Step .s₃ none 1 .s₃

local notation c " ⤳[" 𝓅 "," α "," p "] " c' => Step 𝓅 c α p c'

noncomputable instance : Decidable (c ⤳[𝓅,α,p] c') := Classical.propDecidable _

@[simp] theorem s₁_iff :
    (.s₁ ⤳[𝓅,α,p] s') ↔ ∃ a, α = some a ∧ (s' = .s₁ ∧ p = 𝓅 a ∨ s' = .s₂ ∧ p = 1 - 𝓅 a) := by aesop
@[simp] theorem iff_s₁ : (s ⤳[𝓅,α,p] .s₁) ↔ ∃ a, α = some a ∧ s = .s₁ ∧ p = 𝓅 a := by aesop
@[simp] theorem s₂_iff : (.s₂ ⤳[𝓅,α,p] s') ↔ α = none ∧ p = 1 ∧ s' = .s₃ := by aesop
@[simp] theorem s₃_iff : (.s₃ ⤳[𝓅,α,p] s') ↔ α = none ∧ p = 1 ∧ s' = .s₃ := by aesop

@[simp]
theorem tsum_p :
    (∑' (p : { p // c ⤳[𝓅,α,p] c' }), ↑p) = (∑' p, if c ⤳[𝓅,α,p] c' then p else 0) := by
  apply tsum_eq_tsum_of_ne_zero_bij (fun ⟨x, _⟩ ↦ ⟨x, by simp_all⟩) <;> simp_all
  exact StrictMono.injective fun _ _ a ↦ a

noncomputable def 𝒜 : MDP State (Option ℕ) := ofRelation (Step 𝓅)
  (by rintro s α p s' (_ | _) <;> simp_all)
  (by
    intro s α p₀ c₀ h
    cases h <;> simp_all [ite_and]
    · rw [ENNReal.tsum_eq_add_tsum_ite .s₁]
      simp_all [ite_and]
      rw [ENNReal.tsum_eq_add_tsum_ite .s₂]
      simp_all
    · rw [ENNReal.tsum_eq_add_tsum_ite .s₁]
      simp_all [ite_and]
      rw [ENNReal.tsum_eq_add_tsum_ite .s₂]
      simp_all)
  (by
    rintro (_ | ⟨i, j⟩) <;> simp_all
    use 𝓅 0, some 0, .s₁, 0; simp)

@[simp] def 𝒜.cost : (𝒜 ℯ).Costs
| .s₁ => 1
| _ => 0

@[simp]
theorem 𝒜.act_eq : (𝒜 𝓅).act = fun s ↦ if s = .s₁ then some '' Set.univ else {none} := by
  ext s α
  split_ifs
  · subst_eqs; simp [𝒜]
    aesop
  · simp [𝒜]; cases s <;> simp_all

variable {𝒮 : 𝔖[𝒜 𝓅]}

@[simp] theorem 𝒮_s₂ : 𝒮 {.s₂} = none := by have := 𝒮.mem_act {.s₂}; simp_all
@[simp] theorem 𝒮_s₃ : 𝒮 {.s₃} = none := by have := 𝒮.mem_act {.s₃}; simp_all
@[simp] theorem succs_univ_s₁ : (𝒜 𝓅).succs_univ .s₁ = {.s₁, .s₂} := by
  ext; simp_all [𝒜]
  constructor
  · simp_all
    rintro _ _ _ _ (⟨_, _⟩ | ⟨_, _⟩) <;> simp_all
  · rintro (_ | _) <;> (subst_eqs; simp_all)
    · use some 0, 𝓅 0, 0
    · use some 0, 1 - 𝓅 0, 0
@[simp] theorem succs_univ_s₂ : (𝒜 𝓅).succs_univ .s₂ = {.s₃} := by simp [𝒜]
@[simp] theorem succs_univ_s₃ : (𝒜 𝓅).succs_univ .s₃ = {.s₃} := by simp [𝒜]

def ℒ_a (a : ℕ) : 𝔏[𝒜 𝓅] := ⟨⟨
  fun π ↦ if π.last = .s₁ then some a else none,
  fun π ↦ by simp_all; split_ifs <;> simp⟩,
  by constructor; intro π; simp⟩

@[simp] theorem default_act_s₂ : (𝒜 𝓅).default_act State.s₂ = none := by simp [default_act]
@[simp] theorem default_act_s₃ : (𝒜 𝓅).default_act State.s₃ = none := by simp [default_act]

/-- Picks the action proportional to the length of the scheduled path -/
noncomputable def 𝒮_len (a : ℕ) : 𝔖[𝒜 𝓅] := ⟨
  fun π ↦ if π.last = .s₁ then some (a + ∎|π|) else (𝒜 𝓅).default_act π.last,
  fun π ↦ by
    simp_all; split_ifs <;> simp_all
    set s := π.last with h
    symm at h; rcases s <;> simp_all⟩

abbrev 𝒮_s₁ {𝓅} (𝒮 : 𝔖[𝒜 𝓅]) := (𝒮 {.s₁}).get (by
    refine Option.isSome_iff_exists.mpr ?_
    have := 𝒮.mem_act {.s₁}
    simp at this
    obtain ⟨α, h⟩ := this
    use α
    simp_all)

theorem EC_succ_s₁' :
      (𝒜 𝓅).EC 𝒜.cost 𝒮 .s₁ (n + 1)
    = 1 + 𝓅 (𝒮_s₁ 𝒮) * (𝒜 𝓅).EC 𝒜.cost 𝒮[.s₁ ↦ .s₁]'(by simp) .s₁ n
        + (1 - 𝓅 (𝒮_s₁ 𝒮)) * (𝒜 𝓅).EC 𝒜.cost 𝒮[.s₁ ↦ .s₂]'(by simp) .s₂ n
:= by
  simp [EC_succ]
  rw [ENNReal.tsum_eq_add_tsum_ite ⟨.s₁, by simp_all [𝒜]; aesop⟩]
  rw [ENNReal.tsum_eq_add_tsum_ite ⟨.s₂, by simp_all [𝒜]; aesop⟩]
  simp_all
  simp_all [𝒜]
  simp [add_assoc]
  have : (𝒮 {State.s₁}).isSome = true := by
      refine Option.isSome_iff_exists.mpr ?_
      have := 𝒮.mem_act {.s₁}
      simp at this
      obtain ⟨α, h⟩ := this
      use α
      simp_all
  congr
  · rw [tsum_eq_single (𝓅 ((𝒮 {.s₁}).get this))]
    · split_ifs with h
      · obtain ⟨b, _, _⟩ := h
        simp_all
      · simp_all
        have := h (𝒮_s₁ 𝒮)
        simp_all
        contradiction
    · simp_all
      intro b' h x h'
      contrapose h
      simp_all
      subst_eqs
      have : (𝒮 {State.s₁}).get this = x := Option.get_of_mem this h'
      simp_all
  · have : ∀ {x y z : ENNReal}, x = z → y = 0 → x + y = z := by simp_all
    apply this _ (by simp_all)
    simp_all [ite_and]
    rw [tsum_eq_single (1 - 𝓅 ((𝒮 {.s₁}).get this))]
    · simp_all
      intro h
      have := h (𝒮_s₁ 𝒮)
      simp_all
      contradiction
    · simp_all
      intro b' h x h'
      contrapose h
      simp_all
      subst_eqs
      have : (𝒮 {State.s₁}).get this = x := Option.get_of_mem this h'
      simp_all

@[simp] theorem EC_succ_s₃ : (𝒜 𝓅).EC 𝒜.cost 𝒮 .s₃ n = 0 := by
  induction n generalizing 𝒮 with
  | zero => simp_all
  | succ n ih => simp_all [EC_succ]

@[simp] theorem EC_succ_s₂ : (𝒜 𝓅).EC 𝒜.cost 𝒮 .s₂ n = 0 := by rcases n <;> simp_all [EC_succ]

theorem EC_succ_s₁ :
    (𝒜 𝓅).EC 𝒜.cost 𝒮 .s₁ (n + 1) = 1 + 𝓅 (𝒮_s₁ 𝒮) * (𝒜 𝓅).EC 𝒜.cost 𝒮[.s₁ ↦ .s₁]'(by simp) .s₁ n
:= by simp [EC_succ_s₁']

example :
      (𝒜 𝓅).EC 𝒜.cost (ℒ_a 𝓅 a) .s₁ (n + 1)
    = 1 + 𝓅 a * (𝒜 𝓅).EC 𝒜.cost (ℒ_a 𝓅 a) .s₁ n
:= by
  rw [EC_succ_s₁]
  congr! 2
  apply EC_eq (by simp_all)

/-- Specializes the given scheduler with a chain of `n` repetitions of `[.s₁ ↦ .s₁]` s.t.
    `𝒮[.s₁ ↦ .s₁]^n`. -/
noncomputable def 𝒮_x (𝒮 : 𝔖[𝒜 𝓅]) : ℕ → 𝔖[𝒜 𝓅]
| 0 => 𝒮
| n + 1 => (𝒮_x 𝒮 n)[.s₁ ↦ ⟨.s₁, by simp⟩]

theorem 𝒮_x_add : 𝒮_x 𝓅 (𝒮_x 𝓅 𝒮 n) m = 𝒮_x 𝓅 𝒮 (n + m) := by
  induction m generalizing n 𝒮 with
  | zero => simp [𝒮_x]
  | succ m ih =>
    rw [add_comm, ← add_assoc]
    simp [← ih]
    rfl
noncomputable def 𝒮_x_alt (𝒮 : 𝔖[𝒜 𝓅]) : ℕ → 𝔖[𝒜 𝓅]
  | 0 => 𝒮
  | n + 1 => 𝒮_x 𝓅 𝒮[.s₁ ↦ ⟨.s₁, by simp⟩] n

theorem 𝒮_x_eq_alt (𝒮 : 𝔖[𝒜 𝓅]) :
    𝒮_x 𝓅 𝒮 n = 𝒮_x_alt 𝓅 𝒮 n := by
  induction n generalizing 𝒮 with
  | zero => rfl
  | succ n ih =>
    simp_all [𝒮_x]
    rcases n with _ | n <;> simp_all [𝒮_x_alt]
    simp [𝒮_x] at ih
    rw [ih]

@[simp] theorem 𝒮_x_zero : 𝒮_x 𝓅 𝒮 0 = 𝒮 := rfl

theorem iSup_EC_succ_s₁ :
      ⨆ n, (𝒜 𝓅).EC 𝒜.cost 𝒮 .s₁ n
    = 1 + 𝓅 (𝒮_s₁ 𝒮) * (⨆ n, (𝒜 𝓅).EC 𝒜.cost 𝒮[.s₁ ↦ .s₁]'(by simp) .s₁ n)
:= by
  apply le_antisymm
  · simp
    intro n
    induction n with
    | zero => simp
    | succ n ih => simp [EC_succ_s₁]; gcongr; apply le_iSup
  · simp [ENNReal.mul_iSup, ENNReal.add_iSup]
    intro n
    apply le_iSup_of_le (n + 1)
    simp [EC_succ_s₁]

example {f : ℕ → ENNReal} : ∑' n, f n = f 0 + ∑' n, f (n + 1) := tsum_eq_zero_add' (by simp)

theorem iSup_EC_eq :
    ⨆ n, (𝒜 𝓅).EC 𝒜.cost 𝒮 .s₁ n = ∑' n, ∏ i ∈ Finset.range n, 𝓅 (𝒮_s₁ (𝒮_x 𝓅 𝒮 i)) := by
  simp [ENNReal.tsum_eq_iSup_nat]
  congr with n
  induction n generalizing 𝒮 with
  | zero => simp
  | succ n ih =>
    simp [EC_succ_s₁]
    rw [Finset.sum_range_succ']
    simp [Finset.prod_range_succ']
    rw [add_comm]
    congr
    simp [← Finset.sum_mul]
    rw [mul_comm]
    congr
    simp [𝒮_x_eq_alt]
    apply ih

theorem Path_s₁_prior (π : (𝒜 𝓅).Path) (hi : i < ∎|π|) (h : π[i]'(hi) = State.s₁) (hij : j ≤ i) :
    π[j] = State.s₁ := by
  induction i, hij using Nat.le_induction with
  | base => exact h
  | succ n h' ih =>
    apply ih (by omega)
    have := π.succs_succs_nat (i:=n) (by omega)
    simp_all [𝒜, step_iff]

@[simp]
theorem 𝒮_x_𝒮_len_one : (𝒮_x 𝓅 (𝒮_len 𝓅 n) 1) = 𝒮_len 𝓅 (n + 1) := by
  simp [𝒮_x]
  ext π
  simp_all [𝒮_len]
  split_ifs with h <;> simp_all
  · ring_nf
  · contrapose h
    simp_all
    apply Path_s₁_prior (i:=∎|π| - 1) <;> simp_all

@[simp]
theorem 𝒮_x_𝒮_len : (𝒮_x 𝓅 (𝒮_len 𝓅 n) m) = 𝒮_len 𝓅 (n + m) := by
  induction m generalizing n with
  | zero => simp [𝒮_x]
  | succ m ih =>
    rw [add_comm, ← 𝒮_x_add]
    simp
    rw [ih]
    ring_nf

@[simp] theorem 𝒮_s₁_𝒮_len : 𝒮_s₁ (𝒮_len 𝓅 i) = i + 1 := by
  simp [𝒮_s₁, 𝒮_len]

theorem iSup_EC_𝒮_len :
    ⨆ n, (𝒜 𝓅).EC 𝒜.cost (𝒮_len 𝓅 i) .s₁ n = ∑' (n : ℕ), ∏ x ∈ Finset.range n, 𝓅 (x + 1 + i) := by
  simp [iSup_EC_eq]
  congr! 4
  ring

@[simp]
theorem 𝒮_x_ℒ (ℒ : 𝔏[𝒜 𝓅]) : 𝒮_x 𝓅 ℒ i = ℒ := by
  induction i generalizing ℒ with
  | zero => rfl
  | succ i ih =>
    rw [𝒮_x]
    rw [ih]
    ext π n
    simp [Option.mem_def, MScheduler.toScheduler_apply]
    split_ifs with h
    · simp_all
    · contrapose h
      have := Path_s₁_prior (i:=∎|π| - 1) (π:=π) (j:=0)
      simp_all
      if π.last = .s₁ then
        simp_all
      else
        set s := π.last with h'
        symm at h'
        have := ℒ.toScheduler.mem_act π
        rcases s <;> simp_all

theorem iSup_ECℒ (ℒ : 𝔏[𝒜 𝓅]) :
    ⨆ n, (𝒜 𝓅).EC 𝒜.cost ℒ .s₁ n = (1 - 𝓅 (𝒮_s₁ ℒ.toScheduler))⁻¹
:= by simp [iSup_EC_eq]

theorem iSup_iSup_ECℒ :
    ⨆ ℒ : 𝔏[𝒜 𝓅], ⨆ n, (𝒜 𝓅).EC 𝒜.cost ℒ .s₁ n = ⨆ i, (1 - 𝓅 i)⁻¹
:= by
  simp [iSup_ECℒ]
  apply le_antisymm <;> simp
  · exact fun ℒ ↦ le_iSup_of_le (𝒮_s₁ ℒ.toScheduler) (by rfl)
  · apply fun i ↦ le_iSup_of_le (ℒ_a 𝓅 i) (by simp [ℒ_a, 𝒮_s₁])

def sufficient_lt :=
  ∃ 𝓅 : P, ⨆ i, (1 - 𝓅 i)⁻¹ < ∑' (n : ℕ), ∏ x ∈ Finset.range n, 𝓅 (x + 1)

-- ⨆ i, (1 - 𝓅 i)⁻¹
-- (1 - ⨆ i, 𝓅 i)⁻¹
-- (1 - 99/100)⁻¹
-- (1/100)⁻¹
-- 100


noncomputable def p' (n : ℕ) : ENNReal := 1 - (1/2)^(n + 1) -- 1/2*(1 - (1/2)^n)

example : p' 0 = 1/2 := by simp [p']
example : p' 1 = 1/4 := by simp [p']
example : p' 2 = 1/8 := by
  simp [p']
  ring_nf

-- 1 + p 1 + p 1 * p 2 + p 1 * p 2 * p 3 + ...

theorem iSup_iSup_EC_lt_iSup_iSup_ECℒ_if_sufficent_lt (h : sufficient_lt) :
    ∃ 𝓅, ⨆ ℒ : 𝔏[𝒜 𝓅], ⨆ n, (𝒜 𝓅).EC 𝒜.cost ℒ .s₁ n < ⨆ 𝒮, ⨆ n, (𝒜 𝓅).EC 𝒜.cost 𝒮 .s₁ n := by
  obtain ⟨𝓅, h⟩ := h
  use 𝓅
  apply lt_iSup_iff.mpr
  use 𝒮_len 𝓅 0
  simp [iSup_iSup_ECℒ, iSup_EC_𝒮_len, h]












theorem exists_iSup_iSup_ECℒ_lt_iSup_iSup_EC_if_sufficent_lt (h : sufficient_lt) :
    ∃ (State : Type) (Act : Type) (M : MDP State Act) (c : M.Costs) (s : State),
      ⨅ ℒ : 𝔏[M], ⨆ n, M.EC c ℒ s n < ⨅ 𝒮, ⨆ n, M.EC c 𝒮 s n := by
  obtain ⟨𝓅, h⟩ := iSup_iSup_EC_lt_iSup_iSup_ECℒ_if_sufficent_lt h
  use State, Option ℕ, 𝒜 𝓅, 𝒜.cost, .s₁
  sorry















theorem ashjdashjdasjdhj :
      ∑' (n : ℕ), ∏ x ∈ Finset.range n, 𝓅 (x + 1)
    -- = ⨆ k, ∑ n ∈ Finset.range k, ∏ i ∈ Finset.range n, 𝓅 (i + 1) := by
    = ⨆ k, (1 - (𝓅 (i + 1))^(k + 1)) / (1 - 𝓅 (i + 1)) := by
  simp [ENNReal.tsum_eq_iSup_nat]
  congr! with k
  refine Finset.sum_range_induction _ (fun k ↦ _) ?_ ?_ k
  · simp
    sorry
  · simp_all
    ring_nf
    sorry

theorem one_sub_𝓅_inv_monotone (h : Monotone 𝓅) : Monotone fun i ↦ (1 - 𝓅 i)⁻¹ := by
  refine monotone_nat_of_le_succ ?_
  intro n
  simp_all
  have : 𝓅 n ≤ 𝓅 (n + 1) := h (by simp)
  have : 𝓅 (n + 1) ≤ 1 := 𝓅.le_one (n + 1)
  rw [ENNReal.sub_add_eq_add_sub (by simp) (by simp)]

  sorry

theorem one_sub_𝓅_inv_strict_monotone (h : StrictMono 𝓅) : StrictMono fun i ↦ (1 - 𝓅 i)⁻¹ := by
  refine strictMono_nat_of_lt_succ ?_
  simp
  intro n
  sorry
  -- refine monotone_nat_of_le_succ ?_
  -- intro n
  -- simp_all
  -- have : 𝓅 n ≤ 𝓅 (n + 1) := 𝓅_monotone ε (by simp)
  -- have : 𝓅 (n + 1) ≤ 1 := by sorry
  -- sorry

theorem asdsad (h : ⨆ i, 𝓅 i < 1) : (⨆ i, (1 - 𝓅 i)⁻¹) = (1 - ⨆ i, 𝓅 i)⁻¹ := by
  apply le_antisymm
  · simp
    intro i
    rw [@ENNReal.add_iSup]
    apply le_iSup_of_le i
    exact le_tsub_add
  · sorry
  -- apply le_antisymm
  -- · simp
  --   intro α
  --   have := 𝓅.zero_lt α
  --   have := 𝓅.lt_one α
  --   rw [← ENNReal.tsum_geometric]
  --   simp [-ENNReal.tsum_geometric, ge_iff_le, ENNReal.tsum_eq_iSup_nat]
  --   intro n
  --   simp_all
  --   induction n with
  --   | zero => simp
  --   | succ n ih =>
  --     rw [@geom_sum_succ]


theorem asdhjashj : ∃ 𝓅 : P, (1 - ⨆ i, 𝓅 i)⁻¹ < ⊤ := by
  simp_all
  sorry

theorem asdhjashd : ∃ 𝓅 : P, ∑' (n : ℕ), ∏ x ∈ Finset.range n, 𝓅 (x + 1) = ⊤ := by
  simp [ENNReal.tsum_eq_iSup_nat]
  apply Exists.intro
  · rw [@iSup_eq_top]
    intro b hb
    sorry
  · sorry

  --   -- simp [𝓅]
  --   -- ring_nf
  --   -- refine ENNReal.le_sub_of_add_le_left sorry ?_
  --   -- simp_all
  --   -- ring_nf
  --   -- sorry
  -- · apply le_iSup_of_le 10
  --   simp
  --   ring_nf
  --   refine (ENNReal.le_div_iff_mul_le ?_ ?_).mp ?_ <;> simp

  --   sorry

-- theorem asdasdasd : 𝓅' 0 + 𝓅' 0 * 𝓅' 1 + 𝓅' 0 * 𝓅' 1 * 𝓅' 2 = 6 := by
--   simp [𝓅, ε']
--   ring_nf

theorem iSup_iSup_ECℒ_lt_iSup_iSup_EC (𝓅 : P) (h𝓅 : ⨆ i, 𝓅 i < 1) :
    ∃ 𝓅, ⨆ ℒ : 𝔏[𝒜 𝓅], ⨆ n, (𝒜 𝓅).EC 𝒜.cost ℒ .s₁ n < ⨆ 𝒮, ⨆ n, (𝒜 𝓅).EC 𝒜.cost 𝒮 .s₁ n := by
  use 𝓅
  simp [iSup_iSup_ECℒ]
  apply lt_iSup_iff.mpr
  use 𝒮_len 𝓅 0
  simp [iSup_EC_𝒮_len]
  simp [ENNReal.tsum_eq_iSup_nat]
  -- rw [asdsad _ h𝓅]
  -- rw [ashjdashjdasjdhj]

  sorry

end MDP.Counterexample.B
