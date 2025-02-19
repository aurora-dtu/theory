import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import MDP.OptimalCost
import MDP.Relational
import MDP.SupSup

namespace MDP.Counterexample.C

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
| .s₂ => 1
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
  fun π ↦ if π.last = .s₁ then some (a + ‖π‖) else (𝒜 𝓅).default_act π.last,
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


@[simp] theorem EC_succ_s₃ : (𝒜 𝓅).EC 𝒜.cost 𝒮 n .s₃ = 0 := by
  induction n generalizing 𝒮 with
  | zero => simp_all
  | succ n ih => simp_all [EC_succ]

@[simp] theorem EC_succ_s₂ : (𝒜 𝓅).EC 𝒜.cost 𝒮 n .s₂ = if n = 0 then 0 else 1 := by
  rcases n <;> simp_all [EC_succ]; rw [tsum_eq_single ⟨.s₃, by simp_all [𝒜]⟩] <;> simp_all

theorem EC_succ_s₁' :
      (𝒜 𝓅).EC 𝒜.cost 𝒮 (n + 1) .s₁
    = 𝓅 (𝒮_s₁ 𝒮) * (𝒜 𝓅).EC 𝒜.cost 𝒮[.s₁ ↦ .s₁]'(by simp) n .s₁
        + (1 - 𝓅 (𝒮_s₁ 𝒮)) * (𝒜 𝓅).EC 𝒜.cost 𝒮[.s₁ ↦ .s₂]'(by simp) n .s₂
:= by
  simp
  simp [EC_succ]
  rw [ENNReal.tsum_eq_add_tsum_ite ⟨.s₁, by simp_all [𝒜]; aesop⟩]
  rw [ENNReal.tsum_eq_add_tsum_ite ⟨.s₂, by simp_all [𝒜]; aesop⟩]
  simp_all
  simp_all [𝒜]
  -- simp [add_assoc]
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
  · rcases n with _ | n <;> simp_all
    have : ∀ {x y z : ENNReal}, x = z → y = 0 → x + y = z := by simp_all
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

theorem EC_succ_s₁ :
    (𝒜 𝓅).EC 𝒜.cost 𝒮 (n + 1) .s₁
  = 𝓅 (𝒮_s₁ 𝒮) * (𝒜 𝓅).EC 𝒜.cost 𝒮[.s₁ ↦ .s₁]'(by simp) n .s₁ + if n = 0 then 0 else 1 - 𝓅 (𝒮_s₁ 𝒮)
:= by simp [EC_succ_s₁']

-- example :
--       (𝒜 𝓅).EC 𝒜.cost (ℒ_a 𝓅 a) .s₁ (n + 1)
--     = 1 + 𝓅 a * (𝒜 𝓅).EC 𝒜.cost (ℒ_a 𝓅 a) .s₁ n
-- := by
--   rw [EC_succ_s₁]
--   congr! 2
--   apply EC_eq (by simp_all)

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
      ⨆ n, (𝒜 𝓅).EC 𝒜.cost 𝒮 n .s₁
    = 𝓅 (𝒮_s₁ 𝒮) * (⨆ n, (𝒜 𝓅).EC 𝒜.cost 𝒮[.s₁ ↦ .s₁]'(by simp) n .s₁) + (1 - 𝓅 (𝒮_s₁ 𝒮))
:= by
  apply le_antisymm
  · simp
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rcases n with _ | n
      · simp [EC_succ_s₁]
      · rw [EC_succ_s₁]; simp; gcongr; exact le_iSup_iff.mpr fun _ h ↦ h (n + 1)
  · simp [ENNReal.mul_iSup, ENNReal.add_iSup, ENNReal.iSup_add]
    intro n
    rcases n with _ | n <;> simp_all [EC_succ_s₁, ENNReal.add_iSup, ENNReal.iSup_add]
    · apply le_iSup_of_le 2
      simp [EC_succ_s₁, le_tsub_add]
    · apply le_iSup_of_le (n + 2)
      simp [EC_succ_s₁]

example {f : ℕ → ENNReal} : ∑' n, f n = f 0 + ∑' n, f (n + 1) := tsum_eq_zero_add' (by simp)

theorem asjhdasd : (𝒮.specialize State.s₁ ⟨State.s₁, by simp⟩) = 𝒮_x 𝓅 𝒮 1 := by rfl

theorem iSup_EC_succ_eq_iSup_EC :
    ⨆ n, (𝒜 𝓅).EC 𝒜.cost 𝒮 (n + 1) .s₁ = ⨆ n, (𝒜 𝓅).EC 𝒜.cost 𝒮 n .s₁ :=
  (iSup_le fun n ↦ le_iSup_of_le (n + 1) (by rfl)).antisymm (iSup_le (le_iSup_of_le · EC_le_succ))

theorem iSup_EC_eq :
      ⨆ n, (𝒜 𝓅).EC 𝒜.cost 𝒮 n .s₁
    = ∑' n, (1 - 𝓅 (𝒮_s₁ (𝒮_x 𝓅 𝒮 n))) * ∏ i ∈ Finset.range n, 𝓅 (𝒮_s₁ (𝒮_x 𝓅 𝒮 i)) := by
  rw [← iSup_EC_succ_eq_iSup_EC]
  simp [ENNReal.tsum_eq_iSup_nat]
  congr with n
  induction n generalizing 𝒮 with
  | zero => simp
  | succ n ih =>
    rw [EC_succ_s₁]
    simp
    rw [ih]; clear ih
    rw [Finset.sum_range_succ']
    simp
    simp [Finset.prod_range_succ']
    conv =>
      right
      arg 1
      arg 2
      ext n
      rw [← mul_assoc]
    simp [← Finset.sum_mul]
    nth_rw 2 [mul_comm]
    simp [asjhdasd, 𝒮_x_add]
    simp [add_comm]

theorem Path_s₁_prior (π : (𝒜 𝓅).Path) (hi : i < ‖π‖) (h : π[i]'(hi) = State.s₁) (hij : j ≤ i) :
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
    apply Path_s₁_prior (i:=‖π‖ - 1) <;> simp_all

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
      ⨆ n, (𝒜 𝓅).EC 𝒜.cost (𝒮_len 𝓅 i) n .s₁
    = ∑' (n : ℕ), (1 - 𝓅 (i + n + 1)) * ∏ x ∈ Finset.range n, 𝓅 (i + x + 1) :=
by
  simp [iSup_EC_eq]
--   congr! 4
--   ring

instance {State : Type*} {Act: Type*} {M : MDP State Act} : Membership State M.Path where
  mem π s := ∃ i : Fin ‖π‖, π[i] = s

noncomputable instance {State : Type*} {Act: Type*} [DecidableEq State] {M : MDP State Act}
    {π : M.Path} (s : State) : Decidable (∀ s' ∈ π, s' = s) :=
  Classical.propDecidable (∀ s' ∈ π, s' = s)

@[simp]
theorem Path.mem_states {State : Type*} {Act: Type*} [DecidableEq State] {M : MDP State Act}
    {π : M.Path} {a : State} : a ∈ π.states ↔ a ∈ π := by
  simp [List.mem_iff_getElem]
  simp [Membership.mem, Fin.exists_iff]

theorem EC_𝒮_len' :
      (𝒜 𝓅).EC 𝒜.cost (𝒮_len 𝓅 i) n .s₁
    = if n = 0 then 0
      else 1 - ∑' π : Path[𝒜 𝓅,.s₁,=n], if ∀ s ∈ π.val, s = .s₁ then π.val.Prob (𝒮_len 𝓅 i) else 0
:= by
  rcases n with _ | n
  · simp
  · simp [EC]
    congr with ⟨π, hπ⟩
    simp_all; simp_all
    split_ifs
    · simp_all [Path.ECost, Path.Cost]
      left
      refine List.sum_eq_zero ?_
      simp_all
    · simp_all [Path.ECost]
      suffices π.Cost 𝒜.cost = 1 by simp_all
      sorry

theorem asdjhsad :
      (∑' π : Path[𝒜 𝓅,.s₁,=n], if ∀ s ∈ π.val, s = .s₁ then π.val.Prob (𝒮_len 𝓅 i) else 0)
    = if n = 0 then 0 else ∏ x : Fin (n - 1), 𝓅 (x + i + 1) := by
  rcases n with _ | n
  · simp
  · let π' : (𝒜 𝓅).Path := ⟨List.replicate (n + 1) .s₁, by simp, by simp⟩
    rw [tsum_eq_single ⟨π', by simp [π']⟩]
    · simp_all [Membership.mem, Path.Prob]
      split_ifs
      · simp [𝒮_len]
        simp_all [π', 𝒜]
        conv =>
          left
          arg 2
          ext x
          rw [min_eq_left (by obtain ⟨_, _⟩ := x; simp_all; simp_all; omega)]
        apply Function.Bijective.finset_prod (fun ⟨x, _⟩ ↦ ⟨x, by simp_all⟩)
        · simp; rfl
        · simp; ring_nf; simp
      · simp_all [π']
    · simp_all
      intro π h h' h'' h'''
      simp_all [Membership.mem]
      contrapose h''
      simp_all
      ext i h₁ h₂ <;>simp_all [π']
      exact h''' ⟨i, by omega⟩

  -- rw [← Path.one_sub_tsum_ite_Prob_eq (𝒮:=𝒮_len 𝓅 i) (s:=.s₁) (n:=n) (p:=fun π ↦ ∀ s ∈ π.val, s = .s₁)]

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
      have := Path_s₁_prior (i:=‖π‖ - 1) (π:=π) (j:=0)
      simp_all
      if π.last = .s₁ then
        simp_all
      else
        set s := π.last with h'
        symm at h'
        have := ℒ.toScheduler.mem_act π
        rcases s <;> simp_all

theorem iSup_ECℒ (ℒ : 𝔏[𝒜 𝓅]) :
    ⨆ n, (𝒜 𝓅).EC 𝒜.cost ℒ n .s₁ = 1
:= by simp [iSup_EC_eq, ENNReal.tsum_mul_left, ENNReal.mul_inv_cancel]

theorem iSup_iSup_ECℒ : ⨆ ℒ : 𝔏[𝒜 𝓅], ⨆ n, (𝒜 𝓅).EC 𝒜.cost ℒ n .s₁ = 1 := by
  simp_all [iSup_ECℒ]

theorem iInf_iSup_ECℒ : ⨅ ℒ : 𝔏[𝒜 𝓅], ⨆ n, (𝒜 𝓅).EC 𝒜.cost ℒ n .s₁ = 1 := by
  simp_all [iSup_ECℒ]

def sufficient_lt :=
  ∃ 𝓅 : P, ∑' (n : ℕ), (1 - 𝓅 (n + 1)) * ∏ x ∈ Finset.range n, 𝓅 (x + 1) < 1

-- ⨆ i, (1 - 𝓅 i)⁻¹
-- (1 - ⨆ i, 𝓅 i)⁻¹
-- (1 - 99/100)⁻¹
-- (1/100)⁻¹
-- 100


noncomputable def p' (ε : {ε : ENNReal // 0 < ε ∧ ε < 1}) (n : ℕ) : ENNReal :=
  (1 - ε)^((2 ^ n)⁻¹ : ℝ)
  -- (1 - ε)^((2⁻¹ : ℝ) ^ n)
theorem p'_bounded (n : ℕ) : 0 < p' ε n ∧ p' ε n < 1 := by
  obtain ⟨ε, h⟩ := ε
  simp [p']; ring_nf
  constructor
  · refine ENNReal.rpow_pos ?_ ?_ <;> simp_all
  · refine ENNReal.rpow_lt_one ((ENNReal.sub_lt_self_iff ?_).mpr ?_) ?_ <;> simp_all

example : p' ε 0 = 1 - ε := by simp [p']
example : p' ε 1 = (1 - ε)^(2⁻¹ : ℝ) := by simp [p']
example : p' ε 2 = (1 - ε)^(4⁻¹ : ℝ) := by simp [p']; ring_nf
example : p' ε 3 = (1 - ε)^(8⁻¹ : ℝ) := by simp [p']; ring_nf
example : p' ε 4 = (1 - ε)^(16⁻¹ : ℝ) := by simp [p']; ring_nf

example (ε : {ε : ENNReal // 0 < ε ∧ ε < 1}) : sufficient_lt := by
  exists ⟨p' ε, p'_bounded⟩
  simp [DFunLike.coe]
  simp [p']
  sorry

theorem asdasd (hn : 0 < n) : ∃! π ∈ Path[𝒜 𝓅,.s₁,=n], ∀ s ∈ π, s = .s₁ := by
  simp_all only [Path_eq.iff]
  exists ⟨List.replicate n .s₁, by simp; omega, by simp⟩
  simp_all [Membership.mem, eq_comm]
  rintro π ⟨⟨⟨_⟩, _⟩, h⟩
  ext i h₁ h₂
  · simp_all
  · have := h π[i] ⟨i, by omega⟩
    simp_all
-- theorem asdsadsad (hn : 0 < n) : (𝒜 𝓅).EC 𝒜.cost 𝒮 .s₁ n = 1 := by
--   simp [EC]
--   rw [ENNReal.tsum_eq_add_tsum_ite ⟨⟨List.replicate n .s₁, by simp; omega, by simp⟩, by simp⟩]
--   simp_all
--   nth_rw 1 [Path.ECost]
--   simp [Path.Cost, Subtype.eq_iff]
--   have : ∀ (x : Path[𝒜 𝓅,State.s₁,=n]),
--         x.val = ⟨List.replicate n State.s₁, by simp; omega, by simp⟩
--       ↔ ∀ i : Fin ‖x.val‖, x.val[i] = .s₁ := by
--     simp_all
--     rintro π ⟨hn, h⟩
--     constructor
--     · rintro ⟨_⟩
--       simp
--     · intro h'
--       ext i <;> simp_all
--       apply h' ⟨i, by simp_all⟩
--   simp [this]; clear this
--   have : ∀ (x : Path[𝒜 𝓅,State.s₁,=n]),
--         (∃ i : Fin ‖x.val‖, ¬x.val[i] = .s₁)
--       ↔ ∃ i : Fin ‖x.val‖, x.val[i] = .s₂ := by
--     simp_all
--     rintro π ⟨hn, h⟩
--     constructor <;> simp_all <;> intro i hi
--     · sorry
--     · sorry
--   conv => left; arg 1; ext; rw [← ite_not]
--   simp_all; clear this
--   induction n with
--   | zero => simp_all
--   | succ n ih =>
--     simp_all
--     rcases n with _ | n
--     · sorry
--     · rw []


  -- simp_all [ite_ite_comm]
  -- conv =>
  --   left
  --   arg 1
  --   ext

  -- sorry

theorem tprod_split (f : ℕ → ENNReal) (m : ℕ) :
    (∏' n, f n) = (∏ n : Fin m, f n) * ∏' n, f (n + m + 1) := by
  -- have := prod_mul_tprod_compl (α:=ENNReal) (f:=f)
  symm
  apply (ENNReal.eq_div_iff sorry sorry).mp
  sorry
  -- refine Eq.symm ((fun {a b c} ha ha' ↦ (ENNReal.eq_div_iff ha ha').mp) ?_ ?_ ?_)
  -- <;> sorry

theorem iInf_iSup_ECℒ_lt_iInf_iSup_EC_if_sufficent_lt (ε : {ε : ENNReal // 0 < ε ∧ ε < 1}) :
    ∃ 𝓅, ⨅ 𝒮, ⨆ n, (𝒜 𝓅).EC 𝒜.cost 𝒮 n .s₁ < ⨅ ℒ : 𝔏[𝒜 𝓅], ⨆ n, (𝒜 𝓅).EC 𝒜.cost ℒ n .s₁ := by
  -- obtain ⟨𝓅, h⟩ := h
  simp [iInf_iSup_ECℒ]
  use ⟨p' ε, p'_bounded⟩
  refine iInf_lt_iff.mpr ⟨𝒮_len (⟨p' ε, p'_bounded⟩) 0, ?_⟩
  simp only [EC_𝒮_len', AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, ↓reduceIte]
  simp [asdjhsad (𝓅:=⟨p' ε, p'_bounded⟩) (i:=0)]
  simp_all [DFunLike.coe]
  -- apply?
  rw [@iSup_lt_iff]
  exists 1 - ∏' x, p' ε (↑x + 1)
  -- simp_all
  constructor
  ·
    -- have ⟨h₁, h₂⟩ := p'_bounded q (ε:=ε)
    refine (ENNReal.sub_lt_self_iff ?_).mpr ?_ <;> simp_all
    simp [p']
    sorry
    -- rintro ⟨i, hi⟩
    -- simp_all
    -- exact p'_bounded (i + 1) |>.left
  · rintro (_ | n) <;> simp_all
    rw [ENNReal.sub_add_eq_add_sub]
    · have : ∀ {x y z : ENNReal}, z < y → x ≤ x + y - z := by
        refine fun {x y z} h ↦ ?_
        refine ENNReal.le_sub_of_add_le_left ?_ ?_
        · exact LT.lt.ne_top h
        · rw [add_comm]; gcongr
      apply this
      simp [p']
      sorry
    · sorry
      -- refine Fintype.prod_le_one fun i ↦ ?_
      -- exact p'_bounded (i + 1) |>.right |>.le
    · sorry
      -- refine ENNReal.prod_ne_top fun i ↦ ?_
      -- simp_all
      -- exact p'_bounded (i + 1) |>.right |>.ne_top

-- theorem iSup_iSup_EC_lt_iSup_iSup_ECℒ_if_sufficent_lt (ε : {ε : ENNReal // 0 < ε ∧ ε < 1}) :
--     ∃ 𝓅, ⨆ 𝒮, ⨆ n, (𝒜 𝓅).EC 𝒜.cost 𝒮 .s₁ n < ⨆ ℒ : 𝔏[𝒜 𝓅], ⨆ n, (𝒜 𝓅).EC 𝒜.cost ℒ .s₁ n := by
--   simp [iSup_iSup_ECℒ]
--   use ⟨p' ε, p'_bounded⟩
--   apply iSup_lt_iff.mpr
--   apply lt_iSup_iff.mpr
--   use 𝒮_len ⟨p' ε, p'_bounded⟩ 0
--   rw [← iSup_EC_succ_eq_iSup_EC]
--   simp only [EC_𝒮_len', AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, ↓reduceIte]
--   simp [asdjhsad (𝓅:=⟨p' ε, p'_bounded⟩) (i:=0)]
--   simp [p', DFunLike.coe]
--   rw [@lt_iSup_iff]
--   sorry












theorem exists_iSup_iSup_ECℒ_lt_iSup_iSup_EC_if_sufficent_lt (h : sufficient_lt) :
    ∃ (State : Type) (Act : Type) (M : MDP State Act) (c : M.Costs) (s : State),
      ⨅ ℒ : 𝔏[M], ⨆ n, M.EC c ℒ n s < ⨅ 𝒮, ⨆ n, M.EC c 𝒮 n s := by
  -- obtain ⟨𝓅, h⟩ := iSup_iSup_EC_lt_iSup_iSup_ECℒ_if_sufficent_lt h
  -- use State, Option ℕ, 𝒜 𝓅, 𝒜.cost, .s₁
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
    ∃ 𝓅, ⨆ ℒ : 𝔏[𝒜 𝓅], ⨆ n, (𝒜 𝓅).EC 𝒜.cost ℒ n .s₁ < ⨆ 𝒮, ⨆ n, (𝒜 𝓅).EC 𝒜.cost 𝒮 n .s₁ := by
  use 𝓅
  simp [iSup_iSup_ECℒ]
  apply lt_iSup_iff.mpr
  use 𝒮_len 𝓅 0
  simp [iSup_EC_𝒮_len]
  simp [ENNReal.tsum_eq_iSup_nat]
  -- rw [asdsad _ h𝓅]
  -- rw [ashjdashjdasjdhj]

  sorry

end MDP.Counterexample.C

-- NOTE: what is this?
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/SupIndep.html#iSupIndep
