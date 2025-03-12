import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import MDP.OptimalCost
import MDP.Relational
import MDP.SupSup
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

namespace MDP.Counterexample.C

inductive State where | s₁ | s₂ | s₃
deriving DecidableEq

structure P where
  toFun : ℕ → ENNReal
  property : ∀ n, 0 < toFun n ∧ toFun n < 1

instance : DFunLike P ℕ (fun _ ↦ ENNReal) where
  coe := P.toFun
  coe_injective' := by rintro ⟨a, ha⟩ ⟨b, hb⟩ h; congr

variable (𝓅 : P)

@[simp] theorem P.zero_lt (α) : 0 < 𝓅 α := (𝓅.property α).left
@[simp] theorem P.lt_one (α) : 𝓅 α < 1 := (𝓅.property α).right
@[simp] theorem P.ne_zero (α) : ¬𝓅 α = 0 := (𝓅.zero_lt α).ne.symm
@[simp] theorem P.ne_one (α) : ¬𝓅 α = 1 := (𝓅.lt_one α).ne
@[simp] theorem P.le_one (α) : 𝓅 α ≤ 1 := (𝓅.lt_one α).le
@[simp] theorem P.one_sub_ne_zero (α) : ¬1 - 𝓅 α = 0 := ne_of_gt <| tsub_pos_of_lt (𝓅.lt_one α)
@[simp] theorem P.add_one_sub (α) : 𝓅 α + (1 - 𝓅 α) = 1 := add_tsub_cancel_of_le (𝓅.le_one α)
@[simp] theorem P.ne_top (α) : ¬𝓅 α = ⊤ := (𝓅.lt_one α).ne_top

@[aesop safe [constructors, cases], mk_iff]
inductive Step : State → ℕ → ENNReal → State → Prop where
| first : Step .s₁ α (𝓅 α) .s₁
| leave : Step .s₁ α (1 - 𝓅 α) .s₂
| loose : Step .s₂ 0 1 .s₃
| loop : Step .s₃ 0 1 .s₃

local notation c " ⤳[" 𝓅 "," α "," p "] " c' => Step 𝓅 c α p c'

noncomputable instance : Decidable (c ⤳[𝓅,α,p] c') := Classical.propDecidable _

@[simp] theorem s₁_iff :
    (.s₁ ⤳[𝓅,α,p] s') ↔ (s' = .s₁ ∧ p = 𝓅 α ∨ s' = .s₂ ∧ p = 1 - 𝓅 α) := by aesop
@[simp] theorem iff_s₁ : (s ⤳[𝓅,α,p] .s₁) ↔ s = .s₁ ∧ p = 𝓅 α := by aesop
@[simp] theorem s₂_iff : (.s₂ ⤳[𝓅,α,p] s') ↔ α = 0 ∧ p = 1 ∧ s' = .s₃ := by aesop
@[simp] theorem iff_s₂ : (s ⤳[𝓅,α,p] .s₂) ↔ s = .s₁ ∧ p = 1 - 𝓅 α := by aesop
@[simp] theorem s₃_iff : (.s₃ ⤳[𝓅,α,p] s') ↔ α = 0 ∧ p = 1 ∧ s' = .s₃ := by aesop

@[simp]
theorem tsum_p :
    (∑' (p : { p // c ⤳[𝓅,α,p] c' }), ↑p) = (∑' p, if c ⤳[𝓅,α,p] c' then p else 0) := by
  apply tsum_eq_tsum_of_ne_zero_bij (fun ⟨x, _⟩ ↦ ⟨x, by simp_all⟩) <;> simp_all
  exact StrictMono.injective fun _ _ a ↦ a

noncomputable def 𝒜 : MDP State ℕ := ofRelation (Step 𝓅)
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
    use 𝓅 0, 0, .s₁; simp)

@[simp] def 𝒜.cost : (𝒜 ℯ).Costs
| .s₂ => 1
| _ => 0

@[simp]
theorem 𝒜.act_eq : (𝒜 𝓅).act = fun s ↦ if s = .s₁ then Set.univ else {0} := by
  ext s α
  split_ifs
  · subst_eqs; simp [𝒜]
    aesop
  · simp [𝒜]; cases s <;> simp_all

variable {𝒮 : 𝔖[𝒜 𝓅]}

@[simp] theorem 𝒮_s₂ : 𝒮 {.s₂} = 0 := by have := 𝒮.mem_act {.s₂}; simp_all
@[simp] theorem 𝒮_s₃ : 𝒮 {.s₃} = 0 := by have := 𝒮.mem_act {.s₃}; simp_all
@[simp] theorem succs_univ_s₁ : (𝒜 𝓅).succs_univ .s₁ = {.s₁, .s₂} := by
  ext; simp_all [𝒜]
  constructor
  · simp_all
    rintro _ _ (⟨_, _⟩) <;> simp_all
  · rintro (_ | _) <;> (subst_eqs; simp_all)
@[simp] theorem succs_univ_s₂ : (𝒜 𝓅).succs_univ .s₂ = {.s₃} := by simp [𝒜]
@[simp] theorem succs_univ_s₃ : (𝒜 𝓅).succs_univ .s₃ = {.s₃} := by simp [𝒜]

def ℒ_a (a : ℕ) : 𝔏[𝒜 𝓅] := ⟨⟨
  fun π ↦ if π.last = .s₁ then a else 0,
  fun π ↦ by simp_all⟩,
  by constructor; intro π; simp⟩

@[simp] theorem default_act_s₂ : (𝒜 𝓅).default_act State.s₂ = 0 := by simp [default_act]
@[simp] theorem default_act_s₃ : (𝒜 𝓅).default_act State.s₃ = 0 := by simp [default_act]

/-- Picks the action proportional to the length of the scheduled path -/
noncomputable def 𝒮_len (a : ℕ) : 𝔖[𝒜 𝓅] := ⟨
  fun π ↦ if π.last = .s₁ then (a + ‖π‖) else (𝒜 𝓅).default_act π.last,
  fun π ↦ by
    simp_all
    set s := π.last with h
    symm at h; rcases s <;> simp_all⟩

abbrev 𝒮_s₁ {𝓅} (𝒮 : 𝔖[𝒜 𝓅]) := 𝒮 {.s₁}


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
  rw [ENNReal.tsum_eq_add_tsum_ite ⟨.s₁, by simp_all [𝒜]⟩]
  rw [ENNReal.tsum_eq_add_tsum_ite ⟨.s₂, by simp_all [𝒜]⟩]
  simp_all
  simp_all [𝒜]
  rw [ENNReal.tsum_eq_zero.mpr (by simp_all)]
  simp_all
  congr

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
  split_ifs with h <;> try simp_all
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
    = ∑' (n : ℕ), (1 - 𝓅 (i + n + 1)) * ∏ x ∈ Finset.range n, 𝓅 (i + x + 1) := by
  simp [iSup_EC_eq]

instance {State : Type*} {Act: Type*} {M : MDP State Act} : Membership State M.Path where
  mem π s := ∃ i : Fin ‖π‖, π[i] = s

noncomputable instance {State : Type*} {Act: Type*} [DecidableEq State] {M : MDP State Act}
    {π : M.Path} (s : State) : Decidable (∀ s' ∈ π, s' = s) :=
  Classical.propDecidable (∀ s' ∈ π, s' = s)

@[simp]
theorem Path.mem_extend {State : Type*} {Act: Type*} {M : MDP State Act}
    (π : M.Path) (s : M.succs_univ π.last) (s' : State) : s' ∈ π.extend s ↔ s' ∈ π ∨ s = s' := by
  simp [instMembershipPath]
  constructor
  · simp_all
    rintro ⟨i, hi⟩ h
    simp_all
    if i = ‖π.extend s‖ - 1 then
      simp_all
    else
      simp_all
      simp at hi
      rw [Path.extend_getElem_nat _ (by omega)] at h
      left
      exists ⟨i, by omega⟩
  · rintro (⟨i, hi⟩ | h)
    · use ⟨i, by simp_all; omega⟩
      simp_all
    · use ⟨‖π‖, by simp⟩
      simp_all

@[simp]
theorem Path.mem_states {State : Type*} {Act: Type*} [DecidableEq State] {M : MDP State Act}
    {π : M.Path} {a : State} : a ∈ π.states ↔ a ∈ π := by
  simp [List.mem_iff_getElem]
  simp [Membership.mem, Fin.exists_iff]


theorem Path.induction_on {State : Type*} {Act: Type*} [DecidableEq State] {M : MDP State Act}
  {P : M.Path → Prop} (π : M.Path)
  (single : P {π[0]}) (extend : ∀ π (s' : M.succs_univ π.last), P π → P (π.extend s')) :
    P π := by
  simp_all
  obtain ⟨π, nonempty, progress⟩ := π
  simp_all
  induction π using List.reverseRecOn with
  | nil => contradiction
  | append_singleton l s' ih =>
    simp_all
    if nonempty' : l = [] then
      subst_eqs
      simp_all
      exact single
    else
      simp_all
      have := extend ⟨l, by simp_all, by
          simp_all
          intro i hi
          have := progress i (by simp_all; omega)
          simp [List.getElem_append] at this
          split_ifs at this <;> try omega
          exact this⟩ s'
        (by
          simp_all
          have := progress (l.length - 1) (by simp_all [List.length_pos])
          simp [List.getElem_append] at this
          split_ifs at this <;> (try omega) <;> simp_all)
      apply this
      apply ih
      simp_all
      simp_all [List.getElem_append]
      simp_all [List.length_pos]

@[simp]
theorem Path.mem_singleton {State : Type*} {Act: Type*} [DecidableEq State] {M : MDP State Act}
    (s s' : State) : s ∈ (Path.instSingleton  (M:=M)).singleton s' ↔ s = s' := by
  simp_all [instMembershipPath]
  constructor
  · simp_all
  · intro; simp_all; exact Fin.isSome_find_iff.mp rfl

@[simp]
theorem Path.last_mem {State : Type*} {Act: Type*} [DecidableEq State] {M : MDP State Act}
    (π : M.Path) : π.last ∈ π := by
  simp_all [instMembershipPath]
  use ⟨‖π‖ - 1, by simp⟩

theorem le_of_s₁_eq_s₁ (π : (𝒜 𝓅).Path) {hi : i < ‖π‖} (h : π[i] = State.s₁) {j : ℕ} (hj : j ≤ i) :
    π[j]'(by omega) = State.s₁ := by
  induction i, hj using Nat.le_induction with
  | base => exact h
  | succ n le ih =>
    apply ih
    · have := π.property n (by simp; omega)
      simp at this
      simp_all [𝒜]
    · omega

theorem ge_of_s₁_eq_s₁ (π : (𝒜 𝓅).Path) {hi : i < ‖π‖} (h : π[i] = State.s₃) (hj : i ≤ j)
    (hj' : j < ‖π‖) : π[j]'(by omega) = State.s₃ := by
  obtain ⟨j, _, _⟩ := Nat.exists_eq_add_of_le hj
  simp_all
  induction j generalizing i with
  | zero => simp_all
  | succ j ih =>
    conv => left; arg 2; rw [← add_assoc, add_comm, ← add_assoc]
    apply ih
    · have := π.property i (by simp_all; omega)
      simp_all [add_comm]
    · omega
    · omega

theorem lt_of_s₂_eq_s₁ (π : (𝒜 𝓅).Path) {hi : i < ‖π‖} (h : π[i] = State.s₂) {j : ℕ} (hj : j < i) :
    π[j]'(by omega) = State.s₁ := by
  rcases hj with _ | hj
  · simp_all
    have := π.property j (by simp; omega)
    simp at this
    simp_all [𝒜]
  · rename_i n
    simp_all
    apply le_of_s₁_eq_s₁ (i:=j+1)
    · apply le_of_s₁_eq_s₁ (i:=n)
      · have := π.property n (by simp; omega)
        simp at this
        simp_all [𝒜]
      · simp_all
      · omega
    · simp_all

theorem gt_of_s₂_eq_s₃ (π : (𝒜 𝓅).Path) {hi : i < ‖π‖} (h : π[i] = State.s₂) {j : ℕ} (hj : i < j)
    (hj' : j < ‖π‖) : π[j]'(by omega) = State.s₃ := by
  have := π.property i (by simp_all; omega)
  simp_all
  apply ge_of_s₁_eq_s₁ 𝓅 π this hj hj'

theorem s₂_mem_of_s₁_s₃_mem (π : (𝒜 𝓅).Path) (hs₁ : .s₁ ∈ π) (hs₃ : .s₃ ∈ π) : State.s₂ ∈ π := by
  simp_all [instMembershipPath]
  obtain ⟨⟨i₁, h₁'⟩, h₁⟩ := hs₁
  obtain ⟨⟨i₃, h₃'⟩, h₃⟩ := hs₃
  have : i₁ < i₃ := by
    have := le_of_s₁_eq_s₁ 𝓅 π h₁ (j:=i₃)
    simp_all
  obtain ⟨d, _, _⟩ := Nat.exists_eq_add_of_lt this
  induction d generalizing i₁ with
  | zero =>
    have := π.property i₁
    simp_all
    omega
  | succ d ih =>
    if π[i₁ + 1] = State.s₁ then
      apply ih (i₁ + 1) <;> try omega
      · simp_all
      · rw [← h₃]
        congr! 1
        simp
        omega
    else
      have := π.property i₁ (by simp_all; omega)
      simp_all
      use ⟨i₁ + 1, by omega⟩

theorem askdjaskdkjas (π : (𝒜 𝓅).Path) :
      (∀ s ∈ π, s = .s₁)
    ∨ (∀ s ∈ π, s = .s₃)
    ∨ (∃ j : ℕ, ∀ i : Fin ‖π‖, π[i] = if i < j then .s₁ else if i = j then .s₂ else .s₃) := by
  simp_all [or_iff_not_imp_left]
  intro s₁' hs₁' hs₁'' s₃' hs₃' hs₃''
  simp_all [instMembershipPath]
  suffices .s₂ ∈ π by
    simp_all [instMembershipPath]
    obtain ⟨j, h⟩ := this
    use j
    intro i
    split_ifs with h₁ h₂
    · simp_all
      exact lt_of_s₂_eq_s₁ 𝓅 π h h₁
    · simp_all
    · simp_all
      apply gt_of_s₂_eq_s₃ 𝓅 π h <;> omega
  simp [instMembershipPath]
  obtain ⟨i₃, h₃⟩ := hs₁'
  obtain ⟨i₁, h₁⟩ := hs₃'
  rcases s₁' <;> simp_all
  · use i₃
  · rcases s₃' <;> simp_all
    · obtain ⟨i₁, h₁'⟩ := i₁
      obtain ⟨i₃, h₃'⟩ := i₃
      simp_all
      exact s₂_mem_of_s₁_s₃_mem 𝓅 π ⟨⟨i₁, h₁'⟩, h₁⟩ ⟨⟨i₃, h₃'⟩, h₃⟩
    · use i₁

theorem Cost_one_of_s₂_mem (hs₂ : .s₂ ∈ π) : Path.Cost 𝒜.cost π = 1 := by
  rename_i 𝓅
  obtain ⟨⟨i, hi⟩, hi'⟩ := hs₂
  simp_all
  induction π using Path.induction_on with
  | single => simp_all [Path.Cost, Path.instSingleton]
  | extend π s' ih =>
    obtain ⟨s', hs'⟩ := s'
    simp_all [Path.extend_Cost]
    rcases i with _ | i
    · simp_all [𝒜]
      simp_all [𝒜]
      simp_all [𝒜]
      if ‖π‖ = 1 then
        simp_all
      else
        have : π.last = .s₃ := by
          rw [Path.last]
          apply gt_of_s₂_eq_s₃ (i:=0) _ π  hi' <;> simp_all
        simp_all
        obtain ⟨α, p, h⟩ := hs'
        have : .s₃ ⤳[𝓅,α,p] s' := by convert h; exact this.symm
        simp_all
    · rw [π.extend_getElem_succ (i := ⟨i, by simp at hi; omega⟩)] at hi'
      simp_all
      split_ifs at hi'
      · subst_eqs
        simp_all [𝒜]
        simp_all [𝒜]
        have : Path.Cost 𝒜.cost π = 0 := by
          simp [Path.Cost]
          refine List.sum_eq_zero ?_
          simp_all [instMembershipPath]
          intro ⟨i, hi⟩
          simp_all
          have : π[i] = .s₁ := by
            apply le_of_s₁_eq_s₁ (i:=‖π‖ - 1) _ π
            · exact hs'
            · omega
          simp_all
        simp_all
      · simp_all
        simp_all [𝒜]
        have := ih (by simp at hi; omega)
        simp_all
        split <;> try simp_all
        simp [𝒜] at hs'
        have : i + 1 < ‖π‖ := by simp at hi; omega
        if i + 1 < ‖π‖ - 1 then
          have := gt_of_s₂_eq_s₃ 𝓅 π (i:=i + 1) (j:=‖π‖ - 1) (hi:=this) hi'
          simp_all
          have : State.s₁ = State.s₃ := by
            rw [← hs', ← this]
            rfl
          simp at this
        else
          simp_all
          have : i = ‖π‖ - 2 := by omega
          subst_eqs
          have : ‖π‖ - 2 + 1 = ‖π‖ - 1 := by omega
          simp_all

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
    split_ifs with h
    · simp_all [Path.ECost, Path.Cost]
      left
      refine List.sum_eq_zero ?_
      simp_all
    · simp_all [Path.ECost]
      suffices π.Cost 𝒜.cost = 1 by simp_all
      apply Cost_one_of_s₂_mem
      obtain ⟨s, hs, hs'⟩ := h
      cases s <;> simp_all
      apply s₂_mem_of_s₁_s₃_mem _ _ _ hs
      exact ⟨⟨0, by simp⟩, hπ.right⟩

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

@[simp]
theorem 𝒮_x_ℒ (ℒ : 𝔏[𝒜 𝓅]) : 𝒮_x 𝓅 ℒ i = ℒ := by
  induction i generalizing ℒ with
  | zero => rfl
  | succ i ih =>
    rw [𝒮_x]
    rw [ih]
    ext π
    simp_all
    intro h
    set s := π.last with h'
    symm at h'
    have := ℒ.toScheduler.mem_act π
    rcases s <;> simp_all
    contrapose h
    simp_all
    apply le_of_s₁_eq_s₁ 𝓅 π (i:=‖π‖ - 1) <;> simp_all

theorem iSup_ECℒ (ℒ : 𝔏[𝒜 𝓅]) :
    ⨆ n, (𝒜 𝓅).EC 𝒜.cost ℒ n .s₁ = 1
:= by simp [iSup_EC_eq, ENNReal.tsum_mul_left, ENNReal.mul_inv_cancel]

theorem iSup_iSup_ECℒ : ⨆ ℒ : 𝔏[𝒜 𝓅], ⨆ n, (𝒜 𝓅).EC 𝒜.cost ℒ n .s₁ = 1 := by
  simp_all [iSup_ECℒ]

theorem iInf_iSup_ECℒ : ⨅ ℒ : 𝔏[𝒜 𝓅], ⨆ n, (𝒜 𝓅).EC 𝒜.cost ℒ n .s₁ = 1 := by
  simp_all [iSup_ECℒ]

noncomputable def p : P := ⟨fun n ↦
  (2 ^ (2 ^ n : ℝ)⁻¹)⁻¹, by
  simp
  intro n
  refine ENNReal.one_lt_rpow ?_ ?_ <;> simp⟩

theorem iInf_iSup_EC_ab :
    ⨅ 𝒮, ⨆ n, (𝒜 p).EC 𝒜.cost 𝒮 n .s₁ ≤ ⨆ n, (1 - ∏ x : Fin (n - 1), p (↑x + 1)) := by
  apply iInf_le_of_le (𝒮_len p 0)
  simp_all
  intro n
  apply le_iSup_of_le n
  simp only [EC_𝒮_len', AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, ↓reduceIte]
  simp [asdjhsad (𝓅:=p) (i:=0)]
  split_ifs <;> simp_all

theorem prod_p_eq' : ∏ x : Fin n, p (↑x + 1) = 2^((2 : ℝ)^((-(n : ℝ))) - 1) := by
  simp [p, DFunLike.coe]
  induction n with
  | zero => simp [← ENNReal.rpow_neg]
  | succ n ih =>
    rw [@Fin.prod_univ_castSucc]
    simp [ih]; clear ih
    ring_nf
    simp [ENNReal.rpow_add]
    rw [mul_assoc]
    congr! 1
    rw [← ENNReal.rpow_neg]
    simp [← ENNReal.rpow_add]
    congr! 1
    ring_nf
    simp_all
    rw [@mul_div_left_comm]
    simp_all [@neg_inv]
    rw [@add_neg_eq_iff_eq_add]
    have : ((2 : ℝ) ^ (n : ℝ))⁻¹ = 2^(-n:ℝ) := by
      simp
      rw [← Real.rpow_neg_one]
      have := Real.rpow_mul (x:=2) (y:=n) (z:=-1)
      simp_all
    simp at this; simp [this]; clear this
    ring_nf
    simp [← Real.rpow_neg_one]
    rw [← Real.rpow_add (by simp)]
    ring_nf
    have := Real.rpow_add (x:=2) (by simp) (-1 - n:ℝ) 1
    simp at this; simp [← this]
    ring_nf

theorem iInf_iSup_EC_lt_iInf_iSup_ECℒ :
    ⨅ 𝒮, ⨆ n, (𝒜 p).EC 𝒜.cost 𝒮 n .s₁ < ⨅ ℒ : 𝔏[𝒜 p], ⨆ n, (𝒜 p).EC 𝒜.cost ℒ n .s₁ := by
  simp [iInf_iSup_ECℒ]
  apply (iInf_iSup_EC_ab).trans_lt
  refine iSup_lt_iff.mpr ?_
  use 1/2
  simp_all
  · intro n
    rcases n with _ | n
    · simp
    · simp
      simp [prod_p_eq']
      ring_nf
      have : (2 : ENNReal)⁻¹ = 1 - 2⁻¹ := by rw [ENNReal.one_sub_inv_two]
      rw [this]; clear this
      rw [ENNReal.sub_add_eq_add_sub] <;> simp
      apply ENNReal.le_sub_of_add_le_left (by simp)
      rw [add_comm]
      gcongr
      have : (2 : ENNReal)⁻¹ = 2^(-1:ℝ) := by rw [ENNReal.rpow_neg_one]
      rw [this]
      gcongr
      · simp
      · simp_all
        apply Real.rpow_nonneg
        simp

end MDP.Counterexample.C
