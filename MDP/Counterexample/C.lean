import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import MDP.OptimalCost
import MDP.Paths.Membership
import MDP.Relational
import MDP.SupSup

namespace List

variable {α : Type*}

theorem take_append_cons_drop {l : List α} {s : α} {i : ℕ} (hi : i < l.length) (h : l[i] = s) :
    l.take i ++ s :: l.drop (i + 1) = l := by
  apply ext_getElem
  · simp_all [inf_of_le_left hi.le]; omega
  · simp_all [inf_of_le_left hi.le, getElem_append, getElem_cons]
    intro j hj hj'
    split_ifs
    · rfl
    · simp_all [(by omega : i = j)]
    · congr; omega

end List

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
    · rw [ENNReal.tsum_eq_add_tsum_ite .s₁]; simp_all [ite_and]
      rw [ENNReal.tsum_eq_add_tsum_ite .s₂]; simp_all
    · rw [ENNReal.tsum_eq_add_tsum_ite .s₁]; simp_all [ite_and]
      rw [ENNReal.tsum_eq_add_tsum_ite .s₂]; simp_all)
  (by rintro (_ | ⟨i, j⟩) <;> simp_all; use 𝓅 0, 0, .s₁; simp)

@[simp] def 𝒜.cost : (𝒜 ℯ).Costs | .s₂ => 1 | _ => 0

@[simp] theorem 𝒜.act_eq : (𝒜 𝓅).act = fun s ↦ if s = .s₁ then Set.univ else {0} := by
  ext s; cases s <;> simp_all [𝒜]; aesop

variable {𝒮 : 𝔖[𝒜 𝓅]}

@[simp] theorem 𝒮_s₂ : 𝒮 {.s₂} = 0 := by have := 𝒮.mem_act {.s₂}; simp_all
@[simp] theorem 𝒮_s₃ : 𝒮 {.s₃} = 0 := by have := 𝒮.mem_act {.s₃}; simp_all
@[simp] theorem succs_univ_s₁ : (𝒜 𝓅).succs_univ .s₁ = {.s₁, .s₂} := by
  ext; simp_all [𝒜]
  constructor
  · simp_all; rintro _ _ (⟨_, _⟩) <;> simp_all
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
  simp [EC_succ]
  rw [ENNReal.tsum_eq_add_tsum_ite ⟨.s₁, by simp⟩, ENNReal.tsum_eq_add_tsum_ite ⟨.s₂, by simp⟩]
  simp_all [𝒜, ENNReal.tsum_eq_zero.mpr]
  rfl

theorem EC_succ_s₁ :
    (𝒜 𝓅).EC 𝒜.cost 𝒮 (n + 1) .s₁
  = 𝓅 (𝒮_s₁ 𝒮) * (𝒜 𝓅).EC 𝒜.cost 𝒮[.s₁ ↦ .s₁]'(by simp) n .s₁ + if n = 0 then 0 else 1 - 𝓅 (𝒮_s₁ 𝒮)
:= by simp [EC_succ_s₁']

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

theorem specialize_eq_𝒮_x : 𝒮[.s₁ ↦ .s₁]'(by simp) = 𝒮_x 𝓅 𝒮 1 := by rfl

theorem iSup_EC_succ_eq_iSup_EC :
    ⨆ n, (𝒜 𝓅).EC 𝒜.cost 𝒮 (n + 1) .s₁ = ⨆ n, (𝒜 𝓅).EC 𝒜.cost 𝒮 n .s₁ :=
  (iSup_le fun n ↦ le_iSup_of_le (n + 1) (by rfl)).antisymm (iSup_le (le_iSup_of_le · EC_le_succ))

theorem iSup_EC_eq :
      ⨆ n, (𝒜 𝓅).EC 𝒜.cost 𝒮 n .s₁
    = ∑' n, (1 - 𝓅 (𝒮_s₁ (𝒮_x 𝓅 𝒮 n))) * ∏ i ∈ Finset.range n, 𝓅 (𝒮_s₁ (𝒮_x 𝓅 𝒮 i)) := by
  simp [← iSup_EC_succ_eq_iSup_EC, ENNReal.tsum_eq_iSup_nat]
  congr with n
  induction n generalizing 𝒮 with
  | zero => simp
  | succ n ih =>
    rw [EC_succ_s₁, ih]; clear ih
    simp [Finset.sum_range_succ', Finset.prod_range_succ', ← mul_assoc, ← Finset.sum_mul]
    simp [specialize_eq_𝒮_x, 𝒮_x_add, add_comm, mul_comm]

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
  simp_all [Path.mem_iff_getElem]
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
      · rw [← h₃]; congr! 1; simp; omega
    else
      have := π.property i₁ (by simp_all; omega)
      simp_all
      use ⟨i₁ + 1, by omega⟩

theorem Cost_one_of_s₂_mem (hs₂ : .s₂ ∈ π) : Path.Cost 𝒜.cost π = 1 := by
  rename_i 𝓅
  obtain ⟨⟨i, hi⟩, hi'⟩ := hs₂
  obtain ⟨states, nonempty, progress⟩ := π
  simp at hi
  have := List.take_append_cons_drop hi hi'
  simp [Path.Cost]
  rw [← this]
  simp
  rw [← add_comm, add_assoc]
  have : ∀ x : ENNReal, x = 0 → 1 + x = 1 := by rintro x ⟨_⟩; simp
  apply this; clear this
  simp
  constructor <;> apply List.sum_eq_zero
  · simp_all [List.mem_drop_iff_getElem]
    intro s j hs hs'
    split at hs'
    · suffices states[i + 1 + j] = .s₃ by simp_all
      apply gt_of_s₂_eq_s₃ 𝓅 ⟨states, nonempty, progress⟩ hi' (by omega) (by simp; omega)
    · simp_all
  · simp_all [List.mem_take_iff_getElem]
    intro s j hs hs'
    split at hs'
    · suffices states[j] = .s₁ by simp_all
      apply lt_of_s₂_eq_s₁ 𝓅 ⟨states, nonempty, progress⟩ hi'; simp_all
    · simp_all

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

theorem tsum_paths_eq_ite_tprod :
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
  simp [tsum_paths_eq_ite_tprod]
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
  apply iInf_iSup_EC_ab.trans_lt
  refine iSup_lt_iff.mpr ?_
  use 1/2
  simp_all
  · rintro (_ | n)
    · simp
    simp [prod_p_eq']
    ring_nf
    rw [← ENNReal.one_sub_inv_two, ENNReal.sub_add_eq_add_sub (by simp) (by simp)]
    apply ENNReal.le_sub_of_add_le_left (by simp)
    rw [add_comm]
    gcongr
    rw [← ENNReal.rpow_neg_one]
    gcongr <;> simp_all [Real.rpow_nonneg zero_le_two]

end MDP.Counterexample.C
