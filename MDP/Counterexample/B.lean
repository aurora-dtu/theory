import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import MDP.OptimalCost
import MDP.Relational

noncomputable def ENNReal.sqrt (x : ENNReal) : ENNReal := x^((1 : ℝ)/(2 : ℝ))

namespace MDP.Counterexample.B

/-!
# Counterexample exhibiting `⨆ n, ⨅ 𝒮, EC c 𝒮 n < ⨅ 𝒮, ⨆ n, EC c 𝒮 n`

```
         1,p
    s₀---------s₁
    |          |
 1,p|          |2,p
    |    2,p   |
    s₂---------s₃
```

**Setup**: ([instance](#MDP.Counterexample.B.M))
- The MDP consists of states `s₀` .. with actions `1` and ...
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

Additionally we can show the same for `MDP.lfp_Φ` giving us `iSup_iInf_EC_lt_lfp_Φ`.

-/


noncomputable abbrev w : ENNReal := 2⁻¹

@[simp] theorem w_zero_lt : 0 < w := by simp
@[simp] theorem w_lt_one : w < 1 := by simp
@[simp] theorem w_ne_zero : ¬w = 0 := by simp
@[simp] theorem w_ne_one : ¬w = 1 := by simp
@[simp] theorem w_le_one : w ≤ 1 := by simp
@[simp] theorem w_one_minus : 1 - w = w := by simp
@[simp] theorem w_one_sub_ne_zero : ¬1 - w = 0 := by simp
@[simp] theorem w_add_self : w + w = 1 := ENNReal.inv_two_add_inv_two
@[simp] theorem w_add_one_sub : w + (1 - w) = 1 := by simp
@[simp] theorem w_ne_top : ¬w = ⊤ := by simp

inductive State where
  | s0 | sA | sB | sAB
deriving DecidableEq

inductive Act where | A | B
deriving DecidableEq

@[aesop safe [constructors, cases], mk_iff]
inductive Step : State → Act → ENNReal → State → Prop where
-- s0
| s0_A  : Step .s0 .A w .sA
| s0_A' : Step .s0 .A w .s0
| s0_B  : Step .s0 .B w .sB
| s0_B' : Step .s0 .B w .s0
-- sA
| sA_A  : Step .sA .A 1 .sA
| sA_B  : Step .sA .B w .sAB
| sA_B' : Step .sA .B w .sA
-- sB
| sB_A  : Step .sB .A w .sB
| sB_A' : Step .sB .A w .sAB
| sB_B  : Step .sB .B 1 .sB
-- sAB
| sAB_A : Step .sAB .A 1 .sAB
| sAB_B : Step .sAB .B 1 .sAB

local notation c " ⤳[" α "," p "] " c' => Step c α p c'

noncomputable instance : Decidable (c ⤳[α,p] c') := Classical.propDecidable _

@[simp] theorem s0_iff : (.s0 ⤳[α,p] s') ↔
    p = w ∧ ((α = .A ∧ (s' = .s0 ∨ s' = .sA)) ∨ (α = .B ∧ (s' = .s0 ∨ s' = .sB))) := by aesop
@[simp] theorem sA_iff : (.sA ⤳[α,p] s') ↔
    (α = .A ∧ p = 1 ∧ s' = .sA) ∨ (α = .B ∧ p = w ∧ (s' = .sA ∨ s' = .sAB)) := by aesop
@[simp] theorem sB_iff : (.sB ⤳[α,p] s') ↔
    (α = .B ∧ p = 1 ∧ s' = .sB) ∨ (α = .A ∧ p = w ∧ (s' = .sB ∨ s' = .sAB)) := by aesop
@[simp] theorem sAB_iff : (.sAB ⤳[α,p] s') ↔
    (p = 1 ∧ s' = .sAB) := by rcases α <;> aesop

@[simp]
theorem tsum_p :
    (∑' (p : { p // c ⤳[α,p] c' }), ↑p) = (∑' p, if c ⤳[α,p] c' then p else 0) := by
  apply tsum_eq_tsum_of_ne_zero_bij (fun ⟨x, _⟩ ↦ ⟨x, by simp_all⟩) <;> simp_all
  exact StrictMono.injective fun _ _ a ↦ a

@[simp] theorem exists_p_Act_eq_1 : ∃ (p : ENNReal) (_ : Act), p = 1 := ⟨1, .A, by simp⟩

open ENNReal in
noncomputable def M : MDP State Act := ofRelation Step
  (by rintro s α p s' (_ | _) <;> simp_all)
  (by
    intro s α p₀ c₀ h
    cases h <;> simp_all [ite_and]
    · rw [tsum_eq_add_tsum_ite .sA, tsum_eq_add_tsum_ite .s0]; simp_all
    · rw [tsum_eq_add_tsum_ite .sA, tsum_eq_add_tsum_ite .s0]; simp_all
    · rw [tsum_eq_add_tsum_ite .sB, tsum_eq_add_tsum_ite .s0]; simp_all
    · rw [tsum_eq_add_tsum_ite .sB, tsum_eq_add_tsum_ite .s0]; simp_all
    · rw [tsum_eq_add_tsum_ite .sA, tsum_eq_add_tsum_ite .sAB]; simp_all
    · rw [tsum_eq_add_tsum_ite .sA, tsum_eq_add_tsum_ite .sAB]; simp_all
    · rw [tsum_eq_add_tsum_ite .sB, tsum_eq_add_tsum_ite .sAB]; simp_all
    · rw [tsum_eq_add_tsum_ite .sB, tsum_eq_add_tsum_ite .sAB]; simp_all)
  (by rintro ⟨_⟩ <;> aesop)

@[simp] def M.cost : M.Costs
| .sAB => 0
| _ => 1

@[simp] theorem Act.complete : α = Act.A ∨ α = Act.B := by rcases α <;> simp

@[simp] theorem M.act_s0 : M.act .s0 = Set.univ := by ext α; simp [M]; use .s0; simp
@[simp] theorem M.act_sA : M.act .sA = Set.univ := by ext α; rcases α <;> simp [M]
@[simp] theorem M.act_sB : M.act .sB = Set.univ := by ext α; rcases α <;> simp [M]
@[simp] theorem M.act_sAB : M.act .sAB = Set.univ := by simp [M]

@[simp] theorem M.A_mem_act : .A ∈ M.act s := by rcases s <;> simp
@[simp] theorem M.B_mem_act : .B ∈ M.act s := by rcases s <;> simp

@[simp]
theorem M.act_eq : M.act = fun _ ↦ Set.univ := by ext s α; rcases α <;> aesop

instance : Inhabited Act := ⟨.A⟩

@[simp] theorem M.succs_univ_s0 : M.succs_univ .s0 = {.s0, .sA, .sB} := by ext; simp [M]; aesop
@[simp] theorem M.succs_univ_sA : M.succs_univ .sA = {.sA, .sAB} := by ext; simp [M]; aesop
@[simp] theorem M.succs_univ_sB : M.succs_univ .sB = {.sB, .sAB} := by ext; simp [M]; aesop
@[simp] theorem M.succs_univ_sAB : M.succs_univ .sAB = {.sAB} := by ext; simp [M]

instance : Fintype Act where
  elems := {.A, .B}
  complete := by simp
instance : Fintype State where
  elems := {.s0, .sA, .sB, .sAB}
  complete := by rintro ⟨_⟩ <;> simp

instance : M.FiniteBranching where
  act_fin s := Set.toFinite (M.act s)
  succs_fin a s := Set.toFinite (M.succs s a)

abbrev 𝒮A : M.Scheduler := ⟨fun π ↦ if Even ‖π‖ then .A else .B, by simp⟩
abbrev 𝒮B : M.Scheduler := ⟨fun π ↦ if Even ‖π‖ then .B else .A, by simp⟩

noncomputable abbrev 𝒮A' (s' : State) : M.Scheduler :=
  ⟨fun π ↦ if π[0] = s' then 𝒮A π else M.default_act π.last, by simp⟩
noncomputable abbrev 𝒮B' (s' : State) : M.Scheduler :=
  ⟨fun π ↦ if π[0] = s' then 𝒮B π else M.default_act π.last, by simp⟩

@[simp] theorem 𝒮A_specialized :
    𝒮A[s ↦ s'] = 𝒮B' s' := by
  ext π
  simp_all
  split_ifs with h₁ h₂
  · contrapose h₂
    simp_all
  · simp_all
  · simp_all
  · contrapose h₂
    simp_all
  · simp
@[simp] theorem 𝒮B_specialized :
    𝒮B[s ↦ s'] = 𝒮A' s' := by
  ext π
  simp_all
  split_ifs with h₁ h₂
  · contrapose h₂
    simp_all
  · simp_all
  · simp_all
  · contrapose h₂
    simp_all
  · simp

variable {𝒮 : 𝔖[M]}

@[simp] theorem EC_sAB : M.EC M.cost 𝒮 n .sAB = 0 := by
  induction n generalizing 𝒮 with
  | zero => simp
  | succ n ih =>
    simp [EC_succ, eq_comm]
    rw [tsum_eq_single ⟨.sAB, by simp⟩ (by simp_all)]
    simp_all

@[simp] theorem EC_𝒮A' : EC M.cost (𝒮A' s') n s' = EC M.cost 𝒮A n s' := by apply EC_eq (by simp_all)
@[simp] theorem EC_𝒮B' : EC M.cost (𝒮B' s') n s' = EC M.cost 𝒮B n s' := by apply EC_eq (by simp_all)

noncomputable instance : Decidable (s' ∈ M.succs_univ s) := (M.succs_univ s).decidableMemOfFintype _

open ENNReal in
theorem tsum_succs_univ_split (f : M.succs_univ s → ENNReal) :
      ∑' (s' : M.succs_univ s), M.P s α s' * (f s')
    =
      M.P s α .s0 * (if h : State.s0 ∈ M.succs_univ s then f ⟨.s0, h⟩ else 0) +
      M.P s α .sA * (if h : State.sA ∈ M.succs_univ s then f ⟨.sA, h⟩ else 0) +
      M.P s α .sB * (if h : State.sB ∈ M.succs_univ s then f ⟨.sB, h⟩ else 0) +
      M.P s α .sAB * (if h : State.sAB ∈ M.succs_univ s then f ⟨.sAB, h⟩ else 0)
:= by
  rw [← tsum_eq_tsum_of_ne_zero_bij (β:=State)
    (f:=fun s' ↦ M.P s α s' * (if h : s' ∈ M.succs_univ s then f ⟨s', h⟩ else 0))
    (fun ⟨s, _⟩ ↦ s)]
  · rw [tsum_eq_add_tsum_ite .s0, tsum_eq_add_tsum_ite .sA, tsum_eq_add_tsum_ite .sB,
      tsum_eq_add_tsum_ite .sAB]
    rcases α <;> rcases s <;> simp_all [M]
  · intro ⟨x, _⟩ ⟨y, _⟩ h; simp_all; exact SetCoe.ext h
  · intro y h; simp_all [M]; aesop
  · simp

-- EC M.cost 𝒮A (n + 2) State.sA = 1 + w * (1 + EC M.cost 𝒮A n State.sA)
-- f(n + 2) = 1 + w * (1 + f(n))
-- f(0) = 0, f(1) = 1, f(n + 2) = 1 + 1/2 + f(n)/2
-- f(n) = 3 + 2^(-1 - n/2) * (-3 - 2 * sqrt(2) + (-1)^n * (-3 + 2 * sqrt(2)))
-- f(n) = 3 + 2⁻¹^(1 + n/2) * (-3 - 2 * sqrt(2) + (-1)^n * (-3 + 2 * sqrt(2)))
noncomputable def EC_sA_𝒮A (n : ℕ) : ENNReal :=
  3 + 1/(2^(1 + (n : ℝ)/2)) * (-3 - 2 * (.sqrt 2) + (-1)^n * (-3 + 2 * (.sqrt 2)))

-- 1 + w * (1 + w * (1 + w * (1 + ...)))
-- 1 + w + w * w * (1 + w * (1 + ...)))
-- 1 + w + w * w + w * w * w * (1 + ...)))
-- ∑ i : Finset.range n, w^i
theorem EC_sA_one : M.EC M.cost 𝒮A 1 .sA = 1 := by simp
theorem EC_sA : M.EC M.cost 𝒮A n .sA = if n = 0 then 0 else ∑ i ∈ Finset.range (n/2 + 1), w^i := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih ih' =>
    clear ih'
    simp_all [EC_succ]
    simp [tsum_succs_univ_split]
    simp +contextual [M]
    rw [ih]; clear ih
    rcases n with _ | n
    · simp; ring
    · simp
      simp [mul_add, ← add_assoc]
      simp [Finset.mul_sum]
      calc 1 + w + ∑ i ∈ Finset.range (n + 1), w * w ^ i
        _ = 1 + w + ∑ i ∈ Finset.range (n + 1), w ^ (i + 1) := by simp [npow_add, mul_comm]
        _ = w + (∑ i ∈ Finset.range (n + 1), w ^ (i + 1) + 1^1) := by ring
        _ = w + ∑ i ∈ Finset.range (n + 2), w ^ i := by simp [Finset.sum_range_succ']

      have : ∀ i, w * w ^ i = w ^ (i + 1) := by simp [npow_add, mul_comm]
      simp [this]; clear this

      rw [Finset.sum_range_succ']
      simp [w]
      simp [Finset.sum_range]
      simp_all


      ring_nf

    simp_all

    ring_nf
    rw [tsum_succs_univ_split (s:=.sA)]
    sorry

-- g(0) = 0, g(1) = 1, g(n+2) = 2 + g(n)/2
-- g(n) = 4 + 2^(-1 - n/2) (-4 - 3 sqrt(2) + (-1)^n (-4 + 3 sqrt(2)))
theorem EC_sB : M.EC M.cost 𝒮A n .sB = if n = 0 then 0 else ∑ i ∈ Finset.range (n/2 + 1), w^i := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih ih' =>
    clear ih'
    simp_all [EC_succ]
    simp [tsum_succs_univ_split]
    simp +contextual [M]

-- f(n) = 3 + 2^(-1 - n/2) (-3 - 2 sqrt(2) + (-1)^n (-3 + 2 sqrt(2)))
-- g(n) = 4 + 2^(-1 - n/2) (-4 - 3 sqrt(2) + (-1)^n (-4 + 3 sqrt(2)))
-- h(0) = 0
-- h(1) = 1
-- h(n+2) = 1 + (w * (1 + (w * h(n) + w * f(n))) + w * (1 + w * g(n)))

-- f(n) = 3 + 2^(-1 - n/2) (-3 - 2 sqrt(2) + (-1)^n (-3 + 2 sqrt(2)))
-- g(n) = 4 + 2^(-1 - n/2) (-4 - 3 sqrt(2) + (-1)^n (-4 + 3 sqrt(2)))
-- h(0) = 0
-- h(1) = 1
-- h(n+2) = 1 + (w * (1 + (w * h(n) + w * f(n))) + w * (1 + w * g(n)))
-- h(n+2) = 2 + 2^-2 * h(n) + 2^-2 * f(n) + 2^-2 * g(n)
-- h(n+2) = 2 + (f(n) + g(n) + h(n))/2

attribute [-simp] one_div in
theorem asdasd (f g h : ℕ → ENNReal) : 1 + (w * (1 + (w * (h n) + w * (f n))) + w * (1 + w * (g n))) = 12 := by
  ring_nf
  simp [w, inv_eq_one_div]
  simp?
  -- have : ∀ x : ENNReal, x⁻¹ = 1/x := by exact fun x ↦ inv_eq_one_div x
  simp [ENNReal.inv]
  simp

theorem EC_s0_one : M.EC M.cost 𝒮A 1 .s0 = 1 := by simp
theorem EC_s0 : M.EC M.cost 𝒮A n .s0 = if n = 0 then 0 else 12 := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => sorry
  | more n ih ih' =>
    clear ih'
    simp_all [EC_succ]
    simp [tsum_succs_univ_split]
    simp +contextual [M]
    ring_nf

    sorry

end MDP.Counterexample.B
