import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!

# Markov Decision Process (MDP)

MDP's are probabilistic transition systems consisting of sets of (possibly infinite) states and
actions, equipped with a probability function.

## Main definitions

* `MDP State Act`: Markov Decision Process.
* `MDP.P`: probability function relating states and actions to states.
* `MDP.act`: enabled actions of a state.
* `MDP.succs`, `MDP.succs_univ`: successors of states.
* `MDP.prev`, `MDP.prev_univ`: predecessors of states.
* `MDP.FiniteBranching`: MDP's where both `MDP.succs` and `MDP.act` are finite.

-/

structure MDP (State : Type*) (Act : Type*) where
  /-- The transition probability of going from `s` to `s'` using action `α` -/
  P : State → Act → Option (PMF State)
  exists_P_isSome s : ∃α, (P s α).isSome

namespace MDP

variable {State : Type*} {Act : Type*}

variable (M : MDP State Act)

instance : FunLike (Option (PMF State)) State ENNReal where
  coe pmf' x := if let some pmf := pmf' then pmf x else 0
  coe_injective' := by
    rintro (_ | a) (_ | b) h <;> simp_all
    · exact Ne.elim ‹PMF _›.coe_ne_zero.symm h
    · exact Ne.elim ‹PMF _›.coe_ne_zero h

theorem P_apply_eq : M.P s a s' = if let some pmf := M.P s a then pmf s' else 0 := rfl

@[simp, grind =]
theorem P_get : (M.P s a).get h s' = M.P s a s' := by
  simp [P_apply_eq]
  split <;> simp_all [← Option.eq_none_iff_forall_ne_some]
  grind

/-- An action is enabled in state `s` iff choosing this action gives a positive probability to any
other state. -/
def act (s : State) : Set Act := {a | (M.P s a).isSome}
/-- α-successors of `s` are states `s'` which have a positive probability for a given action `α`,
such that `0 < M.P s α s'`. -/
def succs (α : Act) (s : State) : Set State := {s' | M.P s α s' ≠ 0}
/-- α-predecessors of `s` are states `s'` such that `s' ∈ M.succs α s`. -/
def prev (α : Act) (s' : State) : Set State := {s | s' ∈ M.succs α s}

/-- Successors of `s` are those `s'` with `s' ∈ M.succs α` for some `α`. -/
def succs_univ (s : State) : Set State := ⋃ α, M.succs α s
/-- Predecessors of `s` are those `s'` with `s' ∈ M.prev α` for some `α`. -/
def prev_univ (s : State) : Set State := ⋃ α, M.prev α s
def mem_prev_univ_iff_mem_succs_univ (s s' : State) : s ∈ M.prev_univ s' ↔ s' ∈ M.succs_univ s := by
  simp_all [prev_univ, succs_univ, prev]

theorem P_eq_some_iff : M.P s α = some pmf ↔ DFunLike.coe (M.P s α) = pmf := DFunLike.ext'_iff
theorem P_isSome_iff :
      (M.P s α).isSome
    ↔ ∃ (s' : State) (pmf : PMF State), ¬pmf s' = 0 ∧ DFunLike.coe (M.P s α) = pmf := by
  simp [Option.isSome_iff_exists, P_eq_some_iff, funext_iff]
  constructor
  · simp only [forall_exists_index]
    intro pmf h
    obtain ⟨s', hs'⟩ := pmf.support_nonempty
    use s', pmf, hs'
  · simp only [forall_exists_index, and_imp]
    intro s pmf h h'
    use pmf

class FiniteBranching where
  act_fin : ∀ (s : State), (M.act s).Finite
  succs_fin : ∀ (s : State) (α : Act), (M.succs α s).Finite

noncomputable def ofP (P : State → Act → State → ENNReal)
    (h₁ : ∀ s α, ∑' s', P s α s' = 0 ∨ ∑' s', P s α s' = 1)
    (h₂ : ∀ s, ∃ α s', 0 < P s α s') : MDP State Act where
  P s α :=
    have : Decidable (α ∈ (P s).support) := Classical.propDecidable _
    if h : α ∈ (P s).support then some ⟨P s α, by
      apply (Summable.hasSum_iff ENNReal.summable).mpr
      rcases h₁ s α with h₁ | _
      · simp_all
        apply h
        exact (Set.eqOn_univ (P s α) 0).mp fun ⦃x⦄ a ↦ h₁ x
      · simp_all⟩
    else none
  exists_P_isSome := by
    intro s
    obtain ⟨α, s', hα⟩ := h₂ s
    use α
    simp_all
    intro p
    simp_all only [Pi.zero_apply, lt_self_iff_false]

@[simp]
theorem ofP_P (P : State → Act → State → ENNReal) (h₁) (h₂) :
    (ofP P h₁ h₂).P s α s' = P s α s' := by
  simp [ofP, DFunLike.coe]
  split_ifs <;> simp_all

@[simp] lemma P_le_one (s : State) (α : Act) (s' : State) : M.P s α s' ≤ 1 := by
  simp [P_apply_eq]
  split
  · apply PMF.coe_le_one
  · simp only [zero_le]

@[simp] lemma P_ne_top (s : State) (α : Act) (s' : State) : M.P s α s' ≠ ⊤ :=
  M.P_le_one s α s' |>.trans_lt ENNReal.one_lt_top |>.ne

instance [Fintype Act] : Finite (M.act s) := Subtype.finite
noncomputable instance instFintypeAct [Fintype Act] : Fintype (M.act s) := Fintype.ofFinite _
noncomputable instance instNonemptyAct : Nonempty (M.act s) :=
  have ⟨α, hα⟩ := M.exists_P_isSome s
  ⟨α, Set.mem_of_subset_of_mem (fun _ a ↦ a) hα⟩

noncomputable def default_act (s : State) : Act :=
  (nonempty_subtype.mp <| M.instNonemptyAct (s:=s)).choose
@[simp]
theorem default_act_spec (s : State) : M.default_act s ∈ M.act s :=
  (nonempty_subtype.mp <| M.instNonemptyAct (s:=s)).choose_spec

instance [i : M.FiniteBranching] : Finite (M.act s) := i.act_fin s
noncomputable instance [M.FiniteBranching] : Fintype (M.act s) := Fintype.ofFinite (M.act s)
theorem actFinite [i : M.FiniteBranching] : (M.act s).Finite := i.act_fin s

noncomputable def act₀ [M.FiniteBranching] (s : State) : Finset Act := (M.act s).toFinset

@[simp]
theorem act₀_eq_act [i : M.FiniteBranching] : M.act₀ s = M.act s := by simp [act₀]

@[simp]
theorem act₀_mem_iff_act_mem [M.FiniteBranching] : a ∈ M.act₀ s ↔ a ∈ M.act s := by
  simp only [← act₀_eq_act, Finset.mem_coe]
theorem act₀_prop [FiniteBranching M] (h : a ∈ M.act₀ s) : (M.succs a s).Nonempty := by
  simp_all [act₀_mem_iff_act_mem, act, succs, Option.isSome_iff_exists]
  obtain ⟨pmf, h⟩ := h
  rw [h]
  exact pmf.support_nonempty

noncomputable instance [M.FiniteBranching] : Nonempty (M.act₀ s) := by
  simp_all [M.instNonemptyAct]

noncomputable def act₀_nonempty [M.FiniteBranching] (s : State ) : (M.act₀ s).Nonempty :=
  Finset.nonempty_coe_sort.mp M.instNonemptySubtypeMemFinsetAct₀

lemma P_ne_zero_sum_eq_one (h : ¬M.P s a s' = 0) : ∑' s'', M.P s a s'' = 1 := by
  simp [P_apply_eq] at h ⊢
  split at h <;> try contradiction
  exact ‹PMF _›.tsum_coe

noncomputable instance act.instDefault : Inhabited (M.act s) := Classical.inhabited_of_nonempty'

noncomputable instance act₀.instDefault [M.FiniteBranching] : Inhabited (M.act₀ s) :=
  Classical.inhabited_of_nonempty'

theorem P_sum_one_iff : ∑' s', M.P s a s' = 1 ↔ a ∈ M.act s := by
  simp [act, P_apply_eq]
  split
  · rename_i pmf _; grind [pmf.tsum_coe]
  · simp_all [Option.eq_none_iff_forall_ne_some]

section Succs

noncomputable def succs₀ [i : M.FiniteBranching] (α : Act) (s : State) : Finset State :=
  (i.succs_fin s α).toFinset

@[simp]
theorem succs₀_eq_succs [M.FiniteBranching] : M.succs₀ α s = M.succs α s := by simp [succs, succs₀]

@[simp]
theorem succs₀_mem_eq_succs_mem [M.FiniteBranching] : s' ∈ M.succs₀ a s ↔ s' ∈ M.succs a s := by
  simp [succs, succs₀]

instance [M.FiniteBranching] : Finite (M.succs α s) := Set.Finite.ofFinset (M.succs₀ α s) (by simp)
theorem succs_finite [M.FiniteBranching] : (M.succs α s).Finite := Set.toFinite (M.succs α s)
noncomputable instance [M.FiniteBranching] : Fintype (M.succs α s) := Fintype.ofFinite (M.succs α s)

instance instNonemptySuccs (α : M.act s) : Nonempty (M.succs α s) := by
  obtain ⟨α, hα⟩ := α
  simp [act, Option.isSome_iff_exists] at hα
  obtain ⟨pmf, hpmf⟩ := hα
  obtain ⟨s', hs'⟩ := pmf.support_nonempty
  use s'
  simp [succs]
  exact ne_of_eq_of_ne (congrFun (congrArg DFunLike.coe hpmf) s') hs'
instance instNonemptySuccs₀ [M.FiniteBranching] (α : M.act s) : Nonempty (M.succs₀ α s) := by
  simp only [succs₀_mem_eq_succs_mem]
  exact M.instNonemptySuccs α

theorem prev_iff_succs : s' ∈ M.prev α s ↔ s ∈ M.succs α s' := by simp [prev]
@[grind =, simp]
theorem prev_univ_iff_succs_univ : s' ∈ M.prev_univ s ↔ s ∈ M.succs_univ s' := by
  simp [prev_univ, prev_iff_succs, succs_univ, succs]

@[grind ., simp] theorem succs_implies_succs_univ (s' : M.succs α s) : ↑s' ∈ M.succs_univ s := by
  obtain ⟨s', h⟩ := s'
  simp [succs_univ]
  use α

instance instNonemptySuccsUniv : Nonempty (M.succs_univ s) := by
  simp [succs_univ]
  let α := M.default_act s
  have ⟨s', _⟩ : Nonempty (M.succs α s) := M.instNonemptySuccs ⟨α, by simp [α]⟩
  use s', α

variable [DecidableEq State] [M.FiniteBranching]

noncomputable def succs_univ₀ (s : State) : Finset State := Finset.biUnion (M.act₀ s) (M.succs₀ · s)
theorem succs_univ₀_spec (s s' : State) : s' ∈ M.succs_univ₀ s → ∃α, 0 < M.P s α s' := by
  intro h
  simp [succs_univ₀] at h
  obtain ⟨α, _, hα⟩ := h
  use α
  simp [succs] at hα
  exact pos_iff_ne_zero.mpr hα

@[simp]
theorem succs_univ₀_eq_succs_univ (s : State) :
  M.succs_univ₀ s = M.succs_univ s
:= by
  ext s'
  simp [succs_univ, succs_univ₀, succs, act, Option.isSome_iff_exists, P_apply_eq]
  grind

@[simp]
theorem succs_univ₀_mem_eq_succs_univ_mem (s s' : State) :
  s' ∈ M.succs_univ₀ s ↔ s' ∈ M.succs_univ s
:= by simp [← succs_univ₀_eq_succs_univ]

omit [DecidableEq State] in
theorem succs_Finite : (M.succs s a).Finite := by
  rw [←succs₀_eq_succs]
  apply Finset.finite_toSet
theorem succs_univ_Finite : (M.succs_univ s).Finite := by
  rw [←succs_univ₀_eq_succs_univ]
  apply Finset.finite_toSet

instance instNonemptySuccsUniv₀ : Nonempty (M.succs_univ₀ s) := by
  simp only [succs_univ₀_mem_eq_succs_univ_mem]
  exact instNonemptySuccsUniv M

instance [M.FiniteBranching] : Finite (M.succs_univ s) := by
  apply Set.Finite.ofFinset (M.succs_univ₀ s)
  simp
noncomputable instance [M.FiniteBranching] : Fintype (M.succs_univ s) := Fintype.ofFinite _

end Succs

@[simp]
theorem tsum_succs_univ_P_eq_tsum_succs_P :
    (∑' s' : M.succs_univ s, M.P s α s') = ∑' s' : M.succs α s, M.P s α s' := by
  apply tsum_eq_tsum_of_ne_zero_bij (fun ⟨s, _⟩ ↦ ⟨s.val, by simp_all⟩) <;> simp_all [succs]
  intro ⟨_, _⟩ ⟨_, _⟩; simp; exact SetCoe.ext

@[simp]
theorem tsum_succs_P_eq_tsum_P : ∑' s' : M.succs α s, M.P s α s' = ∑' s', M.P s α s' :=
  tsum_subtype_eq_of_support_subset fun _ a ↦ a

@[simp]
theorem tsum_succs_P_eq_one : α ∈ M.act s → ∑' s', M.P s α s' = 1 := M.P_sum_one_iff.mpr

theorem succs_tsum_add_left (h : α ∈ M.act s) (f : M.succs_univ s → ENNReal) :
    ∑' s' : M.succs_univ s, (M.P s α s' * a + f s') = a + ∑' s' : M.succs_univ s, f s'
:= by simp [ENNReal.tsum_add, ENNReal.tsum_mul_right, h]

end MDP
