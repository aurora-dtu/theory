import Mathlib.Control.Fix
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Real.EReal
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.Use
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Instances.Rat

abbrev PReal := { p : ENNReal // 0 < p ∧ p ≤ 1 }

structure MDP (State : Type*) (Act : Type*) where
  P' : State → Act → Option (PMF State)
  progress s : ∃a, (P' s a).isSome

namespace MDP

variable {State : Type*} {Act : Type*}

def P (M : MDP State Act) (s : State) (a : Act) (s' : State) :=
  match M.P' s a with
  | some pmf => pmf s'
  | none => 0

theorem progress'' (M : MDP State Act) (s : State) : ∃ (a : Act) (pmf : PMF State), (M.P' s a) = some pmf := by
  have ⟨a, h⟩ := M.progress s
  use a
  exact Option.isSome_iff_exists.mp h

theorem progress' (M : MDP State Act) (s : State) : ∃ (a : Act), (M.P s a).support.Nonempty := by
  obtain ⟨a, pmf, s'⟩ := M.progress'' s
  simp_all [P]
  unfold P
  use a
  simp [s']
  exact Function.support_nonempty_iff.mp pmf.support_nonempty

theorem if_and_eq_if_if {α : Type*} (a b : Prop) [Decidable a] [Decidable b] (x y : α) : (if a ∧ b then x else y) = if a then if b then x else y else y := by
  by_cases h : a ∧ b
  · simp only [h, and_self, ↓reduceIte]
  · simp_all only [not_and, ite_false, ite_self, ite_eq_right_iff, isEmpty_Prop, not_false_eq_true,
    implies_true, IsEmpty.forall_iff]

theorem tsum_finsum_if_eq_finsum {α β γ : Type*} [DecidableEq α] [AddCommMonoid β] [TopologicalSpace β] [DecidableEq γ]
  (S : Finset α) (i : α → γ) (f : α → β)
:
  (tsum   fun x ↦ S.sum fun s ↦ if i s = x then f s else 0)         = S.sum f := by
  have : (fun x ↦ S.sum fun s ↦ if i s = x then f s else 0).support ⊆ S.image i := by
    simp only [Finset.coe_image, Function.support_subset_iff, ne_eq, Set.mem_image, Finset.mem_coe]
    intro x h
    obtain ⟨y, h₁, h₂⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    rw [ne_eq, ite_eq_right_iff, not_forall, exists_prop] at h₂
    use y
    rw [h₂.left]
    exact ⟨h₁, rfl⟩
  rw [tsum_eq_sum' this, Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_image]
  rw [Finset.sum_congr] <;> try rfl
  simp only [ite_eq_left_iff, not_exists, not_and]
  exact fun x x' h ↦ (h x x' rfl).elim

lemma P_le_sum_P (M : MDP State Act) (s : State) (a : Act) (s' : State) : M.P s a s' ≤ ∑' (s'' : State), M.P s a s'' :=
  ENNReal.le_tsum s'

@[simp] lemma P_le_one (M : MDP State Act) (s : State) (a : Act) (s' : State) : M.P s a s' ≤ 1 := by
  unfold P
  split
  · apply PMF.coe_le_one
  · simp only [zero_le]

@[simp] lemma P_ne_top (M : MDP State Act) (s : State) (a : Act) (s' : State) : M.P s a s' ≠ ⊤ :=
  M.P_le_one s a s' |>.trans_lt ENNReal.one_lt_top |>.ne

theorem P_pos_iff_sum_eq_one {M : MDP State Act} {s : State} {a : Act} : (M.P s a).support.Nonempty ↔ ∑' s', M.P s a s' = 1 := by
  constructor <;> intro h
  · obtain ⟨s', h⟩ := h
    simp_all [P]
    split
    · simp_all
      apply PMF.tsum_coe
    · simp_all
  · by_contra q
    simp_all

def act (M : MDP State Act) (s : State) : Set Act := (M.P s).support

class FiniteBranching (M : MDP State Act) where
  act_fin : ∀ (s : State), (M.act s).Finite
  succs_fin : ∀ (s : State) (a : Act), (M.P s a).support.Finite

noncomputable def act₀ (M : MDP State Act) [i : M.FiniteBranching] (s : State) : Finset Act := (i.act_fin s).toFinset

noncomputable instance (M : MDP State Act) [Fintype Act] (s : State) : Finite (M.act s) := Subtype.finite
noncomputable instance (M : MDP State Act) [Fintype Act] (s : State) : Fintype (M.act s) := Fintype.ofFinite ↑(M.act s)
noncomputable instance (M : MDP State Act) (s : State) : Nonempty (M.act s) := by
  simp only [act, ← P_pos_iff_sum_eq_one, Set.coe_setOf, nonempty_subtype]
  have ⟨α, hα⟩ := M.progress' s
  use α
  simp_all

instance (M : MDP State Act) [i : M.FiniteBranching] (s : State) : Finite (M.act s) := i.act_fin s
theorem actFinite (M : MDP State Act) [i : M.FiniteBranching] (s : State) : (M.act s).Finite := i.act_fin s
noncomputable instance (M : MDP State Act) [M.FiniteBranching] (s : State) : Fintype (M.act s) := Fintype.ofFinite (M.act s)

@[simp]
theorem act₀_iff_act (M : MDP State Act) [i : M.FiniteBranching] (s : State) : M.act₀ s = M.act s := by simp [act₀]

@[simp]
theorem act₀_mem_iff_act_mem (M : MDP State Act) [M.FiniteBranching] (s : State) (a : Act) : a ∈ M.act₀ s ↔ a ∈ M.act s := by
  simp only [← act₀_iff_act, Finset.mem_coe]
noncomputable def act₀_prop (M : MDP State Act) [i : FiniteBranching M] (s : State) (a : Act) (h : a ∈ M.act₀ s) : (M.P s a).support.Nonempty := by
  simp_all [act₀_mem_iff_act_mem, act]

noncomputable instance (M : MDP State Act) [M.FiniteBranching] (s : State) : Nonempty ↑(M.act₀ s) := by
  simp [act₀]
  have : Nonempty (M.act s) := by exact instNonemptyElemAct M s
  simp at this
  exact this

lemma P_ne_zero_sum_eq_one {M : MDP State Act} {s : State} {a : Act} {s' : State} (h : ¬M.P s a s' = 0) : ∑' s'', M.P s a s'' = 1 := by
  simp [P] at h ⊢
  split
  · rename_i pmf _
    simp [pmf.tsum_coe]
  · rename_i h'
    simp [h'] at h

theorem P_nonempty_iff_act (M : MDP State Act) (s : State) (a : Act) : (M.P s a).support.Nonempty ↔ a ∈ M.act s := by
  simp only [Function.support_nonempty_iff, ne_eq]
  exact Iff.symm Set.mem_def

noncomputable instance act.instDefault {M : MDP State Act} : Inhabited (M.act s) := Classical.inhabited_of_nonempty'

noncomputable instance act₀.instDefault {M : MDP State Act} [M.FiniteBranching] (s : State) : Inhabited (M.act₀ s) := Classical.inhabited_of_nonempty'

theorem progress_act (M : MDP State Act) (s : State) : ∃ (a : Act), a ∈ M.act s := by
  obtain ⟨a, s', h⟩ := M.progress' s
  use a
  rw [←M.P_nonempty_iff_act s a]
  use s'

theorem P_sum_one_iff (M : MDP State Act) (s : State) (a : Act) : ∑' s', M.P s a s' = 1 ↔ a ∈ M.act s := by
  simp [act, Set.mem_setOf_eq, P]
  unfold P
  split
  · rename_i pmf _
    simp [pmf.tsum_coe, pmf.coe_ne_zero]
  · simp_all
    rfl

theorem P_sum_support_one_iff (M : MDP State Act) (s : State) (a : Act) : ∑' s' : (M.P s a).support, M.P s a s' = 1 ↔ a ∈ M.act s := by
  simp only [tsum_subtype_support (M.P s a), ← P_sum_one_iff]

theorem P_sum_support₀_one_iff (M : MDP State Act) [i : M.FiniteBranching] (s : State) (a : Act) : ∑ (s' ∈ (i.succs_fin s a).toFinset), M.P s a s' = 1 ↔ a ∈ M.act s := by
  simp only [Finset.univ_eq_attach, ← P_sum_one_iff]
  symm
  apply Eq.congr _ rfl
  apply tsum_eq_sum
  simp

theorem P_tsum_support_one_iff (M : MDP State Act) (s : State) (a : Act) : ∑' (s' : (M.P s a).support), M.P s a s' = 1 ↔ a ∈ M.act s := by
  unfold P
  split
  · rename_i pmf _
    simp [tsum_subtype, pmf.tsum_coe, act]
    unfold P
    simp_all
    simp [pmf.coe_ne_zero]
  · simp [act]
    unfold P
    simp_all
    rfl

theorem act_eq_sum_one (M : MDP State Act) (s : State) : M.act s = {a | ∑' s', M.P s a s' = 1} := by
  ext α
  have := M.P_sum_one_iff s α
  simp_all only [eq_comm, Set.mem_setOf_eq]

theorem act_eq_sum_ne_zero (M : MDP State Act) (s : State) : M.act s = {a | ¬∑' s', M.P s a s' = 0} := by
  ext α
  simp only [act_eq_sum_one, ← P_pos_iff_sum_eq_one, Function.support_nonempty_iff, ne_eq,
    Set.mem_setOf_eq, ENNReal.tsum_eq_zero, not_forall]
  unfold P
  split
  · exact Function.ne_iff
  · simp
    rfl

def Post (M : MDP State Act) (s : State) (a : Act) : Set State := {s' | ¬M.P s a s' = 0}
def Pre (M : MDP State Act) (s' : State) : Set (State × Act) := {(s, a) | ¬M.P s a s' = 0}

section Succs

variable (M : MDP State Act)

def succs (M : MDP State Act) (α : Act) (s : State) : Set State := (M.P s α).support
def prev (M : MDP State Act) (α : Act) (s' : State) : Set State := {s : State | s' ∈ M.succs α s}
noncomputable def succs₀ (M : MDP State Act) [i : M.FiniteBranching] (α : Act) (s : State) : Finset State := (i.succs_fin s α).toFinset

@[simp]
theorem succs₀_eq_succs (M : MDP State Act) [i : M.FiniteBranching] (α : Act) (s : State) : M.succs₀ α s = M.succs α s := by simp [succs, succs₀]

@[simp]
theorem succs₀_mem_eq_succs_mem [M.FiniteBranching] (s s' : State) :
  s' ∈ M.succs₀ a s ↔ s' ∈ M.succs a s
:= by simp [succs, succs₀]

instance [M.FiniteBranching] : Finite (M.succs α s) := by
  apply Set.Finite.ofFinset (M.succs₀ α s)
  simp
theorem succs_finite [M.FiniteBranching] : (M.succs α s).Finite := Set.toFinite (M.succs α s)
noncomputable instance [M.FiniteBranching] : Fintype (M.succs α s) := Fintype.ofFinite ↑(M.succs α s)

instance instNonemptySuccs (α : M.act s) : Nonempty (M.succs α s) := by
  obtain ⟨α, hα⟩ := α
  simp [act] at hα
  simp [succs]
  exact Function.ne_iff.mp hα
instance instNonemptySuccs₀ [M.FiniteBranching] (α : M.act s) : Nonempty (M.succs₀ α s) := by
  simp only [succs₀_mem_eq_succs_mem]
  exact instNonemptySuccs M α

-- NOTE: Perhaps this should be universally unioned
def succs_univ (s : State) : Set State := ⋃ α ∈ M.act s, M.succs α s
def prev_univ (s : State) : Set State := ⋃ α, M.prev α s

theorem prev_iff_succs : s' ∈ M.prev α s ↔ s ∈ M.succs α s' := by simp [prev]
@[simp]
theorem prev_univ_iff_succs_univ : s' ∈ M.prev_univ s ↔ s ∈ M.succs_univ s' := by
  simp [prev_univ, prev_iff_succs, succs_univ, succs, act]
  constructor
  · simp
    intro α h
    use α, (h <| congrFun · s), h
  · simp
    intro α _ _
    use α

@[simp] theorem succs_implies_succs_univ (s' : M.succs α s) : ↑s' ∈ M.succs_univ s := by
  obtain ⟨s', h⟩ := s'
  simp [succs_univ]
  use α
  simp_all [act, succs]
  exact fun a ↦ h (congrFun a s')

instance instNonemptySuccsUniv : Nonempty (M.succs_univ s) := by
  simp [succs_univ]
  have ⟨α, hα⟩ : Nonempty (M.act s) := M.instNonemptyElemAct s
  have ⟨s', hs⟩ : Nonempty (M.succs α s) := M.instNonemptySuccs ⟨α, hα⟩
  use s', α, hα

variable [DecidableEq State] [M.FiniteBranching]

noncomputable def succs_univ₀ (s : State) : Finset State := Finset.biUnion (M.act₀ s) (M.succs₀ · s)
noncomputable def succs_univ₀_subtype (s : State) : Finset (Subtype (fun s' ↦ s' ∈ M.succs_univ₀ s)) := (M.succs_univ₀ s).attach
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
:= by simp [succs_univ, succs_univ₀, act₀_mem_iff_act_mem, succs, succs₀]

@[simp]
theorem succs_univ₀_mem_eq_succs_univ_mem (s s' : State) :
  s' ∈ M.succs_univ₀ s ↔ s' ∈ M.succs_univ s
:= by simp [succs_univ, succs_univ₀, succs, succs₀]

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
noncomputable instance [M.FiniteBranching] : Fintype (M.succs_univ s) := Fintype.ofFinite ↑(M.succs_univ s)

end Succs

end MDP
