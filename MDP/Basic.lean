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

variable (M : MDP State Act)

def P (s : State) (a : Act) (s' : State) :=
  match M.P' s a with
  | some pmf => pmf s'
  | none => 0

theorem progress' (s : State) : ∃ (a : Act), (M.P s a).support.Nonempty := by
  have ⟨a, h⟩ := M.progress s
  have ⟨pmf, s'⟩ := Option.isSome_iff_exists.mp h
  simp_all [P]
  unfold P
  use a
  simp [s']
  exact Function.support_nonempty_iff.mp pmf.support_nonempty

@[simp] lemma P_le_one (s : State) (a : Act) (s' : State) : M.P s a s' ≤ 1 := by
  unfold P
  split
  · apply PMF.coe_le_one
  · simp only [zero_le]

@[simp] lemma P_ne_top (s : State) (a : Act) (s' : State) : M.P s a s' ≠ ⊤ :=
  M.P_le_one s a s' |>.trans_lt ENNReal.one_lt_top |>.ne

theorem P_pos_iff_sum_eq_one : (M.P s a).support.Nonempty ↔ ∑' s', M.P s a s' = 1 := by
  constructor <;> intro h
  · obtain ⟨s', h⟩ := h
    simp_all [P]
    split
    · simp_all
      apply PMF.tsum_coe
    · simp_all
  · by_contra q
    simp_all

def act (s : State) : Set Act := (M.P s).support

class FiniteBranching where
  act_fin : ∀ (s : State), (M.act s).Finite
  succs_fin : ∀ (s : State) (a : Act), (M.P s a).support.Finite

noncomputable def act₀ [i : M.FiniteBranching] (s : State) : Finset Act := (i.act_fin s).toFinset

noncomputable instance [Fintype Act] : Finite (M.act s) := Subtype.finite
noncomputable instance [Fintype Act] : Fintype (M.act s) := Fintype.ofFinite ↑(M.act s)
noncomputable instance act.instNonEmpty : Nonempty (M.act s) := by
  simp only [act, ← P_pos_iff_sum_eq_one, Set.coe_setOf, nonempty_subtype]
  have ⟨α, hα⟩ := M.progress' s
  use α
  simp_all

noncomputable def default_act (s : State) : Act :=
  (nonempty_subtype.mp <| act.instNonEmpty M (s:=s)).choose
@[simp]
theorem default_act_spec (s : State) : M.default_act s ∈ M.act s :=
  (nonempty_subtype.mp <| act.instNonEmpty M (s:=s)).choose_spec

instance [i : M.FiniteBranching] : Finite (M.act s) := i.act_fin s
theorem actFinite [i : M.FiniteBranching] : (M.act s).Finite := i.act_fin s
noncomputable instance [M.FiniteBranching] : Fintype (M.act s) := Fintype.ofFinite (M.act s)

@[simp]
theorem act₀_iff_act [i : M.FiniteBranching] : M.act₀ s = M.act s := by simp [act₀]

@[simp]
theorem act₀_mem_iff_act_mem [M.FiniteBranching] : a ∈ M.act₀ s ↔ a ∈ M.act s := by
  simp only [← act₀_iff_act, Finset.mem_coe]
theorem act₀_prop [FiniteBranching M] (h : a ∈ M.act₀ s) : (M.P s a).support.Nonempty := by
  simp_all [act₀_mem_iff_act_mem, act]

noncomputable instance [M.FiniteBranching] : Nonempty (M.act₀ s) := by
  simp [act₀]
  have : Nonempty (M.act s) := act.instNonEmpty M
  simp at this
  exact this

lemma P_ne_zero_sum_eq_one (h : ¬M.P s a s' = 0) : ∑' s'', M.P s a s'' = 1 := by
  simp [P] at h ⊢
  split
  · rename_i pmf _
    simp [pmf.tsum_coe]
  · rename_i h'
    simp [h'] at h

theorem P_nonempty_iff_act : (M.P s a).support.Nonempty ↔ a ∈ M.act s := by
  simp only [Function.support_nonempty_iff, ne_eq]
  exact Iff.symm Set.mem_def

noncomputable instance act.instDefault : Inhabited (M.act s) := Classical.inhabited_of_nonempty'

noncomputable instance act₀.instDefault [M.FiniteBranching] : Inhabited (M.act₀ s) :=
  Classical.inhabited_of_nonempty'

theorem P_sum_one_iff : ∑' s', M.P s a s' = 1 ↔ a ∈ M.act s := by
  simp [act, Set.mem_setOf_eq, P]
  unfold P
  split
  · rename_i pmf _
    simp [pmf.tsum_coe, pmf.coe_ne_zero]
  · simp_all
    rfl

theorem P_sum_support_one_iff : ∑' s' : (M.P s a).support, M.P s a s' = 1 ↔ a ∈ M.act s := by
  simp only [tsum_subtype_support (M.P s a), ← P_sum_one_iff]

theorem P_sum_support₀_one_iff [i : M.FiniteBranching] :
    ∑ (s' ∈ (i.succs_fin s a).toFinset), M.P s a s' = 1 ↔ a ∈ M.act s := by
  simp only [Finset.univ_eq_attach, ← P_sum_one_iff]
  symm
  apply Eq.congr _ rfl
  apply tsum_eq_sum
  simp

theorem P_tsum_support_one_iff : ∑' (s' : (M.P s a).support), M.P s a s' = 1 ↔ a ∈ M.act s := by
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

theorem act_eq_sum_one : M.act s = {a | ∑' s', M.P s a s' = 1} := by
  ext a
  have := M.P_sum_one_iff (s:=s) (a:=a)
  simp_all only [eq_comm, Set.mem_setOf_eq]

theorem act_eq_sum_ne_zero (s : State) : M.act s = {a | ¬∑' s', M.P s a s' = 0} := by
  ext α
  simp only [act_eq_sum_one, ← P_pos_iff_sum_eq_one, Function.support_nonempty_iff, ne_eq,
    Set.mem_setOf_eq, ENNReal.tsum_eq_zero, not_forall]
  unfold P
  split
  · exact Function.ne_iff
  · simp
    rfl

def Post (s : State) (a : Act) : Set State := {s' | ¬M.P s a s' = 0}
def Pre (s' : State) : Set (State × Act) := {(s, a) | ¬M.P s a s' = 0}

section Succs

def succs (α : Act) (s : State) : Set State := (M.P s α).support
def prev (α : Act) (s' : State) : Set State := {s : State | s' ∈ M.succs α s}
noncomputable def succs₀ [i : M.FiniteBranching] (α : Act) (s : State) : Finset State :=
  (i.succs_fin s α).toFinset

@[simp]
theorem succs₀_eq_succs [M.FiniteBranching] : M.succs₀ α s = M.succs α s := by simp [succs, succs₀]

@[simp]
theorem succs₀_mem_eq_succs_mem [M.FiniteBranching] : s' ∈ M.succs₀ a s ↔ s' ∈ M.succs a s := by
  simp [succs, succs₀]

instance [M.FiniteBranching] : Finite (M.succs α s) := by
  apply Set.Finite.ofFinset (M.succs₀ α s)
  simp
theorem succs_finite [M.FiniteBranching] : (M.succs α s).Finite := Set.toFinite (M.succs α s)
noncomputable instance [M.FiniteBranching] : Fintype (M.succs α s) := Fintype.ofFinite (M.succs α s)

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
  let α := M.default_act s
  have ⟨s', _⟩ : Nonempty (M.succs α s) := M.instNonemptySuccs ⟨α, by simp [α]⟩
  use s', α, by simp [α]

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
noncomputable instance [M.FiniteBranching] : Fintype (M.succs_univ s) := Fintype.ofFinite _

end Succs

end MDP
