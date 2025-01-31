import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
namespace Finset

variable {α β : Type*}
variable (S : Finset α) (hS : S.Nonempty) (f : α → β)
variable [LinearOrder β]

noncomputable def argmin : α := (S.exists_mem_eq_inf' hS f).choose
noncomputable def argmin_spec : S.argmin hS f ∈ S ∧ S.inf' hS f = f (S.argmin hS f) :=
  (S.exists_mem_eq_inf' hS f).choose_spec

@[simp]
theorem argmin_le (a : α) (ha : a ∈ S) : f (S.argmin hS f) ≤ f a := by
  rw [←(S.argmin_spec hS f).right, inf'_le_iff]
  use a

@[simp]
theorem argmin_mem : S.argmin hS f ∈ S := (S.argmin_spec hS f).left
@[simp]
theorem toFinset_argmin_mem (S : Set α) [Fintype S] (hS : S.toFinset.Nonempty) :
  S.toFinset.argmin hS f ∈ S := Set.mem_toFinset.mp (S.toFinset.argmin_spec hS f).left

end Finset
