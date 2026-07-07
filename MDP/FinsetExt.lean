import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic

/-!
# Extensions to `Finset`

The intention is to upstream these to mathlib.
-/

namespace Finset

variable {ι α : Type*}
variable {s : Finset ι} (hS : s.Nonempty) (f : ι → α)
variable [SemilatticeSup α] [inst : Std.Total (· ≤ · : α → α → Prop)]

@[to_dual]
theorem exists_mem_eq_sup'' (f : ι → α) : ∃ i, i ∈ s ∧ s.sup' H f = f i := by
  induction H using Finset.Nonempty.cons_induction with
  | singleton c => exact ⟨c, mem_singleton_self c, rfl⟩
  | cons c s hcs hs ih =>
    rcases ih with ⟨b, hb, h'⟩
    rw [sup'_cons hs, h']
    cases inst.total (f b) (f c) with
    | inl h => exact ⟨c, mem_cons.2 (Or.inl rfl), sup_eq_left.2 h⟩
    | inr h => exact ⟨b, mem_cons.2 (Or.inr hb), sup_eq_right.2 h⟩

@[to_dual argmin]
noncomputable def argmax : ι := (s.exists_mem_eq_sup'' (H := hS) f).choose
@[to_dual argmin_spec]
theorem argmax_spec : s.argmax hS f ∈ s ∧ s.sup' hS f = f (s.argmax hS f) :=
  (s.exists_mem_eq_sup'' (H := hS) f).choose_spec

@[simp]
theorem argmax_le (a : ι) (ha : a ∈ s) : f a ≤ f (s.argmax hS f) := by
  rw [←(s.argmax_spec hS f).right]
  induction hS using Finset.Nonempty.cons_induction with
  | singleton => simp_all
  | cons c s hcs hs ih =>
    simp_all
    letI : Std.LawfulOrderMax α := by
      refine Std.LawfulOrderMax.of_le_max ?_ ?_ ?_ <;> simp_all
      exact fun a b ↦ Std.le_total
    refine Std.le_max.mpr ?_
    grind
omit [SemilatticeSup α] in
@[simp]
theorem argmin_le [SemilatticeInf α] [inst : Std.Total (· ≤ · : α → α → Prop)]
    (a : ι) (ha : a ∈ s) : f (s.argmin hS f) ≤ f a := by
  rw [←(s.argmin_spec hS f).right]
  induction hS using Finset.Nonempty.cons_induction with
  | singleton => simp_all
  | cons c s hcs hs ih =>
    simp_all
    letI : Std.LawfulOrderMin α := by
      refine Std.LawfulOrderMin.of_min_le ?_ ?_ ?_ <;> simp_all
      exact fun a b ↦ Std.le_total
    refine Std.min_le.mpr ?_
    grind

@[to_dual (attr := simp) argmin_mem, simp]
theorem argmax_mem : s.argmax hS f ∈ s := (s.argmax_spec hS f).left
@[to_dual (attr := simp) toFinset_argmin_mem, simp]
theorem toFinset_argmax_mem (s : Set ι) [Fintype s] (hS : s.toFinset.Nonempty) :
  s.toFinset.argmax hS f ∈ s := Set.mem_toFinset.mp (s.toFinset.argmax_spec hS f).left

end Finset
