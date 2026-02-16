import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.FixedPoints

variable {α : Type*} [CompleteLattice α]

namespace OrderHom

namespace k_induction

noncomputable def Ξ (f : α) (Δ : α →o α) : α →o α :=
  ⟨(Δ · ⊓ f), fun a b hab ↦ by simp; refine inf_le_of_left_le (Δ.mono hab)⟩

def Ξ_iter_antitone (f : α) (Δ : α →o α) : Antitone ((Ξ f Δ)^[·] f) := by
  refine antitone_nat_of_succ_le fun n ↦ ?_
  induction n with
  | zero => simp [Ξ]
  | succ n ih =>
    simp only [Ξ, coe_mk, Function.iterate_succ', Function.comp_apply] at ih ⊢
    gcongr

theorem park (Δ : α →o α) (f) (k) :
    Δ ((Ξ f Δ)^[k] f) ≤ f ↔ Δ ((Ξ f Δ)^[k] f) ≤ (Ξ f Δ)^[k] f := by
  constructor
  · intro h
    have : (⇑(Ξ f Δ))^[k + 1] f ≤ (⇑(Ξ f Δ))^[k] f := by apply Ξ_iter_antitone; omega
    apply le_trans _ this
    simp only [Ξ, coe_mk, Function.iterate_succ', Function.comp_apply, le_inf_iff, le_refl,
      true_and]
    exact le_trans h (by rfl)
  · intro h
    apply le_trans h
    simp [Ξ]
    cases k with
    | zero => simp
    | succ => simp_all only [Function.iterate_succ', Function.comp_apply, inf_le_right]

end k_induction

open k_induction in
/-- k-induction -/
theorem lfp_le_of_iter {Δ : α →o α} {f} (k : ℕ) (h : Δ ((Δ · ⊓ f)^[k] f) ≤ f) :
    lfp Δ ≤ f :=
  (lfp_le Δ ((park Δ f k).mp h)).trans (Ξ_iter_antitone f Δ (by omega : 0 ≤ k))

namespace k_coinduction

noncomputable def Ξ (f : α) (Δ : α →o α) : α →o α :=
  ⟨(Δ · ⊔ f), fun a b hab ↦ by simp; exact le_sup_of_le_left (Δ.mono hab)⟩

def Ξ_iter_monotone (f : α) (Δ : α →o α) : Monotone ((Ξ f Δ)^[·] f) := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  induction n with
  | zero => simp [Ξ]
  | succ n ih =>
    simp only [Ξ, coe_mk, Function.iterate_succ', Function.comp_apply] at ih ⊢
    gcongr

theorem park (Δ : α →o α) (f) (k) :
    f ≤ Δ ((Ξ f Δ)^[k] f) ↔ (Ξ f Δ)^[k] f ≤ Δ ((Ξ f Δ)^[k] f) := by
  constructor
  · intro h
    have : (⇑(Ξ f Δ))^[k ] f ≤ (⇑(Ξ f Δ))^[k + 1] f := by apply Ξ_iter_monotone; omega
    apply le_trans this
    simp only [Ξ, coe_mk, Function.iterate_succ', Function.comp_apply, sup_le_iff, le_refl,
      true_and]
    exact le_trans h (by rfl)
  · intro h
    apply le_trans _ h
    simp only [Ξ, coe_mk]
    cases k with
    | zero => simp
    | succ => simp_all only [Function.iterate_succ', Function.comp_apply, le_sup_right]

end k_coinduction

open k_coinduction in
/-- k-coinduction -/
theorem le_gfp_of_iter {Δ : α →o α} {f} (k : ℕ) (h : f ≤ Δ ((Δ · ⊔ f)^[k] f)) :
    f ≤ gfp Δ :=
  (Ξ_iter_monotone f Δ (by omega : 0 ≤ k)).trans (le_gfp Δ ((park Δ f k).mp h))

end OrderHom
