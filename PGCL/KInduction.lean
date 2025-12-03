import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.FixedPoints

variable {α : Type*} [CompleteLattice α]

open OrderHom

namespace k_induction

noncomputable def Ψ (f : α) (Φ : α →o α) : α →o α :=
  ⟨(Φ · ⊓ f), fun a b hab ↦ by simp; refine inf_le_of_left_le (Φ.mono hab)⟩

def Ψ_iter_antitone (f : α) (Φ : α →o α) : Antitone ((Ψ f Φ)^[·] f) := by
  refine antitone_nat_of_succ_le fun n ↦ ?_
  induction n with
  | zero => simp [Ψ]
  | succ n ih =>
    simp only [Ψ, coe_mk, Function.iterate_succ', Function.comp_apply] at ih ⊢
    gcongr

theorem park (Φ : α →o α) (f) (k) :
    Φ ((Ψ f Φ)^[k] f) ≤ f ↔ Φ ((Ψ f Φ)^[k] f) ≤ (Ψ f Φ)^[k] f := by
  constructor
  · intro h
    have : (⇑(Ψ f Φ))^[k + 1] f ≤ (⇑(Ψ f Φ))^[k] f := by apply Ψ_iter_antitone; omega
    apply le_trans _ this
    simp only [Ψ, coe_mk, Function.iterate_succ', Function.comp_apply, le_inf_iff, le_refl,
      true_and]
    exact le_trans h (by rfl)
  · intro h
    apply le_trans h
    simp [Ψ]
    cases k with
    | zero => simp
    | succ => simp_all only [Function.iterate_succ', Function.comp_apply, inf_le_right]

end k_induction

open k_induction in
theorem k_induction {Φ : α →o α} {f} (k : ℕ) (h : Φ ((Ψ f Φ)^[k] f) ≤ f) :
    lfp Φ ≤ f :=
  (lfp_le Φ ((park Φ f k).mp h)).trans (Ψ_iter_antitone f Φ (by omega : 0 ≤ k))

namespace k_coinduction

noncomputable def Ψ (f : α) (Φ : α →o α) : α →o α :=
  ⟨(Φ · ⊔ f), fun a b hab ↦ by simp; exact le_sup_of_le_left (Φ.mono hab)⟩

def Ψ_iter_monotone (f : α) (Φ : α →o α) : Monotone ((Ψ f Φ)^[·] f) := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  induction n with
  | zero => simp [Ψ]
  | succ n ih =>
    simp only [Ψ, coe_mk, Function.iterate_succ', Function.comp_apply] at ih ⊢
    gcongr

theorem park (Φ : α →o α) (f) (k) :
    f ≤ Φ ((Ψ f Φ)^[k] f) ↔ (Ψ f Φ)^[k] f ≤ Φ ((Ψ f Φ)^[k] f) := by
  constructor
  · intro h
    have : (⇑(Ψ f Φ))^[k ] f ≤ (⇑(Ψ f Φ))^[k + 1] f := by apply Ψ_iter_monotone; omega
    apply le_trans this
    simp only [Ψ, coe_mk, Function.iterate_succ', Function.comp_apply, sup_le_iff, le_refl,
      true_and]
    exact le_trans h (by rfl)
  · intro h
    apply le_trans _ h
    simp only [Ψ, coe_mk]
    cases k with
    | zero => simp
    | succ => simp_all only [Function.iterate_succ', Function.comp_apply, le_sup_right]

end k_coinduction

open k_coinduction in
theorem k_coinduction {Φ : α →o α} {f} (k : ℕ) (h : f ≤ Φ ((Ψ f Φ)^[k] f)) :
    f ≤ gfp Φ :=
  (Ψ_iter_monotone f Φ (by omega : 0 ≤ k)).trans (le_gfp Φ ((park Φ f k).mp h))
