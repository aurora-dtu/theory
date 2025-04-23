import Mathlib.Order.OmegaCompletePartialOrder

namespace OmegaCompletePartialOrder

variable [OmegaCompletePartialOrder α] [OrderBot α]
variable (f : α →o α)

attribute [-simp] Function.iterate_succ
attribute [simp] Function.iterate_succ'

abbrev iterate (f : α →o α) : ℕ →o α :=
  ⟨(f^[·] ⊥), fun _ _ h ↦ Monotone.monotone_iterate_of_le_map f.mono (OrderBot.bot_le _) h⟩

def lfp : (α →o α) →o α :=
  ⟨fun f ↦ ωSup (iterate f),
  by
    intro X₁ X₂ h
    apply ωSup_le_iff.mpr fun i ↦ le_ωSup_of_le i ?_
    suffices X₁^[i] ≤ X₂^[i] by apply this
    apply Monotone.iterate_le_of_le X₁.mono h⟩

def lfp_le (h : f a ≤ a) : lfp f ≤ a := by
  apply ωSup_le_iff.mpr fun i ↦ ?_
  simp only [DFunLike.coe]; simp only [OrderHom.toFun_eq_coe]
  induction i generalizing a with
  | zero => simp
  | succ i ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    apply le_trans _ h
    gcongr
    apply ih h

def lfp_le_fixed (h : f a = a) : lfp f ≤ a := by
  apply ωSup_le_iff.mpr fun i ↦ ?_
  simp only [DFunLike.coe]; simp only [OrderHom.toFun_eq_coe]
  induction i generalizing a with
  | zero => simp
  | succ i ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    rw [← h]
    gcongr
    apply ih h

theorem lfp_le_map : lfp f ≤ f (lfp f) := by
  nth_rw 1 [lfp]
  apply ωSup_le_iff.mpr fun i ↦ ?_
  simp only [DFunLike.coe]; simp only [OrderHom.toFun_eq_coe]
  rcases i with _ | i
  · simp
  · simp only [Function.iterate_succ', Function.comp_apply]
    gcongr; apply le_ωSup_of_le i (by rfl)

def le_lfp (hf : ωScottContinuous f) (h : ∀ (b: α), f b ≤ b → a ≤ b) : a ≤ lfp f := by
  apply h; clear h
  simp [lfp, ωScottContinuous.map_ωSup hf]
  intro i
  apply le_ωSup_of_le (i + 1)
  simp only [DFunLike.coe]; simp only [OrderHom.toFun_eq_coe]
  simp only [Function.iterate_succ', Function.comp_apply, le_refl]

theorem map_le_lfp (hf : ωScottContinuous f) (h : a ≤ lfp f) : f a ≤ lfp f :=
  le_lfp _ hf fun _ h' ↦ le_trans (f.mono <| le_trans h (lfp_le f h')) h'

theorem map_lfp (hf : ωScottContinuous f) : f (lfp f) = lfp f :=
  (map_le_lfp f hf (le_refl _)).antisymm (lfp_le_map f)

theorem isFixedPt_lfp (hf : ωScottContinuous f) : Function.IsFixedPt f (lfp f) := map_lfp f hf

theorem isLeast_lfp_le (hf : ωScottContinuous f) : IsLeast {a | f a ≤ a} (lfp f) :=
  ⟨map_le_lfp f hf (by rfl), mem_lowerBounds.mpr fun _ ↦ lfp_le f⟩

theorem isLeast_lfp (hf : ωScottContinuous f) : IsLeast (Function.fixedPoints f) (lfp f) :=
  ⟨isFixedPt_lfp f hf, mem_lowerBounds.mpr fun _ ↦ lfp_le_fixed f⟩

end OmegaCompletePartialOrder
