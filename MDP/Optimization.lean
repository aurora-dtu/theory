import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Inv
import Mathlib.Order.Hom.Order
import Mathlib.Order.OmegaCompletePartialOrder

theorem iSup_iSup_eq_iSup {α ι : Type*} [CompleteLattice α] [SemilatticeSup ι] (f : ι → ι → α)
    (hf₁ : Monotone f) (hf₂ : ∀ i, Monotone (f i)) :
    ⨆ i, ⨆ j, f i j = ⨆ i, f i i := by
  apply le_antisymm
  · apply iSup₂_le_iff.mpr fun i j ↦ le_iSup_of_le (i ⊔ j) ?_
    apply le_trans (hf₁ le_sup_left j) (hf₂ (i ⊔ j) le_sup_right)
  · apply iSup_le_iff.mpr fun i ↦ le_iSup₂_of_le i i (by rfl)

inductive Optimization where | Angelic | Demonic

namespace Optimization

namespace Notation

scoped notation "𝒜" => Optimization.Angelic
scoped notation "𝒟" => Optimization.Demonic

end Notation

open scoped Notation

variable {ι α : Type*} (O : Optimization)

abbrev dual : Optimization → Optimization
  | 𝒜 => 𝒟
  | 𝒟 => 𝒜
@[grind =, simp] theorem 𝓐_dual : Optimization.Angelic.dual = 𝒟 := by rfl
@[grind =, simp] theorem 𝒟_dual : Optimization.Demonic.dual = 𝒜 := by rfl

section opt₂

variable [Lattice α]

def opt₂ (a b : α) : α :=
  match O with
    | 𝒜 => a ⊔ b
    | 𝒟 => a ⊓ b

@[simp]
theorem opt₂_apply (f g : γ → α) : O.opt₂ f g x = O.opt₂ (f x) (g x) := by
  cases O <;> simp [opt₂]
@[simp]
theorem opt₂_OrderHom_apply [Preorder γ] (f g : γ →o α) : O.opt₂ f g x = O.opt₂ (f x) (g x) := by
  cases O <;> simp [opt₂]

@[gcongr]
theorem opt₂_le {a b c d : α} (hac : a ≤ c) (hbd : b ≤ d) : O.opt₂ a b ≤ O.opt₂ c d := by
  cases O <;> simp [opt₂] <;> constructor
  · exact le_sup_of_le_left hac
  · exact le_sup_of_le_right hbd
  · exact inf_le_of_left_le hac
  · exact inf_le_of_right_le hbd

@[grind =, simp]
theorem 𝒜_opt₂ {a b : α} : (𝒜 : Optimization).opt₂ a b = a ⊔ b := rfl
@[grind =, simp]
theorem 𝒟_opt₂ {a b : α} : (𝒟 : Optimization).opt₂ a b = a ⊓ b := rfl

open OmegaCompletePartialOrder

theorem opt₂_ωScottContinuous {α β : Type*} [Order.Frame α] [Order.Frame β]
    (O : Optimization)
    {f : α →o β} {g : α →o β} (hf : ωScottContinuous f) (hg : ωScottContinuous g) :
    ωScottContinuous (O.opt₂ f g) := by
  cases O
  · simp only [𝒜_opt₂]
    exact CompleteLattice.ωScottContinuous.sup hf hg
  · simp only [𝒟_opt₂]
    refine ωScottContinuous.of_monotone_map_ωSup ?_
    simp [ωSup]
    constructor
    · intro a b hab; simp only [Pi.inf_apply]; gcongr
    · intro c
      have := hf.map_ωSup_of_orderHom; simp [ωSup] at this; rw [this]; clear this
      have := hg.map_ωSup_of_orderHom; simp [ωSup] at this; rw [this]; clear this
      simp [iSup_inf_eq, inf_iSup_eq]
      refine iSup_iSup_eq_iSup (fun i j ↦ f (c j) ⊓ g (c i)) ?_ ?_
      · intro _ _ _ _; simp only; gcongr
      · intro _ _ _ _; simp only; gcongr

end opt₂

variable [CompleteLattice α]

def iOpt : (ι → α) →o α :=
  match O with
    | 𝒜 => ⟨fun f ↦ ⨆ α, f α, fun f g h ↦ by simp only; gcongr; apply h⟩
    | 𝒟 => ⟨fun f ↦ ⨅ α, f α, fun f g h ↦ by simp only; gcongr; apply h⟩

def sOpt (S : Set ι) : (ι → α) →o α :=
  match O with
    | 𝒜 => ⟨fun f ↦ ⨆ α ∈ S, f α, fun f g h ↦ by simp only; gcongr; apply h⟩
    | 𝒟 => ⟨fun f ↦ ⨅ α ∈ S, f α, fun f g h ↦ by simp only; gcongr; apply h⟩

theorem sOpt_eq_iOpt (S : Set ι) (f : ι → α) : O.sOpt S f = O.iOpt fun (a : S) ↦ f a := by
  simp [sOpt, iOpt]
  split <;> simp [iSup_subtype', iInf_subtype']

@[simp]
theorem sOpt_singleton {f : ι → α} : O.sOpt {i} f = f i := by
  simp [sOpt]; split <;> rfl
@[simp]
theorem sOpt_pair {f : ι → α} : O.sOpt {a, b} f = O.opt₂ (f a) (f b) := by
  simp [sOpt, opt₂]; split <;> simp
  · apply le_antisymm
    · simp
    · simp
      constructor
      · apply le_iSup_of_le a; simp
      · apply le_iSup_of_le b; simp
  · apply le_antisymm
    · simp
      constructor
      · apply iInf_le_of_le a; simp
      · apply iInf_le_of_le b; simp
    · simp

@[grind =, simp]
theorem 𝒜_iOpt {f : ι → α} : (𝒜 : Optimization).iOpt f = iSup f := rfl
@[grind =, simp]
theorem 𝒟_iOpt {f : ι → α} : (𝒟 : Optimization).iOpt f = iInf f := rfl

@[grind =, simp]
theorem 𝒜_sOpt {S : Set ι} {f : ι → α} : (𝒜 : Optimization).sOpt S f = ⨆ α ∈ S, f α := rfl
@[grind =, simp]
theorem 𝒟_sOpt {S : Set ι} {f : ι → α} : (𝒟 : Optimization).sOpt S f = ⨅ α ∈ S, f α := rfl

@[grind =, simp]
theorem iOpt_apply {f : ι → β → α} : O.iOpt f s = O.iOpt (f · s) := by
  cases O <;> simp [iOpt]

@[simp]
theorem iOpt_const [Nonempty ι] {x : α} : O.iOpt (fun (_ : ι) ↦ x) = x := by
  cases O <;> simp [iOpt]

theorem ENNReal_add_iOpt [Nonempty ι] {f : ι → ENNReal} :
    O.iOpt (fun (i : ι) ↦ a + f i) = a + O.iOpt f := by
  cases O <;> simp [ENNReal.add_iSup, ENNReal.add_iInf]
theorem ENNReal_iOpt_add [Nonempty ι] {f : ι → ENNReal} :
    O.iOpt (fun (i : ι) ↦ f i + a) = O.iOpt f + a := by
  cases O <;> simp [ENNReal.iSup_add, ENNReal.iInf_add]
theorem ENNReal_mul_iOpt [Nonempty ι] {f : ι → ENNReal} {a : ENNReal} (ha : a ≠ ⊤) :
    O.iOpt (fun (i : ι) ↦ a * f i) = a * O.iOpt f := by
  cases O <;> simp [ENNReal.mul_iSup, ENNReal.mul_iInf, ha]
theorem ENNReal_iOpt_mul [Nonempty ι] {f : ι → ENNReal} {a : ENNReal} (ha : a ≠ ⊤) :
    O.iOpt (fun (i : ι) ↦ f i * a) = O.iOpt f * a := by
  cases O <;> simp [ENNReal.iSup_mul, ENNReal.iInf_mul, ha]

end Optimization

#min_imports
