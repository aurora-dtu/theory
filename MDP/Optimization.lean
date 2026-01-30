import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Inv
import Mathlib.Order.Hom.Order
import Mathlib.Order.OmegaCompletePartialOrder

inductive Optimization where | Angelic | Demonic

namespace Optimization

namespace Notation

scoped notation "𝒜" => Optimization.Angelic
scoped notation "𝒟" => Optimization.Demonic

end Notation

open scoped Notation

variable {ι α : Type*} [CompleteLattice α] (O : Optimization)

def opt₂ (a b : α) : α :=
  match O with
    | 𝒜 => a ⊔ b
    | 𝒟 => a ⊓ b

def opt : (ι → α) →o α :=
  match O with
    | 𝒜 => ⟨fun f ↦ ⨆ α, f α, fun f g h ↦ by simp only; gcongr; apply h⟩
    | 𝒟 => ⟨fun f ↦ ⨅ α, f α, fun f g h ↦ by simp only; gcongr; apply h⟩

def sOpt (S : Set ι) : (ι → α) →o α :=
  match O with
    | 𝒜 => ⟨fun f ↦ ⨆ α ∈ S, f α, fun f g h ↦ by simp only; gcongr; apply h⟩
    | 𝒟 => ⟨fun f ↦ ⨅ α ∈ S, f α, fun f g h ↦ by simp only; gcongr; apply h⟩

theorem sOpt_eq_opt (S : Set ι) (f : ι → α) : O.sOpt S f = O.opt fun (a : S) ↦ f a := by
  simp [sOpt, opt]
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
theorem 𝒜_opt {f : ι → α} : (𝒜 : Optimization).opt f = iSup f := rfl
@[grind =, simp]
theorem 𝒟_opt {f : ι → α} : (𝒟 : Optimization).opt f = iInf f := rfl

@[grind =, simp]
theorem 𝒜_sOpt {S : Set ι} {f : ι → α} : (𝒜 : Optimization).sOpt S f = ⨆ α ∈ S, f α := rfl
@[grind =, simp]
theorem 𝒟_sOpt {S : Set ι} {f : ι → α} : (𝒟 : Optimization).sOpt S f = ⨅ α ∈ S, f α := rfl

@[grind =, simp]
theorem opt_apply {f : ι → β → α} : O.opt f s = O.opt (f · s) := by
  cases O <;> simp [opt]

@[simp]
theorem opt_const [Nonempty ι] {x : α} : O.opt (fun (_ : ι) ↦ x) = x := by
  cases O <;> simp [opt]

theorem ENNReal_add_opt [Nonempty ι] {f : ι → ENNReal} :
    O.opt (fun (i : ι) ↦ a + f i) = a + O.opt f := by
  cases O <;> simp [ENNReal.add_iSup, ENNReal.add_iInf]
theorem ENNReal_opt_add [Nonempty ι] {f : ι → ENNReal} :
    O.opt (fun (i : ι) ↦ f i + a) = O.opt f + a := by
  cases O <;> simp [ENNReal.iSup_add, ENNReal.iInf_add]
theorem ENNReal_mul_opt [Nonempty ι] {f : ι → ENNReal} {a : ENNReal} (ha : a ≠ ⊤) :
    O.opt (fun (i : ι) ↦ a * f i) = a * O.opt f := by
  cases O <;> simp [ENNReal.mul_iSup, ENNReal.mul_iInf, ha]
theorem ENNReal_opt_mul [Nonempty ι] {f : ι → ENNReal} {a : ENNReal} (ha : a ≠ ⊤) :
    O.opt (fun (i : ι) ↦ f i * a) = O.opt f * a := by
  cases O <;> simp [ENNReal.iSup_mul, ENNReal.iInf_mul, ha]

end Optimization

#min_imports
