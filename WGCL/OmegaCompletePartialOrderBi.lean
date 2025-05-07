import Mathlib.Order.OmegaCompletePartialOrder

open OmegaCompletePartialOrder

variable [OmegaCompletePartialOrder α]
variable [OmegaCompletePartialOrder αᵒᵈ]

class OmegaCompletePartialOrderBi (α : Type)
    [instP : OmegaCompletePartialOrder α] [instD : OmegaCompletePartialOrder αᵒᵈ]
where
  preorder_eq : @OrderDual.instPartialOrder _ instP.toPartialOrder = instD.toPartialOrder

instance CompleteLattice.instOmegaCompletePartialOrderBi (α : Type) [CompleteLattice α] :
    OmegaCompletePartialOrderBi α where
  preorder_eq := rfl

variable {α : Type}

abbrev OmegaCompletePartialOrderCo (α : Type) := OmegaCompletePartialOrder αᵒᵈ

variable [instA : OmegaCompletePartialOrder α] [instB : OmegaCompletePartialOrder αᵒᵈ]
variable [instBi : OmegaCompletePartialOrderBi α]

structure OrderDualHom (α : Type) (β : Type) [Preorder α] [Preorder β] where
  toFun : α → β
  antitone' : Antitone toFun

instance [Preorder α] [Preorder β] : DFunLike (OrderDualHom α β) α (fun _ ↦ β) where
  coe := OrderDualHom.toFun
  coe_injective' := fun ⟨f₁, _⟩ ⟨f₂, _⟩ ↦ by simp_all

instance [Preorder α] [Preorder β] : Preorder (OrderDualHom α β) := Preorder.lift OrderDualHom.toFun

def OrderDualHom.anti [Preorder α] [Preorder β] (f : OrderDualHom α β) : Antitone f := f.antitone'

def Cochain (α : Type) [Preorder α] := OrderDualHom ℕ α

instance [Preorder α] : DFunLike (Cochain α) ℕ (fun _ ↦ α) where
  coe := OrderDualHom.toFun
  coe_injective' := fun ⟨f₁, _⟩ ⟨f₂, _⟩ ↦ by simp_all

@[simp]
theorem OmegaCompletePartialOrderBi.le_iff :
    @LE.le α (@Preorder.toLE α (@PartialOrder.toPreorder αᵒᵈ (@toPartialOrder αᵒᵈ instB))) a b ↔
    @LE.le α (@Preorder.toLE α (@PartialOrder.toPreorder α (@toPartialOrder α instA))) b a := by
  have := instBi.preorder_eq
  rw [LE.le, LE.le]
  simp_all [LE.le, Preorder.toLE, PartialOrder.toPreorder]
  rw [← this]
  rfl

@[simp]
def Cochain.toChain (c : Cochain α) : @Chain αᵒᵈ instB.toPreorder :=
  let f := @OrderHom.mk ℕ α inferInstance instB.toPreorder c (by
    intro a b h
    have := c.anti h
    simp_all) ;
  f

namespace OmegaCompletePartialOrderBi

def ωInf (c : Cochain α) : α :=
  let a := ωSup c.toChain
  a

theorem le_ωInf (c : Cochain α) (x) (h : ∀ i, x ≤ c i) : x ≤ ωInf c := by
  simp_all [ωInf]
  rw [← OmegaCompletePartialOrderBi.le_iff]
  simp [-OmegaCompletePartialOrderBi.le_iff]
  simp_all
  exact h

theorem ωInf_le (c : Cochain α) (i) : ωInf c ≤ c i := by
  simp_all [ωInf]
  rw [← OmegaCompletePartialOrderBi.le_iff]
  have := le_ωSup c.toChain i
  exact this

def ωScottCocontinuous {α β} [OmegaCompletePartialOrder αᵒᵈ] [OmegaCompletePartialOrder βᵒᵈ]
    (f : α → β) :=
  let f' : αᵒᵈ → βᵒᵈ := f
  ωScottContinuous f'

def ωScottBicontinuous {β} [OmegaCompletePartialOrder β] [OmegaCompletePartialOrder βᵒᵈ]
    [OmegaCompletePartialOrderBi β] (f : α → β) :=
  ωScottContinuous f ∧ ωScottCocontinuous f

end OmegaCompletePartialOrderBi
