import Mathlib.Order.CompletePartialOrder

open Function

abbrev PartialOrder.lift' [PartialOrder β] (f : α → β) (inj : Injective f) : PartialOrder α :=
  { Preorder.lift f with le_antisymm := fun _ _ h₁ h₂ ↦ inj (h₁.antisymm h₂) }

abbrev CompletePartialOrder.lift' [CompletePartialOrder β] (f : α → β) (inj : Injective f) : CompletePartialOrder α :=
  { Preorder.lift f with
    le_antisymm := fun _ _ h₁ h₂ ↦ inj (h₁.antisymm h₂)
    sSup 𝒟 :=
      let r : β := sSup (f '' 𝒟)
      sorry
    lubOfDirected := sorry
  }


abbrev CompletePartialOrder.lift {α : Type} {β : Type} [CompletePartialOrder β] (f : α → β) (inj : Function.Injective f) :
    CompletePartialOrder α :=
  { PartialOrder.lift f with
    sSup := by sorry
    lubOfDirected := sorry }
