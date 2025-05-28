import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Kernel.Defs
import Mathlib.Topology.Order.ScottTopology
import ProbNetKAT.MeasureExtension
import ProbNetKAT.Scott

namespace ProbNetKAT

set_option grind.warning false

variable {H : Type}

/-- **Lemma 5.** (i) The cartesian product of any collection of DCPOs is a DCPO under the
    componentwise order. -/
instance {α β : Type} [CompletePartialOrder α] [CompletePartialOrder β] :
    CompletePartialOrder (α × β) where
  lubOfDirected := by
    intro D hD
    refine isLUB_iff_le_iff.mpr ?_
    intro ⟨a, b⟩
    let Da := (·.fst) '' D
    let Db := (·.snd) '' D
    have hDa := CompletePartialOrder.lubOfDirected Da (by
      intro x hx y hy
      have : ∃ x', ⟨x, x'⟩ ∈ D := by simp_all [Da]
      obtain ⟨x', hx'⟩ := this
      have : ∃ y', ⟨y, y'⟩ ∈ D := by simp_all [Da]
      obtain ⟨y', hy'⟩ := this
      obtain ⟨⟨z₁, z₂⟩, hzD, hxz, hyz⟩ := hD ⟨x, x'⟩ hx' ⟨y, y'⟩ hy'
      use z₁
      simp_all [Da]
      use z₂)
    have hDb := CompletePartialOrder.lubOfDirected Db (by
      intro x hx y hy
      have : ∃ x', ⟨x', x⟩ ∈ D := by simp_all [Db]
      obtain ⟨x', hx'⟩ := this
      have : ∃ y', ⟨y', y⟩ ∈ D := by simp_all [Db]
      obtain ⟨y', hy'⟩ := this
      obtain ⟨⟨z₁, z₂⟩, hzD, hxz, hyz⟩ := hD ⟨x', x⟩ hx' ⟨y', y⟩ hy'
      use z₂
      simp_all [Db]
      use z₁)
    apply isLUB_iff_le_iff.mp at hDa
    apply isLUB_iff_le_iff.mp at hDb
    replace hDa := hDa a
    replace hDb := hDb b
    sorry

/-- **Lemma 5.** (iii) If E is a DCPO and D is any set, then the family of functions `f : D → E` is
  a DCPO under the pointwise order `f ⊑ g` iff for all `a ∈ D, f(a) ⊑ g(a)`. The supremum of a
  directed set `D` of functions `D → E` is the function `(⨆𝒟)(a) = ⨆ f ∈ 𝒟, f(a)`. -/
instance instCompletePartialOrderPi {E D : Type} [CompletePartialOrder E] :
    CompletePartialOrder (D → E) where
  lubOfDirected := by
    intro 𝒟 h𝒟
    refine isLUB_pi.mpr fun a ↦ ?_
    simp only [Function.eval, sSup_apply]
    have := CompletePartialOrder.lubOfDirected ((· a) '' 𝒟) ?_
    · convert this
      exact Eq.symm sSup_image'
    · intro x hx y hy
      simp_all only [Set.mem_image, exists_exists_and_eq_and]
      obtain ⟨fx, hx, hx'⟩ := hx
      obtain ⟨fy, hy, hy'⟩ := hy
      subst_eqs
      obtain ⟨f, hf, hfx, hfy⟩ := h𝒟 _ hx _ hy
      use f
      exact ⟨hf, hfx a, hfy a⟩

open MeasureTheory

instance : PartialOrder (@ProbabilityMeasure (Set H) ℬ.borel) where
  le := (∀ B ∈ 𝒪, · B ≤ · B)
  le_refl := by simp
  le_trans := by intro a b c hab hcb B hB; exact
    Preorder.le_trans (a B) (b B) (c B) (hab B hB) (hcb B hB)
  le_antisymm μ ν h₁ h₂ := by
    have : ∀ B ∈ 𝒪, μ B = ν B := fun B hB ↦ le_antisymm (h₁ B hB) (h₂ B hB)
    simp_all only [le_refl, implies_true]
    obtain ⟨μ, hμ⟩ := μ
    obtain ⟨ν, hν⟩ := ν
    simp_all
    suffices ∀ B ∈ 𝒪, μ B = ν B by
      congr! 1
      exact MeasureTheory.ext_of_generate_finite 𝒪 (by rw [cantor_borel_eq_scott_borel]; rfl)
        𝒪_IsPiSystem this (by simp)
    intro B hB
    replace := this B hB
    refine (ENNReal.toNNReal_eq_toNNReal_iff' ?_ ?_).mp this <;> simp

noncomputable def ℬ_sSup (D : Set (@ProbabilityMeasure (Set H) ℬ.borel)) :
    @ProbabilityMeasure (Set H) ℬ.borel :=
  ⟨measure_of_fin (fun B ↦ ⨆ μ ∈ D, μ B) sorry, by
    simp
    refine isProbabilityMeasure_iff.mpr ?_
    sorry
  ⟩

noncomputable instance :
    CompletePartialOrder (@ProbabilityMeasure (Set H) ℬ.borel) where
  sSup D := ℬ_sSup D
  lubOfDirected := by sorry

@[simp]
noncomputable instance instLE :
    LE (@ProbabilityTheory.Kernel (Set H) (Set H) ℬ.borel ℬ.borel) where
  le a b := ∀ i, ∀ B ∈ 𝒪, a i B ≤ b i B

noncomputable instance :
    PartialOrder (@ProbabilityTheory.Kernel (Set H) (Set H) ℬ.borel ℬ.borel) := {instLE with
  le_refl a a h := by simp_all
  le_trans a b c hab hbc i B hB := hab i B hB |>.trans (hbc i B hB)
  lt_iff_le_not_le := by simp; sorry
  le_antisymm a b hab hba := by
    simp_all
    ext i
    set μ := a i
    set ν := b i
    let μ' : @ProbabilityMeasure (Set H) ℬ.borel := ⟨μ, by sorry⟩
    let ν' : @ProbabilityMeasure (Set H) ℬ.borel := ⟨ν, by sorry⟩

    have := @instCompletePartialOrderPi
      (@ProbabilityMeasure (Set H) ℬ.borel)
      (Set H)
      instCompletePartialOrderProbabilityMeasureSet_probNetKAT
      |>.le_antisymm

    suffices μ' = ν' by
      sorry
    apply le_antisymm
    · intro B hB
      have := hab i B hB
      simp_all [μ', ν']
      refine (ENNReal.toNNReal_le_toNNReal ?_ ?_).mpr (hab i B hB) <;> sorry
    · intro B hB
      have := hba i B hB
      simp_all [μ', ν']
      refine (ENNReal.toNNReal_le_toNNReal ?_ ?_).mpr (hba i B hB) <;> sorry
}
-- noncomputable instance :
--     PartialOrder (@ProbabilityTheory.Kernel (Set H) (Set H) ℬ.borel ℬ.borel) := {instLE with
--   le_refl a a h := by simp_all
--   le_trans a b c hab hbc i B hB := hab i B hB |>.trans (hbc i B hB)
--   lt_iff_le_not_le := by simp
--   le_antisymm a b hab hba := by
--     obtain ⟨a, ha⟩ := a
--     obtain ⟨b, hb⟩ := b
--     simp_all
--     ext i
--     set μ := a i
--     set ν := b i
--     let μ' : @ProbabilityMeasure (Set H) ℬ.borel := ⟨μ, by sorry⟩
--     let ν' : @ProbabilityMeasure (Set H) ℬ.borel := ⟨ν, by sorry⟩
--     suffices μ' = ν' by
--       sorry
--     apply le_antisymm
--     · intro B hB
--       have := hab i B hB
--       simp_all [μ', ν']
--       refine (ENNReal.toNNReal_le_toNNReal ?_ ?_).mpr (hab i B hB) <;> sorry
--     · intro B hB
--       have := hba i B hB
--       simp_all [μ', ν']
--       refine (ENNReal.toNNReal_le_toNNReal ?_ ?_).mpr (hba i B hB) <;> sorry
-- }

end ProbNetKAT
