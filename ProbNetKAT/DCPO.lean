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
  ⟨extend_measure (fun B ↦ ⨆ μ ∈ D, μ B) (by
    simp_all [extend_measure_requirement]
    intro a b hab h
    sorry
    ), by
    simp
    refine isProbabilityMeasure_iff.mpr ?_
    sorry
  ⟩

noncomputable instance :
    CompletePartialOrder (@ProbabilityMeasure (Set H) ℬ.borel) where
  sSup D := ℬ_sSup D
  lubOfDirected := by
    simp [ℬ_sSup]
    simp [extend_measure, extend_AddContent, extend_B, extend_A_ab, extend_B_b_fin]
    sorry

def MarkovKernel (α β : Type) [MeasurableSpace α] [MeasurableSpace β] :=
    {𝒦 : ProbabilityTheory.Kernel α β // ProbabilityTheory.IsMarkovKernel 𝒦}

def MarkovKernel' (α β : Type) [MeasurableSpace α] [MeasurableSpace β] :=
  {f : α → ProbabilityMeasure β // Measurable f}

@[simp]
instance {α β : Type}  [MeasurableSpace α] [MeasurableSpace β] :
    FunLike (MarkovKernel' α β) α (ProbabilityMeasure β) where
  coe κ i := κ.val i
  coe_injective' := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ h
    congr

@[ext]
theorem MarkovKernel.ext {α β : Type} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {κ η : MarkovKernel' α β} (h : ∀ (a : α), κ a = η a) : κ = η := by
  obtain ⟨κ, hκ⟩ := κ
  obtain ⟨η, hη⟩ := η
  congr
  ext i s hS
  replace h := h i
  simp_all
  -- nth_rw 1 [DFunLike.coe] at h
  -- simp [instFunLikeMarkovKernelProbabilityMeasure] at h
  -- apply Subtype.eq_iff.mp at h
  -- simp_all

@[simp]
noncomputable instance instLE :
    LE (@MarkovKernel' (Set H) (Set H) ℬ.borel ℬ.borel) where
  le a b := ∀ i, ∀ B ∈ 𝒪, a i B ≤ b i B

noncomputable instance :
    PartialOrder (@MarkovKernel' (Set H) (Set H) ℬ.borel ℬ.borel) := {instLE with
  le_refl a a h := by simp_all
  le_trans a b c hab hbc i B hB := hab i B hB |>.trans (hbc i B hB)
  lt_iff_le_not_le := by simp
  le_antisymm a b hab hba := by
    simp_all
    ext i
    exact le_antisymm (hab i) (hba i)
}

instance : @BorelSpace (Set H) ℬ.cantorSpace ℬ.borel := sorry

@[simp]
noncomputable instance :
    SupSet (@MarkovKernel' (Set H) (Set H) ℬ.borel ℬ.borel) where
  sSup 𝒟 :=
    ⟨fun i ↦ sSup ((· i) '' 𝒟), by

      -- have := instCompletePartialOrderProbabilityMeasureSet_probNetKAT.lubOfDirected ((· i) '' 𝒟)
      -- simp only [instFunLikeMarkovKernel'ProbabilityMeasure]

      -- apply?
      -- intro X hX
      -- refine MeasurableSpace.map_def.mp ?_
      -- refine MeasurableSpace.measurableSet_generateFrom ?_
      -- simp_all only [Set.mem_setOf_eq]
      sorry
      -- apply?
      -- refine MeasurableSpace.map_def.mp ?_
      -- have := @Measurable.iSup (Set H) (Set H) ℬ.cantorSpace ℬ.borel sorry (ι:=𝒟) ℬ.borel
      ⟩
    -- let κ := @ProbabilityTheory.Kernel.mk (Set H) (Set H) ℬ.borel ℬ.borel
    --     (fun i ↦ sSup ((DFunLike.coe · i) '' 𝒟))
    --     sorry
    -- ⟨κ, by refine { isProbabilityMeasure := ?_ }; sorry⟩

noncomputable instance :
    CompletePartialOrder (@MarkovKernel (Set H) (Set H) ℬ.borel ℬ.borel) :=
{instSupSetMarkovKernelSet , instPartialOrderMarkovKernelSet with
  lubOfDirected := by
    simp_all only [instSupSetMarkovKernelSet]
    intro 𝒟 h𝒟
    refine isLUB_iff_le_iff.mpr ?_
    intro κ
    constructor
    · intro h
      simp only [upperBounds, Set.mem_setOf_eq]
      intro η hη
      intro i B hB
      have := h i B hB
      have := instCompletePartialOrderProbabilityMeasureSet_probNetKAT.lubOfDirected
          ((· i) '' 𝒟) ?_
      · apply isLUB_iff_le_iff.mp at this
        simp_all only [upperBounds, Set.mem_image, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂, Set.mem_setOf_eq, ge_iff_le]
        replace := this (κ i) |>.mp
        apply this
        · intro B' hB'
          replace h := h i B' hB'
          apply le_trans _ h
          simp only [instFunLikeMarkovKernelProbabilityMeasure, ProbabilityMeasure.coe_mk,
            ProbabilityTheory.Kernel.coe_mk, ProbabilityMeasure.mk_apply]
          apply ENNReal.le_toNNReal_of_coe_le
          · simp
            clear! B this
            clear! κ η
            sorry
          · sorry
        · assumption
        · assumption
      · sorry
    · sorry
    -- refine isLUB_pi.mpr fun a ↦ ?_
    -- simp only [Function.eval, sSup_apply]
    -- have := CompletePartialOrder.lubOfDirected ((· a) '' 𝒟) ?_
    -- · convert this
    --   exact Eq.symm sSup_image'
    -- · intro x hx y hy
    --   simp_all only [Set.mem_image, exists_exists_and_eq_and]
    --   obtain ⟨fx, hx, hx'⟩ := hx
    --   obtain ⟨fy, hy, hy'⟩ := hy
    --   subst_eqs
    --   obtain ⟨f, hf, hfx, hfy⟩ := h𝒟 _ hx _ hy
    --   use f
    --   exact ⟨hf, hfx a, hfy a⟩


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
