import Mathlib.Control.Fix
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Real.EReal
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.Use
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Instances.ENNReal
import Mathlib.Order.LiminfLimsup

theorem asdf {α ι : Type*} (m : ℕ) (g : α → Set ι) (f : (n : α) → g n → ENNReal) :
  ⨅ i : (n : α) → g n, ∑' n, f n (i n) = ∑' n, ⨅ i : (n : α) → g n, f n (i n)
:= by
  have : DecidableEq α := Classical.typeDecidableEq α
  have : ∀ n, Nonempty (g n) := sorry
  have : Nonempty ((n : α) → ↑(g n)) := Pi.instNonempty
  simp_all
  have : ⨅ i : (n : α) → g n, ⨆ S, ∑ n ∈ S, f n (i n) = ⨆ S, ⨅ i : (n : α) → g n, ∑ n ∈ S, f n (i n) := by
    apply le_antisymm _ (iSup_iInf_le_iInf_iSup _)


    -- rw [← Filter.liminf_eq_iSup_iInf]



    -- apply?

    -- refine ENNReal.le_of_forall_pos_le_add ?h
    -- intro ε h h'
    -- apply?

    -- rw [← Filter.liminf_eq_iSup_iInf]

    -- refine iInf_le_iff.mpr ?_
    -- intro b h
    -- refine le_iSup_iff.mpr ?_
    -- intro b' h'

    sorry
  simp [ENNReal.tsum_eq_iSup_sum, this]
  congr with S
  apply le_antisymm
  · induction S using Finset.induction
    · simp
    · rename_i x S' h ih
      simp [Finset.sum_insert h]
      rw [← ENNReal.iInf_add_iInf]
      · apply add_le_add
        · rfl
        · simp [ih]
      · intro i j
        use fun y ↦ if y = x then i y else j y
        gcongr with y hy
        · simp
        · have : ¬y = x := ne_of_mem_of_not_mem hy h
          simp [this]
  · simp
    intro i
    gcongr
    apply iInf_le
