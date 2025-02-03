import Mathlib.Topology.Instances.ENNReal.Lemmas

variable {α : Type*} {ι : Type*}
variable (g : α → Set ι) (f : (n : α) → g n → ENNReal)

theorem tsum_iInf_le_iInf_tsum :
  ∑' n, ⨅ i : (n : α) → g n, f n (i n) ≤ ⨅ i : (n : α) → g n, ∑' n, f n (i n)
:= le_iInf fun i ↦ ENNReal.tsum_le_tsum fun x ↦ iInf_le (f x <| · x) i

theorem iSup_iInf_sum_eq_iSup_sum_iInf [DecidableEq α] (h : ∀ n, Nonempty (g n)) :
    ⨆ S, ⨅ i : (n : α) → g n, ∑ n ∈ S, f n (i n) = ⨆ S, ∑ n ∈ S, ⨅ i : (n : α) → g n, f n (i n)
:= by
  have : Nonempty ((n : α) → ↑(g n)) := Pi.instNonempty
  congr! with S
  apply le_antisymm _ (le_iInf (Finset.sum_le_sum fun _ _ ↦ iInf_le_of_le · (by rfl)))
  induction S using Finset.induction
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

theorem iInf_tsum_le_tsum_iInf [DecidableEq α] (h : ∀ n, Nonempty (g n)) :
  ⨅ i : (n : α) → g n, ∑' n, f n (i n) ≤ ∑' n, ⨅ i : (n : α) → g n, f n (i n)
:= by
  have : ⨅ i : (n : α) → g n, ⨆ S, ∑ n ∈ S, f n (i n) = ⨆ S, ⨅ i : (n : α) → g n, ∑ n ∈ S, f n (i n)
    := by
      apply le_antisymm _ (iSup_iInf_le_iInf_iSup _)
      -- apply?
      -- rw [← Filter.liminf_eq_iSup_iInf]
      -- refine ENNReal.le_of_forall_pos_le_add ?h
      -- intro ε h h'
      -- apply?
      -- rw [← Filter.liminf_eq_iSup_iInf]
      -- refine iInf_le_iff.mpr ?_
      -- intro b h
      -- refine le_iSup_iff.mpr ?_
      -- intro b' h'
      sorry
  simp [ENNReal.tsum_eq_iSup_sum, this, iSup_iInf_sum_eq_iSup_sum_iInf, h]

theorem iInf_tsum_eq_tsum_iInf [DecidableEq α] (h : ∀ n, Nonempty (g n)) :
  ⨅ i : (n : α) → g n, ∑' n, f n (i n) = ∑' n, ⨅ i : (n : α) → g n, f n (i n)
:= (iInf_tsum_le_tsum_iInf g f h).antisymm (tsum_iInf_le_iInf_tsum g f)
