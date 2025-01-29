import MDP.Scheduler

namespace MDP

namespace Path

variable {State : Type*} {Act : Type*}
variable {M : MDP State Act} (π π' : M.Path)

noncomputable def Prob (𝒮 : 𝔖[M]) (π : M.Path) : ENNReal :=
  ∏ (i : Fin (∎|π| - 1)), M.P π[i] (𝒮 (π.take i)) π[i.succ]

@[simp]
theorem singleton_Prob (x : State) (𝒮 : 𝔖[M]) : ({x} : M.Path).Prob 𝒮 = 1 := by
  simp [Prob]
  congr

@[simp]
theorem Prob_le_one (𝒮 : 𝔖[M]) : π.Prob 𝒮 ≤ 1 := by
  simp only [Prob, Fin.getElem_fin, Nat.succ_eq_add_one, Fin.val_succ]
  apply Finset.prod_le_one
  · simp only [Finset.mem_univ, zero_le, imp_self, implies_true]
  · intro n _
    apply M.P_le_one

@[simp]
theorem Prob_ne_top (𝒮 : 𝔖[M]) : π.Prob 𝒮 ≠ ⊤ := by
  exact π.Prob_le_one 𝒮 |>.trans_lt ENNReal.one_lt_top |>.ne

theorem extend_Prob (s : M.succs_univ π.last) (𝒮 : 𝔖[M]) :
    (π.extend s).Prob 𝒮 = M.P π.last (𝒮 π) s * π.Prob 𝒮 := by
  unfold Prob
  let ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero π.length_ne_zero
  rw [←Fin.prod_congr' _ (by simp ; omega : n + 1 = ∎|π.extend s| - 1)]
  rw [←Fin.prod_congr' _ (by omega : n = ∎|π| - 1)]
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.getElem_fin, Nat.succ_eq_add_one, Fin.val_succ]
  rw [mul_comm]
  have hn' : n = ∎|π| - 1 := by omega
  subst_eqs
  simp

theorem prepend_Prob [DecidableEq State] (𝒮 : 𝔖[M]) (s : M.prev_univ π[0]) :
    (π.prepend s).Prob 𝒮 = M.P s (𝒮 {s.val}) π[0] * π.Prob (𝒮[s ↦ π[0]]'(by simp)) := by
  simp [Prob, Fin.getElem_fin, Nat.succ_eq_add_one, Fin.val_succ]
  have h₂ : ∀ f : Fin (∎|π.prepend s| - 1) → ENNReal,
      ∏ i : Fin (∎|π.prepend s| - 1), f i
    = ∏ i : Fin (∎|π| - 1 + 1), f ⟨i, by obtain ⟨i, hi⟩ := i; have := π.length_pos; simp; omega⟩
  := by
    intro f
    congr <;> try simp
    exact (Fin.heq_fun_iff (by simp)).mpr (congrFun rfl)
  simp [h₂, Fin.prod_univ_succ, Scheduler'.specialize]
  congr! 2 with ⟨i, hi⟩

theorem Prob_tail [DecidableEq State] (h : 1 < ∎|π|) (𝒮 : 𝔖[M]) :
    π.Prob 𝒮 = M.P π[0] (𝒮 {π[0]}) π[1] * π.tail.Prob (𝒮[π[0] ↦ π[1]]'(by simp)) := by
  nth_rw 1 [←π.tail_prepend h, prepend_Prob]
  simp [h]

end MDP.Path
