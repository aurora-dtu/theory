import MDP.ENNRealExt
import MDP.Scheduler
import MDP.Paths.Bounded

namespace MDP

variable {State : Type*} {Act : Type*}
variable {M : MDP State Act} (π π' : M.Path)

namespace Path

variable (π π' : M.Path)

noncomputable def Prob (𝒮 : 𝔖[M]) (π : M.Path) : ENNReal :=
  ∏ (i : Fin (‖π‖ - 1)), M.P π[i] (𝒮 (π.take i)) π[i.succ]

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
  rw [←Fin.prod_congr' _ (by simp ; omega : n + 1 = ‖π.extend s‖ - 1)]
  rw [←Fin.prod_congr' _ (by omega : n = ‖π‖ - 1)]
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.getElem_fin, Nat.succ_eq_add_one, Fin.val_succ]
  rw [mul_comm]
  have hn' : n = ‖π‖ - 1 := by omega
  subst_eqs
  simp

theorem prepend_Prob [DecidableEq State] (𝒮 : 𝔖[M]) (s : M.prev_univ π[0]) :
    (π.prepend s).Prob 𝒮 = M.P s (𝒮 {s.val}) π[0] * π.Prob (𝒮[s ↦ π[0]]'(by simp)) := by
  simp [Prob, Fin.getElem_fin, Nat.succ_eq_add_one, Fin.val_succ]
  have h₂ : ∀ f : Fin (‖π.prepend s‖ - 1) → ENNReal,
      ∏ i : Fin (‖π.prepend s‖ - 1), f i
    = ∏ i : Fin (‖π‖ - 1 + 1), f ⟨i, by obtain ⟨i, hi⟩ := i; have := π.length_pos; simp; omega⟩
  := by
    intro f
    congr <;> try simp
    exact (Fin.heq_fun_iff (by simp)).mpr (congrFun rfl)
  simp [h₂, Fin.prod_univ_succ, Scheduler.specialize]
  congr! 2 with ⟨i, hi⟩

theorem Prob_tail [DecidableEq State] (h : 1 < ‖π‖) (𝒮 : 𝔖[M]) :
    π.Prob 𝒮 = M.P π[0] (𝒮 {π[0]}) π[1] * π.tail.Prob (𝒮[π[0] ↦ π[1]]'(by simp)) := by
  nth_rw 1 [←π.tail_prepend h, prepend_Prob]
  simp [h]

end Path

@[simp]
theorem Path.tsum_succs_univ_Prob_eq_one (π : M.Path) :
    ∑' π' : π.succs_univ, π'.val.Prob 𝒮 = π.Prob 𝒮 := by
  rw [succs_univ_eq_extend_range, Set.range_eq_iUnion, ENNReal.tsum_biUnion]
  · simp [extend_Prob, ENNReal.tsum_mul_right]
  · intro ⟨a, _⟩ _ ⟨b, _⟩ _ h
    contrapose h
    simp_all
    have := congrArg Path.last h
    simpa

@[simp]
theorem Path.tsum_Prob_eq_one (n : ℕ) : ∑' π : Path[M,s,=n+1], π.val.Prob 𝒮 = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Path_eq.eq_biUnion_succs_univ _, ENNReal.tsum_biUnion]
    · simpa
    · intro ⟨_, _⟩ _ ⟨_, _⟩ _ _; apply Path_eq.succs_univ_disjoint M (s:=s) (n:=n+1) <;> simp_all

theorem Path_eq.tsum_add_left (f : Path[M,s',=n+1] → ENNReal) :
    ∑' π : Path[M,s',=n+1], (π.val.Prob 𝒮 * a + f π) = a + ∑' π : Path[M,s',=n+1], f π
:= by simp [ENNReal.tsum_add, ENNReal.tsum_mul_right]

@[simp]
theorem Path.tsum_Prob_eq_one_comp (n : ℕ) (S : Set Path[M,s,=n+1]) :
    (∑' π : S, π.val.val.Prob 𝒮) + (∑' π : ↑Sᶜ, π.val.val.Prob 𝒮) = 1 := by
  rw [tsum_add_tsum_compl (s:=S) (f:=fun π ↦ π.val.Prob 𝒮)] <;> simp

@[simp]
theorem Path.one_sub_tsum_ite_Prob_eq (n : ℕ) (p : Path[M,s,=n+1] → Prop) [DecidablePred p] :
    1 - (∑' π, if p π then π.val.Prob 𝒮 else 0) = (∑' π, if p π then 0 else π.val.Prob 𝒮) := by
  apply ENNReal.sub_eq_of_eq_add_rev
  · have h₂ : (∑' π, if p π then π.val.Prob 𝒮 else 0) ≤ ∑' (π : ↑Path[M,s,=n + 1]), Prob 𝒮 ↑π := by
      refine ENNReal.tsum_le_tsum fun π ↦ by split_ifs <;> simp
    exact lt_of_le_of_lt h₂ (by simp) |>.ne
  · symm
    convert Path.tsum_Prob_eq_one_comp (𝒮:=𝒮) (S:=p)
    · apply tsum_eq_tsum_of_ne_zero_bij (fun ⟨⟨π, h₁⟩, h₂⟩ ↦ π)
      · intro ⟨π₁, _⟩ ⟨π₂, _⟩ h; simp_all; exact SetCoe.ext h
      · simp_all; exact fun _ _ h _ ↦ h
      · simp_all; exact fun _ _ h₁ _ h₂ ↦ (h₂ h₁).elim
    · apply tsum_eq_tsum_of_ne_zero_bij (fun ⟨⟨π, h₁⟩, h₂⟩ ↦ π)
      · intro ⟨π₁, _⟩ ⟨π₂, _⟩ h; simp_all; exact SetCoe.ext h
      · simp_all; exact fun _ _ h _ ↦ h
      · simp_all; exact fun _ _ h₁ _ h₂ ↦ (h₁ h₂).elim

@[simp]
theorem Path.one_sub_tsum_ite_Prob_eq' (n : ℕ) (p : Path[M,s,=n+1] → Prop) [DecidablePred p] :
    1 - (∑' π, if p π then 0 else π.val.Prob 𝒮) = (∑' π, if p π then π.val.Prob 𝒮 else 0) := by
  have := Path.one_sub_tsum_ite_Prob_eq (𝒮:=𝒮) n (¬p ·)
  simp_all only [ite_not]

end MDP
