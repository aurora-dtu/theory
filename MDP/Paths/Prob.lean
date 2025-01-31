import MDP.Scheduler
import MDP.Paths.Bounded

namespace ENNReal

protected theorem tsum_biUnion' {ι : Type*} {S : Set ι} {f : α → ENNReal} {t : ι → Set α}
    (h : S.PairwiseDisjoint t) : ∑' x : ⋃ i ∈ S, t i, f x = ∑' (i : S), ∑' (x : t i), f x := by
  rw [← ENNReal.tsum_sigma]
  symm
  fapply Equiv.tsum_eq_tsum_of_support
  · exact Set.BijOn.equiv
      (fun ⟨⟨x, _⟩, ⟨y, _⟩⟩ ↦ ⟨y, ⟨t x, by simp_all; use x; simp_all⟩⟩)
      ⟨fun _ _ ↦ by simp_all, by
        constructor
        · intro ⟨x, x'⟩ _ ⟨y, y'⟩ _ _
          simp_all only [ne_eq, Subtype.mk.injEq, not_false_eq_true]
          ext <;> try assumption
          by_contra q
          have h₁ : {x'.val} ⊆ t x := by simp
          have h₂ : {x'.val} ⊆ t y := by simp_all
          absurd h x.coe_prop y.coe_prop q h₁ h₂
          simp
        · intro ⟨_, _⟩ _
          simp_all [Set.mem_iUnion.mp]⟩
  · simp only [Subtype.forall, Function.mem_support, ne_eq]
    intro ⟨_, ⟨_, _⟩⟩ _
    rfl

protected theorem tsum_biUnion {ι : Type*} {f : α → ENNReal} {t : ι → Set α}
    (h : Set.univ.PairwiseDisjoint t) : ∑' x : ⋃ i, t i, f x = ∑' (i) (x : t i), f x := by
  nth_rw 2 [← tsum_univ]
  rw [← ENNReal.tsum_biUnion' h, Set.biUnion_univ]

end ENNReal

namespace MDP

variable {State : Type*} {Act : Type*}
variable {M : MDP State Act} (π π' : M.Path)

namespace Path

variable (π π' : M.Path)

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
  simp [h₂, Fin.prod_univ_succ, Scheduler.specialize]
  congr! 2 with ⟨i, hi⟩

theorem Prob_tail [DecidableEq State] (h : 1 < ∎|π|) (𝒮 : 𝔖[M]) :
    π.Prob 𝒮 = M.P π[0] (𝒮 {π[0]}) π[1] * π.tail.Prob (𝒮[π[0] ↦ π[1]]'(by simp)) := by
  nth_rw 1 [←π.tail_prepend h, prepend_Prob]
  simp [h]

end Path

@[simp]
theorem Path.tsum_succs_univ_Prob_eq_one (𝒮 : 𝔖[M]) (π : M.Path) :
    ∑' π' : π.succs_univ, π'.val.Prob 𝒮 = π.Prob 𝒮 := by
  rw [succs_univ_eq_extend_range, Set.range_eq_iUnion, ENNReal.tsum_biUnion]
  · simp [extend_Prob, ENNReal.tsum_mul_right]
  · intro ⟨a, _⟩ _ ⟨b, _⟩ _ h
    contrapose h
    simp_all
    have := congrArg Path.last h
    simpa

@[simp]
theorem Path.tsum_Prob_eq_one (𝒮 : 𝔖[M]) (n : ℕ) : ∑' π : Path[M,s,=n], π.val.Prob 𝒮 = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Path_eq.eq_biUnion_succs_univ _, ENNReal.tsum_biUnion]
    · simpa
    · intro ⟨_, _⟩ _ ⟨_, _⟩ _ _; apply Path_eq.succs_univ_disjoint M (s:=s) (n:=n) <;> simp_all

theorem Path_eq.tsum_add_left (𝒮 : 𝔖[M]) (f : Path[M,s',=n] → ENNReal) :
    ∑' π : Path[M,s',=n], (π.val.Prob 𝒮 * a + f π) = a + ∑' π : Path[M,s',=n], f π
:= by simp [ENNReal.tsum_add, ENNReal.tsum_mul_right]

end MDP
