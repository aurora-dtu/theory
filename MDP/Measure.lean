import MDP.Paths.Cost

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
variable {M : MDP State Act}

@[simp]
theorem tsum_succs_univ_P_eq_tsum_succs_P :
    (∑' s' : M.succs_univ s, M.P s α s') = ∑' s' : M.succs α s, M.P s α s' := by
  apply tsum_eq_tsum_of_ne_zero_bij (fun ⟨s, _⟩ ↦ ⟨s.val, by simp_all⟩) <;> simp_all [succs]
  intro ⟨_, _⟩ ⟨_, _⟩; simp; exact SetCoe.ext

@[simp]
theorem tsum_succs_P_eq_tsum_P : ∑' s' : M.succs α s, M.P s α s' = ∑' s', M.P s α s' :=
  tsum_subtype_eq_of_support_subset fun _ a ↦ a

@[simp]
theorem tsum_succs_P_eq_one : α ∈ M.act s → ∑' s', M.P s α s' = 1 := M.P_sum_one_iff.mpr

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

theorem succs_tsum_add_left (𝒮 : 𝔖[M]) (f : M.succs_univ s → ENNReal) :
    ∑' s' : M.succs_univ s, (M.P s (𝒮 {s}) s' * a + f s') = a + ∑' s' : M.succs_univ s, f s'
:= by simp [ENNReal.tsum_add, ENNReal.tsum_mul_right]

end MDP
