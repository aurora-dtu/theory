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
theorem tsum_succs_univ_P_eq_one (h : α ∈ M.act s) : ∑' s' : M.succs_univ s, M.P s α s' = 1 := by
  rw [← (M.P_sum_support_one_iff s α).mpr h]
  apply tsum_eq_tsum_of_ne_zero_bij (fun ⟨s, _⟩ ↦ ⟨s.val, by simp_all⟩) <;> simp_all
  intro ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩ h
  simp_all

@[simp]
theorem Path.tsum_succs_univ_Prob_eq_one (𝒮 : M.Scheduler') (π : M.Path) :
    ∑' π' : π.succs_univ, π'.val.Prob 𝒮 = π.Prob 𝒮 := by
  rw [Equiv.tsum_eq_tsum_of_support (g:=fun s' ↦ (π.extend s').Prob 𝒮)]
  · simp [Path.extend_Prob, ENNReal.tsum_mul_right]
  · apply Set.BijOn.equiv (fun x ↦ ⟨x.val.last, by simp⟩)
    constructor
    · intro ⟨π', h⟩ h'
      simp [Path.succs_univ_eq_extend_succs_univ] at h
      obtain ⟨s', h'', h'''⟩ := h
      subst_eqs
      simp_all
    · constructor
      · intro ⟨π₁, h₁⟩ h₁' ⟨π₂, h₂⟩ h₂' h
        simp [Path.succs_univ_eq_extend_succs_univ] at h h₁ h₂ h₁' h₂' ⊢
        obtain ⟨_, _, _⟩ := h₁
        obtain ⟨_, _, _⟩ := h₂
        subst_eqs
        simp_all
      · intro s h
        simp_all
        use π.extend s
        simp_all
        constructor
        · simp
        · simp
  · simp
    intro π' h h'
    simp [Path.succs_univ_eq_extend_succs_univ] at h
    obtain ⟨s', h'', h'''⟩ := h
    subst_eqs
    simp [Set.BijOn.equiv]

theorem tsum_Prob_eq_one (𝒮 : M.Scheduler') (n : ℕ) : ∑' π : Path[M,s,=n], π.val.Prob 𝒮 = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Path_eq.eq_biUnion_succs_univ _]
    rw [ENNReal.tsum_biUnion (f:=(·.Prob 𝒮)) (t:=fun (π : Path[M,s,=n]) ↦ π.val.succs_univ)]
    · simpa
    · intro ⟨_, _⟩ _ ⟨_, _⟩ _ _; apply Path_eq.succs_univ_disjoint (M:=M) s n <;> simp_all
