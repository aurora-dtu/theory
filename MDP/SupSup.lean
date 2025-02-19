import MDP.OptimalCost

open OmegaCompletePartialOrder OrderHom

namespace MDP

variable {State : Type*} {Act : Type*}
variable {M : MDP State Act}

noncomputable def Ψ (c : M.Costs) : M.Costs →o M.Costs :=
  ⟨fun v s ↦ c s + ⨆ α : M.act s, M.Φf s α v, by intro _ _ _ _; simp; gcongr⟩

theorem tsum_succs_univ_iSup_iSup_EC_comm [DecidableEq State] :
      ∑' s' : M.succs_univ s, ⨆ n, ⨆ 𝒮, M.P s α s' * M.EC c 𝒮 n s'
    ≤ ⨆ n, ⨆ 𝒮, ∑' s' : M.succs_univ s, M.P s α s' * M.EC c 𝒮 n s' := by
  simp [ENNReal.tsum_eq_iSup_sum, ENNReal.add_iSup, ENNReal.mul_iSup]
  intro Z
  simp [iSup_comm (ι':=Finset _)]
  apply le_iSup_of_le Z
  induction Z using Finset.induction with
  | empty => simp
  | insert h ih =>
    rename_i s₀ Z
    simp_all
    apply le_trans <| add_le_add (by rfl) ih; clear ih
    refine ENNReal.iSup_add_iSup_le fun i j ↦ ENNReal.iSup_add_iSup_le fun 𝒮₁ 𝒮₂ ↦ ?_
    apply le_iSup₂_of_le (i ⊔ j) ⟨
      fun π ↦ if π[0] = s₀ then 𝒮₁ π else 𝒮₂ π,
      fun π ↦ by simp_all; split_ifs <;> simp_all⟩
    gcongr with s' hs'
    · exact (EC_le (by simp_all)).trans <| EC_monotone (by omega)
    · obtain ⟨s', _⟩ := s'
      exact (EC_le <| by simp_all; split_ifs <;> simp_all).trans <| EC_monotone (by omega)

theorem iSup_iSup_EC_eq_lfp_Ψ [DecidableEq State] :
    ⨆ n, ⨆ 𝒮, EC c 𝒮 n = lfp (M.Ψ c) := by
  apply le_antisymm
  · refine le_lfp _ fun b h ↦ iSup₂_le fun n 𝒮 ↦ ?_
    induction n generalizing 𝒮 b with
    | zero => simp
    | succ n ih =>
      simp [EC_succ]
      apply le_trans (fun s ↦ ?_) h
      simp [Ψ, Φf]
      gcongr
      apply le_iSup_of_le ⟨𝒮 {s}, by simp⟩
      gcongr
      apply ih _ h
  · apply lfp_le
    simp [Ψ]
    intro s
    simp [ENNReal.add_iSup]
    intro α hα
    simp [Φf, ENNReal.add_iSup, ENNReal.mul_iSup]
    apply le_trans <| add_le_add (by rfl) tsum_succs_univ_iSup_iSup_EC_comm
    simp [ENNReal.add_iSup]
    intro n 𝒮
    apply le_iSup₂_of_le (n + 1) ⟨
        fun π ↦ if ∎|π| = 1 ∧ π[0] = s then α else 𝒮 π.tail,
        fun π ↦ by simp_all; split_ifs <;> simp_all⟩
    simp [EC_succ]
    gcongr
    apply EC_le (by simp_all)

theorem iSup_iSup_ECℒ_le_iSup_iSup_EC : ⨆ n, ⨆ ℒ : 𝔏[M], M.EC c ℒ n ≤ ⨆ n, ⨆ 𝒮, EC c 𝒮 n :=
  iSup₂_mono' fun n ℒ ↦ ⟨n, ℒ, by rfl⟩

-- theorem tsum_succs_univ_iSup_iSup_ECℒ_comm [DecidableEq State] :
--       ∑' s' : M.succs_univ s, ⨆ n, ⨆ ℒ : 𝔏[M], M.P s α s' * M.EC c ℒ s' n
--     ≤ ⨆ n, ⨆ ℒ : 𝔏[M], ∑' s' : M.succs_univ s, M.P s α s' * M.EC c ℒ s' n := by
--   simp [ENNReal.tsum_eq_iSup_sum, ENNReal.add_iSup, ENNReal.mul_iSup]
--   intro Z
--   simp [iSup_comm (ι':=↑(Finset (M.succs_univ s)))]
--   apply le_iSup_of_le Z
--   induction Z using Finset.induction with
--   | empty => simp
--   | insert h ih =>
--     rename_i s₀ Z
--     simp_all
--     apply le_trans <| add_le_add (by rfl) ih; clear ih
--     refine ENNReal.iSup_add_iSup_le fun i j ↦ ENNReal.iSup_add_iSup_le fun 𝒮₁ 𝒮₂ ↦ ?_
--     apply le_iSup₂_of_le (i ⊔ j) ⟨⟨
--       fun π ↦ if π[0] = s₀ then 𝒮₁ π else 𝒮₂ π,
--       fun π ↦ by simp_all; split_ifs <;> simp_all⟩, by constructor; intro π; simp_all⟩
--     sorry
--     -- apply le_iSup₂_of_le (i ⊔ j) ⟨
--     --   fun π ↦ if π[0] = s₀ then 𝒮₁ π else 𝒮₂ π,
--     --   fun π ↦ by simp_all; split_ifs <;> simp_all⟩
--     -- gcongr with s' hs'
--     -- · exact (EC_le (by simp_all)).trans <| EC_monotone (by omega)
--     -- · obtain ⟨s', _⟩ := s'
--     --   exact (EC_le <| by simp_all; split_ifs <;> simp_all).trans <| EC_monotone (by omega)

-- theorem iSup_iSup_ECℒ_eq_lfp_Ψ [DecidableEq State] :
--     (fun s ↦ ⨆ n, ⨆ ℒ : 𝔏[M], EC c ℒ n s) = lfp (M.Ψ c) := by
--   apply le_antisymm (iSup_iSup_ECℒ_le_iSup_iSup_EC.trans <| iSup_iSup_EC_eq_lfp_Ψ.le ·)
--   apply lfp_le
--   simp [Ψ]
--   intro s
--   simp [ENNReal.add_iSup]
--   intro α hα
--   simp [Φf, ENNReal.add_iSup, ENNReal.mul_iSup]
--   apply le_trans <| add_le_add (by rfl) tsum_succs_univ_iSup_iSup_ECℒ_comm
--   simp [ENNReal.add_iSup]
--   intro n ℒ
--   apply le_iSup₂_of_le (n + 1) ⟨⟨
--       fun π ↦ if ∎|π| = 1 ∧ π[0] = s then α else ℒ π.tail,
--       fun π ↦ by obtain ⟨ℒ, _⟩ := ℒ; simp only [DFunLike.coe];simp_all; split_ifs <;> simp_all⟩,
--       by constructor; intro π; simp_all⟩
--   simp_all [EC_succ]
--   gcongr
--   apply EC_le (by simp_all)

-- theorem exists_iSup_iSup_ECℒ_lt_iSup_iSup_EC :
--     ∃ (State : Type) (Act : Type) (M : MDP State Act) (c : M.Costs) (s : State),
--       ⨆ n, ⨆ ℒ : 𝔏[M], M.EC c ℒ n s < ⨆ n, ⨆ 𝒮 : 𝔖[M], EC c 𝒮 n s := by
--   sorry

end MDP
