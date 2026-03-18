import MDP.OptimalCost

open OmegaCompletePartialOrder OrderHom

namespace MDP

variable {State : Type*} {Act : Type*}
variable {M : MDP State Act}

open scoped Optimization.Notation

theorem tsum_succs_univ_iSup_iSup_EC_comm [DecidableEq State] :
      ∑' s' : M.succs_univ s, ⨆ n, ⨆ 𝒮, M.P s α s' * M.EC c 𝒮 n s'
    ≤ ⨆ n, ⨆ 𝒮, ∑' s' : M.succs_univ s, M.P s α s' * M.EC c 𝒮 n s' := by
  simp [ENNReal.tsum_eq_iSup_sum]
  intro Z
  simp [iSup_comm (ι':=Finset _)]
  apply le_iSup_of_le Z
  induction Z using Finset.induction with
  | empty => simp
  | insert s₀ Z h ih =>
    simp_all
    apply le_trans <| add_le_add (by rfl) ih; clear ih
    refine ENNReal.iSup_add_iSup_le fun i j ↦ ENNReal.iSup_add_iSup_le fun 𝒮₁ 𝒮₂ ↦ ?_
    apply le_iSup₂_of_le (i ⊔ j) ⟨
      fun π ↦ if π[0] = s₀ then 𝒮₁ π else 𝒮₂ π,
      fun π ↦ by simp_all; split_ifs <;> simp_all⟩
    gcongr with s' hs'
    · exact (EC_le (by simp_all)).trans <| EC_monotone (by omega)
    · obtain ⟨s', _⟩ := s'
      exact (EC_le <| by simp_all; rintro _ _ ⟨_⟩ _; simp_all).trans <| EC_monotone (by omega)

theorem iSup_iSup_EC_eq_lfp_Φ𝒜 [DecidableEq State] :
    ⨆ n, ⨆ 𝒮, M.EC c 𝒮 n = lfp (M.Φ 𝒜 c) := by
  apply le_antisymm
  · refine le_lfp _ fun b h ↦ iSup₂_le fun n 𝒮 ↦ ?_
    induction n generalizing 𝒮 b with
    | zero => intro; simp
    | succ n ih =>
      simp [EC_succ]
      apply le_trans (fun s ↦ ?_) h
      simp [Φ, Φf, Optimization.sOpt, iSup_subtype']
      gcongr
      apply le_iSup_of_le ⟨𝒮 {s}, by simp⟩
      gcongr
      apply ih _ h
  · apply lfp_le
    simp [Φ, Optimization.sOpt, iSup_subtype']
    intro s
    simp [ENNReal.add_iSup]
    intro α hα
    simp [Φf, ENNReal.mul_iSup]
    apply le_trans <| add_le_add (by rfl) tsum_succs_univ_iSup_iSup_EC_comm
    simp [ENNReal.add_iSup]
    intro n 𝒮
    apply le_iSup₂_of_le (n + 1) ⟨
        fun π ↦ if ‖π‖ = 1 ∧ π[0] = s then α else 𝒮 π.tail,
        fun π ↦ by simp_all; split_ifs <;> simp_all⟩
    simp [EC_succ]
    gcongr
    apply EC_le (by simp_all)

theorem iSup_iSup_ECℒ_le_iSup_iSup_EC : ⨆ n, ⨆ ℒ : 𝔏[M], M.EC c ℒ n ≤ ⨆ n, ⨆ 𝒮, M.EC c 𝒮 n :=
  iSup₂_mono' fun n ℒ ↦ ⟨n, ℒ, by rfl⟩

end MDP
