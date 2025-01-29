import MDP.Paths.Bounded
import MDP.Paths.Cost

open OmegaCompletePartialOrder

theorem iSup_iterate_succ' [CompleteLattice β] (f : (α → β) → α → β) :
    ⨆ n, f^[n + 1] ⊥ s = ⨆ n, f^[n] ⊥ s :=
  le_antisymm (iSup_le_iff.mpr (le_iSup_of_le ·.succ (by rfl))) <| iSup_le_iff.mpr fun n ↦ by
    rcases n with n | n
    · simp
    · apply le_iSup_of_le n (by rfl)

theorem iSup_iterate_succ [CompleteLattice β] (f : (α → β) → α → β) :
    ⨆ n, f^[n + 1] ⊥ = ⨆ n, f^[n] ⊥ := by
  ext; simp; exact iSup_iterate_succ' f

namespace MDP

variable {State : Type*} {Act : Type*}
variable (M : MDP State Act)

noncomputable def Φf (s : State) (a : Act) : (State → ENNReal) →o ENNReal :=
  ⟨fun v ↦ ∑' s' : M.succs_univ s, M.P s a s' * v s', fun _ _ h ↦ by simp; gcongr; apply h⟩

noncomputable def Φℒ (c : M.Costs) (ℒ : 𝔏[M]) : (State → ENNReal) →o (State → ENNReal) :=
  ⟨fun v s ↦ c s + M.Φf s (ℒ {s}) v, by intro v v' h s; simp only; gcongr⟩

noncomputable def act₀_nonempty [M.FiniteBranching] (s : State ) : (M.act₀ s).Nonempty :=
  Finset.nonempty_coe_sort.mp M.instNonemptySubtypeMemFinsetAct₀

noncomputable def Φ (c : M.Costs) : (State → ENNReal) →o (State → ENNReal) :=
  ⟨fun v s ↦ c s + ⨅ α : M.act s, M.Φf s α v, by intro v v' h s; simp only; gcongr⟩

theorem Φ.monotone' : Monotone M.Φ := by
  intro v v' h s
  apply add_le_add h; simp_all

theorem Φ_le_Φℒ : M.Φ c ≤ M.Φℒ c ℒ := by
  intro f s
  simp [Φ, Φℒ]
  gcongr
  apply iInf_le_of_le ⟨ℒ {s}, ℒ.val.property' {s}⟩ (by rfl)

noncomputable def lfp_Φ (c : M.Costs) : State → ENNReal := OrderHom.lfp (M.Φ c)

noncomputable def iSup_Φ (c : M.Costs) : State → ENNReal := ⨆ (n : ℕ), (M.Φ c)^[n + 1] ⊥
noncomputable def iSup'_Φ (c : M.Costs) : State → ENNReal := ⨆ (n : ℕ), (M.Φ c)^[n] ⊥

theorem iSup_Φ_eq_iSup'_Φ : M.iSup_Φ = M.iSup'_Φ := by
  ext c s; simp only [iSup_Φ, iSup'_Φ]; rw [iSup_iterate_succ]

theorem lfp_Φ_step : M.Φ c (M.lfp_Φ c) = M.lfp_Φ c := OrderHom.map_lfp (M.Φ c)

noncomputable def lfp_Φℒ (c : M.Costs) (ℒ : 𝔏[M]) : State → ENNReal :=
  OrderHom.lfp (M.Φℒ c ℒ)

theorem lfp_Φℒ_step : M.Φℒ c 𝒮 (M.lfp_Φℒ c 𝒮) = M.lfp_Φℒ c 𝒮 := OrderHom.map_lfp (M.Φℒ c 𝒮)

theorem lfp_Φ.mono (s : State) : Monotone (M.lfp_Φ · s) :=
  fun _ _ h ↦ OrderHomClass.GCongr.mono OrderHom.lfp (Φ.monotone' M h) s

section FiniteBranching

variable [DecidableEq State] [M.FiniteBranching]

theorem Φf_ωScottContinuous : ωScottContinuous (M.Φf s a) := by
  refine ωScottContinuous.of_monotone_map_ωSup ⟨OrderHom.monotone (M.Φf s a), ?_⟩
  intro c
  simp [Φf, ωSup, tsum_fintype, ENNReal.mul_iSup]
  refine ENNReal.finsetSum_iSup_of_monotone fun S _ _ h ↦ ?_
  gcongr
  exact OrderHomClass.GCongr.mono c h S

theorem Φ_ωScottContinuous : ωScottContinuous (M.Φ c) := by
  refine ωScottContinuous.of_map_ωSup_of_orderHom fun c ↦ ?_
  ext s
  simp [Φ, M.Φf_ωScottContinuous.map_ωSup]
  simp [ωSup, ← ENNReal.add_iSup]
  congr
  exact Eq.symm (Set.iSup_iInf_of_monotone fun α _ _ h ↦ (M.Φf s α).mono (by gcongr))

theorem Φℒ_ωScottContinuous : ωScottContinuous (M.Φℒ c ℒ) := by
  refine ωScottContinuous.of_map_ωSup_of_orderHom fun c ↦ ?_
  ext s
  simp [Φℒ, M.Φf_ωScottContinuous.map_ωSup]
  simp [ωSup, ← ENNReal.add_iSup]

theorem lfp_Φ_eq_iSup'_Φ : M.lfp_Φ = M.iSup'_Φ := by
  funext c
  exact fixedPoints.lfp_eq_sSup_iterate _ M.Φ_ωScottContinuous

theorem lfp_Φℒ_eq_iSup_Φℒ : M.lfp_Φℒ = fun c ℒ ↦ ⨆ n, (M.Φℒ c ℒ)^[n] ⊥ := by
  funext c ℒ
  exact fixedPoints.lfp_eq_sSup_iterate _ M.Φℒ_ωScottContinuous

theorem lfp_Φℒ_eq_iSup_succ_Φℒ : M.lfp_Φℒ = fun c ℒ ↦ ⨆ n, (M.Φℒ c ℒ)^[n + 1] ⊥ := by
  funext c ℒ
  rw [lfp_Φℒ_eq_iSup_Φℒ, iSup_iterate_succ]

theorem lfp_Φ_eq_iSup_Φ : M.lfp_Φ = M.iSup_Φ := M.lfp_Φ_eq_iSup'_Φ.trans M.iSup_Φ_eq_iSup'_Φ.symm

theorem iSup_Φ_step (c : M.Costs) : M.Φ c (M.iSup_Φ c) = M.iSup_Φ c := by
  rw [← lfp_Φ_eq_iSup_Φ]
  exact M.lfp_Φ_step

theorem iSup_Φ_step' (c : M.Costs) (s : State) :
    M.iSup_Φ c s
  = c s + ⨅ a : M.act s, ∑' s' : M.succs_univ s, M.P s a s' * M.iSup_Φ c s'
:= by
  nth_rw 1 [← lfp_Φ_eq_iSup_Φ, ← M.lfp_Φ_step]
  simp [Φ, Φf, lfp_Φ_eq_iSup_Φ]

end MDP.FiniteBranching
