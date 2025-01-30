import MDP.Paths.Bounded
import MDP.Paths.Cost

open OmegaCompletePartialOrder OrderHom

theorem iSup_iterate_succ' [CompleteLattice α] (f : α → α) :
    ⨆ n, f^[n + 1] ⊥ = ⨆ n, f^[n] ⊥ :=
  le_antisymm (iSup_le_iff.mpr (le_iSup_of_le ·.succ (by rfl))) <| iSup_le_iff.mpr fun n ↦ by
    rcases n with n | n
    · simp
    · apply le_iSup_of_le n (by rfl)

theorem iSup_iterate_succ [CompleteLattice α] (f : α → α) :
    ⨆ n, f^[n + 1] ⊥ = ⨆ n, f^[n] ⊥ := by
  simp; exact iSup_iterate_succ' f

theorem fixedPoints.lfp_eq_sSup_succ_iterate [CompleteLattice α] (f : α →o α)
    (h : ωScottContinuous f) : OrderHom.lfp f = ⨆ (n : ℕ), (⇑f)^[n + 1] ⊥ := by
  rw [fixedPoints.lfp_eq_sSup_iterate f h, iSup_iterate_succ]

namespace MDP

variable {State : Type*} {Act : Type*}
variable (M : MDP State Act)

noncomputable def Φf (s : State) (a : Act) : (State → ENNReal) →o ENNReal :=
  ⟨fun v ↦ ∑' s' : M.succs_univ s, M.P s a s' * v s', fun _ _ h ↦ by simp; gcongr; apply h⟩

/-- The Bellman operator. -/
noncomputable def Φ (c : M.Costs) : (State → ENNReal) →o (State → ENNReal) :=
  ⟨fun v s ↦ c s + ⨅ α : M.act s, M.Φf s α v, by intro _ _ _ _; simp; gcongr⟩

/-- The Bellman operator with a fixed scheduler (necessarily `Markovian`). -/
noncomputable def Φℒ (c : M.Costs) (ℒ : 𝔏[M]) : (State → ENNReal) →o (State → ENNReal) :=
  ⟨fun v s ↦ c s + M.Φf s (ℒ {s}) v, by intro _ _ _ _; simp; gcongr⟩

theorem Φ.monotone' : Monotone M.Φ := fun _ _ h _ ↦ add_le_add h (by rfl)

theorem Φ_le_Φℒ : M.Φ c ≤ M.Φℒ c ℒ :=
  fun f s ↦ add_le_add (by rfl) <| iInf_le_of_le ⟨ℒ {s}, ℒ.val.property' {s}⟩ (by rfl)

noncomputable def lfp_Φ (c : M.Costs) : State → ENNReal := lfp (M.Φ c)

theorem iSup_succ_Φ_eq_iSup_Φ (c) : ⨆ (n : ℕ), (M.Φ c)^[n + 1] ⊥ = ⨆ (n : ℕ), (M.Φ c)^[n] ⊥ := by
  ext; rw [iSup_iterate_succ]

theorem lfp_Φ_step : M.Φ c (M.lfp_Φ c) = M.lfp_Φ c := map_lfp (M.Φ c)

noncomputable def lfp_Φℒ (c : M.Costs) (ℒ : 𝔏[M]) : State → ENNReal := lfp (M.Φℒ c ℒ)

theorem lfp_Φℒ_step : M.Φℒ c 𝒮 (M.lfp_Φℒ c 𝒮) = M.lfp_Φℒ c 𝒮 := map_lfp _

section FiniteBranching

variable [DecidableEq State] [M.FiniteBranching]

theorem Φf_ωScottContinuous : ωScottContinuous (M.Φf s a) := by
  refine ωScottContinuous.of_monotone_map_ωSup ⟨(M.Φf s a).mono, fun c ↦ ?_⟩
  simp [Φf, ωSup, tsum_fintype, ENNReal.mul_iSup]
  refine ENNReal.finsetSum_iSup_of_monotone fun S _ _ h ↦ ?_
  gcongr
  exact OrderHomClass.GCongr.mono c h S

theorem Φ_ωScottContinuous : ωScottContinuous (M.Φ c) := by
  refine ωScottContinuous.of_map_ωSup_of_orderHom fun c ↦ funext fun s ↦ ?_
  simp [Φ, M.Φf_ωScottContinuous.map_ωSup]
  simp [ωSup, ← ENNReal.add_iSup]
  congr
  exact Eq.symm (Set.iSup_iInf_of_monotone fun α _ _ _ ↦ (M.Φf s α).mono (by gcongr))

theorem Φℒ_ωScottContinuous : ωScottContinuous (M.Φℒ c ℒ) := by
  refine ωScottContinuous.of_map_ωSup_of_orderHom fun c ↦ funext fun s ↦ ?_
  simp [Φℒ, M.Φf_ωScottContinuous.map_ωSup]
  simp [ωSup, ← ENNReal.add_iSup]

theorem lfp_Φ_eq_iSup_Φ : M.lfp_Φ = fun c ↦ ⨆ (n : ℕ), (M.Φ c)^[n] ⊥ :=
  funext fun _ ↦ fixedPoints.lfp_eq_sSup_iterate _ M.Φ_ωScottContinuous

theorem lfp_Φℒ_eq_iSup_Φℒ : M.lfp_Φℒ = fun c ℒ ↦ ⨆ n, (M.Φℒ c ℒ)^[n] ⊥ :=
  funext₂ fun _ _ ↦ fixedPoints.lfp_eq_sSup_iterate _ M.Φℒ_ωScottContinuous

theorem lfp_Φℒ_eq_iSup_succ_Φℒ : M.lfp_Φℒ = fun c ℒ ↦ ⨆ n, (M.Φℒ c ℒ)^[n + 1] ⊥ :=
  funext₂ fun _ _ ↦ fixedPoints.lfp_eq_sSup_succ_iterate _ M.Φℒ_ωScottContinuous

theorem lfp_Φ_eq_iSup_succ_Φ : M.lfp_Φ = fun c ↦ ⨆ (n : ℕ), (M.Φ c)^[n + 1] ⊥ :=
  M.lfp_Φ_eq_iSup_Φ.trans <| (Set.eqOn_univ _ _).mp fun c _ ↦ (M.iSup_succ_Φ_eq_iSup_Φ c).symm

end MDP.FiniteBranching
