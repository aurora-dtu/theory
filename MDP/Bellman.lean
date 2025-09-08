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
    (h : ωScottContinuous f) : lfp f = ⨆ (n : ℕ), (⇑f)^[n + 1] ⊥ := by
  rw [fixedPoints.lfp_eq_sSup_iterate f h, iSup_iterate_succ]

namespace MDP

variable {State : Type*} {Act : Type*}
variable {M : MDP State Act}

noncomputable def Φf (s : State) (α : Act) : M.Costs →o ENNReal :=
  ⟨fun v ↦ ∑' s' : M.succs_univ s, M.P s α s' * v s', fun _ _ h ↦ by simp; gcongr; apply h⟩

/-- The _demonic_ Bellman operator. -/
noncomputable def dΦ (c : M.Costs) : M.Costs →o M.Costs :=
  ⟨fun v s ↦ c s + ⨅ α : M.act s, M.Φf s α v, by intro _ _ _ _; simp; gcongr⟩

/-- The _angelic_ Bellman operator. -/
noncomputable def aΦ (c : M.Costs) : M.Costs →o M.Costs :=
  ⟨fun v s ↦ c s + ⨆ α : M.act s, M.Φf s α v, by intro _ _ _ _; simp; gcongr⟩

/-- The Bellman operator with a fixed scheduler (necessarily `Markovian`). -/
noncomputable def Φℒ (ℒ : 𝔏[M]) (c : M.Costs) : M.Costs →o M.Costs :=
  ⟨fun v s ↦ c s + Φf s (ℒ {s}) v, by intro _ _ _ _; simp; gcongr⟩

theorem dΦ.monotone' : Monotone M.dΦ := fun _ _ h _ _ ↦ by simp [dΦ]; gcongr; exact h _

theorem dΦ_le_Φℒ : dΦ ≤ Φℒ ℒ :=
  fun c f s ↦ add_le_add (by rfl) <| iInf_le_of_le ⟨ℒ {s}, ℒ.val.property {s}⟩ (by rfl)

@[deprecated]
noncomputable def lfp_Φ : M.Costs → M.Costs := lfp ∘ M.dΦ

theorem iSup_succ_dΦ_eq_iSup_dΦ c : ⨆ (n : ℕ), (M.dΦ c)^[n + 1] ⊥ = ⨆ (n : ℕ), (M.dΦ c)^[n] ⊥ := by
  ext; rw [iSup_iterate_succ]
theorem iSup_succ_dΦ_eq_iSup_dΦ_apply c :
    ⨆ (n : ℕ), (M.dΦ c)^[n + 1] ⊥ x = ⨆ (n : ℕ), (M.dΦ c)^[n] ⊥ x := by
  have := congrFun (iSup_succ_dΦ_eq_iSup_dΦ c) x
  simpa

noncomputable def lfp_Φℒ (ℒ : 𝔏[M]) : M.Costs → M.Costs := lfp ∘ M.Φℒ ℒ

theorem map_lfp_Φℒ : Φℒ c 𝒮 (lfp_Φℒ c 𝒮) = lfp_Φℒ c 𝒮 := map_lfp _

theorem Φf_ωScottContinuous : ωScottContinuous (M.Φf s a) := by
  refine ωScottContinuous.of_monotone_map_ωSup ⟨(M.Φf s a).mono, fun c ↦ ?_⟩
  simp [Φf, ωSup, ENNReal.mul_iSup, ENNReal.tsum_eq_iSup_sum]
  rw [iSup_comm]
  congr with Z
  refine ENNReal.finsetSum_iSup_of_monotone fun S _ _ h ↦ ?_
  gcongr
  exact OrderHomClass.GCongr.mono c h S

theorem Φℒ_ωScottContinuous : ωScottContinuous (M.Φℒ c ℒ) := by
  refine ωScottContinuous.of_map_ωSup_of_orderHom fun c ↦ funext fun s ↦ ?_
  simp [Φℒ, Φf_ωScottContinuous.map_ωSup]
  simp [ωSup, ← ENNReal.add_iSup]

theorem lfp_Φℒ_eq_iSup_Φℒ : M.lfp_Φℒ = fun c ℒ ↦ ⨆ n, (Φℒ c ℒ)^[n] ⊥ :=
  funext₂ fun _ _ ↦ fixedPoints.lfp_eq_sSup_iterate _ Φℒ_ωScottContinuous

theorem lfp_Φℒ_eq_iSup_succ_Φℒ : M.lfp_Φℒ = fun c ℒ ↦ ⨆ n, (Φℒ c ℒ)^[n + 1] ⊥ :=
  funext₂ fun _ _ ↦ fixedPoints.lfp_eq_sSup_succ_iterate _ Φℒ_ωScottContinuous

section FiniteBranching

variable [M.FiniteBranching]

theorem dΦ_ωScottContinuous : ωScottContinuous (M.dΦ c) := by
  refine ωScottContinuous.of_map_ωSup_of_orderHom fun c ↦ funext fun s ↦ ?_
  simp [dΦ, Φf_ωScottContinuous.map_ωSup]
  simp [ωSup, ← ENNReal.add_iSup]
  congr
  exact Eq.symm (Set.iSup_iInf_of_monotone fun α _ _ _ ↦ (M.Φf s α).mono (by gcongr))

theorem lfp_dΦ_eq_iSup_dΦ : lfp (M.dΦ c) = ⨆ (n : ℕ), (dΦ c)^[n] ⊥ :=
  fixedPoints.lfp_eq_sSup_iterate _ M.dΦ_ωScottContinuous

theorem lfp_dΦ_eq_iSup_succ_dΦ : lfp (M.dΦ c) = ⨆ (n : ℕ), (dΦ c)^[n + 1] ⊥ :=
  lfp_dΦ_eq_iSup_dΦ.trans <|
    (Set.eqOn_univ _ _).mp fun c' _ ↦ by simp [← iSup_succ_dΦ_eq_iSup_dΦ_apply]

end MDP.FiniteBranching
