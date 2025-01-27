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
  ext
  simp
  exact iSup_iterate_succ' f

namespace MDP

variable {State : Type*} {Act : Type*}
variable (M : MDP State Act)

noncomputable def Φf (s : State) (a : Act) : (State → ENNReal) →o ENNReal :=
  ⟨fun v ↦ ∑' s' : M.succs_univ s, M.P s a s' * v s', by
    intro v v' v_le_v'
    simp only
    gcongr
    exact v_le_v' _⟩

noncomputable def Φ𝒮 (cost : M.Costs) (𝒮 : M.Scheduler) : (State → ENNReal) →o (State → ENNReal) :=
  ⟨fun v s ↦ cost s + M.Φf s (𝒮 {s}) v, by
    intro v v' h s
    simp only
    gcongr⟩

noncomputable def act₀_nonempty [M.FiniteBranching] (s : State ) : (M.act₀ s).Nonempty :=
  Finset.nonempty_coe_sort.mp (instNonemptySubtypeMemFinsetAct₀ M s)

noncomputable def Φ (cost : M.Costs) : (State → ENNReal) →o (State → ENNReal) :=
  ⟨fun v s ↦ cost s + ⨅ α : M.act s, M.Φf s α v, by
    intro v v' h s
    simp only
    gcongr⟩

theorem Φ.monotone' : Monotone (fun (cost : State → ENNReal) ↦ M.Φ cost) := by
  intro v v' h s
  apply add_le_add h; simp_all

theorem Φ_le_Φ𝒮 (cost : M.Costs) : M.Φ cost ≤ M.Φ𝒮 cost 𝒮 := by
  intro f s
  simp [Φ, Φ𝒮]
  gcongr
  apply iInf_le_of_le ⟨𝒮 {s}, 𝒮.val.property' {s}⟩
  simp

noncomputable def lfp_Φ (cost : M.Costs) : State → ENNReal := OrderHom.lfp (M.Φ cost)

noncomputable def iSup_Φ (cost : M.Costs) : State → ENNReal := ⨆ (n : ℕ), (M.Φ cost)^[n + 1] ⊥
noncomputable def iSup'_Φ (cost : M.Costs) : State → ENNReal := ⨆ (n : ℕ), (M.Φ cost)^[n] ⊥

theorem iSup_Φ_eq_iSup'_Φ : M.iSup_Φ = M.iSup'_Φ := by
  ext cost s
  simp [iSup_Φ, iSup'_Φ]
  apply le_antisymm
  · simp
    intro n
    refine le_iSup_iff.mpr ?h.h.a.a
    intro e h
    have := h (n + 1)
    simp_all
  · simp
    intro n
    apply le_iSup_iff.mpr
    intro e h
    rcases n with n | n
    · simp_all
    · simp_all

theorem Φ_iterate_succ (cost : M.Costs) (s : State) :
    (M.Φ cost)^[i + 1] ⊥ s
  = cost s + ⨅ α : M.act s, M.Φf s α ((M.Φ cost)^[i] ⊥)
:= by
  simp only [Function.iterate_succ', Function.comp_apply, Φ]
  simp
theorem Φ𝒮_iterate_succ (cost : M.Costs) (𝒮 : M.Scheduler) (s : State) :
    (M.Φ𝒮 cost 𝒮)^[i + 1] ⊥ s
  = cost s + (M.Φf s (𝒮 {s})) ((M.Φ𝒮 cost 𝒮)^[i] ⊥)
:= by
  simp only [Function.iterate_succ', Function.comp_apply, Φ𝒮]
  simp

theorem lfp_Φ_step (cost : M.Costs) : M.Φ cost (M.lfp_Φ cost) = M.lfp_Φ cost :=
  OrderHom.map_lfp (M.Φ cost)

theorem lfp_Φ_step' (cost : M.Costs) (s : State) :
    M.lfp_Φ cost s
  = cost s + (⨅ a : M.act s, ∑' s' : M.succs_univ s, M.P s a s' * M.lfp_Φ cost s')
:= by
  conv => left ; rw [←lfp_Φ_step]
  simp [Φ]
  congr! 2 with α

theorem lfp_Φ_step_Φf (cost : M.Costs) (s : State) :
    M.lfp_Φ cost s
  = cost s + ⨅ a : M.act s, M.Φf s a (M.lfp_Φ cost)
:= by
  conv => left ; rw [←lfp_Φ_step]
  simp [Φ]

noncomputable def lfp_Φ𝒮 (cost : M.Costs) (𝒮 : M.Scheduler) : State → ENNReal :=
  OrderHom.lfp (M.Φ𝒮 cost 𝒮)

theorem lfp_Φ𝒮_step (cost : M.Costs) (𝒮 : M.Scheduler) :
    M.Φ𝒮 cost 𝒮 (M.lfp_Φ𝒮 cost 𝒮) = M.lfp_Φ𝒮 cost 𝒮 := OrderHom.map_lfp (M.Φ𝒮 cost 𝒮)

theorem lfp_Φ𝒮_step_Φf (cost : M.Costs) (𝒮 : M.Scheduler) (s : State) :
    M.lfp_Φ𝒮 cost 𝒮 s
  = cost s + M.Φf s (𝒮 {s}) (M.lfp_Φ𝒮 cost 𝒮)
:= by
  conv => left ; rw [←lfp_Φ𝒮_step]
  simp [Φ𝒮]

theorem lfp_Φ.mono (s : State) : Monotone (fun (cost : State → ENNReal) ↦ M.lfp_Φ cost s) :=
  fun _ _ h ↦ OrderHomClass.GCongr.mono OrderHom.lfp (Φ.monotone' M h) s

section FiniteBranching

variable [DecidableEq State] [M.FiniteBranching]

theorem Φf.ωScottContinuous (s) (a) : ωScottContinuous (M.Φf s a) := by
  refine ωScottContinuous.of_monotone_map_ωSup ?_
  use OrderHom.monotone (M.Φf s a)
  simp [Φf]
  intro c
  simp [ωSup, tsum_fintype, ENNReal.mul_iSup]
  refine ENNReal.finsetSum_iSup_of_monotone ?h.hf
  intro S i₁ i₂ h
  simp
  gcongr
  exact OrderHomClass.GCongr.mono c h S

theorem Φ.ωScottContinuous (cost : M.Costs) : ωScottContinuous (M.Φ cost) := by
  refine ωScottContinuous.of_map_ωSup_of_orderHom ?_
  intro c
  ext s
  unfold Φ
  simp [ωSup]
  simp [← ENNReal.add_iSup]
  congr
  have := (Φf.ωScottContinuous M s · |>.map_ωSup)
  simp_all [ωSup]
  refine Eq.symm (Set.iSup_iInf_of_monotone ?h.e_a.hf)
  intro α i₁ i₂ h
  apply (M.Φf s α).mono <| OrderHomClass.GCongr.mono c h

theorem Φ𝒮.ωScottContinuous (cost : M.Costs) : ωScottContinuous (M.Φ𝒮 cost 𝒮) := by
  refine ωScottContinuous.of_map_ωSup_of_orderHom ?_
  intro c
  ext s
  unfold Φ𝒮
  simp [ωSup]
  simp [← ENNReal.add_iSup]
  congr
  have := (Φf.ωScottContinuous M s · |>.map_ωSup)
  simp_all [ωSup]

theorem lfp_Φ_eq_iSup'_Φ : M.lfp_Φ = M.iSup'_Φ := by
  funext c
  exact fixedPoints.lfp_eq_sSup_iterate _ (Φ.ωScottContinuous M c)

theorem lfp_Φ𝒮_eq_iSup_Φ𝒮 : M.lfp_Φ𝒮 = fun cost 𝒮 ↦ ⨆ n, (M.Φ𝒮 cost 𝒮)^[n] ⊥ := by
  funext c 𝒮
  exact fixedPoints.lfp_eq_sSup_iterate _ (Φ𝒮.ωScottContinuous M c)

theorem lfp_Φ𝒮_eq_iSup_succ_Φ𝒮 : M.lfp_Φ𝒮 = fun cost 𝒮 ↦ ⨆ n, (M.Φ𝒮 cost 𝒮)^[n + 1] ⊥ := by
  funext c 𝒮
  rw [lfp_Φ𝒮_eq_iSup_Φ𝒮, iSup_iterate_succ]

theorem lfp_Φ_eq_iSup_Φ : M.lfp_Φ = M.iSup_Φ := M.lfp_Φ_eq_iSup'_Φ.trans M.iSup_Φ_eq_iSup'_Φ.symm

theorem iSup_Φ_step (cost : M.Costs) : M.Φ cost (M.iSup_Φ cost) = M.iSup_Φ cost := by
  rw [←lfp_Φ_eq_iSup_Φ]
  exact M.lfp_Φ_step cost

theorem iSup_Φ_step' (cost : M.Costs) (s : State) :
    M.iSup_Φ cost s
  = cost s + ⨅ a : M.act s, ∑' s' : M.succs_univ s, M.P s a s' * M.iSup_Φ cost s'
:= by
  rw [←lfp_Φ_eq_iSup_Φ]
  exact M.lfp_Φ_step' cost s
