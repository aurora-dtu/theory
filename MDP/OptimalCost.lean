import MDP.Bellman
import MDP.BScheduler

open OrderHom

namespace MDP

variable {State : Type*} {Act : Type*}
variable {M : MDP State Act}

noncomputable def EC (c : M.Costs) (𝒮 : 𝔖[M]) (n : ℕ) (s : State) :=
  ∑' π : Path[M,s,=n], π.val.ECost c 𝒮

noncomputable abbrev OEC (c : M.Costs) (s : State) := ⨅ 𝒮 : 𝔖[M], ⨆ n : ℕ, M.EC c 𝒮 n s

@[simp]
theorem EC_zero : M.EC c 𝒮 0 = 0 := by ext; simp [EC]
@[simp]
theorem EC_one : M.EC c 𝒮 1 = c := by
  ext
  simp [EC, Path.ECost, Path.Cost, Path.Prob, Path.instSingleton]
  simp only [Path.length]
  simp
@[simp]
theorem EC_one' : M.EC c 𝒮 1 s = c s := by simp

theorem EC_le_succ [DecidableEq State] : M.EC c 𝒮 n s ≤ M.EC c 𝒮 (n + 1) s := by
  rcases n with _ | n <;> simp [EC]
  rw [Path_eq.eq_biUnion_succs_univ, ENNReal.tsum_biUnion]
  · gcongr with π
    obtain ⟨π, h, _, _⟩ := π
    rw [Path.succs_univ_eq_extend_range, Set.range_eq_iUnion, ENNReal.tsum_biUnion]
    · simp
      simp [Path.ECost, Path.extend_Cost, Path.extend_Prob]
      conv => right; arg 1; ext; rw [mul_comm, mul_assoc, mul_add, mul_add]
      simp [tsum_add, ENNReal.tsum_mul_right]
      apply le_add_right
      simp [mul_comm]
    · intro ⟨x, _⟩ _ ⟨y, _⟩ _ h
      simp_all
      contrapose h
      simp_all
      have := congrArg Path.last h
      simp at this
      exact this
  · intro ⟨_, _⟩ _ ⟨_, _⟩ _ _; apply Path_eq.succs_univ_disjoint M (s:=s) (n:=n+1) <;> simp_all

theorem EC_monotone [DecidableEq State] : Monotone (M.EC c 𝒮 · s) := by
  intro n m h
  induction m, h using Nat.le_induction with
  | base => rfl
  | succ n' h ih => exact ih.trans EC_le_succ

theorem EC_succ [DecidableEq State] (𝒮 : 𝔖[M]) :
    EC c 𝒮 (n + 1) = c + fun s ↦ ∑' s' : M.succs_univ s, M.P s (𝒮 {s}) s' * EC c 𝒮[s ↦ s'] n s'
:= by
  ext s
  rcases n with _ | n
  · simp_all
  · simp [← M.succs_tsum_add_left (s:=s) (α:=𝒮 {s}) (by simp), EC]
    rw [Path_eq.eq_succs_univ_biUnion, ENNReal.tsum_biUnion M.Path_eq_follows_disjoint]
    congr! 2 with s'
    simp [← Path_eq.tsum_add_left (𝒮:=𝒮[s ↦ s']), ← ENNReal.tsum_mul_left]
    apply tsum_eq_tsum_of_ne_zero_bij fun ⟨π, _⟩ ↦ ⟨π.val.prepend ⟨s, by simp⟩, by simp⟩
    · intro ⟨⟨a, _, ha⟩, _⟩ ⟨⟨b, _, hb⟩, _⟩ h
      simp_all
      apply (Path.prepend_inj_right _ _ (by simp_all)).mp h
    · simp_all
      intro π ⟨_, _⟩ _ _; subst_eqs
      use π.tail
      simp_all [Path.prepend_ECost, Path.ECost_tail, or_comm]
    · simp_all [Path.prepend_ECost]; intros; ring
theorem EC_eq (h : ∀ π ∈ Path[M,s,≤n], 𝒮 π = 𝒮' π) : EC c 𝒮 n s = EC c 𝒮' n s := by
  simp_all [EC, Path.ECost, Path.Prob]
theorem EC_le (h : ∀ π ∈ Path[M,s,≤n], 𝒮 π = 𝒮' π) : EC c 𝒮 n s ≤ EC c 𝒮' n s := (EC_eq h).le

variable [DecidableEq State]

@[simp]
theorem EC_markovian_scheduler_specialize {𝒮 : 𝔖[M]} [𝒮.Markovian] :
    M.EC c 𝒮[s₀ ↦ s] n s = M.EC c 𝒮 n s := EC_eq (by simp_all [𝒮.MarkovianOn])

theorem bound_EC_succ_eq_bound_EC (s : State) (s' : M.succs_univ s) :
    ⨅ ℬ : 𝔖[M,s,≤n+1], EC c ℬ[s ↦ s'].val n s' = ⨅ ℬ : 𝔖[M,s',≤n], EC c ℬ.val n s'
:= Function.Surjective.iInf_congr (·[s ↦ s']) (by use ·.cast_arb_tail; simp) (fun _ ↦ rfl)

theorem iInf_EC_specialized_eq_bounded (s : State) (s' : M.succs_univ s) :
    ⨅ 𝒮 : 𝔖[M], EC c 𝒮[s ↦ s'] n s' = ⨅ ℬ : 𝔖[M,s,≤n+1], EC c ℬ[s ↦ s'].val n s'
:= Function.Surjective.iInf_congr (·.bound) (by use ·.val; ext; simp_all)
  (fun _ ↦ EC_eq fun _ _ ↦ by simp; split_ifs <;> simp_all)

theorem iInf_scheduler_eq_iInf_act_iInf_scheduler :
    ⨅ 𝒮 : 𝔖[M], ∑' s' : M.succs_univ s, M.P s (𝒮 {s}) s' * EC c 𝒮[s ↦ s'] n s'
  = ⨅ α : M.act s, ⨅ 𝒮 : 𝔖[M], ∑' s' : M.succs_univ s, M.P s α s' * EC c 𝒮[s ↦ s'] n s'
:= le_antisymm
  (le_iInf₂ fun α 𝒮 ↦ iInf_le_of_le
    ⟨fun π ↦ if ‖π‖ = 1 ∧ π[0] = s then α else 𝒮 π, fun π ↦ by
      simp only; split_ifs <;> simp_all [Path.last, -Path.getElem_length_pred_eq_last]⟩
    (ENNReal.tsum_le_tsum fun _ ↦ mul_le_mul (by simp) (EC_le (by simp)) (by simp) (by simp)))
  (le_iInf fun 𝒮 ↦ iInf₂_le_of_le ⟨𝒮 {s}, by simp⟩ 𝒮 (by rfl))

variable [M.FiniteBranching] in
theorem tsum_iInf_bounded_comm (f : (s' : M.succs_univ s) → 𝔖[M,s',≤n] → ENNReal) :
    ∑' s' : M.succs_univ s, ⨅ ℬ : 𝔖[M,s',≤n], f s' ℬ
  = ⨅ ℬ : 𝔖[M,s,≤n+1], ∑' s' : M.succs_univ s, f s' ℬ[s ↦ s']
:= by
  apply le_antisymm (le_iInf_iff.mpr fun ℬ ↦ ENNReal.tsum_le_tsum (iInf_le_of_le ℬ[s ↦ ·] (by rfl)))
  apply iInf_le_of_le <| BScheduler.mk' (M:=M) s (n+1) (fun ⟨π, hπ⟩ ↦
      if h : ‖π‖ ≤ 1 then M.default_act π.last
      else BScheduler.elems.argmin (by simp) (f ⟨π[1], by simp [← hπ.right]⟩) π.tail)
    (fun _ ↦ by simp_all; split <;> simp)
  gcongr with s'
  simp
  convert fun ℬ ↦ (le_of_eq_of_le (c:=f s' ℬ) <| congrArg _ <| BScheduler.mk'_argmin s s' (f s')) _
  all_goals try simp_all only [implies_true, Path_le.first_le]
  simp [← BScheduler.elems.argmin_spec (by simp) (f s') |>.right]; use ℬ

variable [M.FiniteBranching] in
theorem tsum_iInf_EC_comm :
    ∑' s' : M.succs_univ s, ⨅ 𝒮 : 𝔖[M], M.P s α s' * EC c 𝒮[s ↦ s'] n s'
  = ⨅ 𝒮 : 𝔖[M], ∑' s' : M.succs_univ s, M.P s α s' * EC c 𝒮[s ↦ s'] n s'
:= by
  convert tsum_iInf_bounded_comm fun s' ℬ ↦ M.P s α s' * EC c ℬ.val n s'
  · simp [← ENNReal.mul_iInf, iInf_EC_specialized_eq_bounded, bound_EC_succ_eq_bound_EC]; rfl
  · apply Function.Surjective.iInf_congr (·.bound) (by use ·.val; ext; simp_all [Scheduler.bound])
    congr! 3; exact EC_eq (by simp_all)

theorem iInf_EC_eq_specialized (s : State) (s' : M.succs_univ s) :
    ⨅ 𝒮, EC c 𝒮 n s' = ⨅ 𝒮 : 𝔖[M], EC c 𝒮[s ↦ s'] n s' :=
  (le_iInf_comp _ _).antisymm (le_iInf (iInf_le_of_le ⟨· ∘ .tail, by simp⟩ (EC_le (by simp_all))))

theorem iInf_EC_succ_eq_Φ [M.FiniteBranching] : ⨅ 𝒮, EC c 𝒮 (n + 1) = M.Φ c (⨅ 𝒮, EC c 𝒮 n) :=
  by ext; simp [EC_succ, Φ, Φf, ← ENNReal.add_iInf, iInf_EC_eq_specialized, ENNReal.mul_iInf,
      tsum_iInf_EC_comm, iInf_scheduler_eq_iInf_act_iInf_scheduler]

theorem iInf_EC_eq_Φ [M.FiniteBranching] : ⨅ 𝒮, EC c 𝒮 n = (M.Φ c)^[n] ⊥ := by
  induction n with
  | zero => simp [EC, Path.ECost, Path.Cost]; rfl
  | succ n ih => rw [Function.iterate_succ']; simp [ih, iInf_EC_succ_eq_Φ]

theorem iSup_iInf_EC_eq_iSup_Φ [M.FiniteBranching] : ⨆ n, ⨅ 𝒮, EC c 𝒮 n = ⨆ n, (M.Φ c)^[n] ⊥ :=
  by simp_all [iInf_EC_eq_Φ]

theorem iSup_iInf_EC_eq_lfp_Φ [M.FiniteBranching] : ⨆ n, ⨅ 𝒮, EC c 𝒮 n = M.lfp_Φ c := by
  simp [lfp_Φ_eq_iSup_Φ, iInf_EC_eq_Φ]

theorem Φℒ_step_ECℒ (c : M.Costs) (ℒ : 𝔏[M]) :
    EC c ℒ (n + 1) = Φℒ ℒ c (EC c ℒ n) := by
  induction n with
  | zero => ext; simp [EC_succ, Φℒ, Φf]
  | succ n ih =>
    simp [ih, EC_succ]
    simp [EC, Path.ECost, Path.Cost, Path.Prob, MScheduler.markovian, Φℒ, Φf]
    rfl

attribute [-simp] Function.iterate_succ in
theorem iSup_ECℒ_eq_lfp_Φℒ (ℒ : 𝔏[M]) [M.FiniteBranching] :
    (⨆ n, EC c ℒ n) = lfp_Φℒ ℒ c := by
  simp [lfp_Φℒ_eq_iSup_Φℒ]
  congr! with n
  induction n generalizing ℒ with
  | zero => simp [Φℒ, Φf]; rfl
  | succ n ih => simp [Φℒ_step_ECℒ, ih, Function.iterate_succ']

noncomputable def ℒ' [M.FiniteBranching] (c : M.Costs) : 𝔏[M] :=
  ⟨⟨fun π ↦ (M.act π.last).toFinset.argmin (M.act₀_nonempty _) (M.Φf π.last · (lfp_Φ c)), by simp⟩,
    by constructor; simp [Scheduler.IsMarkovian]⟩

noncomputable def ℒ'_spec [M.FiniteBranching] (c : M.Costs) (s : State) :
  ⨅ α : M.act s, M.Φf s α (lfp_Φ c) = (Φf s · (lfp_Φ c)) (ℒ' c {s})
:= by
  convert Finset.argmin_spec (M.act s).toFinset (act₀_nonempty M s) (Φf s · (lfp_Φ c)) |>.right
  simp [Finset.inf'_eq_inf, Finset.inf_eq_iInf, iInf_subtype]

omit [DecidableEq State] in
theorem lfp_Φℒ_eq_lfp_Φ [M.FiniteBranching] : M.lfp_Φℒ (ℒ' c) c = lfp_Φ c := by
  apply le_antisymm
  · apply lfp_le
    nth_rw 2 [← map_lfp_Φ]
    simp [Φℒ, Φ]
    congr! 2 with s
    exact M.ℒ'_spec c s |>.symm
  · refine lfp_le _ fun s ↦ ?_
    nth_rw 2 [← map_lfp_Φℒ]
    apply M.Φ_le_Φℒ

attribute [-simp] Function.iterate_succ in
theorem iSup_iInf_EC_eq_iInf_iSup_EC [M.FiniteBranching] :
    ⨆ n, ⨅ 𝒮 : 𝔖[M], EC c 𝒮 n = ⨅ 𝒮 : 𝔖[M], ⨆ n, EC c 𝒮 n := by
  apply le_antisymm (iSup_iInf_le_iInf_iSup _) (iInf_le_of_le ↑(M.ℒ' c) _)
  simp [iSup_ECℒ_eq_lfp_Φℒ, iSup_iInf_EC_eq_lfp_Φ, lfp_Φℒ_eq_lfp_Φ]

theorem iInf_iSup_EC_eq_iInf_iSup_ECℒ [M.FiniteBranching] :
    ⨅ 𝒮 : 𝔖[M], ⨆ n, EC c 𝒮 n = ⨅ ℒ : 𝔏[M], ⨆ n, EC c ℒ n := by
  simp [← iSup_iInf_EC_eq_iInf_iSup_EC, iSup_iInf_EC_eq_lfp_Φ, iSup_ECℒ_eq_lfp_Φℒ]
  apply le_antisymm
  · refine le_iInf fun ℒ ↦ ?_
    apply lfp_le
    nth_rw 2 [← map_lfp_Φℒ]
    apply Φ_le_Φℒ
  · rw [← M.lfp_Φℒ_eq_lfp_Φ]
    apply iInf_le

omit [DecidableEq State] in
theorem iSup_iInf_EC_le_iSup_iInf_ECℒ :
    ⨆ n, ⨅ 𝒮 : 𝔖[M], EC c 𝒮 n ≤ ⨆ n, ⨅ ℒ : 𝔏[M], EC c ℒ n :=
  iSup_mono fun _ ↦ le_iInf_comp _ _

theorem iSup_iInf_ECℒ_eq_iInf_iSup_ECℒ [M.FiniteBranching] :
    ⨆ n, ⨅ ℒ : 𝔏[M], EC c ℒ n = ⨅ ℒ : 𝔏[M], ⨆ n, M.EC c ℒ n := by
  apply le_antisymm (iSup_iInf_le_iInf_iSup _) (le_of_eq_of_le _ iSup_iInf_EC_le_iSup_iInf_ECℒ)
  simp [iInf_iSup_EC_eq_iInf_iSup_ECℒ, iSup_iInf_EC_eq_iInf_iSup_EC]

theorem iInf_iSup_EC_eq_lfp_Φ [M.FiniteBranching] :
    ⨅ 𝒮 : 𝔖[M], ⨆ n, EC c 𝒮 n = M.lfp_Φ c := by
  simp [← iSup_iInf_EC_eq_lfp_Φ, iSup_iInf_EC_eq_iInf_iSup_EC]

end MDP
