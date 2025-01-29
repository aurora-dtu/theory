import MDP.Paths.Cost
import MDP.Measure
import MDP.Bellman
import MDP.FinsetExt

namespace MDP

variable {State : Type*} {Act : Type*}
variable {M : MDP State Act}

theorem Path_eq.tsum_add_left (𝒮 : M.Scheduler') (f : Path[M,s',=n] → ENNReal) :
    ∑' π : Path[M,s',=n], (π.val.Prob 𝒮 * a + f π) = a + ∑' π : Path[M,s',=n], f π
:= by
  simp [ENNReal.tsum_add, ENNReal.tsum_mul_right, tsum_Prob_eq_one]

theorem succs_tsum_add_left (𝒮 : M.Scheduler') (f : M.succs_univ s → ENNReal) :
    ∑' s' : M.succs_univ s, (M.P s (𝒮 {s}) s' * a + f s') = a + ∑' s' : M.succs_univ s, f s'
:= by
  simp [ENNReal.tsum_add, ENNReal.tsum_mul_right, tsum_Prob_eq_one]

@[simp]
theorem EC_zero : M.EC c 𝒮 s 0 = c s := by
  simp [EC, Path.ECost, Path.Cost, Path.Prob, Path.instSingleton]
  simp only [Path.length]
  simp

theorem EC_succ [DecidableEq State] (𝒮 : M.Scheduler') :
    EC c 𝒮 s (n + 1) = c s + ∑' s' : M.succs_univ s, M.P s (𝒮 {s}) s' * EC c 𝒮[s ↦ s'] s' n := by
  simp [← succs_tsum_add_left 𝒮, EC]
  rw [Path_eq.eq_succs_univ_biUnion', ENNReal.tsum_biUnion M.Path_eq_follows_disjoint]
  congr! 2 with s'
  simp [← Path_eq.tsum_add_left 𝒮[s ↦ s'], ← ENNReal.tsum_mul_left]
  apply tsum_eq_tsum_of_ne_zero_bij fun ⟨π, _⟩ ↦ ⟨π.val.prepend ⟨s, by simp⟩, by simp⟩
  · intro ⟨⟨a, _, ha⟩, _⟩ ⟨⟨b, _, hb⟩, _⟩ h
    simp_all
    apply (Path.prepend_inj_right _ _ (by simp_all)).mp h
  · simp_all
    intro π ⟨_, _⟩ _ _; subst_eqs
    use π.tail
    simp_all [Path.prepend_ECost, Path.ECost_tail, or_comm]
  · simp_all [Path.prepend_ECost]; intros; ring
theorem EC_eq (h : ∀ π ∈ Path[M,s,≤n], 𝒮 π = 𝒮' π) : EC c 𝒮 s n = EC c 𝒮' s n := by
  simp_all [EC, Path.ECost, Path.Prob]
theorem EC_le (h : ∀ π ∈ Path[M,s,≤n], 𝒮 π = 𝒮' π) : EC c 𝒮 s n ≤ EC c 𝒮' s n := (EC_eq h).le

variable [DecidableEq State]

theorem EC_eq_bound (s : State) (s' : M.succs_univ s) :
    ⨅ 𝒮, EC c 𝒮 s' n = ⨅ 𝒮 : M.Scheduler', EC c (𝒮.bound (s:=s') (n:=n)).val s' n := by
  congr with 𝒮
  apply EC_eq fun _ _ ↦ by simp_all [Scheduler'.bound]
theorem EC_bound_eq_bound_EC (s : State) (s' : M.succs_univ s) :
    ⨅ 𝒮 : M.Scheduler', EC c (𝒮.bound (s:=s') (n:=n)).val s' n
  = ⨅ 𝒮 : M.BScheduler' s' n, EC c 𝒮.val s' n
:= Function.Surjective.iInf_congr (·.bound) (by use ·.val; ext _ h; simp [h]) (fun _ ↦ rfl)
theorem bound_EC_succ_eq_bound_EC (s : State) (s' : M.succs_univ s) :
    ⨅ 𝒮 : M.BScheduler' s (n + 1), EC c 𝒮[s ↦ s'].val s' n
  = ⨅ 𝒮 : M.BScheduler' s' n, EC c 𝒮.val s' n
:= Function.Surjective.iInf_congr (·[s ↦ s']) (by use ·.cast_arb_tail; simp) (fun _ ↦ rfl)

theorem iInf_EC_specialized_eq_bounded (s : State) (s' : M.succs_univ s) :
    ⨅ 𝒮 : M.Scheduler', EC c 𝒮[s ↦ s'] (↑s') n
  = ⨅ 𝒮 : M.BScheduler' s (n + 1), EC c 𝒮[s ↦ s'].val (↑s') n
:= Function.Surjective.iInf_congr (·.bound) (by use ·.val; ext π hπ; simp_all)
  (fun _ ↦ EC_eq fun _ _ ↦ by simp; split_ifs <;> simp_all)
theorem iInf_EC_eq_specialized (s : State) (s' : M.succs_univ s) :
    ⨅ 𝒮, EC c 𝒮 s' n = ⨅ 𝒮 : M.Scheduler', EC c 𝒮[s ↦ s'] s' n := by
  rw [EC_eq_bound, EC_bound_eq_bound_EC, iInf_EC_specialized_eq_bounded, bound_EC_succ_eq_bound_EC]

theorem iInf_scheduler_eq_iInf_act_iInf_scheduler :
    ⨅ 𝒮 : M.Scheduler', ∑' s' : M.succs_univ s, M.P s (𝒮 {s}) s' * EC c 𝒮[s ↦ s'] s' n
  = ⨅ α : M.act s, ⨅ 𝒮 : M.Scheduler', ∑' s' : M.succs_univ s, M.P s α s' * EC c 𝒮[s ↦ s'] s' n
:= by
  apply le_antisymm
  · apply le_iInf_iff.mpr fun α ↦ le_iInf_iff.mpr fun 𝒮 ↦ ?_
    apply iInf_le_of_le ⟨fun π ↦ if ∎|π| = 1 ∧ π[0] = s then α else 𝒮 π, fun π ↦ by
      simp only; split_ifs <;> simp_all only [Path.last, Subtype.coe_prop, Scheduler'.mem_act_if]⟩
    simp
    gcongr
    exact EC_le fun _ _ ↦ by simp
  · apply le_iInf_iff.mpr fun 𝒮 ↦ iInf_le_of_le ⟨𝒮 {s}, by simp⟩ ?_
    apply iInf_le_of_le 𝒮 (by rfl)

variable [M.FiniteBranching] in
theorem tsum_iInf_bounded_comm (f : (s' : M.succs_univ s) → M.BScheduler' s' n → ENNReal) :
    ∑' s' : M.succs_univ s, ⨅ ℬ : M.BScheduler' s' n, f s' ℬ
  = ⨅ ℬ : M.BScheduler' s (n + 1), ∑' s' : M.succs_univ s, f s' ℬ[s ↦ s']
:= by
  apply le_antisymm (le_iInf_iff.mpr fun ℬ ↦ ENNReal.tsum_le_tsum (iInf_le_of_le ℬ[s ↦ ·] (by rfl)))
  apply iInf_le_of_le <| BScheduler'.mk' (M:=M) s (n+1) (fun ⟨π, hπ⟩ ↦
      if h : ∎|π| ≤ 1 then M.default_act π.last
      else BScheduler'.elems.argmin (by simp) (f ⟨π[1], by simp [← hπ.right]⟩) π.tail)
    (fun _ ↦ by simp_all; split <;> simp)
  gcongr with s'
  simp
  convert fun ℬ ↦ (le_of_eq_of_le (c:=f s' ℬ) <| congrArg _ <| BScheduler'.mk'_argmin s s' (f s')) _
  all_goals try simp_all only [implies_true, Path_le.first_le]
  simp [← BScheduler'.elems.argmin_spec (by simp) (f s') |>.right]; use ℬ

variable [M.FiniteBranching] in
theorem tsum_iInf_EC_comm :
    ∑' s' : M.succs_univ s, ⨅ 𝒮 : M.Scheduler', M.P s α s' * EC c 𝒮[s ↦ s'] s' n
  = ⨅ 𝒮 : M.Scheduler', ∑' s' : M.succs_univ s, M.P s α s' * EC c 𝒮[s ↦ s'] s' n
:= by
  convert tsum_iInf_bounded_comm fun s' ℬ ↦ M.P s α s' * EC c ℬ.val s' n
  · simp [← ENNReal.mul_iInf, iInf_EC_specialized_eq_bounded, bound_EC_succ_eq_bound_EC]; rfl
  · apply Function.Surjective.iInf_congr (·.bound) (by use ·.val; ext; simp_all [Scheduler'.bound])
    congr! 3; exact EC_eq fun _ _ ↦ by simp_all

theorem iInf_EC_succ_eq_Φ [M.FiniteBranching] : ⨅ 𝒮, EC c 𝒮 s (n + 1) = M.Φ c (⨅ 𝒮, EC c 𝒮 · n) s :=
  by simp [EC_succ, Φ, Φf, ← ENNReal.add_iInf, iInf_EC_eq_specialized, ENNReal.mul_iInf,
      tsum_iInf_EC_comm, iInf_scheduler_eq_iInf_act_iInf_scheduler]

theorem iInf_EC_eq_Φ [M.FiniteBranching] : ⨅ 𝒮, EC c 𝒮 s n = (M.Φ c)^[n + 1] ⊥ s := by
  induction n generalizing s with
  | zero =>
    simp [EC, Path.ECost, Path.Cost]
    simp [Path.instSingleton, Φ, Φf]
  | succ n ih =>
    rw [Function.iterate_succ']
    simp [ih, iInf_EC_succ_eq_Φ]

theorem iSup_iInf_EC_eq_iSup_Φ [M.FiniteBranching] : ⨆ n, ⨅ 𝒮, EC c 𝒮 s n = ⨆ n, (M.Φ c)^[n] ⊥ s :=
  by simp [iInf_EC_eq_Φ, iSup_iterate_succ', -Function.iterate_succ]

theorem iSup_iInf_EC_eq_lfp_Φ [M.FiniteBranching] : ⨆ n, ⨅ 𝒮, EC c 𝒮 s n = M.lfp_Φ c s := by
  simp [lfp_Φ_eq_iSup_Φ, iSup_Φ, iInf_EC_eq_Φ]

theorem iSup_iInf_EC_eq_lfp_Φ' [M.FiniteBranching] : (⨆ n, ⨅ 𝒮, EC c 𝒮 · n) = M.lfp_Φ c := by
  simp [iSup_iInf_EC_eq_lfp_Φ]

theorem Φ𝒮_step_EC' (c : M.Costs) (𝒮 : M.Scheduler) :
    M.EC c 𝒮 s (n + 1) = M.Φ𝒮 c 𝒮 (M.EC c 𝒮 · n) s := by
  induction n generalizing s with
  | zero => simp [EC_succ]; rfl
  | succ n ih =>
    simp [ih, EC_succ]; clear ih
    simp [EC, Path.ECost, Path.Cost, Path.Prob, Scheduler.markovian, Φ𝒮, Φf,
      Scheduler'.Markovian_path_take''']

attribute [-simp] Function.iterate_succ in
theorem iSup_n_EC'_eq_lfp_Φ𝒮 (𝒮 : M.Scheduler) [M.FiniteBranching] :
    (⨆ n, M.EC c 𝒮 s n) = M.lfp_Φ𝒮 c 𝒮 s := by
  simp [lfp_Φ𝒮_eq_iSup_succ_Φ𝒮]
  congr with n
  induction n generalizing s 𝒮 with
  | zero => simp [Φ𝒮, Φf]
  | succ n ih => simp [Φ𝒮_step_EC', ih, Function.iterate_succ']

noncomputable def 𝒮' [M.FiniteBranching] (c : M.Costs) : M.Scheduler :=
  ⟨Scheduler'.mk' fun π ↦ ⟨
    (M.act π.last).toFinset.argmin (M.act₀_nonempty π.last) (M.Φf π.last · (M.lfp_Φ c)), by simp⟩,
    by constructor; simp⟩

noncomputable def 𝒮'_spec [M.FiniteBranching] (c : M.Costs) (s : State) :
  ⨅ α : M.act s, M.Φf s α (M.lfp_Φ c) = (M.Φf s · (M.lfp_Φ c)) (M.𝒮' c {s})
:= by
  convert Finset.argmin_spec (M.act s).toFinset (act₀_nonempty M s) (M.Φf s · (M.lfp_Φ c)) |>.right
  simp [Finset.inf'_eq_inf, Finset.inf_eq_iInf, iInf_subtype]

omit [DecidableEq State] in
theorem lfp_Φ𝒮_eq_lfp_Φ [M.FiniteBranching] : M.lfp_Φ𝒮 c (𝒮' c) = M.lfp_Φ c := by
  apply le_antisymm
  · apply OrderHom.lfp_le
    nth_rw 2 [← lfp_Φ_step]
    simp [Φ𝒮, Φ]
    congr! 2 with s
    exact M.𝒮'_spec c s |>.symm
  · apply OrderHom.lfp_le
    intro s
    nth_rw 2 [← lfp_Φ𝒮_step]
    apply M.Φ_le_Φ𝒮

attribute [-simp] Function.iterate_succ in
theorem iSup_iInf_EC_eq_iInf_iSup_EC [M.FiniteBranching] :
    ⨆ n, ⨅ 𝒮 : M.Scheduler', M.EC c 𝒮 s n = ⨅ 𝒮 : M.Scheduler', ⨆ n, M.EC c 𝒮 s n := by
  apply le_antisymm (iSup_iInf_le_iInf_iSup _)
  suffices ∃ (𝒮' : M.Scheduler), ⨆ n, M.EC c 𝒮' s n = ⨆ n, ⨅ 𝒮 : M.Scheduler', EC c 𝒮 s n by
    obtain ⟨𝒮', h⟩ := this
    simp [← h, iInf_le]
  use M.𝒮' c
  simp [iSup_n_EC'_eq_lfp_Φ𝒮, iSup_iInf_EC_eq_lfp_Φ, lfp_Φ𝒮_eq_lfp_Φ]

theorem iInf_iSup_EC_eq_iInf_iSup_EC' [M.FiniteBranching] :
    ⨅ 𝒮 : M.Scheduler', ⨆ n, M.EC c 𝒮 s n = ⨅ 𝒮 : M.Scheduler, ⨆ n, M.EC c 𝒮 s n := by
  rw [← iSup_iInf_EC_eq_iInf_iSup_EC, iSup_iInf_EC_eq_lfp_Φ]
  simp [iSup_n_EC'_eq_lfp_Φ𝒮]
  apply le_antisymm
  · refine le_iInf fun 𝒮 ↦ ?_
    suffices M.lfp_Φ c ≤ M.lfp_Φ𝒮 c 𝒮 by exact this s
    apply OrderHom.lfp_le
    nth_rw 2 [← lfp_Φ𝒮_step]
    apply Φ_le_Φ𝒮
  · rw [← M.lfp_Φ𝒮_eq_lfp_Φ]
    apply iInf_le

omit [DecidableEq State] in
theorem iSup_iInf_EC_le_iSup_iInf_EC' :
    ⨆ n, ⨅ 𝒮 : M.Scheduler', M.EC c 𝒮 s n ≤ ⨆ n, ⨅ 𝒮 : M.Scheduler, M.EC c 𝒮 s n :=
  iSup_mono fun _ ↦ le_iInf_comp _ _

theorem iSup_iInf_EC'_eq_iInf_iSup_EC' [M.FiniteBranching] :
    ⨆ n, ⨅ 𝒮 : M.Scheduler, M.EC c 𝒮 s n = ⨅ 𝒮 : M.Scheduler, ⨆ n, M.EC c 𝒮 s n := by
  apply le_antisymm (iSup_iInf_le_iInf_iSup _) (le_of_eq_of_le _ iSup_iInf_EC_le_iSup_iInf_EC')
  simp [iInf_iSup_EC_eq_iInf_iSup_EC', iSup_iInf_EC_eq_iInf_iSup_EC]

theorem iInf_iSup_EC_eq_lfp_Φ [M.FiniteBranching] :
    ⨅ 𝒮 : M.Scheduler', ⨆ n, M.EC c 𝒮 s n = M.lfp_Φ c s := by
  simp [← iSup_iInf_EC_eq_lfp_Φ, iSup_iInf_EC_eq_iInf_iSup_EC]

theorem Complete [M.FiniteBranching] :
  let S: Set ENNReal := {
    ⨆ n, ⨅ 𝒮 : M.Scheduler', M.EC c 𝒮 s n,
    ⨆ n, ⨅ 𝒮 : M.Scheduler, M.EC c 𝒮 s n,
    ⨅ 𝒮 : M.Scheduler', ⨆ n, M.EC c 𝒮 s n,
    ⨅ 𝒮 : M.Scheduler, ⨆ n, M.EC c 𝒮 s n,
    M.lfp_Φ c s
  }
  ∀ v₁ v₂ : S, v₁ = v₂
:= by
  simp
  simp only [iSup_iInf_EC_eq_iInf_iSup_EC, iInf_iSup_EC_eq_iInf_iSup_EC',
    iSup_iInf_EC'_eq_iInf_iSup_EC', ← iSup_iInf_EC_eq_lfp_Φ, and_self]

end MDP
