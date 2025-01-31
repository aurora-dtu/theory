import PGCL.SmallStep

namespace pGCL

variable {ϖ : Type*} [DecidableEq ϖ]

noncomputable def OMDP : MDP (Conf ϖ) Act :=
  MDP.ofRelation SmallStep SmallStep.p_ne_zero SmallStep.sums_to_one SmallStep.progress

namespace OMDP

@[simp]
theorem act_eq : OMDP.act = SmallStep.act (ϖ:=ϖ) := by
  ext c α
  simp [OMDP, MDP.ofRelation_act, SmallStep.act]

@[simp]
theorem succs_univ_eq : (OMDP (ϖ:=ϖ)).succs_univ = fun c ↦ {c' | ∃ α p, c ⤳[α,p] c'} := by
  simp [OMDP]

@[simp]
theorem P_eq : (OMDP (ϖ:=ϖ)).P = (fun c α c' ↦ ∑' (p : { p // c ⤳[α,p] c' }), ↑p) := by simp [OMDP]

theorem P_support_eq_succs : (Function.support (OMDP.P c α)) = SmallStep.succs (ϖ:=ϖ) c α := by
  ext c'
  simp [SmallStep.succs]
  constructor
  · simp; intro p h hp; use p
  · simp; intro p h; use p, h, SmallStep.p_ne_zero h

instance : MDP.FiniteBranching (OMDP (ϖ:=ϖ)) where
  act_fin c := Set.toFinite (OMDP.act c)
  succs_fin c α := by
    simp only [OMDP.P_support_eq_succs, SmallStep.succs_eq_succs_fin, Finset.finite_toSet]

@[simp]
noncomputable def cost (X : Exp ϖ)
  | ·⟨⇓ ϖ, σ⟩ => X σ
  | ·⟨tick r, σ⟩ => r σ
  | ·⟨c' ; _, σ⟩ => cost X (·⟨c', σ⟩)
  | _ => 0

@[simp] theorem cost_X_of_pGCL : cost X (·⟨C, σ⟩) = cost 0 (·⟨C, σ⟩) := by induction C <;> simp_all

@[simp]
theorem Φ_simp {C : Conf ϖ} :
    OMDP.Φ c f C = c C + ⨅ α ∈ SmallStep.act C, ∑' s' : OMDP.succs_univ C, OMDP.P C α s' * f s'
:= by simp [MDP.Φ, MDP.Φf, iInf_subtype]

@[simp]
theorem bot_eq {X : Exp ϖ} : (OMDP.Φ (cost X))^[i] ⊥ none = 0 := by
  induction i <;> simp_all [-Function.iterate_succ, Function.iterate_succ']

noncomputable instance : Decidable (s' ∈ (OMDP (ϖ:=ϖ)).succs_univ s) := Classical.propDecidable _

theorem tsum_succs_univ' (f : (OMDP (ϖ:=ϖ)).succs_univ c → ENNReal) :
    (∑' s', f s') = ∑' s', if h : _ then f ⟨s', h⟩ else 0 := by
  symm
  apply tsum_eq_tsum_of_ne_zero_bij (↑↑·) _ _ (by simp_all)
  · intro ⟨_, _⟩ ⟨_, _⟩; simp; apply SetCoe.ext
  · simp_all; intro _ α p _ _; use α, p

variable {X : Exp ϖ}

@[simp]
theorem sink_eq : (OMDP.Φ (cost X))^[i] ⊥ (some (none, σ)) = if i = 0 then 0 else X σ := by
  induction i <;> simp_all [-Function.iterate_succ, Function.iterate_succ', OMDP.tsum_succs_univ']

@[simp]
theorem lfp_Φ_bot : OMDP.lfp_Φ (cost X) none = 0 := by simp [MDP.lfp_Φ_eq_iSup_Φ]

@[simp]
theorem lfp_Φ_sink : OMDP.lfp_Φ (cost X) (some (none, σ)) = X σ := by
  rw [← MDP.lfp_Φ_step]; simp_all [tsum_succs_univ']

noncomputable def step : (pGCL ϖ → Exp ϖ → Exp ϖ) →o pGCL ϖ → Exp ϖ → Exp ϖ :=
  ⟨fun Y ↦ (fun C X σ ↦
    OMDP.Φ (cost X) (match · with | ·⟨⇓ ϖ,σ'⟩ => X σ' | ·⟨C',σ'⟩ => Y C' X σ' | ⊥ => 0) (·⟨C, σ⟩))
    , by
      intro _ _ _ _ _ _
      apply (OMDP.Φ _).mono
      rintro (_ | ⟨_ | _, _⟩) <;> try rfl
      apply_assumption⟩

variable {f : pGCL ϖ → Exp ϖ → Exp ϖ}

@[simp] theorem step.skip : step f skip = (· ·) := by simp_all [step, OMDP.tsum_succs_univ']
@[simp] theorem step.assign : step f (.assign x e) = fun X σ ↦ f .skip X (σ[x ↦ e σ]) :=
  by simp_all [step, OMDP.tsum_succs_univ']
@[simp] theorem step.tick : step f (.tick r) = fun X ↦ r + f .skip X := by
  simp_all [step, OMDP.tsum_succs_univ']; rfl
@[simp] theorem step.prob : step f (.prob C₁ p C₂) = fun X ↦ p.pick (f C₁ X) (f C₂ X) := by
  simp_all [step, OMDP.tsum_succs_univ']
  ext X σ
  rw [ENNReal.tsum_eq_add_tsum_ite (·⟨C₁,σ⟩), ENNReal.tsum_eq_add_tsum_ite (·⟨C₂,σ⟩)]
  by_cases C₁ = C₂ <;> simp_all [eq_comm, ite_and]
@[simp] theorem step.nonDet : step f (.nonDet C₁ C₂) = f C₁ ⊓ f C₂ := by
  ext X σ
  simp [step, MDP.Φ, MDP.Φf, OMDP.tsum_succs_univ']
  simp_all [ite_and]
  apply le_antisymm <;> simp
  · constructor
    · apply iInf_le_of_le ⟨.L, by simp⟩
      rw [tsum_eq_single (·⟨C₁,σ⟩) (by simp_all [Imp.swap])]; simp
    · apply iInf_le_of_le ⟨.R, by simp⟩
      rw [tsum_eq_single (·⟨C₂,σ⟩) (by simp_all [Imp.swap])]; simp
  · rintro α (⟨_, _⟩ | ⟨_, _⟩)
    · rw [ENNReal.tsum_eq_add_tsum_ite (·⟨C₁,σ⟩)]; simp
    · rw [ENNReal.tsum_eq_add_tsum_ite (·⟨C₂,σ⟩)]; simp
theorem step.loop :
    step f (.loop b C) = fun X ↦ b.probOf * f (C ; .loop b C) X + b.not.probOf * f .skip X := by
  funext X σ
  simp [step, OMDP.tsum_succs_univ']
  split_ifs <;> simp_all

end OMDP

open OMDP

noncomputable def dop (C : pGCL ϖ) (X : Exp ϖ) : Exp ϖ := (OMDP.lfp_Φ (cost X) <| ·⟨C, ·⟩)

theorem dop_eq_iSup_Φ : dop (ϖ:=ϖ) = ⨆ n, fun C X σ ↦ (OMDP.Φ (cost X))^[n] ⊥ (·⟨C,σ⟩) := by
  ext C X σ; rw [dop, MDP.lfp_Φ_eq_iSup_Φ]; apply le_antisymm <;> simp
theorem dop_eq_iSup_succ_Φ :
    dop (ϖ:=ϖ) = ⨆ n, fun C X σ ↦ (OMDP.Φ (cost X))^[n + 1] ⊥ (·⟨C,σ⟩) := by
  ext C X σ; rw [dop, MDP.lfp_Φ_eq_iSup_succ_Φ]; apply le_antisymm <;> simp

theorem step_dop : step (ϖ:=ϖ) dop = dop := by
  funext C X σ
  rw [dop, ← MDP.lfp_Φ_step]
  simp only [step, OrderHom.coe_mk]
  congr! 3 with C'
  rcases C' with ⟨none, σ'⟩ | ⟨C', σ'⟩ | _ <;> simp [dop]

@[simp] theorem dop_skip : dop (ϖ:=ϖ) .skip = (· ·) := by rw [← step_dop]; simp

theorem dop_isLeast (b : pGCL ϖ → Exp ϖ → Exp ϖ) (h : step b ≤ b) : dop ≤ b := by
  rw [dop_eq_iSup_Φ, iSup_le_iff]
  intro n
  induction n with
  | zero => intros _ _ _; simp [cost]
  | succ i ih =>
    refine le_trans (fun _ _ _ ↦ ?_) h
    simp [Function.iterate_succ', step, -Function.iterate_succ]
    gcongr; split <;> simp_all [ih _ _ _]; split_ifs <;> simp

variable {C : pGCL ϖ}

attribute [-simp] Function.iterate_succ in
theorem dop_le_seq : C.dop ∘ C'.dop ≤ (C ; C').dop := by
  intro X σ
  nth_rw 1 [dop_eq_iSup_succ_Φ]
  simp
  intro n
  induction n generalizing C C' σ with
  | zero => nth_rw 2 [← step_dop]; simp_all [step, MDP.Φf]
  | succ i ih =>
    nth_rw 2 [← step_dop]
    rw [Function.iterate_succ', Function.comp_apply]
    simp [step, OMDP.tsum_succs_univ']
    refine add_le_add (le_refl _) (iInf₂_mono fun α hα ↦ C'.tsum_after_le (by simp) ?_ ?_)
    all_goals intros; simp_all; split_ifs <;> simp_all [mul_le_mul]

theorem step_dwp : step (ϖ:=ϖ) dwp = dwp := by
  funext C; induction C with try simp_all
  | loop => rw [step.loop, dwp_loop_fp]; rfl
  | seq C₁ C₂ ih₁ ih₂ =>
    ext X σ
    rw [← ih₁]
    simp [step, OMDP.tsum_succs_univ']
    congr! 4
    apply C₂.tsum_after_eq <;> simp_all <;> split_ifs <;> simp_all
    rintro _ _ _ _ _ h ⟨_⟩ _ _ h' ⟨_⟩ hp _
    exact ⟨⟨_, _, h⟩, _, h', hp⟩

theorem dwp_le_dop.loop (ih : C.dwp ≤ C.dop) : dwp (.loop b C) ≤ dop (.loop b C) := by
  refine fun X ↦ OrderHom.lfp_le (dwp_loop_f b C X) (le_trans ?_ <| step_dop.le _ _ ·)
  simp_all [step, OMDP.tsum_succs_univ', dwp_loop_f]
  split_ifs <;> simp_all; apply (ih _).trans (dop_le_seq _)

theorem dwp_le_dop : dwp (ϖ:=ϖ) ≤ dop := by
  intro C
  induction C with
  | skip => simp
  | assign => rw [← step_dop]; simp
  | prob C₁ p C₂ ih₁ ih₂ => rw [← step_dop]; intro X; simp_all [ih₁ X, ih₂ X]
  | nonDet C₁ C₂ ih₁ ih₂ => intro X σ; rw [← step_dop]; simp_all [ih₁ X σ, ih₂ X σ]
  | loop b C ih => exact dwp_le_dop.loop ih
  | seq C₁ C₂ ih₁ ih₂ => intro; exact (dwp.monotone _ (ih₂ _)).trans (ih₁ _) |>.trans (dop_le_seq _)
  | tick => rw [← step_dop]; simp

theorem dop_eq_dwp : dop (ϖ:=ϖ) = dwp := (dop_isLeast _ step_dwp.le).antisymm dwp_le_dop
