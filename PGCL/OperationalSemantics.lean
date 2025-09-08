import MDP.Bellman
import MDP.Relational
import MDP.SmallStepSemantics
import PGCL.SmallStep2
import PGCL.WeakestPre

namespace pGCL

variable {ϖ : Type*} [DecidableEq ϖ]

@[simp]
noncomputable def cost (X : Exp ϖ)
  | conf[⇓ ϖ, σ] => X σ
  | conf[tick(~ r), σ] => r σ
  | conf[~c' ; ~_, σ] => cost X conf[~c', σ]
  | _ => 0

omit [DecidableEq ϖ] in
@[simp]
theorem cost_mono : Monotone (cost (ϖ:=ϖ)) := fun a b hab ↦ by
  intro x
  unfold cost
  induction x with
  | bot => simp
  | term x =>
    obtain ⟨p, σ⟩ := x
    · simp
    · simp
      exact hab _
  | prog p =>
    induction p with simp
    | seq C₁ C₂ ih₁ ih₂ =>
      simp_all
      split at ih₁ <;> simp_all

@[simp]
theorem cost_X_of_pGCL : cost X conf[~C, σ] = cost 0 conf[~C, σ] := by induction C <;> simp_all

noncomputable instance instSmallStepSemantics :
    SmallStepSemantics (pGCL ϖ) (States ϖ) Termination Act where
  r := SmallStep
  h₀ := SmallStep.p_ne_zero
  h₁ := SmallStep.sums_to_one
  h₂ := SmallStep.progress
  h₃ := by
    intros t σ C'
    constructor
    · grind
    · rintro ⟨_⟩
      simp only [SmallStep.to_bot, Conf.term.injEq, reduceCtorEq, or_false, exists_and_left,
        exists_eq_left]
      grind
  h₄ := by
    intros C'
    constructor
    · grind
    · rintro ⟨_⟩
      simp only [SmallStep.to_bot, reduceCtorEq, or_true, and_true, exists_const, exists_eq_left,
        exists_eq]
  cost
  cost_mono
  cost_bot := by simp

noncomputable instance : DemonicExpectationTransformer (pGCL ϖ) (States ϖ) where
  det := dwp
noncomputable instance : AngelicExpectationTransformer (pGCL ϖ) (States ϖ) where
  aet := awp

attribute [simp] SmallStepSemantics.cost
attribute [simp] DemonicExpectationTransformer.det
attribute [simp] AngelicExpectationTransformer.aet

open SmallStepSemantics

theorem P_support_eq_succs : (Function.support (mdp.P c α)) = SmallStep.succs (ϖ:=ϖ) c α := by
  ext c'
  simp [SmallStep.succs]
  constructor
  · simp [mdp, r]; intro p h hp; use p
  · simp [mdp]; intro p h; use p, h, SmallStep.p_ne_zero h

open scoped Classical in
noncomputable instance : MDP.FiniteBranching (instSmallStepSemantics (ϖ:=ϖ)).mdp where
  act_fin := (Set.toFinite <| mdp.act ·)
  succs_fin s α := by
    simp [P_support_eq_succs, SmallStep.succs, ← SmallStep.succs_univ_fin'_eq_r]
    let S : Set _ := ((SmallStep.succs_univ_fin' s).image (·.snd.snd)).toSet
    have : {c' | ∃ p, (α, p, c') ∈ SmallStep.succs_univ_fin' s} ⊆ S := by
      intro; simp
      grind
    exact Set.Finite.subset (Finset.finite_toSet _) this

variable {f : pGCL ϖ → Exp ϖ →o Exp ϖ}

variable {C : pGCL ϖ}

@[simp, grind]
theorem act_seq :
      instSmallStepSemantics.act (Conf.prog (pgcl {~C ; ~C'}) σ)
    = instSmallStepSemantics.act (Conf.prog C σ) := by
  ext; simp [act, r]; grind

@[simp] theorem ς.skip : instSmallStepSemantics.ς f skip = ⟨(· ·), fun ⦃_ _⦄ a ↦ a⟩ := by
  ext X σ
  rw [ς_apply_fin {.N} {conf[⇓, σ]}] <;> simp_all [ς_continuation_fin, act, mdp, r]
@[simp] theorem ς.assign :
      instSmallStepSemantics.ς f (pgcl {~x := ~e})
    = ⟨fun X σ ↦ X (σ[x ↦ e σ]), fun _ _ h σ ↦ h (σ[x ↦ e σ])⟩ := by
  ext X σ
  rw [ς_apply_fin {.N} {conf[⇓, σ[x ↦ e σ]]}] <;> simp_all [ς_continuation_fin, act, mdp, r]
@[simp] theorem ς.tick {t} :
    instSmallStepSemantics.ς f (.tick t) = ⟨fun X ↦ t + X, fun _ _ _ ↦ by simp; gcongr⟩ := by
  ext X σ
  rw [ς_apply_fin {.N} {conf[⇓, σ]}] <;> simp_all [ς_continuation_fin, act, mdp, r]
@[simp] theorem ς.assert :
    instSmallStepSemantics.ς f (.assert b) = ⟨fun X ↦ b.iver * X, fun _ _ _ ↦ by simp; gcongr⟩ := by
  ext X σ
  if b σ then
    rw [ς_apply_fin {.N} {conf[⇓, σ]}] <;> simp_all [ς_continuation_fin, act, mdp, r]
  else
    rw [ς_apply_fin {.N} {conf[↯, σ]}] <;> simp_all [ς_continuation_fin, act, mdp, r]
@[simp] theorem ς.prob :
      instSmallStepSemantics.ς f (.prob C₁ p C₂)
    = ⟨fun X ↦ p.pick (f C₁ X) (f C₂ X),
       fun a b h ↦ by simp; apply ProbExp.pick_le <;> apply (f _).mono h⟩ := by
  ext X σ
  rw [ς_apply_fin {Act.N} (SmallStep.succs_fin conf[{ ~C₁ } [~p] { ~C₂ }, σ] Act.N)]
  · simp_all [SmallStep.succs_fin]
    simp_all [ς_continuation_fin, mdp, r]
    if C₁ = C₂ then simp_all else
    have : ¬C₂ = C₁ := by grind
    split_ifs <;> simp_all [ite_and, ProbExp.pick, -ProbExp.pick_of]
  · ext; simp_all [act, r]
    rintro ⟨_⟩
    split_ifs
    · simp
    · if hp : 0 < p.val σ then
        use p.val σ
        simp_all
      else
        use 1 - p.val σ
        simp_all
  · ext
    simp [SmallStep.succs_fin, mdp, r]
    have h₀ : ∀ (x : ENNReal) (p' : Prop), ¬(x = 0 ∧ 0 < x ∧ p') := by simp_all
    split_ifs <;> subst_eqs <;> simp [*]
    constructor
    · rintro (⟨_, _⟩ | ⟨_, _⟩)
      · simp [*]; exact (ProbExp.not_zero_off p σ).mp ‹_›
      · have : ¬C₂ = C₁ := by grind
        simp [*]; exact (ProbExp.lt_one_iff p σ).mp ‹_›
    · grind
open scoped Classical in
@[simp] theorem ς.nonDet : instSmallStepSemantics.ς f (.nonDet C₁ C₂) = f C₁ ⊓ f C₂ := by
  ext X σ
  rw [ς_apply_act₂ Act.L Act.R {conf[~C₁, σ], conf[~C₂, σ]}]
  · simp_all [ς_continuation_fin]
    simp_all [mdp, r]
    if hC₁₂ : C₁ = C₂ then
      subst_eqs
      simp
    else
      rw [Finset.sum_pair]
      · have hC₂₁ : ¬C₂ = C₁ := by grind
        simp [hC₂₁]
      · grind
  · simp [act, r]
    ext
    simp
    grind
  · ext c
    simp [mdp, r]
    grind

@[simp] theorem aς.skip : instSmallStepSemantics.aς f skip = ⟨(· ·), fun ⦃_ _⦄ a ↦ a⟩ := by
  ext X σ
  rw [aς_apply_fin {.N} {conf[⇓, σ]}] <;> simp_all [ς_continuation_fin, act, mdp, r]
@[simp] theorem aς.assign :
      instSmallStepSemantics.aς f (pgcl {~x := ~e})
    = ⟨fun X σ ↦ X (σ[x ↦ e σ]), fun _ _ h σ ↦ h (σ[x ↦ e σ])⟩ := by
  ext X σ
  rw [aς_apply_fin {.N} {conf[⇓, σ[x ↦ e σ]]}] <;> simp_all [ς_continuation_fin, act, mdp, r]
@[simp] theorem aς.tick {t} :
    instSmallStepSemantics.aς f (.tick t) = ⟨fun X ↦ t + X, fun _ _ _ ↦ by simp; gcongr⟩ := by
  ext X σ
  rw [aς_apply_fin {.N} {conf[⇓, σ]}] <;> simp_all [ς_continuation_fin, act, mdp, r]
@[simp] theorem aς.assert :
    instSmallStepSemantics.aς f (.assert b) = ⟨fun X ↦ b.iver * X, fun _ _ _ ↦ by simp; gcongr⟩ := by
  ext X σ
  if b σ then
    rw [aς_apply_fin {.N} {conf[⇓, σ]}] <;> simp_all [ς_continuation_fin, act, mdp, r]
  else
    rw [aς_apply_fin {.N} {conf[↯, σ]}] <;> simp_all [ς_continuation_fin, act, mdp, r]
@[simp] theorem aς.prob :
      instSmallStepSemantics.aς f (.prob C₁ p C₂)
    = ⟨fun X ↦ p.pick (f C₁ X) (f C₂ X),
       fun a b h ↦ by simp; apply ProbExp.pick_le <;> apply (f _).mono h⟩ := by
  ext X σ
  rw [aς_apply_fin {Act.N} (SmallStep.succs_fin conf[{ ~C₁ } [~p] { ~C₂ }, σ] Act.N)]
  · simp_all [SmallStep.succs_fin]
    simp_all [ς_continuation_fin, mdp, r]
    if C₁ = C₂ then simp_all else
    have : ¬C₂ = C₁ := by grind
    split_ifs <;> simp_all [ite_and, ProbExp.pick, -ProbExp.pick_of]
  · ext; simp_all [act, r]
    rintro ⟨_⟩
    split_ifs
    · simp
    · if hp : 0 < p.val σ then
        use p.val σ
        simp_all
      else
        use 1 - p.val σ
        simp_all
  · ext
    simp [SmallStep.succs_fin, mdp, r]
    have h₀ : ∀ (x : ENNReal) (p' : Prop), ¬(x = 0 ∧ 0 < x ∧ p') := by simp_all
    split_ifs <;> subst_eqs <;> simp [*]
    constructor
    · rintro (⟨_, _⟩ | ⟨_, _⟩)
      · simp [*]; exact (ProbExp.not_zero_off p σ).mp ‹_›
      · have : ¬C₂ = C₁ := by grind
        simp [*]; exact (ProbExp.lt_one_iff p σ).mp ‹_›
    · grind
open scoped Classical in
@[simp] theorem aς.nonDet : instSmallStepSemantics.aς f (.nonDet C₁ C₂) = f C₁ ⊔ f C₂ := by
  ext X σ
  rw [aς_apply_act₂ Act.L Act.R {conf[~C₁, σ], conf[~C₂, σ]}]
  · simp_all [ς_continuation_fin]
    simp_all [mdp, r]
    if hC₁₂ : C₁ = C₂ then
      subst_eqs
      simp
    else
      rw [Finset.sum_pair]
      · have hC₂₁ : ¬C₂ = C₁ := by grind
        simp [hC₂₁]
      · grind
  · simp [act, r]
    ext
    simp
    grind
  · ext c
    simp [mdp, r]
    grind

open scoped Classical in
theorem ς.loop :
      instSmallStepSemantics.ς f (.loop b C (ϖ:=ϖ))
    = ⟨fun X ↦ b.iver * f (pgcl { ~C ; while ~b {~C} }) X + b.not.iver * X,
       fun a b h ↦ by simp; gcongr⟩
:= by
  ext X σ
  if b σ = true then
    rw [ς_apply_fin {.N} {conf[~C ; while ~b { ~C }, σ]}]
    · simp_all [ς_continuation_fin, mdp, r, ite_and]
    · simp [act, r]
    · ext; simp_all [mdp, r]
  else
    rw [ς_apply_fin {.N} {conf[⇓, σ]}]
    · simp_all [ς_continuation_fin, mdp, r, ite_and]
    · simp [act, r]
    · ext; simp_all [mdp, r]

theorem ς.seq {C₁ C₂ : pGCL ϖ}
    (ih₁ : instSmallStepSemantics.ς dwp C₁ = dwp⟦~C₁⟧) :
    instSmallStepSemantics.ς dwp (pgcl {~C₁ ; ~C₂}) = dwp⟦~C₁⟧.comp dwp⟦~C₂⟧ := by
  ext
  simp [← ih₁, ς, tsum_succs_univ']
  congr! 4
  apply C₂.tsum_after_eq <;> simp [mdp, r, pGCL.after]
  rintro C' σ' α p (⟨C, _, _, _⟩ | ⟨_, _, _⟩) p' (⟨_, _, _⟩ | ⟨_, _, ⟨_⟩⟩) hp' _
  · simp at *
    grind
  · grind
  · use conf[⇓, σ']
    simp; grind

open scoped Classical in
theorem aς.loop :
      instSmallStepSemantics.aς f (.loop b C (ϖ:=ϖ))
    = ⟨fun X ↦ b.iver * f (pgcl { ~C ; while ~b {~C} }) X + b.not.iver * X,
       fun a b h ↦ by simp; gcongr⟩
:= by
  ext X σ
  if b σ = true then
    rw [aς_apply_fin {.N} {conf[~C ; while ~b { ~C }, σ]}]
    · simp_all [ς_continuation_fin, mdp, r, ite_and]
    · simp [act, r]
    · ext; simp_all [mdp, r]
  else
    rw [aς_apply_fin {.N} {conf[⇓, σ]}]
    · simp_all [ς_continuation_fin, mdp, r, ite_and]
    · simp [act, r]
    · ext; simp_all [mdp, r]

theorem aς.seq {C₁ C₂ : pGCL ϖ}
    (ih₁ : instSmallStepSemantics.aς awp C₁ = awp⟦~C₁⟧) :
    instSmallStepSemantics.aς awp (pgcl {~C₁ ; ~C₂}) = awp⟦~C₁⟧.comp awp⟦~C₂⟧ := by
  ext
  simp [← ih₁, aς, tsum_succs_univ']
  congr! 4
  apply C₂.tsum_after_eq <;> simp [mdp, r, pGCL.after]
  rintro C' σ' α p (⟨C, _, _, _⟩ | ⟨_, _, _⟩) p' (⟨_, _, _⟩ | ⟨_, _, ⟨_⟩⟩) hp' _
  · simp at *
    grind
  · grind
  · use conf[⇓, σ']
    simp; grind

attribute [-simp] Function.iterate_succ in
theorem dop_le_seq :
      instSmallStepSemantics.dop C ∘ instSmallStepSemantics.dop C'
    ≤ instSmallStepSemantics.dop pgcl {~C ; ~C'} := by
  intro X σ
  nth_rw 1 [dop_eq_iSup_succ_Φ]
  simp
  intro n
  induction n generalizing C C' σ with
  | zero =>
    have : ⨅ α ∈ instSmallStepSemantics.act (Conf.prog C σ), (0 : ENNReal) = 0 :=
      SmallStep.iInf_act_const
    nth_rw 2 [← ς_dop_eq_dop]; simp_all [ς]
  | succ i ih =>
    nth_rw 2 [← ς_dop_eq_dop]
    rw [Function.iterate_succ', Function.comp_apply]
    simp [ς, tsum_succs_univ']
    -- gcongr
    refine add_le_add (le_refl _) (iInf₂_mono fun α hα ↦ C'.tsum_after_le ?_ ?_ ?_ ?_)
    · simp [mdp, r]
    · simp [mdp, r]
      intro σ'
      split_ifs <;> try rfl
      gcongr
      have := instSmallStepSemantics.Φ_term_eq (A:=Act) (X:=(instSmallStepSemantics.dop C') X)
                (t:=Termination.term) (σ:=σ') (n:=i+1)
      simp at this
      rw [this]
    · simp [mdp, r]
      intro σ' α' p' h
      right
      have := instSmallStepSemantics.Φ_term_eq (A:=Act) (X:=(instSmallStepSemantics.dop C') X)
                (t:=Termination.fault) (σ:=σ') (n:=i+1)
      simp at this
      rw [this]
    · simp [mdp, r]
      intro C' σ'
      split_ifs <;> try rfl
      gcongr
      simp_all

attribute [-simp] Function.iterate_succ in
theorem aop_le_seq :
      instSmallStepSemantics.aop C ∘ instSmallStepSemantics.aop C'
    ≤ instSmallStepSemantics.aop pgcl {~C ; ~C'} := by
  intro X σ
  nth_rw 1 [aop_eq_iSup_succ_Ψ]
  simp
  intro n
  induction n generalizing C C' σ with
  | zero =>
    have : ⨅ α ∈ instSmallStepSemantics.act (Conf.prog C σ), (0 : ENNReal) = 0 :=
      SmallStep.iInf_act_const
    nth_rw 2 [← aς_aop_eq_aop]; simp_all [aς]
  | succ i ih =>
    nth_rw 2 [← aς_aop_eq_aop]
    rw [Function.iterate_succ', Function.comp_apply]
    simp [aς, tsum_succs_univ']
    -- gcongr
    refine add_le_add (le_refl _) (iSup₂_mono fun α hα ↦ C'.tsum_after_le ?_ ?_ ?_ ?_)
    · simp [mdp, r]
    · simp [mdp, r]
      intro σ'
      split_ifs <;> try rfl
      gcongr
      have := instSmallStepSemantics.Ψ_term_eq (A:=Act) (X:=(instSmallStepSemantics.aop C') X)
                (t:=Termination.term) (σ:=σ') (n:=i+1)
      simp at this
      rw [this]
    · simp [mdp, r]
      intro σ' α' p' h
      right
      have := instSmallStepSemantics.Ψ_term_eq (A:=Act) (X:=(instSmallStepSemantics.aop C') X)
                (t:=Termination.fault) (σ:=σ') (n:=i+1)
      simp at this
      rw [this]
    · simp [mdp, r]
      intro C' σ'
      split_ifs <;> try rfl
      gcongr
      simp_all

open scoped Classical in
theorem dwp_le_dop.loop (ih : C.dwp ≤ instSmallStepSemantics.dop C) :
    dwp⟦while ~b { ~C }⟧ ≤ instSmallStepSemantics.dop (.loop b C (ϖ:=ϖ)) := by
  intro X
  apply OrderHom.lfp_le
  nth_rw 2 [← ς_dop_eq_dop]
  intro σ
  simp_all [ς, tsum_succs_univ', BExpr.iver, BExpr.not, act, r]
  simp_all [mdp, r]
  rintro α p C' ⟨_⟩ ⟨_⟩ ⟨_⟩
  split_ifs <;> simp_all
  apply le_trans (ih _) (dop_le_seq _)

open scoped Classical in
theorem awp_le_aop.loop (ih : C.awp ≤ instSmallStepSemantics.aop C) :
    awp⟦while ~b { ~C }⟧ ≤ instSmallStepSemantics.aop (.loop b C (ϖ:=ϖ)) := by
  intro X
  apply OrderHom.lfp_le
  nth_rw 2 [← aς_aop_eq_aop]
  intro σ
  simp_all [aς, tsum_succs_univ', BExpr.iver, BExpr.not, act, r]
  simp_all [mdp, r]
  split_ifs
  · simp_all
  · simp_all
    apply le_iSup_of_le .N
    apply le_iSup_of_le 1
    simp
    apply le_trans (ih _) (aop_le_seq _)
  · simp_all
    apply le_iSup_of_le .N
    apply le_iSup_of_le 1
    apply le_iSup_of_le conf[⇓, σ]
    simp
  · simp_all

open scoped Classical in
noncomputable instance instSoundDemonicExpectationTransformer :
    SoundDemonicExpectationTransformer (pGCL ϖ) (States ϖ) Termination Act where
  det_le_dop := by
    intro C; induction C with try simp_all; (try rw [← ς_dop_eq_dop]; simp; done)
    | seq C₁ C₂ ih₁ ih₂ =>
      apply le_trans _ dop_le_seq
      intro σ
      simp
      exact OrderHom.apply_mono ih₁ (ih₂ σ)
    | prob =>
      intro X
      rw [← ς_dop_eq_dop]; simp
      gcongr <;> apply_assumption
    | nonDet C₁ C₂ ih₁ ih₂ =>
      intro X
      rw [← ς_dop_eq_dop]; simp
      exact ⟨inf_le_of_left_le (ih₁ X), inf_le_of_right_le (ih₂ X)⟩
    | loop b C' ih => apply dwp_le_dop.loop ih
  det_prefixed_point := by
    apply le_of_eq
    funext C; induction C with try simp_all [ς.seq]
    | loop =>
      rw [ς.loop]
      ext
      rw [← dwp_fp]
      simp only [dwp.seq, OrderHom.comp_coe, Function.comp_apply, OrderHom.coe_mk, Pi.add_apply,
        Pi.mul_apply]
      rfl

open scoped Classical in
noncomputable instance instSoundAngelicExpectationTransformer :
    SoundAngelicExpectationTransformer (pGCL ϖ) (States ϖ) Termination Act where
  aet_le_aop := by
    intro C; induction C with try simp_all; (try rw [← aς_aop_eq_aop]; simp; done)
    | seq C₁ C₂ ih₁ ih₂ =>
      apply le_trans _ aop_le_seq
      intro σ
      simp
      exact OrderHom.apply_mono ih₁ (ih₂ σ)
    | prob =>
      intro X
      rw [← aς_aop_eq_aop]; simp
      gcongr <;> apply_assumption
    | nonDet C₁ C₂ ih₁ ih₂ =>
      constructor
      all_goals intro X; rw [← aς_aop_eq_aop]; simp
      · exact le_sup_of_le_left (ih₁ X)
      · exact le_sup_of_le_right (ih₂ X)
    | loop b C' ih => apply awp_le_aop.loop ih
  aet_prefixed_point := by
    apply le_of_eq
    simp only [AngelicExpectationTransformer.aet]
    funext C; induction C with try simp_all [aς.seq]
    | loop =>
      rw [aς.loop]
      ext
      rw [← dop_fp]
      simp only [awp.seq, OrderHom.comp_coe, Function.comp_apply, OrderHom.coe_mk, Pi.add_apply,
        Pi.mul_apply]
      rfl

example : dwp (ϖ:=ϖ) = instSmallStepSemantics.dop := by
  rw [← SoundDemonicExpectationTransformer.det_eq_dop]; rfl
example : awp (ϖ:=ϖ) = instSmallStepSemantics.aop := by
  rw [← SoundAngelicExpectationTransformer.aet_eq_aop]; rfl

/--
info: 'pGCL.instSoundDemonicExpectationTransformer' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms instSoundDemonicExpectationTransformer
/--
info: 'pGCL.instSoundAngelicExpectationTransformer' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms instSoundAngelicExpectationTransformer

end pGCL
