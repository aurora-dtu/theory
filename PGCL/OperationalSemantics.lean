import MDP.Bellman
import MDP.Relational
import MDP.SmallStepSemantics
import PGCL.SmallStep2
import PGCL.WeakestPre

namespace pGCL

variable {ϖ : Type*} [DecidableEq ϖ]

@[simp]
noncomputable def cost_t : Exp ϖ →o Termination × States ϖ → ENNReal :=
  ⟨fun X c ↦ match c with
  | (.term, σ) => X σ
  | (.fault, _) => 0, fun _ _ _ _ ↦ by
    simp; split
    · apply_assumption
    · rfl⟩

@[simp]
noncomputable def cost_p : pGCL ϖ × States ϖ → ENNReal
  | conf₀[tick(~ r), σ] => r σ
  | conf₀[~c' ; ~_, σ] => cost_p conf₀[~c', σ]
  | _ => 0

noncomputable instance instSmallStepSemantics :
    SmallStepSemantics (pGCL ϖ) (States ϖ) Termination Act where
  r := SmallStep
  h₀ := SmallStep.p_ne_zero
  h₁ := SmallStep.sums_to_one
  h₂ := SmallStep.progress
  cost_t
  cost_p

open SmallStepSemantics

attribute [simp] SmallStepSemantics.r
attribute [simp] SmallStepSemantics.cost_t
attribute [simp] SmallStepSemantics.cost_p

noncomputable instance : DemonicExpectationTransformer (pGCL ϖ) (States ϖ) where
  det := dwp
noncomputable instance : AngelicExpectationTransformer (pGCL ϖ) (States ϖ) where
  aet := awp

attribute [simp] SmallStepSemantics.cost
attribute [simp] DemonicExpectationTransformer.det
attribute [simp] AngelicExpectationTransformer.aet

open SmallStepSemantics

open scoped Classical in
noncomputable instance : (instSmallStepSemantics (ϖ:=ϖ)).FiniteBranching where
  finite := by simp [r, ← SmallStep.succs_univ_fin'_eq_r]

variable {f : pGCL ϖ → Exp ϖ →o Exp ϖ}

variable {C : pGCL ϖ} {σ : States ϖ}

open scoped Classical in
@[simp, grind]
theorem act_eq_SmallStep_act :
    instSmallStepSemantics.act (Conf.prog C σ) = (some ·) '' SmallStep.act (C, σ) := by
  ext
  simp [act, r, SmallStep.act, conf₂_to_conf]
  grind

@[simp, grind]
theorem act_seq :
      instSmallStepSemantics.act (Conf.prog (pgcl {~C ; ~C'}) σ)
    = instSmallStepSemantics.act (Conf.prog C σ) := by
  ext; simp

attribute [simp] iInf_and
attribute [simp] iSup_and

@[simp] theorem dς.skip : instSmallStepSemantics.dς f skip = ⟨(· ·), fun ⦃_ _⦄ a ↦ a⟩ := by
  ext X σ
  simp [dς, psucc, r]
  rw [tsum_eq_single ⟨(1, conf₁[⇓, σ]), by simp⟩] <;> simp
@[simp] theorem dς.assign :
      instSmallStepSemantics.dς f (pgcl {~x := ~e})
    = ⟨fun X σ ↦ X (σ[x ↦ e σ]), fun _ _ h σ ↦ h (σ[x ↦ e σ])⟩ := by
  ext X σ
  simp [dς, psucc, r]
  rw [tsum_eq_single ⟨(1, conf₁[⇓, σ[x ↦ e σ]]), by simp⟩] <;> simp
@[simp] theorem dς.tick {t} :
    instSmallStepSemantics.dς f (.tick t) = ⟨fun X ↦ t + X, fun _ _ _ ↦ by simp; gcongr⟩ := by
  ext X σ
  simp [dς, psucc, r]
  rw [tsum_eq_single ⟨(1, conf₁[⇓, σ]), by simp⟩] <;> simp
@[simp] theorem dς.assert :
    instSmallStepSemantics.dς f (.assert b) = ⟨fun X ↦ b.iver * X, fun _ _ _ ↦ by simp; gcongr⟩
:= by
  ext X σ
  simp [dς, psucc, r]
  if hb : b σ then
    rw [tsum_eq_single ⟨(1, conf₁[⇓, σ]), by simp [hb]⟩] <;> simp [hb]
  else
    rw [tsum_eq_single ⟨(1, conf₁[↯, σ]), by simp [hb]⟩] <;> simp [hb]
@[simp] theorem dς.prob :
      instSmallStepSemantics.dς f (.prob C₁ p C₂)
    = ⟨fun X ↦ p.pick (f C₁ X) (f C₂ X),
       fun a b h ↦ by simp; apply ProbExp.pick_le <;> apply (f _).mono h⟩ := by
  ext X σ
  simp [dς, psucc, r]
  if h₁₂ : C₁ = C₂ then
    subst_eqs
    simp_all only [ProbExp.pick_same]
    rw [tsum_eq_single ⟨(1, conf₁[~C₁, σ]), by simp⟩] <;> simp
  else if hp₀ : p.val σ = 0 then
    have h₂₁ : ¬C₂ = C₁ := by grind
    rw [tsum_eq_single ⟨(1, conf₁[~C₂, σ]), by simp [h₁₂, h₂₁, hp₀]⟩] <;> simp_all [ProbExp.pick]
    grind
  else if hp₁ : p.val σ = 1 then
    have h₂₁ : ¬C₂ = C₁ := by grind
    rw [tsum_eq_single ⟨(1, conf₁[~C₁, σ]), by simp [hp₁, h₁₂]⟩]
      <;> simp_all [ProbExp.pick]
    grind
  else
    simp_all only [ProbExp.not_zero_off, ProbExp.lt_one_iff]
    rw [ENNReal.tsum_eq_add_tsum_ite ⟨(p.val σ, conf₁[~C₁, σ]), by simp [h₁₂, hp₀]⟩]
    simp_all only
    rw [tsum_eq_single ⟨(1 - p.val σ, conf₁[~C₂, σ]), by simp [h₁₂, hp₁]⟩] <;> simp
    · simp [ProbExp.pick, -ProbExp.pick_of]; grind
    · grind
open scoped Classical in
@[simp] theorem dς.nonDet : instSmallStepSemantics.dς f (.nonDet C₁ C₂) = f C₁ ⊓ f C₂ := by
  ext X σ
  simp [dς, SmallStepSemantics.cost_p, act_eq_SmallStep_act, Set.mem_image, psucc, r,
    Set.coe_setOf, Set.mem_setOf_eq, SmallStepSemantics.cost_t, cost_t, iInf_exists, iInf_and,
    OrderHom.coe_mk, cost_p, SmallStep.act_nonDet, Set.mem_insert_iff, Set.mem_singleton_iff,
    zero_add, OrderHom.coe_inf, -Pi.inf_apply]
  apply le_antisymm
  · simp
    constructor
    · apply iInf_le_of_le (some .L)
      apply iInf_le_of_le .L
      simp
      rw [tsum_eq_single ⟨(1, conf₁[~C₁, σ]), by simp⟩] <;> simp
    · apply iInf_le_of_le (some .R)
      apply iInf_le_of_le .R
      simp
      rw [tsum_eq_single ⟨(1, conf₁[~C₂, σ]), by simp⟩] <;> simp
  · simp
    rintro α α' (⟨⟨_⟩⟩ | ⟨⟨_⟩⟩) ⟨_⟩
    · simp
      left
      rw [tsum_eq_single ⟨(1, conf₁[~C₁, σ]), by simp⟩] <;> simp
    · simp
      right
      rw [tsum_eq_single ⟨(1, conf₁[~C₂, σ]), by simp⟩] <;> simp

@[simp] theorem aς.skip : instSmallStepSemantics.aς f skip = ⟨(· ·), fun ⦃_ _⦄ a ↦ a⟩ := by
  ext X σ
  simp [aς, psucc, r]
  rw [tsum_eq_single ⟨(1, conf₁[⇓, σ]), by simp⟩] <;> simp
@[simp] theorem aς.assign :
      instSmallStepSemantics.aς f (pgcl {~x := ~e})
    = ⟨fun X σ ↦ X (σ[x ↦ e σ]), fun _ _ h σ ↦ h (σ[x ↦ e σ])⟩ := by
  ext X σ
  simp [aς, psucc, r]
  rw [tsum_eq_single ⟨(1, conf₁[⇓, σ[x ↦ e σ]]), by simp⟩] <;> simp
@[simp] theorem aς.tick {t} :
    instSmallStepSemantics.aς f (.tick t) = ⟨fun X ↦ t + X, fun _ _ _ ↦ by simp; gcongr⟩ := by
  ext X σ
  simp [aς, psucc, r]
  rw [tsum_eq_single ⟨(1, conf₁[⇓, σ]), by simp⟩] <;> simp
@[simp] theorem aς.assert :
    instSmallStepSemantics.aς f (.assert b) = ⟨fun X ↦ b.iver * X, fun _ _ _ ↦ by simp; gcongr⟩
:= by
  ext X σ
  simp [aς, psucc, r]
  if hb : b σ then
    rw [tsum_eq_single ⟨(1, conf₁[⇓, σ]), by simp [hb]⟩] <;> simp [hb]
  else
    rw [tsum_eq_single ⟨(1, conf₁[↯, σ]), by simp [hb]⟩] <;> simp [hb]
@[simp] theorem aς.prob :
      instSmallStepSemantics.aς f (.prob C₁ p C₂)
    = ⟨fun X ↦ p.pick (f C₁ X) (f C₂ X),
       fun a b h ↦ by simp; apply ProbExp.pick_le <;> apply (f _).mono h⟩ := by
  ext X σ
  simp [aς, psucc, r]
  if h₁₂ : C₁ = C₂ then
    subst_eqs
    simp_all only [ProbExp.pick_same]
    rw [tsum_eq_single ⟨(1, conf₁[~C₁, σ]), by simp⟩] <;> simp
  else if hp₀ : p.val σ = 0 then
    have h₂₁ : ¬C₂ = C₁ := by grind
    rw [tsum_eq_single ⟨(1, conf₁[~C₂, σ]), by simp [h₁₂, h₂₁, hp₀]⟩] <;> simp_all [ProbExp.pick]
    grind
  else if hp₁ : p.val σ = 1 then
    have h₂₁ : ¬C₂ = C₁ := by grind
    rw [tsum_eq_single ⟨(1, conf₁[~C₁, σ]), by simp [hp₁, h₁₂]⟩]
      <;> simp_all [ProbExp.pick]
    grind
  else
    simp_all only [ProbExp.not_zero_off, ProbExp.lt_one_iff]
    rw [ENNReal.tsum_eq_add_tsum_ite ⟨(p.val σ, conf₁[~C₁, σ]), by simp [h₁₂, hp₀]⟩]
    simp_all only
    rw [tsum_eq_single ⟨(1 - p.val σ, conf₁[~C₂, σ]), by simp [h₁₂, hp₁]⟩] <;> simp
    · simp [ProbExp.pick, -ProbExp.pick_of]; grind
    · grind
open scoped Classical in
@[simp] theorem aς.nonDet : instSmallStepSemantics.aς f (.nonDet C₁ C₂) = f C₁ ⊔ f C₂ := by
  ext X σ
  simp only [aς, SmallStepSemantics.cost_p, act_eq_SmallStep_act, Set.mem_image, psucc, r,
    Set.coe_setOf, Set.mem_setOf_eq, SmallStepSemantics.cost_t, cost_t, iSup_exists, iSup_and,
    OrderHom.coe_mk, cost_p, SmallStep.act_nonDet, Set.mem_insert_iff, Set.mem_singleton_iff,
    zero_add, OrderHom.coe_sup, Pi.sup_apply]
  apply le_antisymm
  · simp only [iSup_le_iff]
    rintro α α' (⟨⟨_⟩⟩ | ⟨⟨_⟩⟩) ⟨_⟩
    · simp
      rw [tsum_eq_single ⟨(1, conf₁[~C₁, σ]), by simp⟩] <;> simp
    · simp
      rw [tsum_eq_single ⟨(1, conf₁[~C₂, σ]), by simp⟩] <;> simp
  · simp
    constructor
    · apply le_iSup_of_le (some .L)
      apply le_iSup_of_le .L
      simp
      rw [tsum_eq_single ⟨(1, conf₁[~C₁, σ]), by simp⟩] <;> simp
    · apply le_iSup_of_le (some .R)
      apply le_iSup_of_le .R
      simp
      rw [tsum_eq_single ⟨(1, conf₁[~C₂, σ]), by simp⟩] <;> simp

open scoped Classical in
theorem dς.loop :
      instSmallStepSemantics.dς f (.loop b C (ϖ:=ϖ))
    = ⟨fun X ↦ b.iver * f (pgcl { ~C ; while ~b {~C} }) X + b.not.iver * X,
       fun a b h ↦ by simp; gcongr⟩
:= by
  ext X σ
  simp [dς, psucc, r]
  if hb : b σ = true then
    rw [tsum_eq_single ⟨(1, conf₁[~C ; while ~b { ~C }, σ]), by simp [hb]⟩] <;> simp [hb]
  else
    rw [tsum_eq_single ⟨(1, conf₁[⇓, σ]), by simp [hb]⟩] <;> simp [hb]

open scoped Classical in
theorem tsum_succs_univ' {α : Act} (f : instSmallStepSemantics.psucc C σ α → ENNReal) :
    (∑' s', f s') = ∑' s', if h : _ then f ⟨s', h⟩ else 0 := by
  symm
  apply tsum_eq_tsum_of_ne_zero_bij (↑↑·) _ _ (by simp_all)
  · intro ⟨_, _⟩ ⟨_, _⟩; simp; apply SetCoe.ext
  · simp_all--; intro _ α p _ _; use α, p

theorem dς.seq {C₁ C₂ : pGCL ϖ}
    (ih₁ : instSmallStepSemantics.dς dwp C₁ = dwp⟦~C₁⟧) :
    instSmallStepSemantics.dς dwp (pgcl {~C₁ ; ~C₂}) = dwp⟦~C₁⟧.comp dwp⟦~C₂⟧ := by
  ext X σ
  simp [← ih₁, dς, tsum_succs_univ']
  congr! 7 with α α' hα
  rcases α with (_ | α)
  · contradiction
  · simp [psucc, r]
    obtain ⟨p₀, hα⟩ := hα
    apply C₂.tsum_after_eq' <;> simp [pGCL.after]
    rintro p C' σ' (⟨C', h, ⟨_⟩⟩ | ⟨h, ⟨_⟩⟩) hp h₀
    · simp_all
    · simp_all
      use .term, σ'

open scoped Classical in
theorem aς.loop :
      instSmallStepSemantics.aς f (.loop b C (ϖ:=ϖ))
    = ⟨fun X ↦ b.iver * f (pgcl { ~C ; while ~b {~C} }) X + b.not.iver * X,
       fun a b h ↦ by simp; gcongr⟩
:= by
  ext X σ
  simp [aς, psucc, r]
  if hb : b σ = true then
    rw [tsum_eq_single ⟨(1, conf₁[~C ; while ~b { ~C }, σ]), by simp [hb]⟩] <;> simp [hb]
  else
    rw [tsum_eq_single ⟨(1, conf₁[⇓, σ]), by simp [hb]⟩] <;> simp [hb]
theorem aς.seq {C₁ C₂ : pGCL ϖ}
    (ih₁ : instSmallStepSemantics.aς awp C₁ = awp⟦~C₁⟧) :
    instSmallStepSemantics.aς awp (pgcl {~C₁ ; ~C₂}) = awp⟦~C₁⟧.comp awp⟦~C₂⟧ := by
  ext X σ
  simp [← ih₁, aς, tsum_succs_univ']
  congr! 7 with α α' hα
  rcases α with (_ | α')
  · contradiction
  · simp [psucc, r]
    simp [SmallStep.act] at hα
    obtain ⟨p₀, hα⟩ := hα
    apply C₂.tsum_after_eq' <;> simp [pGCL.after]
    rintro p C' σ' (⟨C', h, ⟨_⟩⟩ | ⟨h, ⟨_⟩⟩) hp h₀
    · simp_all
    · simp_all
      use .term, σ'

theorem dop_le_seq :
      instSmallStepSemantics.dop C ∘ instSmallStepSemantics.dop C'
    ≤ instSmallStepSemantics.dop pgcl {~C ; ~C'} := by
  apply SmallStepSemantics.dop_le_seq pGCL.seq pGCL.after <;> try simp
  · simp [psucc, pGCL.after]
    grind [psucc, pGCL.after]
  · grind [after_term, pGCL.after]
  · intros; split <;> simp_all
  · exact pGCL.after_inj

theorem aop_le_seq :
      instSmallStepSemantics.aop C ∘ instSmallStepSemantics.aop C'
    ≤ instSmallStepSemantics.aop pgcl {~C ; ~C'} := by
  apply SmallStepSemantics.aop_le_seq pGCL.seq pGCL.after <;> try simp
  · simp [psucc, pGCL.after]
    grind [psucc, pGCL.after]
  · grind [after_term, pGCL.after]
  · intros; split <;> simp_all
  · exact pGCL.after_inj

open scoped Classical in
theorem dwp_le_dop.loop (ih : C.dwp ≤ instSmallStepSemantics.dop C) :
    dwp⟦while ~b { ~C }⟧ ≤ instSmallStepSemantics.dop (.loop b C (ϖ:=ϖ)) := by
  intro X
  apply OrderHom.lfp_le
  nth_rw 2 [← dς_dop_eq_dop]
  intro σ
  simp [dς.loop]
  gcongr
  apply le_trans (fun _ ↦ ih _) dop_le_seq

open scoped Classical in
theorem awp_le_aop.loop (ih : C.awp ≤ instSmallStepSemantics.aop C) :
    awp⟦while ~b { ~C }⟧ ≤ instSmallStepSemantics.aop (.loop b C (ϖ:=ϖ)) := by
  intro X
  apply OrderHom.lfp_le
  nth_rw 2 [← aς_aop_eq_aop]
  intro σ
  simp [aς.loop]
  gcongr
  apply le_trans (fun _ ↦ ih _) aop_le_seq

open scoped Classical in
noncomputable instance instSoundDemonicExpectationTransformer :
    SoundDemonicExpectationTransformer (pGCL ϖ) (States ϖ) Termination Act where
  det_le_dop := by
    intro C; induction C with try simp_all; (try rw [← dς_dop_eq_dop]; simp; done)
    | seq C₁ C₂ ih₁ ih₂ =>
      apply le_trans _ dop_le_seq
      intro σ
      simp
      exact OrderHom.apply_mono ih₁ (ih₂ σ)
    | prob =>
      intro X
      rw [← dς_dop_eq_dop]; simp
      gcongr <;> apply_assumption
    | nonDet C₁ C₂ ih₁ ih₂ =>
      intro X
      rw [← dς_dop_eq_dop]; simp
      exact ⟨inf_le_of_left_le (ih₁ X), inf_le_of_right_le (ih₂ X)⟩
    | loop b C' ih => apply dwp_le_dop.loop ih
  det_prefixed_point := by
    apply le_of_eq
    funext C; induction C with try simp_all [dς.seq]
    | loop =>
      rw [dς.loop]
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
