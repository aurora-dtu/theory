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
noncomputable def cost_p₀ : pGCL ϖ × States ϖ → ENNReal
  | conf₀[tick(~ r), σ] => r σ
  | conf₀[~c' ; ~_, σ] => cost_p₀ conf₀[~c', σ]
  | _ => 0
@[simp]
noncomputable def cost_p : Exp ϖ →o pGCL ϖ × States ϖ → ENNReal :=
  ⟨fun X c ↦ cost_p₀ c, fun _ _ _ ↦ by rfl⟩

noncomputable instance 𝕊 : SmallStepSemantics (pGCL ϖ) (States ϖ) Termination Act where
  r := SmallStep
  relation_p_pos := SmallStep.p_ne_zero
  succs_sum_to_one := SmallStep.sums_to_one
  progress := SmallStep.progress
  cost_t
  cost_p

noncomputable abbrev 𝒪 := (𝕊 (ϖ:=ϖ)).mdp

open SmallStepSemantics

attribute [simp] SmallStepSemantics.r
attribute [simp] SmallStepSemantics.cost_t
attribute [simp] SmallStepSemantics.cost_p
attribute [simp] SmallStepSemantics.cost

open scoped Classical in
noncomputable instance : (𝕊 (ϖ:=ϖ)).FiniteBranching where
  finite := by simp [r, ← SmallStep.succs_univ_fin'_eq_r]

variable {f : pGCL ϖ → Exp ϖ →o Exp ϖ}

variable {C : pGCL ϖ} {σ : States ϖ}

open scoped Classical in
@[simp, grind]
theorem act_eq_SmallStep_act :
    𝕊.act (Conf.prog C σ) = (some ·) '' SmallStep.act (C, σ) := by
  ext
  simp [act, r, SmallStep.act, conf₂_to_conf]
  grind

@[simp, grind]
theorem act_seq :
      𝕊.act (Conf.prog (pgcl {~C ; ~C'}) σ)
    = 𝕊.act (Conf.prog C σ) := by
  ext; simp

attribute [simp] iInf_and
attribute [simp] iSup_and

open MDP (Optimization)

variable {b : BExpr ϖ} [DecidablePred b] {O : Optimization}

@[simp] theorem ς.skip : 𝕊.ς O f skip = ⟨(· ·), fun ⦃_ _⦄ a ↦ a⟩ := by
  ext X σ
  simp [ς, psucc, r, Optimization.act]
  rw [tsum_eq_single ⟨(1, conf₁[⇓, σ]), by simp⟩] <;> simp
@[simp] theorem ς.assign :
      𝕊.ς O f (pgcl {~x := ~e})
    = ⟨fun X σ ↦ X (σ[x ↦ e σ]), fun _ _ h σ ↦ h (σ[x ↦ e σ])⟩ := by
  ext X σ
  simp [ς, psucc, r, Optimization.act]
  rw [tsum_eq_single ⟨(1, conf₁[⇓, σ[x ↦ e σ]]), by simp⟩] <;> simp
@[simp] theorem ς.tick {t} :
    𝕊.ς O f (.tick t) = ⟨fun X ↦ t + X, fun _ _ _ ↦ by simp; gcongr⟩ := by
  ext X σ
  simp [ς, psucc, r, Optimization.act]
  rw [tsum_eq_single ⟨(1, conf₁[⇓, σ]), by simp⟩] <;> simp
@[simp] theorem ς.assert :
    𝕊.ς O f (.assert b) = ⟨fun X ↦ b.iver * X, fun _ _ _ ↦ by simp; gcongr⟩
:= by
  ext X σ
  simp [ς, psucc, r, Optimization.act]
  if hb : b σ then
    rw [tsum_eq_single ⟨(1, conf₁[⇓, σ]), by simp [hb]⟩] <;> simp [hb]
  else
    rw [tsum_eq_single ⟨(1, conf₁[↯, σ]), by simp [hb]⟩] <;> simp [hb]
@[simp] theorem ς.prob :
      𝕊.ς O f (.prob C₁ p C₂)
    = ⟨fun X ↦ p.pick (f C₁ X) (f C₂ X),
       fun a b h ↦ by simp; apply ProbExp.pick_le <;> apply (f _).mono h⟩ := by
  ext X σ
  simp [ς, psucc, r, Optimization.act]
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
@[simp] theorem ς.nonDet : 𝕊.ς O f (.nonDet C₁ C₂) = O.opt₂ (f C₁) (f C₂) := by
  ext X σ
  have : ((fun x ↦ some x) '' {Act.L, Act.R}) = {some .L, some .R} := by ext; simp; grind
  simp [ς, psucc, r, Optimization.act, this]
  congr
  · rw [tsum_eq_single ⟨(1, conf₁[~C₁, σ]), by simp⟩] <;> simp
  · rw [tsum_eq_single ⟨(1, conf₁[~C₂, σ]), by simp⟩] <;> simp

open scoped Classical in
theorem ς.loop :
      𝕊.ς O f (.loop b C (ϖ:=ϖ))
    = ⟨fun X ↦ b.iver * f (pgcl { ~C ; while ~b {~C} }) X + b.not.iver * X,
       fun a b h ↦ by simp; gcongr⟩
:= by
  ext X σ
  simp [ς, psucc, r, Optimization.act]
  if hb : b σ then
    rw [tsum_eq_single ⟨(1, conf₁[~C ; while ~b { ~C }, σ]), by simp [hb]⟩] <;> simp [hb]
  else
    rw [tsum_eq_single ⟨(1, conf₁[⇓, σ]), by simp [hb]⟩] <;> simp [hb]

open scoped Classical in
theorem tsum_succs_univ' {α : Act} (f : 𝕊.psucc C σ α → ENNReal) :
    (∑' s', f s') = ∑' s', if h : _ then f ⟨s', h⟩ else 0 := by
  symm
  apply tsum_eq_tsum_of_ne_zero_bij (↑↑·) _ _ (by simp_all)
  · intro ⟨_, _⟩ ⟨_, _⟩; simp; apply SetCoe.ext
  · simp_all--; intro _ α p _ _; use α, p

noncomputable def wp (O : Optimization) : pGCL ϖ → Exp ϖ →o Exp ϖ :=
  match O with
  | .Angelic => pGCL.awp
  | .Demonic => pGCL.dwp

@[simp]
theorem wp_seq {C₁ C₂ : pGCL ϖ} : wp O (.seq C₁ C₂) = (wp O C₁).comp (wp O C₂) := by
   cases O <;> simp [wp]

theorem ς.seq {C₁ C₂ : pGCL ϖ}
    (ih₁ : 𝕊.ς O (wp O) C₁ = C₁.wp O) :
    𝕊.ς O (wp O) (pgcl {~C₁ ; ~C₂}) = (wp O C₁).comp (wp O C₂) := by
  ext X σ
  simp [← ih₁, ς, tsum_succs_univ', Optimization.act]
  congr! 5 with α' α
  clear α'
  simp [psucc, r]
  apply C₂.tsum_after_eq' <;> simp [pGCL.after]
  rintro p C' σ' (⟨C', h, ⟨_⟩⟩ | ⟨h, ⟨_⟩⟩) hp h₀
  · simp_all
  · simp_all
    use .term, σ'

theorem op_le_seq :
      𝕊.op O C ∘ 𝕊.op O C'
    ≤ 𝕊.op O pgcl {~C ; ~C'} := by
  apply SmallStepSemantics.op_le_seq pGCL.seq pGCL.after <;> try simp
  · simp [psucc, pGCL.after]
    grind [psucc, pGCL.after]
  · grind [after_term, pGCL.after]
  · intros; split <;> simp_all
  · exact pGCL.after_inj

open scoped Classical in
theorem wp_le_op.loop (ih : C.wp O ≤ 𝕊.op O C) :
    pgcl { while ~b { ~C } }.wp O ≤ 𝕊.op O (.loop b C (ϖ:=ϖ)) := by
  intro X
  cases O <;> simp [wp] at ih ⊢
  -- TOOD: unify proofs
  all_goals
    apply OrderHom.lfp_le
    nth_rw 2 [← ς_op_eq_op]
    intro σ
    simp [ς.loop]
    gcongr
    apply le_trans (fun _ ↦ ih _) op_le_seq

noncomputable instance instET : 𝕊.ET O (wp O (ϖ:=ϖ)) where
  et_le_op := by
    intro C; induction C with try simp_all; (try rw [← ς_op_eq_op]; cases O <;> simp [wp] <;> done)
    | assert b =>
      rw [← ς_op_eq_op]; cases O <;> simp [wp] <;> rfl
    | seq C₁ C₂ ih₁ ih₂ =>
      apply le_trans _ op_le_seq
      intro σ
      simp
      exact OrderHom.apply_mono ih₁ (ih₂ σ)
    | prob C₁ p C₂ ih₁ ih₂ =>
      intro X
      cases O
      all_goals
        simp [wp]
        rw [← ς_op_eq_op]
        simp
        gcongr <;> apply_assumption
    | nonDet C₁ C₂ ih₁ ih₂ =>
      intro X
      rw [← ς_op_eq_op]; simp
      cases O
      · simp [wp, Optimization.opt₂]
        exact ⟨le_sup_of_le_left (ih₁ X), le_sup_of_le_right (ih₂ X)⟩
      · simp [wp, Optimization.opt₂]
        exact ⟨inf_le_of_left_le (ih₁ X), inf_le_of_right_le (ih₂ X)⟩
    | loop b C' ih => apply wp_le_op.loop ih
  et_prefixed_point := by
    apply le_of_eq
    funext C; induction C with try simp_all [ς.seq]; cases O <;> simp_all [wp, awp, dwp] <;> try rfl
    | seq C₁ C₂ ih₁ ih₂ => rw [ς.seq ih₁]; simp
    | loop b C' ih =>
      rw [ς.loop]
      ext
      cases O
      · simp [wp] at ih ⊢
        nth_rw 2 [← awp_fp]
        rfl
      · simp [wp] at ih ⊢
        nth_rw 2 [← dwp_fp]
        rfl

example : dwp (ϖ:=ϖ) = 𝕊.op .Demonic := by rw [← instET.et_eq_op]; rfl
example : awp (ϖ:=ϖ) = 𝕊.op .Angelic := by rw [← instET.et_eq_op]; rfl

/-- info: 'pGCL.instET' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms instET

end pGCL
