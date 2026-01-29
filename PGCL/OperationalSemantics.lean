import PGCL.SmallStep2
import PGCL.WeakestLiberalPre

namespace pGCL

variable {𝒱 : Type*} {ϖ : Γ[𝒱]} [DecidableEq 𝒱]

@[simp]
noncomputable def cost_t : 𝔼[ϖ, ENNReal] →o Termination × States ϖ → ENNReal :=
  ⟨fun X c ↦ match c with
  | (.term, σ) => X σ
  | (.fault, _) => 0, fun _ _ _ _ ↦ by
    simp; split
    · apply_assumption
    · rfl⟩

@[simp]
noncomputable def cost_t' : 𝔼[ϖ, ENNReal] →o Termination × States ϖ → ENNReal :=
  ⟨fun X c ↦ match c with
  | (.term, σ) => X σ
  | (.fault, σ) => 1, fun _ _ _ _ ↦ by
    simp; split
    · apply_assumption
    · rfl⟩

@[simp]
noncomputable def cost_p : pGCL ϖ × States ϖ → ENNReal
  | conf₀[tick(~ r), σ] => r σ
  | conf₀[~c' ; ~_, σ] => cost_p conf₀[~c', σ]
  | _ => 0

@[simp]
noncomputable def cost_p' : pGCL ϖ × States ϖ → ENNReal := 0

noncomputable instance 𝕊
    (cT : 𝔼[ϖ, ENNReal] →o Termination × States ϖ → ENNReal) (cP : pGCL ϖ × States ϖ → ENNReal) :
    SmallStepSemantics (pGCL ϖ) (States ϖ) Termination Act where
  r := SmallStep
  relation_p_pos := SmallStep.p_ne_zero
  succs_sum_to_one := SmallStep.sums_to_one
  progress := SmallStep.progress
  cost_t := cT
  cost_p := cP

noncomputable instance : SmallStepSemantics (pGCL ϖ) (States ϖ) Termination Act := 𝕊 cost_t cost_p

variable (cT : 𝔼[ϖ, ENNReal] →o Termination × States ϖ → ENNReal)
variable (cP : pGCL ϖ × States ϖ → ENNReal)

-- @[simp] alias cP := cost_p

noncomputable abbrev 𝒪 := (𝕊 cT cP (ϖ:=ϖ)).mdp

open SmallStepSemantics

attribute [simp] SmallStepSemantics.r
attribute [simp] SmallStepSemantics.cost_t
attribute [simp] SmallStepSemantics.cost_p
attribute [simp] SmallStepSemantics.cost

open scoped Classical in
noncomputable instance : (𝕊 cost_t cost_p (ϖ:=ϖ)).FiniteBranching where
  finite := by simp [r, ← SmallStep.succs_univ_fin'_eq_r]

variable {f : pGCL ϖ → 𝔼[ϖ, ENNReal] →o 𝔼[ϖ, ENNReal]}

variable {C : pGCL ϖ} {σ : States ϖ}

@[simp]
theorem act_eq_SmallStep_act :
    (𝕊 cT cP).act (Conf.prog C σ) = (some ·) '' SmallStep.act (C, σ) := by
  ext
  simp [act, r, SmallStep.act, conf₂_to_conf]
  grind

@[simp]
theorem act_seq :
      (𝕊 cT cP).act (Conf.prog (pgcl {~C ; ~C'}) σ)
    = (𝕊 cT cP).act (Conf.prog C σ) := by
  ext; simp

attribute [simp] iInf_and
attribute [simp] iSup_and

variable {b : BExpr ϖ} [DecidablePred b] {O : Optimization}

open scoped Optimization.Notation

-- instance : Coe (𝔼[States ϖ] →o 𝔼[States ϖ]) (𝔼[ϖ, ENNReal] →o 𝔼[ϖ, ENNReal]) where
--   coe x := x

-- instance : HAdd (𝔼[ϖ, ENNReal] →o 𝔼[ϖ, ENNReal]) (𝔼[ϖ, ENNReal] →o 𝔼[ϖ, ENNReal]) (𝔼[ϖ, ENNReal] →o 𝔼[ϖ, ENNReal]) := OrderHom.instHAdd

@[reducible, simp]
noncomputable instance : HAdd (𝔼[ϖ, ENNReal] →o 𝔼[ϖ, ENNReal]) (𝔼[States ϖ] →o 𝔼[States ϖ]) (𝔼[ϖ, ENNReal] →o 𝔼[ϖ, ENNReal]) where
  hAdd a b :=
    let b' : 𝔼[ϖ, ENNReal] →o 𝔼[ϖ, ENNReal] := b
    a + b'

-- @[simp]
def cP' (f : pGCL ϖ × States ϖ → ENNReal) : pGCL ϖ → 𝔼[ϖ, ENNReal] →o 𝔼[ϖ, ENNReal] :=
  fun C ↦ ⟨fun X σ ↦ f (C, σ), fun a b h σ ↦ by simp⟩

omit [DecidableEq 𝒱] in
@[grind =, simp] theorem cP'_apply {f : pGCL ϖ × States ϖ → ENNReal} :
    cP' f C X = fun σ ↦ f (C, σ) := rfl

@[simp] theorem ς.skip :
      (𝕊 cT cP).ς O f skip
    = ⟨(fun X σ ↦ cP (pgcl {skip}, σ) + cT X (.term, σ)),
        fun _ _ h _ ↦ by
          simp; gcongr; apply cT.mono h⟩ := by
  ext X σ
  simp [ς, psucc, r, Optimization.act]
  rw [tsum_eq_single ⟨(1, conf₁[⇓, σ]), by simp⟩] <;> simp
@[simp] theorem ς.assign :
      (𝕊 cT cP).ς O f (pgcl {~x := ~e})
    -- = ⟨fun X σ ↦ X (σ[x ↦ e σ]), fun _ _ h σ ↦ h (σ[x ↦ e σ])⟩ := by
    = ⟨fun X σ ↦ cP (.assign x e, σ) + cT X (.term, σ[x ↦ e σ]),
        fun _ _ h _ ↦ by
          simp; gcongr; apply cT.mono h⟩ := by
  ext X σ
  simp [ς, psucc, r, Optimization.act]
  rw [tsum_eq_single ⟨(1, conf₁[⇓, σ[x ↦ e σ]]), by simp⟩] <;> simp
@[simp] theorem ς.tick {t} :
      (𝕊 cT cP).ς O f (.tick t)
    = ⟨fun X σ ↦ cP (.tick t, σ) + cT X (.term, σ),
        fun _ _ h _ ↦ by
          simp; gcongr; apply cT.mono h⟩ := by
  ext X σ
  simp [ς, psucc, r, Optimization.act]
  rw [tsum_eq_single ⟨(1, conf₁[⇓, σ]), by simp⟩] <;> simp
@[simp] theorem ς.observe :
      (𝕊 cT cP).ς O f (.observe b)
    = ⟨fun X σ ↦ cP (.observe b, σ) + i[b] σ * cT X (.term, σ) + (1 - i[b] σ) * cT X (.fault, σ),
        fun _ _ h σ ↦ by
          simp; gcongr
          all_goals apply cT.mono h⟩
:= by
  ext X σ
  simp [ς, psucc, r, Optimization.act]
  if hb : b σ then
    rw [tsum_eq_single ⟨(1, conf₁[⇓, σ]), by simp [hb]⟩] <;> simp [hb]
  else
    rw [tsum_eq_single ⟨(1, conf₁[↯, σ]), by simp [hb]⟩] <;> simp [hb]
@[simp] theorem ς.prob :
      (𝕊 cT cP).ς O f (.prob C₁ p C₂)
    = cP' cP (.prob C₁ p C₂) + p.pick' (f C₁) (f C₂) := by
  ext (X : 𝔼[ϖ, ENNReal]) σ
  simp [ς, psucc, r, Optimization.act]
  simp only [DFunLike.coe]
  simp
  if h₁₂ : C₁ = C₂ then
    subst_eqs
    simp
    rw [tsum_eq_single ⟨(1, conf₁[~C₁, σ]), by simp⟩] <;> simp
  else if hp₀ : p σ = 0 then
    have h₂₁ : ¬C₂ = C₁ := by grind
    rw [tsum_eq_single ⟨(1, conf₁[~C₂, σ]), by simp [h₁₂, h₂₁, hp₀]⟩] <;> simp_all [ProbExp.pick]
    grind
  else if hp₁ : p σ = 1 then
    have h₂₁ : ¬C₂ = C₁ := by grind
    rw [tsum_eq_single ⟨(1, conf₁[~C₁, σ]), by simp [hp₁, h₁₂]⟩] <;> simp_all [ProbExp.pick]
    grind
  else
    simp_all only [ProbExp.not_zero_off, ProbExp.lt_one_iff]
    rw [ENNReal.tsum_eq_add_tsum_ite ⟨(p σ, conf₁[~C₁, σ]), by simp [h₁₂, hp₀]⟩]
    simp_all only
    rw [tsum_eq_single ⟨(1 - p σ, conf₁[~C₂, σ]), by simp [h₁₂, hp₁]⟩] <;> simp
    · simp [ProbExp.pick]; grind
    · grind
open scoped Classical in
@[simp] theorem ς.nonDet :
    (𝕊 cT cP).ς O f (.nonDet C₁ C₂) = (cP' cP (.nonDet C₁ C₂)) + O.opt₂ (f C₁) (f C₂) := by
  ext X σ
  have : ((fun x ↦ some x) '' {Act.L, Act.R}) = {some .L, some .R} := by ext; simp; grind
  simp [ς_apply, psucc, r, Optimization.act, this]
  simp only [DFunLike.coe]; simp only [OrderHom.toFun_eq_coe]
  congr
  · rw [tsum_eq_single ⟨(1, conf₁[~C₁, σ]), by simp⟩] <;> simp
  · rw [tsum_eq_single ⟨(1, conf₁[~C₂, σ]), by simp⟩] <;> simp

open scoped Classical in
theorem ς.loop :
      (𝕊 cT cP).ς O f (.loop b C (ϖ:=ϖ))
    = (cP' cP (.loop b C))
      -- TODO: make this Φ
      + ⟨fun X σ ↦ i[b σ] * f (pgcl { ~C ; while ~b {~C} }) X σ + i[¬b σ] * cT X (.term, σ),
        fun a b h σ ↦ by
          simp; gcongr
          · apply (f _).mono h
          · apply cT.mono h⟩
:= by
  ext X σ
  simp [ς, psucc, r, Optimization.act]
  congr
  if hb : b σ then
    rw [tsum_eq_single ⟨(1, conf₁[~C ; while ~b { ~C }, σ]), by simp [hb]⟩] <;> simp [hb]
  else
    rw [tsum_eq_single ⟨(1, conf₁[⇓, σ]), by simp [hb]⟩] <;> simp [hb]

open scoped Classical in
theorem tsum_succs_univ' {α : Act} (f : (𝕊 cT cP).psucc C σ α → ENNReal) :
    (∑' s', f s') = ∑' s', if h : _ then f ⟨s', h⟩ else 0 := by
  symm
  apply tsum_eq_tsum_of_ne_zero_bij (↑↑·) _ _ (by simp_all)
  · intro ⟨_, _⟩ ⟨_, _⟩; simp; apply SetCoe.ext
  · simp_all
open scoped Classical in
theorem tsum_succs_univ'' {α : Act} (f : (𝕊 cT cost_p').psucc C σ α → ENNReal) :
    (∑' s', f s') = ∑' s', if h : _ then f ⟨s', h⟩ else 0 := by
  symm
  apply tsum_eq_tsum_of_ne_zero_bij (↑↑·) _ _ (by simp_all)
  · intro ⟨_, _⟩ ⟨_, _⟩; simp; apply SetCoe.ext
  · simp_all

theorem ς.seq' {C₁ C₂ : pGCL ϖ}
    (ih₁ : (𝕊 cost_t cost_p).ς O (wp O) C₁ = C₁.wp O) :
    (𝕊 cost_t cost_p).ς O (wp O) (pgcl {~C₁ ; ~C₂}) = (wp O C₁).comp (wp O C₂) := by
  ext X σ
  simp [← ih₁, ς, tsum_succs_univ', Optimization.act, OrderHom.comp]
  simp only [DFunLike.coe]
  simp
  congr! 5 with α' α
  clear α'
  simp [psucc, r]
  apply C₂.tsum_after_eq' <;> simp [pGCL.after]
  · rintro p C' σ' (⟨C', h, ⟨_⟩⟩ | ⟨h, ⟨_⟩⟩) hp h₀ <;> simp_all
    · simp only [DFunLike.coe] at h₀; simp only [OrderHom.toFun_eq_coe] at h₀
      grind
    -- · use .term, σ'; simp_all; exact h₀

theorem ς.seq'' {C₁ C₂ : pGCL ϖ}
    (ih₁ : (𝕊 cost_t' cost_p').ς O (wfp' O) C₁ = C₁.wfp' O) :
    (𝕊 cost_t' cost_p').ς O (wfp' O) (pgcl {~C₁ ; ~C₂}) = (wfp' O C₁).comp (wfp' O C₂) := by
  ext X σ
  simp [← ih₁, ς_apply, tsum_succs_univ', Optimization.act]
  congr! 4 with α' α
  clear α'
  simp [psucc, r]
  apply tsum_eq_tsum_of_ne_zero_bij (fun ⟨(p, C), _⟩ ↦ (p, C₂.after C))
  · intro ⟨⟨_, a⟩, _⟩ ⟨⟨_, b⟩, _⟩ h
    grind
  · rintro ⟨p, (C | t), σ⟩
      <;> simp only [after, Set.mem_range, Subtype.exists, Prod.exists, Function.mem_support]
    · grind [wfp', mul_eq_zero, Function.mem_support]
    · grind [one_ne_zero, mul_eq_zero, Function.mem_support]
  · simp [after, wfp']
    grind

theorem op_le_seq [(𝕊 cT cP).mdp.FiniteBranching]
    (t_const : 𝔼[ϖ, ENNReal])
    (hp : ∀ C C' σ, cP (pgcl {~C ; ~C'}, σ) = cP (C, σ))
    (ht : ∀ X σ, cT X (Termination.term, σ) ≤ X σ)
    (ht' : ∀ X σ, cT X (Termination.fault, σ) = t_const σ) :
      (𝕊 cT cP).op O C ∘ (𝕊 cT cP).op O C'
    ≤ (𝕊 cT cP).op O pgcl {~C ; ~C'} := by
  -- have ht₂ : ∀ (X : States ϖ → ENNReal) σ, cT X (Termination.term, σ) ≤ X σ := ht
  -- have ht'₂ : ∀ (X : States ϖ → ENNReal) σ, cT X (Termination.fault, σ) = t_const σ := ht'
  apply (𝕊 cT cP).op_le_seq pGCL.seq pGCL.after t_const <;> try simp [hp, hp']
  · intros; apply hp
  · simp
  · simp [psucc, pGCL.after]
    grind [psucc, pGCL.after]
  · grind [pGCL.after]
  · simp only [after, SmallStepSemantics.cost_t]
    grind
  · intros
    cases ‹Termination›
    · grind [after_fault]
    · apply ht
  · exact pGCL.after_inj

open scoped Classical in
theorem wp_le_op.loop (ih : C.wp O ≤ (𝕊 cost_t cost_p).op O C) :
    pgcl { while ~b { ~C } }.wp O ≤ (𝕊 cost_t cost_p).op O (.loop b C (ϖ:=ϖ)) := by
  intro X
  apply OrderHom.lfp_le
  nth_rw 2 [← (𝕊 cost_t cost_p).ς_op_eq_op]
  intro σ
  simp [ς.loop]
  simp [Φ]
  gcongr
  apply le_trans (ih _) <| op_le_seq cost_t cost_p 0 _ _ _ _ <;> simp

omit [DecidableEq 𝒱] in
@[simp] theorem Exp.mk_zero_eq : (fun _ ↦ 0 : 𝔼[ϖ, ENNReal]) = 0 := by rfl

noncomputable instance instET : (𝕊 cost_t cost_p).ET O (wp O (ϖ:=ϖ)) where
  et_le_op := by
    intro C; induction C with try simp_all; (try rw [← ς_op_eq_op]; cases O <;> simp [wp] <;> done)
    | assign =>
      rw [← ς_op_eq_op]
      intro X
      simp only [OrderHom.toFun_eq_coe, wp.assign_apply, ς.assign, cost_p, OrderHom.mk_apply,
        zero_add, OrderHom.coe_mk]
      rfl
    | seq C₁ C₂ ih₁ ih₂ =>
      apply le_trans _ (op_le_seq cost_t cost_p 0 _ _ _) <;> simp
      intro σ
      simp
      exact OrderHom.apply_mono ih₁ (ih₂ σ)
    | prob C₁ p C₂ ih₁ ih₂ =>
      intro X
      simp
      rw [← ς_op_eq_op]
      simp only [ς.prob, cP']
      simp only [instHAddOrderHomForallStatesENNReal, cost_p, OrderHom.add_apply, OrderHom.coe_mk,
        Exp.mk_zero_eq, ProbExp.pick'_apply, zero_add]
      gcongr <;> apply_assumption
    | nonDet C₁ C₂ ih₁ ih₂ =>
      intro X
      rw [← ς_op_eq_op]; simp
      gcongr <;> apply_assumption
    | loop b C' ih => apply wp_le_op.loop ih
    | tick r => rw [← ς_op_eq_op]; simp; rfl
    | observe b => rw [← ς_op_eq_op]; intro _ _; simp
  et_prefixed_point := by
    apply le_of_eq
    funext C; induction C with try simp_all [ς.seq']; (try rfl) <;> try ext; simp
    | loop b C' ih =>
      rw [ς.loop]
      ext
      simp
      nth_rw 2 [← wp_fp]
      simp only [Φ, OrderHom.coe_mk, OrderHom.mk_apply, Pi.add_apply, Pi.mul_apply,
        BExpr.iver_apply, BExpr.not_apply]

example : dwp (ϖ:=ϖ) = (𝕊 cost_t cost_p).op .Demonic := by rw [← instET.et_eq_op]
example : awp (ϖ:=ϖ) = (𝕊 cost_t cost_p).op .Angelic := by rw [← instET.et_eq_op]

/-- info: 'pGCL.instET' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms instET

noncomputable instance : SmallStepSemantics (pGCL ϖ) (States ϖ) Termination Act := 𝕊 cost_t' cost_p'
open scoped Classical in
noncomputable instance : (𝕊 cost_t' cost_p' (ϖ:=ϖ)).FiniteBranching where
  finite := by simp [r, ← SmallStep.succs_univ_fin'_eq_r]

open scoped Classical in
theorem wfp'_le_op.loop (ih : C.wfp' O ≤ (𝕊 cost_t' cost_p').op O C) :
    wfp'[O]⟦while ~b { ~C }⟧ ≤ (𝕊 cost_t' cost_p').op O (.loop b C (ϖ:=ϖ)) := by
  intro X
  apply OrderHom.lfp_le
  simp
  nth_rw 2 [← (𝕊 cost_t' cost_p').ς_op_eq_op]
  intro σ
  if hb : b σ then
    simp [ς.loop, BExpr.probOf, ProbExp.pick, hb]
    apply le_trans (ih _)
    simp
    apply op_le_seq _ _ 1 <;> try simp +contextual
  else
    simp [ς.loop, BExpr.probOf, ProbExp.pick, hb]

noncomputable instance instET' : (𝕊 cost_t' cost_p').ET O (wfp' O (ϖ:=ϖ)) where
  et_le_op := by
    intro C; induction C with try simp_all; (try rw [← ς_op_eq_op]; simp [wfp']; (try rfl); done)
    | seq C₁ C₂ ih₁ ih₂ =>
      apply le_trans _ (op_le_seq _ _ 1 _ _ _) <;> simp
      intro σ
      simp [wfp']
      exact OrderHom.apply_mono ih₁ (ih₂ σ)
    | prob C₁ p C₂ ih₁ ih₂ =>
      intro X
      rw [← ς_op_eq_op]
      simp only [OrderHom.toFun_eq_coe, ς.prob, instHAddOrderHomForallStatesENNReal,
        OrderHom.add_apply, cP'_apply, Pi.ofNat_apply, Exp.mk_zero_eq, ProbExp.pick'_apply,
        zero_add]
      simp [wfp']
      gcongr <;> apply_assumption
    | nonDet C₁ C₂ ih₁ ih₂ =>
      intro X
      rw [← ς_op_eq_op]; simp [wfp']
      gcongr <;> apply_assumption
    | loop b C' ih => apply wfp'_le_op.loop ih
    | observe b => rw [← ς_op_eq_op, wfp']; intro _ _; simp [BExpr.probOf, ProbExp.pick]
  et_prefixed_point := by
    apply le_of_eq
    funext C; induction C with try simp_all [ς.seq'']; (try rfl) <;> try ext; simp [wfp']; done
    | loop b C' ih =>
      rw [ς.loop]
      ext X σ
      simp
      nth_rw 1 [wfp']
      simp
      nth_rw 2 [← wfp'_fp]
      simp [fΦ, ProbExp.pick]
      if hb : b σ then simp [hb] else simp [hb]
    | observe b =>
      ext X σ
      simp [wfp']
      if hb : b σ then simp [hb] else simp [hb]

/-- info: 'pGCL.instET'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms instET'

example {C : pGCL ϖ} : wfp'[𝒟]⟦~C⟧ = (𝕊 cost_t' cost_p').op .Demonic C := by rw [instET'.et_eq_op]
example {C : pGCL ϖ} : wfp'[𝒜]⟦~C⟧ = (𝕊 cost_t' cost_p').op .Angelic C := by rw [instET'.et_eq_op]

end pGCL

#min_imports
