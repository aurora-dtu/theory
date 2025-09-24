import MDP.Bellman
import MDP.Relational
import MDP.SmallStepSemantics
import PGCL.SmallStep2
import PGCL.WeakestPre
import PGCL.WeakestLiberalPre

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
noncomputable def cost_t' : Exp ϖ →o Termination × States ϖ → ENNReal :=
  ⟨fun X c ↦ match c with
  | (.term, σ) => X σ
  | (.fault, σ) => 1, fun _ _ _ _ ↦ by
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

@[simp]
noncomputable def cost_p' : Exp ϖ →o pGCL ϖ × States ϖ → ENNReal :=
  ⟨fun X c ↦ 0, fun _ _ _ ↦ by rfl⟩

noncomputable instance 𝕊
    (cT : Exp ϖ →o Termination × States ϖ → ENNReal) (cP : Exp ϖ →o pGCL ϖ × States ϖ → ENNReal) :
    SmallStepSemantics (pGCL ϖ) (States ϖ) Termination Act where
  r := SmallStep
  relation_p_pos := SmallStep.p_ne_zero
  succs_sum_to_one := SmallStep.sums_to_one
  progress := SmallStep.progress
  cost_t := cT
  cost_p := cP

noncomputable instance : SmallStepSemantics (pGCL ϖ) (States ϖ) Termination Act := 𝕊 cost_t cost_p

variable (cT : Exp ϖ →o Termination × States ϖ → ENNReal)
variable (cP : Exp ϖ →o pGCL ϖ × States ϖ → ENNReal)

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

variable {f : pGCL ϖ → Exp ϖ →o Exp ϖ}

variable {C : pGCL ϖ} {σ : States ϖ}

open scoped Classical in
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

omit [DecidableEq ϖ] in
@[simp] theorem Exp.zero_add (g : Exp ϖ) : ((fun _ ↦ 0) + g) = g := by ext; simp
omit [DecidableEq ϖ] in
@[simp] theorem Exp.add_zero (g : Exp ϖ) : (g + (fun _ ↦ 0)) = g := by ext; simp

namespace OrderHom

variable {α β : Type*} [Preorder α] [Preorder β] [Add β] [AddLeftMono β] [AddRightMono β]

instance : Add (α →o β) where
  add a b := ⟨fun x ↦ a x + b x, fun x y h ↦ by simp; gcongr⟩
@[simp] theorem add_apply (f g : α →o β) : (f + g) x = f x + g x := by rfl
@[simp] theorem zero_add {β : Type*} [Preorder β] [AddZeroClass β] [AddLeftMono β] [AddRightMono β]
    (g : α →o β) : ((⟨fun _ ↦ 0, monotone_const⟩ : α →o β) + g) = g := by ext; simp
@[simp] theorem add_zero {β : Type*} [Preorder β] [AddZeroClass β] [AddLeftMono β] [AddRightMono β]
    (g : α →o β) : (g + (⟨fun _ ↦ 0, monotone_const⟩ : α →o β)) = g := by ext; simp

instance {α β : Type*} [Preorder β] [Add β] [i : AddRightMono β] : AddRightMono (α → β) where
  elim a b c h i := by simp [Function.swap]; gcongr; apply h
instance {α β : Type*} [Preorder β] [Add β] [i : AddLeftMono β] : AddLeftMono (α → β) where
  elim a b c h i := by simp only [Pi.add_apply]; gcongr; apply h

end OrderHom

@[simp]
def cP' (f : Exp ϖ →o pGCL ϖ × States ϖ → ENNReal) : pGCL ϖ → Exp ϖ →o Exp ϖ :=
  fun C ↦ ⟨fun X σ ↦ f X (C, σ), fun a b h σ ↦ by simp; apply f.mono h⟩

@[simp] theorem ς.skip :
      (𝕊 cT cP).ς O f skip
    = ⟨(fun X σ ↦ cP X (pgcl {skip}, σ) + cT X (.term, σ)),
        fun _ _ h _ ↦ by
          simp; gcongr
          · apply cP.mono h
          · apply cT.mono h⟩ := by
  ext X σ
  simp [ς, psucc, r, Optimization.act]
  rw [tsum_eq_single ⟨(1, conf₁[⇓, σ]), by simp⟩] <;> simp
@[simp] theorem ς.assign :
      (𝕊 cT cP).ς O f (pgcl {~x := ~e})
    -- = ⟨fun X σ ↦ X (σ[x ↦ e σ]), fun _ _ h σ ↦ h (σ[x ↦ e σ])⟩ := by
    = ⟨fun X σ ↦ cP X (.assign x e, σ) + cT X (.term, σ[x ↦ e σ]),
        fun _ _ h _ ↦ by
          simp
          gcongr
          · apply cP.mono h
          · apply cT.mono h⟩ := by
  ext X σ
  simp [ς, psucc, r, Optimization.act]
  rw [tsum_eq_single ⟨(1, conf₁[⇓, σ[x ↦ e σ]]), by simp⟩] <;> simp
@[simp] theorem ς.tick {t} :
      (𝕊 cT cP).ς O f (.tick t)
    = ⟨fun X σ ↦ cP X (.tick t, σ) + cT X (.term, σ),
        fun _ _ h _ ↦ by
          simp; gcongr
          · apply cP.mono h
          · apply cT.mono h⟩ := by
  ext X σ
  simp [ς, psucc, r, Optimization.act]
  rw [tsum_eq_single ⟨(1, conf₁[⇓, σ]), by simp⟩] <;> simp
@[simp] theorem ς.observe :
      (𝕊 cT cP).ς O f (.observe b)
    = ⟨fun X σ ↦ cP X (.observe b, σ) + i[b] σ * cT X (.term, σ) + (1 - i[b] σ) * cT X (.fault, σ),
        fun _ _ h σ ↦ by
          simp; gcongr
          · apply cP.mono h
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
    = cP' cP (.prob C₁ p C₂) + ⟨fun X ↦ p.pick (f C₁ X) (f C₂ X), fun a b h ↦ by simp; gcongr⟩ := by
  ext X σ
  simp [ς, psucc, r, Optimization.act]
  if h₁₂ : C₁ = C₂ then
    subst_eqs
    simp_all only [ProbExp.pick_same]
    rw [tsum_eq_single ⟨(1, conf₁[~C₁, σ]), by simp⟩] <;> simp
  else if hp₀ : p σ = 0 then
    have h₂₁ : ¬C₂ = C₁ := by grind
    rw [tsum_eq_single ⟨(1, conf₁[~C₂, σ]), by simp [h₁₂, h₂₁, hp₀]⟩] <;> simp_all [ProbExp.pick]
    grind
  else if hp₁ : p σ = 1 then
    have h₂₁ : ¬C₂ = C₁ := by grind
    rw [tsum_eq_single ⟨(1, conf₁[~C₁, σ]), by simp [hp₁, h₁₂]⟩]
      <;> simp_all [ProbExp.pick]
    grind
  else
    simp_all only [ProbExp.not_zero_off, ProbExp.lt_one_iff]
    rw [ENNReal.tsum_eq_add_tsum_ite ⟨(p σ, conf₁[~C₁, σ]), by simp [h₁₂, hp₀]⟩]
    simp_all only
    rw [tsum_eq_single ⟨(1 - p σ, conf₁[~C₂, σ]), by simp [h₁₂, hp₁]⟩] <;> simp
    · simp [ProbExp.pick, -ProbExp.pick_of]; grind
    · grind
open scoped Classical in
@[simp] theorem ς.nonDet :
    (𝕊 cT cP).ς O f (.nonDet C₁ C₂) = (cP' cP (.nonDet C₁ C₂)) + O.opt₂ (f C₁) (f C₂) := by
  ext X σ
  have : ((fun x ↦ some x) '' {Act.L, Act.R}) = {some .L, some .R} := by ext; simp; grind
  simp [ς, psucc, r, Optimization.act, this]
  congr
  · rw [tsum_eq_single ⟨(1, conf₁[~C₁, σ]), by simp⟩] <;> simp
  · rw [tsum_eq_single ⟨(1, conf₁[~C₂, σ]), by simp⟩] <;> simp

open scoped Classical in
theorem ς.loop :
      (𝕊 cT cP).ς O f (.loop b C (ϖ:=ϖ))
    = (cP' cP (.loop b C))
      + ⟨fun X σ ↦ b.iver σ * f (pgcl { ~C ; while ~b {~C} }) X σ + b.not.iver σ * cT X (.term, σ),
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
  simp [← ih₁, ς, tsum_succs_univ', Optimization.act]
  congr! 5 with α' α
  clear α'
  simp [psucc, r]
  apply C₂.tsum_after_eq' <;> simp [pGCL.after]
  rintro p C' σ' (⟨C', h, ⟨_⟩⟩ | ⟨h, ⟨_⟩⟩) hp h₀ <;> simp_all
  · use .term, σ'

theorem ς.seq'' {C₁ C₂ : pGCL ϖ}
    (ih₁ : (𝕊 cost_t' cost_p').ς O (wfp' O) C₁ = C₁.wfp' O) :
    (𝕊 cost_t' cost_p').ς O (wfp' O) (pgcl {~C₁ ; ~C₂}) = (wfp' O C₁).comp (wfp' O C₂) := by
  ext X σ
  simp [← ih₁, ς, tsum_succs_univ', Optimization.act]
  congr! 4 with α' α
  clear α'
  simp [psucc, r]
  apply tsum_eq_tsum_of_ne_zero_bij (fun ⟨(p, C), _⟩ ↦ (p, C₂.after C))
  · intro ⟨⟨_, a⟩, _⟩ ⟨⟨_, b⟩, _⟩ h
    simp_all only [Prod.mk.injEq, Subtype.mk.injEq, true_and]
    exact C₂.after_inj h.right
  · rintro ⟨p, (C | t), σ⟩ <;> simp [after]
    · rintro (⟨C', h₁, ⟨_⟩⟩ | h)
      · simp_all [wfp']
      · grind
    · intros
      simp_all
      subst_eqs
      use .fault, σ
      simp_all
  · simp [after, wfp']
    grind

theorem op_le_seq [(𝕊 cT cP).mdp.FiniteBranching]
    (t_const : Exp ϖ)
    (hp : ∀ X C C' σ, cP X (pgcl {~C ; ~C'}, σ) = cP X (C, σ))
    (hp' : ∀ X C σ, cP X (C, σ) = cP 0 (C, σ))
    (ht : ∀ X σ, cT X (Termination.term, σ) ≤ X σ)
    (ht' : ∀ X σ, cT X (Termination.fault, σ) = t_const σ) :
      (𝕊 cT cP).op O C ∘ (𝕊 cT cP).op O C'
    ≤ (𝕊 cT cP).op O pgcl {~C ; ~C'} := by
  apply (𝕊 cT cP).op_le_seq pGCL.seq pGCL.after t_const <;> try simp [hp, hp']
  · simp [psucc, pGCL.after]
    grind [psucc, pGCL.after]
  · grind [after_term, pGCL.after]
  · intros; subst_eqs; apply ht
  · exact pGCL.after_inj

open scoped Classical in
theorem wp_le_op.loop (ih : C.wp O ≤ (𝕊 cost_t cost_p).op O C) :
    pgcl { while ~b { ~C } }.wp O ≤ (𝕊 cost_t cost_p).op O (.loop b C (ϖ:=ϖ)) := by
  intro X
  apply OrderHom.lfp_le
  nth_rw 2 [← (𝕊 cost_t cost_p).ς_op_eq_op]
  intro σ
  simp [ς.loop]
  gcongr
  apply le_trans (fun _ ↦ ih _) (op_le_seq cost_t cost_p 0 _ _ _ _) <;> simp

noncomputable instance instET : (𝕊 cost_t cost_p).ET O (wp O (ϖ:=ϖ)) where
  et_le_op := by
    intro C; induction C with try simp_all; (try rw [← ς_op_eq_op]; cases O <;> simp [wp] <;> done)
    | seq C₁ C₂ ih₁ ih₂ =>
      apply le_trans _ (op_le_seq cost_t cost_p 0 _ _ _ _) <;> simp
      intro σ
      simp
      exact OrderHom.apply_mono ih₁ (ih₂ σ)
    | prob C₁ p C₂ ih₁ ih₂ =>
      intro X
      rw [← ς_op_eq_op]; simp
      gcongr <;> apply_assumption
    | nonDet C₁ C₂ ih₁ ih₂ =>
      intro X
      rw [← ς_op_eq_op]; simp
      gcongr <;> apply_assumption
    | loop b C' ih => apply wp_le_op.loop ih
    | tick r => rw [← ς_op_eq_op]; simp; rfl
    | observe b => rw [← ς_op_eq_op]; simp; rfl
  et_prefixed_point := by
    apply le_of_eq
    funext C; induction C with try simp_all [ς.seq'] <;> (try rfl) <;> try ext; simp
    | loop b C' ih =>
      rw [ς.loop]
      ext
      simp
      nth_rw 2 [← wp_fp]
      rfl

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
    intro C; induction C with try simp_all; (try rw [← ς_op_eq_op]; simp [wfp']; done)
    | seq C₁ C₂ ih₁ ih₂ =>
      intro X
      apply le_trans _ (op_le_seq _ _ 1 _ _ _ _) <;> simp
      intro σ
      simp [wfp']
      exact OrderHom.apply_mono ih₁ (ih₂ σ)
    | prob C₁ p C₂ ih₁ ih₂ =>
      intro X
      rw [← ς_op_eq_op]; simp [wfp']
      gcongr <;> apply_assumption
    | nonDet C₁ C₂ ih₁ ih₂ =>
      intro X
      rw [← ς_op_eq_op]; simp [wfp']
      gcongr <;> apply_assumption
    | loop b C' ih => apply wfp'_le_op.loop ih
    | observe b => rw [← ς_op_eq_op, wfp']; simp [BExpr.probOf, ProbExp.pick]; rfl
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
      simp [fΦ, ProbExp.pick, -ProbExp.pick_of]
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
