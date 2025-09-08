import MDP.Bellman
import MDP.Relational
import PGCL.SmallStep
import PGCL.WeakestPre

/-!
# Operation MDP derived from `SmallStep`.

## Main definitions

* `pGCL.𝒬`: The derived `MDP` from the small step semantics.
* `pGCL.𝒬.ς`: The characteristic function of doing one step in the `pGCL.𝒬`.
* `pGCL.op`: The demonic expected cost given by the least fixed point of the Bellman-operator
  `MDP.Φ`.
* `pGCL.op_eq_wp`: The proof connecting the fixed point characteristic of the operational
  semantics to the weakest preexpectation formalization of `pGCL`.
-/

namespace pGCL

open OrderHom

variable {ϖ : Type*} [DecidableEq ϖ]

noncomputable def 𝒬 : MDP (Conf ϖ) Act :=
  MDP.ofRelation SmallStep SmallStep.p_ne_zero SmallStep.sums_to_one SmallStep.progress

namespace General

end General

namespace 𝒬

@[simp]
theorem act_eq : 𝒬.act = SmallStep.act (ϖ:=ϖ) := by
  ext c α
  simp [𝒬, MDP.ofRelation_act, SmallStep.act]

@[simp]
theorem succs_univ_eq : (𝒬 (ϖ:=ϖ)).succs_univ = fun c ↦ {c' | ∃ α p, c ⤳[α,p] c'} := by
  simp [𝒬]

@[simp]
theorem P_eq : (𝒬 (ϖ:=ϖ)).P = (fun c α c' ↦ ∑' (p : { p // c ⤳[α,p] c' }), ↑p) := by simp [𝒬]

theorem P_support_eq_succs : (Function.support (𝒬.P c α)) = SmallStep.succs (ϖ:=ϖ) c α := by
  ext c'
  simp [SmallStep.succs]
  constructor
  · simp; intro p h hp; use p
  · simp; intro p h; use p, h, SmallStep.p_ne_zero h

instance : MDP.FiniteBranching (𝒬 (ϖ:=ϖ)) where
  act_fin c := Set.toFinite (𝒬.act c)
  succs_fin c α := by
    simp only [𝒬.P_support_eq_succs, SmallStep.succs_eq_succs_fin, Finset.finite_toSet]

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
  | none => simp
  | some x =>
    obtain ⟨p, σ⟩ := x
    induction p with
    | fault => simp
    | term => simp; apply hab
    | prog p =>
      induction p with simp
      | seq C₁ C₂ ih₁ ih₂ =>
        simp_all
        split at ih₁ <;> simp_all

@[simp]
theorem cost_X_of_pGCL : cost X conf[~C, σ] = cost 0 conf[~C, σ] := by induction C <;> simp_all

@[simp]
theorem Φ_simp {C : Conf ϖ} :
    𝒬.dΦ c f C = c C + ⨅ α ∈ SmallStep.act C, ∑' s' : 𝒬.succs_univ C, 𝒬.P C α s' * f s'
:= by simp [dΦ, MDP.Φf, iInf_subtype]

@[simp]
theorem bot_eq {X : Exp ϖ} : (𝒬.dΦ (cost X))^[i] ⊥ none = 0 := by
  induction i <;> simp_all [-Function.iterate_succ, Function.iterate_succ']

noncomputable instance : Decidable (s' ∈ (𝒬 (ϖ:=ϖ)).succs_univ s) := Classical.propDecidable _

theorem tsum_succs_univ' (f : (𝒬 (ϖ:=ϖ)).succs_univ c → ENNReal) :
    (∑' s', f s') = ∑' s', if h : _ then f ⟨s', h⟩ else 0 := by
  symm
  apply tsum_eq_tsum_of_ne_zero_bij (↑↑·) _ _ (by simp_all)
  · intro ⟨_, _⟩ ⟨_, _⟩; simp; apply SetCoe.ext
  · simp_all; intro _ α p _ _; use α, p

variable {X : Exp ϖ}

@[simp]
theorem term_eq : (𝒬.dΦ (cost X))^[i] ⊥ conf[⇓, σ] = if i = 0 then 0 else X σ := by
  induction i <;> simp_all [-Function.iterate_succ, Function.iterate_succ', 𝒬.tsum_succs_univ']
@[simp]
theorem fault_eq : (𝒬.dΦ (cost X))^[i] ⊥ conf[↯, σ] = 0 := by
  induction i <;> simp_all [-Function.iterate_succ, Function.iterate_succ', 𝒬.tsum_succs_univ']

@[simp]
theorem lfp_Φ_bot : lfp (𝒬.dΦ <| cost X) none = 0 := by simp lfp_dΦ_eq_iSup_dΦΦ]

@[simp]
theorem lfp_Φ_term : lfp (𝒬.dΦ <| cost X) conf[⇓, σ] = X σ := by
  rw [← map_lfp]; simp_all [tsum_succs_univ']
@[simp]
theorem lfp_Φ_fault : lfp (𝒬.dΦ <| cost X) conf[↯, σ] = 0 := by
  rw [← map_lfp]; simp_all [tsum_succs_univ']

noncomputable def ς : (pGCL ϖ → Exp ϖ →o Exp ϖ) →o pGCL ϖ → Exp ϖ →o Exp ϖ :=
  ⟨fun Y ↦ (fun C ↦ ⟨fun X σ ↦
    𝒬.dΦ (cost X)
      (match · with
      | conf[⇓,σ'] => X σ' | conf[↯,σ'] => 0 | conf[~C',σ'] => Y C' X σ' | ⊥ => 0) conf[~C, σ],
      fun a b h σ ↦ by
        simp
        gcongr
        split
        · apply h
        · rfl
        · apply (Y _).mono h
        · rfl⟩),
    by
      intro _ _ _ _ _ _
      apply (𝒬.dΦ _).mono
      rintro (_ | ⟨_ | _, _⟩) <;> try rfl
      apply_assumption⟩

variable {f : pGCL ϖ → Exp ϖ →o Exp ϖ}

@[simp] theorem ς.skip : ς f skip = ⟨(· ·), fun ⦃_ _⦄ a ↦ a⟩ := by simp_all [ς, 𝒬.tsum_succs_univ']
@[simp] theorem ς.assign :
      ς f (pgcl {~x := ~e})
    = ⟨fun X σ ↦ f .skip X (σ[x ↦ e σ]), fun a b h σ ↦ by simp; apply (f _).mono h⟩ :=
  by simp_all [ς, 𝒬.tsum_succs_univ']
@[simp] theorem ς.tick : ς f (.tick r) = ⟨fun X ↦ r + f .skip X, fun _ _ _ ↦ by simp; gcongr⟩ := by
  simp_all [ς, 𝒬.tsum_succs_univ']; rfl
@[simp] theorem ς.assert :
    ς f (.assert b) = ⟨fun X ↦ b.iver * f .skip X, fun _ _ _ ↦ by simp; gcongr⟩ := by
  ext X
  simp_all [ς, 𝒬.tsum_succs_univ', BExpr.iver]; grind
@[simp] theorem ς.prob :
      ς f (.prob C₁ p C₂)
    = ⟨fun X ↦ p.pick (f C₁ X) (f C₂ X),
       fun a b h ↦ by simp; apply ProbExp.pick_le <;> apply (f _).mono h⟩ := by
  simp only [ς]
  simp only [Φ_simp, cost_X_of_pGCL, P_eq, SmallStep.tsum_p, tsum_succs_univ', succs_univ_eq,
    Set.mem_setOf_eq, coe_mk, cost, SmallStep.act_prob, Set.mem_singleton_iff, SmallStep.prob_iff,
    exists_and_left, exists_eq_left, dite_eq_ite, iInf_iInf_eq_left, true_and, zero_add]
  ext X σ
  simp only [SmallStep.prob_iff, exists_and_left, exists_eq_left, coe_mk]
  rw [ENNReal.tsum_eq_add_tsum_ite conf[~C₁,σ], ENNReal.tsum_eq_add_tsum_ite conf[~C₂,σ]]
  by_cases C₁ = C₂ <;> simp_all [eq_comm, ite_and]
@[simp] theorem ς.nonDet : ς f (.nonDet C₁ C₂) = f C₁ ⊓ f C₂ := by
  ext X σ
  simp [ς, dΦ, MDP.Φf, 𝒬.tsum_succs_univ']
  simp_all [ite_and]
  apply le_antisymm <;> simp
  · constructor
    · apply iInf_le_of_le ⟨.L, by simp⟩
      rw [tsum_eq_single conf[~C₁,σ] (by simp_all [Imp.swap])]; simp
    · apply iInf_le_of_le ⟨.R, by simp⟩
      rw [tsum_eq_single conf[~C₂,σ] (by simp_all [Imp.swap])]; simp
  · rintro α (⟨_, _⟩ | ⟨_, _⟩)
    · rw [ENNReal.tsum_eq_add_tsum_ite conf[~C₁,σ]]; simp
    · rw [ENNReal.tsum_eq_add_tsum_ite conf[~C₂,σ]]; simp
theorem ς.loop :
      ς f (.loop b C)
    = ⟨fun X ↦ b.iver * f (pgcl { ~C ; while ~b {~C} }) X + b.not.iver * f .skip X,
       fun a b h ↦ by simp; gcongr⟩
:= by
  ext X σ
  simp [ς, 𝒬.tsum_succs_univ']
  split_ifs <;> simp_all

end 𝒬

open 𝒬

noncomputable def op (C : pGCL ϖ) : Exp ϖ →o Exp ϖ :=
  ⟨fun X ↦ (lfp (𝒬.dΦ <| cost X) <| conf[~C, ·]), fun a b h σ ↦ by
    suffices lfp (dΦ (cost a)) ≤ lfp (dΦ (cost b)) by exact this _
    gcongr
    apply MDP.Φ.monotone' (cost_mono h)⟩

theorem op_eq_iSup_Φ :
    op (ϖ:=ϖ)
  = ⨆ n, fun C ↦ ⟨fun X σ ↦ (𝒬.dΦ (cost X))^[n] ⊥ conf[~C,σ], fun a b h σ ↦ by
    simp
    suffices (⇑(dΦ (cost a)))^[n] ⊥ ≤ (⇑(dΦ (cost b)))^[n] ⊥ by apply this
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [Function.iterate_succ', Function.comp_apply]
      exact apply_mono (MDP.Φ.monotone' (cost_mono h)) ih⟩ := by
  ext C X σ; rw [op]
  simp [fixedPoints.lfp_eq_sSup_iterate _ dΦ_ωScottContinuous]
theorem op_eq_iSup_succ_Φ :
      op (ϖ:=ϖ)
    = ⨆ n, fun C ↦ ⟨fun X σ ↦ (𝒬.dΦ (cost X))^[n + 1] ⊥ conf[~C,σ], fun a b h σ ↦ by
      simp only
      suffices (⇑(dΦ (cost a)))^[n + 1] ⊥ ≤ (⇑(dΦ (cost b)))^[n + 1] ⊥ by apply this
      induction n with
      | zero => simp; apply MDP.Φ.monotone' (cost_mono h)
      | succ n ih =>
        simp only [Function.iterate_succ', Function.comp_apply] at ih ⊢
        exact apply_mono (MDP.Φ.monotone' (cost_mono h)) ih⟩ := by
  ext C X σ; rw [op]
  simp only [coe_mk, _root_.iSup_apply, coe_iSup]
  rw [fixedPoints.lfp_eq_sSup_iterate _ dΦ_ωScottContinuous]
  rw [← iSup_iterate_succ]
  simp
theorem ς_op_eq_op : ς (ϖ:=ϖ) op = op := by
  ext C X σ
  simp [op]
  rw [← map_lfp]
  simp only [ς, OrderHom.coe_mk]
  congr! 3 with C'
  rcases C' with ⟨none, σ'⟩ | ⟨C', σ'⟩ | _ <;> simp [op]

@[simp] theorem op_skip : op (ϖ:=ϖ) .skip = ⟨(· ·), fun ⦃_ _⦄ ↦ (·)⟩ := by rw [← ς_op_eq_op]; simp

theorem op_isLeast (b : pGCL ϖ → Exp ϖ →o Exp ϖ) (h : ς b ≤ b) : op ≤ b := by
  rw [op_eq_iSup_Φ, iSup_le_iff]
  intro n
  induction n with
  | zero => intros _ _ _; simp
  | succ i ih =>
    refine le_trans (fun C X σ ↦ ?_) h
    simp [Function.iterate_succ', ς, -Function.iterate_succ]
    gcongr
    split
    · simp_all only [term_eq]; split_ifs <;> simp
    · simp_all only [fault_eq, le_refl]
    · simp_all only; exact ih _ X _
    · simp_all only [bot_eq, le_refl]

theorem lfp_ς_eq_op : lfp (ς (ϖ:=ϖ)) = op :=
  (lfp_le_fixed _ ς_op_eq_op).antisymm (le_lfp _ op_isLeast)

variable {C : pGCL ϖ}

attribute [-simp] Function.iterate_succ in
theorem op_le_seq : C.op ∘ C'.op ≤ pgcl {~C ; ~C'}.op := by
  intro X σ
  nth_rw 1 [op_eq_iSup_succ_Φ]
  simp
  intro n
  induction n generalizing C C' σ with
  | zero => nth_rw 2 [← ς_op_eq_op]; simp_all [ς]
  | succ i ih =>
    nth_rw 2 [← ς_op_eq_op]
    rw [Function.iterate_succ', Function.comp_apply]
    simp [ς, 𝒬.tsum_succs_univ']
    refine add_le_add (le_refl _) (iInf₂_mono fun α hα ↦ C'.tsum_after_le ?_ ?_ ?_ ?_)
    all_goals intros; simp_all
    all_goals split_ifs <;> simp_all [mul_le_mul]

theorem ς_wp_le_wp : ς (ϖ:=ϖ) wp ≤ wp := by
  apply le_of_eq
  funext C; induction C with try simp_all
  | loop =>
    rw [ς.loop]
    ext X σ
    simp; nth_rw 2 [← wp_fp]; rfl
  | seq C₁ C₂ ih₁ ih₂ =>
    ext X σ
    rw [← ih₁]
    simp [ς, 𝒬.tsum_succs_univ']
    congr! 4
    apply C₂.tsum_after_eq <;> simp_all; split_ifs <;> simp_all
    rintro _ _ _ _ _ h ⟨_⟩ _ _ h' ⟨_⟩ hp _
    exact ⟨⟨_, _, h⟩, _, h', hp⟩

theorem wp_le_op.loop (ih : C.wp ≤ C.op) : wp⟦while ~b { ~C }⟧ ≤ op (.loop b C) := by
  intro X
  apply lfp_le
  nth_rw 2 [← ς_op_eq_op]
  intro σ
  simp [ς, 𝒬.tsum_succs_univ', BExpr.iver, BExpr.not]
  split_ifs <;> simp_all
  apply le_trans (fun _ ↦ ih _) op_le_seq

theorem wp_le_op : wp (ϖ:=ϖ) ≤ op := by
  intro C
  induction C with (try rw [← ς_op_eq_op]; simp; done)
  | prob C₁ p C₂ ih₁ ih₂ => rw [← ς_op_eq_op]; intro X; simp; gcongr <;> apply_assumption
  | nonDet C₁ C₂ ih₁ ih₂ =>
    intro X σ; rw [← ς_op_eq_op]; specialize ih₁ X σ; specialize ih₂ X σ; simp_all
  | loop b C ih => exact wp_le_op.loop ih
  | seq C₁ C₂ ih₁ ih₂ =>
    intro; simp; exact ((wp _).mono (ih₂ _)).trans (ih₁ _) |>.trans (op_le_seq _)

theorem op_eq_wp : op (ϖ:=ϖ) = wp := (op_isLeast _ ς_wp_le_wp).antisymm wp_le_op

end pGCL
