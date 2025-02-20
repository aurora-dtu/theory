import PGCL.SmallStep

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
  | ·⟨⇓ ϖ, σ⟩ => X σ
  | ·⟨tick r, σ⟩ => r σ
  | ·⟨c' ;; _, σ⟩ => cost X (·⟨c', σ⟩)
  | _ => 0

@[simp] theorem cost_X_of_pGCL : cost X (·⟨C, σ⟩) = cost 0 (·⟨C, σ⟩) := by induction C <;> simp_all

@[simp]
theorem Φ_simp {C : Conf ϖ} :
    𝒬.Φ c f C = c C + ⨅ α ∈ SmallStep.act C, ∑' s' : 𝒬.succs_univ C, 𝒬.P C α s' * f s'
:= by simp [MDP.Φ, MDP.Φf, iInf_subtype]

@[simp]
theorem bot_eq {X : Exp ϖ} : (𝒬.Φ (cost X))^[i] ⊥ none = 0 := by
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
theorem sink_eq : (𝒬.Φ (cost X))^[i] ⊥ (some (none, σ)) = if i = 0 then 0 else X σ := by
  induction i <;> simp_all [-Function.iterate_succ, Function.iterate_succ', 𝒬.tsum_succs_univ']

@[simp]
theorem lfp_Φ_bot : 𝒬.lfp_Φ (cost X) none = 0 := by simp [MDP.lfp_Φ_eq_iSup_Φ]

@[simp]
theorem lfp_Φ_sink : 𝒬.lfp_Φ (cost X) (some (none, σ)) = X σ := by
  rw [← MDP.map_lfp_Φ]; simp_all [tsum_succs_univ']

noncomputable def ς : (pGCL ϖ → Exp ϖ → Exp ϖ) →o pGCL ϖ → Exp ϖ → Exp ϖ :=
  ⟨fun Y ↦ (fun C X σ ↦
    𝒬.Φ (cost X) (match · with | ·⟨⇓ ϖ,σ'⟩ => X σ' | ·⟨C',σ'⟩ => Y C' X σ' | ⊥ => 0) (·⟨C, σ⟩))
    , by
      intro _ _ _ _ _ _
      apply (𝒬.Φ _).mono
      rintro (_ | ⟨_ | _, _⟩) <;> try rfl
      apply_assumption⟩

variable {f : pGCL ϖ → Exp ϖ → Exp ϖ}

@[simp] theorem ς.skip : ς f skip = (· ·) := by simp_all [ς, 𝒬.tsum_succs_univ']
@[simp] theorem ς.assign : ς f (.assign x e) = fun X σ ↦ f .skip X (σ[x ↦ e σ]) :=
  by simp_all [ς, 𝒬.tsum_succs_univ']
@[simp] theorem ς.tick : ς f (.tick r) = fun X ↦ r + f .skip X := by
  simp_all [ς, 𝒬.tsum_succs_univ']; rfl
@[simp] theorem ς.prob : ς f (.prob C₁ p C₂) = fun X ↦ p.pick (f C₁ X) (f C₂ X) := by
  simp_all [ς, 𝒬.tsum_succs_univ']
  ext X σ
  rw [ENNReal.tsum_eq_add_tsum_ite (·⟨C₁,σ⟩), ENNReal.tsum_eq_add_tsum_ite (·⟨C₂,σ⟩)]
  by_cases C₁ = C₂ <;> simp_all [eq_comm, ite_and]
@[simp] theorem ς.nonDet : ς f (.nonDet C₁ C₂) = f C₁ ⊓ f C₂ := by
  ext X σ
  simp [ς, MDP.Φ, MDP.Φf, 𝒬.tsum_succs_univ']
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
theorem ς.loop :
    ς f (.loop b C) = fun X ↦ b.probOf * f (C ;; .loop b C) X + b.not.probOf * f .skip X := by
  funext X σ
  simp [ς, 𝒬.tsum_succs_univ']
  split_ifs <;> simp_all

end 𝒬

open 𝒬

noncomputable def op (C : pGCL ϖ) (X : Exp ϖ) : Exp ϖ := (𝒬.lfp_Φ (cost X) <| ·⟨C, ·⟩)

theorem op_eq_iSup_Φ : op (ϖ:=ϖ) = ⨆ n, fun C X σ ↦ (𝒬.Φ (cost X))^[n] ⊥ (·⟨C,σ⟩) := by
  ext C X σ; rw [op, MDP.lfp_Φ_eq_iSup_Φ]; apply le_antisymm <;> simp
theorem op_eq_iSup_succ_Φ :
    op (ϖ:=ϖ) = ⨆ n, fun C X σ ↦ (𝒬.Φ (cost X))^[n + 1] ⊥ (·⟨C,σ⟩) := by
  ext C X σ; rw [op, MDP.lfp_Φ_eq_iSup_succ_Φ]; apply le_antisymm <;> simp

theorem ς_op_eq_op : ς (ϖ:=ϖ) op = op := by
  funext C X σ
  rw [op, ← MDP.map_lfp_Φ]
  simp only [ς, OrderHom.coe_mk]
  congr! 3 with C'
  rcases C' with ⟨none, σ'⟩ | ⟨C', σ'⟩ | _ <;> simp [op]

@[simp] theorem op_skip : op (ϖ:=ϖ) .skip = (· ·) := by rw [← ς_op_eq_op]; simp

theorem op_isLeast (b : pGCL ϖ → Exp ϖ → Exp ϖ) (h : ς b ≤ b) : op ≤ b := by
  rw [op_eq_iSup_Φ, iSup_le_iff]
  intro n
  induction n with
  | zero => intros _ _ _; simp [cost]
  | succ i ih =>
    refine le_trans (fun _ _ _ ↦ ?_) h
    simp [Function.iterate_succ', ς, -Function.iterate_succ]
    gcongr; split <;> simp_all [ih _ _ _]; split_ifs <;> simp

theorem lfp_ς_eq_op : lfp (ς (ϖ:=ϖ)) = op :=
  (lfp_le_fixed _ ς_op_eq_op).antisymm (le_lfp _ op_isLeast)

variable {C : pGCL ϖ}

attribute [-simp] Function.iterate_succ in
theorem op_le_seq : C.op ∘ C'.op ≤ (C ;; C').op := by
  intro X σ
  nth_rw 1 [op_eq_iSup_succ_Φ]
  simp
  intro n
  induction n generalizing C C' σ with
  | zero => nth_rw 2 [← ς_op_eq_op]; simp_all [ς, MDP.Φf]
  | succ i ih =>
    nth_rw 2 [← ς_op_eq_op]
    rw [Function.iterate_succ', Function.comp_apply]
    simp [ς, 𝒬.tsum_succs_univ']
    refine add_le_add (le_refl _) (iInf₂_mono fun α hα ↦ C'.tsum_after_le (by simp) ?_ ?_)
    all_goals intros; simp_all; split_ifs <;> simp_all [mul_le_mul]

theorem ς_wp_eq_wp : ς (ϖ:=ϖ) wp = wp := by
  funext C; induction C with try simp_all
  | loop => rw [ς.loop, wp_loop_fp]; rfl
  | seq C₁ C₂ ih₁ ih₂ =>
    ext X σ
    rw [← ih₁]
    simp [ς, 𝒬.tsum_succs_univ']
    congr! 4
    apply C₂.tsum_after_eq <;> simp_all <;> split_ifs <;> simp_all
    rintro _ _ _ _ _ h ⟨_⟩ _ _ h' ⟨_⟩ hp _
    exact ⟨⟨_, _, h⟩, _, h', hp⟩

theorem wp_le_op.loop (ih : C.wp ≤ C.op) : wp (.loop b C) ≤ op (.loop b C) := by
  refine fun X ↦ lfp_le (wp_loop_f b C X) (le_trans ?_ <| ς_op_eq_op.le _ _ ·)
  simp_all [ς, 𝒬.tsum_succs_univ', wp_loop_f]
  split_ifs <;> simp_all; apply (ih _).trans (op_le_seq _)

theorem wp_le_op : wp (ϖ:=ϖ) ≤ op := by
  intro C
  induction C with
  | skip => simp
  | assign => rw [← ς_op_eq_op]; simp
  | prob C₁ p C₂ ih₁ ih₂ => rw [← ς_op_eq_op]; intro X; simp_all [ih₁ X, ih₂ X]
  | nonDet C₁ C₂ ih₁ ih₂ => intro X σ; rw [← ς_op_eq_op]; simp_all [ih₁ X σ, ih₂ X σ]
  | loop b C ih => exact wp_le_op.loop ih
  | seq C₁ C₂ ih₁ ih₂ => intro; exact (wp.monotone _ (ih₂ _)).trans (ih₁ _) |>.trans (op_le_seq _)
  | tick => rw [← ς_op_eq_op]; simp

theorem op_eq_wp : op (ϖ:=ϖ) = wp := (op_isLeast _ ς_wp_eq_wp.le).antisymm wp_le_op

end pGCL
