
noncomputable def wp' (C : pGCL Γ) : (Γ.Mem → Prop) →o (Γ.Mem → Prop) :=
  match C with
  | tick t => ⟨fun X ↦ X, fun _ _ h σ ↦ h σ⟩
  | skip => ⟨fun X ↦ X, fun _ _ h ↦ by simp [h]⟩
  | observe b => ⟨fun X ↦ (b ·) ⊓ X, fun _ _ h σ ↦ by simp; sorry⟩
  | assign v e => ⟨fun X ↦ X[v ↦ e], sorry⟩
  | seq C₁ C₂ => C₁.wp'.comp C₂.wp'
  | prop C₁ p C₂ => ⟨fun X ↦ ((0 < p ·) ⇨ C₁.wp' X) ⊓ ((p · < 1) ⇨ C₂.wp' X), sorry⟩
  | nondet C₁ C₂ => ⟨fun X ↦ C₁.wp' X ⊓ C₂.wp' X, sorry⟩
  | loop b C => ⟨fun X ↦ gfp (Ξ' (b ·) (wp' C) X), by sorry⟩

set_option quotPrecheck false in
/-- A _valid_ predicate. -/
notation "⊢ " x => ∀ σ, x σ

theorem classic_assume {C : pGCL Γ} {f}
    (P Q : Γ.Mem → Prop) (h : ⊢ P ⇨ C.wp' Q)
    (h' : (⊢ P ⇨ C.wp' Q) → (C.wp f ≤ a)) :
    C.wp f ≤ a := by
  apply h' h

theorem classic_lift {C : pGCL Γ}
    (P Q : Γ.Mem → Prop) (h : C.wp i[Q] ≤ i[P]) :
    ⊢ P ⇨ C.wp' Q := by
  induction C with
  | tick =>
    intro σ hP
    specialize h σ
    simp [hP] at h ⊢
  | skip =>
    intro σ hP
    specialize h
    have h' := h σ
    simp [hP] at h' h ⊢

theorem classic_colift {C : pGCL Γ}
    (P Q : Γ.Mem → Prop) (h : ⊢ C.wp' Q ⇨ P) :
    C.wp i[Q] ≤ i[P] := by
  induction C generalizing P Q with
  | tick => sorry
  | skip =>
    intro σ
    specialize h
    simp [] at h ⊢
    exact h σ
  | loop b C ih =>
    apply park_induction
    simp_all
    simp [Ξ] at ih ⊢
    intro σ
    if hb : b σ then
      simp [hb]
      apply ih
      sorry
    else
      simp [hb]
      specialize h σ
      simp [wp'] at h
      rw [← map_lfp] at h
      simp [Ξ', -map_lfp, hb] at h
      exact h
    apply le_trans _ (ih _)
    intro σ
    specialize h
    have h' := h σ
    simp [] at h' h ⊢

theorem classic_colift'_sem {C : pGCL Γ}
    (P Q : Γ.Mem → Prop) (h : P σ → C.wp' Q σ) :
    i[P] σ ≤ C.wlp i[Q] σ := by
  induction C generalizing σ P Q with
  | tick t => by_cases P σ <;> simp_all
  | assign x e => simp_all
  | observe b => by_cases P σ <;> simp_all
  | skip => by_cases P σ <;> simp_all
  | seq C₁ C₂ ih₁ ih₂ =>
    simp_all only [wp'_seq_apply, wlp_seq_apply]
    apply le_trans (ih₁ P (C₂.wp' Q) h)
    apply C₁.wlp.mono
    exact fun _ ↦ ih₂ _ Q id
  | loop b C ih =>
    by_cases hP : P σ <;> simp_all
    simp [wlp]
    rw [fixedPoints.gfp_eq_sInf_iterate _ sorry]
    simp
    simp [wp'] at h
    rw [fixedPoints.gfp_eq_sInf_iterate _ sorry] at h
    simp at h
    intro n
    specialize h n
    induction n with
    | zero => simp
    | succ n ih' =>
      simp only [Function.iterate_succ', Function.comp_apply] at h ⊢

    sorry
    -- apply park_coinduction
    -- simp_all only [Pi.himp_apply, himp_iff_imp]
    -- simp [Ξ] at ih ⊢
    -- intro σ
    -- if hb : b σ then
    --   simp [hb]
    --   apply ih
    --   sorry
    -- else
    --   simp [hb]
    --   specialize h σ
    --   simp [wp'] at h
    --   rw [← map_lfp] at h
    --   simp [Ξ', -map_lfp, hb] at h
    --   exact h
    -- -- apply le_trans _ (ih _)
    -- -- intro σ
    -- -- specialize h
    -- -- have h' := h σ
    -- -- simp [] at h' h ⊢
  | nondet C₁ C₂ ih₁ ih₂ =>
    simp_all only [wp'_nondet_apply, Pi.inf_apply, inf_Prop_eq, wlp_nondet_apply, le_inf_iff,
      implies_true, and_self]
  | prop C₁ p C₂ ih₁ ih₂ =>
    specialize ih₁ (σ:=σ) P Q
    specialize ih₂ (σ:=σ) P Q
    simp_all only [wp'_prop_apply, Pi.inf_apply, Pi.himp_apply, himp_iff_imp, inf_Prop_eq,
      wlp_prop_apply, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.one_apply]
    if hP : P σ then
      simp_all only [forall_const, Iverson.apply_true]
      if hp₀ : p σ = 0 then
        simp_all
      else if hp₁ :  p σ = 1 then
        simp_all
      else
        have : 0 < p σ := pos_of_ne_zero hp₀
        have : p σ < 1 := sorry
        simp_all only [forall_const, ge_iff_le]
        grw [← ih₁, ← ih₂]
        simp [le_add_tsub]
    else
      simp_all only [IsEmpty.forall_iff, not_false_eq_true, Iverson.apply_false, zero_le, imp_self]

theorem classic_colift'_sem_iff {C : pGCL Γ}
    (Q : Γ.Mem → Prop) : i[C.wp' Q σ] = C.wlp i[Q] σ := by
  induction C generalizing Q σ with
  | tick => simp; sorry
  | skip => simp; rfl
  | observe b =>
    simp [Iverson.iver]
    grind
  | seq C₁ C₂ ih₁ ih₂ =>
    simp_all
    congr!
    ext
    rw [← ih₂]
    rfl
  | prop C₁ p C₂ ih₁ ih₂ =>
    classical
    simp_all [Iverson.iver, ite_and]
    if hp₀ : p σ = 0 then
      simp_all
    else if hp₁ :  p σ = 1 then
      simp_all
    else
      have : 0 < p σ := pos_of_ne_zero hp₀
      have : p σ < 1 := sorry
      simp_all only [forall_const]
      specialize ih₁ (σ:=σ) Q; symm at ih₁
      specialize ih₂ (σ:=σ) Q; symm at ih₂
      split_ifs at ih₁ ih₂ with h₁ h₂
      · simp_all
        sorry
      · simp_all
        symm
        simp_all
        sorry
      · simp_all
        sorry
      · simp_all

      -- grw [← ih₁, ← ih₂]


theorem classic_colift' {C : pGCL Γ}
    (P Q : Γ.Mem → Prop) (h : ⊢ P ⇨ C.wp' Q) :
    i[P] ≤ C.wlp i[Q] := by
  intro σ
  apply classic_colift'_sem
  apply h

theorem classic_park_induction {b} {C : pGCL Γ} {f} {P}
    (I' : Γ.Mem → Prop)
    (I)
    (h₀ : ⊢ I' ⇨ (Ξ' (b ·) (wp' C) P) I')
    (h : (⊢ I' ⇨ (Ξ' (b ·) (wp' C) P) I') → (Ξ (b ·) (wp C) f) I ≤ I) :
    (pGCL.loop b C).wp f ≤ I :=
  lfp_le _ (h h₀)

theorem classic_park_induction' {b} {C : pGCL Γ} {f} {P}
    (I' : Γ.Mem → Prop)
    (I)
    (h₀ : ⊢ I' ⇨ (Ξ' (b ·) (wp' C) P) I')
    (h : (Ξ (b ·) (wp C) f) (I * i[I']) ≤ I) :
    (pGCL.loop b C).wp f ≤ I := by
  grw [park_induction (I * i[I'])]
  · sorry
  · apply le_trans h
    sorry

variable {Q : Γ.Mem → Prop}

@[grind, simp] theorem wp'_tick_apply : wp' (.tick t) Q = Q := rfl
@[grind, simp] theorem wp'_observe_apply : wp' (.observe b) Q = (b · : Γ.Mem → Prop) ⊓ Q := rfl
@[grind, simp] theorem wp'_skip_apply : wp' .skip Q = Q := rfl
@[grind, simp] theorem wp'_assign_apply : wp' (.assign v e) Q = Q[v ↦ e] := rfl
@[grind, simp] theorem wp'_seq_apply {C₁ C₂ : pGCL Γ} :
  wp' (.seq C₁ C₂) Q = wp' C₁ (wp' C₂ Q) := rfl
@[grind, simp] theorem wp'_prop_apply {C₁ C₂ : pGCL Γ} :
    wp' (.prop C₁ p C₂) Q = ((0 < p ·) ⇨ wp' C₁ Q) ⊓ ((p · < 1) ⇨ wp' C₂ Q) := rfl
@[grind, simp] theorem wp'_nondet_apply {C₁ C₂ : pGCL Γ} :
    wp' (.nondet C₁ C₂) Q = wp' C₁ Q ⊓ wp' C₂ Q := rfl
@[grind, simp] theorem wp'_ite_apply {b : Γ.Mem → Bool} {C₁ C₂ : pGCL Γ} :
    wp' (.ite b C₁ C₂) Q = (b · : Γ.Mem → Prop) ⊓ wp' C₁ Q ⊔ (b · : Γ.Mem → Prop)ᶜ ⊓ wp' C₂ Q := by
  ext σ
  simp [ite]
  split_ifs <;> simp_all
