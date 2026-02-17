import HeyVL.Semantics
import Mathlib.Data.Finset.Sort
import PGCL.IdleInduction

attribute [grind =] Finset.empty_union

open Optimization.Notation

open pGCL

open HeyLo

inductive Encoding where | wlp | wp

open Globals in
def spGCL.enc (C : spGCL) (O : Optimization) (E : Encoding) :
    Globals → Globals × HeyVL := fun G ↦
  match C with
  | spgcl {while @b inv(@I) {@C}} =>
    let (G, C) := C.enc O E G
    match E with
    | .wp => (G, heyvl {
      coassert(@I) ; cohavocs(@C.mods) ; covalidate ; coassume(@I) ;
      if (@b) { @C ; coassert(@I) ; coassume(⊤) } })
    | .wlp => (G, heyvl {
      assert(@I) ; havocs(@C.mods) ; validate ; assume(@I) ;
      if (@b) { @C ; assert(@I) ; assume(0) } })
  | spgcl {{@C₁} [@p] {@C₂}} =>
    let (G, C₁) := C₁.enc O E G ; let (G, C₂) := C₂.enc O E G
    let_fresh choice : .Bool ← G
    (G, heyvl { choice :≈ flip(@p); if (choice) {@C₁} else {@C₂} })
  | spgcl {skip} => (G, heyvl {skip})
  | spgcl {@x := @e} => (G, heyvl {@x :≈ @(.pure e)})
  | spgcl {@C₁ ; @C₂} =>
    let (G, C₂) := C₂.enc O E G
    let (G, C₁) := C₁.enc O E G
    (G, heyvl{@C₁ ; @C₂})
  | spgcl {{@C₁} [] {@C₂}} =>
    let (G, C₁) := C₁.enc O E G
    let (G, C₂) := C₂.enc O E G
    match O with
    | 𝒜 => (G, heyvl {if (⊔) {@C₁} else {@C₂}})
    | 𝒟 => (G, heyvl {if (⊓) {@C₁} else {@C₂}})
  | spgcl {if @b then @C₁ else @C₂ end} =>
    let (G, C₁) := C₁.enc O E G
    let (G, C₂) := C₂.enc O E G
    (G, heyvl {if (@b) {@C₁} else {@C₂}})
  | spgcl {tick(@r)} =>
    match E with
    | .wp => (G, heyvl { reward(@r) })
    -- NOTE: we include `r` as a subexpression such that `fv` is the same in both cases
    | .wlp => (G, heyvl { reward(0 * @r) })
  | spgcl {observe(@r)} => (G, heyvl { assert(@r.embed) })

@[grind ., grind! ., simp]
theorem spGCL.enc_G_mono {C : spGCL} : G ⊆ (C.enc O E G).1 := by
  fun_induction enc <;> grind
@[grind =, simp]
theorem spGCL.fv_HeyVL_subset {C : spGCL} :
    (C.enc O E G).2.fv = C.fv ∪ ((C.enc O E G).1 \ G) := by
  induction C generalizing G with
    simp_all [spGCL.enc, fv, embed, HeyLo.not, HeyVL.fv, HeyVL.Skip, HeyVL.If, HeyLo.fv]
  | assign => simp [Distribution.pure, Distribution.fv]
  | seq C₁ C₂ ih₁ ih₂ => grind
  | tick r => cases E <;> simp [HeyVL.fv]
  | nonDet C₁ C₂ ih₁ ih₂ => grind
  | ite b C₁ C₂ ih₁ ih₂ => grind
  | prob C₁ p C₂ ih₁ ih₂ =>
    simp only [Distribution.fv, Distribution.flip, Distribution.bin, List.map_cons, HeyLo.fv,
      Finset.union_empty, Finset.empty_union, List.map_nil, List.toFinset_cons, List.toFinset_nil,
      insert_empty_eq, Finset.mem_singleton, Finset.insert_eq_of_mem, Finset.singleton_biUnion]
    ext a
    simp_all only [Finset.mem_insert, Finset.mem_union, Finset.mem_sdiff]
    have :
        a = { name := ((C₂.enc O E (C₁.enc O E G).1).1.fresh Ty.Bool).2.name, type := Ty.Bool }
        ↔ a = ((C₂.enc O E (C₁.enc O E G).1).1.fresh Ty.Bool).2 := by
      grind [Ident, Globals.fresh]
    constructor
    · rintro (h | h | h | h | h) <;> try grind
    · grind
  | loop b I C ih =>
    have := (C.enc O E G).2.mods_subset_fv
    cases E
    · simp only [HeyVL.fv, HeyVL.Havocs_fv, Finset.sort_toFinset, HeyLo.fv, Finset.union_empty,
      Finset.union_assoc, Finset.empty_union]
      grind
    · simp only [HeyVL.fv, HeyVL.Cohavocs_fv, Finset.sort_toFinset, HeyLo.fv, Finset.union_empty,
      Finset.union_assoc, Finset.empty_union]
      grind

@[grind ., simp]
theorem spGCL.enc_mods (C : spGCL) : C.mods ⊆ (C.enc O E G).2.mods := by
  induction C generalizing G with simp_all [mods, enc, HeyVL.mods, HeyVL.If] <;> try grind
  | loop => cases E <;> simp_all only [HeyVL.mods] <;> grind

def spGCL.vp (C : spGCL) (O : Optimization) (E : Encoding) (φ : 𝔼r) : 𝔼r :=
  (C.enc O E (C.fv ∪ φ.fv)).2.vp φ

theorem spGCL.enc_prob_vp {C₁ C₂ : spGCL} {G : Globals} (hG : (C₁.prob p C₂).fv ∪ φ.fv ⊆ G) :
      (((C₁.prob p C₂).enc O E G).2.vp φ).sem
    =   (p.sem ⊓ 1) * ((C₁.enc O E G).2.vp φ).sem
      + (1 - p.sem ⊓ 1) * ((C₂.enc O E (C₁.enc O E G).1).2.vp φ).sem := by
  simp [enc, HeyVL.vp, HeyVL.If, Distribution.flip]
  have :
      ⟨((C₂.enc O E (C₁.enc O E G).1).1.fresh Ty.Bool).2.name, .Bool⟩
    = ((C₂.enc O E (C₁.enc O E G).1).1.fresh Ty.Bool).2 := by
    ext
    · rfl
    · simp
  repeat rw [Substitution.indep_pair (HeyLo.sem_indep (by grind))]

set_option maxHeartbeats 500000 in
private lemma spGCL.wp_le_vp_aux {C : spGCL} {G : Globals} (hG : C.fv ∪ φ.fv ⊆ G) :
    wp[O]⟦@C.pGCL⟧ φ.sem ≤ ((C.enc O .wp G).2.vp φ).sem := by
  induction C generalizing G φ with
  | skip =>
    intro σ
    simp only [Ty.lit, pGCL, wp.skip_apply, enc, HeyVL.Skip, HeyVL.vp, sem_add_apply, Ty.expr,
      sem_zero, Pi.add_apply, Pi.ofNat_apply, add_zero, le_refl]
  | assign x e => simp [spGCL.enc, HeyVL.vp, spGCL.pGCL]
  | seq C₁ C₂ ih₁ ih₂ =>
    simp only [spGCL.enc, HeyVL.vp, spGCL.pGCL, wp.seq_apply]
    grw [← ih₁, ← ih₂]
    · grind
    · simp
      grind
  | ite b C₁ C₂ ih₁ ih₂ =>
    simp only [pGCL, pGCL.ite, wp.prob_apply, enc, HeyVL.if_vp_sem, Ty.expr, sem_not_apply]
    simp only [fv, Finset.union_assoc] at hG
    grw [← ih₁, ← ih₂]
    · intro σ; simp only [Ty.lit, Pi.add_apply, Pi.mul_apply, BExpr.probOf_apply, Pi.sub_apply,
      Pi.ofNat_apply, hnot_eq_compl, Pi.iver_apply, Pi.compl_apply, compl_iff_not, Iverson.iver_neg,
      ENNReal.natCast_sub, Nat.cast_one, le_refl]
    · grind
    · clear ih₁; grind
  | nonDet C₁ C₂ ih₁ ih₂ =>
    simp [spGCL.fv] at hG
    simp only [pGCL, wp.nonDet_apply, Optimization.opt₂, enc]
    cases O
    · simp only [HeyVL.vp, sem_sup_apply]
      grw [← ih₁, ← ih₂] <;> grind
    · simp only [HeyVL.vp, sem_inf_apply]
      grw [← ih₁, ← ih₂] <;> grind
  | prob C₁ p C₂ ih₁ ih₂ =>
    simp only [Ty.lit, spGCL.enc_prob_vp hG, Ty.expr]
    grw [← ih₁, ← ih₂]
    · intro σ; rfl
    · grind
    · grind
  | loop b I C ih =>
    simp only [Ty.lit, pGCL, enc, HeyVL.vp, sem_sup_apply, Ty.expr, Finset.sort_nodup,
      HeyVL.vp_cohavocs, sem_covalidate, Exp.covalidate_subst]
    intro σ
    if inv : IdleInvariant wp[O]⟦@C.pGCL⟧ b.sem φ.sem I.sem C.modsᶜ σ then
      simp
      left
      apply IdleInduction
      grind
    else
      simp [IdleInvariant] at inv
      obtain ⟨σ', h₁, h₂⟩ := inv
      simp [Ψ] at h₂
      let Ξ := HeyVL.Subs.of (C.enc O .wp G).2.mods.sort (by simp) σ'
      have σ_eq_σ' : σ[..Ξ.help'] = σ' := by
        ext x
        simp +contextual [Ξ]
        intro h

        specialize h₁ x (by contrapose! h; exact C.enc_mods (by grind))
        simp_all only
      simp_all only [Ty.lit, Pi.sup_apply, iSup_apply, Exp.covalidate_apply, Exp.substs_help_apply,
        le_sup_iff]
      right
      apply le_iSup_of_le Ξ
      simp [σ_eq_σ']
      apply ENNReal.le_covalidate_sdiff_of_lt
      simp [HeyVL.vp, HeyVL.Skip]
      replace ih :
            wp[O]⟦@C.pGCL⟧ I.sem σ'
          ≤ ((C.enc O .wp G).2.vp (I ⊔ (⊤ ↜ φ))).sem σ' := by
        specialize ih (φ:=I ⊔ (⊤ ↜ φ)) (G:=G) (by simp [HeyLo.fv]; grind) σ'
        grw [← ih]; gcongr; intro; simp
      grw [← ih]
      exact h₂
  | tick r =>
    grind [spGCL.enc, HeyVL.vp, add_comm, spGCL.pGCL, wp.tick_apply, le_refl]
  | observe r =>
    intro σ
    simp only [Ty.lit, pGCL, wp.observe_apply, Pi.mul_apply, Pi.iver_apply, enc, HeyVL.vp,
      sem_inf_apply, Ty.expr, sem_embed, Pi.inf_apply, Pi.top_apply, le_inf_iff,
      BExpr.iver_mul_le_apply, and_true]
    if r.sem σ then simp_all [Iverson.iver] else simp_all

theorem spGCL.wp_le_vp {C : spGCL} :
    wp[O]⟦@C.pGCL⟧ φ.sem ≤ (C.vp O .wp φ).sem := wp_le_vp_aux (by rfl)

/-- info: 'spGCL.wp_le_vp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spGCL.wp_le_vp

@[grind ., simp]
theorem pGCL.wlp_le_one [DecidableEq 𝒱] {Γ : Γ[𝒱]} {C : pGCL Γ} {φ} : wlp[O]⟦@C⟧ φ ≤ 1 := by
  intro; simp [wlp]

private lemma spGCL.vp_le_wlp_aux.loop
    (ih : ∀ {φ : 𝔼r} {G : Globals}, C.fv ∪ φ.fv ⊆ G →
      φ.sem ≤ 1 → ((C.enc O Encoding.wlp G).2.vp φ).sem ≤ wlp[O]⟦@C.pGCL⟧ φ.sem)
    (hG : (loop b I C).fv ∪ φ.fv ⊆ G) (hφ : φ.sem ≤ 1) (hI : I.sem ≤ 1 ∧ ∀ a ∈ C.invs, a.sem ≤ 1) :
    (((loop b I C).enc O Encoding.wlp G).2.vp φ).sem ≤ wlp[O]⟦@(loop b I C).pGCL⟧ φ.sem := by
  simp only [Ty.expr, enc, HeyVL.vp, sem_inf_apply, Finset.sort_nodup, HeyVL.vp_havocs,
    sem_validate, sem_himp_apply, HeyVL.if_vp_sem, sem_not_apply, Exp.validate_subst,
    Exp.himp_subst, Exp.add_subst, Exp.mul_subst, Exp.iver_subst, pGCL]
  intro σ
  if inv : IdleCoinvariant wlp[O]⟦@C.pGCL⟧ b.sem φ.sem I.sem C.modsᶜ σ then
    simp
    left
    apply IdleCoinduction <;> grind
  else
    simp [IdleCoinvariant] at inv
    obtain ⟨σ', h₁, h₂⟩ := inv
    simp [Ψ] at h₂
    simp_all only [Pi.inf_apply, inf_le_iff]
    right
    simp_all only [Ty.expr, Ty.lit, hnot_eq_compl, Exp.not_subst, iInf_apply, Exp.validate_apply,
      Pi.himp_apply, Exp.substs_help_apply, Pi.add_apply, Pi.mul_apply, Pi.iver_apply,
      Pi.compl_apply, compl_iff_not]
    let Ξ := HeyVL.Subs.of (C.enc O .wlp G).2.mods.sort (by simp) σ'
    have σ_eq_σ' : σ[..Ξ.help'] = σ' := by
      ext x
      simp +contextual [Ξ]
      intro h
      specialize h₁ x (by contrapose! h; exact C.enc_mods (by grind))
      simp_all
    apply iInf_le_of_le Ξ
    apply ENNReal.validate_himp_le_of_lt
    simp [HeyVL.vp, HeyVL.Skip, σ_eq_σ']
    replace ih :
          ((C.enc O .wlp G).2.vp (I ⊓ (0 ⇨ φ))).sem σ'
        ≤ wlp[O]⟦@C.pGCL⟧ I.sem σ' := by
      specialize ih (φ:=I ⊓ (0 ⇨ φ)) (G:=G) (by simp [HeyLo.fv]; grind) (by simp; grind) σ'
      grw [ih]; simp
    grw [ih]
    exact h₂

set_option maxHeartbeats 700000 in
private lemma spGCL.vp_le_wlp_aux {C : spGCL} {G : Globals} (hG : C.fv ∪ φ.fv ⊆ G)
    (hφ : φ.sem ≤ 1) (hI : ∀ I ∈ C.invs, I.sem ≤ 1) :
    ((C.enc O .wlp G).2.vp φ).sem ≤ wlp O C.pGCL φ.sem := by
  induction C generalizing G φ with
  | skip =>
    intro σ
    have hφ' : ∀ σ, φ.sem σ ≤ 1 := (hφ ·)
    simp only [Ty.lit, enc, HeyVL.Skip, HeyVL.vp, sem_add_apply, Ty.expr, sem_zero, Pi.add_apply,
      Pi.ofNat_apply, add_zero, pGCL, wlp.skip_apply, Pi.inf_apply, hφ', inf_of_le_left, le_refl]
  | assign x e =>
    intro σ
    have hφ' : ∀ σ, φ.sem σ ≤ 1 := (hφ ·)
    simp only [Ty.lit, enc, HeyVL.vp, Distribution.pure_map, Distribution.pure_toExpr,
      sem_add_apply, Ty.expr, sem_mul_apply, sem_one, sem_subst, one_mul, sem_zero, Pi.add_apply,
      Pi.substs_cons, Substitution.substs_nil, Pi.zero_apply, add_zero, pGCL, wlp.assign_apply,
      Pi.inf_apply, Pi.one_apply, hφ', inf_of_le_left, le_refl]
  | seq C₁ C₂ ih₁ ih₂ =>
    simp only [Ty.expr, enc, HeyVL.vp, pGCL, wlp.seq_apply]
    simp_all
    specialize ih₂ (G:=G) (by grind) hφ
    grw [ih₁, ih₂]
    · grind
    · apply le_trans ih₂; simp
  | ite b C₁ C₂ ih₁ ih₂ =>
    simp only [Ty.expr, enc, HeyVL.if_vp_sem, sem_not_apply, pGCL, pGCL.ite, wlp.prob_apply]
    simp only [fv, Finset.union_assoc] at hG
    grw [ih₁ _ hφ, ih₂ _ hφ]
    · intro; simp only [Ty.lit, hnot_eq_compl, Pi.add_apply, Pi.mul_apply, Pi.iver_apply,
      Pi.compl_apply, compl_iff_not, Iverson.iver_neg, ENNReal.natCast_sub, Nat.cast_one,
      BExpr.probOf_apply, Pi.sub_apply, Pi.ofNat_apply, le_refl]
    all_goals grind
  | nonDet C₁ C₂ ih₁ ih₂ =>
    simp only [Ty.expr, enc, pGCL, wlp.nonDet_apply, Optimization.opt₂]
    simp [spGCL.fv] at hG
    have : C₁.fv ∪ φ.fv ⊆ G := by grind
    cases O
    · simp only [HeyVL.vp, sem_sup_apply, Ty.expr]
      grw [ih₁ _ hφ, ih₂ _ hφ] <;> grind
    · simp only [HeyVL.vp, sem_inf_apply, Ty.expr]
      grw [ih₁ _ hφ, ih₂ _ hφ] <;> grind
  | prob C₁ p C₂ ih₁ ih₂ =>
    simp only [Ty.lit, spGCL.enc_prob_vp hG, Ty.expr]
    grw [ih₁ _ hφ, ih₂ _ hφ]
    · intro σ
      simp only [Ty.lit, wlp, ProbExp.ofExp, OrderHom.coe_mk, Pi.add_apply, Pi.mul_apply,
        Pi.inf_apply, Pi.one_apply, Pi.sub_apply, pGCL, wlp'.prob_apply, OrderHom.mk_apply,
        ProbExp.add_apply, ProbExp.mul_apply, ProbExp.coe_apply, ProbExp.sub_apply,
        ProbExp.one_apply, le_inf_iff, le_refl, true_and]
      have := ProbExp.pick_le (p:=ProbExp.ofExp p.sem) (x:=1)
                (l:=wlp'[O]⟦@C₁.pGCL⟧ ⟨φ.sem ⊓ 1, by simp⟩ σ)
                (r:=wlp'[O]⟦@C₂.pGCL⟧ ⟨φ.sem ⊓ 1, by simp⟩ σ)
      simp only [Ty.lit, ProbExp.le_one_apply, ProbExp.ofExp_apply, forall_const] at this
      grind
    · grind
    · grind
    · grind
    · grind
  | loop b I C ih =>
    simp_all only [Ty.expr, Ty.lit, invs, Finset.mem_insert, or_true, implies_true, forall_const,
      forall_eq_or_imp]
    exact vp_le_wlp_aux.loop ih hG hφ hI
  | tick r =>
    simp only [Ty.expr, Ty.lit, enc, HeyVL.vp, sem_add_apply, pGCL, wlp.tick_apply]
    intro σ
    simp [Pi.add_apply, Ty.lit, add_zero, le_refl]
    apply hφ
  | observe r =>
    intro σ
    simp only [Ty.lit, enc, HeyVL.vp, sem_inf_apply, Ty.expr, sem_embed, Pi.inf_apply,
      Pi.mul_apply, Pi.iver_apply, Pi.top_apply, pGCL, wlp.observe_apply, inf_le_iff]
    if r.sem σ then
      simp_all only [Ty.expr, Ty.lit, invs, Finset.notMem_empty, IsEmpty.forall_iff, implies_true,
        Iverson.iver_True, Nat.cast_one, one_mul, BExpr.probOf_apply, Pi.one_apply, le_inf_iff,
        top_le_iff, ENNReal.one_ne_top, and_false, le_refl, true_and, false_or]
      apply hφ
    else
      simp_all only [Ty.expr, Ty.lit, invs, Finset.notMem_empty, IsEmpty.forall_iff, implies_true,
        Iverson.iver_False, Nat.cast_zero, zero_mul, BExpr.probOf_apply, Pi.ofNat_apply, le_refl,
        nonpos_iff_eq_zero, true_or]

theorem spGCL.vp_le_wlp {C : spGCL} (hφ : φ.sem ≤ 1) (hI : ∀ I ∈ C.invs, I.sem ≤ 1) :
    (C.vp O .wlp φ).sem ≤ wlp[O]⟦@C.pGCL⟧ φ.sem := vp_le_wlp_aux (by rfl) hφ hI

/-- info: 'spGCL.vp_le_wlp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spGCL.vp_le_wlp
