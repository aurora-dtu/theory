import Mathlib.Data.ENNReal.Inv
import Mathlib.Order.FixedPoints
import PGCL.pGCL
import MDP.Optimization

namespace pGCL

open OrderHom OmegaCompletePartialOrder
open scoped Optimization.Notation

variable {ϖ : Type*} [DecidableEq ϖ]

noncomputable def wp (O : Optimization) : pGCL ϖ → Exp ϖ →o Exp ϖ
  | pgcl {skip} => ⟨fun X ↦ X, fun ⦃_ _⦄ a ↦ a⟩
  | pgcl {~x := ~A} => ⟨fun X ↦ X[x ↦ A], fun ⦃_ _⦄ a i ↦ a _⟩
  | pgcl {~C₁; ~C₂} => ⟨fun X ↦ C₁.wp O (C₂.wp O X), fun a b h ↦ (C₁.wp _).mono ((C₂.wp _).mono h)⟩
  | pgcl {{~C₁} [~p] {~C₂}} =>
    ⟨fun X ↦ p.pick (C₁.wp O X) (C₂.wp O X),
     fun a b hab ↦ by apply ProbExp.pick_le <;> apply (wp O _).mono hab⟩
  | pgcl {{~C₁}[]{~C₂}} =>
    ⟨O.opt₂ (C₁.wp O) (C₂.wp O), fun a b hab ↦ by simp only [Optimization.opt₂_apply]; gcongr⟩
  | pgcl {while ~b {~C'}} => ⟨fun X ↦ lfp ⟨
      (i[b] * C'.wp O · + i[b.not] * X),
      fun _ _ _ ↦ by simp; gcongr⟩, fun _ _ _ ↦ by simp; gcongr; intro; simp; gcongr⟩
  | pgcl {tick(~e)} => ⟨(e + ·), fun _ _ h ↦ by simp; gcongr⟩
  | pgcl {observe(~b)} => ⟨(i[b] * ·), fun _ _ h ↦ by simp; gcongr⟩

syntax "wp[" term "]⟦" cpgcl_prog "⟧" : term

macro_rules
| `(wp[$O]⟦ $p ⟧) => `(pGCL.wp $O pgcl {$p})

@[app_unexpander pGCL.wp]
def wpUnexpander : Lean.PrettyPrinter.Unexpander
| `($(_) $o $c) => do
    let c ← match c with | `(pgcl {$c}) => pure c | _ => `(cpgcl_prog| ~ $c)
    `(wp[$o]⟦$c⟧)
| _ => throw ()

noncomputable def Φ (O : Optimization) (φ : BExpr ϖ) [DecidablePred φ] (C' : pGCL ϖ) (f : Exp ϖ) :
    Exp ϖ →o Exp ϖ :=
  ⟨fun X ↦ i[φ] * wp[O]⟦~C'⟧ X + i[φ.not] * f, by intro _ _ _; simp; gcongr⟩

variable {O : Optimization}

theorem wp_loop (φ  : BExpr ϖ) (C' : pGCL ϖ) [DecidablePred φ] :
    wp[O]⟦while ~φ{~C'}⟧ f = lfp (Φ O φ C' f) := rfl

theorem wp_fp (φ : BExpr ϖ) [DecidablePred φ] (C' : pGCL ϖ) :
    (Φ O φ C' f) (wp[O]⟦while ~φ{~C'}⟧ f) = wp[O]⟦while ~φ{~C'}⟧ f := by simp [wp_loop]

variable {x : ϖ} {e : Exp ϖ} {b : BExpr ϖ} {C₁ : pGCL ϖ}

-- @[simp] theorem wp.skip : wp[O]⟦skip⟧ = ⟨(·), fun (_ _ : Exp ϖ) a ↦ a⟩ := rfl
-- @[simp] theorem wp.assign :
--     wp[O]⟦~x := ~A⟧ = ⟨fun X ↦ X[x ↦ A], fun _ _ h _ ↦ h _⟩ := rfl
-- @[simp] theorem wp.seq : wp[O]⟦~C₁ ; ~C₂⟧ = OrderHom.comp (C₁.wp O) (C₂.wp O) := rfl
-- @[simp] theorem wp.prob :
--     wp[O]⟦{~C₁}[~p]{~C₂}⟧ = ⟨fun X ↦ p.pick (C₁.wp O X) (C₂.wp O X), fun _ _ _ ↦ by simp; gcongr⟩
-- := rfl
-- @[simp] theorem wp.nonDet : wp[O]⟦{~C₁}[]{~C₂}⟧ = O.opt₂ (C₁.wp O) (C₂.wp O) := by ext; simp [wp]
-- @[simp] theorem wp.tick : wp[O]⟦tick(~e)⟧ = ⟨fun X ↦ e + X, fun _ _ _ ↦ by simp; gcongr⟩ := rfl
-- open scoped Classical in
-- @[simp] theorem wp.observe :
--     wp[O]⟦observe(~b)⟧ = ⟨fun X ↦ i[b] * X, fun _ _ _ ↦ by simp; gcongr⟩ := rfl

section

variable {X : Exp ϖ}

@[simp] theorem wp.skip_apply : wp[O]⟦skip⟧ X = X := rfl
@[simp] theorem wp.assign_apply :
    wp[O]⟦~x := ~A⟧ X = X[x ↦ A] := rfl
@[simp] theorem wp.seq_apply : wp[O]⟦~C₁ ; ~C₂⟧ X = wp[O]⟦~C₁⟧ (wp[O]⟦~C₂⟧ X) := rfl
@[simp] theorem wp.prob_apply :
    wp[O]⟦{~C₁}[~p]{~C₂}⟧ X = p.pick (C₁.wp O X) (C₂.wp O X)
:= rfl
@[simp] theorem wp.nonDet_apply : wp[O]⟦{~C₁}[]{~C₂}⟧ X = O.opt₂ (C₁.wp O X) (C₂.wp O X) := by
  ext; simp [wp]
@[simp] theorem wp.tick_apply : wp[O]⟦tick(~e)⟧ X = e + X := rfl
open scoped Classical in
@[simp] theorem wp.observe_apply :
    wp[O]⟦observe(~b)⟧ X = i[b] * X := rfl

end

noncomputable abbrev dwp : pGCL ϖ → Exp ϖ →o Exp ϖ := wp 𝒟
noncomputable abbrev awp : pGCL ϖ → Exp ϖ →o Exp ϖ := wp 𝒜

syntax "dwp⟦" cpgcl_prog "⟧" : term
syntax "awp⟦" cpgcl_prog "⟧" : term

macro_rules
| `(dwp⟦ $p ⟧) => `(pGCL.dwp pgcl {$p})
| `(awp⟦ $p ⟧) => `(pGCL.awp pgcl {$p})

@[app_unexpander pGCL.dwp]
def dwpUnexpander : Lean.PrettyPrinter.Unexpander
| `($(_) $c) => do
    let c ← match c with | `(pgcl {$c}) => pure c | _ => `(cpgcl_prog| ~ $c)
    `(dwp⟦$c⟧)
| _ => throw ()

@[app_unexpander pGCL.awp]
def awpUnexpander : Lean.PrettyPrinter.Unexpander
| `($(_) $c) => do
    let c ← match c with | `(pgcl {$c}) => pure c | _ => `(cpgcl_prog| ~ $c)
    `(awp⟦$c⟧)
| _ => throw ()

/-- Strip all `tick`s from a program. -/
def st : pGCL ϖ → pGCL ϖ
  | pgcl {skip} => pgcl {skip}
  | pgcl {~x := ~A} => pgcl {~x := ~A}
  | pgcl {~C₁ ; ~C₂} => pgcl {~C₁.st ; ~C₂.st}
  | pgcl {{~C₁} [~p] {~C₂}} => pgcl {{~C₁.st} [~p] {~C₂.st}}
  | pgcl {{~C₁} [] {~C₂}} => pgcl {{~C₁.st} [] {~C₂.st}}
  | pgcl {while ~b {~C'}} => pgcl {while ~b {~C'.st}}
  | pgcl {tick(~ _)} => pgcl {skip}
  | pgcl {observe(~ b)} => pgcl {observe(~b)}

def Φ.continuous [DecidablePred b] {C' : pGCL ϖ} (ih : ωScottContinuous wp[O]⟦~C'⟧) :
    ωScottContinuous ⇑(Φ O b C' X) := by
  simp [ωScottContinuous_iff_map_ωSup_of_orderHom] at ih ⊢
  intro c
  simp [Φ, ωSup] at ih ⊢
  ext σ
  simp [ih, ENNReal.mul_iSup, ENNReal.iSup_add]

def wp.continuous (C : pGCL ϖ) : ωScottContinuous (C.wp O) := by
  refine ωScottContinuous.of_map_ωSup_of_orderHom ?_
  simp [ωSup]
  induction C with (try simp; done)
  | assign x e => intro c; ext σ; simp
  | seq C₁ C₂ ih₁ ih₂ =>
    intro c
    simp [ih₂]
    have : ∀ i, wp[O]⟦~C₂⟧ (c i) = c.map wp[O]⟦~C₂⟧ i := by simp
    simp only [this, ih₁]
  | prob C₁ p C₂ ih₁ ih₂ =>
    simp [ProbExp.pick]
    intro C
    ext σ
    simp [ENNReal.mul_iSup, ih₁, ih₂]
    rw [ENNReal.iSup_add_iSup]
    intro i j; use i ⊔ j
    gcongr <;> apply (wp _ _).mono <;> gcongr <;> omega
  | nonDet C₁ C₂ ih₁ ih₂ =>
    simp
    simp [ih₁, ih₂]; clear ih₁ ih₂
    intro c
    cases O <;> simp [Optimization.opt₂]
    · ext
      simp
      simp [iSup_sup, sup_iSup]
      apply le_antisymm
      · simp
        intro i j
        constructor
        · apply le_iSup_of_le j; simp
        · apply le_iSup_of_le i; simp
      · simp
        intro i
        constructor <;> apply le_iSup₂_of_le i i <;> simp
    · ext σ
      simp
      rw [iSup_inf_eq]
      simp [inf_iSup_eq]
      apply le_antisymm
      · simp only [iSup_le_iff]
        intro i j
        apply le_iSup_of_le (i ⊔ j)
        gcongr <;> apply (wp _ _).mono <;> gcongr <;> omega
      · simp only [iSup_le_iff]
        intro i
        apply le_iSup₂_of_le i i
        simp
  | loop b C' ih =>
    intro c
    simp [wp_loop]
    ext σ
    replace ih : ωScottContinuous ⇑wp[O]⟦~C'⟧ := by
      simpa [ωScottContinuous_iff_map_ωSup_of_orderHom]
    rw [fixedPoints.lfp_eq_sSup_iterate _ (Φ.continuous ih)]
    conv => right; arg 1; ext; rw [fixedPoints.lfp_eq_sSup_iterate _ (Φ.continuous ih)]
    simp
    rw [iSup_comm]
    congr with i
    suffices (⇑(Φ O b C' fun a ↦ ⨆ i, c i a))^[i] ⊥ = ⨆ i_1, (⇑(Φ O b C' (c i_1)))^[i] ⊥ by
      replace := congrFun this σ; simp at this; convert this; simp
    clear σ
    induction i with
    | zero => simp
    | succ i ih' =>
      simp only [Function.iterate_succ', Function.comp_apply]
      rw [ih']; clear ih'
      simp [Φ]
      ext σ
      simp
      rw [← ENNReal.iSup_add_iSup]
      · simp [← ENNReal.mul_iSup]
        congr
        rw [ωScottContinuous_iff_map_ωSup_of_orderHom] at ih
        simp [ωSup] at ih
        specialize ih ⟨fun i_1 ↦ ((fun X ↦ i[b] * wp[O]⟦~C'⟧ X + i[b.not] * c i_1)^[i] ⊥), _⟩
        · intro a b hab σ; simp
          induction i generalizing σ with
          | zero => simp
          | succ i ih =>
            simp only [Function.iterate_succ', Function.comp_apply]
            simp
            gcongr
            · apply (wp _ _).mono
              apply ih
            · apply c.mono hab
        · replace ih := congrFun ih σ
          simp only [DFunLike.coe] at ih
          simp at ih
          convert ih
      · intro j k
        use j ⊔ k
        gcongr
        · apply (wp _ _).mono fun X ↦ ?_
          simp
          induction i generalizing X with
          | zero => simp
          | succ i ih =>
            simp only [Function.iterate_succ', Function.comp_apply]
            simp
            gcongr
            · apply (wp _ _).mono
              apply ih
            · apply c.mono; omega
        · apply c.mono; omega
  | tick r => intro c; ext σ; simp [ENNReal.add_iSup]
  | observe r => intro c; ext σ; simp [wp, ENNReal.mul_iSup]

omit [DecidableEq ϖ] in
theorem Exp.sub_sub_cancel {a b : Exp ϖ} (h : ∀ σ, a σ ≠ ⊤) (h₂ : b ≤ a) : a - (a - b) = b := by
  ext σ; apply ENNReal.sub_sub_cancel (h σ) (h₂ σ)

theorem wp_le_one (C : pGCL ϖ) (X : Exp ϖ) (hX : X ≤ 1) : wp[O]⟦~C.st⟧ X ≤ 1 := by
  induction C generalizing X with
  | skip => simp [st, hX]
  | assign => simp [st]; intro σ; apply hX
  | seq C₁ C₂ ih₁ ih₂ => apply ih₁ _ (ih₂ _ hX)
  | prob C₁ p C₂ ih₁ ih₂ =>
    simp [st]
    calc
      p.pick (wp[O]⟦~C₁.st⟧ X) (wp[O]⟦~C₂.st⟧ X) ≤ p.pick 1 1 := by
          gcongr <;> apply_assumption <;> exact hX
      _ ≤ 1 := by simp
  | nonDet C₁ C₂ ih₁ ih₂ =>
    simp [st]
    cases O
    · simp [Optimization.opt₂]; exact ⟨ih₁ X hX, ih₂ X hX⟩
    · simp [Optimization.opt₂]; exact inf_le_of_right_le (ih₂ X hX)
  | tick => simp [st, hX]
  | observe b =>
    simp [st]; intro σ; specialize hX σ; simp_all [BExpr.iver]; split_ifs <;> simp [hX]
  | loop b C' ih =>
    simp [st]
    apply lfp_le
    intro σ
    specialize hX σ
    simp_all [BExpr.iver]
    split_ifs
    · simp; apply ih; rfl
    · simp; apply hX

omit [DecidableEq ϖ] in
@[simp]
theorem ProbExp.one_sub_one_sub_apply {X : ProbExp ϖ} : 1 - (1 - X σ) = X σ := by
  apply ENNReal.sub_sub_cancel <;> simp
omit [DecidableEq ϖ] in
@[simp]
theorem ProbExp.one_sub_one_sub {X : ProbExp ϖ} : 1 - (1 - X) = X := by
  ext; simp
omit [DecidableEq ϖ] in
@[simp]
theorem ProbExp.one_sub_le {X : ProbExp ϖ} : 1 - X.val ≤ 1 := by
  intro σ; simp

theorem wp_le_add (C : pGCL ϖ) : wp[𝒟]⟦~C.st⟧ X + wp[𝒟]⟦~C.st⟧ Y ≤ wp[𝒟]⟦~C.st⟧ (X + Y) := by
  induction C generalizing X Y with try simp [wp, st]; (try intro; simp [mul_add]; done); done
  | seq C₁ C₂ ih₁ ih₂ =>
    simp [st]
    grw [ih₁, ih₂]
  | loop b C' ih =>
    simp [st]
    simp [wp_loop]
    simp [fixedPoints.lfp_eq_sSup_iterate _ (Φ.continuous (wp.continuous C'.st))]
    intro σ
    simp
    rw [ENNReal.iSup_add_iSup]
    · gcongr with n
      induction n generalizing σ with
      | zero => simp
      | succ n ihn =>
        simp only [Function.iterate_succ', Function.comp_apply]
        simp [Φ] at ihn ⊢
        if hb : b σ then
          simp [hb]
          apply le_trans ih
          apply (wp _ _).mono
          intro σ'
          simp
          apply ihn
        else
          simp [hb]
    · intro i j
      use i ⊔ j
      gcongr
      · sorry
      · sorry
  | nonDet C₁ C₂ ih₁ ih₂ =>
    simp [st, Optimization.opt₂]
    grw [← ih₁, ← ih₂]
    constructor <;> gcongr <;> simp
  | prob C₁ p C₂ ih₁ ih₂ =>
    simp [st]
    grw [← ih₁, ← ih₂]
    simp [ProbExp.pick]
    ring_nf; rfl

open scoped Classical in
theorem wp_le_add_right {X : Exp ϖ} {Y : ENNReal} (C : pGCL ϖ) : wp[𝒟]⟦~C.st⟧ (X + Y) ≤ wp[𝒟]⟦~C.st⟧ X + Y := by
  induction C generalizing X Y with try simp [wp, st]
  | seq C₁ C₂ ih₁ ih₂ =>
    grw [← ih₁, ih₂]
  | loop b C' ih =>
    sorry
  | nonDet C₁ C₂ ih₁ ih₂ =>
    simp [Optimization.opt₂]
    grw [ih₁, ih₂]
    intro σ
    simp only [Exp.min_apply, Exp.add_apply]
    rw [min_add]
  | prob C₁ p C₂ ih₁ ih₂ =>
    grw [ih₁, ih₂]
    simp [ProbExp.pick]
    ring_nf
    intro σ
    simp
    sorry
  | observe b =>
    simp [mul_add]; gcongr
    simp

omit [DecidableEq ϖ] in
theorem lfp_le_gfp (f : Exp ϖ →o Exp ϖ) : lfp f ≤ gfp f := by
  apply le_gfp
  simp
omit [DecidableEq ϖ] in
theorem lfp_le_gfp' (f g : Exp ϖ →o Exp ϖ) (h : f ≤ g) : lfp f ≤ gfp g := by
  apply le_trans (lfp_le_gfp _)
  gcongr
omit [DecidableEq ϖ] in
theorem lfp_le_gfp'_apply (f g : Exp ϖ →o Exp ϖ) (h : f ≤ g) : lfp f σ ≤ gfp g σ := by
  apply le_trans (lfp_le_gfp _)
  gcongr

omit [DecidableEq ϖ] in
theorem ProbExp.lfp_le_gfp (f : ProbExp ϖ →o ProbExp ϖ) : lfp f ≤ gfp f := by
  apply le_gfp
  simp
omit [DecidableEq ϖ] in
theorem ProbExp.lfp_le_gfp' (f g : ProbExp ϖ →o ProbExp ϖ) (h : f ≤ g) : lfp f ≤ gfp g := by
  apply le_trans (lfp_le_gfp _)
  gcongr
omit [DecidableEq ϖ] in
theorem ProbExp.lfp_le_gfp'_apply (f g : ProbExp ϖ →o ProbExp ϖ) (h : f ≤ g) :
    lfp f σ ≤ gfp g σ := by
  apply le_trans (lfp_le_gfp _)
  gcongr

end pGCL
