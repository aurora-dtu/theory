import Mathlib.Data.ENNReal.Inv
import Mathlib.Order.FixedPoints
import PGCL.WeakestPre
import MDP.Optimization

namespace pGCL

open OrderHom OmegaCompletePartialOrder
open scoped Optimization.Notation

variable {ϖ : Type*} [DecidableEq ϖ]

noncomputable def wfp (O : Optimization) : pGCL ϖ → ProbExp ϖ →o ProbExp ϖ
  | pgcl {skip} => ⟨fun X ↦ X, fun ⦃_ _⦄ a ↦ a⟩
  | pgcl {~x := ~A} => ⟨fun X ↦ X[x ↦ A], fun ⦃_ _⦄ a i ↦ a _⟩
  | pgcl {~C₁; ~C₂} => (C₁.wfp O).comp (C₂.wfp O)
  | pgcl {{~C₁} [~p] {~C₂}} =>
    ⟨fun X ↦ p.pickProb (C₁.wfp O X) (C₂.wfp O X),
     fun a b hab ↦ by apply ProbExp.pickProb_le <;> apply (wfp O _).mono hab⟩
  | pgcl {{~C₁}[]{~C₂}} =>
    ⟨O.opt₂ (C₁.wfp O) (C₂.wfp O), fun a b hab ↦ by simp only [Optimization.opt₂_apply]; gcongr⟩
  | pgcl {while ~b {~C'}} => ⟨fun X ↦ lfp ⟨
      (fun Y ↦ b.probOf.pickProb (C'.wfp O Y) X),
      fun _ _ _ ↦ by simp; gcongr⟩, fun _ _ _ ↦ by simp; gcongr; intro; simp; gcongr⟩
  | pgcl {tick(~e)} => ⟨(·), fun _ _ h ↦ by simp; gcongr⟩
  | pgcl {observe(~b)} => ⟨(b.probOf.pickProb · 1), fun _ _ h ↦ by simp; gcongr⟩

syntax "wfp[" term "]⟦" cpgcl_prog "⟧" : term

macro_rules
| `(wfp[$O]⟦ $p ⟧) => `(pGCL.wfp $O pgcl {$p})

@[app_unexpander pGCL.wfp]
def wfpUnexpander : Lean.PrettyPrinter.Unexpander
| `($(_) $o $c) => do
    let c ← match c with | `(pgcl {$c}) => pure c | _ => `(cpgcl_prog| ~ $c)
    `(wfp[$o]⟦$c⟧)
| _ => throw ()

noncomputable def wfp' (O : Optimization) : pGCL ϖ → Exp ϖ →o Exp ϖ
  | pgcl {skip} => ⟨fun X ↦ X, fun ⦃_ _⦄ a ↦ a⟩
  | pgcl {~x := ~A} => ⟨fun X ↦ X[x ↦ A], fun ⦃_ _⦄ a i ↦ by exact a _⟩
  | pgcl {~C₁; ~C₂} => (C₁.wfp' O).comp (C₂.wfp' O)
  | pgcl {{~C₁} [~p] {~C₂}} =>
    ⟨fun X ↦ p.pick (C₁.wfp' O X) (C₂.wfp' O X),
     fun a b hab ↦ by apply ProbExp.pick_le <;> apply (wfp' O _).mono hab⟩
  | pgcl {{~C₁}[]{~C₂}} =>
    ⟨O.opt₂ (C₁.wfp' O) (C₂.wfp' O), fun a b hab ↦ by simp only [Optimization.opt₂_apply]; gcongr⟩
  | pgcl {while ~b {~C'}} => ⟨fun X ↦ lfp ⟨
      (fun Y ↦ b.probOf.pick (C'.wfp' O Y) X),
      fun _ _ _ ↦ by simp; gcongr⟩, fun _ _ _ ↦ by simp; gcongr; intro; simp; gcongr⟩
  | pgcl {tick(~e)} => ⟨(·), fun _ _ h ↦ by simp; gcongr⟩
  | pgcl {observe(~b)} => ⟨(b.probOf.pick · 1), fun _ _ h ↦ by simp; gcongr⟩

syntax "wfp'[" term "]⟦" cpgcl_prog "⟧" : term

macro_rules
| `(wfp'[$O]⟦ $p ⟧) => `(pGCL.wfp' $O pgcl {$p})

@[app_unexpander pGCL.wfp']
def wfp'Unexpander : Lean.PrettyPrinter.Unexpander
| `($(_) $o $c) => do
    let c ← match c with | `(pgcl {$c}) => pure c | _ => `(cpgcl_prog| ~ $c)
    `(wfp'[$o]⟦$c⟧)
| _ => throw ()

theorem wfp_eq_wfp' {C : pGCL ϖ} : wfp[O]⟦~C⟧ X = wfp'[O]⟦~C⟧ X := by
  induction C generalizing X with try simp [wfp, wfp', *]; (try rfl); done
  | nonDet C₁ C₂ ih₁ ih₂ =>
    simp [wfp, wfp', ← ih₁, ← ih₂]; ext; simp [Optimization.opt₂]
    cases O <;> simp
  | loop b C' ih =>
    simp [wfp, wfp']
    apply le_antisymm
    · suffices
            lfp ⟨fun Y ↦ b.probOf.pickProb (wfp[O]⟦~C'⟧ Y) X, _⟩
          ≤ ⟨lfp ⟨fun Y ↦ b.probOf.pick (wfp'[O]⟦~C'⟧ Y) ⇑X, _⟩, by
              apply lfp_le
              intro σ
              simp only [DFunLike.coe]
              simp [ProbExp.pick, BExpr.probOf]
              by_cases hb : b σ
              · simp [hb]
                specialize ih (X:=1)
                replace ih := congrFun ih σ
                have : (wfp[O]⟦~C'⟧ 1) σ ≤ 1 := by simp
                simp at ih
                rw [ih] at this
                exact this
              · simp [hb]; apply ProbExp.le_one
              ⟩ by
        exact this
      apply lfp_le
      simp
      intro σ
      simp
      nth_rw 2 [← map_lfp]
      simp [-map_lfp, ih]
    · apply lfp_le
      simp [← ih]
      nth_rw 2 [← map_lfp]
      simp [-map_lfp]

noncomputable def fΦ (O : Optimization) (φ : BExpr ϖ) [DecidablePred φ] (C' : pGCL ϖ) (f : Exp ϖ) :
    Exp ϖ →o Exp ϖ :=
  ⟨fun X ↦ φ.probOf.pick (wfp'[O]⟦~C'⟧ X) f, by intro _ _ _; simp; gcongr⟩

noncomputable def fΦ' (O : Optimization) (φ : BExpr ϖ) [DecidablePred φ] (C' : pGCL ϖ) (f : ProbExp ϖ) :
    ProbExp ϖ →o ProbExp ϖ :=
  ⟨fun X ↦ φ.probOf.pickProb (wfp[O]⟦~C'⟧ X) f, by intro _ _ _; simp; gcongr⟩

theorem wfp'_loop (φ  : BExpr ϖ) (C' : pGCL ϖ) [DecidablePred φ] :
    wfp'[O]⟦while ~φ{~C'}⟧ f = lfp (fΦ O φ C' f) := rfl

theorem wfp'_fp (φ : BExpr ϖ) [DecidablePred φ] (C' : pGCL ϖ) :
    (fΦ O φ C' f) (wfp'[O]⟦while ~φ{~C'}⟧ f) = wfp'[O]⟦while ~φ{~C'}⟧ f := by simp [wfp'_loop]

theorem wfp_loop (φ  : BExpr ϖ) (C' : pGCL ϖ) [DecidablePred φ] :
    wfp[O]⟦while ~φ{~C'}⟧ f = lfp (fΦ O φ C' f) := by simp [wfp_eq_wfp', wfp'_loop]

noncomputable def wlp (O : Optimization) : pGCL ϖ → ProbExp ϖ →o ProbExp ϖ
  | pgcl {skip} => ⟨fun X ↦ X, fun ⦃_ _⦄ a ↦ a⟩
  | pgcl {~x := ~A} => ⟨fun X ↦ X[x ↦ A], fun ⦃_ _⦄ a i ↦ a _⟩
  | pgcl {~C₁; ~C₂} => (C₁.wlp O).comp (C₂.wlp O)
  | pgcl {{~C₁} [~p] {~C₂}} =>
    ⟨fun X ↦ p.pickProb (C₁.wlp O X) (C₂.wlp O X),
     fun a b hab ↦ by apply ProbExp.pickProb_le <;> apply (wlp O _).mono hab⟩
  | pgcl {{~C₁}[]{~C₂}} =>
    ⟨O.opt₂ (C₁.wlp O) (C₂.wlp O), fun a b hab ↦ by simp only [Optimization.opt₂_apply]; gcongr⟩
  | pgcl {while ~b {~C'}} => ⟨fun X ↦ gfp ⟨
      (fun Y ↦ b.probOf.pickProb (C'.wlp O Y) X),
      fun _ _ _ ↦ by simp; gcongr⟩, fun _ _ _ ↦ by simp; gcongr; intro; simp; gcongr⟩
  | pgcl {tick(~e)} => ⟨(·), fun _ _ h ↦ by simp; gcongr⟩
  | pgcl {observe(~b)} => ⟨fun X ↦ b.probOf * X, fun _ _ h ↦ by simp; gcongr⟩

syntax "wlp[" term "]⟦" cpgcl_prog "⟧" : term

macro_rules
| `(wlp[$O]⟦ $p ⟧) => `(pGCL.wlp $O pgcl {$p})

@[app_unexpander pGCL.wlp]
def wlpUnexpander : Lean.PrettyPrinter.Unexpander
| `($(_) $o $c) => do
    let c ← match c with | `(pgcl {$c}) => pure c | _ => `(cpgcl_prog| ~ $c)
    `(wlp[$o]⟦$c⟧)
| _ => throw ()

noncomputable def lΦ (O : Optimization) (b : BExpr ϖ) (C' : pGCL ϖ)
    (f : ProbExp ϖ) : ProbExp ϖ →o ProbExp ϖ :=
  ⟨fun Y ↦ b.probOf.pickProb (C'.wlp O Y) f, fun _ _ _ ↦ by simp; gcongr⟩

section

variable {X : ProbExp ϖ}

theorem wlp_loop (φ  : BExpr ϖ) (C' : pGCL ϖ) :
    wlp[O]⟦while ~φ {~C'}⟧ f = gfp (lΦ O φ C' f) := rfl

@[simp] theorem wlp.skip_apply : wlp[O]⟦skip⟧ X = X := rfl
@[simp] theorem wlp.assign_apply :
    wlp[O]⟦~x := ~A⟧ X = X[x ↦ A] := rfl
@[simp] theorem wlp.seq_apply : wlp[O]⟦~C₁ ; ~C₂⟧ X = wlp[O]⟦~C₁⟧ (wlp[O]⟦~C₂⟧ X) := rfl
@[simp] theorem wlp.prob_apply :
    wlp[O]⟦{~C₁}[~p]{~C₂}⟧ X = p.pickProb (C₁.wlp O X) (C₂.wlp O X)
:= rfl
@[simp] theorem wlp.nonDet_apply : wlp[O]⟦{~C₁}[]{~C₂}⟧ X = O.opt₂ (C₁.wlp O X) (C₂.wlp O X) := by
  ext; simp [wlp]
@[simp] theorem wlp.tick_apply : wlp[O]⟦tick(~e)⟧ X = X := rfl
open scoped Classical in
@[simp] theorem wlp.observe_apply :
    wlp[O]⟦observe(~b)⟧ X = p[b] * X := rfl

end

noncomputable def wlp' (O : Optimization) : pGCL ϖ → ProbExp ϖ →o ProbExp ϖ
  | pgcl {skip} => ⟨fun X ↦ X, fun ⦃_ _⦄ a ↦ a⟩
  | pgcl {~x := ~A} => ⟨fun X ↦ ⟨fun σ ↦ X (σ[x ↦ A σ]), by intro; simp⟩, fun ⦃_ _⦄ a i ↦ a _⟩
  | pgcl {~C₁; ~C₂} => (C₁.wlp' O).comp (C₂.wlp' O)
  | pgcl {{~C₁} [~p] {~C₂}} =>
    ⟨fun X ↦ p.pickProb (C₁.wlp' O X) (C₂.wlp' O X),
     fun a b hab ↦ by apply ProbExp.pickProb_le <;> apply (wlp' O _).mono hab⟩
  | pgcl {{~C₁}[]{~C₂}} =>
    ⟨O.opt₂ (C₁.wlp' O) (C₂.wlp' O), fun a b hab ↦ by simp only [Optimization.opt₂_apply]; gcongr⟩
  | pgcl {while ~b {~C'}} => ⟨fun X ↦ gfp ⟨
      (fun Y ↦ b.probOf.pickProb (C'.wlp' O Y) X),
      fun _ _ _ ↦ by simp; gcongr⟩, fun _ _ _ ↦ by simp; gcongr; intro; simp; gcongr⟩
  | pgcl {tick(~e)} => ⟨(·), fun _ _ h ↦ by simp; gcongr⟩
  | pgcl {observe(~b)} => ⟨(b.probOf.pickProb · 1), fun _ _ h ↦ by simp; gcongr⟩

noncomputable def lΦ' (O : Optimization) (b : BExpr ϖ) (C' : pGCL ϖ)
    (f : ProbExp ϖ) : ProbExp ϖ →o ProbExp ϖ :=
  ⟨fun Y ↦ b.probOf.pickProb (C'.wlp' O Y) f, fun _ _ _ ↦ by simp; gcongr⟩

theorem wlp'_loop (φ  : BExpr ϖ) (C' : pGCL ϖ) :
    wlp' O pgcl {while ~φ {~C'}} f = gfp (lΦ' O φ C' f) := rfl

noncomputable def wlp'' (O : Optimization) : pGCL ϖ → Exp ϖ →o Exp ϖ
  | pgcl {skip} => ⟨fun X ↦ X, fun ⦃_ _⦄ a ↦ a⟩
  | pgcl {~x := ~A} => ⟨fun X ↦ X[x ↦ A], fun ⦃_ _⦄ a i ↦ by exact a _⟩
  | pgcl {~C₁; ~C₂} => (C₁.wlp'' O).comp (C₂.wlp'' O)
  | pgcl {{~C₁} [~p] {~C₂}} =>
    ⟨fun X ↦ p.pick (C₁.wlp'' O X) (C₂.wlp'' O X),
     fun a b hab ↦ by apply ProbExp.pick_le <;> apply (wlp'' O _).mono hab⟩
  | pgcl {{~C₁}[]{~C₂}} =>
    ⟨O.opt₂ (C₁.wlp'' O) (C₂.wlp'' O), fun a b hab ↦ by simp only [Optimization.opt₂_apply]; gcongr⟩
  | pgcl {while ~b {~C'}} => ⟨fun X ↦ gfp ⟨
      (fun Y ↦ b.probOf.pick (C'.wlp'' O Y) X),
      fun _ _ _ ↦ by simp; gcongr⟩, fun _ _ _ ↦ by simp; gcongr; intro; simp; gcongr⟩
  | pgcl {tick(~e)} => ⟨(·), fun _ _ h ↦ by simp; gcongr⟩
  | pgcl {observe(~b)} => ⟨(b.probOf.pick · 1), fun _ _ h ↦ by simp; gcongr⟩

syntax "wlp''[" term "]⟦" cpgcl_prog "⟧" : term

macro_rules
| `(wlp''[$O]⟦ $p ⟧) => `(pGCL.wlp'' $O pgcl {$p})

@[app_unexpander pGCL.wlp'']
def wlp''Unexpander : Lean.PrettyPrinter.Unexpander
| `($(_) $o $c) => do
    let c ← match c with | `(pgcl {$c}) => pure c | _ => `(cpgcl_prog| ~ $c)
    `(wlp''[$o]⟦$c⟧)
| _ => throw ()

noncomputable def lΦ'' (O : Optimization) (b : BExpr ϖ) (C' : pGCL ϖ)
    (f : Exp ϖ) : Exp ϖ →o Exp ϖ :=
  ⟨fun Y ↦ b.probOf.pick (C'.wlp'' O Y) f, fun _ _ _ ↦ by simp; gcongr⟩

theorem wlp''_loop (φ  : BExpr ϖ) (C' : pGCL ϖ) :
    wlp'' O pgcl {while ~φ {~C'}} f = gfp (lΦ'' O φ C' f) := rfl

theorem wlp'_eq_wlp'' (O : Optimization) (C : pGCL ϖ) : C.wlp' O X = C.wlp'' O X := by
  induction C generalizing X with try simp [wlp', wlp'', *]; (try rfl); done
  | nonDet C₁ C₂ ih₁ ih₂ =>
    simp [wlp', wlp'']
    rw [← ih₁, ← ih₂]
    cases O <;> simp [Optimization.opt₂] <;> rfl
  | loop b C' ih =>
    rw [wlp'_loop, wlp''_loop]
    apply le_antisymm
    · apply le_gfp
      simp [lΦ'']
      nth_rw 1 [← map_gfp]
      nth_rw 1 [lΦ']
      simp
      grind
    · suffices
              ⟨gfp (lΦ'' O b C' X), by
                apply gfp_le
                intro a ha
                simp [lΦ''] at ha
                apply le_trans ha
                have : ProbExp.pick p[b] 1 1 ≤ 1 := sorry
                apply le_trans _ this
                gcongr
                · sorry
                · apply X.prop⟩
            ≤ gfp (lΦ' O b C' X) by
        exact this
      apply le_gfp
      intro σ
      simp
      nth_rw 1 [← map_gfp]
      nth_rw 1 [lΦ'']
      nth_rw 1 [lΦ']
      simp [-map_gfp, ih]

section

variable {X : Exp ϖ}

@[simp] theorem wlp''.skip_apply : wlp''[O]⟦skip⟧ X = X := rfl
@[simp] theorem wlp''.assign_apply :
    wlp''[O]⟦~x := ~A⟧ X = X[x ↦ A] := rfl
@[simp] theorem wlp''.seq_apply : wlp''[O]⟦~C₁ ; ~C₂⟧ X = wlp''[O]⟦~C₁⟧ (wlp''[O]⟦~C₂⟧ X) := rfl
@[simp] theorem wlp''.prob_apply :
    wlp''[O]⟦{~C₁}[~p]{~C₂}⟧ X = p.pick (C₁.wlp'' O X) (C₂.wlp'' O X) := rfl
@[simp] theorem wlp''.nonDet_apply :
    wlp''[O]⟦{~C₁}[]{~C₂}⟧ X = O.opt₂ (C₁.wlp'' O X) (C₂.wlp'' O X) := by
  ext; simp [wlp'']
@[simp] theorem wlp''.tick_apply : wlp''[O]⟦tick(~e)⟧ X = X := rfl
open scoped Classical in
@[simp] theorem wlp''.observe_apply :
    wlp''[O]⟦observe(~b)⟧ X = p[b].pick X 1 := rfl

end

def wfp.continuous (C : pGCL ϖ) : ωScottContinuous (C.wfp O) := by
  refine ωScottContinuous.of_map_ωSup_of_orderHom ?_
  simp [ωSup]
  sorry

attribute [- simp] Function.iterate_succ in
theorem wlp'_sound (C : pGCL ϖ) (X : ProbExp ϖ) :
    wlp[𝒟]⟦~C.st⟧ X = 1 - wfp[𝒜]⟦~C.st⟧ (1 - X) := by
  induction C generalizing X with
  | skip =>
    ext σ
    simp [wlp, wfp, st]
  | assign => ext σ; simp [st, wlp, wfp]
  | seq C₁ C₂ ih₁ ih₂ =>
    ext σ
    simp [wlp, wfp, st]
    rw [ih₂ _, ih₁ _ ]
    simp
  | prob C₁ p C₂ ih₁ ih₂ =>
    ext σ
    simp [wlp, wfp, st]
    simp [ih₁, ih₂]
    simp [ProbExp.pickProb, ProbExp.pick]
    simp [ENNReal.mul_sub]
    set f := wfp[𝒜]⟦~C₁.st⟧ (1 - X) σ
    set g := wfp[𝒜]⟦~C₂.st⟧ (1 - X) σ
    refine (ENNReal.toReal_eq_toReal_iff' ?_ ?_).mp ?_
    · simp
    · simp
    · have hf : f ≤ 1 := by simp [f]
      have hg : g ≤ 1 := by simp [g]
      have hf' : f ≠ ⊤ := (hf.trans_lt ENNReal.one_lt_top).ne
      have hg' : g ≠ ⊤ := (hg.trans_lt ENNReal.one_lt_top).ne
      rw [ENNReal.toReal_add, ENNReal.toReal_sub_of_le, ENNReal.toReal_sub_of_le,
          ENNReal.toReal_sub_of_le, ENNReal.toReal_sub_of_le, ENNReal.toReal_add]
            <;> try simp [ENNReal.mul_ne_top, *]
      · ring
      · calc
          p σ * f + (1 - p σ) * g ≤ p σ * 1 + (1 - p σ) * 1 := by gcongr
          _ ≤ 1 := by simp
      · calc (1 - p σ) * g ≤ (1 - p σ) * 1 := by gcongr
          _ ≤ 1 - p σ := by simp
      · calc p σ * f ≤ p σ * 1 := by gcongr
          _ ≤ p σ := by simp
  | nonDet C₁ C₂ ih₁ ih₂ =>
    ext σ
    simp [wlp, st, Optimization.opt₂]
    simp [ih₁, ih₂]
    set f := wfp[𝒜]⟦~C₁.st⟧ (1 - X) σ
    set g := wfp[𝒜]⟦~C₂.st⟧ (1 - X) σ
    apply le_antisymm
    · simp only [inf_le_iff]
      if hfg : f ≤ g then
        right
        gcongr
        refine max_le hfg (by rfl)
      else
        left
        gcongr
        simp at hfg
        refine max_le (by rfl) hfg.le
    · simp only [le_inf_iff]
      constructor
      · gcongr; exact le_max_left f g
      · gcongr; exact le_max_right f g
  | loop b C' ih =>
    simp [wlp, st, wfp]
    simp [ih _]
    rw [fixedPoints.lfp_eq_sSup_iterate _ _, fixedPoints.gfp_eq_sInf_iterate _ _]
    · simp
      ext σ
      simp [ENNReal.sub_iSup]
      apply le_antisymm
      · simp
        intro i
        apply iInf_le_of_le (i + 1)
        induction i generalizing σ with
        | zero => simp
        | succ i ih =>
          nth_rw 2 [Function.iterate_succ']
          nth_rw 1 [Function.iterate_succ']
          simp
          set f := (fun Y ↦ b.probOf.pickProb (1 - wfp[𝒜]⟦~C'.st⟧ (1 - Y)) X)^[i + 1]
          set g := (fun Y ↦ b.probOf.pickProb (wfp[𝒜]⟦~C'.st⟧ Y) (1 - X))^[i]
          if b σ then
            simp_all only [ProbExp.pick, BExpr.probOf, ProbExp.coe_exp_coe, ProbExp.coe_apply,
              Exp.add_apply, Exp.mul_apply, BExpr.true_iver, ProbExp.exp_coe_apply,
              ProbExp.sub_apply, ProbExp.one_apply, one_mul, Exp.sub_apply, Exp.one_apply,
              tsub_self, zero_mul, add_zero]
            gcongr
            apply (wfp _ _).mono
            intro σ
            specialize ih σ
            simp
            refine ENNReal.le_sub_of_add_le_left ?_ ?_
            · simp
            · suffices hg : g ⊥ σ ≤ 1 by
                exact (ENNReal.le_sub_iff_add_le_right (hg.trans_lt ENNReal.one_lt_top).ne hg).mp ih
              simp [g]
          else
            simp_all [ProbExp.pick, BExpr.probOf]
      · simp
        intro i
        apply iInf_le_of_le i
        induction i generalizing σ with
        | zero => simp
        | succ i ih =>
          nth_rw 2 [Function.iterate_succ']
          nth_rw 1 [Function.iterate_succ']
          simp only [Function.comp_apply]
          set f := (fun Y ↦ b.probOf.pickProb (wfp[𝒜]⟦~C'.st⟧ Y) (1 - X))^[i]
          set g := (fun Y ↦ b.probOf.pickProb (1 - wfp[𝒜]⟦~C'.st⟧ (1 - Y)) X)^[i]
          if b σ then
            simp_all only [BExpr.probOf, ProbExp.pickProb_apply, ProbExp.pick, Exp.add_apply,
              Exp.mul_apply, ProbExp.coe_apply, BExpr.true_iver, one_mul, Exp.sub_apply,
              Exp.one_apply, tsub_self, ProbExp.sub_apply, ProbExp.one_apply, zero_mul, add_zero]
            gcongr
            apply (wfp _ _).mono
            intro σ
            simp
            exact tsub_le_iff_left.mp (ih σ)
          else
            simp_all only [tsub_le_iff_right, BExpr.probOf, ProbExp.pickProb_apply, ProbExp.pick,
              Exp.add_apply, Exp.mul_apply, ProbExp.coe_apply, Bool.false_eq_true, BExpr.false_iver,
              zero_mul, Exp.sub_apply, Exp.one_apply, tsub_zero, ProbExp.sub_apply,
              ProbExp.one_apply, one_mul, zero_add, ProbExp.one_sub_one_sub_apply, le_refl]
    · refine ωScottContinuous.of_monotone_map_ωSup ?_
      apply Exists.intro
      · simp [ωSup]
        simp only [DFunLike.coe]
        simp
        intro c
        rw [← toDual_iInf]
        congr
        ext σ
        simp [BExpr.probOf, ProbExp.pick]
        by_cases b σ
        · simp_all
          rw [← ENNReal.sub_iSup (by simp)]
          congr
          have := wfp.continuous C'.st (O:=𝒜)
          rw [ωScottContinuous_iff_map_ωSup_of_orderHom] at this
          simp [ωSup] at this
          let c' : Chain (ProbExp ϖ) := c.map ⟨fun x ↦ ⟨fun σ ↦ 1 - x.val σ, by intro σ; simp⟩, fun a b hab σ ↦ by
            simp only [ProbExp.coe_apply]; gcongr; apply hab⟩
          specialize this c'
          replace := congrArg DFunLike.coe this
          replace := congrFun this σ
          simp only at this
          convert this with σ'
          · simp [c']
            ext σ'
            simp
            rw [← ENNReal.sub_iInf]
            rfl
          · simp
            congr
        · simp_all
      · apply OrderHom.monotone
    · refine ωScottContinuous_iff_map_ωSup_of_orderHom.mpr ?_
      intro c
      simp
      ext σ
      simp [ωSup]
      if hb : b σ then
        simp [hb, BExpr.probOf, ProbExp.pick]
        have := wfp.continuous C'.st (O:=𝒜)
        rw [ωScottContinuous_iff_map_ωSup_of_orderHom] at this
        simp [ωSup] at this
        specialize this c
        replace := congrArg DFunLike.coe this
        replace := congrFun this σ
        simp at this
        exact this
      else
        simp [hb, BExpr.probOf, ProbExp.pick]
  | tick => ext; simp [st, wlp, wfp]
  | observe b =>
    ext σ; simp [st, wlp, wfp, BExpr.probOf, ProbExp.pick]
    if hb : b σ then
      simp [hb]
    else
      simp [hb]

omit [DecidableEq ϖ] in
theorem ωScottContinuous_dual_iff {f : Exp ϖ →o Exp ϖ} :
      ωScottContinuous ⇑(OrderHom.dual f)
    ↔ (∀ (c : Chain (Exp ϖ)ᵒᵈ), f (⨅ i, c i) = ⨅ i, f (c i)) := by
  simp [ωScottContinuous_iff_map_ωSup_of_orderHom, ωSup]; rfl

omit [DecidableEq ϖ] in
theorem ωScottContinuous_dual_iff' {f : Exp ϖ →o Exp ϖ} :
      ωScottContinuous ⇑(OrderHom.dual f)
    ↔ (∀ (c : ℕ → Exp ϖ), Antitone c → f (⨅ i, c i) = ⨅ i, f (c i)) := by
  simp [ωScottContinuous_iff_map_ωSup_of_orderHom, ωSup]
  constructor
  · intro h c hc; exact h ⟨c, hc⟩
  · intro h c; exact h c c.mono

def lΦ''.continuous' {C' : pGCL ϖ} (ih : ωScottContinuous (OrderHom.dual wlp''[O]⟦~C'⟧)) :
    ωScottContinuous ⇑(OrderHom.dual (lΦ'' O b C' X)) := by
  simp [ωScottContinuous_dual_iff] at ih ⊢
  intro c
  simp [lΦ''] at ih ⊢
  ext σ
  simp [ih, ProbExp.pick, ENNReal.mul_iInf, ENNReal.iInf_add]

omit [DecidableEq ϖ] in
theorem ProbExp.iInf_pick_of_Antitone (p : ProbExp ϖ) {f g : ℕ → Exp ϖ}
    (hf : Antitone f) (hg : Antitone g) :
    ⨅ i, p.pick (f i) (g i) = p.pick (⨅ i, f i) (⨅ i, g i) := by
  ext σ
  simp [ProbExp.pick]
  simp [ENNReal.mul_iInf]
  rw [← ENNReal.iInf_add_iInf]
  intro j k
  use j ⊔ k
  gcongr
  · apply hf; omega
  · apply hg; omega


@[simp]
def wlp''.continuous (C : pGCL ϖ) : ωScottContinuous (OrderHom.dual (C.wlp'' O)) := by
  simp [ωScottContinuous_dual_iff']
  induction C with (try simp; done)
  | assign x e => intro c h; ext σ; simp
  | seq C₁ C₂ ih₁ ih₂ =>
    intro c hc
    simp [ih₂, hc]
    rw [ih₁]
    intro a b hab
    apply (wlp'' _ _).mono (hc hab)
  | prob C₁ p C₂ ih₁ ih₂ =>
    simp [ProbExp.pick]
    intro c hc
    ext σ
    specialize ih₁ c hc
    specialize ih₂ c hc
    simp [ENNReal.mul_iInf, ih₁, ih₂]
    rw [ENNReal.iInf_add_iInf]
    intro i j; use i ⊔ j
    gcongr <;> apply (wlp'' _ _).mono (hc (by simp))
  | nonDet C₁ C₂ ih₁ ih₂ =>
    simp
    simp +contextual [ih₁, ih₂]; clear ih₁ ih₂
    intro c hc
    cases O <;> simp [Optimization.opt₂]
    · ext σ
      simp
      rw [sup_iInf_eq]
      simp [iInf_sup_eq]
      apply le_antisymm
      · simp only [le_iInf_iff]
        intro n
        apply iInf₂_le_of_le n n <;> simp
      · simp only [le_iInf_iff]
        intro i j
        apply iInf_le_of_le (i ⊔ j)
        gcongr <;> apply (wlp'' _ _).mono <;> apply hc <;> omega
    · ext
      simp
      simp [iInf_inf, inf_iInf]
      apply le_antisymm
      · simp
        intro i
        constructor <;> apply iInf₂_le_of_le i i <;> simp
      · simp
        intro i j
        constructor
        · apply iInf_le_of_le j; simp
        · apply iInf_le_of_le i; simp
  | loop b C' ih =>
    intro c hc
    simp [wlp''_loop]
    ext σ
    replace ih : ωScottContinuous ⇑(OrderHom.dual wlp''[O]⟦~C'⟧) := by
      simpa [ωScottContinuous_dual_iff']
    rw [fixedPoints.gfp_eq_sInf_iterate _ (lΦ''.continuous' ih)]
    conv => right; arg 1; ext; rw [fixedPoints.gfp_eq_sInf_iterate _ (lΦ''.continuous' ih)]
    simp
    rw [iInf_comm]
    congr with i
    suffices (⇑(lΦ'' O b C' (⨅ i, c i)))^[i] ⊤ = ⨅ i_1, (⇑(lΦ'' O b C' (c i_1)))^[i] ⊤ by
      replace := congrFun this σ; simp at this; convert this; -- simp
    clear σ
    induction i with
    | zero => simp
    | succ i ih' =>
      simp only [Function.iterate_succ', Function.comp_apply]
      rw [ih']; clear ih'
      simp [lΦ'']
      ext σ
      simp
      simp [ωScottContinuous_dual_iff'] at ih
      have : Antitone fun i_1 ↦ (fun Y ↦ p[b].pick (wlp''[O]⟦~C'⟧ Y) (c i_1))^[i] ⊤ := by
        intro a b hab σ; simp
        induction i generalizing σ with
        | zero => simp
        | succ i ih =>
          simp only [Function.iterate_succ', Function.comp_apply]
          simp [ProbExp.pick]
          gcongr
          · apply (wlp'' _ _).mono
            apply ih
          · apply hc hab
      simp [ih _ this, ← p[b].iInf_pick_of_Antitone (fun _ _ h ↦ (wlp'' _ _).mono (this h)) hc]
  | observe r =>
    intro c hc; ext σ; simp [wlp'']
    have := p[r].iInf_pick_of_Antitone (f:=c) (g:=1) hc (by intro; simp)
    simp only [Pi.one_apply, ciInf_const] at this
    simp [← this]


@[simp]
def lΦ''.continuous {C' : pGCL ϖ} : ωScottContinuous ⇑(OrderHom.dual (lΦ'' O φ C' f)) :=
  continuous' (wlp''.continuous C')


theorem wlp''_loop_eq_iter (φ  : BExpr ϖ) (C' : pGCL ϖ) [DecidablePred φ] :
    wlp''[O]⟦while ~φ{~C'}⟧ f = ⨅ n, (⇑(lΦ'' O φ C' f))^[n] ⊤ := by
  rw [wlp''_loop, fixedPoints.gfp_eq_sInf_iterate _ lΦ''.continuous]

-- attribute [- simp] Function.iterate_succ in
-- theorem wlp'_sound (C : pGCL ϖ) (X : ProbExp ϖ) :
--     wlp' 𝒟 C.st X = 1 - wp 𝒜 C.st (1 - X) := by
--   induction C generalizing X with
--   | skip =>
--     ext σ
--     simp [wlp', st]
--   | assign => ext σ; simp [st, wlp']
--   | seq C₁ C₂ ih₁ ih₂ =>
--     ext σ
--     simp [wlp', st]
--     have ih₁' : ∀ X, (wlp' 𝒟 C₁.st) X = ⟨1 - wp[𝒜]⟦~C₁.st⟧ (1 - ⇑X), by simp [← ih₁]; intro σ; simp⟩
--       := by intro X; ext σ; simp [ih₁]
--     have ih₂' : ∀ X, (wlp' 𝒟 C₂.st) X = ⟨1 - wp[𝒜]⟦~C₂.st⟧ (1 - ⇑X), by simp [← ih₂]; intro σ; simp⟩
--       := by intro X; ext σ; simp [ih₂]
--     rw [ih₂' _, ih₁' _ ]
--     simp
--     congr! 2
--     ext σ
--     simp
--     refine ENNReal.sub_sub_cancel ?_ ?_
--     · simp
--     · apply wp_le_one
--       apply ProbExp.one_sub_le
--   | prob C₁ p C₂ ih₁ ih₂ =>
--     ext σ
--     simp [wlp', st]
--     have ih₁' : ∀ X, (wlp' 𝒟 C₁.st) X = ⟨1 - wp[𝒜]⟦~C₁.st⟧ (1 - ⇑X), by simp [← ih₁]; intro σ; simp⟩
--       := by intro X; ext σ; simp [ih₁]
--     have ih₂' : ∀ X, (wlp' 𝒟 C₂.st) X = ⟨1 - wp[𝒜]⟦~C₂.st⟧ (1 - ⇑X), by simp [← ih₂]; intro σ; simp⟩
--       := by intro X; ext σ; simp [ih₂]
--     simp [ih₁', ih₂']
--     simp [ProbExp.pickProb, ProbExp.pick]
--     simp [ENNReal.mul_sub]
--     set f := wp[𝒜]⟦~C₁.st⟧ (1 - ⇑X) σ
--     set g := wp[𝒜]⟦~C₂.st⟧ (1 - ⇑X) σ
--     refine (ENNReal.toReal_eq_toReal_iff' ?_ ?_).mp ?_
--     · simp
--     · simp
--     · have hf : f ≤ 1 := wp_le_one _ _ ProbExp.one_sub_le _
--       have hg : g ≤ 1 := wp_le_one _ _ ProbExp.one_sub_le _
--       have hf' : f ≠ ⊤ := (hf.trans_lt ENNReal.one_lt_top).ne
--       have hg' : g ≠ ⊤ := (hg.trans_lt ENNReal.one_lt_top).ne
--       rw [ENNReal.toReal_add, ENNReal.toReal_sub_of_le, ENNReal.toReal_sub_of_le,
--           ENNReal.toReal_sub_of_le, ENNReal.toReal_sub_of_le, ENNReal.toReal_add]
--             <;> try simp [ENNReal.mul_ne_top, *]
--       · ring
--       · calc
--           p σ * f + (1 - p σ) * g ≤ p σ * 1 + (1 - p σ) * 1 := by gcongr
--           _ ≤ 1 := by simp
--       · calc (1 - p σ) * g ≤ (1 - p σ) * 1 := by gcongr
--           _ ≤ 1 - p σ := by simp
--       · calc p σ * f ≤ p σ * 1 := by gcongr
--           _ ≤ p σ := by simp
--   | nonDet C₁ C₂ ih₁ ih₂ =>
--     ext σ
--     simp [wlp', st, Optimization.opt₂]
--     have ih₁' : ∀ X, (wlp' 𝒟 C₁.st) X = ⟨1 - wp[𝒜]⟦~C₁.st⟧ (1 - ⇑X), by simp [← ih₁]; intro σ; simp⟩
--       := by intro X; ext σ; simp [ih₁]
--     have ih₂' : ∀ X, (wlp' 𝒟 C₂.st) X = ⟨1 - wp[𝒜]⟦~C₂.st⟧ (1 - ⇑X), by simp [← ih₂]; intro σ; simp⟩
--       := by intro X; ext σ; simp [ih₂]
--     simp [ih₁', ih₂']
--     set f := wp[𝒜]⟦~C₁.st⟧ (1 - ⇑X) σ
--     set g := wp[𝒜]⟦~C₂.st⟧ (1 - ⇑X) σ
--     apply le_antisymm
--     · simp only [inf_le_iff]
--       if hfg : f ≤ g then
--         right
--         gcongr
--         refine max_le hfg (by rfl)
--       else
--         left
--         gcongr
--         simp at hfg
--         refine max_le (by rfl) hfg.le
--     · simp only [le_inf_iff]
--       constructor
--       · gcongr; exact le_max_left f g
--       · gcongr; exact le_max_right f g
--   | loop b C' ih =>
--     simp [wlp', st, wp]
--     have ih' : ∀ X, (wlp' 𝒟 C'.st) X = ⟨1 - wp[𝒜]⟦~C'.st⟧ (1 - ⇑X), by simp [← ih]; intro σ; simp⟩
--       := by intro X; ext σ; simp [ih]
--     simp [ih' _]
--     rw [fixedPoints.lfp_eq_sSup_iterate _ _, fixedPoints.gfp_eq_sInf_iterate _ _]
--     · simp
--       ext σ
--       clear ih'
--       simp [ENNReal.sub_iSup]
--       apply le_antisymm
--       · simp
--         intro i
--         apply iInf_le_of_le (i + 1)
--         induction i generalizing σ with
--         | zero => simp
--         | succ i ih =>
--           nth_rw 2 [Function.iterate_succ']
--           nth_rw 1 [Function.iterate_succ']
--           simp
--           set f := (fun Y ↦ b.probOf.pickProb ⟨1 - wp[𝒜]⟦~C'.st⟧ (1 - ⇑Y), _⟩ X)^[i + 1]
--           set g := (fun x ↦ i[b] * wp[𝒜]⟦~C'.st⟧ x + i[b.not] * (1 - X))^[i]
--           if b σ then
--             simp_all only [ProbExp.pickProb, BExpr.probOf, ProbExp.coe_apply, Pi.add_apply,
--               Pi.mul_apply, ↓reduceIte, Pi.sub_apply, Pi.one_apply, one_mul, tsub_self, zero_mul,
--               add_zero, BExpr.true_iver, BExpr.true_not_iver]
--             gcongr
--             apply (wp _ _).mono
--             intro σ
--             specialize ih σ
--             simp
--             refine ENNReal.le_sub_of_add_le_left ?_ ?_
--             · simp
--             · suffices hg : g ⊥ σ ≤ 1 by
--                 exact (ENNReal.le_sub_iff_add_le_right (hg.trans_lt ENNReal.one_lt_top).ne hg).mp ih
--               simp [g]
--               clear! f g ih
--               clear ih
--               induction i generalizing σ with
--               | zero => simp
--               | succ i ih =>
--                 simp [Function.iterate_succ']
--                 if b σ then
--                   simp_all
--                   apply wp_le_one C' _ ih
--                 else
--                   simp_all
--           else
--             simp_all [ProbExp.pickProb, BExpr.probOf]
--       · simp
--         intro i
--         apply iInf_le_of_le i
--         induction i generalizing σ with
--         | zero => simp
--         | succ i ih =>
--           nth_rw 2 [Function.iterate_succ']
--           nth_rw 1 [Function.iterate_succ']
--           simp only [Function.comp_apply, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.one_apply]
--           set f := (fun Y ↦ b.probOf.pickProb ⟨1 - wp[𝒜]⟦~C'.st⟧ (1 - ⇑Y), _⟩ X)^[i]
--           set g := (fun x ↦ i[b] * wp[𝒜]⟦~C'.st⟧ x + i[b.not] * (1 - X))^[i]
--           if b σ then
--             simp_all only [BExpr.true_iver, one_mul, BExpr.true_not_iver, zero_mul, add_zero,
--               ProbExp.pickProb, BExpr.probOf, ProbExp.coe_apply, Pi.add_apply, Pi.mul_apply,
--               ↓reduceIte, Pi.sub_apply, Pi.one_apply, tsub_self]
--             gcongr
--             apply (wp _ _).mono
--             intro σ
--             simp
--             exact tsub_le_iff_left.mp (ih σ)
--           else
--             simp_all only [tsub_le_iff_right, Bool.false_eq_true, BExpr.false_iver, zero_mul,
--               BExpr.false_not_iver, one_mul, zero_add, ProbExp.pickProb, BExpr.probOf,
--               ProbExp.coe_apply, Pi.add_apply, Pi.mul_apply, ↓reduceIte, Pi.sub_apply, Pi.one_apply,
--               tsub_zero, ProbExp.le_one, add_tsub_cancel_of_le, le_refl]
--     · refine ωScottContinuous.of_monotone_map_ωSup ?_
--       apply Exists.intro
--       · simp [ωSup]
--         simp only [DFunLike.coe]
--         simp
--         intro c
--         rw [← toDual_iInf]
--         congr
--         ext σ
--         simp [BExpr.probOf, ProbExp.pickProb]
--         split_ifs
--         · simp_all
--           rw [← ENNReal.sub_iSup (by simp)]
--           congr
--           have := wp.continuous C'.st (O:=𝒜)
--           rw [ωScottContinuous_iff_map_ωSup_of_orderHom] at this
--           simp [ωSup] at this
--           let c' : Chain (Exp ϖ) := c.map ⟨fun x σ ↦ 1 - x.val σ, fun a b hab σ ↦ by
--             simp only; gcongr; apply hab⟩
--           specialize this c'
--           replace := congrFun this σ
--           simp only at this
--           convert this with σ'
--           simp [c']
--           have : ∀ (p : ProbExp ϖ), p.val σ' = p σ' := by intro; rfl
--           simp [this]
--           rw [← ENNReal.sub_iInf]
--           congr
--         · simp_all
--       · apply OrderHom.monotone
--     · refine ωScottContinuous.of_apply₂ ?_
--       intro σ
--       simp
--       refine ωScottContinuous_iff_monotone_map_ωSup.mpr ?_
--       apply Exists.intro
--       · simp [ωSup]
--         simp only [DFunLike.coe]
--         intro c
--         simp only [toFun_eq_coe]
--         simp [← ENNReal.iSup_add, ← ENNReal.mul_iSup]
--         congr
--         have := wp.continuous C'.st (O:=𝒜)
--         rw [ωScottContinuous_iff_map_ωSup_of_orderHom] at this
--         simp [ωSup] at this
--         specialize this c
--         exact congrFun this σ
--       · intro a b hab; simp
--         gcongr
--         apply (wp _ _).mono hab
--   | tick => ext; simp [st, wlp']
--   | observe b =>
--     ext σ; simp [st, wlp', wp, BExpr.probOf, ProbExp.pickProb]
--     if b σ then
--       simp_all only [↓reduceIte, tsub_self, add_zero, BExpr.true_iver, one_mul,
--       simp_all only [↓reduceIte, tsub_zero, zero_add, Bool.false_eq_true, BExpr.false_iver,
--         zero_mul]
--   | diverge =>
--     ext
--     simp only [st, wlp', coe_mk, Pi.one_apply, ProbExp.one_apply, wp.diverge, Pi.sub_apply,
--       tsub_self, one_ne_zero]
--     -- NOTE: BREAKS
--     sorry

-- theorem wlp_add_le (C : pGCL ϖ) : wlp 𝒜 C.st ⟨X.val + Y.val, sorry⟩ ≤ (wlp 𝒜 C.st X).val + wlp 𝒜 C.st Y := by
--   induction C generalizing X Y with try simp [wlp, st]; (try intro; simp [mul_add]; rfl)
--   | seq C₁ C₂ ih₁ ih₂ =>
--     set wlp₁ := wlp 𝒟 C₁.st
--     set wlp₂ := wlp 𝒟 C₂.st
--     grw [← ih₁]
--     apply (wlp _ _).mono
--     apply ih₂
--   | loop b C' ih =>
--     sorry
--   | nonDet C₁ C₂ ih₁ ih₂ =>
--     simp [Optimization.opt₂]
--     intro σ
--     simp
--     constructor
--     · apply le_trans (ih₁ _); simp; gcongr <;> exact le_max_left _ _
--     · apply le_trans (ih₂ _); simp; gcongr <;> exact le_max_right _ _
--   | prob => sorry
--   | diverge => intro; simp

-- theorem wlp_le_add (C : pGCL ϖ) : (wlp 𝒟 C.st X).val + wlp 𝒟 C.st Y ≤ wlp 𝒟 C.st ⟨X.val + Y.val, sorry⟩ := by
--   induction C generalizing X Y with try simp [wlp, st]; (try intro; simp [mul_add]; done)
--   | seq C₁ C₂ ih₁ ih₂ =>
--     set wlp₁ := wlp 𝒟 C₁.st
--     set wlp₂ := wlp 𝒟 C₂.st
--     grw [ih₁]
--     apply (wlp _ _).mono
--     apply ih₂
--   | loop b C' ih =>
--     sorry
--   | nonDet C₁ C₂ ih₁ ih₂ =>
--     simp [Optimization.opt₂]
--     intro σ
--     simp
--     constructor
--     · apply le_trans _ (ih₁ _); simp; gcongr <;> exact min_le_left _ _
--     · apply le_trans _ (ih₂ _); simp; gcongr <;> exact min_le_right _ _
--   | prob C₁ p C₂ ih₁ ih₂ =>
--     grw [← ih₁, ← ih₂]
--     simp [ProbExp.pick]
--     ring_nf; rfl
--   | diverge =>
--     intro; simp
--     -- NOTE: BREAKS
--     sorry

-- theorem wp_le_wlp (C : pGCL ϖ) : wp 𝒟 C.st X.val ≤ wlp 𝒟 C.st X := by
--   induction C generalizing X with try simp [wp, wlp, st]; (try intro; simp [mul_add]; rfl)
--   | seq C₁ C₂ ih₁ ih₂ =>
--     intro σ
--     replace ih₁ := fun {X} ↦ ih₁ (X:=X) σ
--     simp at ih₁
--     grw [← ih₁]
--     apply (wp _ _).mono
--     apply ih₂
--   | nonDet C₁ C₂ ih₁ ih₂ =>
--     intro σ
--     simp only [Optimization.opt₂, Pi.inf_apply, ProbExp.inf_apply]
--     gcongr
--     · apply ih₁
--     · apply ih₂
--   | prob C₁ p C₂ ih₁ ih₂ =>
--     simp [ProbExp.pick, ProbExp.pickProb]
--     gcongr
--     · apply ih₁
--     · apply ih₂
--   | loop b C' ih =>
--     intro σ
--     simp
--     apply le_trans _ (ProbExp.lfp_le_gfp'_apply _ _ _)
--     rotate_right
--     · rfl
--     simp [lfp]
--     have : Nonempty ↑{a | b.probOf.pickProb ((wlp 𝒟 C'.st) a) X ≤ a} := by use ⊤; simp
--     rw [ProbExp.sInf_apply (S:={a : ProbExp ϖ | b.probOf.pickProb ((wlp 𝒟 C'.st) a) X ≤ a})]
--     simp
--     intro p h
--     apply iInf_le_of_le ⟨p, by
--       intro σ
--       specialize h σ
--       simp [BExpr.probOf, ProbExp.pickProb, BExpr.iver, BExpr.not] at h ⊢
--       apply le_trans _ h
--       split_ifs
--       · simp
--         apply ih
--       · simp; rfl⟩
--     rfl
--   | diverge => rfl


-- attribute [- simp] Function.iterate_succ in
-- theorem wlp_sound (C : pGCL ϖ) (X : ProbExp ϖ) :
--     wp 𝒟 C.st X + wlp 𝒟 C.st 0 = wlp 𝒟 C.st X := by
--   -- let x : ϖ := sorry
--   -- if C = pgcl { {~x := 1} [] { { observe(false) } [~⟨1/2, by sorry⟩] { skip } } } then
--   --   subst_eqs
--   --   simp [st, wlp, Optimization.opt₂, wp]
--   --   ext σ;
--   --   simp [ProbExp.pick, ProbExp.pickProb, BExpr.probOf]
--   --   simp [DFunLike.coe]



--   --   sorry
--   -- else

--   induction C generalizing X with
--   | skip => ext σ; simp [wlp, st]
--   | assign => ext σ; simp [st, wlp]
--   | seq C₁ C₂ ih₁ ih₂ =>
--     -- ext σ
--     simp [wlp, st]
--     have ih₁' : ∀ (X : ProbExp ϖ), ⟨wp[𝒟]⟦~C₁.st⟧ ⇑X + ⇑((wlp 𝒟 C₁.st) 0), sorry⟩ = (wlp 𝒟 C₁.st) X := by
--       intro; ext; simp; nth_rw 2 [← ih₁]; simp
--     have ih₂' : ∀ (X : ProbExp ϖ), ⟨wp[𝒟]⟦~C₂.st⟧ ⇑X + ⇑((wlp 𝒟 C₂.st) 0), sorry⟩ = (wlp 𝒟 C₂.st) X := by
--       intro; ext; simp; nth_rw 2 [← ih₂]; simp
--     nth_rw 2 [← ih₁']
--     simp [← ih₂' X]
--     apply le_antisymm
--     · intro σ
--       simp
--       have := wp_le_add C₁ (X:=wp[𝒟]⟦~C₂.st⟧ ⇑X) (Y:=⇑((wlp 𝒟 C₂.st) 0)) σ
--       simp at this
--       grw [← this]
--       simp [add_assoc]
--       gcongr
--       rw [← ih₁]
--       rfl
--     · nth_rw 2 [← ih₁]
--       intro σ
--       simp
--       have := wp_le_add C₁ (X:=wlp 𝒟 C₂.st 0) (Y:=⇑((wlp 𝒟 C₁.st) 0)) σ
--       simp at this
--       grw [this]
--       sorry

--     ext σ
--     simp
--     rw [← ih₂]
--     rw [← ih₁]
--     apply le_antisymm
--     · simp [← add_assoc]
--       gcongr
--       apply wp_le_add
--     · simp [← add_assoc]
--       rw [ih₂]
--       have : wp[𝒟]⟦~C₁.st⟧ (⇑((wlp 𝒟 C₂.st) 0)) σ + ((wlp 𝒟 C₁.st) 0) σ = (wlp 𝒟 (C₁.seq C₂).st) 0 σ := by
--         simp [wlp, st]
--         nth_rw 2 [← ih₁]
--         rfl
--       simp [st, wlp] at this
--       simp [add_assoc]
--       rw [this]
--       rw [← ih₂]
--       set wp₁ := wp[𝒟]⟦~C₁.st⟧
--       set wp₂ := wp[𝒟]⟦~C₂.st⟧
--       set wlp₁ := wlp 𝒟 C₁.st
--       set wlp₂ := wlp 𝒟 C₂.st
--       nth_rw 2 [← ih₂']
--       calc
--         wp₁ (wp₂ ⇑X + ⇑(wlp₂ 0)) σ + (wlp₁ 0) σ ≤
--             wp₁ (wp₂ ⇑X) σ + (wlp₁ ⟨wp₂ 0, by sorry⟩ σ + wlp₁ (wlp₂ 0) σ) :=
--           by
--             simp [← add_assoc]
--             rw [ih₂]
--             sorry
--         _ ≤
--             wp₁ (wp₂ ⇑X) σ + (wlp₁ ⟨wp₂ 0 + ⇑(wlp₂ 0), _⟩) σ :=
--           by
--             gcongr
--             apply wlp_le_add



--       gcongr
--       · apply (wp _ _).mono
--         rw [← ih₂]
--         intro σ
--         simp
--       · apply (wlp _ _).mono
--         intro; simp
--   | prob C₁ p C₂ ih₁ ih₂ =>
--     ext σ
--     simp [wlp, st]
--     set wp₁ := wp[𝒟]⟦~C₁.st⟧; set wp₂ := wp[𝒟]⟦~C₂.st⟧
--     set wlp₁ := wlp 𝒟 C₁.st; set wlp₂ := wlp 𝒟 C₂.st
--     have ih₁' : ∀ X, ⟨wp₁ X.val + ⇑(wlp₁ 0), le_trans (ih₁ X).le (ProbExp.le_one _)⟩ = wlp₁ X := by
--       intro X; ext σ; exact congrFun (ih₁ X) σ
--     have ih₂' : ∀ X, ⟨wp₂ X.val + ⇑(wlp₂ 0), le_trans (ih₂ X).le (ProbExp.le_one _)⟩ = wlp₂ X := by
--       intro X; ext σ; exact congrFun (ih₂ X) σ
--     nth_rw 2 [← ih₁', ← ih₂']
--     simp [ProbExp.pickProb, ProbExp.pick]
--     ring_nf
--     nth_rw 3 [add_comm]
--     nth_rw 1 [add_assoc]
--     nth_rw 3 [add_comm]
--     nth_rw 1 [← add_assoc]
--     rfl
--   | nonDet C₁ C₂ ih₁ ih₂ =>
--     ext σ
--     simp [wlp, st, Optimization.opt₂]
--     set wp₁ := wp[𝒟]⟦~C₁.st⟧; set wp₂ := wp[𝒟]⟦~C₂.st⟧
--     set wlp₁ := wlp 𝒟 C₁.st; set wlp₂ := wlp 𝒟 C₂.st
--     have ih₁' : ∀ X, ⟨wp₁ X.val + ⇑(wlp₁ 0), le_trans (ih₁ X).le (ProbExp.le_one _)⟩ = wlp₁ X := by
--       intro X; ext σ; exact congrFun (ih₁ X) σ
--     have ih₂' : ∀ X, ⟨wp₂ X.val + ⇑(wlp₂ 0), le_trans (ih₂ X).le (ProbExp.le_one _)⟩ = wlp₂ X := by
--       intro X; ext σ; exact congrFun (ih₂ X) σ
--     nth_rw 2 [← ih₁', ← ih₂']
--     simp
--     -- set f := wp[𝒜]⟦~C₁.st⟧ (1 - ⇑X) σ
--     -- set g := wp[𝒜]⟦~C₂.st⟧ (1 - ⇑X) σ
--     apply le_antisymm
--     · simp only [le_inf_iff]
--       constructor
--       · gcongr <;> exact min_le_left _ _
--       · gcongr <;> exact min_le_right _ _
--     · -- simp only [-inf_le_iff]
--       rw [min_add]
--       gcongr
--       · rfl
--       · sorry
--       · rfl
--       · sorry
--       if h : wp₁ X σ ≤ wp₂ X σ then
--         have h' :  wlp₁ 0 σ ≤ wlp₂ 0 σ := by
--           rw [← ih₁, ← ih₂]
--           simp
--           gcongr

--           have h₁ := wp_le_wlp C₁ (X:=X) σ
--           have h₂ := wp_le_wlp C₂ (X:=X) σ
--           simp [wlp₁, wlp₂, wp₁, wp₂] at h₁ h₂ h ⊢
--           have := h.trans h₂

--           apply le_trans _ h₂
--           apply le_trans _ h
--           sorry
--         sorry
--       else
--         sorry

--       -- if hfg : f ≤ g then
--       --   right
--       --   gcongr
--       --   refine max_le hfg (by rfl)
--       -- else
--       --   left
--       --   gcongr
--       --   simp at hfg
--       --   refine max_le (by rfl) hfg.le
--   | loop b C' ih =>
--     -- simp [wlp, st, wp]
--     -- sorry
--     have ih' : ∀ X, (wlp 𝒟 C'.st) X = ⟨1 - wp[𝒜]⟦~C'.st⟧ (1 - ⇑X), by simp [← ih]; intro σ; simp⟩
--       := by intro X; ext σ; simp [ih]
--     simp [ih' _]
--     rw [fixedPoints.lfp_eq_sSup_iterate _ _, fixedPoints.gfp_eq_sInf_iterate _ _]
--     · simp
--       ext σ
--       clear ih'
--       simp [ENNReal.sub_iSup]
--       apply le_antisymm
--       · simp
--         intro i
--         apply iInf_le_of_le (i + 1)
--         induction i generalizing σ with
--         | zero => simp
--         | succ i ih =>
--           nth_rw 2 [Function.iterate_succ']
--           nth_rw 1 [Function.iterate_succ']
--           simp
--           set f := (fun Y ↦ b.probOf.pickProb ⟨1 - wp[𝒜]⟦~C'.st⟧ (1 - ⇑Y), _⟩ X)^[i + 1]
--           set g := (fun x ↦ i[b] * wp[𝒜]⟦~C'.st⟧ x + i[b.not] * (1 - X))^[i]
--           if b σ then
--             simp_all only [ProbExp.pickProb, BExpr.probOf, ProbExp.coe_apply, Pi.add_apply,
--               Pi.mul_apply, ↓reduceIte, Pi.sub_apply, Pi.one_apply, one_mul, tsub_self, zero_mul,
--               add_zero, BExpr.true_iver, BExpr.true_not_iver]
--             gcongr
--             apply (wp _ _).mono
--             intro σ
--             specialize ih σ
--             simp
--             refine ENNReal.le_sub_of_add_le_left ?_ ?_
--             · simp
--             · suffices hg : g ⊥ σ ≤ 1 by
--                 exact (ENNReal.le_sub_iff_add_le_right (hg.trans_lt ENNReal.one_lt_top).ne hg).mp ih
--               simp [g]
--               clear! f g ih
--               clear ih
--               induction i generalizing σ with
--               | zero => simp
--               | succ i ih =>
--                 simp [Function.iterate_succ']
--                 if b σ then
--                   simp_all
--                   apply wp_le_one C' _ ih
--                 else
--                   simp_all
--           else
--             simp_all [ProbExp.pickProb, BExpr.probOf]
--       · simp
--         intro i
--         apply iInf_le_of_le i
--         induction i generalizing σ with
--         | zero => simp; rfl
--         | succ i ih =>
--           nth_rw 2 [Function.iterate_succ']
--           nth_rw 1 [Function.iterate_succ']
--           simp only [Function.comp_apply, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.one_apply]
--           set f := (fun Y ↦ b.probOf.pickProb ⟨1 - wp[𝒜]⟦~C'.st⟧ (1 - ⇑Y), _⟩ X)^[i]
--           set g := (fun x ↦ i[b] * wp[𝒜]⟦~C'.st⟧ x + i[b.not] * (1 - X))^[i]
--           if b σ then
--             simp_all only [BExpr.true_iver, one_mul, BExpr.true_not_iver, zero_mul, add_zero,
--               ProbExp.pickProb, BExpr.probOf, ProbExp.coe_apply, Pi.add_apply, Pi.mul_apply,
--               ↓reduceIte, Pi.sub_apply, Pi.one_apply, tsub_self]
--             gcongr
--             apply (wp _ _).mono
--             intro σ
--             simp
--             exact tsub_le_iff_left.mp (ih σ)
--           else
--             simp_all only [tsub_le_iff_right, Bool.false_eq_true, BExpr.false_iver, zero_mul,
--               BExpr.false_not_iver, one_mul, zero_add, ProbExp.pickProb, BExpr.probOf,
--               ProbExp.coe_apply, Pi.add_apply, Pi.mul_apply, ↓reduceIte, Pi.sub_apply, Pi.one_apply,
--               tsub_zero, ProbExp.le_one, add_tsub_cancel_of_le, le_refl]
--     · refine ωScottContinuous.of_monotone_map_ωSup ?_
--       apply Exists.intro
--       · simp [ωSup]
--         simp only [DFunLike.coe]
--         simp
--         intro c
--         rw [← toDual_iInf]
--         congr
--         ext σ
--         simp [BExpr.probOf, ProbExp.pickProb]
--         split_ifs
--         · simp_all
--           rw [← ENNReal.sub_iSup (by simp)]
--           congr
--           have := wp.continuous C'.st (O:=𝒜)
--           rw [ωScottContinuous_iff_map_ωSup_of_orderHom] at this
--           simp [ωSup] at this
--           let c' : Chain (Exp ϖ) := c.map ⟨fun x σ ↦ 1 - x.val σ, fun a b hab σ ↦ by
--             simp only; gcongr; apply hab⟩
--           specialize this c'
--           replace := congrFun this σ
--           simp only at this
--           convert this with σ'
--           simp [c']
--           have : ∀ (p : ProbExp ϖ), p.val σ' = p σ' := by intro; rfl
--           simp [this]
--           rw [← ENNReal.sub_iInf]
--           congr
--         · simp_all
--       · apply OrderHom.monotone
--     · refine ωScottContinuous.of_apply₂ ?_
--       intro σ
--       simp
--       refine ωScottContinuous_iff_monotone_map_ωSup.mpr ?_
--       apply Exists.intro
--       · simp [ωSup]
--         simp only [DFunLike.coe]
--         intro c
--         simp only [toFun_eq_coe]
--         simp [← ENNReal.iSup_add, ← ENNReal.mul_iSup]
--         congr
--         have := wp.continuous C'.st (O:=𝒜)
--         rw [ωScottContinuous_iff_map_ωSup_of_orderHom] at this
--         simp [ωSup] at this
--         specialize this c
--         exact congrFun this σ
--       · intro a b hab; simp
--         gcongr
--         apply (wp _ _).mono hab
--   | tick => ext; simp [st, wlp]
--   | observe b =>
--     ext σ; simp [st, wlp, wp, BExpr.probOf, BExpr.iver]

end pGCL
