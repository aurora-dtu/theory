import Mathlib.Data.ENNReal.Inv
import Mathlib.Order.FixedPoints
import PGCL.WeakestPre
import MDP.Optimization

namespace pGCL

open OrderHom OmegaCompletePartialOrder
open scoped Optimization.Notation

variable {𝒱 : Type*} {ϖ : Γ[𝒱]} [DecidableEq 𝒱]

noncomputable def pΦ (g : ProbExp ϖ →o ProbExp ϖ) (φ : BExpr ϖ) :
    ProbExp ϖ →o ProbExp ϖ →o ProbExp ϖ :=
  ⟨fun f ↦ ⟨fun X ↦ p[φ] * g X + (1 - p[φ]) * f, by intro _ _ _; simp only; gcongr⟩,
    by intro _ _ _ _; simp only; gcongr⟩

notation "pΦ[" g "]" => pΦ g

omit [DecidableEq 𝒱] in
theorem pΦ_eq_Φ (hg : ∀ (X : ProbExp ϖ) σ, g X σ = g' X σ) :
    pΦ[g] φ x y = Φ[g'] φ x y := by
  ext σ
  simp only [pΦ, coe_mk, ProbExp.add_apply, ProbExp.mul_apply, BExpr.probOf_apply, ← hg,
    ProbExp.sub_apply, ProbExp.one_apply, Φ, mk_apply, Pi.add_apply, Pi.mul_apply, Pi.iver_apply,
    Pi.compl_apply, compl_iff_not, Iverson.iver_neg, ENNReal.natCast_sub, Nat.cast_one, inf_eq_left]
  apply ProbExp.pick_le (p:=p[φ]) <;> simp

omit [DecidableEq 𝒱] in
theorem pΦ_apply {g : ProbExp ϖ →o ProbExp ϖ} :
    pΦ[g] φ f = ⟨fun X ↦ p[φ] * g X + (1 - p[φ]) * f, by intro _ _ _; simp; gcongr⟩ := rfl
omit [DecidableEq 𝒱] in
theorem pΦ_apply₂ {g : ProbExp ϖ →o ProbExp ϖ} :
    pΦ[g] φ f X = p[φ] * g X + (1 - p[φ]) * f := rfl


omit [DecidableEq 𝒱] in
theorem ProbExp.ωScottContinuous_dual_iff' {f : ProbExp ϖ →o ProbExp ϖ} :
    ωScottContinuous f.dual ↔ ∀ (c : ℕ → ProbExp ϖ), Antitone c → f (⨅ i, c i) = ⨅ i, f (c i) := by
  simp [ωScottContinuous_iff_map_ωSup_of_orderHom, ωSup]
  constructor
  · intro h c hc; exact h ⟨c, hc⟩
  · intro h c; exact h c c.mono

omit [DecidableEq 𝒱] in
theorem pΦ.continuous {g : ProbExp ϖ →o ProbExp ϖ} (hg : ωScottContinuous g.dual) :
    ωScottContinuous (pΦ[g] b X).dual := by
  simp [ProbExp.ωScottContinuous_dual_iff'] at hg ⊢
  intro c hc
  ext σ
  simp [pΦ]
  simp [hg c hc, ENNReal.mul_iInf, ENNReal.iInf_add]
  rw [@iInf_inf]
omit [DecidableEq 𝒱] in
theorem pΦ.continuous' {g : ProbExp ϖ →o ProbExp ϖ} (hg : ωScottContinuous g) :
    ωScottContinuous (pΦ[g] b X) := by
  simp [ωScottContinuous_iff_map_ωSup_of_orderHom, ωSup] at hg ⊢
  intro c
  ext σ
  simp [pΦ]
  simp [hg c, ENNReal.mul_iSup, ENNReal.iSup_add]
  rw [@iSup_inf_eq]

noncomputable def wfp (O : Optimization) : pGCL ϖ → ProbExp ϖ →o ProbExp ϖ
  | pgcl {skip} => ⟨fun X ↦ X, fun ⦃_ _⦄ a ↦ a⟩
  | pgcl {~x := ~A} => ⟨fun X ↦ X[x ↦ A], fun ⦃_ _⦄ a h ↦ (a _)⟩
  | pgcl {~C₁; ~C₂} => (C₁.wfp O).comp (C₂.wfp O)
  | pgcl {{~C₁} [~p] {~C₂}} =>
    ⟨fun X ↦ p * C₁.wfp O X + (1 - p) * C₂.wfp O X,
     fun a b hab ↦ by simp; gcongr⟩
  | pgcl {{~C₁} [] {~C₂}} => O.opt₂ (C₁.wfp O) (C₂.wfp O)
  | pgcl {while ~b {~C'}} => ⟨fun X ↦ lfp (pΦ[wfp O C'] b X), fun _ _ _ ↦ by simp; gcongr⟩
  | pgcl {tick(~e)} => ⟨(·), fun _ _ h ↦ by simp; gcongr⟩
  | pgcl {observe(~b)} => ⟨fun X ↦ p[b] ⇨ X, fun _ _ h ↦ by simp only; gcongr⟩

syntax "wfp[" term "]⟦" cpgcl_prog "⟧" : term

macro_rules
| `(wfp[$O]⟦ $p ⟧) => `(pGCL.wfp $O pgcl {$p})

@[app_unexpander pGCL.wfp]
def wfpUnexpander : Lean.PrettyPrinter.Unexpander
| `($(_) $o $c) => do
    let c ← match c with | `(pgcl {$c}) => pure c | _ => `(cpgcl_prog| ~ $c)
    `(wfp[$o]⟦$c⟧)
| _ => throw ()

noncomputable def wfp' (O : Optimization) : pGCL ϖ → 𝔼[ϖ, ENNReal] →o 𝔼[ϖ, ENNReal]
  | pgcl {skip} => ⟨fun X ↦ X, fun ⦃_ _⦄ a ↦ a⟩
  | pgcl {~x := ~A} => ⟨fun X ↦ X[x ↦ A], fun ⦃_ _⦄ a i ↦ by exact a _⟩
  | pgcl {~C₁; ~C₂} => (C₁.wfp' O).comp (C₂.wfp' O)
  | pgcl {{~C₁} [~p] {~C₂}} =>
    ⟨fun X ↦ p * C₁.wfp' O X + (1 - p) * C₂.wfp' O X,
     fun a b hab ↦ by simp only; gcongr⟩
  | pgcl {{~C₁}[]{~C₂}} =>
    ⟨O.opt₂ (C₁.wfp' O) (C₂.wfp' O), fun a b hab ↦ by simp only [Optimization.opt₂_apply]; gcongr⟩
  | pgcl {while ~b {~C'}} => ⟨fun X ↦ lfp (Φ[wfp' O C'] b X), fun _ _ _ ↦ by simp; gcongr⟩
  | pgcl {tick(~e)} => ⟨(·), fun _ _ h ↦ by simp; gcongr⟩
  | pgcl {observe(~b)} => ⟨fun X ↦ p[b] * X + (1 - p[b]), fun _ _ h ↦ by simp; gcongr⟩

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
  | prob C₁ p C₂ ih₁ ih₂ => ext; simp [wfp, wfp', ← ih₁, ← ih₂]
  | observe b => ext σ; simp [wfp, wfp', himp]; if h : b σ then simp [h, eq_comm] else simp [h]
  | nonDet C₁ C₂ ih₁ ih₂ =>
    simp [wfp, wfp', ← ih₁, ← ih₂]; ext; simp [Optimization.opt₂]
    cases O <;> simp
  | loop b C' ih =>
    simp [wfp, wfp']
    apply le_antisymm
    · suffices lfp ((pΦ[wfp[O]⟦~C'⟧] b) X) ≤ ⟨lfp ((Φ[wfp'[O]⟦~C'⟧] b) ⇑X), by
          apply lfp_le
          intro σ
          replace ih := congrFun (@ih ⟨1, by simp⟩) σ
          simp at ih
          simp [Φ, ← ih]
          by_cases hb : b σ <;> simp [hb]⟩ by
        exact Pi.le_def.mpr this
      apply lfp_le
      intro σ
      simp
      nth_rw 2 [← map_lfp]
      rw [pΦ_eq_Φ (g':=wfp'[O]⟦~C'⟧)]
      · rfl
      · simp [ih]
    · apply lfp_le
      nth_rw 2 [← map_lfp]
      rw [pΦ_eq_Φ (g':=wfp'[O]⟦~C'⟧)]
      simp [ih]

theorem wfp'_loop (φ  : BExpr ϖ) (C' : pGCL ϖ) :
    wfp'[O]⟦while ~φ {~C'}⟧ f = lfp (Φ[wfp'[O]⟦~C'⟧] φ f) := rfl

theorem wfp'_fp (φ : BExpr ϖ) (C' : pGCL ϖ) :
    (Φ[wfp'[O]⟦~C'⟧] φ f) (wfp'[O]⟦while ~φ {~C'}⟧ f) = wfp'[O]⟦while ~φ {~C'}⟧ f := by
  simp [wfp'_loop]

theorem wfp_loop (φ  : BExpr ϖ) (C' : pGCL ϖ) :
    wfp[O]⟦while ~φ {~C'}⟧ f = lfp (Φ[wfp'[O]⟦~C'⟧] φ f) := by simp [wfp_eq_wfp', wfp'_loop]

noncomputable def wlp (O : Optimization) : pGCL ϖ → ProbExp ϖ →o ProbExp ϖ
  | pgcl {skip} => ⟨fun X ↦ X, fun ⦃_ _⦄ a ↦ a⟩
  | pgcl {~x := ~A} => ⟨fun X ↦ X[x ↦ A], fun ⦃_ _⦄ a i ↦ a _⟩
  | pgcl {~C₁; ~C₂} => (C₁.wlp O).comp (C₂.wlp O)
  | pgcl {{~C₁} [~p] {~C₂}} =>
    ⟨fun X ↦ p * C₁.wlp O X + (1 - p) * C₂.wlp O X,
     fun a b hab ↦ by simp only; gcongr⟩
  | pgcl {{~C₁}[]{~C₂}} =>
    ⟨O.opt₂ (C₁.wlp O) (C₂.wlp O), fun a b hab ↦ by simp only [Optimization.opt₂_apply]; gcongr⟩
  | pgcl {while ~b {~C'}} => ⟨fun X ↦ gfp (pΦ[wlp O C'] b X), fun _ _ h ↦ by simp; gcongr⟩
  | pgcl {tick(~e)} => ⟨(·), fun _ _ h ↦ by simp; gcongr⟩
  | pgcl {observe(~b)} => ⟨fun X ↦ p[b] * X, fun _ _ h ↦ by simp; gcongr⟩

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
  ⟨fun Y ↦ p[b] * C'.wlp O Y + (1 - p[b]) * f, fun _ _ _ ↦ by simp; gcongr⟩

section

variable {X : ProbExp ϖ}

theorem wlp_loop (φ  : BExpr ϖ) (C' : pGCL ϖ) :
    wlp[O]⟦while ~φ {~C'}⟧ f = gfp (lΦ O φ C' f) := rfl

@[simp] theorem wlp.skip_apply : wlp[O]⟦skip⟧ X = X := rfl
@[simp] theorem wlp.assign_apply :
    wlp[O]⟦~x := ~A⟧ X = X[x ↦ A] := rfl
@[simp] theorem wlp.seq_apply : wlp[O]⟦~C₁ ; ~C₂⟧ X = wlp[O]⟦~C₁⟧ (wlp[O]⟦~C₂⟧ X) := rfl
@[simp] theorem wlp.prob_apply :
    wlp[O]⟦{~C₁}[~p]{~C₂}⟧ X = p * C₁.wlp O X + (1 - p) * C₂.wlp O X
:= rfl
@[simp] theorem wlp.nonDet_apply : wlp[O]⟦{~C₁}[]{~C₂}⟧ X = O.opt₂ (C₁.wlp O X) (C₂.wlp O X) := by
  ext; simp [wlp]
@[simp] theorem wlp.tick_apply : wlp[O]⟦tick(~e)⟧ X = X := rfl
@[simp] theorem wlp.observe_apply :
    wlp[O]⟦observe(~b)⟧ X = p[b] * X := rfl

end

noncomputable def wlp'' (O : Optimization) (C : pGCL ϖ) : 𝔼[ϖ, ENNReal] →o 𝔼[ϖ, ENNReal] :=
  ⟨fun X ↦ wlp[O]⟦~C⟧ (ProbExp.ofExp X),
    by intro a b hab σ; simp [ProbExp.ofExp]; apply (wlp _ _).mono; gcongr⟩

syntax "wlp''[" term "]⟦" cpgcl_prog "⟧" : term

macro_rules
| `(wlp''[$O]⟦ $p ⟧) => `(pGCL.wlp'' $O pgcl {$p})

@[app_unexpander pGCL.wlp'']
def wlp''Unexpander : Lean.PrettyPrinter.Unexpander
| `($(_) $o $c) => do
    let c ← match c with | `(pgcl {$c}) => pure c | _ => `(cpgcl_prog| ~ $c)
    `(wlp''[$o]⟦$c⟧)
| _ => throw ()

section

variable {X : 𝔼[ϖ, ENNReal]}

@[simp] theorem wlp''.skip_apply : wlp''[O]⟦skip⟧ X = X ⊓ 1 := rfl
@[simp] theorem wlp''.assign_apply :
    wlp''[O]⟦~x := ~A⟧ X = (X ⊓ 1)[x ↦ A] := rfl
@[simp] theorem wlp''.seq_apply : wlp''[O]⟦~C₁ ; ~C₂⟧ X = wlp''[O]⟦~C₁⟧ (wlp''[O]⟦~C₂⟧ X ⊓ 1) := by
  simp [wlp'', ProbExp.ofExp]; congr! 1; ext; simp
@[simp] theorem wlp''.prob_apply :
    wlp''[O]⟦{~C₁}[~p]{~C₂}⟧ X = p * C₁.wlp'' O X + (1 - p) * C₂.wlp'' O X := by
  ext; simp [wlp'']
@[simp] theorem wlp''.nonDet_apply :
    wlp''[O]⟦{~C₁}[]{~C₂}⟧ X = O.opt₂ (C₁.wlp'' O X) (C₂.wlp'' O X) := by
  ext; simp [wlp'']; cases O <;> simp [Optimization.opt₂]
@[simp] theorem wlp''.tick_apply : wlp''[O]⟦tick(~e)⟧ X = X ⊓ 1 := by
  simp [wlp'']; rfl
@[simp] theorem wlp''.observe_apply :
    wlp''[O]⟦observe(~b)⟧ X = p[b] * (X ⊓ 1) := by
  ext σ
  simp [wlp'', ProbExp.ofExp]

end

attribute [- simp] Function.iterate_succ in
theorem wlp'_sound (C : pGCL ϖ) (X : ProbExp ϖ) : wlp[O]⟦~C⟧ X = 1 - wfp[O.dual]⟦~C⟧ (1 - X) := by
  induction C generalizing X with
  | skip => ext σ; simp [wlp, wfp]
  | assign => ext σ; simp [wlp, wfp]
  | seq C₁ C₂ ih₁ ih₂ =>
    ext σ
    simp [wlp, wfp]
    rw [ih₂ _, ih₁ _ ]
    simp
  | prob C₁ p C₂ ih₁ ih₂ =>
    ext σ
    simp [wlp, wfp]
    simp [ih₁, ih₂]
    simp [ENNReal.mul_sub]
    set f := wfp[O.dual]⟦~C₁⟧ (1 - X) σ
    set g := wfp[O.dual]⟦~C₂⟧ (1 - X) σ
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
      · grw [hg]; simp
      · grw [hf]; simp
  | nonDet C₁ C₂ ih₁ ih₂ =>
    ext σ
    simp [wfp, ih₁, ih₂]
    cases O
    · simp [Optimization.opt₂, Optimization.dual]
      simp [Optimization.dual] at ih₁ ih₂
      set f := wfp[𝒟]⟦~C₁⟧ (1 - X) σ
      set g := wfp[𝒟]⟦~C₂⟧ (1 - X) σ
      apply le_antisymm
      · simp only [sup_le_iff]
        constructor
        · gcongr; exact min_le_left _ _
        · gcongr; exact min_le_right _ _
      · simp only [le_sup_iff]
        if hfg : f ≤ g then
          left
          gcongr
          simp [f, g] at hfg
          apply le_min (by rfl) hfg
        else
          right
          gcongr
          apply le_min (le_of_not_ge hfg) (by rfl)
    · simp [Optimization.opt₂, Optimization.dual]
      simp [Optimization.dual] at ih₁ ih₂
      set f := wfp[𝒜]⟦~C₁⟧ (1 - X) σ
      set g := wfp[𝒜]⟦~C₂⟧ (1 - X) σ
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
    simp [wlp, wfp]
    rw [ProbExp.gfp_eq_lfp_compl]
    simp [compl]
    congr! 4 with Y
    ext σ
    simp [pΦ]
    if hb : b σ then simp [hb, ih] else simp [hb]
  | tick => ext; simp [wlp, wfp]
  | observe b =>
    ext σ; simp [wlp, wfp, BExpr.probOf]
    if hb : b σ then
      simp [hb]
      have : 1 ≤ 1 - X σ ↔ X σ = 0 := by
        constructor
        · intro h
          have : X σ ≤ 1 := ProbExp.le_one_apply X σ
          rw [ENNReal.le_sub_iff_add_le_left] at h
          · have : (X σ + 1) - 1 ≤ 1 - 1 := tsub_le_tsub_right h 1
            simp_all
          · simp_all
          · simp_all
        · simp_all
      split_ifs <;> simp_all
    else
      simp [hb]

attribute [- simp] Function.iterate_succ in
theorem wlp'_sound' (C : pGCL ϖ) : wlp[O]⟦~C⟧ = wfp[O.dual]⟦~C⟧ᶜ := by ext; rw [wlp'_sound]; rfl

def wfp'.continuous (C : pGCL ϖ) : ωScottContinuous (C.wfp' O) := by
  refine ωScottContinuous.of_map_ωSup_of_orderHom ?_
  simp [ωSup, Chain, Pi.evalOrderHom, Chain.map]
  induction C with
  | skip => simp [wfp']
  | assign x A => intro C; ext σ; simp [wfp']
  | seq C₁ C₂ ih₁ ih₂ =>
    simp [wfp']
    simp_all
    intro c
    specialize ih₁ ⟨fun i a ↦ wfp'[O]⟦~C₂⟧ (c i) a,
                    fun _ _ h _ ↦ by simp; apply (wfp' _ _).mono; apply c.mono h⟩
    simp at ih₁
    simp [ih₁]
  | nonDet C₁ C₂ ih₁ ih₂ =>
    intro c; ext σ
    cases O
    · simp_all [wfp', Optimization.opt₂, ← iSup_sup_eq]
    simp_all [wfp', Optimization.opt₂]
    refine Eq.symm (iSup_inf_of_monotone ?_ ?_)
    · intro a b hab; apply (wfp' _ _).mono (c.mono hab)
    · intro a b hab; apply (wfp' _ _).mono (c.mono hab)
  | prob C₁ p C₂ ih₁ ih₂ =>
    intro c; ext σ
    cases O
    · simp_all only [wfp', mk_apply, Pi.add_apply, Pi.mul_apply, ENNReal.mul_iSup, Pi.sub_apply,
      Pi.one_apply, ENNReal.add_iSup, ENNReal.iSup_add]
      refine iSup_iSup_eq_iSup _ ?_ ?_
      · intro _ _ _ _; simp; gcongr; apply (wfp' _ _).mono; gcongr
      · intro _ _ _ _; simp; gcongr; apply (wfp' _ _).mono; gcongr
    · simp_all only [wfp', mk_apply, Pi.add_apply, Pi.mul_apply, ENNReal.mul_iSup, Pi.sub_apply,
      Pi.one_apply, ENNReal.add_iSup, ENNReal.iSup_add]
      refine iSup_iSup_eq_iSup _ ?_ ?_
      · intro _ _ _ _; simp; gcongr; apply (wfp' _ _).mono; gcongr
      · intro _ _ _ _; simp; gcongr; apply (wfp' _ _).mono; gcongr
  | loop b C' ih =>
    simp_all [wfp']
    intro c
    simp [Φ_iSup']
    have := OrderHom.lfp_iSup (f:=⟨fun i ↦ (Φ[wfp'[O]⟦~C'⟧] b) (c i), fun _ _ _ ↦ by simp; gcongr⟩)
    simp at this
    rw [this (fun _ ↦ Φ.continuous (ωScottContinuous_iff_map_ωSup_of_orderHom.mpr ih))]
    ext; simp
  | tick => simp [wfp']
  | observe =>
    intro; ext
    simp_all only [wfp', mk_apply, Pi.add_apply, Pi.mul_apply, BExpr.probOf_apply, ENNReal.mul_iSup,
      Pi.sub_apply, Pi.ofNat_apply, ENNReal.iSup_add]

def wfp.continuous (C : pGCL ϖ) : ωScottContinuous (C.wfp O) := by
  refine ωScottContinuous.of_map_ωSup_of_orderHom ?_
  simp [Chain, ωSup, Chain.map, comp_coe, Function.comp_apply,]
  intro c
  have := wfp'.continuous C (O:=O)
  simp [ωScottContinuous_iff_map_ωSup_of_orderHom, ωSup, Chain, Pi.evalOrderHom, Chain.map] at this
  ext σ
  simp [wfp_eq_wfp']
  convert congrFun (this ⟨fun i ↦ c i, fun _ _ _ _ ↦ by simp; apply c.mono ‹_›⟩) σ
  simp

omit [DecidableEq 𝒱] in
theorem ωScottContinuous_dual_prob_iff {f : ProbExp ϖ →o ProbExp ϖ} :
    ωScottContinuous f.dual ↔ ∀ (c : ℕ → ProbExp ϖ), Antitone c → f (⨅ i, c i) = ⨅ i, f (c i) := by
  simp [ωScottContinuous_iff_map_ωSup_of_orderHom, ωSup]
  constructor
  · intro h c hc; exact h ⟨c, hc⟩
  · intro h c; exact h c c.mono

def wlp.continuous_aux (C : pGCL ϖ) (h : ∀ X, wlp[O]⟦~C⟧ X = 1 - wfp[O.dual]⟦~C⟧ (1 - X)) :
    ωScottContinuous (C.wlp O).dual := by
  simp [ωScottContinuous_dual_prob_iff]
  have :
        wlp[O]⟦~C⟧
      = ⟨fun X ↦ 1 - wfp[O.dual]⟦~C⟧ (1 - X), fun _ _ _ ↦ by simp; gcongr⟩ := by
    ext; simp [h]
  simp [this]; clear this
  have wfp_con := wfp.continuous C (O:=O.dual)
  simp [ωScottContinuous_iff_map_ωSup_of_orderHom, ωSup] at wfp_con
  intro c hc
  have : (1 - ⨅ i, c i) = ⨆ i, 1 - c i := by ext σ; simp [ENNReal.sub_iInf]
  simp [this]
  specialize wfp_con ⟨fun i ↦ 1 - c i, fun _ _ h ↦ by simp; gcongr; apply hc h⟩
  simp only [DFunLike.coe] at wfp_con; simp at wfp_con
  ext
  simp [wfp_con, ENNReal.sub_iSup]

def wlp.continuous (C : pGCL ϖ) : ωScottContinuous (C.wlp O).dual :=
  continuous_aux C (wlp'_sound C)

@[simp]
def wlp''.continuous (C : pGCL ϖ) : ωScottContinuous (C.wlp'' O).dual := by
  have wlp_con := wlp.continuous (O:=O) C
  simp [ωScottContinuous_dual_iff', wlp'']
  simp [ωScottContinuous_dual_prob_iff] at wlp_con
  intro c hc
  specialize wlp_con (ProbExp.ofExp ∘ c) ?_
  · intro a b hab σ;
    simp only [Function.comp_apply, ProbExp.ofExp, ProbExp.coe_apply, Pi.inf_apply, Pi.one_apply]
    gcongr
    apply hc hab
  ext σ
  simp
  replace wlp_con := DFunLike.congr_fun wlp_con σ
  simp at wlp_con
  convert wlp_con
  simp [ProbExp.ofExp, iInf_inf]
  ext
  simp

@[simp]
def Φ.wlp''_continuous {C' : pGCL ϖ} : ωScottContinuous (Φ[wlp''[O]⟦~C'⟧] φ f).dual :=
  cocontinuous (wlp''.continuous C')

theorem wlp''_loop_eq_gfp (φ  : BExpr ϖ) (C' : pGCL ϖ) :
    wlp''[O]⟦while ~φ {~C'}⟧ f = gfp (pΦ[wlp[O]⟦~C'⟧] φ (ProbExp.ofExp f)) := by
  simp [wlp'', wlp]
theorem wlp''_loop_eq_iter (φ  : BExpr ϖ) (C' : pGCL ϖ) :
    wlp''[O]⟦while ~φ {~C'}⟧ f = ⨅ n, (Φ[wlp''[O]⟦~C'⟧] φ (f ⊓ 1))^[n] 1 := by
  rw [wlp''_loop_eq_gfp]
  simp [wlp'']
  rw [fixedPoints.gfp_eq_sInf_iterate _ (pΦ.continuous (wlp.continuous C'))]
  ext σ
  simp [Φ, pΦ]
  congr! with n
  induction n with
  | zero => simp; rfl
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    simp [← ih]; clear ih
    ext; simp [Iverson.iver, BExpr.probOf, compl]; split_ifs <;> simp

end pGCL
