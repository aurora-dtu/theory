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
  ⟨fun f ↦ ⟨fun X ↦ p[φ].pickProb (g X) f, by intro _ _ _; simp only; gcongr⟩,
    by intro _ _ _ _; simp only; gcongr⟩

notation "pΦ[" g "]" => pΦ g

omit [DecidableEq 𝒱] in
theorem pΦ_eq_Φ (hg : ∀ (X : ProbExp ϖ) σ, g X σ = g' X σ) :
    pΦ[g] φ x y = Φ[g'] φ x y := by
  ext σ
  simp [pΦ, Φ_eq_pick, ProbExp.pick, hg]

omit [DecidableEq 𝒱] in
theorem pΦ_apply {g : ProbExp ϖ →o ProbExp ϖ} :
    pΦ[g] φ f = ⟨fun X ↦ p[φ].pickProb (g X) f, by intro _ _ _; simp; gcongr⟩ := rfl
omit [DecidableEq 𝒱] in
theorem pΦ_apply₂ {g : ProbExp ϖ →o ProbExp ϖ} :
    pΦ[g] φ f X = p[φ].pickProb (g X) f := rfl


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
  simp [pΦ, ProbExp.pickProb]
  simp [hg c hc, ENNReal.mul_iInf, ENNReal.iInf_add]
  rw [@iInf_inf]
omit [DecidableEq 𝒱] in
theorem pΦ.continuous' {g : ProbExp ϖ →o ProbExp ϖ} (hg : ωScottContinuous g) :
    ωScottContinuous (pΦ[g] b X) := by
  simp [ωScottContinuous_iff_map_ωSup_of_orderHom, ωSup] at hg ⊢
  intro c
  ext σ
  simp [pΦ, ProbExp.pickProb]
  simp [hg c, ENNReal.mul_iSup, ENNReal.iSup_add]
  rw [@iSup_inf_eq]

noncomputable def wfp (O : Optimization) : pGCL ϖ → ProbExp ϖ →o ProbExp ϖ
  | pgcl {skip} => ⟨fun X ↦ X, fun ⦃_ _⦄ a ↦ a⟩
  | pgcl {~x := ~A} => ⟨fun X ↦ X[x ↦ A], fun ⦃_ _⦄ a i ↦ a _⟩
  | pgcl {~C₁; ~C₂} => (C₁.wfp O).comp (C₂.wfp O)
  | pgcl {{~C₁} [~p] {~C₂}} =>
    ⟨fun X ↦ p.pickProb (C₁.wfp O X) (C₂.wfp O X),
     fun a b hab ↦ by apply ProbExp.pickProb_le <;> apply (wfp O _).mono hab⟩
  | pgcl {{~C₁} [] {~C₂}} => O.opt₂ (C₁.wfp O) (C₂.wfp O)
  | pgcl {while ~b {~C'}} => ⟨fun X ↦ lfp (pΦ[wfp O C'] b X), fun _ _ _ ↦ by simp; gcongr⟩
  | pgcl {tick(~e)} => ⟨(·), fun _ _ h ↦ by simp; gcongr⟩
  | pgcl {observe(~b)} => ⟨(p[b].pickProb · 1), fun _ _ h ↦ by simp; gcongr⟩

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
    ⟨fun X ↦ p.pick (C₁.wfp' O X) (C₂.wfp' O X),
     fun a b hab ↦ by apply ProbExp.pick_le <;> apply (wfp' O _).mono hab⟩
  | pgcl {{~C₁}[]{~C₂}} =>
    ⟨O.opt₂ (C₁.wfp' O) (C₂.wfp' O), fun a b hab ↦ by simp only [Optimization.opt₂_apply]; gcongr⟩
  | pgcl {while ~b {~C'}} => ⟨fun X ↦ lfp (Φ[wfp' O C'] b X), fun _ _ _ ↦ by simp; gcongr⟩
  | pgcl {tick(~e)} => ⟨(·), fun _ _ h ↦ by simp; gcongr⟩
  | pgcl {observe(~b)} => ⟨(p[b].pick · 1), fun _ _ h ↦ by simp; gcongr⟩

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
    ⟨fun X ↦ p.pickProb (C₁.wlp O X) (C₂.wlp O X),
     fun a b hab ↦ by apply ProbExp.pickProb_le <;> apply (wlp O _).mono hab⟩
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
  ⟨fun Y ↦ p[b].pickProb (C'.wlp O Y) f, fun _ _ _ ↦ by simp; gcongr⟩

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

-- TODO: remove this?
-- theorem wlp''_loop (φ  : BExpr ϖ) (C' : pGCL ϖ) :
--     wlp'' O pgcl {while ~φ {~C'}} f = gfp (Φ[wlp''[O]⟦~C'⟧] φ f) := by rfl

section

variable {X : 𝔼[ϖ, ENNReal]}

@[simp] theorem wlp''.skip_apply : wlp''[O]⟦skip⟧ X = X ⊓ 1 := rfl
@[simp] theorem wlp''.assign_apply :
    wlp''[O]⟦~x := ~A⟧ X = (X ⊓ 1)[x ↦ A] := rfl
@[simp] theorem wlp''.seq_apply : wlp''[O]⟦~C₁ ; ~C₂⟧ X = wlp''[O]⟦~C₁⟧ (wlp''[O]⟦~C₂⟧ X ⊓ 1) := by
  simp [wlp'', ProbExp.ofExp]; congr! 1; ext; simp
@[simp] theorem wlp''.prob_apply :
    wlp''[O]⟦{~C₁}[~p]{~C₂}⟧ X = p.pick (C₁.wlp'' O X) (C₂.wlp'' O X) := by
  simp [wlp'']
@[simp] theorem wlp''.nonDet_apply :
    wlp''[O]⟦{~C₁}[]{~C₂}⟧ X = O.opt₂ (C₁.wlp'' O X) (C₂.wlp'' O X) := by
  ext; simp [wlp'']; cases O <;> simp [Optimization.opt₂]
@[simp] theorem wlp''.tick_apply : wlp''[O]⟦tick(~e)⟧ X = X ⊓ 1 := by
  simp [wlp'']; rfl
-- TODO: should the go to 0 or 1?
@[simp] theorem wlp''.observe_apply :
    wlp''[O]⟦observe(~b)⟧ X = p[b].pick (X ⊓ 1) 0 := by
  ext σ
  simp [wlp'', ProbExp.ofExp, ProbExp.pick]
  -- if hb : b σ then simp [hb] else simp [hb]

end

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
    · simp_all only [wfp', ProbExp.pick, mk_apply, Pi.add_apply, Pi.mul_apply, ENNReal.mul_iSup,
      Pi.sub_apply, Pi.one_apply, ENNReal.add_iSup, ENNReal.iSup_add]
      refine iSup_iSup_eq_iSup _ ?_ ?_
      · intro _ _ _ _; simp; gcongr; apply (wfp' _ _).mono; gcongr
      · intro _ _ _ _; simp; gcongr; apply (wfp' _ _).mono; gcongr
    · simp_all only [wfp', ProbExp.pick, mk_apply, Pi.add_apply, Pi.mul_apply, ENNReal.mul_iSup,
      Pi.sub_apply, Pi.one_apply, ENNReal.add_iSup, ENNReal.iSup_add]
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
    simp_all only [wfp', ProbExp.pick, mul_one, mk_apply, Pi.add_apply, Pi.mul_apply,
      BExpr.probOf_apply, ENNReal.mul_iSup, Pi.sub_apply, Pi.ofNat_apply, ENNReal.iSup_add]

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

attribute [- simp] Function.iterate_succ in
theorem wlp'_sound (C : pGCL ϖ) (X : ProbExp ϖ) :
    wlp[O]⟦~C⟧ X = 1 - wfp[O.dual]⟦~C⟧ (1 - X) := by
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
    simp [ProbExp.pick]
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
      · calc
          p σ * f + (1 - p σ) * g ≤ p σ * 1 + (1 - p σ) * 1 := by gcongr
          _ ≤ 1 := by simp
      · calc (1 - p σ) * g ≤ (1 - p σ) * 1 := by gcongr
          _ ≤ 1 - p σ := by simp
      · calc p σ * f ≤ p σ * 1 := by gcongr
          _ ≤ p σ := by simp
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
    set F : ProbExp ϖ →o ProbExp ϖ :=
      ⟨fun X ↦ 1 - wfp[O.dual]⟦~C'⟧ (1 - X), fun _ _ _ ↦ by simp only; gcongr⟩
    have ih' : wlp[O]⟦~C'⟧ = F := by
      ext; simp [ih, F]
    simp [ih']
    rw [fixedPoints.lfp_eq_sSup_iterate _ (pΦ.continuous' (wfp.continuous C'))]
    rw [fixedPoints.gfp_eq_sInf_iterate _ _]
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
          if b σ then
            nth_rw 1 [pΦ_apply₂]
            nth_rw 1 [pΦ_apply₂]
            simp_all only [ProbExp.pickProb_apply, ProbExp.pick_true, ProbExp.sub_apply,
              ProbExp.one_apply]
            gcongr
            apply (wfp _ _).mono
            intro σ
            specialize ih σ
            simp
            grw [ih]
            simp
          else
            simp_all [ProbExp.pick, BExpr.probOf, pΦ_apply₂]
      · simp
        intro i
        apply iInf_le_of_le i
        induction i generalizing σ with
        | zero => simp
        | succ i ih =>
          nth_rw 2 [Function.iterate_succ']
          nth_rw 1 [Function.iterate_succ']
          simp only [Function.comp_apply]
          set f := (fun Y ↦ p[b].pickProb (wfp[O.dual]⟦~C'.st⟧ Y) (1 - X))^[i]
          set g := (fun Y ↦ p[b].pickProb (1 - wfp[O.dual]⟦~C'.st⟧ (1 - Y)) X)^[i]
          if b σ then
            nth_rw 1 [pΦ_apply₂]
            nth_rw 1 [pΦ_apply₂]
            simp_all only [BExpr.probOf, ProbExp.pickProb_apply, ProbExp.pick, ProbExp.mk_vcoe,
              Pi.add_apply, Pi.mul_apply, Pi.iver_apply, Iverson.iver_True, Nat.cast_one, one_mul,
              Pi.sub_apply, Pi.ofNat_apply, tsub_self, ProbExp.sub_apply, ProbExp.one_apply,
              zero_mul, add_zero]
            gcongr
            apply (wfp _ _).mono
            intro σ
            simp
            exact tsub_le_iff_left.mp (ih σ)
          else
            simp_all only [tsub_le_iff_right, pΦ_apply₂, BExpr.probOf, ProbExp.pickProb_apply,
              ProbExp.pick, ProbExp.mk_vcoe, Pi.add_apply, Pi.mul_apply, Pi.iver_apply,
              Iverson.iver_False, Nat.cast_zero, zero_mul, Pi.sub_apply, Pi.ofNat_apply, tsub_zero,
              ProbExp.sub_apply, ProbExp.one_apply, one_mul, zero_add,
              ProbExp.one_sub_one_sub_apply, le_refl]
    · refine pΦ.continuous ?_
      simp [F]
      refine ProbExp.ωScottContinuous_dual_iff'.mpr ?_
      simp
      intro c hc
      have h₁ := wfp.continuous C' (O:=O.dual)
      simp [ωScottContinuous_iff_map_ωSup_of_orderHom] at h₁
      replace h₁ := h₁ ⟨fun i ↦ 1 - c i, fun  _ _ h ↦ by simp; gcongr; apply hc h⟩
      simp [ωSup] at h₁
      simp only [DFunLike.coe] at h₁
      simp at h₁
      have h₂ : (⨆ i, 1 - c i) = 1 - ⨅ i, c i := by ext σ; simp [ENNReal.sub_iInf]
      ext σ
      simp [← h₂, h₁, ENNReal.sub_iSup]
  | tick => ext; simp [wlp, wfp]
  | observe b =>
    ext σ; simp [wlp, wfp, BExpr.probOf, ProbExp.pick]
    if hb : b σ then
      simp [hb]
    else
      simp [hb]

omit [DecidableEq 𝒱] in
theorem ωScottContinuous_dual_prob_iff {f : ProbExp ϖ →o ProbExp ϖ} :
    ωScottContinuous f.dual ↔ ∀ (c : ℕ → ProbExp ϖ), Antitone c → f (⨅ i, c i) = ⨅ i, f (c i) := by
  simp [ωScottContinuous_iff_map_ωSup_of_orderHom, ωSup]
  constructor
  · intro h c hc; exact h ⟨c, hc⟩
  · intro h c; exact h c c.mono

def wlp.continuous (C : pGCL ϖ) : ωScottContinuous (C.wlp O).dual := by
  simp [ωScottContinuous_dual_prob_iff]
  have :
        wlp[O]⟦~C⟧
      = ⟨fun X ↦ 1 - wfp[O.dual]⟦~C⟧ (1 - X), fun _ _ _ ↦ by simp; gcongr⟩ := by
    ext; simp [wlp'_sound]
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

omit [DecidableEq 𝒱] in
theorem ProbExp.iInf_pick_of_Antitone (p : ProbExp ϖ) {f g : ℕ → 𝔼[ϖ, ENNReal]}
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
    simp
    simp [← ih]; clear ih
    simp [ProbExp.pick]
    congr! 4
    · ext; simp [ProbExp.ofExp]
    · ext; simp [Iverson.iver, BExpr.probOf, compl]; split_ifs <;> simp


end pGCL
