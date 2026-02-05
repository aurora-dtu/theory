import Mathlib.Data.ENNReal.Inv
import Mathlib.Order.FixedPoints
import Mathlib.Tactic.Monotonicity.Basic
import PGCL.pGCL
import MDP.Optimization

open OrderHom OmegaCompletePartialOrder

theorem OrderHom.lfp_ωScottContinuous {α ι : Type*} [CompleteLattice α] [CompleteLattice ι]
    {f : ι →o α →o α} (hf' : ωScottContinuous f) (hf : ∀ i, ωScottContinuous ⇑(f i)) :
    ωScottContinuous fun X ↦ lfp (f X) := by
  refine ωScottContinuous.of_monotone_map_ωSup ?_
  simp [ωSup]
  constructor
  · intro _ _ _; simp only; gcongr
  intro c
  simp [fixedPoints.lfp_eq_sSup_iterate _ (hf _)]
  rw [iSup_comm]
  congr with n
  induction n generalizing c with
  | zero => simp
  | succ n ih =>
    simp_all only [Function.iterate_succ', Function.comp_apply]
    simp [ωScottContinuous_iff_map_ωSup_of_orderHom, ωSup, Chain.map, comp, OrderHom.ωSup] at hf'
    simp only [DFunLike.coe] at hf'
    simp only [toFun_eq_coe, Function.comp_apply, Function.eval] at hf'
    simp [hf']
    simp [ωScottContinuous_iff_map_ωSup_of_orderHom, ωSup, Chain.map] at hf
    replace hf := hf (c:=⟨fun i ↦ (f (c i))^[n] ⊥, fun a b h ↦ by
      suffices (f (c a))^[n] ≤ (f (c b))^[n] by exact this ⊥
      refine Monotone.iterate_le_of_le (f _).mono ?_ n; simp only [coe_le_coe]; gcongr⟩)
    simp only [DFunLike.coe] at hf
    simp at hf
    simp [hf]
    apply iSup_iSup_eq_iSup
    · intro a b hab s; simp; apply f.mono (c.mono hab)
    · intro i a b hab; simp; gcongr
      suffices (f (c a))^[n] ≤ (f (c b))^[n] by exact this ⊥
      refine Monotone.iterate_le_of_le (f _).mono ?_ n; simp only [coe_le_coe]; gcongr

theorem OrderHom.lfp_iSup {α : Type*} [CompleteLattice α] {f : ℕ →o α →o α}
    (hf : ∀ i, ωScottContinuous ⇑(f i)) : lfp (⨆ i, f i) = ⨆ i, lfp (f i) := by
  rw [fixedPoints.lfp_eq_sSup_iterate _ (by simp; exact CompleteLattice.ωScottContinuous.iSup hf)]
  conv => enter [2, 1, i]; rw [fixedPoints.lfp_eq_sSup_iterate _ (hf i)]
  simp
  rw [iSup_comm]
  congr with n
  induction n with
  | zero => simp
  | succ n ih =>
    simp_all only [Function.iterate_succ', Function.comp_apply, _root_.iSup_apply]
    simp [ωScottContinuous_iff_map_ωSup_of_orderHom, ωSup] at hf
    replace hf := fun i' ↦ hf i' ⟨fun i ↦ (⇑(f i))^[n] ⊥, fun a b h ↦ by
      simp
      suffices (⇑(f a))^[n] ≤ (⇑(f b))^[n] by exact this ⊥
      refine Monotone.iterate_le_of_le (f a).mono ?_ n
      simp
      gcongr⟩
    simp only [DFunLike.coe] at hf
    simp at hf
    simp [hf]
    apply iSup_iSup_eq_iSup
    · intro a b hab s; simp; apply f.mono hab
    · intro i a b hab; simp; gcongr;
      suffices (⇑(f a))^[n] ≤ (⇑(f b))^[n] by exact this ⊥
      refine Monotone.iterate_le_of_le (f a).mono ?_ n
      simp
      gcongr

namespace pGCL

open scoped Optimization.Notation

variable {𝒱 : Type*} {ϖ : Γ[𝒱]} [DecidableEq 𝒱]

noncomputable def Φ (g : 𝔼[ϖ, ENNReal] →o 𝔼[ϖ, ENNReal]) (φ : BExpr ϖ) :
    𝔼[ϖ, ENNReal] →o 𝔼[ϖ, ENNReal] →o 𝔼[ϖ, ENNReal] :=
  ⟨fun f ↦ ⟨fun X ↦ i[φ] * g X + i[φᶜ] * f, by intro _ _ _; simp; gcongr⟩,
    by intro _ _ _ _; simp; gcongr⟩

notation "Φ[" g "]" => Φ g

omit [DecidableEq 𝒱] in
theorem Φ_eq_pick :
    Φ[g] φ f = ⟨fun (X : 𝔼[ϖ, ENNReal]) ↦ p[φ].pick (g X) f, fun _ _ _ ↦ by simp; gcongr⟩ := by
  ext X σ
  simp only [Φ, coe_mk, mk_apply, Pi.add_apply, Pi.mul_apply, Pi.iver_apply, Pi.compl_apply,
    compl_iff_not, Iverson.iver_neg, ENNReal.natCast_sub, Nat.cast_one, ProbExp.pick,
    BExpr.probOf_apply, Pi.sub_apply, Pi.ofNat_apply]

omit [DecidableEq 𝒱] in
theorem Φ_eq_pick_apply {X : 𝔼[ϖ, ENNReal]} : Φ[g] φ f X = p[φ].pick (g X) f := by
  simp [Φ_eq_pick]

noncomputable def wp (O : Optimization) : pGCL ϖ → 𝔼[ϖ, ENNReal] →o 𝔼[ϖ, ENNReal]
  | pgcl {skip} => ⟨fun X ↦ X, fun ⦃_ _⦄ a ↦ a⟩
  | pgcl {~x := ~A} => ⟨fun X ↦ X[x ↦ A], fun ⦃_ _⦄ a j ↦ by exact a _⟩
  | pgcl {~C₁; ~C₂} => ⟨fun X ↦ C₁.wp O (C₂.wp O X), fun a b h ↦ (C₁.wp _).mono ((C₂.wp _).mono h)⟩
  | pgcl {{~C₁} [~p] {~C₂}} =>
    ⟨fun X ↦ p.pick (C₁.wp O X) (C₂.wp O X),
     fun a b hab ↦ by apply ProbExp.pick_le <;> apply (wp O _).mono hab⟩
  | pgcl {{~C₁}[]{~C₂}} =>
    ⟨O.opt₂ (C₁.wp O) (C₂.wp O), fun a b hab ↦ by simp only [Optimization.opt₂_apply]; gcongr⟩
  | pgcl {while ~b {~C'}} => ⟨fun X ↦ lfp (Φ[wp O C'] b X), fun _ _ _ ↦ by simp; gcongr⟩
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

variable {O : Optimization}

theorem wp_loop (φ  : BExpr ϖ) (C' : pGCL ϖ) :
    wp[O]⟦while ~φ{~C'}⟧ f = lfp (Φ[wp[O]⟦~C'⟧] φ f) := rfl

theorem wp_fp (φ : BExpr ϖ) (C' : pGCL ϖ) :
    (Φ[wp[O]⟦~C'⟧] φ f) (wp[O]⟦while ~φ{~C'}⟧ f) = wp[O]⟦while ~φ{~C'}⟧ f := by simp [wp_loop]

variable {x : 𝒱} {e : 𝔼[ϖ, ENNReal]} {b : BExpr ϖ} {C₁ : pGCL ϖ}

section

variable {X : 𝔼[ϖ, ENNReal]}

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
@[simp] theorem wp.observe_apply :
    wp[O]⟦observe(~b)⟧ X = i[b] * X := rfl

end

@[gcongr]
theorem wp_le_wp {C : pGCL ϖ} {a b : 𝔼[ϖ, ENNReal]} (h : a ≤ b) : wp[O]⟦~C⟧ a σ ≤ wp[O]⟦~C⟧ b σ :=
  (wp _ _).mono h σ

noncomputable abbrev dwp : pGCL ϖ → 𝔼[ϖ, ENNReal] →o 𝔼[ϖ, ENNReal] := wp 𝒟
noncomputable abbrev awp : pGCL ϖ → 𝔼[ϖ, ENNReal] →o 𝔼[ϖ, ENNReal] := wp 𝒜

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

def Φ.continuous {g : 𝔼[ϖ, ENNReal] →o 𝔼[ϖ, ENNReal]} (ih : ωScottContinuous g) :
    ωScottContinuous ⇑(Φ[g] b X) := by
  simp [ωScottContinuous_iff_map_ωSup_of_orderHom] at ih ⊢
  intro c
  simp [Φ, ωSup] at ih ⊢
  ext σ
  simp [ih, ENNReal.mul_iSup, ENNReal.iSup_add]

def Φ.continuous' {g : 𝔼[ϖ, ENNReal] →o 𝔼[ϖ, ENNReal]} : ωScottContinuous ⇑(Φ[g] b) := by
  refine ωScottContinuous.of_map_ωSup_of_orderHom ?_
  intro c
  ext X σ
  simp only [Φ, ωSup, Chain.map_coe, Pi.evalOrderHom_coe, Function.comp_apply, Function.eval,
    coe_mk, mk_apply, Pi.add_apply, Pi.mul_apply, Pi.iver_apply, Pi.compl_apply, compl_iff_not,
    ENNReal.mul_iSup, ENNReal.add_iSup, OrderHom.ωSup, apply_coe]
omit [DecidableEq 𝒱] in
theorem Φ_iSup {g : 𝔼[ϖ, ENNReal] →o 𝔼[ϖ, ENNReal]} (f : ℕ → 𝔼[ϖ, ENNReal]) :
    Φ[g] b (⨆ i, f i) = ⨆ i, Φ[g] b (f i) := by
  ext X σ
  simp [Φ, ENNReal.mul_iSup, ENNReal.add_iSup]
omit [DecidableEq 𝒱] in
theorem Φ_iSup' {g : 𝔼[ϖ, ENNReal] →o 𝔼[ϖ, ENNReal]} (f : ℕ → 𝔼[ϖ, ENNReal]) :
    Φ[g] b (fun a ↦ ⨆ i, f i a) = ⨆ i, Φ[g] b (f i) := by
  ext X σ
  simp [Φ, ENNReal.mul_iSup, ENNReal.add_iSup]

omit [DecidableEq 𝒱] in
theorem ωScottContinuous_dual_iff {f : 𝔼[ϖ, ENNReal] →o 𝔼[ϖ, ENNReal]} :
      ωScottContinuous f.dual ↔ (∀ (c : Chain (𝔼[ϖ, ENNReal])ᵒᵈ), f (⨅ i, c i) = ⨅ i, f (c i)) := by
  simp [ωScottContinuous_iff_map_ωSup_of_orderHom, ωSup]; rfl

omit [DecidableEq 𝒱] in
theorem ωScottContinuous_dual_iff' {α ι : Type*} [CompleteLattice α] {f : (ι → α) →o (ι → α)} :
    ωScottContinuous f.dual ↔ (∀ (c : ℕ → (ι → α)), Antitone c → f (⨅ i, c i) = ⨅ i, f (c i)) := by
  simp [ωScottContinuous_iff_map_ωSup_of_orderHom, ωSup]
  constructor
  · intro h c hc; exact h ⟨c, hc⟩
  · intro h c; exact h c c.mono

def Φ.cocontinuous {g : 𝔼[ϖ, ENNReal] →o 𝔼[ϖ, ENNReal]} (ih : ωScottContinuous g.dual) :
    ωScottContinuous (Φ[g] b X).dual := by
  simp [ωScottContinuous_dual_iff] at ih ⊢
  intro c
  simp [Φ] at ih ⊢
  ext σ
  simp only [ih, Pi.add_apply, Pi.mul_apply, Pi.iver_apply, _root_.iInf_apply,
    ENNReal.natCast_ne_top, IsEmpty.forall_iff, ENNReal.mul_iInf, Pi.compl_apply, compl_iff_not,
    ENNReal.iInf_add]

@[simp]
def wp.continuous (C : pGCL ϖ) : ωScottContinuous (C.wp O) := by
  induction C with
  | skip => exact ωScottContinuous_iff_map_ωSup_of_orderHom.mpr (congrFun rfl)
  | assign => exact ωScottContinuous_iff_map_ωSup_of_orderHom.mpr (congrFun rfl)
  | seq C₁ C₂ ih₁ ih₂ => simp only [wp, coe_mk]; exact ωScottContinuous.comp ih₁ ih₂
  | nonDet C₁ C₂ ih₁ ih₂ => exact O.opt₂_ωScottContinuous ih₁ ih₂
  | prob C₁ p C₂ ih₁ ih₂ => exact p.pick_ωScottContinuous ih₁ ih₂
  | loop b C' ih => apply OrderHom.lfp_ωScottContinuous Φ.continuous' (fun _ ↦ Φ.continuous ih)
  | tick => simp [ωScottContinuous_iff_map_ωSup_of_orderHom, ωSup, funext_iff, ENNReal.add_iSup]
  | observe => simp [ωScottContinuous_iff_map_ωSup_of_orderHom, ωSup, funext_iff, ENNReal.mul_iSup]

@[simp]
def Φ.wp_continuous {C' : pGCL ϖ} : ωScottContinuous ⇑(Φ[wp[O]⟦~C'⟧] b X) :=
  continuous (wp.continuous C')

theorem wp_loop_eq_iter (φ  : BExpr ϖ) (C' : pGCL ϖ) :
    wp[O]⟦while ~φ{~C'}⟧ f = ⨆ n, (Φ[wp[O]⟦~C'⟧] φ f)^[n] 0 := by
  rw [wp_loop, fixedPoints.lfp_eq_sSup_iterate _ Φ.wp_continuous]
  rfl

theorem wp_le_one (C : pGCL ϖ) (X : 𝔼[ϖ, ENNReal]) (hX : X ≤ 1) : wp[O]⟦~C.st⟧ X ≤ 1 := by
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
    simp [st]; intro σ; specialize hX σ; apply le_trans _ hX; simp
  | loop b C' ih =>
    simp [st]
    apply lfp_le
    intro σ
    simp_all only [Φ, coe_mk, mk_apply, Pi.add_apply, Pi.mul_apply, Pi.iver_apply, Pi.compl_apply,
      compl_iff_not, Pi.one_apply]
    if b σ then
      simp_all
      apply ih _ (by rfl)
    else
      simp_all
      apply hX

end pGCL
