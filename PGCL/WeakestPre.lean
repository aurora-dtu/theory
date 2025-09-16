import Mathlib.Data.ENNReal.Inv
import Mathlib.Order.FixedPoints
import PGCL.pGCL

namespace pGCL

open OrderHom

variable {ϖ : Type*} [DecidableEq ϖ]

noncomputable def dwp : pGCL ϖ → Exp ϖ →o Exp ϖ
  | pgcl {skip} => ⟨fun X ↦ X, fun ⦃_ _⦄ a ↦ a⟩
  | pgcl {~x := ~A} => ⟨fun X σ ↦ X (σ[x ↦ A σ]), fun ⦃_ _⦄ a i ↦ a _⟩
  | pgcl {~C₁; ~C₂} => ⟨fun X ↦ C₁.dwp (C₂.dwp X), fun a b hab ↦ C₁.dwp.mono (C₂.dwp.mono hab)⟩
  | pgcl {{~C₁} [~p] {~C₂}} =>
    ⟨fun X ↦ p.pick (C₁.dwp X) (C₂.dwp X),
     fun a b hab ↦ by apply ProbExp.pick_le <;> apply (dwp _).mono hab⟩
  | pgcl {{~C₁}[]{~C₂}} => ⟨fun X ↦ C₁.dwp X ⊓ C₂.dwp X, fun a b hab ↦ by simp only; gcongr⟩
  | pgcl {while ~b {~C'}} => ⟨fun X ↦ lfp ⟨
      (b.iver * C'.dwp · + b.not.iver * X),
      fun _ _ _ ↦ by simp; gcongr⟩, fun _ _ _ ↦ by simp; gcongr; intro; simp; gcongr⟩
  | pgcl {tick(~e)} => ⟨(e + ·), fun _ _ h ↦ by simp; gcongr⟩
  | pgcl {assert(~b)} => ⟨(b.iver * ·), fun _ _ h ↦ by simp; gcongr⟩

syntax "dwp⟦" cpgcl_prog "⟧" : term
syntax "dwp[" term "]⟦" cpgcl_prog "⟧" : term

macro_rules
| `(dwp⟦ $p ⟧) => `(pGCL.dwp pgcl {$p})
| `(dwp[$t]⟦ $p ⟧) => `(pGCL.dwp (ϖ:=$t) pgcl {$p})

@[app_unexpander pGCL.dwp]
def dwpUnexpander : Lean.PrettyPrinter.Unexpander
| `($(_) $c) => do
    let c ← match c with | `(pgcl {$c}) => pure c | _ => `(cpgcl_prog| ~ $c)
    `(dwp⟦$c⟧)
| _ => throw ()

noncomputable def dΦ (φ : BExpr ϖ) [DecidablePred φ] (C' : pGCL ϖ) (f : Exp ϖ) : Exp ϖ →o Exp ϖ :=
  ⟨fun X ↦ φ.iver * dwp⟦~C'⟧ X + φ.not.iver * f, by intro _ _ _; simp; gcongr⟩

theorem dwp_loop (φ  : BExpr ϖ) (C' : pGCL ϖ) [DecidablePred φ] :
    dwp⟦while ~φ{~C'}⟧ f = lfp (dΦ φ C' f) := rfl

theorem dwp_fp (φ : BExpr ϖ) [DecidablePred φ] (C' : pGCL ϖ) :
    (dΦ φ C' f) (dwp⟦while ~φ{~C'}⟧ f) = dwp⟦while ~φ{~C'}⟧ f := by simp [dwp_loop]

@[simp] theorem dwp.skip : dwp[ϖ]⟦skip⟧ = ⟨(·), fun ⦃_ _⦄ a ↦ a⟩ := rfl
@[simp] theorem dwp.assign :
    dwp[ϖ]⟦~x := ~A⟧ = ⟨fun X σ ↦ X (σ[x ↦ A σ]), fun _ _ h _ ↦ h _⟩ := rfl
@[simp] theorem dwp.seq : dwp[ϖ]⟦~C₁ ; ~C₂⟧ = OrderHom.comp C₁.dwp C₂.dwp := rfl
@[simp] theorem dwp.prob :
    dwp[ϖ]⟦{~C₁}[~p]{~C₂}⟧ = ⟨fun X ↦ p.pick (C₁.dwp X) (C₂.dwp X), fun _ _ _ ↦ by simp; gcongr⟩
:= rfl
@[simp] theorem dwp.nonDet : dwp[ϖ]⟦{~C₁}[]{~C₂}⟧ = C₁.dwp ⊓ C₂.dwp := rfl
@[simp] theorem dwp.tick : dwp[ϖ]⟦tick(~e)⟧ = ⟨fun X ↦ e + X, fun _ _ _ ↦ by simp; gcongr⟩ := rfl
open scoped Classical in
@[simp] theorem dwp.assert :
    dwp[ϖ]⟦assert(~b)⟧ = ⟨fun X ↦ b.iver * X, fun _ _ _ ↦ by simp; gcongr⟩ := rfl

noncomputable def awp : pGCL ϖ → Exp ϖ →o Exp ϖ
  | pgcl {skip} => ⟨fun X ↦ X, fun ⦃_ _⦄ a ↦ a⟩
  | pgcl {~x := ~A} => ⟨fun X σ ↦ X (σ[x ↦ A σ]), fun ⦃_ _⦄ a i ↦ a _⟩
  | pgcl {~C₁; ~C₂} => ⟨fun X ↦ C₁.awp (C₂.awp X), fun a b hab ↦ C₁.awp.mono (C₂.awp.mono hab)⟩
  | pgcl {{~C₁} [~p] {~C₂}} =>
    ⟨fun X ↦ p.pick (C₁.awp X) (C₂.awp X),
     fun a b hab ↦ by apply ProbExp.pick_le <;> apply (awp _).mono hab⟩
  | pgcl {{~C₁}[]{~C₂}} => ⟨fun X ↦ C₁.awp X ⊔ C₂.awp X, fun a b hab ↦ by simp only; gcongr⟩
  | pgcl {while ~b {~C'}} => ⟨fun X ↦ lfp ⟨
      (b.iver * C'.awp · + b.not.iver * X),
      fun _ _ _ ↦ by simp; gcongr⟩, fun _ _ _ ↦ by simp; gcongr; intro; simp; gcongr⟩
  | pgcl {tick(~e)} => ⟨(e + ·), fun _ _ h ↦ by simp; gcongr⟩
  | pgcl {assert(~b)} => ⟨(b.iver * ·), fun _ _ h ↦ by simp; gcongr⟩

syntax "awp⟦" cpgcl_prog "⟧" : term
syntax "awp[" term "]⟦" cpgcl_prog "⟧" : term

macro_rules
| `(awp⟦ $p ⟧) => `(pGCL.awp pgcl {$p})
| `(awp[$t]⟦ $p ⟧) => `(pGCL.awp (ϖ:=$t) pgcl {$p})

@[app_unexpander pGCL.awp]
def awpUnexpander : Lean.PrettyPrinter.Unexpander
| `($(_) $c) => do
    let c ← match c with | `(pgcl {$c}) => pure c | _ => `(cpgcl_prog| ~ $c)
    `(awp⟦$c⟧)
| _ => throw ()

noncomputable def aΦ (φ : BExpr ϖ) [DecidablePred φ] (C' : pGCL ϖ) (f : Exp ϖ) : Exp ϖ →o Exp ϖ :=
  ⟨fun X ↦ φ.iver * awp⟦~C'⟧ X + φ.not.iver * f, by intro _ _ _; simp; gcongr⟩

theorem awp_loop (φ : BExpr ϖ) [DecidablePred φ] (C' : pGCL ϖ) :
    (C'.loop φ).awp f = lfp (aΦ φ C' f) := rfl

theorem awp_fp (φ : BExpr ϖ) [DecidablePred φ] (C' : pGCL ϖ) :
    (aΦ φ C' f) ((C'.loop φ).awp f) = (C'.loop φ).awp f := by simp [awp_loop]

@[simp] theorem awp.skip : awp[ϖ]⟦skip⟧ = ⟨(·), fun ⦃_ _⦄ a ↦ a⟩ := rfl
@[simp] theorem awp.assign :
    awp[ϖ]⟦~x := ~A⟧ = ⟨fun X σ ↦ X (σ[x ↦ A σ]), fun _ _ h _ ↦ h _⟩ := rfl
@[simp] theorem awp.seq : awp[ϖ]⟦~C₁ ; ~C₂⟧ = OrderHom.comp C₁.awp C₂.awp := rfl
@[simp] theorem awp.prob :
    awp[ϖ]⟦{~C₁}[~p]{~C₂}⟧ = ⟨fun X ↦ p.pick (C₁.awp X) (C₂.awp X), fun _ _ _ ↦ by simp; gcongr⟩
:= rfl
@[simp] theorem awp.nonDet : awp[ϖ]⟦{~C₁}[]{~C₂}⟧ = C₁.awp ⊔ C₂.awp := rfl
@[simp] theorem awp.tick : awp[ϖ]⟦tick(~e)⟧ = ⟨fun X ↦ e + X, fun _ _ _ ↦ by simp; gcongr⟩ := rfl
open scoped Classical in
@[simp] theorem awp.assert :
    awp[ϖ]⟦assert(~b)⟧ = ⟨fun X ↦ b.iver * X, fun _ _ _ ↦ by simp; gcongr⟩ := rfl


end pGCL
