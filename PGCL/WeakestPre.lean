import Mathlib.Data.ENNReal.Inv
import Mathlib.Order.FixedPoints
import PGCL.pGCL
import MDP.Optimization

namespace pGCL

open OrderHom
open scoped Optimization.Notation

variable {ϖ : Type*} [DecidableEq ϖ]

noncomputable def wp (O : Optimization) : pGCL ϖ → Exp ϖ →o Exp ϖ
  | pgcl {skip} => ⟨fun X ↦ X, fun ⦃_ _⦄ a ↦ a⟩
  | pgcl {~x := ~A} => ⟨fun X σ ↦ X (σ[x ↦ A σ]), fun ⦃_ _⦄ a i ↦ a _⟩
  | pgcl {~C₁; ~C₂} => ⟨fun X ↦ C₁.wp O (C₂.wp O X), fun a b h ↦ (C₁.wp _).mono ((C₂.wp _).mono h)⟩
  | pgcl {{~C₁} [~p] {~C₂}} =>
    ⟨fun X ↦ p.pick (C₁.wp O X) (C₂.wp O X),
     fun a b hab ↦ by apply ProbExp.pick_le <;> apply (wp O _).mono hab⟩
  | pgcl {{~C₁}[]{~C₂}} =>
    ⟨O.opt₂ (C₁.wp O) (C₂.wp O), fun a b hab ↦ by simp only [Optimization.opt₂_apply]; gcongr⟩
  | pgcl {while ~b {~C'}} => ⟨fun X ↦ lfp ⟨
      (b.iver * C'.wp O · + b.not.iver * X),
      fun _ _ _ ↦ by simp; gcongr⟩, fun _ _ _ ↦ by simp; gcongr; intro; simp; gcongr⟩
  | pgcl {tick(~e)} => ⟨(e + ·), fun _ _ h ↦ by simp; gcongr⟩
  | pgcl {assert(~b)} => ⟨(b.iver * ·), fun _ _ h ↦ by simp; gcongr⟩

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
  ⟨fun X ↦ φ.iver * wp[O]⟦~C'⟧ X + φ.not.iver * f, by intro _ _ _; simp; gcongr⟩

variable {O : Optimization}

theorem wp_loop (φ  : BExpr ϖ) (C' : pGCL ϖ) [DecidablePred φ] :
    wp[O]⟦while ~φ{~C'}⟧ f = lfp (Φ O φ C' f) := rfl

theorem wp_fp (φ : BExpr ϖ) [DecidablePred φ] (C' : pGCL ϖ) :
    (Φ O φ C' f) (wp[O]⟦while ~φ{~C'}⟧ f) = wp[O]⟦while ~φ{~C'}⟧ f := by simp [wp_loop]

variable {x : ϖ} {e : Exp ϖ} {b : BExpr ϖ} {C₁ : pGCL ϖ}

@[simp] theorem wp.skip : wp[O]⟦skip⟧ = ⟨(·), fun (_ _ : Exp ϖ) a ↦ a⟩ := rfl
@[simp] theorem wp.assign :
    wp[O]⟦~x := ~A⟧ = ⟨fun X σ ↦ X (σ[x ↦ A σ]), fun _ _ h _ ↦ h _⟩ := rfl
@[simp] theorem wp.seq : wp[O]⟦~C₁ ; ~C₂⟧ = OrderHom.comp (C₁.wp O) (C₂.wp O) := rfl
@[simp] theorem wp.prob :
    wp[O]⟦{~C₁}[~p]{~C₂}⟧ = ⟨fun X ↦ p.pick (C₁.wp O X) (C₂.wp O X), fun _ _ _ ↦ by simp; gcongr⟩
:= rfl
@[simp] theorem wp.nonDet : wp[O]⟦{~C₁}[]{~C₂}⟧ = O.opt₂ (C₁.wp O) (C₂.wp O) := by ext; simp [wp]
@[simp] theorem wp.tick : wp[O]⟦tick(~e)⟧ = ⟨fun X ↦ e + X, fun _ _ _ ↦ by simp; gcongr⟩ := rfl
open scoped Classical in
@[simp] theorem wp.assert :
    wp[O]⟦assert(~b)⟧ = ⟨fun X ↦ b.iver * X, fun _ _ _ ↦ by simp; gcongr⟩ := rfl

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

end pGCL
