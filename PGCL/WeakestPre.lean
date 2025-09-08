import Mathlib.Data.ENNReal.Inv
import Mathlib.Order.FixedPoints
import PGCL.pGCL

section
variable {α : Type*} [CompleteLattice α]

theorem OrderHom.lfp_monotone : Monotone (OrderHom.lfp (α:=α)) := by
  intro f g h
  simp_all [lfp]
  intro x h'
  apply sInf_le
  simp
  exact le_trans (h x) h'

theorem OrderHom.lfp_apply_le {ι : Type*} (f g : (ι → α) →o (ι → α)) (h : f ≤ g) (a : ι) :
    OrderHom.lfp f a ≤ OrderHom.lfp g a := by
  simp_all [lfp]
  intro x h'
  apply sInf_le
  simp
  use x
  simp
  exact le_trans (h x) h'

end

namespace pGCL

variable {ϖ : Type*} [DecidableEq ϖ]

/-- A version of `OrderHom.lfp` that does not require `f` the `Monotone` upfront. -/
protected def wp.lfp {α} [CompleteLattice α] (f : α → α) : α := sInf {a | f a ≤ a}

namespace wp.lfp

variable [CompleteLattice α]

theorem monotone : Monotone (wp.lfp (α:=α)) := by
  intro f g h
  simp_all [wp.lfp]
  intro x h'
  apply sInf_le
  simp [le_trans (h x) h']

@[simp] theorem wp_lfp_eq_lfp (f : α → α) (h : Monotone f) : wp.lfp f = OrderHom.lfp ⟨f, h⟩ := rfl
@[simp] theorem wp_lfp_eq_lfp_OrderHom (f : α →o α) : wp.lfp f = OrderHom.lfp f := rfl

end wp.lfp

noncomputable def wp' : pGCL ϖ → Exp ϖ →o Exp ϖ :=
  have : ∀ (C C' : pGCL ϖ), WellFoundedRelation.rel C C' ↔ sizeOf C < sizeOf C' := by aesop
  have : ∀ (a b : ℕ), a < 1 + a + b := by omega
  WellFounded.fix sizeOfWFRel.wf fun C wp ↦
  match C with
  | pgcl {skip} => ⟨(·), fun ⦃_ _⦄ h ↦ h⟩
  | pgcl {~x := ~A} => ⟨fun X σ ↦ X (σ[x ↦ A σ]), fun ⦃_ _⦄ h i ↦ h _⟩
  | pgcl {~C₁ ; ~C₂} =>
    ⟨fun X ↦ wp C₁ (by simp_all) (wp C₂ (by simp_all) X),
     fun _ _ h ↦ by simp; apply (wp _ _).mono ((wp _ _).mono h)⟩
  | pgcl {{~C₁} [~p] {~C₂}} =>
    ⟨fun X ↦ p.pick (wp C₁ (by simp_all) X) (wp C₂ (by simp_all) X), fun _ _ h ↦ by simp; gcongr⟩
  | pgcl {{~C₁} [] {~C₂}} =>
    ⟨fun X ↦ wp C₁ (by simp_all) X ⊓ wp C₂ (by simp_all) X,
     fun _ _ h ↦ by
      simp; exact ⟨inf_le_left.trans ((wp _ _).mono h), inf_le_right.trans ((wp _ _).mono h)⟩⟩
  | pgcl {while ~b {~C'}} =>
    ⟨fun X ↦ OrderHom.lfp
      ⟨(b.iver * wp C' (by simp_all) · + b.not.iver * X),
       fun a b hab σ ↦ by simp; gcongr; apply (wp _ _).mono hab⟩,
     fun a b hab ↦ by simp; gcongr; intro; simp only; gcongr⟩
  | pgcl {tick(~e)} => ⟨(e + ·), fun _ _ h ↦ by simp; gcongr⟩
  | pgcl {assert(~b)} => ⟨(b.iver * ·), fun _ _ h ↦ by simp; gcongr⟩

noncomputable def wp : pGCL ϖ → Exp ϖ →o Exp ϖ
  | .skip => ⟨fun X ↦ X, fun ⦃_ _⦄ a ↦ a⟩
  | .assign x A => ⟨fun X σ ↦ X (σ[x ↦ A σ]), fun ⦃_ _⦄ a i ↦ a _⟩
  | .seq C₁ C₂ => ⟨fun X ↦ C₁.wp' (C₂.wp' X), fun a b hab ↦ C₁.wp'.mono (C₂.wp'.mono hab)⟩
  | .prob C₁ p C₂ =>
    ⟨fun X ↦ p.pick (C₁.wp' X) (C₂.wp' X),
     fun a b hab ↦ by apply ProbExp.pick_le <;> apply (wp' _).mono hab⟩
  | .nonDet C₁ C₂ =>
    ⟨fun X ↦ C₁.wp' X ⊓ C₂.wp' X,
     fun a b hab ↦ by
      simp
      exact ⟨inf_le_left.trans (C₁.wp'.mono hab), inf_le_right.trans (C₂.wp'.mono hab)⟩⟩
  | .loop b C' => ⟨fun X ↦ OrderHom.lfp ⟨
      (b.iver * C'.wp' · + b.not.iver * X),
      by intro a b hab; simp; gcongr⟩, fun a b hab ↦ by simp; gcongr; intro; simp; gcongr⟩
  | .tick e => ⟨(e + ·), fun _ _ h ↦ by simp; gcongr⟩
  | .assert b => ⟨(b.iver * ·), fun _ _ h ↦ by simp; gcongr⟩

syntax "wp⟦" cpgcl_prog "⟧" : term
syntax "wp[" term "]⟦" cpgcl_prog "⟧" : term
syntax "wp'⟦" cpgcl_prog "⟧" : term
syntax "wp'[" term "]⟦" cpgcl_prog "⟧" : term

macro_rules
| `(wp⟦ $p ⟧) => `(pGCL.wp pgcl {$p})
| `(wp[$t]⟦ $p ⟧) => `(pGCL.wp (ϖ:=$t) pgcl {$p})
| `(wp'⟦ $p ⟧) => `(pGCL.wp' pgcl {$p})
| `(wp'[$t]⟦ $p ⟧) => `(pGCL.wp' (ϖ:=$t) pgcl {$p})

@[app_unexpander pGCL.wp]
def wpUnexpander : Lean.PrettyPrinter.Unexpander
| `($(_) $c) => do
    let c := ← match c with | `(pgcl {$c}) => pure c | _ => `(cpgcl_prog| ~ $c)
    `(wp⟦$c⟧)
| _ => throw ()
@[app_unexpander pGCL.wp']
def wp'Unexpander : Lean.PrettyPrinter.Unexpander
| `($(_) $c) => do
    let c := ← match c with | `(pgcl {$c}) => pure c | _ => `(cpgcl_prog| ~ $c)
    `(wp'⟦$c⟧)
| _ => throw ()

@[simp]
theorem wp'_eq_wp (C : pGCL ϖ) : C.wp' = C.wp := by
  cases C <;> (simp_all [wp, pGCL.wp']; rw [WellFounded.fix_eq])

noncomputable def Φ (φ : BExpr ϖ) (C' : pGCL ϖ) (f : Exp ϖ) :
    Exp ϖ →o Exp ϖ := ⟨fun X ↦ φ.iver * (C'.wp X) + φ.not.iver * f, by
      intro X₁ X₂ h σ
      simp
      gcongr
      apply C'.wp.mono h⟩

theorem wp_loop (C' : pGCL ϖ) :
    (C'.loop φ).wp f = OrderHom.lfp (Φ φ C' f) := by
  rw [wp]
  simp
  rfl

theorem wp_fp (C' : pGCL ϖ) :
    (Φ φ C' f) ((C'.loop φ).wp f) = (C'.loop φ).wp f := by simp [wp_loop]

@[simp] theorem wp.skip : wp[ϖ]⟦skip⟧ = ⟨(·), fun ⦃_ _⦄ a ↦ a⟩ := rfl
@[simp] theorem wp.assign :
    wp[ϖ]⟦~x := ~A⟧ = ⟨fun X σ ↦ X (σ[x ↦ A σ]), fun _ _ h _ ↦ h _⟩ := rfl
@[simp] theorem wp.seq : wp[ϖ]⟦~C₁ ; ~C₂⟧ = OrderHom.comp C₁.wp C₂.wp := by rw [wp]; simp; rfl
@[simp] theorem wp.prob :
    wp[ϖ]⟦{~C₁}[~p]{~C₂}⟧ = ⟨fun X ↦ p.pick (C₁.wp X) (C₂.wp X), fun _ _ _ ↦ by simp; gcongr⟩
:= by rw [wp]; simp
@[simp] theorem wp.nonDet : wp[ϖ]⟦{~C₁}[]{~C₂}⟧ = C₁.wp ⊓ C₂.wp := by rw [wp]; simp; rfl
@[simp] theorem wp.tick : wp[ϖ]⟦tick(~e)⟧ = ⟨fun X ↦ e + X, fun _ _ _ ↦ by simp; gcongr⟩ := rfl
@[simp] theorem wp.assert :
    wp[ϖ]⟦assert(~b)⟧ = ⟨fun X ↦ b.iver * X, fun _ _ _ ↦ by simp; gcongr⟩ := rfl

noncomputable def awp' : pGCL ϖ → Exp ϖ →o Exp ϖ :=
  have : ∀ (C C' : pGCL ϖ), WellFoundedRelation.rel C C' ↔ sizeOf C < sizeOf C' := by aesop
  have : ∀ (a b : ℕ), a < 1 + a + b := by omega
  WellFounded.fix sizeOfWFRel.wf fun C wp ↦
  match C with
  | pgcl {skip} => ⟨(·), fun ⦃_ _⦄ h ↦ h⟩
  | pgcl {~x := ~A} => ⟨fun X σ ↦ X (σ[x ↦ A σ]), fun ⦃_ _⦄ h i ↦ h _⟩
  | pgcl {~C₁ ; ~C₂} =>
    ⟨fun X ↦ wp C₁ (by simp_all) (wp C₂ (by simp_all) X),
     fun _ _ h ↦ by simp; apply (wp _ _).mono ((wp _ _).mono h)⟩
  | pgcl {{~C₁} [~p] {~C₂}} =>
    ⟨fun X ↦ p.pick (wp C₁ (by simp_all) X) (wp C₂ (by simp_all) X), fun _ _ h ↦ by simp; gcongr⟩
  | pgcl {{~C₁} [] {~C₂}} =>
    ⟨fun X ↦ wp C₁ (by simp_all) X ⊔ wp C₂ (by simp_all) X,
     fun _ _ h ↦ by
      sorry
      -- simp; exact ⟨le_sup_left.trans ((wp _ _).mono h), le_sup_right.trans ((wp _ _).mono h)⟩
      ⟩
  | pgcl {while ~b {~C'}} =>
    ⟨fun X ↦ OrderHom.lfp
      ⟨(b.iver * wp C' (by simp_all) · + b.not.iver * X),
       fun a b hab σ ↦ by simp; gcongr; apply (wp _ _).mono hab⟩,
     fun a b hab ↦ by simp; gcongr; intro; simp only; gcongr⟩
  | pgcl {tick(~e)} => ⟨(e + ·), fun _ _ h ↦ by simp; gcongr⟩
  | pgcl {assert(~b)} => ⟨(b.iver * ·), fun _ _ h ↦ by simp; gcongr⟩

noncomputable def awp : pGCL ϖ → Exp ϖ →o Exp ϖ
  | .skip => ⟨fun X ↦ X, fun ⦃_ _⦄ a ↦ a⟩
  | .assign x A => ⟨fun X σ ↦ X (σ[x ↦ A σ]), fun ⦃_ _⦄ a i ↦ a _⟩
  | .seq C₁ C₂ => ⟨fun X ↦ C₁.wp' (C₂.wp' X), fun a b hab ↦ C₁.wp'.mono (C₂.wp'.mono hab)⟩
  | .prob C₁ p C₂ =>
    ⟨fun X ↦ p.pick (C₁.wp' X) (C₂.wp' X),
     fun a b hab ↦ by apply ProbExp.pick_le <;> apply (wp' _).mono hab⟩
  | .nonDet C₁ C₂ =>
    ⟨fun X ↦ C₁.wp' X ⊔ C₂.wp' X,
     fun a b hab ↦ by
      simp
      -- exact ⟨inf_le_left.trans (C₁.wp'.mono hab), inf_le_right.trans (C₂.wp'.mono hab)⟩
      sorry⟩
  | .loop b C' => ⟨fun X ↦ OrderHom.lfp ⟨
      (b.iver * C'.wp' · + b.not.iver * X),
      by intro a b hab; simp; gcongr⟩, fun a b hab ↦ by simp; gcongr; intro; simp; gcongr⟩
  | .tick e => ⟨(e + ·), fun _ _ h ↦ by simp; gcongr⟩
  | .assert b => ⟨(b.iver * ·), fun _ _ h ↦ by simp; gcongr⟩

syntax "awp⟦" cpgcl_prog "⟧" : term
syntax "awp[" term "]⟦" cpgcl_prog "⟧" : term
syntax "awp'⟦" cpgcl_prog "⟧" : term
syntax "awp'[" term "]⟦" cpgcl_prog "⟧" : term

macro_rules
| `(awp⟦ $p ⟧) => `(pGCL.awp pgcl {$p})
| `(awp[$t]⟦ $p ⟧) => `(pGCL.awp (ϖ:=$t) pgcl {$p})
| `(awp'⟦ $p ⟧) => `(pGCL.awp' pgcl {$p})
| `(awp'[$t]⟦ $p ⟧) => `(pGCL.awp' (ϖ:=$t) pgcl {$p})

@[app_unexpander pGCL.awp]
def awpUnexpander : Lean.PrettyPrinter.Unexpander
| `($(_) $c) => do
    let c := ← match c with | `(pgcl {$c}) => pure c | _ => `(cpgcl_prog| ~ $c)
    `(awp⟦$c⟧)
| _ => throw ()
@[app_unexpander pGCL.awp']
def awp'Unexpander : Lean.PrettyPrinter.Unexpander
| `($(_) $c) => do
    let c := ← match c with | `(pgcl {$c}) => pure c | _ => `(cpgcl_prog| ~ $c)
    `(awp'⟦$c⟧)
| _ => throw ()

@[simp]
theorem awp'_eq_awp (C : pGCL ϖ) : C.awp' = C.awp := by
  sorry
  -- cases C <;> (simp_all [awp, pGCL.awp']; rw [WellFounded.fix_eq])


end pGCL
