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
protected def dwp.lfp {α} [CompleteLattice α] (f : α → α) : α := sInf {a | f a ≤ a}

namespace dwp.lfp

variable [CompleteLattice α]

theorem monotone : Monotone (dwp.lfp (α:=α)) := by
  intro f g h
  simp_all [dwp.lfp]
  intro x h'
  apply sInf_le
  simp [le_trans (h x) h']

@[simp] theorem dwp_lfp_eq_lfp (f : α → α) (h : Monotone f) : dwp.lfp f = OrderHom.lfp ⟨f, h⟩ := rfl
@[simp] theorem dwp_lfp_eq_lfp_OrderHom (f : α →o α) : dwp.lfp f = OrderHom.lfp f := rfl

end dwp.lfp

noncomputable def dwp' : pGCL ϖ → Exp ϖ →o Exp ϖ :=
  have : ∀ (C C' : pGCL ϖ), WellFoundedRelation.rel C C' ↔ sizeOf C < sizeOf C' := by aesop
  have : ∀ (a b : ℕ), a < 1 + a + b := by omega
  WellFounded.fix sizeOfWFRel.wf fun C dwp ↦
  match C with
  | pgcl {skip} => ⟨(·), fun ⦃_ _⦄ h ↦ h⟩
  | pgcl {~x := ~A} => ⟨fun X σ ↦ X (σ[x ↦ A σ]), fun ⦃_ _⦄ h i ↦ h _⟩
  | pgcl {~C₁ ; ~C₂} =>
    ⟨fun X ↦ dwp C₁ (by simp_all) (dwp C₂ (by simp_all) X),
     fun _ _ h ↦ by simp; apply (dwp _ _).mono ((dwp _ _).mono h)⟩
  | pgcl {{~C₁} [~p] {~C₂}} =>
    ⟨fun X ↦ p.pick (dwp C₁ (by simp_all) X) (dwp C₂ (by simp_all) X), fun _ _ h ↦ by simp; gcongr⟩
  | pgcl {{~C₁} [] {~C₂}} =>
    ⟨fun X ↦ dwp C₁ (by simp_all) X ⊓ dwp C₂ (by simp_all) X,
     fun _ _ h ↦ by
      simp; exact ⟨inf_le_left.trans ((dwp _ _).mono h), inf_le_right.trans ((dwp _ _).mono h)⟩⟩
  | pgcl {while ~b {~C'}} =>
    ⟨fun X ↦ OrderHom.lfp
      ⟨(b.iver * dwp C' (by simp_all) · + b.not.iver * X),
       fun a b hab σ ↦ by simp; gcongr; apply (dwp _ _).mono hab⟩,
     fun a b hab ↦ by simp; gcongr; intro; simp only; gcongr⟩
  | pgcl {tick(~e)} => ⟨(e + ·), fun _ _ h ↦ by simp; gcongr⟩
  | pgcl {assert(~b)} => ⟨(b.iver * ·), fun _ _ h ↦ by simp; gcongr⟩

noncomputable def dwp : pGCL ϖ → Exp ϖ →o Exp ϖ
  | .skip => ⟨fun X ↦ X, fun ⦃_ _⦄ a ↦ a⟩
  | .assign x A => ⟨fun X σ ↦ X (σ[x ↦ A σ]), fun ⦃_ _⦄ a i ↦ a _⟩
  | .seq C₁ C₂ => ⟨fun X ↦ C₁.dwp' (C₂.dwp' X), fun a b hab ↦ C₁.dwp'.mono (C₂.dwp'.mono hab)⟩
  | .prob C₁ p C₂ =>
    ⟨fun X ↦ p.pick (C₁.dwp' X) (C₂.dwp' X),
     fun a b hab ↦ by apply ProbExp.pick_le <;> apply (dwp' _).mono hab⟩
  | .nonDet C₁ C₂ =>
    ⟨fun X ↦ C₁.dwp' X ⊓ C₂.dwp' X,
     fun a b hab ↦ by
      simp
      exact ⟨inf_le_left.trans (C₁.dwp'.mono hab), inf_le_right.trans (C₂.dwp'.mono hab)⟩⟩
  | loop b C' => ⟨fun X ↦ OrderHom.lfp ⟨
      (b.iver * C'.dwp' · + b.not.iver * X),
      by intro a b hab; simp; gcongr⟩, fun a b hab ↦ by simp; gcongr; intro; simp; gcongr⟩
  | .tick e => ⟨(e + ·), fun _ _ h ↦ by simp; gcongr⟩
  | assert b => ⟨(b.iver * ·), fun _ _ h ↦ by simp; gcongr⟩

syntax "dwp⟦" cpgcl_prog "⟧" : term
syntax "dwp[" term "]⟦" cpgcl_prog "⟧" : term
syntax "dwp'⟦" cpgcl_prog "⟧" : term
syntax "dwp'[" term "]⟦" cpgcl_prog "⟧" : term

macro_rules
| `(dwp⟦ $p ⟧) => `(pGCL.dwp pgcl {$p})
| `(dwp[$t]⟦ $p ⟧) => `(pGCL.dwp (ϖ:=$t) pgcl {$p})
| `(dwp'⟦ $p ⟧) => `(pGCL.dwp' pgcl {$p})
| `(dwp'[$t]⟦ $p ⟧) => `(pGCL.dwp' (ϖ:=$t) pgcl {$p})

@[app_unexpander pGCL.dwp]
def dwpUnexpander : Lean.PrettyPrinter.Unexpander
| `($(_) $c) => do
    let c := ← match c with | `(pgcl {$c}) => pure c | _ => `(cpgcl_prog| ~ $c)
    `(dwp⟦$c⟧)
| _ => throw ()
@[app_unexpander pGCL.dwp']
def dwp'Unexpander : Lean.PrettyPrinter.Unexpander
| `($(_) $c) => do
    let c := ← match c with | `(pgcl {$c}) => pure c | _ => `(cpgcl_prog| ~ $c)
    `(dwp'⟦$c⟧)
| _ => throw ()

@[simp]
theorem dwp'_eq_wp (C : pGCL ϖ) : C.dwp' = C.dwp := by
  cases C <;> (simp_all [dwp, pGCL.dwp']; rw [WellFounded.fix_eq])

noncomputable def dΦ (φ : BExpr ϖ) [DecidablePred φ] (C' : pGCL ϖ) (f : Exp ϖ) :
    Exp ϖ →o Exp ϖ := ⟨fun X ↦ φ.iver * (C'.dwp X) + φ.not.iver * f, by
      intro X₁ X₂ h σ
      simp
      gcongr
      apply C'.dwp.mono h⟩

theorem dwp_loop (φ  : BExpr ϖ) (C' : pGCL ϖ) [DecidablePred φ] :
    (C'.loop φ).dwp f = OrderHom.lfp (dΦ φ C' f) := by
  rw [dwp]
  simp
  rfl

theorem dwp_fp (φ : BExpr ϖ) [DecidablePred φ] (C' : pGCL ϖ) :
    (dΦ φ C' f) ((C'.loop φ).dwp f) = (C'.loop φ).dwp f := by simp [dwp_loop]

@[simp] theorem dwp.skip : dwp[ϖ]⟦skip⟧ = ⟨(·), fun ⦃_ _⦄ a ↦ a⟩ := rfl
@[simp] theorem dwp.assign :
    dwp[ϖ]⟦~x := ~A⟧ = ⟨fun X σ ↦ X (σ[x ↦ A σ]), fun _ _ h _ ↦ h _⟩ := rfl
@[simp] theorem dwp.seq : dwp[ϖ]⟦~C₁ ; ~C₂⟧ = OrderHom.comp C₁.dwp C₂.dwp := by rw [dwp]; simp; rfl
@[simp] theorem dwp.prob :
    dwp[ϖ]⟦{~C₁}[~p]{~C₂}⟧ = ⟨fun X ↦ p.pick (C₁.dwp X) (C₂.dwp X), fun _ _ _ ↦ by simp; gcongr⟩
:= by rw [dwp]; simp
@[simp] theorem dwp.nonDet : dwp[ϖ]⟦{~C₁}[]{~C₂}⟧ = C₁.dwp ⊓ C₂.dwp := by rw [dwp]; simp; rfl
@[simp] theorem dwp.tick : dwp[ϖ]⟦tick(~e)⟧ = ⟨fun X ↦ e + X, fun _ _ _ ↦ by simp; gcongr⟩ := rfl
open scoped Classical in
@[simp] theorem dwp.assert :
    dwp[ϖ]⟦assert(~b)⟧ = ⟨fun X ↦ b.iver * X, fun _ _ _ ↦ by simp; gcongr⟩ := rfl

open scoped Classical in
noncomputable def awp' : pGCL ϖ → Exp ϖ →o Exp ϖ :=
  have : ∀ (C C' : pGCL ϖ), WellFoundedRelation.rel C C' ↔ sizeOf C < sizeOf C' := by aesop
  have : ∀ (a b : ℕ), a < 1 + a + b := by omega
  WellFounded.fix sizeOfWFRel.wf fun C awp ↦
  match C with
  | pgcl {skip} => ⟨(·), fun ⦃_ _⦄ h ↦ h⟩
  | pgcl {~x := ~A} => ⟨fun X σ ↦ X (σ[x ↦ A σ]), fun ⦃_ _⦄ h i ↦ h _⟩
  | pgcl {~C₁ ; ~C₂} =>
    ⟨fun X ↦ awp C₁ (by simp_all) (awp C₂ (by simp_all) X),
     fun _ _ h ↦ by simp; apply (awp _ _).mono ((awp _ _).mono h)⟩
  | pgcl {{~C₁} [~p] {~C₂}} =>
    ⟨fun X ↦ p.pick (awp C₁ (by simp_all) X) (awp C₂ (by simp_all) X), fun _ _ h ↦ by simp; gcongr⟩
  | pgcl {{~C₁} [] {~C₂}} =>
    ⟨fun X ↦ awp C₁ (by simp_all) X ⊔ awp C₂ (by simp_all) X,
     fun a b h ↦ by
      simp
      constructor
      · have : awp C₁ (by simp_all) a ≤ awp C₁ (by simp_all) b := (awp C₁ (by simp_all)).mono h
        exact le_sup_of_le_left ((awp C₁ _).mono h)
      · have : awp C₂ (by simp_all) a ≤ awp C₂ (by simp_all) b := (awp C₂ (by simp_all)).mono h
        exact le_sup_of_le_right ((awp C₂ _).mono h)⟩
  | pgcl {while ~b {~C'}} =>
    ⟨fun X ↦ OrderHom.lfp
      ⟨(b.iver * awp C' (by simp_all) · + b.not.iver * X),
       fun a b hab σ ↦ by simp; gcongr; apply (awp _ _).mono hab⟩,
     fun a b hab ↦ by simp; gcongr; intro; simp only; gcongr⟩
  | pgcl {tick(~e)} => ⟨(e + ·), fun _ _ h ↦ by simp; gcongr⟩
  | pgcl {assert(~b)} => ⟨(b.iver * ·), fun _ _ h ↦ by simp; gcongr⟩

open scoped Classical in
noncomputable def awp : pGCL ϖ → Exp ϖ →o Exp ϖ
  | .skip => ⟨fun X ↦ X, fun ⦃_ _⦄ a ↦ a⟩
  | .assign x A => ⟨fun X σ ↦ X (σ[x ↦ A σ]), fun ⦃_ _⦄ a i ↦ a _⟩
  | .seq C₁ C₂ => ⟨fun X ↦ C₁.awp' (C₂.awp' X), fun a b hab ↦ C₁.awp'.mono (C₂.awp'.mono hab)⟩
  | .prob C₁ p C₂ =>
    ⟨fun X ↦ p.pick (C₁.awp' X) (C₂.awp' X),
     fun a b hab ↦ by apply ProbExp.pick_le <;> apply (awp' _).mono hab⟩
  | .nonDet C₁ C₂ =>
    ⟨fun X ↦ C₁.awp' X ⊔ C₂.awp' X,
     fun a b hab ↦ by
      simp
      constructor
      · have : C₁.awp' a ≤ C₁.awp' b := C₁.awp'.mono hab
        exact le_sup_of_le_left (C₁.awp'.mono hab)
      · have : C₂.awp' a ≤ C₂.awp' b := C₂.awp'.mono hab
        exact le_sup_of_le_right (C₂.awp'.mono hab)⟩
  | loop b C' => ⟨fun X ↦ OrderHom.lfp ⟨
      (b.iver * C'.awp' · + b.not.iver * X),
      by intro a b hab; simp; gcongr⟩, fun a b hab ↦ by simp; gcongr; intro; simp; gcongr⟩
  | .tick e => ⟨(e + ·), fun _ _ h ↦ by simp; gcongr⟩
  | assert b => ⟨(b.iver * ·), fun _ _ h ↦ by simp; gcongr⟩

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
  cases C <;> (simp_all [awp, pGCL.awp']; rw [WellFounded.fix_eq])

noncomputable def aΦ (φ : BExpr ϖ) [DecidablePred φ] (C' : pGCL ϖ) (f : Exp ϖ) :
    Exp ϖ →o Exp ϖ := ⟨fun X ↦ φ.iver * (C'.awp X) + φ.not.iver * f, by
      intro X₁ X₂ h σ
      simp
      gcongr
      apply C'.awp.mono h⟩

theorem awp_loop (φ : BExpr ϖ) [DecidablePred φ] (C' : pGCL ϖ) :
    (C'.loop φ).awp f = OrderHom.lfp (aΦ φ C' f) := by
  rw [awp]
  simp
  rfl

theorem dop_fp (φ : BExpr ϖ) [DecidablePred φ] (C' : pGCL ϖ) :
    (aΦ φ C' f) ((C'.loop φ).awp f) = (C'.loop φ).awp f := by simp [awp_loop]

@[simp] theorem awp.skip : awp[ϖ]⟦skip⟧ = ⟨(·), fun ⦃_ _⦄ a ↦ a⟩ := rfl
@[simp] theorem awp.assign :
    awp[ϖ]⟦~x := ~A⟧ = ⟨fun X σ ↦ X (σ[x ↦ A σ]), fun _ _ h _ ↦ h _⟩ := rfl
@[simp] theorem awp.seq : awp[ϖ]⟦~C₁ ; ~C₂⟧ = OrderHom.comp C₁.awp C₂.awp := by rw [awp]; simp; rfl
@[simp] theorem awp.prob :
    awp[ϖ]⟦{~C₁}[~p]{~C₂}⟧ = ⟨fun X ↦ p.pick (C₁.awp X) (C₂.awp X), fun _ _ _ ↦ by simp; gcongr⟩
:= by rw [awp]; simp
@[simp] theorem awp.nonDet : awp[ϖ]⟦{~C₁}[]{~C₂}⟧ = C₁.awp ⊔ C₂.awp := by rw [awp]; simp; rfl
@[simp] theorem awp.tick : awp[ϖ]⟦tick(~e)⟧ = ⟨fun X ↦ e + X, fun _ _ _ ↦ by simp; gcongr⟩ := rfl
open scoped Classical in
@[simp] theorem awp.assert :
    awp[ϖ]⟦assert(~b)⟧ = ⟨fun X ↦ b.iver * X, fun _ _ _ ↦ by simp; gcongr⟩ := rfl


end pGCL
