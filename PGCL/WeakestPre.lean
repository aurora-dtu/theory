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

attribute [-simp] ProbExp.pick_of in
noncomputable def wp' : pGCL ϖ → Exp ϖ →o Exp ϖ :=
  have : ∀ (C C' : pGCL ϖ), WellFoundedRelation.rel C C' ↔ sizeOf C < sizeOf C' := by aesop
  have : ∀ (a b : ℕ), a < 1 + a + b := by omega
  WellFounded.fix sizeOfWFRel.wf fun C wp ↦
  ⟨fun X ↦ match C with
  | pgcl {skip} => X
  | pgcl {~x := ~A} => fun σ ↦ X (σ[x ↦ A σ])
  | pgcl {~C₁ ; ~C₂} => wp C₁ (by simp_all) (wp C₂ (by simp_all) X)
  | pgcl {{~C₁} [~p] {~C₂}} => p.pick (wp C₁ (by simp_all) X) (wp C₂ (by simp_all) X)
  | pgcl {{~C₁} [] {~C₂}} => wp C₁ (by simp_all) X ⊓ wp C₂ (by simp_all) X
  | pgcl {while ~b {~C'}} => OrderHom.lfp ⟨
      (b.iver * wp C' (by simp_all) · + b.not.iver * X),
      fun a b hab σ ↦ by simp; gcongr; apply (wp _ _).mono hab⟩
  | pgcl {tick(~e)} => e + X
  | pgcl {assert(~b)} => b.iver * X,
  by
    intro X Y hXY
    simp
    cases C
    · simp; assumption
    · intro σ; simp; apply_assumption
    · intro σ; simp; apply (wp _ _).mono ((wp _ _).mono hXY)
    · simp; apply ProbExp.pick_le <;> apply (wp _ _).mono hXY
    · simp; exact ⟨inf_le_left.trans ((wp _ _).mono hXY), inf_le_right.trans ((wp _ _).mono hXY)⟩
    · simp; gcongr; intro σ; simp; gcongr
    · simp; gcongr
    · simp; gcongr
  ⟩

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
  | .tick e => ⟨fun X ↦ e + X, fun a b hab ↦ by simp; gcongr⟩
  | .assert b => ⟨fun X ↦ b.iver * X, fun a b hab ↦ by simp; gcongr⟩

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

@[simp] theorem wp.skip : wp (ϖ:=ϖ) .skip = ⟨(·), fun ⦃_ _⦄ a ↦ a⟩ := rfl
@[simp] theorem wp.assign :
    wp (ϖ:=ϖ) (.assign x A) = ⟨fun X σ ↦ X (σ[x ↦ A σ]), fun _ _ h _ ↦ h _⟩ := rfl
@[simp] theorem wp.seq : wp (ϖ:=ϖ) (.seq C₁ C₂) = OrderHom.comp C₁.wp C₂.wp := by rw [wp]; simp; rfl
@[simp] theorem wp.prob :
    wp (ϖ:=ϖ) (.prob C₁ p C₂) = ⟨fun X ↦ p.pick (C₁.wp X) (C₂.wp X), fun _ _ _ ↦ by simp; gcongr⟩
:= by rw [wp]; simp
@[simp] theorem wp.nonDet : wp (ϖ:=ϖ) (.nonDet C₁ C₂) = C₁.wp ⊓ C₂.wp := by rw [wp]; simp; rfl
@[simp] theorem wp.tick : wp (ϖ:=ϖ) (.tick e) = ⟨fun X ↦ e + X, fun _ _ _ ↦ by simp; gcongr⟩ := rfl
@[simp] theorem wp.assert :
    wp (ϖ:=ϖ) (.assert b) = ⟨fun X ↦ b.iver * X, fun _ _ _ ↦ by simp; gcongr⟩ := rfl

end pGCL
