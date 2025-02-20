import Mathlib.Order.FixedPoints
import PGCL.pGCL

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

noncomputable def wp (C : pGCL ϖ) (X : Exp ϖ) : Exp ϖ := match C with
  | .skip => X
  | .assign x A => fun σ ↦ X (σ[x ↦ A σ])
  | .seq C₁ C₂ => C₁.wp (C₂.wp X)
  | .prob C₁ p C₂ => p.pick (C₁.wp X) (C₂.wp X)
  | .nonDet C₁ C₂ => C₁.wp X ⊓ C₂.wp X
  | .loop b C' => wp.lfp (b.probOf * C'.wp · + b.not.probOf * X)
  | .tick e => e + X

@[simp] theorem wp.skip : wp (ϖ:=ϖ) .skip = (·) := rfl
@[simp] theorem wp.assign : wp (ϖ:=ϖ) (.assign x A) = fun X σ ↦ X (σ[x ↦ A σ]) := rfl
@[simp] theorem wp.seq : wp (ϖ:=ϖ) (.seq C₁ C₂) = C₁.wp ∘ C₂.wp := rfl
@[simp] theorem wp.prob : wp (ϖ:=ϖ) (.prob C₁ p C₂) = fun X ↦ p.pick (C₁.wp X) (C₂.wp X) := rfl
@[simp] theorem wp.nonDet : wp (ϖ:=ϖ) (.nonDet C₁ C₂) = C₁.wp ⊓ C₂.wp := rfl
@[simp] theorem wp.tick : wp (ϖ:=ϖ) (.tick e) = fun X ↦ e + X := rfl

@[simp] theorem wp.monotone (C : pGCL ϖ) : Monotone (C.wp) := by
  intro X₁ X₂ h
  induction C generalizing X₁ X₂ with simp_all [wp]
  | assign x e => intro σ; exact h _
  | nonDet C₁ C₂ ih₁ ih₂ => simp [inf_le_of_left_le (ih₁ h), inf_le_of_right_le (ih₂ h)]
  | loop b C' => exact lfp.monotone fun Y σ ↦ by by_cases h' : b σ <;> simp_all [h σ]
  | tick e => apply add_le_add_left h

noncomputable def wp_loop_f (b : BExpr ϖ) (C' : pGCL ϖ) (X : Exp ϖ) : Exp ϖ →o Exp ϖ :=
  ⟨fun Y ↦ b.probOf * C'.wp Y + b.not.probOf * X,
   fun _ _ h σ ↦ by simp [add_le_add, mul_le_mul, wp.monotone C' h σ]⟩
theorem wp_loop : (loop (ϖ:=ϖ) b C').wp = fun X ↦ OrderHom.lfp (C'.wp_loop_f b X) := rfl

theorem wp_loop_fp (b : BExpr ϖ) (C : pGCL ϖ) :
  (pGCL.loop b C).wp = fun X ↦ b.probOf * (C ;; .loop b C).wp X + b.not.probOf * X
:= by
  ext
  simp only [wp_loop, wp_loop_f, Pi.add_apply, Pi.mul_apply]
  rw [← OrderHom.map_lfp]
  rfl

end pGCL
