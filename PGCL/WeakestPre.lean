import Mathlib.Order.FixedPoints
import Mathlib.Tactic.Use
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Instances.Rat
import PGCL.Exp
import PGCL.pGCL

namespace pGCL

variable {ϖ : Type*}
variable [DecidableEq ϖ]

def lfp {α} [CompleteLattice α] (f : α → α) : α := sInf {a | f a ≤ a}

namespace lfp

variable [CompleteLattice α]

theorem monotone : Monotone (lfp (α:=α)) := by
  intro f g h
  simp_all [lfp]
  intro x h'
  apply sInf_le
  simp [le_trans (h x) h']

@[simp] theorem eq_OrderHom_lfp (f : α → α) (h : Monotone f) : lfp f = OrderHom.lfp ⟨f, h⟩ := rfl
@[simp] theorem eq_OrderHom_lfp' (f : α →o α) : lfp f = OrderHom.lfp f := rfl

end lfp

noncomputable def dwp (C : pGCL ϖ) (X : Exp ϖ) : Exp ϖ := match C with
  | .skip => X
  | .assign x A => fun σ ↦ X (σ[x ↦ A σ])
  | .seq C₁ C₂ => C₁.dwp (C₂.dwp X)
  | .prob C₁ p C₂ => p.pick (C₁.dwp X) (C₂.dwp X)
  | .nonDet C₁ C₂ => C₁.dwp X ⊓ C₂.dwp X
  | .loop B C' => lfp (B.probOf * C'.dwp · + B.not.probOf * X)
  | .tick e => e + X

@[simp] theorem dwp.skip : dwp (ϖ:=ϖ) skip = (·) := rfl
@[simp] theorem dwp.assign : dwp (ϖ:=ϖ) (assign x A) = fun X σ ↦ X (σ[x ↦ A σ]) := rfl
@[simp] theorem dwp.seq : dwp (ϖ:=ϖ) (seq C₁ C₂) = C₁.dwp ∘ C₂.dwp := rfl
@[simp] theorem dwp.prob : dwp (ϖ:=ϖ) (prob C₁ p C₂) = fun X ↦ p.pick (C₁.dwp X) (C₂.dwp X) := rfl
@[simp] theorem dwp.nonDet : dwp (ϖ:=ϖ) (nonDet C₁ C₂) = C₁.dwp ⊓ C₂.dwp := rfl
@[simp] theorem dwp.tick : dwp (ϖ:=ϖ) (tick e) = fun X ↦ e + X := rfl

@[simp] theorem dwp.monotone (C : pGCL ϖ) : Monotone (C.dwp) := by
  intro X₁ X₂ h
  induction C generalizing X₁ X₂ with simp_all [dwp]
  | assign x e => intro σ; exact h _
  | nonDet C₁ C₂ ih₁ ih₂ => simp [inf_le_of_left_le (ih₁ h), inf_le_of_right_le (ih₂ h)]
  | loop B C' => exact lfp.monotone fun Y σ ↦ by by_cases h' : B σ <;> simp_all [h σ]
  | tick e => apply add_le_add_left h

noncomputable def dwp_loop_f (B : BExpr ϖ) (C' : pGCL ϖ) (X : Exp ϖ) : Exp ϖ →o Exp ϖ :=
  ⟨fun Y => B.probOf * C'.dwp Y + B.not.probOf * X,
   fun _ _ h σ ↦ by simp [add_le_add, mul_le_mul, dwp.monotone C' h σ]⟩
theorem dwp_loop : (loop (ϖ:=ϖ) B C').dwp = fun X ↦ OrderHom.lfp (C'.dwp_loop_f B X) := rfl

theorem dwp_loop_fp (b : BExpr ϖ) (C : pGCL ϖ) :
  (pGCL.loop b C).dwp = fun X ↦ b.probOf * (C ; pGCL.loop b C).dwp X + b.not.probOf * X
:= by
  ext
  simp only [dwp_loop, dwp_loop_f, Pi.add_apply, Pi.mul_apply]
  rw [← OrderHom.map_lfp]
  rfl

end pGCL
