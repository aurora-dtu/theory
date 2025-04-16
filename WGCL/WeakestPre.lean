import Mathlib.Order.OmegaCompletePartialOrder
import WGCL.Subst

namespace WGCL

variable {D : Type} {W : Type} {Var : Type}

variable [DecidableEq Var]

instance : Subst (Mem D Var) Var D where
  subst σ x v := fun y ↦ if x = y then v else σ y

instance : Subst (Weighting D W Var) Var (AExpr D Var) where
  subst f x E := fun σ ↦ f σ[x ↦ E σ]

@[simp]
theorem Weighting.subst_mono [Preorder W] {f₁ f₂ : Weighting D W Var} (h : f₁ ≤ f₂) (x : Var)
    (y : AExpr D Var) : f₁[x ↦ y] ≤ f₂[x ↦ y] := by
  intro σ
  exact h fun y_1 => if x = y_1 then y σ else σ y_1

def BExpr.not (B : BExpr D Var) : BExpr D Var := fun σ ↦ ¬B σ

variable [∀ (B : BExpr D Var) σ, Decidable (B σ)]

def BExpr.iver [One W] [Zero W] (B : BExpr D Var) : Weighting D W Var := (if B · then 1 else 0)

variable [Semiring W]

variable [OmegaCompletePartialOrder W] [OrderBot W]

open OmegaCompletePartialOrder

def wGCL.lfp (f : Weighting D W Var →o Weighting D W Var) : Weighting D W Var :=
  ωSup ⟨(f^[·] ⊥), fun _ _ h ↦ Monotone.monotone_iterate_of_le_map f.mono (OrderBot.bot_le _) h⟩

def wGCL.lfp_mono : Monotone (lfp (D:=D) (W:=W) (Var:=Var)) := by
  intro X₁ X₂ h σ
  simp [lfp, ωSup]
  intro i
  refine le_ωSup_of_le i ?_
  suffices X₁^[i] ≤ X₂^[i] by apply this
  apply Monotone.iterate_le_of_le X₁.mono h

variable [AddLeftMono W]
variable [MulLeftMono W]

attribute [local simp] Function.swap
instance : AddLeftMono  (Weighting D W Var) := ⟨by intro _ _ _ _ _; simp; gcongr; apply_assumption⟩
instance : MulLeftMono  (Weighting D W Var) := ⟨by intro _ _ _ _ _; simp; gcongr; apply_assumption⟩

protected def wGCL.wp' : wGCL D W Var → Weighting D W Var →o Weighting D W Var :=
  have : ∀ (C C' : wGCL D W Var), WellFoundedRelation.rel C C' ↔ sizeOf C < sizeOf C' := by aesop
  have : ∀ (a b : ℕ), a < 1 + a + b := by omega
  WellFounded.fix sizeOfWFRel.wf fun C wp ↦ ⟨fun f ↦ match C with
  | wgcl { ~x := ~E }                     => f[x ↦ E]
  | wgcl { ~C₁; ~C₂ }                     => wp C₁ (by simp_all) (wp C₂ (by simp_all) f)
  | wgcl { if (~φ) { ~C₁ } else { ~C₂ } } =>
    φ.iver * wp C₁ (by simp_all) f + φ.not.iver * wp C₂ (by simp_all) f
  | wgcl { { ~C₁ } ⊕ { ~C₂ } }            => wp C₁ (by simp_all) f + wp C₂ (by simp_all) f
  | wgcl { ⊙ ~a }                         => a * f
  | wgcl { while (~φ) { ~C' } }           =>
    lfp ⟨fun X ↦ φ.iver * wp C' (by simp_all) X + φ.not.iver * f, by intro X₁ X₂ h; simp; gcongr⟩,
  by
    intro f₁ f₂ h
    split
    next x E _ => simp_all
    next C₁ C₂ wp => exact (wp C₁ ?_).mono <| (wp C₂ (by simp_all)).mono h
    next φ C₁ C₂ wp =>
      intro σ
      simp [BExpr.iver, BExpr.not]
      split_ifs <;> (simp; exact (wp _ (by simp_all)).mono h σ)
    next => simp; gcongr
    next => simp; gcongr
    next φ C wp => apply lfp_mono fun X σ ↦ ?_; simp; gcongr; exact h σ⟩

def wGCL.wp (C : wGCL D W Var) : Weighting D W Var →o Weighting D W Var := ⟨fun f ↦ match C with
  | wgcl { ~x := ~E }                     => f[x ↦ E]
  | wgcl { ~C₁; ~C₂ }                     => C₁.wp' (C₂.wp' f)
  | wgcl { if (~φ) { ~C₁ } else { ~C₂ } } => φ.iver * C₁.wp' f + φ.not.iver * C₂.wp' f
  | wgcl { { ~C₁ } ⊕ { ~C₂ } }            => C₁.wp' f + C₂.wp' f
  | wgcl { ⊙ ~a }                         => a * f
  | wgcl { while (~φ) { ~C' } }           => lfp ⟨fun X ↦ φ.iver * C'.wp' X + φ.not.iver * f, by
    intro X₁ X₂ h
    simp
    gcongr⟩,
  by
    intro f₁ f₂ h
    cases C <;> (simp_all; try gcongr)
    apply lfp_mono fun X σ ↦ ?_; simp; gcongr; exact h σ⟩

@[simp]
theorem wGCL.wp'_eq_wp (C : wGCL D W Var) : C.wp' = C.wp := by
  cases C <;> (simp_all [wp, wGCL.wp']; rw [WellFounded.fix_eq])

def wGCL.Φ  (φ : BExpr D Var) (C' : wGCL D W Var) (f : Weighting D W Var) :
    Weighting D W Var →o Weighting D W Var := ⟨fun X ↦ φ.iver * C'.wp X + φ.not.iver * f, by
      intro X₁ X₂ h σ
      simp
      gcongr
      apply (wp C').mono h⟩

theorem wGCL.wp_loop (C' : wGCL D W Var) : wgcl { while (~φ) { ~C' } }.wp f = lfp (Φ φ C' f) := by
  rw [wp]
  simp
  rfl

variable [∀ (B : BExpr ℕ String) σ, Decidable (B σ)]

syntax "wp⟦" cwgcl_prog "⟧" : term
syntax "wp[" term "," term "," term "]⟦" cwgcl_prog "⟧" : term
syntax "wp⟦" cwgcl_prog "⟧(" cwgcl_wght ")" : term
syntax "wp[" term "," term "," term "]⟦" cwgcl_prog "⟧(" cwgcl_wght ")" : term

macro_rules
| `(wp⟦$c⟧) => `(wgcl{$c}.wp)
| `(wp[$D,$W,$Var]⟦$c⟧) => `((wgcl{$c} : wGCL $D $W $Var).wp)
| `(wp⟦$c⟧($f)) => `(wgcl{$c}.wp wght{$f})
| `(wp[$D,$W,$Var]⟦$c⟧($f)) => `((wgcl {$c} : wGCL $D $W $Var).wp wght{$f})

section

open Lean PrettyPrinter Delaborator SubExpr

@[app_unexpander wGCL.wp]
def wGCL.unexpandWp : Unexpander
| `($(_) wgcl {$C} $f) => do
  let f ← unexpandWeighting f
  `(wp⟦$C⟧($f))
| `($(_) wgcl {$C}) => `(wp⟦$C⟧)
| _ => throw ()

end

end WGCL
