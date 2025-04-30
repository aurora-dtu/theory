import Mathlib.Algebra.Order.Group.Action
import WGCL.Subst
import WGCL.FixedPoints

namespace WGCL

variable {D : Type} {M : Type} {W : Type} {Var : Type}

variable [DecidableEq Var]

def BExpr.not (B : BExpr D Var) : BExpr D Var := fun σ ↦ ¬B σ

variable [∀ (B : BExpr D Var) σ, Decidable (B σ)]

def BExpr.iver [OmegaCompletePartialOrder M] [Zero M] (B : BExpr D Var) :
    Weighting D M Var →o Weighting D M Var :=
  ⟨fun f σ ↦ if B σ then f σ else 0, by
    intro f₁ f₂ h σ
    simp
    split_ifs <;> simp_all [h σ]⟩

variable [Monoid W] [AddCommMonoid M]
variable [inst : DistribMulAction W M]

instance : SMul W M := inst.toSMul

variable [OmegaCompletePartialOrder M] [OrderBot M]

open OmegaCompletePartialOrder

variable [AddLeftMono M]
variable [CovariantClass W M HSMul.hSMul LE.le]

attribute [local simp] Function.swap
instance : AddLeftMono (Weighting D M Var) := ⟨by intro _ _ _ _ _; simp; gcongr; apply_assumption⟩
instance : CovariantClass (𝕎 W (Mem D Var)) (Weighting D M Var) HSMul.hSMul LE.le :=
  ⟨by intro _ _ _ _ σ; simp; gcongr; apply_assumption⟩

instance {𝒮 : Type} [Mul 𝒮] [Preorder 𝒮] [MulLeftMono 𝒮] :
    CovariantClass 𝒮 𝒮 HSMul.hSMul LE.le :=
  ⟨fun x ↦ by simp_all; exact fun {n₁ n₂} a ↦ mul_le_mul_left' a x⟩

section wp

protected def wGCL.wp' : wGCL D W Var → Weighting D M Var →o Weighting D M Var :=
  have : ∀ (C C' : wGCL D W Var), WellFoundedRelation.rel C C' ↔ sizeOf C < sizeOf C' := by aesop
  have : ∀ (a b : ℕ), a < 1 + a + b := by omega
  WellFounded.fix sizeOfWFRel.wf fun C wp ↦ ⟨fun f ↦ match C with
  | wgcl { ~x := ~E }                     => f[x ↦ E]
  | wgcl { ~C₁; ~C₂ }                     => wp C₁ (by simp_all) (wp C₂ (by simp_all) f)
  | wgcl { if (~φ) { ~C₁ } else { ~C₂ } } =>
    φ.iver (wp C₁ (by simp_all) f) + φ.not.iver (wp C₂ (by simp_all) f)
  | wgcl { { ~C₁ } ⊕ { ~C₂ } }            => wp C₁ (by simp_all) f + wp C₂ (by simp_all) f
  | wgcl { ⊙ ~a }                         => a ⊗ f
  | wgcl { while (~φ) { ~C' } }           =>
    lfp ⟨fun X ↦ φ.iver (wp C' (by simp_all) X) + φ.not.iver f, by intro X₁ X₂ h; simp; gcongr⟩,
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
    next a wp => intro σ; simp; gcongr; apply_assumption
    next φ C wp => simp; gcongr; intro X σ; simp; gcongr; apply (BExpr.iver φ.not).mono h σ⟩

def wGCL.wp (C : wGCL D W Var) : Weighting D M Var →o Weighting D M Var := ⟨fun f ↦ match C with
  | wgcl { ~x := ~E }                     => f[x ↦ E]
  | wgcl { ~C₁; ~C₂ }                     => C₁.wp' (C₂.wp' f)
  | wgcl { if (~φ) { ~C₁ } else { ~C₂ } } => φ.iver (C₁.wp' f) + φ.not.iver (C₂.wp' f)
  | wgcl { { ~C₁ } ⊕ { ~C₂ } }            => C₁.wp' f + C₂.wp' f
  | wgcl { ⊙ ~a }                         => a • f
  | wgcl { while (~φ) { ~C' } }           => lfp ⟨fun X ↦ φ.iver (C'.wp' X) + φ.not.iver f, by
    intro X₁ X₂ h
    simp
    gcongr⟩,
  by
    intro f₁ f₂ h
    cases C <;> (simp_all; try gcongr); intro X σ; simp; gcongr; exact (BExpr.not _).iver.mono h σ⟩

@[simp]
theorem wGCL.wp'_eq_wp (C : wGCL D W Var) : C.wp' (M:=M) = C.wp := by
  cases C <;> (simp_all [wp, wGCL.wp']; rw [WellFounded.fix_eq])

def wGCL.Φ  (φ : BExpr D Var) (C' : wGCL D W Var) (f : Weighting D M Var) :
    Weighting D M Var →o Weighting D M Var := ⟨fun X ↦ φ.iver (C'.wp X) + φ.not.iver f, by
      intro X₁ X₂ h σ
      simp
      gcongr
      apply φ.iver.mono <| (wp C').mono h⟩

theorem wGCL.wp_loop (C' : wGCL D W Var) :
    wgcl { while (~φ) { ~C' } }.wp f = lfp (Φ (M:=M) φ C' f) := by
  rw [wp]
  simp
  rfl

end wp

section wlp

variable [OmegaCompletePartialCoOrder M] [OrderTop M]

instance [OmegaCompletePartialCoOrder M] : OmegaCompletePartialCoOrder (Weighting D M Var) := sorry

-- protected def wGCL.wlp' :
--     wGCL D W Var → Weighting D M Var →o Weighting D M Var :=
--   have : ∀ (C C' : wGCL D W Var), WellFoundedRelation.rel C C' ↔ sizeOf C < sizeOf C' := by aesop
--   have : ∀ (a b : ℕ), a < 1 + a + b := by omega
--   WellFounded.fix sizeOfWFRel.wf fun C wlp ↦ ⟨fun f ↦ match C with
--   | wgcl { ~x := ~E }                     => f[x ↦ E]
--   | wgcl { ~C₁; ~C₂ }                     => wlp C₁ (by simp_all) (wlp C₂ (by simp_all) f)
--   | wgcl { if (~φ) { ~C₁ } else { ~C₂ } } =>
--     φ.iver (wlp C₁ (by simp_all) f) + φ.not.iver (wlp C₂ (by simp_all) f)
--   | wgcl { { ~C₁ } ⊕ { ~C₂ } }            => wlp C₁ (by simp_all) f + wlp C₂ (by simp_all) f
--   | wgcl { ⊙ ~a }                         => a ⊗ f
--   | wgcl { while (~φ) { ~C' } }           =>
--     gfp ⟨fun X ↦ φ.iver (wlp C' (by simp_all) X) + φ.not.iver f, by intro X₁ X₂ h; simp; gcongr⟩,
--   by
--     intro f₁ f₂ h
--     split
--     next x E _ => simp_all
--     next C₁ C₂ wlp => exact (wlp C₁ ?_).mono <| (wlp C₂ (by simp_all)).mono h
--     next φ C₁ C₂ wlp =>
--       intro σ
--       simp [BExpr.iver, BExpr.not]
--       split_ifs <;> (simp; exact (wlp _ (by simp_all)).mono h σ)
--     next => simp; gcongr
--     next a wlp => intro σ; simp; gcongr; apply_assumption
--     next φ C wlp => simp; gcongr; intro X σ; simp; gcongr; apply (BExpr.iver φ.not).mono h σ⟩

-- def wGCL.wlp (C : wGCL D W Var) : Weighting D M Var →o Weighting D M Var := ⟨fun f ↦ match C with
--   | wgcl { ~x := ~E }                     => f[x ↦ E]
--   | wgcl { ~C₁; ~C₂ }                     => C₁.wlp' (C₂.wlp' f)
--   | wgcl { if (~φ) { ~C₁ } else { ~C₂ } } => φ.iver (C₁.wlp' f) + φ.not.iver (C₂.wlp' f)
--   | wgcl { { ~C₁ } ⊕ { ~C₂ } }            => C₁.wlp' f + C₂.wlp' f
--   | wgcl { ⊙ ~a }                         => a • f
--   | wgcl { while (~φ) { ~C' } }           => lfp ⟨fun X ↦ φ.iver (C'.wlp' X) + φ.not.iver f, by
--     intro X₁ X₂ h
--     simp
--     gcongr⟩,
--   by
--     intro f₁ f₂ h
--     cases C <;> (simp_all; try gcongr); intro X σ; simp; gcongr; exact (BExpr.not _).iver.mono h σ⟩

end wlp

variable [∀ (B : BExpr ℕ String) σ, Decidable (B σ)]

syntax "wp⟦" cwgcl_prog "⟧" : term
syntax "wp[" term "," term "," term "," term "]⟦" cwgcl_prog "⟧" : term
syntax "wp⟦" cwgcl_prog "⟧(" cwgcl_wght ")" : term
syntax "wp[" term "," term "," term "," term "]⟦" cwgcl_prog "⟧(" cwgcl_wght ")" : term

macro_rules
| `(wp⟦$c⟧) => `(wgcl{$c}.wp)
| `(wp[$D,$M,$W,$Var]⟦$c⟧) => `((wgcl{$c} : wGCL $D $W $Var).wp (M:=$M))
| `(wp⟦$c⟧($f)) => `(wgcl{$c}.wp wght{$f})
| `(wp[$D,$M,$W,$Var]⟦$c⟧($f)) => `((wgcl {$c} : wGCL $D $W $Var).wp (M:=$M) wght{$f})

section

open Lean PrettyPrinter Delaborator SubExpr

@[app_unexpander wGCL.wp]
def wGCL.unexpandWp : Unexpander
| `($(_) wgcl {$C} $f) => do
  let f ← unexpandWeighting f
  `(wp⟦$C⟧($f))
| `($(_) wgcl {$C}) => `(wp⟦$C⟧)
| _ => throw ()

syntax "i[" term "]" : term

@[app_unexpander BExpr.iver]
def BExpr.unexpandIver : Unexpander
| `($_ $b) => `(i[$b])
| _ => throw ()

end

section

open scoped Classical in
example :
    wp[ℕ,M,W,Var]⟦
      while (~(fun σ ↦ σ x > 0 ∧ σ y > 0)) {
        { ~x := ~(· x - 1); ~y := ~(· y + 1)} ⊕ { ~y := ~(· y - 1) } ;
        ⊙ 1
      }
    ⟧(0) ≤ wght {0} := by
  intro σ
  simp
  sorry

end

end WGCL
