import PGCL.WeakestPre
import Mathlib.Data.ENNReal.Inv

namespace pGCL

variable {ϖ : Type*} [DecidableEq ϖ]

open OrderHom

/-- Strip all `tick`s from a program. -/
def st : pGCL ϖ → pGCL ϖ
  | .skip => .skip
  | .assign x A => .assign x A
  | .seq C₁ C₂ => .seq C₁.st C₂.st
  | .prob C₁ p C₂ => .prob C₁.st p C₂.st
  | .nonDet C₁ C₂ => .nonDet C₁.st C₂.st
  | .loop b C' => .loop b C'.st
  | .tick _ => .skip
  | .assert b => .assert b

def diverge : pGCL ϖ := .loop (fun _ ↦ true) .skip
def ite (b : BExpr ϖ) (C₁ C₂ : pGCL ϖ) : pGCL ϖ := .prob C₁ b.probOf C₂

/-- A program is _Almost Surely Terminating_ iff it's weakest pre-expectation without ticks of one
  is one is. -/
def AST (C : pGCL ϖ) : Prop := C.st.wp 1 = 1

noncomputable def cwp (C : pGCL ϖ) : Exp ϖ →o Exp ϖ :=
  ⟨(C.wp · / C.st.wp 1), fun a b hab σ ↦ ENNReal.div_le_div ((wp _).monotone hab _) (by rfl)⟩

theorem park_induction (b : BExpr ϖ) (C : pGCL ϖ) (f I) (h : (Φ b C f) I ≤ I) :
    (C.loop b).wp f ≤ I := lfp_le _ (by simp [Φ] at h ⊢; exact h)

def Ψ (f : Exp ϖ) (Φ : Exp ϖ →o Exp ϖ) : Exp ϖ →o Exp ϖ := ⟨(Φ · ⊓ f), fun a b hab ↦ by
  simp
  refine inf_le_of_left_le (Φ.mono hab)⟩

theorem k_induction_park (Φ : Exp ϖ →o Exp ϖ) (f) (k) :
    Φ ((Ψ f Φ)^[k] f) ≤ f ↔ Φ ((Ψ f Φ)^[k] f) ≤ (Ψ f Φ)^[k] f := by
  constructor
  · intro h
    have : (⇑(Ψ f Φ))^[k + 1] f ≤ (⇑(Ψ f Φ))^[k] f := by
      induction k generalizing f with
      | zero => simp_all [Ψ]
      | succ k ih =>
        simp_all only [Function.iterate_succ', Function.comp_apply]
        gcongr
        apply ih
        apply le_trans _ h
        simp [Ψ]
        gcongr
        sorry
    apply le_trans _ this
    simp only [Function.iterate_succ', Function.comp_apply]
    simp only [Ψ, coe_mk]
    simp only [le_inf_iff, le_refl, true_and]
    apply le_trans h
    rfl
  · intro h
    apply le_trans h
    simp [Ψ]
    induction k with
    | zero => simp
    | succ k ih =>
      simp_all only [Function.iterate_succ', Function.comp_apply]
      exact inf_le_right

theorem k_induction (Φ : Exp ϖ →o Exp ϖ) (f) (h : Φ ((Ψ f Φ)^[k] f) ≤ f) :
    lfp Φ ≤ f := by
  -- apply le_trans _ h

  have := (k_induction_park Φ f k).mpr
  apply le_trans _ (this ?_)
  · apply lfp_le
    gcongr
    apply le_trans h
    sorry
  · apply le_trans h
    induction k with
    | zero => simp
    | succ k ih =>
      sorry

  -- induction k generalizing f with
  -- | zero => exact lfp_le _ h
  -- | succ n ih =>
  --   simp_all only [Function.iterate_succ', Function.comp_apply]
  --   simp [Ψ] at h
  --   -- rw [← map_lfp]
  --   apply ih
  --   apply le_trans _ h
  --   gcongr
  --   apply ih
  --   sorry

-- /-- Park induction -/
-- theorem wGCL.wp_le_of_le {C : wGCL D W Var} (I : Weighting D M Var) (h : Φ φ C f I ≤ I) :
--     wp⟦while (~φ) {~C}⟧(~f) ≤ I := by
--   rw [wp_loop]; exact lfp_le _ h

theorem p_induction (b : BExpr ϖ) (C : pGCL ϖ) (I : BExpr ϖ) (V : States ϖ → NNReal)
    (p : NNReal → NNReal) (d : NNReal → NNReal) (hp : Antitone p) (hd : Antitone d)
    (h₁ : I.iver ≤ (pGCL.loop b C).wp I.iver)
    (h₂ : G)
    :
    I.iver ≤ (pGCL.loop b C).wp 1 := sorry


end pGCL
