import PGCL.WeakestPre
import Mathlib.Data.ENNReal.Inv

namespace pGCL

variable {ϖ : Type*} [DecidableEq ϖ]

open OrderHom

/-- Strip all `tick`s from a program. -/
def st : pGCL ϖ → pGCL ϖ
  | pgcl {skip} => pgcl {skip}
  | pgcl {~x := ~A} => pgcl {~x := ~A}
  | pgcl {~C₁ ; ~C₂} => pgcl {~C₁.st ; ~C₂.st}
  | pgcl {{~C₁} [~p] {~C₂}} => pgcl {{~C₁.st} [~p] {~C₂.st}}
  | pgcl {{~C₁} [] {~C₂}} => pgcl {{~C₁.st} [] {~C₂.st}}
  | pgcl {while ~b {~C'}} => pgcl {while ~b {~C'.st}}
  | pgcl {tick(_)} => pgcl {skip}
  | pgcl {assert(b)} => pgcl {assert(b)}

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

theorem p_induction (φ : BExpr ϖ) (C : pGCL ϖ) (I : BExpr ϖ) (V : States ϖ → ENNReal)
    (p : ENNReal → ENNReal) (d : ENNReal → ENNReal) (hp : Antitone p) (hd : Antitone d)
    -- [I] is a subinvariant
    (h₁ : I.iver ≤ Φ φ C I.iver I.iver)
    -- V = 0 indicates termination
    (h₂ : φ.not.iver = BExpr.iver fun σ ↦ V σ = 0)
    -- V is a superinvariant
    (h₃ : V ≥ φ.iver * (C.awp V) + φ.not.iver * V)
    -- V satisfies a progress condition
    (h₄ : p ∘ V * φ.iver * I.iver ≤ fun σ ↦ C.wp (BExpr.iver fun σ' ↦ V σ' ≤ V σ - d (V σ)) σ)
    :
    I.iver ≤ wp⟦while ~φ {~C}⟧ 1 := by
  simp_all
  sorry

example :
      (BExpr.iver fun σ ↦ true)
    ≤ wp⟦
        while ~(fun σ ↦ σ "x" > 0) {
          { x := ~fun σ ↦ σ "x" - 1 } [~⟨1/2, by intro; simp⟩] { x := ~fun σ ↦ σ "x" + 1 } }
      ⟧ 1 := by
  apply p_induction _ _ _ (· "x") (1/2) 1
  · intro _ _ _; rfl
  · intro _ _ _; rfl
  · simp [Φ]
    intro σ
    simp [BExpr.iver, BExpr.not]
    split_ifs <;> simp_all
  · ext; simp [BExpr.iver, BExpr.not]
  · intro σ
    simp [BExpr.iver, BExpr.not, awp]
    split_ifs <;> try simp [ProbExp.pick, States.subst, *]
    · rename_i h
      contrapose h
      apply pos_iff_ne_zero.mp ‹_›
    · simp [← mul_add]
      if 1 ≤ σ "x" then
        rw [ENNReal.sub_add_eq_add_sub ‹_› (by simp)]
        ring_nf
        simp_all
        rw [mul_comm, mul_assoc]
        have : ((2 : ENNReal) * 2⁻¹) = 1 := by refine ENNReal.mul_inv_cancel ?_ ?_ <;> simp
        simp [this]
      else
        simp_all
        have : σ "x" - 1 = 0 := by
          refine tsub_eq_zero_of_le ?_
          (expose_names; exact le_of_lt h_2)
        simp [this]
        simp [mul_add]
  · intro σ
    simp [ProbExp.pick, States.subst, *]
    simp [BExpr.iver]
    split_ifs <;> simp

inductive T : Prop where

#check ((∀ (p : Prop), p : Prop) : Prop)

end pGCL
