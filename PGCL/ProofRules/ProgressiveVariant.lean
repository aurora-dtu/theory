import PGCL.WeakestPre
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.NNReal.Basic

namespace pGCL

variable {ϖ : Type*} [DecidableEq ϖ]

open OrderHom

notation "i[" x "]" => BExpr.iver x

/-- `I` is called a superinvarirant with respect to postcondition `f` -/
def superinvariant (φ : BExpr ϖ) [DecidablePred φ] (I : Exp ϖ) (f : Exp ϖ) : Prop :=
  i[φ] * f + i[φ.not] * I ≤ I
/-- `I` is called a subinvarirant with respect to postcondition `f` -/
def subinvariant (φ : BExpr ϖ) [DecidablePred φ] (I : Exp ϖ) (f : Exp ϖ) : Prop :=
  I ≤ i[φ] * f + i[φ.not] * I
/-- `I` is called a wp-subinvarirant of `while φ {C}` with respect to postcondition `f` -/
def wpSubinvariant (φ : BExpr ϖ) [DecidablePred φ] (C : pGCL ϖ) (I : Exp ϖ) (f : Exp ϖ) : Prop :=
  I ≤ i[φ] * (dwp⟦~C⟧ f) + i[φ.not] * I

-- theorem subinvariant_go (φ : BExpr ϖ) [DecidablePred φ] (C : pGCL ϖ) (I f : Exp ϖ)
--     -- [I] is a subinvariant
--     (hI : subinvariant φ I (dwp⟦~C⟧ I)) :
--     I ≤ dwp⟦while ~φ {~C}⟧ I := by
--   simp_all [subinvariant]
--   apply le_lfp
--   intro b hb
--   simp_all
--   apply le_trans hI
--   apply le_trans _ hb
--   gcongr
--   rw [← dwp_fp]
--   simp [dΦ]
--   gcongr
--   · rfl

@[simp]
theorem BExpr.mul_self (φ : BExpr ϖ) [DecidablePred φ] : i[φ] * i[φ] = i[φ] := by
  ext; simp [BExpr.iver]
@[simp]
theorem BExpr.mul_not (φ : BExpr ϖ) [DecidablePred φ] : i[φ] * i[φ.not] = 0 := by
  ext; simp [BExpr.iver, BExpr.not]
@[simp]
theorem BExpr.not_mul (φ : BExpr ϖ) [DecidablePred φ] : i[φ.not] * i[φ] = 0 := by
  ext; simp [BExpr.iver, BExpr.not]

/-- Kaminski – Theorem 5.12 -/
theorem bounded_expectation (φ : BExpr ϖ) [DecidablePred φ] (C : pGCL ϖ)
    (b : ENNReal) (f I' : States ϖ → ENNReal) (hf : f ≤ fun _ ↦ b) (hI' : I' ≤ fun _ ↦ b)
    (h_inv : wpSubinvariant φ C (i[φ.not] * f + i[φ] * I') f) :
    let I := i[φ.not] * f + i[φ] * I'
    let T := dwp⟦while ~φ {~C}⟧ 1
    (∀ G [DecidablePred G], I = i[G] →
      T * I ≤ dwp⟦while ~φ {~C}⟧ f) ∧
    (∀ G [DecidablePred G], I = i[G] →
      i[G] * I ≤ dwp⟦while ~φ {~C}⟧ f) ∧
    (∀ (ε : ENNReal), 0 < ε ∧ ε < ⊤ → (fun _ ↦ ε) * I ≤ T →
      I ≤ dwp⟦while ~φ {~C}⟧ f)
     := by
  set I := i[φ.not] * f + i[φ] * I'
  set T := dwp⟦while ~φ {~C}⟧ 1
  simp
  split_ands
  · intro G _ hIG
    simp_all [I, T, wpSubinvariant]
    simp [← hIG, mul_add, ← mul_assoc] at h_inv
    rw [add_comm] at h_inv
    have : i[φ] * I' ≤ i[φ] * dwp⟦~C⟧ f := by
      intro σ
      specialize h_inv σ
      simp at h_inv ⊢
      contrapose! h_inv
      gcongr
      simp_all
      refine ENNReal.mul_ne_top ?_ ?_
      · simp [BExpr.iver]; split_ifs <;> simp
      · simp
        specialize hf σ
        simp at hf
        sorry
    intro σ
    simp [BExpr.iver]
    split_ifs with hG
    · apply dwp⟦~_⟧.mono
      replace hIG := congrFun hIG σ
      specialize h_inv σ
      simp [BExpr.iver, BExpr.not, hG] at hIG h_inv
      split_ifs at hIG
      · simp_all
        sorry
      · simp_all
        sorry
    · simp
    -- sorry
  · sorry
  · intro ε hε hε' hεI
    simp_all [I, T, wpSubinvariant, mul_add, ← mul_assoc]
    apply le_trans h_inv; clear h_inv
    rw [add_comm] at hεI
    have : ∀ (x y : Exp ϖ), (fun _ ↦ ε) * x ≤ (fun _ ↦ ε) * y → x ≤ y := by
      intro x y h σ; specialize h σ; simp_all
      contrapose! h
      gcongr
      exact LT.lt.ne_top hε'

    apply this; clear this
    simp [mul_add, ← mul_assoc]
    -- apply le_trans hεI
    sorry

theorem bounded_expectation₃ (φ : BExpr ϖ) [DecidablePred φ] (C : pGCL ϖ)
    (b : ENNReal) (f I' : States ϖ → ENNReal) (hf : f ≤ fun _ ↦ b) (hI' : I' ≤ fun _ ↦ b)
    (h_inv : wpSubinvariant φ C (i[φ.not] * f + i[φ] * I') f) :
    let I := i[φ.not] * f + i[φ] * I'
    let T := dwp⟦while ~φ {~C}⟧ 1
    (∀ (ε : ENNReal), 0 < ε ∧ ε < ⊤ → (fun _ ↦ ε) * I ≤ T →
      I ≤ dwp⟦while ~φ {~C}⟧ f)
:= (bounded_expectation φ C b f I' hf hI' h_inv).2.2

theorem zero_one_law_of_probabilitic_termination (φ : BExpr ϖ) [DecidablePred φ] (C : pGCL ϖ) (I : BExpr ϖ) [DecidablePred I]
    -- [I] is a subinvariant
    (hI : wpSubinvariant φ C i[I] i[I])
    (ε : ENNReal) (hε : 0 < ε ∧ ε < ⊤)
    (heI : pgcl_aexp {~(fun _ ↦ ε) * [~I]} ≤ dwp⟦while ~φ {~C}⟧ 1) :
    i[I] ≤ dwp⟦while ~φ {~C}⟧ (pgcl_aexp {[~φ.not ∧ ~I]}) := by
  simp_all [wpSubinvariant]
  set f := (pgcl_aexp {[~φ.not ∧ ~I]})
  have h₀ : i[I] = i[φ.not] * f + i[φ] * i[I] := by
    ext σ
    simp [f, BExpr.iver, BExpr.not]
    split_ifs <;> simp_all
  rw [h₀] -- ; clear h₀
  have h₁ : i[I] ≤ i[φ] * dwp⟦~C⟧ i[I] + i[φ.not] * f := by
    apply le_trans hI
    simp [f]
    intro σ
    simp [BExpr.iver, BExpr.not, ite_and]
    split_ifs <;> simp
  have heI' := heI
  rw [h₀] at heI'
  apply bounded_expectation₃ φ C 1 f i[I] _ _ _ ε hε heI'
  · intro σ; simp [f, BExpr.iver]; split_ifs <;> simp
  · intro σ; simp [BExpr.iver]; split_ifs <;> simp
  · simp [wpSubinvariant, f]
    intro σ
    simp [BExpr.iver, BExpr.not, ite_and]
    split_ifs <;> simp
    sorry
  -- · rw [← h₀]
  --   assumption

/-- Theorem 6.7 -/
theorem AST_of_bounded_int_variant (ψ : BExpr ϖ) [DecidablePred ψ] (C : pGCL ϖ) (I : BExpr ϖ) [DecidablePred I]
    -- [I] is a subinvariant
    (hI : wpSubinvariant ψ C i[I] i[I])
    (Z : States ϖ → ℕ) (L H : ℕ) (ε : ENNReal) (hε : 0 < ε ∧ ε ≤ 1)
    (hZLH : pgcl_aexp {[~ψ ∧ ~I]} ≤ i[fun σ ↦ L ≤ Z σ ∧ Z σ ≤ H])
    (heZ : pgcl_aexp {~(fun _ ↦ ε) * [~ψ ≤ ~I]} ≤ fun σ ↦ dwp⟦~C⟧ (pgcl_aexp { [~Z ≤ ~(fun _ ↦ Z σ)] }) σ) :
    i[I] ≤ dwp⟦while ~ψ {~C}⟧ 1 := by
  -- simp_all only [le_Prop_eq]
  simp [wpSubinvariant] at hI
  have := zero_one_law_of_probabilitic_termination ψ C I hI ε ⟨hε.left, hε.right.trans_lt ENNReal.one_lt_top⟩
  · simp_all
    have h' : i[fun σ ↦ ψ.not σ ∧ (ψ σ → I σ)] = i[ψ.not] := by ext; simp [BExpr.not, BExpr.iver]; grind
    simp at h'
    -- rw [h'] at this
    -- simp_all
    sorry
  -- · sorry

/-- Theorem 6.8 -/
theorem progressive_variant (φ : BExpr ϖ) [DecidablePred φ] (C : pGCL ϖ) (I : BExpr ϖ) [DecidablePred I]
    (V : States ϖ → ENNReal)
    (p : ENNReal → ENNReal) (d : ENNReal → ENNReal) (hp : Antitone p) (hd : Antitone d)
    -- [I] is a subinvariant
    (h₁ : i[I] ≤ dΦ φ C i[I] i[I])
    -- V = 0 indicates termination
    (h₂ : i[φ.not] = pgcl_aexp {[~V = 0]})
    -- V is a superinvariant
    (h₃ : V ≥ i[φ] * (awp⟦~C⟧ V) + i[φ.not] * V)
    -- V satisfies a progress condition
    (h₄ : p ∘ V * i[φ] * i[I] ≤ fun σ ↦ C.dwp (BExpr.iver fun σ' ↦ V σ' ≤ V σ - d (V σ)) σ) :
    i[I] ≤ dwp⟦while ~φ {~C}⟧ 1 := by
  simp_all
  have : ∀ h : ENNReal, i[I] ≤ dwp⟦while 0 < ~V ∧ ~V ≤ ~(fun _ ↦ h) {~C}⟧ 1 := by
    intro h;
    set ψ : BExpr ϖ := pgcl_bexp { 0 < ~V ∧ ~V ≤ ~(fun _ ↦ h) }
    have : i[I] ≤ ψ.iver * dwp⟦~C⟧ i[I] + ψ.not.iver * i[I] := by
      simp [dΦ] at h₁
      replace h₁ : i[φ] * i[I] ≤ i[φ] * dwp⟦~C⟧ i[I] := by
        intro σ
        specialize h₁ σ
        simp [BExpr.iver] at h₁ ⊢
        split_ifs with hI <;> simp_all [BExpr.not]
      replace h₂ : i[φ] = BExpr.iver fun σ ↦ 0 < V σ := by
        ext σ;
        have := congrFun h₂ σ
        simp_all [BExpr.iver, BExpr.not]
        split_ifs <;> simp_all
      rw [h₂] at h₁
      replace h₁ : ψ.iver * i[I] ≤ ψ.iver * dwp⟦~C⟧ i[I] := by
        intro σ
        specialize h₁ σ
        simp_all [ψ, BExpr.iver]
        split_ifs <;> simp_all
      apply le_trans _ (?_ : ψ.iver * i[I] + ψ.not.iver * i[I] ≤ _)
      · intro σ
        simp [BExpr.iver, BExpr.not]; split_ifs <;> simp
      · gcongr
    set Z : States ϖ → ℕ := fun σ ↦ Nat.ceil (V σ / d h).toNNReal
    set L : ℕ := 0
    set H : ℕ := Nat.ceil (h / d h).toNNReal
    simp
    apply AST_of_bounded_int_variant _ _ _ _ Z L H (p h)
    · sorry
    · intro σ
      simp [BExpr.iver, ite_and]
      split_ifs <;> simp_all [L, Z, H]
      sorry
    · intro σ
      simp [BExpr.iver, ite_and]
      split_ifs
      · simp_all [ψ, Z]
        specialize this σ
        simp [BExpr.iver, BExpr.not, ite_and] at this
        specialize h₁ σ
        replace h₂ := congrFun h₂ σ
        specialize h₃ σ
        specialize h₄ σ
        split_ifs at this <;> simp_all [BExpr.iver, BExpr.not]
        · rename_i h₁ h₂; absurd h₂; simp; assumption
        · sorry
        · sorry
        · sorry
        · sorry
        · sorry
      · simp_all
    · sorry
  sorry
    -- have : pgcl_aexp {[~ψ ≤ ~I]} ≤ pgcl_aexp {[~L ≤ ~Z ∧ ~Z ≤ ~H]} := by
    --   intro σ
    --   simp [Z, L, H, ψ, BExpr.iver]
    --   split_ifs with h' h'' <;> simp_all
    --   simp [imp_iff_not_or] at h'
    --   rcases h' with (h' | h' | h')
    --   · simp [h'] at h''
    --   · sorry
    --   · sorry

    -- sorry

example :
      (BExpr.iver fun _ ↦ true)
    ≤ dwp⟦while 0 < x { { x := x - 1 } [~⟨1/2, fun _ ↦ by simp⟩] { x := x + 1 } }⟧ 1 := by
  apply progressive_variant _ _ _ (pgcl_aexp {x}) (1/2) 1
  · intro _ _ _; rfl
  · intro _ _ _; rfl
  · simp [dΦ]
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
      rw [ENNReal.sub_add_eq_add_sub]
      · simp [mul_add, ← add_assoc]
        ring_nf
        rw [mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel] <;> simp
      · simp; assumption
      · simp
  · intro σ
    simp [ProbExp.pick, States.subst, *]
    simp [BExpr.iver]
    split_ifs <;> simp

end pGCL
