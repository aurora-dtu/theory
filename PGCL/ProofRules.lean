import PGCL.WeakestPre
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.NNReal.Basic

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
  | pgcl {tick(~ _)} => pgcl {skip}
  | pgcl {assert(~ b)} => pgcl {assert(~b)}

def diverge : pGCL ϖ := .loop (fun _ ↦ true) .skip
def ite (b : BExpr ϖ) [DecidablePred b] (C₁ C₂ : pGCL ϖ) : pGCL ϖ := .prob C₁ b.probOf C₂

/-- A program is _Almost Surely Terminating_ iff it's weakest pre-expectation without ticks of one
  is one is. -/
def AST (C : pGCL ϖ) : Prop := C.st.dwp 1 = 1

noncomputable def cwp (C : pGCL ϖ) : Exp ϖ →o Exp ϖ :=
  ⟨(C.dwp · / C.st.dwp 1), fun a b hab σ ↦ ENNReal.div_le_div ((dwp _).monotone hab _) (by rfl)⟩

theorem park_induction (b : BExpr ϖ) [DecidablePred b] (C : pGCL ϖ) (f I) (h : (dΦ b C f) I ≤ I) :
    (C.loop b).dwp f ≤ I := lfp_le _ (by simp; exact h)

def Ψ (f : Exp ϖ) (Φ : Exp ϖ →o Exp ϖ) : Exp ϖ →o Exp ϖ := ⟨(Φ · ⊓ f), fun a b hab ↦ by
  simp
  refine inf_le_of_left_le (Φ.mono hab)⟩

def Ψ_iter_antitone (f : Exp ϖ) (Φ : Exp ϖ →o Exp ϖ) : Antitone ((Ψ f Φ)^[·] f) := by
  refine antitone_nat_of_succ_le fun n ↦ ?_
  induction n with
  | zero => simp [Ψ]
  | succ n ih =>
    simp only [Ψ, coe_mk, Function.iterate_succ', Function.comp_apply] at ih ⊢
    gcongr

omit [DecidableEq ϖ] in
theorem k_induction_park (Φ : Exp ϖ →o Exp ϖ) (f) (k) :
    Φ ((Ψ f Φ)^[k] f) ≤ f ↔ Φ ((Ψ f Φ)^[k] f) ≤ (Ψ f Φ)^[k] f := by
  constructor
  · intro h
    have : (⇑(Ψ f Φ))^[k + 1] f ≤ (⇑(Ψ f Φ))^[k] f := by apply Ψ_iter_antitone; omega
    apply le_trans _ this
    simp only [Ψ, coe_mk, Function.iterate_succ', Function.comp_apply, le_inf_iff, le_refl,
      true_and]
    exact le_trans h (by rfl)
  · intro h
    apply le_trans h
    simp [Ψ]
    induction k with
    | zero => simp
    | succ k ih => simp_all only [Function.iterate_succ', Function.comp_apply, inf_le_right]

omit [DecidableEq ϖ] in
theorem k_induction {Φ : Exp ϖ →o Exp ϖ} {f} (k : ℕ) (h : Φ ((Ψ f Φ)^[k] f) ≤ f) :
    lfp Φ ≤ f :=
  (lfp_le Φ ((k_induction_park Φ f k).mp h)).trans (Ψ_iter_antitone f Φ (by omega : 0 ≤ k))

-- /-- Park induction -/
-- theorem wGCL.wp_le_of_le {C : wGCL D W Var} (I : Weighting D M Var) (h : Φ φ C f I ≤ I) :
--     wp⟦while (~φ) {~C}⟧(~f) ≤ I := by
--   rw [wp_loop]; exact lfp_le _ h

noncomputable def p9_10th : ProbExp String :=
  ⟨9/10, by intro; simp; refine (ENNReal.div_le_iff ?_ ?_).mpr ?_ <;> simp; norm_cast⟩

@[simp]
theorem p9_10th_inv : p9_10th.val σ = p9_10th.val (fun _ ↦ 0) := by rfl

noncomputable def BoundedRetransmissionProtocol : pGCL String := pgcl {
  while sent < toSend ∧ fail < maxFail {
    {fail := 0; sent := sent + 1} [~p9_10th] {fail := fail + 1; totalFail := totalFail + 1}
  }
}

set_option maxHeartbeats 50000000 in
example :
      dwp⟦~BoundedRetransmissionProtocol⟧ (pgcl_aexp {totalFail})
    ≤ pgcl_aexp { [toSend ≤ 3] * (totalFail + 1) + [3 < toSend] * ~⊤ } := by
  simp [BoundedRetransmissionProtocol]
  apply k_induction 4
  intro σ
  simp only [dwp.prob, dwp.seq, dwp.assign, Pi.add_apply, mk_comp_mk, coe_mk, Function.comp_apply,
    Ψ, Function.iterate_succ', Function.iterate_zero, CompTriple.comp_eq, Pi.mul_apply, BExpr.iver,
    Pi.top_apply, ite_mul, one_mul, zero_mul, Pi.inf_apply, BExpr.not, not_and, not_lt]
  simp only [ProbExp.pick, States.subst, ↓reduceIte, String.reduceEq, Nat.cast_add, Nat.cast_one,
    Pi.add_apply, Pi.mul_apply, p9_10th_inv, mul_ite, mul_zero, Pi.sub_apply, Pi.one_apply,
    nonpos_iff_eq_zero, zero_add, Nat.reduceAdd]
  if σ "toSend" = 0 then
    simp_all only [not_lt_zero', false_and, ↓reduceIte, IsEmpty.forall_iff, zero_add, zero_le,
      add_zero, self_le_add_right]
  else if σ "toSend" = 1 then
    simp_all only [one_ne_zero, not_false_eq_true, Nat.lt_one_iff, zero_add, lt_self_iff_false,
      false_and, ↓reduceIte, IsEmpty.forall_iff, Nat.one_le_ofNat, Nat.not_ofNat_lt_one, add_zero,
      self_le_add_right, inf_of_le_left, zero_lt_one, true_and, forall_const]
    sorry
  else if h : σ "toSend" = 2 then
    simp only [h, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceLT, add_zero, isEmpty_Prop, not_lt,
      le_add_iff_nonneg_left, zero_le, IsEmpty.forall_iff]
    sorry
    -- split
  else if h : σ "toSend" = 3 then
    simp only [h, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceLT, add_zero, isEmpty_Prop, not_lt,
      le_add_iff_nonneg_left, zero_le, IsEmpty.forall_iff]
    sorry
  else if h : σ "toSend" = 4 then
    simp only [h, Nat.reduceLeDiff, ↓reduceIte, add_zero, ite_self, isEmpty_Prop, not_lt,
      le_add_iff_nonneg_left, zero_le, IsEmpty.forall_iff, zero_add, inf_of_le_right, mul_zero,
      nonpos_iff_eq_zero, ite_eq_right_iff, Nat.cast_eq_zero]
    sorry
    -- split
  else
    sorry
  -- if h : 3 < σ "toSend" then
  --   simp [h]
  --   if h' : σ "toSend" ≤ 3 then
  --     simp [h']
  --   else
  --     simp at h h'
  --     simp [h, h']
  --     sorry
  -- if h : σ "sent" < σ "toSend" ∧ σ "fail" < σ "maxFail" then
  --   simp [h]
  --   sorry
  -- else
  --   sorry

end pGCL
