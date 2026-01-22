import PGCL.WeakestPre
import PGCL.WeakestLiberalPre
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.String.Basic
import ENNRealArith

namespace pGCL

variable {ϖ : Type*} [DecidableEq ϖ]

open OrderHom
open Optimization.Notation

/-- A program is _Almost Surely Terminating_ iff it's weakest pre-expectation without ticks of one
  is one is. -/
def AST (C : pGCL ϖ) : Prop := C.st.dwp 1 = 1

noncomputable def cwp (O : Optimization) (C : pGCL ϖ) : Exp ϖ →o Exp ϖ :=
  ⟨(wp[O]⟦~C⟧ · / wlp[O]⟦~C⟧ 1),
    fun a b hab σ ↦ ENNReal.div_le_div ((wp _ _).monotone hab _) (by rfl)⟩

syntax "cwp[" term "]⟦" cpgcl_prog "⟧" : term

macro_rules
| `(cwp[$O]⟦ $p ⟧) => `(pGCL.cwp $O pgcl {$p})

@[app_unexpander pGCL.cwp]
def cwpUnexpander : Lean.PrettyPrinter.Unexpander
| `($(_) $o $c) => do
    let c ← match c with | `(pgcl {$c}) => pure c | _ => `(cpgcl_prog| ~ $c)
    `(cwp[$o]⟦$c⟧)
| _ => throw ()

theorem park_induction {O: Optimization} {b : BExpr ϖ} {C : pGCL ϖ} {f}
    (I) (h : (Φ O b C f) I ≤ I) : wp[O]⟦while ~b { ~C }⟧ f ≤ I :=
  lfp_le _ (by simp; exact h)
theorem park_coinduction {O: Optimization} {b : BExpr ϖ} {C : pGCL ϖ} {f}
    (I) (h : I ≤ p[b].pickProb (wlp[O]⟦~C⟧ I) f) : wlp[O]⟦while ~b { ~C }⟧ f ≥ I :=
  le_gfp _ (by simp; exact h)

noncomputable def Ψ (f : Exp ϖ) (Φ : Exp ϖ →o Exp ϖ) : Exp ϖ →o Exp ϖ :=
  ⟨(Φ · ⊓ f), fun a b hab ↦ by simp; refine inf_le_of_left_le (Φ.mono hab)⟩

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

omit [DecidableEq ϖ] in
theorem k_coinduction {Φ : Exp ϖ →o Exp ϖ} {f} (k : ℕ) (h : f ≤ Φ ((Ψ f Φ)^[k] f)) :
    f ≤ gfp Φ := by
  sorry
  -- apply le_trans h; clear h
  -- apply le_gfp
  -- have h₁ := Ψ_iter_antitone f Φ (by omega : 0 ≤ k)
  -- have h₂ := k_induction_park Φ f k
  -- simp at h₁
  -- replace := h₂.mp ?_
  -- · apply le_trans this
  --   sorry
  -- · apply le_trans _ h₁
  --   apply?

  -- apply le_trans (Ψ_iter_antitone f Φ (by omega : 0 ≤ k))
  -- have := le_gfp Φ ((k_induction_park Φ f k).mp h)
  -- (gfp_le Φ ((k_induction_park Φ f k).mp h)).trans (Ψ_iter_antitone f Φ (by omega : 0 ≤ k))

theorem park_k_induction {O: Optimization} {b : BExpr ϖ} [DecidablePred b] {C : pGCL ϖ} {f} (k : ℕ)
    (I : Exp ϖ) (h : Φ O b C f ((fun x ↦ (i[b] * wp[O]⟦~C⟧ x + i[b.not] * f) ⊓ I)^[k] I) ≤ I) :
    wp[O]⟦while ~b { ~C }⟧ f ≤ I := k_induction k h

theorem park_k_coinduction {O: Optimization} {b : BExpr ϖ} [DecidablePred b] {C : pGCL ϖ} {f : ProbExp ϖ} (k : ℕ)
    (I : ProbExp ϖ) (h : fΦ' O b C f ((fun x ↦ (p[b] * wlp[O]⟦~C⟧ x + p[b.not] * f) ⊓ I)^[k] I) ≤ I) :
    I ≤ wlp[O]⟦while ~b { ~C }⟧ f := sorry

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
  simp only [wp.prob_apply, wp.seq_apply, wp.assign_apply, BExpr.not, BExpr.and_apply,
    BExpr.lt_apply, Ψ, coe_mk, Function.iterate_succ, Function.comp_apply, Exp.mul_subst,
    Exp.add_subst, Exp.one_subst, Exp.min_subst, Exp.add_apply, Exp.mul_apply, BExpr.iver, ite_mul,
    one_mul, zero_mul, BExpr.le_apply, Exp.ofNat_apply', Nat.cast_ofNat, Exp.one_apply,
    Exp.top_apply]
  simp only [Exp.const, Function.iterate_zero, id_eq, Exp.min_subst, Exp.add_subst, Exp.mul_subst,
    Exp.one_subst]
  -- simp only [ProbExp.pick, States.instSubst, String.reduceEq, ↓reduceIte, Nat.cast_add,
  --   Nat.cast_one, Pi.add_apply, Pi.mul_apply, mul_ite, mul_zero, Pi.sub_apply, Pi.one_apply,
  --   nonpos_iff_eq_zero, zero_add, Nat.reduceAdd]
  if σ "toSend" = 0 then
    simp_all only [not_neg, false_and, ↓reduceIte, zero_add, zero_le, add_zero]
    sorry
  else if σ "toSend" = 1 then
    simp_all only [one_ne_zero, not_false_eq_true, Nat.one_le_ofNat, ↓reduceIte,
      Nat.not_ofNat_lt_one, add_zero]
    sorry
  else if h : σ "toSend" = 2 then
    simp_all only [OfNat.ofNat_ne_zero, not_false_eq_true, OfNat.ofNat_ne_one]
    sorry
    -- split
  else if h : σ "toSend" = 3 then
    simp_all only [OfNat.ofNat_ne_zero, not_false_eq_true, OfNat.ofNat_ne_one, OfNat.ofNat_eq_ofNat,
      Nat.succ_ne_self, le_refl, ↓reduceIte, lt_self_iff_false, add_zero]
    sorry
  else if h : σ "toSend" = 4 then
    simp_all only [OfNat.ofNat_ne_zero, not_false_eq_true, OfNat.ofNat_ne_one, OfNat.ofNat_eq_ofNat,
      Nat.reduceEqDiff, Nat.succ_ne_self]
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

@[simp]
theorem _root_.ENNReal.toReal_ite [Decidable b] :
    ENNReal.toReal (if b then x else y) = if b then x.toReal else y.toReal := by
  split_ifs <;> rfl
@[simp]
theorem _root_.ENNReal.ite_ne_top [Decidable b] {x y : ENNReal} :
    ¬(if b then x else y) = ⊤ ↔ if b then x ≠ ⊤ else y ≠ ⊤ := by
  split_ifs <;> rfl
@[simp]
theorem _root_.ENNReal.sub_inv_ne_zero {n : ENNReal} (h : 1 < n) : 1 - n ⁻¹ ≠ (0 : ENNReal) := by
  refine pos_iff_ne_zero.mp ?_
  simp [h]

-- theorem Exp.div_le_iff_le_mul {a b c : Exp ϖ} (hb0 : b ≠ 0 ∨ c ≠ ⊤) (hbt : b ≠ ⊤ ∨ c ≠ 0) :
--     a / b ≤ c ↔ a ≤ c * b := by
--   constructor
--   · intro h σ; specialize h σ
--     replace hb0 : ¬b σ = 0 ∨ ¬c σ = ⊤ := by
--       contrapose! hb0
--       simp_all
--       rcases hb0 with (hb0 | hb0)
--       · contrapose! hb0
--         simp_all
--     replace hbt : ¬b σ = ⊤ ∨ ¬c σ = 0 := by
--       rcases hbt with (hbt | hbt)
--       · grind
--     simp_all
--     rw [Exp.div_le_iff_le_mul]

@[simp] theorem BExpr.iver_subst {b : BExpr ϖ} {x : ϖ} {e : Exp ϖ} : i[b][x ↦ e] = i[b[x ↦ e]] :=
  rfl
@[simp] theorem BExpr.probOf_subst {b : BExpr ϖ} {x : ϖ} {e : Exp ϖ} : p[b][x ↦ e] = p[b[x ↦ e]] :=
  rfl
@[simp] theorem BExpr.eq_subst {l r : Exp ϖ} {x : ϖ} {e : Exp ϖ} :
  (BExpr.eq l r)[x ↦ e] = BExpr.eq l[x ↦ e] r[x ↦ e] := rfl
@[simp] theorem BExpr.and_subst {l r : BExpr ϖ} {x : ϖ} {e : Exp ϖ} :
  (BExpr.and l r)[x ↦ e] = BExpr.and l[x ↦ e] r[x ↦ e] := rfl
@[simp] theorem BExpr.not_subst {l : BExpr ϖ} {x : ϖ} {e : Exp ϖ} :
  (BExpr.not l)[x ↦ e] = BExpr.not l[x ↦ e] := rfl
@[simp] theorem Exp.const_subst {y : ϖ} {x : ϖ} {e : Exp ϖ} :
    (Exp.const y)[x ↦ e] = if x = y then e else Exp.const y := by
  ext; simp; split_ifs <;> simp_all [const]

omit [DecidableEq ϖ] in
@[simp] theorem BExpr.mk_apply : (⟨b, h⟩ : BExpr ϖ) σ ↔ b σ := by rfl

@[simp] theorem BExpr.true_apply : (true : BExpr ϖ) σ ↔ true := by rfl
@[simp] theorem BExpr.false_apply : (false : BExpr ϖ) σ ↔ false := by rfl
@[simp] theorem BExpr.true_subst {x : ϖ} {A : Exp ϖ} : (true : BExpr ϖ)[x ↦ A] = true := by rfl
@[simp] theorem BExpr.false_subst {x : ϖ} {A : Exp ϖ} : (false : BExpr ϖ)[x ↦ A] = false := by rfl

@[simp] theorem BExpr.false_and {x : BExpr ϖ} : BExpr.and false x = false := by ext; simp
@[simp] theorem BExpr.true_and {x : BExpr ϖ} : BExpr.and true x = x := by ext; simp
@[simp] theorem BExpr.and_false {x : BExpr ϖ} : BExpr.and x false = false := by ext; simp
@[simp] theorem BExpr.and_true {x : BExpr ϖ} : BExpr.and x true = x := by ext; simp
@[simp] theorem BExpr.not_false : BExpr.not (false : BExpr ϖ) = true := by ext; simp
@[simp] theorem BExpr.not_true : BExpr.not (true : BExpr ϖ) = false := by ext; simp

@[simp] theorem BExpr.eq_of {a b : Exp ϖ} (h : a = b) : BExpr.eq a b = true := by
  subst_eqs; ext; simp
@[simp] theorem BExpr.neq_of {a b : Exp ϖ} (h : ∀ σ, a σ ≠ b σ) : BExpr.eq a b = false := by
  ext σ; simp; contrapose! h; use σ

@[simp] theorem BExpr.iver_true : (i[true] : Exp ϖ) = 1 := by rfl
@[simp] theorem BExpr.iver_false : (i[false] : Exp ϖ) = 0 := by rfl
@[simp] theorem BExpr.probOf_true : (p[true] : ProbExp ϖ) = 1 := by rfl
@[simp] theorem BExpr.probOf_false : (p[false] : ProbExp ϖ) = 0 := by rfl

@[simp] theorem wtf {x : ϖ} {e : Exp ϖ} : (@OfNat.ofNat (Exp ϖ) 2 instOfNatAtLeastTwo)[x ↦ e] = 2 := by rfl
@[simp] theorem wtf₃ {x : ϖ} {e : Exp ϖ} : (3 : Exp ϖ)[x ↦ e] = 3 := by rfl
@[simp] theorem wtf₈ {x : ϖ} {e : Exp ϖ} : (8 : Exp ϖ)[x ↦ e] = 8 := by rfl
@[simp] theorem wtf'₂ : 2⁻¹ ⊓ (1 : Exp ϖ) = 2⁻¹ := by ext σ; simp
@[simp] theorem wtf'₃ : 3⁻¹ ⊓ (1 : Exp ϖ) = 3⁻¹ := by ext σ; simp
@[simp] theorem wtf'₈ : 8⁻¹ ⊓ (1 : Exp ϖ) = 8⁻¹ := by ext σ; simp
@[simp] theorem Exp.one_sub_half : (1 : Exp ϖ) - 2⁻¹ = 2⁻¹ := by
  ext σ; simp
@[simp] theorem ProbExp.one_sub_half : (1 : ProbExp ϖ) - ProbExp.inv 2 = ProbExp.inv 2 := by
  ext σ; simp

@[simp] theorem ProbExp.inf_subst {X Y : ProbExp ϖ} {x : ϖ} {A : Exp ϖ} :
    (X ⊓ Y)[x ↦ A] = X[x ↦ A] ⊓ Y[x ↦ A] := by rfl
@[simp] theorem ProbExp.mul_inf {s X Y : ProbExp ϖ} :
    s * (X ⊓ Y) = s * X ⊓ s * Y := by ext; simp [mul_min]
@[simp] theorem ProbExp.mul_le_left {s X : ProbExp ϖ} :
    s * X ≤ X := by intro σ; simp; exact mul_le_of_le_one_left' (le_one s σ)
@[simp] theorem ProbExp.mul_le_right {s X : ProbExp ϖ} :
    X * s ≤ X := by intro σ; simp; exact mul_le_of_le_one_right' (le_one s σ)
@[simp] theorem ProbExp.inf_mul_right {s X : ProbExp ϖ} :
    X ⊓ X * s = X * s := by ext; simp

@[simp] theorem BExpr.coe_probOf : ProbExp.exp_coe p[x] = i[x] := by rfl

example {X : Exp ϖ} :
    cwp[O]⟦skip⟧ X = X := by
  ext; simp [cwp, wlp]
example {X : Exp String} :
      cwp[O]⟦{x := 2; y := 1} [2⁻¹] {x := 3; y := 2} ; observe(x=2)⟧ X
    = X["y" ↦ 1]["x" ↦ 2] := by
  simp [cwp, wlp, wp, ProbExp.pick, ProbExp.pickProb]
  rw [mul_comm]
  ext σ
  simp [ENNReal.mul_div_cancel_right]
example {X : Exp String} :
      cwp[O]⟦
        {c₁ := 0} [2⁻¹] {c₁ := 1} ;
        {c₂ := 0} [2⁻¹] {c₂ := 1} ;
        observe(¬ (c₁ = 1 ∧ c₂ = 1))
      ⟧ X
    = 3⁻¹ * (X["c₂" ↦ 0]["c₁" ↦ 0] + X["c₂" ↦ 1]["c₁" ↦ 0] + X["c₂" ↦ 0]["c₁" ↦ 1]) := by
  simp [cwp, wlp, wp, ProbExp.pick, ProbExp.pickProb]
  simp [← mul_assoc]
  ring_nf
  simp [← mul_add, ← add_mul]
  rw [mul_comm, mul_div_assoc]
  congr! 1
  ext σ
  simp
  refine ENNReal.eq_inv_of_mul_eq_one_left ?_
  simp [ENNReal.div_mul, ENNReal.mul_div_cancel_right, ENNReal.div_eq_one_iff]
  sorry

example :
      cwp[O]⟦
        {aliceDunnit := 0} [3⁻¹] {aliceDunnit := 1} ;
        if aliceDunnit = 1 then
          {withGun := 0} [3⁻¹] {withGun := 1}
        else
          {withGun := 0} [8⁻¹] {withGun := 1}
        end ;
        observe(withGun = gunFound)
      ⟧ (pgcl_aexp { aliceDunnit })
    = pgcl_aexp { ([gunFound = 0] * 16/19) + ([gunFound = 1] * 32/53) } := by
  simp [cwp, wp, wlp, ite]
  ring_nf
  sorry

  -- simp [← mul_assoc]

  -- ext σ
  -- simp only [cwp, wp, ProbExp.pick, coe_mk, ite, wp.prob, mul_add, ← mul_assoc, Pi.mul_apply,
  --   Pi.add_apply, States.subst_apply, ↓reduceIte, zero_ne_one, Bool.false_eq_true,
  --   BExpr.false_probOf, ProbExp.inv_apply, OfNat.ofNat_ne_zero, Nat.cast_ofNat, zero_mul,
  --   Pi.sub_apply, Pi.one_apply, add_zero, tsub_zero, one_mul, zero_add, BExpr.true_probOf,
  --   tsub_self, wlp, ProbExp.pickProb, ProbExp.mk_vcoe, mk_comp_mk, Function.comp_apply,
  --   ProbExp.mul_apply, ProbExp.one_apply, mul_one, ProbExp.coe_apply, String.reduceEq,
  --   Nat.cast_zero, mul_zero, Nat.cast_one, Pi.div_apply, ENNReal.add_div]
  -- ring_nf
  -- simp [BExpr.iver, BExpr.probOf]
  -- apply (ENNReal.toReal_eq_toReal_iff' ?_ ?_).mp
  -- · repeat rw [ENNReal.toReal_add]
  --   · simp
  --     (repeat rw [ENNReal.toReal_add]) <;> simp [ENNReal.ite_ne_top, ENNReal.mul_ne_top]
  --     split_ifs <;> grind
  --   · simp [ENNReal.div_ne_top]
  --   · simp [ENNReal.div_ne_top]
  --   · split_ifs <;> simp [ENNReal.div_ne_top, ENNReal.mul_ne_top]
  --   · split_ifs <;> simp [ENNReal.div_ne_top]
  -- · split_ifs <;> simp [ENNReal.div_ne_top, ENNReal.mul_ne_top]
  -- · split_ifs <;> simp [ENNReal.div_ne_top]

@[gcongr]
theorem cool {C : pGCL ϖ} (h : X ≤ Y) : wlp[O]⟦~C⟧ X ≤ wlp[O]⟦~C⟧ Y := by
  gcongr

theorem cwp_rule (P : Exp ϖ) (Q : ProbExp ϖ) (h : P / Q ≤ Y)
    (hwp : wp[O]⟦~C⟧ X ≤ P) (hwlp : Q ≤ wlp[O]⟦~C⟧ 1) : cwp[O]⟦~C⟧ X ≤ Y := by
  simp [cwp]
  simp only [DFunLike.coe] at hwlp ⊢
  simp only [toFun_eq_coe] at hwlp ⊢
  grw [← h, hwp]
  gcongr
  exact hwlp

open scoped Classical in
example :
      cwp[O]⟦
        while x = 0 {
          {x := 1} [2⁻¹] {x := 0} ;
          observe(x = 1)
        }
      ⟧ X
    ≤ pgcl_aexp { ([x = 0] * (1/2) * ~X["x" ↦ 1]) + [¬x = 0] * ~X } := by
  let Q : Exp String := pgcl_aexp { ([x = 0] * (1/2) * ~X["x" ↦ 1]) + [¬x = 0] * ~X }
  let P : ProbExp String := 1
  apply cwp_rule Q P
  · simp [P, Q]
  · grw [park_k_induction 1 _]
    simp [Φ, Q, ProbExp.pick]
  · grw [← park_k_coinduction 1 _]
    apply ProbExp.le_one

@[gcongr]
theorem Exp.le_subst {X Y : Exp ϖ} {x : ϖ} {A : Exp ϖ} (h : X ≤ Y) : X[x ↦ A] ≤ Y[x ↦ A] :=
  fun _ ↦ h _

@[gcongr]
theorem ProbExp.le_subst {X Y : ProbExp ϖ} {x : ϖ} {A : Exp ϖ} (h : X ≤ Y) : X[x ↦ A] ≤ Y[x ↦ A] :=
  fun _ ↦ h _

@[simp]
theorem States.subst_rfl {σ : States ϖ} {c : ϖ} : σ[c ↦ σ c] = σ := by
  ext; simp +contextual

theorem Exp.iver_eq_mul_cases (c : ϖ) (x : Exp ϖ) :
    i[pgcl_bexp { ~(Exp.const c) = ~d }] * x = i[pgcl_bexp { ~(Exp.const c) = ~d }] * x[c ↦ d] := by
  ext σ
  simp [BExpr.iver, const]
  split_ifs with h
  · simp_all [← h]
  · simp

@[simp] theorem States.subst_same {σ : States ϖ} {x : ϖ} {A B : ENNReal} :
    σ[x ↦ B][x ↦ A] = σ[x ↦ A] := by
  ext σ; simp; grind
@[simp] theorem States.subst_comm_ne {σ : States ϖ} {x y : ϖ} {A B : ENNReal}
    (h : x ≠ y) : σ[x ↦ A][y ↦ B] = σ[y ↦ B][x ↦ A] := by
  ext σ; simp; grind
@[simp] theorem Exp.subst_same {X : Exp ϖ} {x : ϖ} {A B : Exp ϖ} :
    X[x ↦ B][x ↦ A] = X[x ↦ B[x ↦ A]] := by
  ext σ; simp
@[simp] theorem ProbExp.subst_same {X : ProbExp ϖ} {x : ϖ} {A B : Exp ϖ} :
    X[x ↦ B][x ↦ A] = X[x ↦ B[x ↦ A]] := by
  ext σ; simp
theorem Exp.subst_sort_nat [Preorder ϖ] {X : Exp ϖ} {x y : ϖ} {A B : ℕ}
    (h : x < y := by simp [List.lex_eq_true_iff_lt.mp]) :
    X[x ↦ (A : Exp ϖ)][y ↦ (B : Exp ϖ)] = X[y ↦ (B : Exp ϖ)][x ↦ (A : Exp ϖ)] := by
  ext σ; simp; rw [States.subst_comm_ne]; exact h.ne.symm

omit [DecidableEq ϖ] in
@[simp] theorem Epr.inf_zero {X : Exp ϖ} : X ⊓ 0 = 0 := by ext; simp

open scoped Classical in
example {a b : ENNReal} (ha : a ≤ 1) (hb : b ≤ 1) :
      wp[O]⟦
        { t := 1 } [2⁻¹] { t := 2 } ;
        c := 1 ;
        while c = 1 {
          if t = 1 then
            {c := 0} [~⟨fun _ ↦ a, sorry⟩] {t := 2}
          else
            {c := 0} [~⟨fun _ ↦ b, sorry⟩] {t := 1}
          end
        }
      ⟧ pgcl_aexp {[turn = 1]}
    ≤ 2⁻¹ * (1 + a / (a + b - a * b) + (1 - b) * (a / (a + b - a * b))) := by
  -- intro σ
  simp only [wp.seq_apply, wp.assign_apply, wp.prob_apply]
  let α : ENNReal := a / (a + b - a * b)
  let β : ENNReal := (1 - b) * α
  let I : Exp String := pgcl_aexp {
    [t = 1 ∧ c = 0] + ([t = 1 ∧ c = 1] * ~α) + ([t = 2 ∧ c = 1] * ~β)
  }
  grw [park_k_induction 1 I]
  · simp [ProbExp.pick, ← mul_add]
    simp [I, α, β]
    rw [add_assoc]
    nth_rw 2 [mul_add]
    set f : Exp String := 2⁻¹ * (↑(a / (a + b - a * b)) + ↑((1 - b) * (a / (a + b - a * b))))
    simp
    rw [← zero_add (a:=f)]
    gcongr
    · intro; simp
    · simp [f]; rfl
  · simp [Φ, ite]
    simp [ProbExp.pick]
    nth_rw 2 [Exp.iver_eq_mul_cases]
    simp
    rw [Exp.iver_eq_mul_cases]
    simp
    have ha : ∀ (x : String) e, Exp.instSubst.subst (fun _ ↦ a) x e = a := by simp [Exp.instSubst]; rfl
    have hb : ∀ (x : String) e, Exp.instSubst.subst (fun _ ↦ b) x e = b := by simp [Exp.instSubst]; rfl
    simp [ha, hb]
    simp [I]
    nth_rw 6 [add_comm]
    gcongr
    ·
      sorry
    · sorry
  --   simp [α, β]
  --   intro σ
  --   simp
  --   have : σ "t" ∈ ({1, 2} : Set _) := by sorry
  --   have : σ "c" ∈ ({0, 1} : Set _) := by sorry
  --   simp [BExpr.iver, Exp.const, ite_and, Exp.ennreal_coe]
  --   split_ifs <;> simp_all
  --   ·
  --     simp only [mul_min, -inf_le_iff]
  --     refine (ENNReal.toReal_le_toReal ?_ ?_).mp ?_
  --     · simp_all
  --       sorry
  --     · simp_all
  --       sorry
  --     ·
  --       have : 0 < a + b - a * b := by sorry
  --       have : a * b ≤ a + b := by sorry
  --       have : a + b - a * b ≠ 0 := by sorry
  --       have : a ≠ ⊤ := by sorry
  --       have : b ≠ ⊤ := by sorry
  --       simp_all [ENNReal.toReal_sub_of_le, ENNReal.toReal_min]
  --       rw [ENNReal.toReal_min] <;> simp_all [ENNReal.toReal_add, ENNReal.mul_ne_top, ENNReal.add_ne_top, Exp.ennreal_coe, ENNReal.div_ne_top]
  --       · simp
  --       · sorry
  --       · sorry

  --   nth_rw 2 [Exp.iver_eq_mul_cases]
  --   simp
  --   -- simp
  --   intro σ
  --   simp [BExpr.iver, Exp.const]
  --   split_ifs
  --   · simp_all
  --   · simp_all
  --   · simp_all

  --   have q := (by simp [List.lex_eq_true_iff_lt.mp] : "c" < "t")

  --   simp [← Exp.subst_sort_nat q]
  --   have := Exp.subst_sort_nat (ϖ:=String) (X:=X["c" ↦ 0]) (x:="c") (y:="t") (A:=1) (B:=1)
  --   have := @Exp.subst_sort_nat
  --   simp at this

  --   simp only [String.lt_iff_toList_lt, String.toList, ↓Char.isValue, List.cons_lex_cons,
  --     Char.reduceLT, decide_true, Char.reduceBEq, List.lex_nil, Bool.and_self, Bool.or_false,
  --     List.lex_eq_true_iff_lt.mp, Exp.subst_nat_eq, Nat.cast_zero, Nat.cast_one,
  --     forall_const] at this
  --   simp [← this]
  --   simp [Exp.subst_sort_nat, List.lex_eq_true_iff_lt.mp]
  --   have : ['c'] < ['t'] := by exact List.lex_eq_true_iff_lt.mp rfl
  --   simp [Exp.subst_sort]

  -- simp only [ProbExp.pick]
  -- simp only [wp.seq, wp.prob, wp.assign, -coe_mk, -comp_coe, -Function.comp_apply]
  -- simp only [coe_mk, comp_coe, -Function.comp_apply]
  -- simp
  -- -- simp [← mul_add]
  -- -- refine (ENNReal.inv_mul_le_iff ?_ ?_).mpr ?_ <;> try simp
  -- let I : Exp ϖ := sorry
  -- grw [park_induction I]
  -- · sorry
  -- · sorry

noncomputable def RabinsMutualExclusion : pGCL String := pgcl {
  while 1 < i {
    n := i ;
    while 0 < n {
      {d := 0} [2⁻¹] {d := 1} ;
      i := i - d ;
      n := n - 1
    }
  }
}

noncomputable def RabinsMutualExclusion.pre : ProbExp String :=
  ⟨pgcl_aexp { [i = 1] + [1 < i] * (2/3) }, by
    intro i; simp [BExpr.iver]; split_ifs <;> simp_all
    refine ENNReal.div_le_of_le_mul ?_
    norm_cast⟩
noncomputable def RabinsMutualExclusion.post : ProbExp String :=
  ⟨pgcl_aexp { [i = 1] }, by simp⟩

noncomputable def Exp.fakePow (x y : Exp ϖ) : Exp ϖ :=
  fun σ ↦ (x σ)^(FloorSemiring.floor (y σ).toNNReal : ℕ)

@[simp]
theorem Exp.fakePow_subst {X Y e : Exp ϖ} {x : ϖ} :
    (X.fakePow Y)[x ↦ e] = X[x ↦ e].fakePow Y[x ↦ e] := by rfl
@[simp]
theorem Exp.fakePow_apply {X Y : Exp ϖ} :
    (X.fakePow Y) σ = (X σ)^(FloorSemiring.floor (Y σ).toNNReal) := by rfl

@[simp] theorem BExpr.zero_le {X : Exp ϖ} : BExpr.le 0 X = true := by ext; simp
@[simp] theorem BExpr.le_refl {X : Exp ϖ} : BExpr.le X X = true := by ext; simp
@[simp] theorem BExpr.le_subst {X Y e : Exp ϖ} {x : ϖ} :
    (BExpr.le X Y)[x ↦ e] = BExpr.le X[x ↦ e] Y[x ↦ e] := rfl
@[simp] theorem BExpr.lt_refl {X : Exp ϖ} : BExpr.lt X X = false := by ext; simp
@[simp] theorem BExpr.lt_subst {X Y e : Exp ϖ} {x : ϖ} :
    (BExpr.lt X Y)[x ↦ e] = BExpr.lt X[x ↦ e] Y[x ↦ e] := rfl

theorem ProbExp.gcongr {X Y : ProbExp ϖ} (h : ProbExp.exp_coe X ≤ ProbExp.exp_coe Y) : X ≤ Y := by apply h
theorem ProbExp.coe_add {X Y : ProbExp ϖ} :
    ProbExp.exp_coe (X + Y) = (X.exp_coe + Y.exp_coe) ⊓ 1 := by
  ext σ
  simp
theorem ProbExp.coe_sub {X Y : ProbExp ϖ} :
    ProbExp.exp_coe (X - Y) = (X.exp_coe - Y.exp_coe) ⊓ 1 := by
  ext σ
  simp
  apply le_add_right
  simp
theorem ProbExp.coe_mul {X Y : ProbExp ϖ} :
    ProbExp.exp_coe (X * Y) = (X.exp_coe * Y.exp_coe) := by
  ext σ
  simp only [exp_coe_apply, mul_apply, Exp.mul_apply]

@[simp]
theorem Exp.one_ne_top : (1 : Exp ϖ) ≠ ⊤ := by
  intro h
  have := congrFun h (fun _ ↦ 0)
  simp at this
@[simp, grind]
theorem BExpr.iver_ne_top {b : BExpr ϖ} : i[b] ≠ ⊤ := by
  have : i[b] ≤ 1 := by simp
  contrapose! this
  rw [this]
  simp
@[simp, grind]
theorem BExpr.iver_apply_ne_top {b : BExpr ϖ} : i[b] σ ≠ ⊤ := by
  have : i[b] σ ≤ 1 := by simp
  contrapose! this
  rw [this]
  simp


open RabinsMutualExclusion in
example : pre ≤ wlp[O]⟦~RabinsMutualExclusion⟧ post := by
  simp [RabinsMutualExclusion, pre, post]
  let Iₒ := pre
  let invar1 := pgcl_aexp {
    1 -
      ( [i = n] * ((n + 1) / ~(Exp.fakePow 2 pgcl_aexp {n}))
      + [i = n + 1] * (1 / ~(Exp.fakePow 2 pgcl_aexp {n})))
  }
  let invar2 := pgcl_aexp {
      ( [i = n] * (n / ~(Exp.fakePow 2 pgcl_aexp {n}))
      + [i = n + 1] * (1 / ~(Exp.fakePow 2 pgcl_aexp {n})))
  }
  let Iᵢ : ProbExp String := ⟨pgcl_aexp { [0 ≤ n ∧ n ≤ i] * (((2/3) * ~invar1) + ~invar2) }, by
    simp [invar1, invar2]
    intro σ
    simp [BExpr.iver]
    split_ifs <;> simp_all
    · sorry
    · sorry
    · sorry
    ⟩
  grw [park_coinduction Iₒ]
  · rfl
  · simp
    grw [park_coinduction Iᵢ]
    · simp [Iₒ, Iᵢ, pre, invar1, invar2]
      have : i[pgcl_bexp {i = i + 1}] = 0 := by
        ext σ; simp [BExpr.iver]
        set i := Exp.const "i" σ
        sorry
      simp [this]
      simp [ProbExp.pickProb]
      apply ProbExp.gcongr
      simp [ProbExp.coe_add, ProbExp.coe_sub, ProbExp.coe_mul]
      constructor
      ·
        nth_rw 1 [add_comm]
        gcongr
        · intro σ; simp
          set i := Exp.const "i" σ
          set i' := FloorSemiring.floor i.toNNReal
          rw [ENNReal.mul_sub]
          · simp
            simp [ENNReal.add_div, mul_add]
            ring_nf
            sorry
          · simp; intro
            suffices ¬(2 : ENNReal) = ⊤ * 3 by refine ENNReal.div_ne_top ?_ ?_ <;> simp
            simp
        · intro σ; simp [BExpr.iver]; split_ifs <;> simp_all
      · intro; simp [BExpr.iver]; split_ifs <;> simp_all
        refine (ENNReal.div_le_iff ?_ ?_).mpr ?_ <;> norm_cast
    · simp [Iᵢ, invar1, invar2]
      apply ProbExp.gcongr
      simp
      rw [Exp.iver_eq_mul_cases]
      simp
      have : i[pgcl_bexp {n = n + 1}] = 0 := by sorry
      simp [this, ProbExp.pick, Iₒ, pre]
      intro σ
      simp
      refine (ENNReal.toReal_le_toReal ?_ ?_).mp ?_
      ·
        simp
        apply ENNReal.mul_ne_top
        · simp
        · simp
          constructor
          · apply ENNReal.mul_ne_top
            · finiteness
            · finiteness
          · apply ENNReal.mul_ne_top
            · sorry
            · simp
              sorry
      · simp
        sorry
      · sorry

example : wp[O]⟦
      x' := x ;
      n' := n ;
      while x < n {
        { x := x + 2 } [2⁻¹] { x := x - 1 } ;
        tick(1)
      }
    ⟧ 0 ≤ 2 := by
  simp
  let I : Exp String := pgcl_aexp { 2 * ((n + 1) - x) }
  grw [park_k_induction 0 I]
  · sorry
  · simp [Φ, ProbExp.pick]
    simp [I]
    nth_rw 2 [mul_add]
    nth_rw 2 [mul_add]
    simp [← mul_assoc]
    have : 2⁻¹ * (2 : Exp String) = 1 := by ext; simp; refine ENNReal.inv_mul_cancel ?_ ?_ <;> simp
    simp [this]
    simp [← add_assoc]
    nth_rw 2 [add_comm]
    simp [← add_assoc]
    have : 2⁻¹ + 2⁻¹ = (1 : Exp String) := by ext; simp; exact ENNReal.inv_two_add_inv_two
    simp [this]
    intro σ
    simp [BExpr.lt, BExpr.iver, Exp.const]
    sorry
    -- eq_as_reals
    -- split_ifs
    -- · rw [ENNReal.mul_sub] <;> try simp only [ne_eq, ENNReal.ofNat_ne_top, not_false_eq_true,
    --   implies_true]
    --   simp [mul_add]
    --   have : Exp.const "n" σ ≠ ⊤ := by sorry
    --   refine (ENNReal.toReal_le_toReal ?_ ?_).mp ?_
    --   · simp [this]
    --   · simp [this, ENNReal.mul_eq_top]
    --   · rw [ENNReal.toReal_sub_of_le]
    --     · simp
    --       rw [ENNReal.toReal_add]
    --       · rw [ENNReal.toReal_add] <;> try finiteness
    --         simp
    --         rw [ENNReal.toReal_add] <;> try finiteness
    --         simp
    --         rw [ENNReal.toReal_sub_of_le]
    --         · rw [ENNReal.toReal_add] <;> try finiteness
    --           simp
    --           rw [ENNReal.toReal_sub_of_le]
    --           · repeat rw [ENNReal.toReal_add] <;> try finiteness
    --             simp
    --             rw [ENNReal.toReal_sub_of_le] <;> try finiteness
    --             · simp
    --               linarith
    --             · simp
    --           · simp
    --             sorry
    --           · finiteness
    --         · sorry
    --         · finiteness
    --       · finiteness
    --       · finiteness
    --     · suffices 2 * Exp.const "x" σ ≤ 2 * Exp.const "n" σ by
    --         apply le_trans this; exact le_self_add
    --       gcongr
    --     · simp [ENNReal.mul_eq_top, this]

    -- · simp
    -- ring_nf
    -- grind

    -- ring_nf
    -- intro σ
    -- simp [BExpr.lt, BExpr.iver]
    -- simp [ENNReal.inv_mul_cancel]
    -- simp [I]
    -- split_ifs
    -- · simp_all
    -- · simp_all
    -- · simp_all
    -- split_ifs
    -- · simp_all
    --   sorry
    -- · simp_all
    --   sorry
    -- · simp_all
    --   sorry
    -- · simp_all
    --   simp [ENNReal.inv_mul_cancel]
    --   have : (2⁻¹ * (2 : ENNReal)) = 1 := by simp [ENNReal.inv_mul_cancel]
    --   sorry
    -- all_goals sorry

end pGCL
