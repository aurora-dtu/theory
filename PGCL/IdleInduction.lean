import PGCL.WeakestLiberalPre
import PGCL.Fix
import PGCL.KInduction

open Optimization.Notation
open OrderHom

namespace pGCL

variable {𝒱 : Type*} {ϖ : Γ[𝒱]} [DecidableEq 𝒱]

theorem wlp_apply_eq_wlp''_apply {C : pGCL ϖ} :
    wlp[O]⟦@C⟧ X σ = wlp''[O]⟦@C⟧ X σ := by
  simp [wlp'']

/-- An _Idle invariant_ is _Park invariant_ that holds for states with a set of fixed variables. -/
def IdleInvariant (g : 𝔼[ϖ, ENNReal] →o 𝔼[ϖ, ENNReal]) (b : BExpr ϖ) (φ : 𝔼[ϖ, ENNReal])
    (I : 𝔼[ϖ, ENNReal]) (S : Set 𝒱) (σ₀ : States ϖ) : Prop :=
  ∀ σ, (∀ v ∈ S, σ v = σ₀ v) → Φ[g] b φ I σ ≤ I σ

/-- _Idle induction_ is _Park induction_, but the engine is running (i.e. an initial state is
given), and as a consequence only states that vary over the modified variables need to be
considered for the inductive invariant. -/
theorem IdleInduction {b : BExpr ϖ} {C : pGCL ϖ} {φ : 𝔼[ϖ, ENNReal]} {I : 𝔼[ϖ, ENNReal]}
    {σ₀ : States ϖ} (h : IdleInvariant wp[O]⟦@C⟧ b φ I C.modsᶜ σ₀) :
    wp[O]⟦while @b { @C }⟧ φ σ₀ ≤ I σ₀ := by
  apply wp_le_of_fix (S:=C.modsᶜ)
  rw [wp_fix _ _ _ (by simp; rfl)]
  apply lfp_le
  intro σ'
  simp only [Φ, coe_mk, mk_apply, Pi.add_apply, Pi.mul_apply, Pi.iver_apply, Exp.fix_apply,
    Pi.compl_apply, compl_iff_not]
  simp [IdleInvariant, Φ] at h
  rw [← C.wp_fix I C.modsᶜ (by simp)]
  convert h (σ₀.cofix σ') ?_
  simp +contextual

/-- An _Idle coinvariant_ is _Park coinvariant_ that holds for states with a set of fixed variables.
-/
def IdleCoinvariant (g : 𝔼[ϖ, ENNReal] →o 𝔼[ϖ, ENNReal]) (b : BExpr ϖ) (φ : 𝔼[ϖ, ENNReal])
    (I : 𝔼[ϖ, ENNReal]) (S : Set 𝒱) (σ₀ : States ϖ) : Prop :=
  ∀ σ, (∀ v ∈ S, σ v = σ₀ v) → I σ ≤ Φ[g] b φ I σ

/-- _Idle coinduction_ is _Park coinduction_, but the engine is running (i.e. an initial state is
given), and as a consequence only states that vary over the modified variables need to be
considered for the coinductive invariant. -/
theorem IdleCoinduction {b : BExpr ϖ} {C : pGCL ϖ} {φ : 𝔼[ϖ, ENNReal]} {I : 𝔼[ϖ, ENNReal]}
    {σ₀ : States ϖ} (h : IdleCoinvariant wlp''[O]⟦@C⟧ b φ I C.modsᶜ σ₀) (hI : I ≤ 1) (hφ : φ ≤ 1) :
    I σ₀ ≤ wlp''[O]⟦while @b { @C }⟧ φ σ₀ := by
  apply le_wlp''_of_fix (S:=C.modsᶜ)
  rw [wlp''_fix _ _ _ (by simp; rfl)]
  simp [fix]
  rw [wlp''_loop_eq_gfp]
  fapply le_gfp_prob
  · exact fun i ↦ hI (σ₀.cofix i)
  intro σ'
  simp only [Exp.fix_apply, pΦ, coe_mk]
  simp [IdleCoinvariant, Φ] at h
  have := C.wlp_fix ⟨I, hI⟩ C.modsᶜ (by simp) (σ₀:=σ₀) (O:=O)
  simp [ProbExp.fix] at this
  rw [← this]
  convert h (σ₀.cofix σ') ?_
  · simp [Iverson.iver]; split <;> simp_all [wlp'', ProbExp.ofExp]
    apply hφ
  · simp +contextual

/-- A _Idle k-invariant_. -/
def IdleKInvariant (g : 𝔼[ϖ, ENNReal] →o 𝔼[ϖ, ENNReal]) (b : BExpr ϖ) (φ : 𝔼[ϖ, ENNReal]) (k : ℕ)
    (I : 𝔼[ϖ, ENNReal]) (S : Set 𝒱) (σ₀ : States ϖ) : Prop :=
    ∀ σ, (∀ v ∈ S, σ v = σ₀ v) → (Φ[g] b φ) ((Φ[g] b φ · ⊓ I)^[k] I) σ ≤ I σ

/-- _Idle k-induction_. -/
theorem IdleKInduction {b : BExpr ϖ} {C : pGCL ϖ} {φ : 𝔼[ϖ, ENNReal]} {I : 𝔼[ϖ, ENNReal]} (k : ℕ)
     {σ₀ : States ϖ} (h : IdleKInvariant wp[O]⟦@C⟧ b φ k I C.modsᶜ σ₀) :
    wp[O]⟦while @b { @C }⟧ φ σ₀ ≤ I σ₀ := by
  apply wp_le_of_fix (S:=C.modsᶜ)
  rw [wp_fix _ _ _ (by simp; rfl)]
  apply lfp_le_of_iter k
  intro σ'
  simp only [Φ, coe_mk, mk_apply, Pi.add_apply, Pi.mul_apply, Pi.iver_apply, Exp.fix_apply,
    Pi.compl_apply, compl_iff_not]
  simp [IdleKInvariant, Φ] at h
  have : ((fun x ↦
              (i[Exp.fix b C.modsᶜ σ₀] * wp[O]⟦@(C.fix C.modsᶜ σ₀)⟧ x
                + i[(Exp.fix b C.modsᶜ σ₀)ᶜ] * Exp.fix φ C.modsᶜ σ₀) ⊓ Exp.fix I C.modsᶜ σ₀)^[k]
          (Exp.fix I C.modsᶜ σ₀))
        = Exp.fix ((fun x ↦ (i[b] * wp[O]⟦@(C)⟧ x + i[(b)ᶜ] * φ) ⊓ I)^[k] I) C.modsᶜ σ₀ := by
      clear h σ'
      induction k with
      | zero => simp
      | succ k ih =>
        simp only [Function.iterate_succ', Function.comp_apply]
        ext σ'
        simp
        congr
        simp [ih]
        rw [← wp_fix _ _ _ (by simp)]
        simp
  simp [this]
  rw [← wp_fix _ _ _ (by simp)]
  convert h (σ₀.cofix σ') ?_
  · simp +contextual

/-- A _Idle k-coinvariant_. -/
def IdleKCoinvariant (g : ProbExp ϖ →o ProbExp ϖ) (b : BExpr ϖ) (φ : ProbExp ϖ) (k : ℕ)
    (I : ProbExp ϖ) (S : Set 𝒱) (σ₀ : States ϖ) : Prop :=
    ∀ σ, (∀ v ∈ S, σ v = σ₀ v) → I σ ≤ (pΦ[g] b φ) ((pΦ[g] b φ · ⊔ I)^[k] I) σ

/-- _Idle k-coinduction_. -/
theorem IdleKCoinduction {b : BExpr ϖ} {C : pGCL ϖ} {φ : ProbExp ϖ} {I : ProbExp ϖ} (k : ℕ)
     {σ₀ : States ϖ} (h : IdleKCoinvariant wlp[O]⟦@C⟧ b φ k I C.modsᶜ σ₀) :
    I σ₀ ≤ wlp[O]⟦while @b { @C }⟧ φ σ₀ := by
  apply le_wlp_of_fix (S:=C.modsᶜ)
  rw [wlp_fix _ _ _ (by simp; rfl)]
  simp [fix]
  fapply le_gfp_of_iter_prob k
  · intro; simp
  intro σ'
  simp [ProbExp.fix_apply, pΦ, coe_mk]
  simp [IdleKCoinvariant, pΦ] at h
  have : ((fun x ↦
                (p[Exp.fix b C.modsᶜ σ₀] * (wlp[O]⟦@(C.fix C.modsᶜ σ₀)⟧ x)
                  + (1 - p[Exp.fix b C.modsᶜ σ₀]) * (φ.fix C.modsᶜ σ₀))
                ⊔ ⟨⇑(I.fix C.modsᶜ σ₀), by intro; simp⟩)^[k]
            ⟨⇑(I.fix C.modsᶜ σ₀), by intro; simp⟩)
        = ProbExp.fix ((fun x ↦
                (p[b] * (wlp[O]⟦@C⟧ x) + (1 - p[b]) * φ) ⊔
                  ⟨⇑I, by intro; simp⟩)^[k]
            ⟨⇑I, by intro; simp⟩) C.modsᶜ σ₀ := by
    clear h σ'
    induction k with
    | zero => ext; simp
    | succ k ih =>
      simp only [Function.iterate_succ', Function.comp_apply]
      ext
      simp [ih]
      rw [← wlp_fix _ _ _ (by simp)]
      congr! 1
  simp [this]
  rw [← wlp_fix _ _ _ (by simp)]
  convert h (σ₀.cofix σ') ?_
  · simp +contextual

/-- A _Idle k-coinvariant_. -/
def IdleKCoinvariant'' (g : 𝔼[ϖ, ENNReal] →o 𝔼[ϖ, ENNReal]) (b : BExpr ϖ) (φ : 𝔼[ϖ, ENNReal])
    (k : ℕ) (I : 𝔼[ϖ, ENNReal]) (S : Set 𝒱) (σ₀ : States ϖ) : Prop :=
    ∀ σ, (∀ v ∈ S, σ v = σ₀ v) → I σ ≤ (Φ[g] b φ) ((Φ[g] b φ · ⊔ I)^[k] I) σ

def IdleKCoinvariant''.toIdleKCoinvariant {C : pGCL ϖ}
    (h : IdleKCoinvariant'' wlp''[O]⟦@C⟧ b φ k I C.modsᶜ σ₀) (hI : I ≤ 1) (hφ : φ ≤ 1) :
    IdleKCoinvariant wlp[O]⟦@C⟧ b ⟨φ, hφ⟩ k ⟨I, hI⟩ C.modsᶜ σ₀ := by
  intro σ hσ
  simp
  specialize h σ hσ
  convert h
  ext
  simp [pΦ, Φ, wlp'']
  rw [min_eq_left]
  swap
  · apply ProbExp.pick_le (p:=p[b])
    · simp
    · apply hφ
  congr! 4
  · clear h hσ σ
    induction k with
    | zero => ext; simp; apply hI
    | succ k ih =>
      simp only [Function.iterate_succ', Function.comp_apply]
      simp [ih]; clear ih
      ext σ
      simp
      have : ∀ (x y z : ENNReal), x ≤ y → (x = z → (min x y = z)) := by
        intro x y z h
        grind
      symm
      apply this
      · simp
        if hb : b σ then
          simp [hb]; apply hI
        else
          simp [hb]
          constructor
          · apply hφ
          · apply hI
      · congr
        simp [Iverson.iver]
        split_ifs <;> simp
        apply hφ
  · simp [Iverson.iver]
    split_ifs <;> simp

/-- _Idle k-coinduction_. -/
theorem IdleKCoinduction'' {b : BExpr ϖ} {C : pGCL ϖ} {φ : 𝔼[ϖ, ENNReal]} {I : 𝔼[ϖ, ENNReal]}
    (k : ℕ) {σ₀ : States ϖ} (h : IdleKCoinvariant'' wlp''[O]⟦@C⟧ b φ k I C.modsᶜ σ₀)
    (hI : I ≤ 1) (hφ : φ ≤ 1) :
    I σ₀ ≤ wlp''[O]⟦while @b { @C }⟧ φ σ₀ := by
  convert IdleKCoinduction k (IdleKCoinvariant''.toIdleKCoinvariant h hI hφ)
  simp [wlp'']
  congr
  ext σ
  simp
  apply hφ

end pGCL
