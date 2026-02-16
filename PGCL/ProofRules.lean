import PGCL.WeakestPre
import PGCL.WeakestLiberalPre
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.String.Basic
import ENNRealArith
import PGCL.KInduction

namespace pGCL

variable {𝒱 : Type*} {Γ : Γ[𝒱]} [DecidableEq 𝒱]

open OrderHom
open Optimization.Notation

/-- A program is _Almost Surely Terminating_ iff it's weakest pre-expectation without ticks of one
  is one is. -/
def AST (C : pGCL Γ) : Prop := wp[𝒟]⟦@C.st⟧ 1 = 1

noncomputable def cwp (O : Optimization) (C : pGCL Γ) : 𝔼[Γ, ENNReal] →o 𝔼[Γ, ENNReal] :=
  ⟨(wp[O]⟦@C⟧ · / wlp[O]⟦@C⟧ 1),
    fun a b hab σ ↦ ENNReal.div_le_div ((wp _ _).monotone hab _) (by rfl)⟩

syntax "cwp[" term "]⟦" cpgcl_prog "⟧" : term

macro_rules
| `(cwp[$O]⟦ $p ⟧) => `(pGCL.cwp $O pgcl {$p})

@[app_unexpander pGCL.cwp]
def cwpUnexpander : Lean.PrettyPrinter.Unexpander
| `($(_) $o $c) => do
    let c ← match c with | `(pgcl {$c}) => pure c | _ => `(cpgcl_prog| @ $c)
    `(cwp[$o]⟦$c⟧)
| _ => throw ()

/-- Encodes a program for analyzing _expected runtimes_ by removing all existing tick statements,
and adding `tick(1)` to every existing non-tick statement. -/
def ertEnc : pGCL Γ → pGCL Γ
  | pgcl {skip} => pgcl {tick(1); skip}
  | pgcl {@x := @A} => pgcl {tick(1); @x := @A}
  | pgcl {@C₁ ; @C₂} => pgcl {@C₁.ertEnc ; @C₂.ertEnc}
  | pgcl {{@C₁} [@p] {@C₂}} => pgcl {tick(1); {@C₁.ertEnc} [@p] {@C₂.ertEnc}}
  | pgcl {{@C₁} [] {@C₂}} => pgcl {tick(1); {@C₁.ertEnc} [] {@C₂.ertEnc}}
  | pgcl {while @b {@C'}} => pgcl {tick(1); while @b {@C'.ertEnc}}
  | pgcl {tick(@ _)} => pgcl {skip}
  | pgcl {observe(@ b)} => pgcl {tick(1); observe(@b)}

noncomputable def ert (O : Optimization) (C : pGCL Γ) : 𝔼[Γ, ENNReal] →o 𝔼[Γ, ENNReal] :=
  wp[O]⟦@C.ertEnc⟧

syntax "ert[" term "]⟦" cpgcl_prog "⟧" : term

macro_rules
| `(ert[$O]⟦ $p ⟧) => `(pGCL.ert $O pgcl {$p})

@[app_unexpander pGCL.ert]
def ertUnexpander : Lean.PrettyPrinter.Unexpander
| `($(_) $o $c) => do
    let c ← match c with | `(pgcl {$c}) => pure c | _ => `(cpgcl_prog| @ $c)
    `(ert[$o]⟦$c⟧)
| _ => throw ()

/-- A _Park invariant_. -/
def ParkInvariant (g : 𝔼[Γ, ENNReal] →o 𝔼[Γ, ENNReal]) (b : BExpr Γ) (φ : 𝔼[Γ, ENNReal])
    (I : 𝔼[Γ, ENNReal]) : Prop := Ψ[g] b φ I ≤ I

/-- _Park induction_. -/
theorem ParkInduction {b : BExpr Γ} {C : pGCL Γ} {φ : 𝔼[Γ, ENNReal]} {I : 𝔼[Γ, ENNReal]}
    (h : ParkInvariant wp[O]⟦@C⟧ b φ I) :
    wp[O]⟦while @b { @C }⟧ φ ≤ I := lfp_le _ h

/-- A _Park coinvariant_. -/
def ParkCoinvariant (g : ProbExp Γ →o ProbExp Γ) (b : BExpr Γ) (φ : ProbExp Γ)
    (I : ProbExp Γ) : Prop := I ≤ pΨ[g] b φ I

/-- _Park coinduction_. -/
theorem ParkCoinduction {b : BExpr Γ} {C : pGCL Γ} {φ : ProbExp Γ} {I : ProbExp Γ}
    (h : ParkCoinvariant wlp[O]⟦@C⟧ b φ I) :
    I ≤ wlp[O]⟦while @b { @C }⟧ φ := le_gfp _ h

/-- A _Park k-invariant_. -/
def ParkKInvariant (g : 𝔼[Γ, ENNReal] →o 𝔼[Γ, ENNReal]) (b : BExpr Γ) (φ : 𝔼[Γ, ENNReal]) (k : ℕ)
    (I : 𝔼[Γ, ENNReal]) : Prop := (Ψ[g] b φ) ((Ψ[g] b φ · ⊓ I)^[k] I) ≤ I

/-- _Park k-induction_. -/
theorem ParkKInduction {b : BExpr Γ} {C : pGCL Γ} {φ : 𝔼[Γ, ENNReal]} {I : 𝔼[Γ, ENNReal]} (k : ℕ)
    (h : ParkKInvariant wp[O]⟦@C⟧ b φ k I) :
    wp[O]⟦while @b { @C }⟧ φ ≤ I := lfp_le_of_iter k h

/-- A _Park k-coinvariant_. -/
def ParkKCoinvariant (g : ProbExp Γ →o ProbExp Γ) (b : BExpr Γ) (φ : ProbExp Γ) (k : ℕ)
    (I : ProbExp Γ) : Prop := I ≤ (pΨ[g] b φ) ((pΨ[g] b φ · ⊔ I)^[k] I)

/-- _Park k-coinduction_. -/
theorem ParkKCoinduction {b : BExpr Γ} {C : pGCL Γ} {φ : ProbExp Γ} {I : ProbExp Γ} (k : ℕ)
    (h : ParkKCoinvariant wlp[O]⟦@C⟧ b φ k I) :
    I ≤ wlp[O]⟦while @b { @C }⟧ φ := le_gfp_of_iter k h

end pGCL
