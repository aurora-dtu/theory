import PGCL.WeakestPre
import PGCL.WeakestLiberalPre
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.String.Basic
import ENNRealArith
import PGCL.KInduction

namespace pGCL

variable {𝒱 : Type*} {ϖ : Γ[𝒱]} [DecidableEq 𝒱]

open OrderHom
open Optimization.Notation

/-- A program is _Almost Surely Terminating_ iff it's weakest pre-expectation without ticks of one
  is one is. -/
def AST (C : pGCL ϖ) : Prop := wp[𝒟]⟦~C.st⟧ 1 = 1

noncomputable def cwp (O : Optimization) (C : pGCL ϖ) : 𝔼[ϖ, ENNReal] →o 𝔼[ϖ, ENNReal] :=
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

/-- Encodes a program for analyzing _expected runtimes_ by removing all existing tick statements,
and adding `tick(1)` to every existing non-tick statement. -/
def ertEnc : pGCL ϖ → pGCL ϖ
  | pgcl {skip} => pgcl {tick(1); skip}
  | pgcl {~x := ~A} => pgcl {tick(1); ~x := ~A}
  | pgcl {~C₁ ; ~C₂} => pgcl {~C₁.ertEnc ; ~C₂.ertEnc}
  | pgcl {{~C₁} [~p] {~C₂}} => pgcl {tick(1); {~C₁.ertEnc} [~p] {~C₂.ertEnc}}
  | pgcl {{~C₁} [] {~C₂}} => pgcl {tick(1); {~C₁.ertEnc} [] {~C₂.ertEnc}}
  | pgcl {while ~b {~C'}} => pgcl {tick(1); while ~b {~C'.ertEnc}}
  | pgcl {tick(~ _)} => pgcl {skip}
  | pgcl {observe(~ b)} => pgcl {tick(1); observe(~b)}

noncomputable def ert (O : Optimization) (C : pGCL ϖ) : 𝔼[ϖ, ENNReal] →o 𝔼[ϖ, ENNReal] :=
  wp[O]⟦~C.ertEnc⟧

syntax "ert[" term "]⟦" cpgcl_prog "⟧" : term

macro_rules
| `(ert[$O]⟦ $p ⟧) => `(pGCL.ert $O pgcl {$p})

@[app_unexpander pGCL.ert]
def ertUnexpander : Lean.PrettyPrinter.Unexpander
| `($(_) $o $c) => do
    let c ← match c with | `(pgcl {$c}) => pure c | _ => `(cpgcl_prog| ~ $c)
    `(ert[$o]⟦$c⟧)
| _ => throw ()

/-- A _Park invariant_. -/
def ParkInvariant (g : 𝔼[ϖ, ENNReal] →o 𝔼[ϖ, ENNReal]) (b : BExpr ϖ) (φ : 𝔼[ϖ, ENNReal])
    (I : 𝔼[ϖ, ENNReal]) : Prop := Φ[g] b φ I ≤ I

/-- _Park induction_. -/
theorem ParkInduction {b : BExpr ϖ} {C : pGCL ϖ} {φ : 𝔼[ϖ, ENNReal]} {I : 𝔼[ϖ, ENNReal]}
    (h : ParkInvariant wp[O]⟦~C⟧ b φ I) :
    wp[O]⟦while ~b { ~C }⟧ φ ≤ I := lfp_le _ h

/-- A _Park coinvariant_. -/
def ParkCoinvariant (g : ProbExp ϖ →o ProbExp ϖ) (b : BExpr ϖ) (φ : ProbExp ϖ)
    (I : ProbExp ϖ) : Prop := I ≤ pΦ[g] b φ I

/-- _Park coinduction_. -/
theorem ParkCoinduction {b : BExpr ϖ} {C : pGCL ϖ} {φ : ProbExp ϖ} {I : ProbExp ϖ}
    (h : ParkCoinvariant wlp[O]⟦~C⟧ b φ I) :
    I ≤ wlp[O]⟦while ~b { ~C }⟧ φ := le_gfp _ h

/-- A _Park k-invariant_. -/
def ParkKInvariant (g : 𝔼[ϖ, ENNReal] →o 𝔼[ϖ, ENNReal]) (b : BExpr ϖ) (φ : 𝔼[ϖ, ENNReal]) (k : ℕ)
    (I : 𝔼[ϖ, ENNReal]) : Prop := (Φ[g] b φ) ((Φ[g] b φ · ⊓ I)^[k] I) ≤ I

/-- _Park k-induction_. -/
theorem ParkKInduction {b : BExpr ϖ} {C : pGCL ϖ} {φ : 𝔼[ϖ, ENNReal]} {I : 𝔼[ϖ, ENNReal]} (k : ℕ)
    (h : ParkKInvariant wp[O]⟦~C⟧ b φ k I) :
    wp[O]⟦while ~b { ~C }⟧ φ ≤ I := lfp_le_of_iter k h

/-- A _Park k-coinvariant_. -/
def ParkKCoinvariant (g : ProbExp ϖ →o ProbExp ϖ) (b : BExpr ϖ) (φ : ProbExp ϖ) (k : ℕ)
    (I : ProbExp ϖ) : Prop := I ≤ (pΦ[g] b φ) ((pΦ[g] b φ · ⊔ I)^[k] I)

/-- _Park k-coinduction_. -/
theorem ParkKCoinduction {b : BExpr ϖ} {C : pGCL ϖ} {φ : ProbExp ϖ} {I : ProbExp ϖ} (k : ℕ)
    (h : ParkKCoinvariant wlp[O]⟦~C⟧ b φ k I) :
    I ≤ wlp[O]⟦while ~b { ~C }⟧ φ := le_gfp_of_iter k h

end pGCL
