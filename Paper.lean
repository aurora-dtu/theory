import Paper.Syntax
import MDP.InducedMarkovChain
import PGCL.OperationalSemantics
import PGCL.ProofRules
import MDP.SupSup

/-!

# Glossary of Lean theorems and definitions

This file contains links to all references, definitions, lemmas and theorems from the paper.

They are listed roughly in the order they appear in the paper. This file should serve as a jumping
off point to navigate and explore the formalization, and not as a reference to _how_ things are
defined. We invite the reader to click on the names in each definition to jump to their original
definition. In Visual Studio Code one can Ctrl/CMD+Click on symbols to jump to their definition.

The names of the definitions on this file bear no semantic meaning, and are purely to nominally
distinguish them for documentation generation.

-/

namespace Paper

open OmegaCompletePartialOrder
open Optimization.Notation

namespace Section3

/-!

## Section 3 – Preliminaries

-/

variable {𝒱 : Type*} [DecidableEq 𝒱] {Γ : Γ[𝒱]}
variable {α β : Type*} [CompleteLattice α] [CompleteLattice β]

paper_link[1] ENNReal
/-- Written $\mathbb{R}_{[0, 1]}$ in the paper -/
paper_link[2] pGCL.ProbExp (𝒱:=𝒱)

paper_link[3] CompleteLattice
paper_link[4] Bot
paper_link[5] Top

paper_link[6] Monotone (α:=α) (β:=β)

/-- For continuity we use `ωScottContinuous` -/
paper_link[7] ωScottContinuous (α:=α) (β:=β)
/-- And for co-continuity we use `OrderDual` to flip the order of the order -/
paper_link[8] ωScottContinuous (α:=α) (β:=OrderDual β)

/-- Kleene fixed point theorem for `lfp` -/
paper_thm[9] fixedPoints.lfp_eq_sSup_iterate (α:=α)
/-- Kleene fixed point theorem for `gfp` -/
paper_thm[10] fixedPoints.gfp_eq_sInf_iterate (α:=α)

paper_link[11] MeasurableSpace
paper_link[12] MeasureTheory.IsProbabilityMeasure μ
paper_link[13] PMF

end Section3

namespace Section4

/-!

## Section 4 – Expected Total Costs in Markov Decision Processes

-/

/-!

### Markov Chains

-/

paper_link[1] MarkovChain

variable {MC : MarkovChain α}

paper_link[2] MC.Path
/-- Written $\text{Path}^ω$ in the paper -/
paper_link[3] MC.Path'

paper_link[4] MarkovChain.Path'.pref (M:=MC)
paper_link[5] MarkovChain.Path.Cyl (M:=MC)
paper_link[6] MC.Pr
paper_thm[7] MC.Pr_cyl
paper_link[8] MC.embed

/-!

### Expected Costs of MDPs as Sums over Paths

-/

variable {S : Type*} {A : Type*} [DecidableEq S]

variable {M : MDP S A}

paper_link[9] MDP

paper_link[10] M.succs
paper_link[11] M.act
paper_link[12] M.Path
paper_link[13] M.Scheduler
paper_link[14] M.inducedMC'

paper_thm[15] M.inducedMC'_cyl π h

/-!

### Expected Costs of MDPs as Least Fixed Points

-/

variable {α β : Type*} [CompleteLattice α] [CompleteLattice β]

paper_link[16] Pi.instCompleteLattice (α:=α) (β:=fun _ ↦ β)

paper_link[17] M.Φ
paper_thm[18] MDP.Φ_𝒜_ωScottContinuous (M:=M) (c:=c)
paper_thm[19] M.iSup_iSup_EC_eq_lfp_Φ𝒜 (c:=c)

variable [M.FiniteBranching]

paper_thm[20] MDP.Φ_𝒟_ωScottContinuous (M:=M) (c:=c)

paper_thm[21] M.iSup_iInf_EC_eq_lfp_Φ𝒟 (c:=c)

paper_link[22] M.MScheduler
paper_link[23] M.Φℒ
paper_thm[24] M.lfp_Φℒ_eq_lfp_Φ (c:=c)

paper_thm[25] M.iInf_iSup_EC_eq_lfp_Φ𝒟 (c:=c)

end Section4

namespace Section5

open pGCL

/-!

## Section 5 – pGCL: probabilistic Guarded Command Language

-/

/-!

### Program States, pGCL Syntax, and Design Considerations

-/

variable {𝒱 : Type*} [DecidableEq 𝒱] {Γ : Γ[𝒱]}

paper_link[1] pGCL.States (𝒱:=𝒱)
paper_link[2] Substitution

paper_link[3] pGCL (𝒱:=𝒱)
paper_link[4] ProbExp (𝒱:=𝒱)

paper_link[5] Conf
paper_link[6] SmallStep (Γ:=Γ)

/-!

### Operational Semantics

-/

/-- Operational MDP -/
paper_link[7] pGCL.𝒪 (Γ:=Γ)

/-! We split the cost functions into two parts, one for programs and one for terminations -/

/-- Cost of program for $\text{ct}$ -/
paper_link[8] pGCL.cost_p (Γ:=Γ)
/-- Cost of termination for $\text{ct}$ -/
paper_link[9] pGCL.cost_t (Γ:=Γ)
/-- Cost of program for $\text{cp}$ -/
paper_link[10] pGCL.cost_p' (Γ:=Γ)
/-- Cost of termination for $\text{cp}$ -/
paper_link[11] pGCL.cost_t' (Γ:=Γ)

section

variable {O : Optimization} {f} {g} [O.ΦContinuous (pGCL.𝕊 (Γ:=Γ) f g).mdp]

paper_link[12] (pGCL.𝕊 (Γ:=Γ) f g).op
paper_thm[13] (pGCL.𝕊 f g).op_le_seq (O:=O) (C:=C) (C':=C')


/-!

### Weakest Preexpectation Calculi

-/

paper_link[14] Iverson
paper_link[15] Ψ (Γ:=Γ)
paper_link[16] wp (Γ:=Γ)
paper_link[17] wlp (Γ:=Γ)
paper_link[18] cwp (Γ:=Γ)

/-!

### Soundness

-/

paper_link[19] (pGCL.𝕊 (Γ:=Γ) f g).ς
paper_thm[20] (pGCL.𝕊 (Γ:=Γ) f g).lfp_ς_eq_op (O:=O)
paper_thm[21] wp_eq_op (Γ:=Γ) (C:=C) (O:=O)
paper_link[22] wfp (Γ:=Γ)
paper_thm[23] wfp_eq_op (Γ:=Γ) (C:=C) (O:=O)
paper_thm[24] wlp_sound (Γ:=Γ) (C:=C) (O:=O)

end

/-!

### Quantitative Loop Invariants

-/

variable [CompleteLattice α]

paper_thm[25] OrderHom.lfp_le_of_iter (α:=α) (f:=f) (Δ:=Δ)
paper_thm[26] OrderHom.le_gfp_of_iter (α:=α) (f:=f) (Δ:=Δ)
paper_thm[27] pGCL.ParkKInduction (Γ:=Γ) (I:=I) (φ:=φ) (b:=b) (O:=O) (C:=C)
paper_thm[28] pGCL.ParkKCoinduction (Γ:=Γ) (I:=I) (φ:=φ) (b:=b) (O:=O) (C:=C)

paper_link[29] States.EQ (Γ:=Γ)
paper_thm[30] pGCL.IdleKInduction (Γ:=Γ) (I:=I) (φ:=φ) (b:=b) (O:=O) (C:=C) (σ₀:=σ₀)
paper_thm[31] pGCL.IdleKCoinduction (Γ:=Γ) (I:=I) (φ:=φ) (b:=b) (O:=O) (C:=C) (σ₀:=σ₀)

end Section5

namespace Section6

/-!

## Section 6 – Sound Encodings into an Intermediate Verification Language

-/

/-!

### The Intermediate Verification Language HeyVL

-/

paper_link[1] HeyLo
paper_link[2] HeyVL
/-- Written using `￢` (notice this is a different symbol than Boolean negation `¬`) -/
paper_link[3] HNot
/-- Written using `xᶜ`. We add `~x` as custom syntax too to align with the paper -/
paper_link[4] Compl
/-- Written using `a ⇨ b` and is Heyting implicaiton.
In the paper this is `b ↜ a` (notice the flipped order of arguments). -/
paper_link[5] HImp
/-- Written using `a \ b` and is Heyting co-implicaiton.
In the paper this is `b ↜ a` (notice the flipped order of arguments). -/
paper_link[6] SDiff
paper_link[7] BiheytingAlgebra
paper_link[8] HeyVL.vp

/-- A HeyVL program C verifies if `vp⟦C⟧ ⊤ = ⊤` -/
paper_link[9] HeyVL.Verifies

/-!

### Case Study: Correctness of Encodings for pGCL

-/

paper_thm[10] spGCL.enc (C:=C) (O:=O)

paper_thm[11] spGCL.wp_le_vp (C:=C) (φ:=φ) (O:=O)
paper_thm[12] spGCL.vp_le_wlp (C:=C) (φ:=φ) (O:=O)

paper_thm[13] Conditions.wlp_valid (C:=C)

end Section6

end Paper
