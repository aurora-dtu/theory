import Paper.Links

/-!

# Definitions, lemmas and theorems listed in order

This file contains links to all definitions, lemmas and theorems from the paper.

They are listed roughly in the order they appear in the paper. This file should serve as a jumping
off point to navigate and explore the formalization, and not as a reference to _how_ things are
defined. We invite the reader to click on the names in each definition to jump to their original
definition. In Visual Studio Code one can Ctrl/CMD+Click on symbols to jump to their definition.

See [`Links`](Paper/Links.html) for a glossary of list things listed in the paper, including Mathlib
definitions.

-/

namespace Paper

set_option linter.unusedSectionVars false

open OmegaCompletePartialOrder
open Optimization.Notation
open pGCL OrderHom

variable {𝒱 : Type*} [DecidableEq 𝒱] {Γ : Γ[𝒱]}
variable {α β : Type*} [CompleteLattice α] [CompleteLattice β]
variable {S : Type*} {A : Type*} [DecidableEq S]
variable {MC : MarkovChain S} {M : MDP S A} [M.FiniteBranching]
variable {O : Optimization} {f} {g} [O.ΦContinuous (pGCL.𝕊 (Γ:=Γ) f g).mdp]

/-! ## Section 4 – Expected Total Costs in Markov Decision Processes -/

Section 4, Definition 1: MarkovChain
Section 4, Definition 2: MarkovChain.Path.Cyl (M:=MC)
Section 4, Theorem 3: MC.Pr_cyl
Section 4, Definition 4: MDP
Section 4, Definition 5: M.inducedMC'
Section 4, Theorem 6: M.inducedMC'_cyl (𝒮:=𝒮)
Section 4, Definition 7: M.ECost
Section 4, Definition 8: M.OEC
Section 4, Lemma 9: Pi.instCompleteLattice (α:=S) (β:=fun _ ↦ ENNReal)
Section 4, Definition 10: M.Φ
Section 4, Lemma 11: PProd.mk ((M.Φ 𝒜 c).mono) (M.Φ_𝒜_ωScottContinuous (c:=c))
Section 4, Theorem 12: M.iSup_iSup_EC_eq_lfp_Φ𝒜 (c:=c)
Section 4, Lemma 13: PProd.mk ((M.Φ 𝒟 c).mono) (M.Φ_𝒟_ωScottContinuous (c:=c))
Section 4, Lemma 14: M.iSup_iInf_EC_eq_lfp_Φ𝒟 (c:=c)
Section 4, Definition 15: M.MScheduler
Section 4, Lemma 16: M.iSup_ECℒ_eq_lfp_Φℒ (c:=c)
Section 4, Definition 17: M.optℒ
Section 4, Lemma 18: M.lfp_Φℒ_eq_lfp_Φ (c:=c)
Section 4, Theorem 19: M.iInf_iSup_EC_eq_lfp_Φ𝒟 (c:=c)

/-! ## Section 5 – pGCL: probabilistic Guarded Command Language -/

Section 5, Definition 20: Conf (pGCL Γ) (pGCL.State Γ) pGCL.Termination
Section 5, Definition 21: pGCL.SmallStep (Γ:=Γ)
Section 5, Definition 22: pGCL.𝒪 (Γ:=Γ)
/-- In Lean the cost functions are split for programs and terminations where `ct = cost_p, cost_t`
and  `cp = cost_p', cost_t'`. -/
Section 5, Definition 23: ((cost_p (Γ:=Γ), cost_t (Γ:=Γ)), (cost_p' (Γ:=Γ), cost_t' (Γ:=Γ)))
Section 5, Definition 24: (pGCL.𝕊 (Γ:=Γ) f g).op
Section 5, Lemma 25: (pGCL.𝕊 f g).op_le_seq (O:=O) (C:=C) (C':=C')
Section 5, Definition 26: (pGCL.𝕊 (Γ:=Γ) f g).ξ
Section 5, Lemma 27: (pGCL.𝕊 (Γ:=Γ) f g).lfp_ξ_eq_op (O:=O)
variable {et} [(𝕊 f g).ET O et] in
Section 5, Lemma 28: SmallStepSemantics.ET.et_eq_op (𝕊:=pGCL.𝕊 f g) (et:=et) (O:=O)
Section 5, Lemma 29: pGCL.ξ.seq (Γ:=Γ) (C₁:=C₁) (C₂:=C₂) (O:=O)
Section 5, Theorem 30: wp_eq_op (Γ:=Γ) (C:=C) (O:=O)
Section 5, Definition 31: wfp (Γ:=Γ)
Section 5, Lemma 32: wfp_eq_op (Γ:=Γ) (C:=C) (O:=O)
Section 5, Theorem 33: wlp_sound (Γ:=Γ) (C:=C) (O:=O)
Section 5, Lemma 34: PProd.mk (lfp_le_of_iter (f:=f') (Δ:=Δ)) (le_gfp_of_iter (α:=α) (f:=f') (Δ:=Δ))
Section 5, Theorem 35: ParkKInduction (Γ:=Γ) (I:=I) (φ:=φ) (C:=C) (b:=b) (O:=O)
Section 5, Theorem 36: ParkKCoinduction (Γ:=Γ) (I:=I) (φ:=φ) (C:=C) (b:=b) (O:=O)
Section 5, Definition 37: State.EQ (Γ:=Γ)
Section 5, Theorem 38: IdleInduction (Γ:=Γ) (I:=I) (φ:=φ) (b:=b) (O:=O) (C:=C) (σ₀:=σ₀)
Section 5, Theorem 39: IdleCoinduction (Γ:=Γ) (I:=I) (φ:=φ) (b:=b) (O:=O) (C:=C) (σ₀:=σ₀)

/-! ## Section 6 – Sound Encodings into an Intermediate Verification Language -/

Section 6, Definition 40: HeyVL.Verifies
Section 6, Theorem 41: spGCL.wp_le_vp (C:=C) (φ:=φ) (O:=O)
Section 6, Theorem 42: spGCL.vp_le_wlp (C:=C) (φ:=φ) (O:=O)
Section 6, Theorem 43: Conditions.wlp_valid (C:=C)

end Paper
