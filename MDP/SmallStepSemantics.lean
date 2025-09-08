import MDP.Bellman
import MDP.Relational
import MDP.SupSup

open OrderHom

abbrev 𝔼 (S : Type*) := S → ENNReal

notation "𝔼[" S "]" => 𝔼 S

inductive Conf (P S T : Type*) where
  | term (t : T) (σ : S)
  | prog (P : P) (σ : S)
  | bot

class SmallStepSemantics (P S T A : Type*) where
  r : Conf P S T → A → ENNReal → Conf P S T → Prop
  h₀ : ∀ {c α p c'}, r c α p c' → ¬p = 0
  h₁ : ∀ {c α p₀ c'}, r c α p₀ c' → ∑' (b : Conf P S T) (p : { p // r c α p b }), p.val = 1
  h₂ : ∀ (s : Conf P S T), ∃ p a x, r s a p x
  h₃ : ∀ {t σ c'}, (∃ α p, r (Conf.term t σ) α p c') ↔ c' = Conf.bot
  h₄ : ∀ {c'}, (∃ α p, r Conf.bot α p c') ↔ c' = Conf.bot

  cost : 𝔼[S] → Conf P S T → ENNReal
  cost_mono : Monotone cost

  cost_bot : ∀ X, cost X .bot = 0

namespace SmallStepSemantics

attribute [simp] SmallStepSemantics.cost_bot

variable {P S A T : Type*} [i : SmallStepSemantics P S T A]

noncomputable def mdp : MDP (Conf P S T) A := MDP.ofRelation i.r i.h₀ i.h₁ i.h₂

def act (c : Conf P S T) : Set A := {α | ∃ p c', i.r c α p c'}

noncomputable def dop (C : P) : 𝔼[S] →o 𝔼[S] :=
  ⟨fun X ↦ (lfp (i.mdp.dΦ <| i.cost X) <| Conf.prog C ·), fun a b h σ ↦ by
    suffices lfp (i.mdp.dΦ (i.cost a)) ≤ lfp (i.mdp.dΦ (i.cost b)) by exact this _
    gcongr
    apply MDP.dΦ.monotone' (i.cost_mono h)⟩
noncomputable def aop (C : P) : 𝔼[S] →o 𝔼[S] :=
  ⟨fun X ↦ (lfp (i.mdp.aΦ <| i.cost X) <| Conf.prog C ·), fun a b h σ ↦ by
    suffices lfp (MDP.aΦ (i.cost a)) ≤ lfp (MDP.aΦ (i.cost b)) by exact this _
    gcongr
    apply MDP.aΦ.monotone' (i.cost_mono h)⟩

@[simp]
theorem dΦ_simp {C : Conf P S T} :
    i.mdp.dΦ c f C = c C + ⨅ α ∈ i.act C, ∑' s' : i.mdp.succs_univ C, i.mdp.P C α s' * f s'
:= by
  simp [MDP.dΦ, act, MDP.act, MDP.Φf, iInf_subtype, mdp]
  congr! with α
  apply le_antisymm
  · simp
    intro p C' h
    apply iInf_le_of_le _ (by rfl)
    refine Function.ne_iff.mpr ?_
    simp
    use C', p, h, h₀ h
  · simp
    intro h
    apply Function.ne_iff.mp at h
    simp at h
    obtain ⟨C', p, h, hp⟩ := h
    apply iInf_le_of_le p (iInf_le_of_le C' (iInf_le_of_le h (by rfl)))
@[simp]
theorem aΦ_simp {C : Conf P S T} :
    i.mdp.aΦ c f C = c C + ⨆ α ∈ i.act C, ∑' s' : i.mdp.succs_univ C, i.mdp.P C α s' * f s'
:= by
  simp [MDP.aΦ, MDP.Φf, act, MDP.act, iSup_subtype, mdp]
  simp [funext_iff]
  congr! with α
  rw [iSup_comm]
  congr!
  simp
  exact i.h₀

open scoped Classical in
theorem tsum_succs_univ' (f : i.mdp.succs_univ c → ENNReal) :
    (∑' s', f s') = ∑' s', if h : _ then f ⟨s', h⟩ else 0 := by
  symm
  apply tsum_eq_tsum_of_ne_zero_bij (↑↑·) _ _ (by simp_all)
  · intro ⟨_, _⟩ ⟨_, _⟩; simp; apply SetCoe.ext
  · simp_all--; intro _ α p _ _; use α, p

@[simp]
theorem succs_univ_term : i.mdp.succs_univ (.term t σ) = {.bot} := by
  simp [mdp, h₃]
@[simp]
theorem succs_univ_bot : i.mdp.succs_univ .bot = {.bot} := by
  simp [mdp, h₄]

@[simp]
theorem Φ_bot_eq : (i.mdp.dΦ (i.cost X))^[n] ⊥ .bot = 0 := by
  induction n <;> simp_all [-Function.iterate_succ, Function.iterate_succ', tsum_succs_univ']
  apply le_antisymm
  · have ⟨p, α, C', h⟩ := i.h₂ Conf.bot
    apply iInf_le_of_le α
    apply iInf_le_of_le (by simp [act]; grind)
    simp [*]
  · simp
@[simp]
theorem Φ_term_eq :
    (i.mdp.dΦ (i.cost X))^[n] ⊥ (.term t σ) = if n = 0 then 0 else i.cost X (Conf.term t σ) := by
  induction n <;> simp_all [-Function.iterate_succ, Function.iterate_succ', tsum_succs_univ']
  nth_rw 2 [← add_zero (cost A X (Conf.term t σ))]
  congr
  apply le_antisymm
  · have ⟨p, α, C', h⟩ := i.h₂ (Conf.term t σ)
    apply iInf_le_of_le α
    apply iInf_le_of_le (by simp [act]; grind)
    simp [succs_univ_term]
  · simp

@[simp]
theorem aΦ_bot_eq : (i.mdp.aΦ (i.cost X))^[n] ⊥ .bot = 0 := by
  induction n <;> simp_all [-Function.iterate_succ, Function.iterate_succ', tsum_succs_univ']
@[simp]
theorem aΦ_term_eq :
    (i.mdp.aΦ (i.cost X))^[n] ⊥ (.term t σ) = if n = 0 then 0 else i.cost X (Conf.term t σ) := by
  induction n <;> simp_all [-Function.iterate_succ, Function.iterate_succ', tsum_succs_univ']
  nth_rw 2 [← add_zero (cost A X (Conf.term t σ))]
  congr
  simp

noncomputable def dς : (P → 𝔼[S] →o 𝔼[S]) →o P → 𝔼[S] →o 𝔼[S] :=
  ⟨fun Y ↦ (fun C ↦ ⟨fun X σ ↦
    i.mdp.dΦ (i.cost X)
      (match · with
      | .term t σ' => i.cost X (.term t σ') | .prog C' σ' => Y C' X σ' | .bot => 0) (.prog C σ),
      fun a b h σ ↦ by
        simp
        gcongr
        · apply i.cost_mono h
        · split
          · apply i.cost_mono h
          · apply (Y _).mono h
          · rfl⟩),
    by
      intro _ _ _ _ _ _
      apply (i.mdp.dΦ _).mono
      rintro (_ | ⟨_ , _⟩) <;> try rfl
      apply_assumption⟩
noncomputable def aς : (P → 𝔼[S] →o 𝔼[S]) →o P → 𝔼[S] →o 𝔼[S] :=
  ⟨fun Y ↦ (fun C ↦ ⟨fun X σ ↦
    i.mdp.aΦ (i.cost X)
      (match · with
      | .term t σ' => i.cost X (.term t σ') | .prog C' σ' => Y C' X σ' | .bot => 0) (.prog C σ),
      fun a b h σ ↦ by
        simp
        gcongr
        · apply i.cost_mono h
        · split
          · apply i.cost_mono h
          · apply (Y _).mono h
          · rfl⟩),
    by
      intro _ _ _ _ _ _
      apply (i.mdp.aΦ _).mono
      rintro (_ | ⟨_ , _⟩) <;> try rfl
      apply_assumption⟩

section Demonic

variable [i.mdp.FiniteBranching]

@[simp]
theorem lfp_dΦ_term :
    lfp (i.mdp.dΦ (i.cost X)) (Conf.term t σ) = i.cost X (Conf.term t σ) := by
  rw [MDP.lfp_dΦ_eq_iSup_dΦ]
  simp
  apply le_antisymm
  · simp
    intro i
    split_ifs <;> simp
  · apply le_iSup_of_le 1
    simp
@[simp]
theorem lfp_dΦ_bot :
    lfp (i.mdp.dΦ (i.cost X)) Conf.bot = 0 := by
  rw [MDP.lfp_dΦ_eq_iSup_dΦ]
  simp

theorem dop_eq_iSup_dΦ :
    i.dop
  = ⨆ n, fun C ↦ ⟨fun X σ ↦ (i.mdp.dΦ (i.cost X))^[n] ⊥ (.prog C σ), fun a b h σ ↦ by
    simp
    suffices (⇑(MDP.dΦ (i.cost a)))^[n] ⊥ ≤ (⇑(MDP.dΦ (i.cost b)))^[n] ⊥ by apply this
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [Function.iterate_succ', Function.comp_apply]
      exact apply_mono (MDP.dΦ.monotone' (i.cost_mono h)) ih⟩ := by
  ext C X σ; rw [dop]
  simp [fixedPoints.lfp_eq_sSup_iterate _ MDP.dΦ_ωScottContinuous]
theorem dop_eq_iSup_succ_dΦ :
      i.dop
    = ⨆ n, fun C ↦ ⟨fun X σ ↦ (i.mdp.dΦ (i.cost X))^[n + 1] ⊥ (.prog C σ), fun a b h σ ↦ by
      simp only
      suffices (⇑(MDP.dΦ (i.cost a)))^[n + 1] ⊥ ≤ (⇑(MDP.dΦ (i.cost b)))^[n + 1] ⊥ by apply this
      induction n with
      | zero => simp; apply MDP.dΦ.monotone' (cost_mono h)
      | succ n ih =>
        simp only [Function.iterate_succ', Function.comp_apply] at ih ⊢
        exact apply_mono (MDP.dΦ.monotone' (cost_mono h)) ih⟩ := by
  ext C X σ; rw [dop]
  simp only [coe_mk, _root_.iSup_apply, coe_iSup]
  rw [fixedPoints.lfp_eq_sSup_iterate _ MDP.dΦ_ωScottContinuous]
  rw [← iSup_iterate_succ]
  simp
theorem dς_dop_eq_dop : i.dς i.dop = i.dop := by
  ext C X σ
  simp [dop]
  rw [← map_lfp]
  simp only [dς, OrderHom.coe_mk]
  congr! 3 with C'
  rcases C' with ⟨t, σ'⟩ | ⟨C', σ'⟩ | _ <;> simp [dop]

theorem dop_isLeast (b : P → 𝔼[S] →o 𝔼[S]) (h : i.dς b ≤ b) : i.dop ≤ b := by
  rw [dop_eq_iSup_dΦ, iSup_le_iff]
  intro n
  induction n with
  | zero => intros _ _ _; simp
  | succ i ih =>
    refine le_trans (fun C X σ ↦ ?_) h
    simp [Function.iterate_succ', dς, -Function.iterate_succ]
    gcongr
    split
    · simp_all []; split_ifs <;> simp
    · simp_all only; exact ih _ X _
    · simp_all [le_refl]

theorem lfp_dς_eq_dop : lfp i.dς = i.dop :=
  (lfp_le_fixed _ i.dς_dop_eq_dop).antisymm (le_lfp _ i.dop_isLeast)

class DemonicExpectationTransformer (P S : Type*) where
  det : P → 𝔼[S] →o 𝔼[S]

class SoundDemonicExpectationTransformer (P S T A : Type*)
    [i : SmallStepSemantics P S T A] [i.mdp.FiniteBranching]
    [i' : DemonicExpectationTransformer P S] where
  det_le_dop : i'.det ≤ i.dop
  det_prefixed_point : i.dς i'.det ≤ i'.det

variable [i' : DemonicExpectationTransformer P S] [SoundDemonicExpectationTransformer P S T A]

theorem SoundDemonicExpectationTransformer.det_eq_dop : i'.det = i.dop :=
  le_antisymm det_le_dop (dop_isLeast i'.det det_prefixed_point)

end Demonic

section Angelic

@[simp]
theorem lfp_aΦ_term :
    lfp (i.mdp.aΦ (i.cost X)) (Conf.term t σ) = i.cost X (Conf.term t σ) := by
  rw [MDP.lfp_aΦ_eq_iSup_aΦ]
  simp
  apply le_antisymm
  · simp
    intro i
    split_ifs <;> simp
  · apply le_iSup_of_le 1
    simp
@[simp]
theorem lfp_aΦ_bot :
    lfp (i.mdp.aΦ (i.cost X)) Conf.bot = 0 := by
  rw [MDP.lfp_aΦ_eq_iSup_aΦ]
  simp

theorem aop_eq_iSup_aΦ :
    i.aop
  = ⨆ n, fun C ↦ ⟨fun X σ ↦ (i.mdp.aΦ (i.cost X))^[n] ⊥ (.prog C σ), fun a b h σ ↦ by
    simp
    suffices (⇑(MDP.aΦ (i.cost a)))^[n] ⊥ ≤ (⇑(MDP.aΦ (i.cost b)))^[n] ⊥ by apply this
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [Function.iterate_succ', Function.comp_apply]
      exact apply_mono (MDP.aΦ.monotone' (i.cost_mono h)) ih⟩ := by
  ext C X σ; rw [aop]
  simp [fixedPoints.lfp_eq_sSup_iterate _ MDP.aΦ_ωScottContinuous]
theorem aop_eq_iSup_succ_aΦ :
      i.aop
    = ⨆ n, fun C ↦ ⟨fun X σ ↦ (i.mdp.aΦ (i.cost X))^[n + 1] ⊥ (.prog C σ), fun a b h σ ↦ by
      simp only
      suffices (⇑(MDP.aΦ (i.cost a)))^[n + 1] ⊥ ≤ (⇑(MDP.aΦ (i.cost b)))^[n + 1] ⊥ by apply this
      induction n with
      | zero => simp; apply MDP.aΦ.monotone' (cost_mono h)
      | succ n ih =>
        simp only [Function.iterate_succ', Function.comp_apply] at ih ⊢
        exact apply_mono (MDP.aΦ.monotone' (cost_mono h)) ih⟩ := by
  ext C X σ; rw [aop]
  simp only [coe_mk, _root_.iSup_apply, coe_iSup]
  rw [fixedPoints.lfp_eq_sSup_iterate _ MDP.aΦ_ωScottContinuous]
  rw [← iSup_iterate_succ]
  simp
theorem aς_aop_eq_aop : i.aς i.aop = i.aop := by
  ext C X σ
  simp [aop]
  rw [← map_lfp]
  simp only [aς, OrderHom.coe_mk]
  congr! 3 with C'
  rcases C' with ⟨t, σ'⟩ | ⟨C', σ'⟩ | _ <;> simp [aop]

theorem aop_isLeast (b : P → 𝔼[S] →o 𝔼[S]) (h : i.aς b ≤ b) : i.aop ≤ b := by
  rw [aop_eq_iSup_aΦ, iSup_le_iff]
  intro n
  induction n with
  | zero => intros _ _ _; simp
  | succ i ih =>
    refine le_trans (fun C X σ ↦ ?_) h
    simp [Function.iterate_succ', aς, -Function.iterate_succ]
    gcongr
    split
    · simp_all []; split_ifs <;> simp
    · simp_all only; exact ih _ X _
    · simp_all [le_refl]

class AngelicExpectationTransformer (P S : Type*) where
  aet : P → 𝔼[S] →o 𝔼[S]

class SoundAngelicExpectationTransformer (P S T A : Type*)
    [i : SmallStepSemantics P S T A]
    [i' : AngelicExpectationTransformer P S] where
  aet_le_aop : i'.aet ≤ i.aop
  aet_prefixed_point : i.aς i'.aet ≤ i'.aet

variable [i' : AngelicExpectationTransformer P S] [SoundAngelicExpectationTransformer P S T A]

theorem SoundAngelicExpectationTransformer.aet_eq_aop : i'.aet = i.aop :=
  le_antisymm aet_le_aop (aop_isLeast i'.aet aet_prefixed_point)

end Angelic

open scoped Classical in
theorem dς_apply {p : P} {σ : S}
    (a : Set A) (ss : Set (Conf P S T))
    (ha : a = i.act (Conf.prog p σ)) (ha : ss = i.mdp.succs_univ (Conf.prog p σ)) :
    i.dς v p X σ = i.cost X (Conf.prog p σ) +
        ⨅ α ∈ a,
          ∑' (s' : Conf P S T),
          if s' ∈ ss then
            i.mdp.P (Conf.prog p σ) α s' *
              match s' with
              | Conf.term t σ' => i.cost X (Conf.term t σ')
              | Conf.prog C' σ' => v C' X σ'
              | Conf.bot => 0
          else 0 := by
  subst_eqs
  simp [dς, tsum_succs_univ']

open scoped Classical in
theorem aς_apply {p : P} {σ : S}
    (a : Set A) (ss : Set (Conf P S T))
    (ha : a = i.act (Conf.prog p σ)) (ha : ss = i.mdp.succs_univ (Conf.prog p σ)) :
    i.aς v p X σ = i.cost X (Conf.prog p σ) +
        ⨆ α ∈ a,
          ∑' (s' : Conf P S T),
          if s' ∈ ss then
            i.mdp.P (Conf.prog p σ) α s' *
              match s' with
              | Conf.term t σ' => i.cost X (Conf.term t σ')
              | Conf.prog C' σ' => v C' X σ'
              | Conf.bot => 0
          else 0 := by
  subst_eqs
  simp [aς, tsum_succs_univ']

noncomputable def dς_continuation_fin
    (v : P → 𝔼[S] →o 𝔼[S]) (X : 𝔼[S]) (p : P) (σ : S) (ss : Finset (Conf P S T)) (α : A) :=
  ∑ s' ∈ ss,
    i.mdp.P (Conf.prog p σ) α s' *
      match s' with
      | Conf.term t σ' => i.cost X (Conf.term t σ')
      | Conf.prog C' σ' => v C' X σ'
      | Conf.bot => 0

open scoped Classical in
theorem dς_apply_fin {p : P} {σ : S}
    (as : Finset A) (ss : Finset (Conf P S T))
    (has : as = i.act (Conf.prog p σ)) (hss : ss = i.mdp.succs_univ (Conf.prog p σ)) :
    i.dς v p X σ = i.cost X (Conf.prog p σ) +
        ⨅ α ∈ as, dς_continuation_fin (A:=A) v X p σ ss α := by
  unfold dς_continuation_fin
  have : Fintype (i.act (Conf.prog p σ)) := by rw [← has]; exact FinsetCoe.fintype _
  have : Fintype (i.mdp.succs_univ (Conf.prog p σ)) := by rw [← hss]; exact FinsetCoe.fintype _
  have : as = (i.act (Conf.prog p σ)).toFinset := by ext; simp_all [← has]
  have : ss = (i.mdp.succs_univ (Conf.prog p σ)).toFinset := by ext; simp_all [← hss]
  rw [dς_apply as ss] <;> simp_all
  subst_eqs
  congr! 4 with α hα
  rw [← Finset.tsum_subtype]
  apply tsum_eq_tsum_of_ne_zero_bij (fun ⟨⟨x, hx⟩, _⟩ ↦ x)
  · intro ⟨⟨_, _⟩, _⟩; simp_all
  · intro; simp_all
  · simp_all

open scoped Classical in
theorem dς_apply_act₂ {p : P} {σ : S}
    (a₁ a₂ : A) (ss : Finset (Conf P S T))
    (has : {a₁, a₂} = i.act (Conf.prog p σ)) (hss : ss = i.mdp.succs_univ (Conf.prog p σ)) :
    i.dς v p X σ = i.cost X (Conf.prog p σ) +
        (dς_continuation_fin (T:=T) v X p σ ss a₁ ⊓ dς_continuation_fin (T:=T) v X p σ ss a₂) := by
  rw [dς_apply_fin {a₁, a₂} ss (by simp [has]) hss]
  congr
  rw [← iInf_pair]
  simp

open scoped Classical in
theorem aς_apply_fin {p : P} {σ : S}
    (as : Finset A) (ss : Finset (Conf P S T))
    (has : as = i.act (Conf.prog p σ)) (hss : ss = i.mdp.succs_univ (Conf.prog p σ)) :
    i.aς v p X σ = i.cost X (Conf.prog p σ) +
        ⨆ α ∈ as, dς_continuation_fin (A:=A) v X p σ ss α := by
  unfold dς_continuation_fin
  have : Fintype (i.act (Conf.prog p σ)) := by rw [← has]; exact FinsetCoe.fintype _
  have : Fintype (i.mdp.succs_univ (Conf.prog p σ)) := by rw [← hss]; exact FinsetCoe.fintype _
  have : as = (i.act (Conf.prog p σ)).toFinset := by ext; simp_all [← has]
  have : ss = (i.mdp.succs_univ (Conf.prog p σ)).toFinset := by ext; simp_all [← hss]
  rw [aς_apply as ss] <;> simp_all
  subst_eqs
  congr! 4 with α hα
  rw [← Finset.tsum_subtype]
  apply tsum_eq_tsum_of_ne_zero_bij (fun ⟨⟨x, hx⟩, _⟩ ↦ x)
  · intro ⟨⟨_, _⟩, _⟩; simp_all
  · intro; simp_all
  · simp_all

open scoped Classical in
theorem aς_apply_act₂ {p : P} {σ : S}
    (a₁ a₂ : A) (ss : Finset (Conf P S T))
    (has : {a₁, a₂} = i.act (Conf.prog p σ)) (hss : ss = i.mdp.succs_univ (Conf.prog p σ)) :
    i.aς v p X σ = i.cost X (Conf.prog p σ) +
        (dς_continuation_fin (T:=T) v X p σ ss a₁ ⊔ dς_continuation_fin (T:=T) v X p σ ss a₂) := by
  rw [aς_apply_fin {a₁, a₂} ss (by simp [has]) hss]
  congr
  rw [← iSup_pair]
  simp

-- attribute [-simp] Function.iterate_succ in
-- theorem op_le_seq (seq : P → P → P)
--     (h_cost₀ : ∀ C σ X, i.cost X (.prog C σ) = i.cost 0 (.prog C σ))
--     (h_cost_seq : ∀ C C' σ X, i.cost X (.prog (seq C C') σ) = i.cost X (.prog C σ))
--     (h_seq_act : ∀ C σ, i.act (.prog (seq C C') σ) = i.act (.prog C σ)) :
--       i.dop C ∘ i.dop C'
--     ≤ i.dop (seq C C') := by
--   intro X σ
--   nth_rw 1 [dop_eq_iSup_succ_dΦ]
--   simp
--   intro n
--   induction n generalizing C C' σ with
--   | zero =>
--     have : ⨅ α ∈ i.act (Conf.prog C σ), (0 : ENNReal) = 0 :=
--       sorry
--     nth_rw 2 [← dς_dop_eq_dop]; simp_all [dς]
--   | succ i ih =>
--     nth_rw 2 [← dς_dop_eq_dop]
--     rw [Function.iterate_succ', Function.comp_apply]
--     simp [dς, tsum_succs_univ', *]
--     refine add_le_add (le_refl _) (iInf₂_mono fun α hα ↦ ?_)
--     · simp [mdp, r]
--     · simp [mdp, r]
--       intro σ'
--       split_ifs <;> try rfl
--       gcongr
--       have := i.Φ_term_eq (A:=Act) (X:=(i.dop C') X)
--                 (t:=Termination.term) (σ:=σ') (n:=i+1)
--       simp at this
--       rw [this]
--     · simp [mdp, r]
--       intro σ' α' p' h
--       right
--       have := i.Φ_term_eq (A:=Act) (X:=(i.dop C') X)
--                 (t:=Termination.fault) (σ:=σ') (n:=i+1)
--       simp at this
--       rw [this]
--     · simp [mdp, r]
--       intro C' σ'
--       split_ifs <;> try rfl
--       gcongr
--       simp_all

end SmallStepSemantics
