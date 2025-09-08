import MDP.Bellman
import MDP.Relational

open OrderHom

abbrev 𝔼 (S : Type*) := S → ENNReal

notation "𝔼[" S "]" => 𝔼 S

class WeakestPreexpectation (P S : Type*) where
  wp : P → 𝔼[S] →o 𝔼[S]

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

noncomputable def op (C : P) : 𝔼[S] →o 𝔼[S] :=
  ⟨fun X ↦ (lfp (i.mdp.Φ <| i.cost X) <| Conf.prog C ·), fun a b h σ ↦ by
    suffices lfp (MDP.Φ (i.cost a)) ≤ lfp (MDP.Φ (i.cost b)) by exact this _
    gcongr
    apply MDP.Φ.monotone' (i.cost_mono h)⟩

@[simp]
theorem Φ_simp {C : Conf P S T} :
    i.mdp.Φ c f C = c C + ⨅ α ∈ i.act C, ∑' s' : i.mdp.succs_univ C, i.mdp.P C α s' * f s'
:= by
  simp [MDP.Φ, act, MDP.act, MDP.Φf, iInf_subtype, mdp]
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
theorem bot_eq : (i.mdp.Φ (i.cost X))^[n] ⊥ .bot = 0 := by
  induction n <;> simp_all [-Function.iterate_succ, Function.iterate_succ', tsum_succs_univ']
  apply le_antisymm
  · have ⟨p, α, C', h⟩ := i.h₂ Conf.bot
    apply iInf_le_of_le α
    apply iInf_le_of_le (by simp [act]; grind)
    simp [*]
  · simp
@[simp]
theorem term_eq :
    (i.mdp.Φ (i.cost X))^[n] ⊥ (.term t σ) = if n = 0 then 0 else i.cost X (Conf.term t σ) := by
  induction n <;> simp_all [-Function.iterate_succ, Function.iterate_succ', tsum_succs_univ']
  nth_rw 2 [← add_zero (cost A X (Conf.term t σ))]
  congr
  apply le_antisymm
  · have ⟨p, α, C', h⟩ := i.h₂ (Conf.term t σ)
    apply iInf_le_of_le α
    apply iInf_le_of_le (by simp [act]; grind)
    simp [succs_univ_term]
  · simp

noncomputable def ς : (P → 𝔼[S] →o 𝔼[S]) →o P → 𝔼[S] →o 𝔼[S] :=
  ⟨fun Y ↦ (fun C ↦ ⟨fun X σ ↦
    i.mdp.Φ (i.cost X)
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
      apply (i.mdp.Φ _).mono
      rintro (_ | ⟨_ , _⟩) <;> try rfl
      apply_assumption⟩

variable [i.mdp.FiniteBranching]

@[simp]
theorem lfp_Φ_term :
    lfp (i.mdp.Φ (i.cost X)) (Conf.term t σ) = i.cost X (Conf.term t σ) := by
  rw [MDP.lfp_Φ_eq_iSup_Φ]
  simp
  apply le_antisymm
  · simp
    intro i
    split_ifs <;> simp
  · apply le_iSup_of_le 1
    simp
@[simp]
theorem lfp_Φ_bot :
    lfp (i.mdp.Φ (i.cost X)) Conf.bot = 0 := by
  rw [MDP.lfp_Φ_eq_iSup_Φ]
  simp

theorem op_eq_iSup_Φ :
    i.op
  = ⨆ n, fun C ↦ ⟨fun X σ ↦ (i.mdp.Φ (i.cost X))^[n] ⊥ (.prog C σ), fun a b h σ ↦ by
    simp
    suffices (⇑(MDP.Φ (i.cost a)))^[n] ⊥ ≤ (⇑(MDP.Φ (i.cost b)))^[n] ⊥ by apply this
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [Function.iterate_succ', Function.comp_apply]
      exact apply_mono (MDP.Φ.monotone' (i.cost_mono h)) ih⟩ := by
  ext C X σ; rw [op]
  simp [fixedPoints.lfp_eq_sSup_iterate _ MDP.Φ_ωScottContinuous]
theorem op_eq_iSup_succ_Φ :
      i.op
    = ⨆ n, fun C ↦ ⟨fun X σ ↦ (i.mdp.Φ (i.cost X))^[n + 1] ⊥ (.prog C σ), fun a b h σ ↦ by
      simp only
      suffices (⇑(MDP.Φ (i.cost a)))^[n + 1] ⊥ ≤ (⇑(MDP.Φ (i.cost b)))^[n + 1] ⊥ by apply this
      induction n with
      | zero => simp; apply MDP.Φ.monotone' (cost_mono h)
      | succ n ih =>
        simp only [Function.iterate_succ', Function.comp_apply] at ih ⊢
        exact apply_mono (MDP.Φ.monotone' (cost_mono h)) ih⟩ := by
  ext C X σ; rw [op]
  simp only [coe_mk, _root_.iSup_apply, coe_iSup]
  rw [fixedPoints.lfp_eq_sSup_iterate _ MDP.Φ_ωScottContinuous]
  rw [← iSup_iterate_succ]
  simp
theorem ς_op_eq_op : i.ς i.op = i.op := by
  ext C X σ
  simp [op]
  rw [← map_lfp]
  simp only [ς, OrderHom.coe_mk]
  congr! 3 with C'
  rcases C' with ⟨t, σ'⟩ | ⟨C', σ'⟩ | _ <;> simp [op]

theorem op_isLeast (b : P → 𝔼[S] →o 𝔼[S]) (h : i.ς b ≤ b) : i.op ≤ b := by
  rw [op_eq_iSup_Φ, iSup_le_iff]
  intro n
  induction n with
  | zero => intros _ _ _; simp
  | succ i ih =>
    refine le_trans (fun C X σ ↦ ?_) h
    simp [Function.iterate_succ', ς, -Function.iterate_succ]
    gcongr
    split
    · simp_all []; split_ifs <;> simp
    · simp_all only; exact ih _ X _
    · simp_all [le_refl]

theorem lfp_ς_eq_op : lfp i.ς = i.op :=
  (lfp_le_fixed _ i.ς_op_eq_op).antisymm (le_lfp _ i.op_isLeast)

class SoundWeakestPreexpexation (P S T A : Type*)
    [i : SmallStepSemantics P S T A] [i.mdp.FiniteBranching] [i' : WeakestPreexpectation P S] where
  wp_le_op : i'.wp ≤ i.op
  wp_prefixed_point : i.ς i'.wp ≤ i'.wp

variable [i' : WeakestPreexpectation P S] [SoundWeakestPreexpexation P S T A]

theorem SoundWeakestPreexpexation.wp_eq_op : i'.wp = i.op :=
  le_antisymm wp_le_op (op_isLeast i'.wp wp_prefixed_point)

omit [i.mdp.FiniteBranching] i' [SoundWeakestPreexpexation P S T A] in
open scoped Classical in
theorem ς_apply {p : P} {σ : S}
    (a : Set A) (ss : Set (Conf P S T))
    (ha : a = i.act (Conf.prog p σ)) (ha : ss = i.mdp.succs_univ (Conf.prog p σ)) :
    i.ς v p X σ = i.cost X (Conf.prog p σ) +
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
  simp [ς, tsum_succs_univ']

noncomputable def ς_continuation_fin
    (v : P → 𝔼[S] →o 𝔼[S]) (X : 𝔼[S]) (p : P) (σ : S) (ss : Finset (Conf P S T)) (α : A) :=
  ∑ s' ∈ ss,
    i.mdp.P (Conf.prog p σ) α s' *
      match s' with
      | Conf.term t σ' => i.cost X (Conf.term t σ')
      | Conf.prog C' σ' => v C' X σ'
      | Conf.bot => 0

omit [i.mdp.FiniteBranching] i' [SoundWeakestPreexpexation P S T A] in
open scoped Classical in
theorem ς_apply_fin {p : P} {σ : S}
    (as : Finset A) (ss : Finset (Conf P S T))
    (has : as = i.act (Conf.prog p σ)) (hss : ss = i.mdp.succs_univ (Conf.prog p σ)) :
    i.ς v p X σ = i.cost X (Conf.prog p σ) +
        ⨅ α ∈ as, ς_continuation_fin (A:=A) v X p σ ss α := by
  unfold ς_continuation_fin
  have : Fintype (i.act (Conf.prog p σ)) := by rw [← has]; exact FinsetCoe.fintype _
  have : Fintype (i.mdp.succs_univ (Conf.prog p σ)) := by rw [← hss]; exact FinsetCoe.fintype _
  have : as = (i.act (Conf.prog p σ)).toFinset := by ext; simp_all [← has]
  have : ss = (i.mdp.succs_univ (Conf.prog p σ)).toFinset := by ext; simp_all [← hss]
  rw [ς_apply as ss] <;> simp_all
  subst_eqs
  congr! 4 with α hα
  rw [← Finset.tsum_subtype]
  apply tsum_eq_tsum_of_ne_zero_bij (fun ⟨⟨x, hx⟩, _⟩ ↦ x)
  · intro ⟨⟨_, _⟩, _⟩; simp_all
  · intro; simp_all
  · simp_all

omit [i.mdp.FiniteBranching] i' [SoundWeakestPreexpexation P S T A] in
open scoped Classical in
theorem ς_apply_act₂ {p : P} {σ : S}
    (a₁ a₂ : A) (ss : Finset (Conf P S T))
    (has : {a₁, a₂} = i.act (Conf.prog p σ)) (hss : ss = i.mdp.succs_univ (Conf.prog p σ)) :
    i.ς v p X σ = i.cost X (Conf.prog p σ) +
        (ς_continuation_fin (T:=T) v X p σ ss a₁ ⊓ ς_continuation_fin (T:=T) v X p σ ss a₂) := by
  rw [ς_apply_fin {a₁, a₂} ss (by simp [has]) hss]
  congr
  rw [← iInf_pair]
  simp

omit i' [SoundWeakestPreexpexation P S T A] in
open scoped Classical in
theorem ς_apply_fin' {p : P} {σ : S} :
    i.ς v p X σ = i.cost X (Conf.prog p σ) +
        ⨅ α ∈ i.mdp.act₀ (Conf.prog p σ),
          ∑ s' ∈ i.mdp.succs₀ α (Conf.prog p σ),
            i.mdp.P (Conf.prog p σ) α s' *
              match s' with
              | Conf.term t σ' => i.cost X (Conf.term t σ')
              | Conf.prog C' σ' => v C' X σ'
              | Conf.bot => 0 := by
  rw [ς_apply_fin (i.mdp.act₀ (Conf.prog p σ)) (i.mdp.succs_univ₀ (Conf.prog p σ))]
  · simp_all
    congr! 4
    apply Finset.sum_bij_ne_zero (fun x _ _ ↦ x)
    · simp_all [MDP.succs_univ]
      intros
      apply_assumption
    · simp
    · simp_all [MDP.succs_univ]
      grind
    · simp
  · simp [act, mdp]
  · simp [mdp]

-- attribute [-simp] Function.iterate_succ in
-- theorem op_le_seq (seq : P → P → P)
--     (h_cost₀ : ∀ C σ X, i.cost X (.prog C σ) = i.cost 0 (.prog C σ))
--     (h_cost_seq : ∀ C C' σ X, i.cost X (.prog (seq C C') σ) = i.cost X (.prog C σ))
--     (h_seq_act : ∀ C σ, i.act (.prog (seq C C') σ) = i.act (.prog C σ)) :
--       i.op C ∘ i.op C'
--     ≤ i.op (seq C C') := by
--   intro X σ
--   nth_rw 1 [op_eq_iSup_succ_Φ]
--   simp
--   intro n
--   induction n generalizing C C' σ with
--   | zero =>
--     have : ⨅ α ∈ i.act (Conf.prog C σ), (0 : ENNReal) = 0 :=
--       sorry
--     nth_rw 2 [← ς_op_eq_op]; simp_all [ς]
--   | succ i ih =>
--     nth_rw 2 [← ς_op_eq_op]
--     rw [Function.iterate_succ', Function.comp_apply]
--     simp [ς, tsum_succs_univ', *]
--     refine add_le_add (le_refl _) (iInf₂_mono fun α hα ↦ ?_)
--     · simp [mdp, r]
--     · simp [mdp, r]
--       intro σ'
--       split_ifs <;> try rfl
--       gcongr
--       have := i.term_eq (A:=Act) (X:=(i.op C') X)
--                 (t:=Termination.term) (σ:=σ') (n:=i+1)
--       simp at this
--       rw [this]
--     · simp [mdp, r]
--       intro σ' α' p' h
--       right
--       have := i.term_eq (A:=Act) (X:=(i.op C') X)
--                 (t:=Termination.fault) (σ:=σ') (n:=i+1)
--       simp at this
--       rw [this]
--     · simp [mdp, r]
--       intro C' σ'
--       split_ifs <;> try rfl
--       gcongr
--       simp_all


end SmallStepSemantics
