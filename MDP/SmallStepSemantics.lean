import MDP.Bellman
import MDP.Relational
import MDP.SupSup

open OrderHom OmegaCompletePartialOrder

abbrev 𝔼 (S : Type*) := S → ENNReal

notation "𝔼[" S "]" => 𝔼 S

inductive Conf (P S T : Type*) where
  | term (t : T) (σ : S)
  | prog (P : P) (σ : S)
  | bot

class SmallStepSemantics (P S T A : Type*) [Nonempty A] where
  r : P × S → A → ENNReal → (P ⊕ T) × S → Prop
  h₀ : ∀ {c α p c'}, r c α p c' → ¬p = 0
  h₁ : ∀ {c α p₀ c'}, r c α p₀ c' → ∑' (b) (p : { p // r c α p b }), p.val = 1
  h₂ : ∀ s, ∃ p a x, r s a p x

  cost_p : P × S → ENNReal
  cost_t : 𝔼[S] →o T × S → ENNReal

namespace SmallStepSemantics

variable {P S A T : Type*} [Nonempty A] [i : SmallStepSemantics P S T A]

noncomputable instance : Inhabited A := Classical.inhabited_of_nonempty ‹_›

@[grind]
inductive rr : Conf P S T → Option A → ENNReal → Conf P S T → Prop where
  | bot : rr .bot none 1 .bot
  | term : rr (.term _ _) none 1 .bot
  | prog₀ : i.r (C, σ) α p (.inl C', σ') → rr (.prog C σ) α p (.prog C' σ')
  | prog₁ : i.r (C, σ) α p (.inr t, σ') → rr (.prog C σ) α p (.term t σ')

@[simp] theorem rr.bot_to : i.rr .bot α p c' ↔ α = none ∧ p = 1 ∧ c' = .bot := by grind
@[simp] theorem rr.term_to : i.rr (.term t σ) α p c' ↔ α = none ∧ p = 1 ∧ c' = .bot := by grind

@[simp]
def conf₂_to_conf : (P ⊕ T) × S → Conf P S T
  | (.inl C, σ) => .prog C σ
  | (.inr t, σ) => .term t σ
@[simp]
def conf_to_conf₂ : Conf P S T → Option ((P ⊕ T) × S)
  | .prog C σ => some (.inl C, σ)
  | .term t σ => some (.inr t, σ)
  | .bot => none

@[simp, grind]
theorem rr_prog :
      i.rr (.prog C σ) α p c'
    ↔ ∃ c'' α', i.r (C, σ) α' p c'' ∧ conf₂_to_conf c'' = c' ∧ some α' = α := by
  simp [conf₂_to_conf]; grind

theorem h₀' : ∀ {c α p c'}, i.rr c α p c' → ¬p = 0 := by
  intro C α p c'; rintro (_ | _) <;> (try simp_all) <;> try apply i.h₀ ‹_›
theorem h₁' : ∀ {c α p₀ c'}, i.rr c α p₀ c' → ∑' (b) (p : { p // i.rr c α p b }), p.val = 1 := by
  intro C α p c'; rintro (_ | _)
  · rw [tsum_eq_single .bot, tsum_eq_single ⟨1, by grind⟩] <;> simp_all
  · rw [tsum_eq_single .bot, tsum_eq_single ⟨1, by grind⟩] <;> simp_all
  · rename_i h
    conv => right; rw [← i.h₁ h]
    apply tsum_eq_tsum_of_ne_zero_bij
      (fun ⟨x, _⟩ ↦ conf₂_to_conf x)
    · intro ⟨_, _⟩ ⟨_, _⟩; simp [conf₂_to_conf]; grind
    · simp [conf₂_to_conf]; grind
    · simp [conf₂_to_conf]
      constructor
      · intros
        congr! <;> simp [conf₂_to_conf]
      · congr! <;> simp [conf₂_to_conf]
  · rename_i h
    conv => right; rw [← i.h₁ h]
    apply tsum_eq_tsum_of_ne_zero_bij
      (fun ⟨x, _⟩ ↦ match x with | (.inl C, σ) => .prog C σ | (.inr t, σ) => .term t σ)
    · intro ⟨_, _⟩ ⟨_, _⟩; grind
    · simp only [Function.support_subset_iff, ne_eq, ENNReal.tsum_eq_zero, Subtype.forall,
      not_forall, exists_prop, Set.mem_range, Subtype.exists, Function.mem_support, Prod.exists,
      Sum.exists, forall_exists_index, and_imp]; grind
    · simp
      constructor
      · intros
        congr! <;> simp [conf₂_to_conf]
      · congr! <;> simp [conf₂_to_conf]

theorem h₂' : ∀ s, ∃ p a x, i.rr s a p x := by
  rintro (⟨t, σ⟩ | ⟨C, σ⟩ | _)
  · use 1, default, .bot; grind
  · have ⟨p, α, c', h⟩ := i.h₂ (C, σ)
    use p, α, conf₂_to_conf c'
    grind
  · use 1, default, .bot; grind
theorem h₃ : ∀ {t σ c'}, (∃ α p, i.rr (Conf.term t σ) α p c') ↔ c' = Conf.bot := by
  -- grind
  intros
  constructor
  · grind
  · rintro ⟨_⟩; use none, 1; grind
theorem h₄ : ∀ {c'}, (∃ α p, i.rr Conf.bot α p c') ↔ c' = Conf.bot := by
  intro
  constructor
  · grind
  · rintro ⟨_⟩; use none, 1; grind

noncomputable def mdp : MDP (Conf P S T) (Option A) := MDP.ofRelation i.rr i.h₀' i.h₁' i.h₂'

def cost (X : 𝔼[S]) : i.mdp.Costs
  | .bot => 0
  | .term t σ => i.cost_t X (t, σ)
  | .prog C σ => i.cost_p (C, σ)

def cost_mono : Monotone i.cost := by
  intro a b h c
  simp [cost]
  split
  · rfl
  · apply i.cost_t.mono h
  · rfl

@[simp] theorem cost_bot (X) : i.cost X .bot = 0 := by rfl

def act (c : Conf P S T) : Set (Option A) := {α | ∃ p c', i.rr c α p c'}

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

open scoped Classical in
theorem tsum_succs_univ' (f : i.mdp.succs_univ c → ENNReal) :
    (∑' s', f s') = ∑' s', if h : _ then f ⟨s', h⟩ else 0 := by
  symm
  apply tsum_eq_tsum_of_ne_zero_bij (↑↑·) _ _ (by simp_all)
  · intro ⟨_, _⟩ ⟨_, _⟩; simp; apply SetCoe.ext
  · simp_all--; intro _ α p _ _; use α, p

@[simp]
theorem dΦ_simp {C : Conf P S T} :
    i.mdp.dΦ c f C = c C + ⨅ α ∈ i.act C, ∑' s' : i.mdp.succs_univ C, i.mdp.P C α s' * f s'
:= by
  simp [MDP.dΦ, act, MDP.act, MDP.Φf, iInf_subtype, tsum_succs_univ']
  congr! with α
  apply le_antisymm
  · simp
    intro p C' h
    apply iInf_le_of_le _ (by rfl)
    refine Function.ne_iff.mpr ?_
    simp [mdp]
    use C', p, h, h₀' h
  · simp
    intro h
    apply Function.ne_iff.mp at h
    simp [mdp] at h
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
  exact i.h₀'

@[simp, grind]
theorem succs_univ_term : i.mdp.succs_univ (.term t σ) = {.bot} := by simp [mdp]
@[simp, grind]
theorem succs_univ_bot : i.mdp.succs_univ .bot = {.bot} := by simp [mdp]
@[simp, grind]
theorem succs_univ_prog :
    i.mdp.succs_univ (.prog C σ) = (conf₂_to_conf '' {c' | ∃ p α, i.r (C, σ) α p c'}) := by
  ext
  simp [mdp, conf₂_to_conf]
  grind


@[simp]
theorem dΦ_bot_eq : (i.mdp.dΦ (i.cost X))^[n] ⊥ .bot = 0 := by
  induction n <;> simp_all [-Function.iterate_succ, Function.iterate_succ', tsum_succs_univ']
  apply le_antisymm
  · have ⟨p, α, C', h⟩ := i.h₂' Conf.bot
    apply iInf_le_of_le α
    apply iInf_le_of_le (by simp [act]; grind)
    simp [*]
  · simp
@[simp]
theorem dΦ_term_eq :
    (i.mdp.dΦ (i.cost X))^[n] ⊥ (.term t σ) = if n = 0 then 0 else i.cost X (Conf.term t σ) := by
  induction n <;> simp_all [-Function.iterate_succ, Function.iterate_succ', tsum_succs_univ']
  nth_rw 2 [← add_zero (i.cost X (Conf.term t σ))]
  congr
  apply le_antisymm
  · have ⟨p, α, C', h⟩ := i.h₂' (Conf.term t σ)
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
  nth_rw 2 [← add_zero (i.cost X (Conf.term t σ))]
  congr
  simp

-- ⊢ (cost_p T A (C, σ) +
--     ⨅ α ∈ act (Conf.prog C σ),
--       ∑' (s' : ↑(mdp.succs_univ (Conf.prog C σ))),
--         mdp.P (Conf.prog C σ) α ↑s' *
--           match ↑s' with
--           | Conf.term t σ' => cost_t P A X (t, σ')
--           | Conf.prog C' σ' => Y C' X σ'
--           | Conf.bot => 0) =
--   sorry Y C X σ

def psucc (C : P) (σ : S) (α : A) : Set (ENNReal × (P ⊕ T) × S) := {s | i.r (C, σ) α s.fst s.snd}

theorem please₀ (C : P) (σ : S) (α : A) (f : ENNReal × (P ⊕ T) × S → ENNReal) :
      ∑' (s : (psucc C σ α)), f s.val
    = ∑' (s : {s // ∃ p, i.r (C, σ) α p s}),
        ∑' (p : {sp : ENNReal × (P ⊕ T) × S // sp.2 = s.val ∧ i.r (C, σ) α sp.1 sp.2}), f p.val
:= by
  simp [psucc]
  have := ENNReal.tsum_biUnion
            (ι:={s // ∃ p, i.r (C, σ) α p s})
            (t:=fun s ↦ {sp : ENNReal × (P ⊕ T) × S | sp.2 = s ∧ i.r (C, σ) α sp.1 sp.2}) (f:=f)
  simp at this
  rw [← this]
  · clear this
    apply tsum_eq_tsum_of_ne_zero_bij (fun ⟨⟨x, _⟩, _⟩ ↦ ⟨x, by simp_all; simp_all⟩)
    · intro ⟨_, _⟩ ⟨_, _⟩; simp_all; grind
    · rintro ⟨⟨p, (C | t), σ⟩, _⟩
      · simp; grind
      · simp; grind
    · simp
  · clear this
    intro ⟨p₀, s₀, hs₀⟩ _ ⟨p₁, s₁, hs₁⟩ _ h
    simp_all only [Set.mem_univ, ne_eq, Subtype.mk.injEq]
    intro Z hZ₁ hZ₂ ⟨p', s', σ'⟩ hZ
    simp_all
    have h₁ := hZ₁ hZ
    have h₂ := hZ₂ hZ
    simp_all
theorem please (C : P) (σ : S) (α : A) (f : ENNReal × (P ⊕ T) × S → ENNReal) :
      ∑' (s : (psucc C σ α)), f s.val
    = ∑' (x : ↑(i.mdp.succs_univ (Conf.prog C σ))) (p : {p // rr (Conf.prog C σ) (some α) p x.val}),
        if let some C := conf_to_conf₂ x.val then f (p, C) else 0 := by
  simp [please₀]
  symm
  apply tsum_eq_tsum_of_ne_zero_bij (fun ⟨⟨x, hx₀⟩, hx₁⟩ ↦ ⟨conf₂_to_conf x, by
    simp_all only [Function.mem_support, ne_eq, ENNReal.tsum_eq_zero, Subtype.forall, and_imp,
      Prod.forall, forall_eq, not_forall, mdp, MDP.ofRelation_succs_univ, rr_prog, conf₂_to_conf,
      Prod.exists, Sum.exists, Set.mem_setOf_eq]
    obtain ⟨p, hp, hp'⟩ := hx₁
    use α, p
    rcases x with ⟨(C | t), σ⟩ <;> simp_all⟩)
  · intro ⟨⟨_, _, _⟩, _⟩ ⟨⟨_, _, _⟩, _⟩; simp_all [conf₂_to_conf]; grind
  · intro ⟨_, _, _⟩; simp at *; simp [mdp] at *
    rintro p (h | h)
    · grind
    · grind
  · simp only [mdp, conf₂_to_conf, Subtype.forall, Function.mem_support, ne_eq,
    ENNReal.tsum_eq_zero, and_imp, Prod.forall, forall_eq, not_forall, forall_exists_index,
    Sum.forall]
    split_ands
    · intros C' σ' p h p' h' h''
      apply tsum_eq_tsum_of_ne_zero_bij (fun ⟨⟨⟨p₀, x⟩, h₀⟩, h₁⟩ ↦ ⟨p₀, by
        simp_all only [Function.mem_support, ne_eq, rr_prog, conf₂_to_conf, Option.some.injEq,
          exists_eq_right_right, Prod.exists, Sum.exists, Conf.prog.injEq, exists_eq_right,
          reduceCtorEq, and_false, exists_false, or_false]
        simp_all only
        obtain ⟨⟨_⟩, _⟩ := h₀
        assumption⟩)
      · intro ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩
        simp_all only [Subtype.mk.injEq]
        simp_all only [Function.mem_support, ne_eq]
        grind
      · intro ⟨_, _⟩
        simp_all only [Function.mem_support, ne_eq, Set.mem_range, Subtype.mk.injEq, Subtype.exists,
          exists_prop, Prod.exists, Prod.mk.injEq, existsAndEq, and_true, Sum.exists, Sum.inl.injEq,
          true_and, reduceCtorEq, false_and, exists_false, or_false, exists_eq_right_right,
          not_false_eq_true]
        grind
      · simp
    · intros C' σ' p h p' h' h''
      apply tsum_eq_tsum_of_ne_zero_bij (fun ⟨⟨⟨p₀, x⟩, h₀⟩, h₁⟩ ↦ ⟨p₀, by
        simp_all only [Function.mem_support, ne_eq, rr_prog, conf₂_to_conf, Option.some.injEq,
          exists_eq_right_right, Prod.exists, Sum.exists, reduceCtorEq, and_false, exists_false,
          Conf.term.injEq, exists_eq_right, false_or]
        simp_all only
        obtain ⟨⟨_⟩, _⟩ := h₀
        assumption⟩)
      · intro ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩
        simp_all only [Subtype.mk.injEq]
        simp_all only [Function.mem_support, ne_eq]
        grind
      · intro ⟨_, _⟩
        simp_all
        grind
      · simp

noncomputable def dς' : (P → 𝔼[S] →o 𝔼[S]) →o P → 𝔼[S] →o 𝔼[S] :=
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

noncomputable def dς : (P → 𝔼[S] →o 𝔼[S]) →o P → 𝔼[S] →o 𝔼[S] :=
  ⟨fun Y ↦ (fun C ↦ ⟨fun X σ ↦
    i.cost_p (C, σ) +
      ⨅ α ∈ i.act (Conf.prog C σ),
        match α with
        | some α => ∑' (s : i.psucc C σ α),
            s.val.fst *
              match s.val.snd with | (.inl C', σ') => Y C' X σ' | (.inr t, σ') => i.cost_t X (t, σ')
        | none => 0,
    by
      intro a b hab σ
      simp
      gcongr; split
      · gcongr; split
        · apply (Y _).mono hab
        · apply i.cost_t.mono hab
      · rfl⟩),
    by
      intro a b hab C X σ
      simp
      gcongr; split
      · gcongr; split
        · apply hab
        · rfl
      · rfl⟩

theorem dς_eq_dς' : i.dς = i.dς' := by
  ext Y C X σ
  simp [dς, dς', cost]
  congr! with α hα
  rcases α with (_ | α)
  · simp [act] at hα
  · simp_all
    have := please (A:=A) (C:=C) (σ:=σ) (α:=α) (f:=fun (s : ENNReal × (P ⊕ T) × S) ↦ s.1 *
      match s.2 with
      | (Sum.inl C', σ') => (Y C') X σ'
      | (Sum.inr t, σ') => cost_t P A X (t, σ'))
    simp [this]; clear this
    simp [mdp, ← ENNReal.tsum_mul_right]
    grind

noncomputable def aς : (P → 𝔼[S] →o 𝔼[S]) →o P → 𝔼[S] →o 𝔼[S] :=
  ⟨fun Y ↦ (fun C ↦ ⟨fun X σ ↦
    i.cost_p (C, σ) +
      ⨆ α ∈ i.act (Conf.prog C σ),
        match α with
        | some α => ∑' (s : i.psucc C σ α),
            s.val.fst *
              match s.val.snd with | (.inl C', σ') => Y C' X σ' | (.inr t, σ') => i.cost_t X (t, σ')
        | none => 0,
    by
      intro a b hab σ
      simp
      gcongr; split
      · gcongr; split
        · apply (Y _).mono hab
        · apply i.cost_t.mono hab
      · rfl⟩),
    by
      intro a b hab C X σ
      simp
      gcongr; split
      · gcongr; split
        · apply hab
        · rfl
      · rfl⟩

noncomputable def aς' : (P → 𝔼[S] →o 𝔼[S]) →o P → 𝔼[S] →o 𝔼[S] :=
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

theorem aς_eq_aς' : i.aς = i.aς' := by
  ext Y C X σ
  simp [aς, aς', cost]
  congr! with α hα
  rcases α with (_ | α)
  · simp [act] at hα
  · have := please (A:=A) (C:=C) (σ:=σ) (α:=α) (f:=fun (s : ENNReal × (P ⊕ T) × S) ↦ s.1 *
      match s.2 with
      | (Sum.inl C', σ') => (Y C') X σ'
      | (Sum.inr t, σ') => cost_t P A X (t, σ'))
    simp [this]; clear this
    simp [mdp, ← ENNReal.tsum_mul_right]
    grind

theorem tsum_ite_left {α β : Type*} [AddCommMonoid α] [TopologicalSpace α] (P : Prop) [Decidable P]
    (x : β → α) : (∑' (b : β), if P then x b else 0) = if P then ∑' (b : β), x b else 0 := by
  split_ifs <;> simp

@[mk_iff]
class FiniteBranching (P S T A : Type*) [Nonempty A] [i : SmallStepSemantics P S T A] : Prop where
  finite : ∀ C, {(α, p, C') | i.r C α p C'}.Finite

@[simp]
theorem mdp_act_term : i.mdp.act (Conf.term t σ) = {none} := by
  ext; simp [mdp]
@[simp]
theorem mdp_act_bot : i.mdp.act Conf.bot = {none} := by
  ext; simp [mdp]

instance [instFin : i.FiniteBranching] : i.mdp.FiniteBranching where
  act_fin C := by
    rcases C with (⟨t, σ⟩ | ⟨C, σ⟩ | _) <;> try simp
    have := instFin.finite (C, σ)
    suffices
          (Set.image (some ·.fst) {(α, p, C') | r (C, σ) (α : A) p (C' : (P ⊕ T) × S)})
        = (i.mdp.act (Conf.prog C σ)) by
      rw [← this]
      exact Set.Finite.image _ (instFin.finite (C, σ))
    ext α
    simp [mdp, conf₂_to_conf]
    grind
  succs_fin C α := by
    rcases C with (⟨t, σ⟩ | ⟨C, σ⟩ | _) <;> try simp
    · rcases α with (_ | α)
      · have : (Function.support (i.mdp.P (.term t σ) none)) = {.bot} := by
          ext; simp [mdp]
        simp [this]
      · have : (Function.support (i.mdp.P (.term t σ) α)) = {} := by
          ext; simp [mdp]
        simp [this]
    · rcases α with (_ | α)
      · have : (Function.support (i.mdp.P (.prog C σ) none)) = {} := by
          ext; simp [mdp]
        simp [this]
      · suffices
              (Function.support (mdp.P (Conf.prog C σ) (some α)))
            ⊆ (Set.image (conf₂_to_conf ·.snd.snd)
                {(α, p, C') | r (C, σ) (α : A) p (C' : (P ⊕ T) × S)}) by
          apply Set.Finite.subset _ this
          exact Set.Finite.image _ (instFin.finite (C, σ))
        intro
        simp [conf₂_to_conf, mdp]
        grind
    · rcases α with (_ | α)
      · have : (Function.support (i.mdp.P .bot none)) = {Conf.bot} := by
          ext; simp [mdp]
        simp [this]
      · have : (Function.support (i.mdp.P .bot α)) = {} := by
          ext; simp [mdp]
        simp [this]

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
  simp only [dς, OrderHom.coe_mk, dΦ_simp, cost]
  congr! 4 with α hα
  conv => right; arg 1; ext; simp [mdp]
  simp [← ENNReal.tsum_mul_right]
  rcases α with (_ | α)
  · simp [act] at hα
  · have := please (A:=A) (C:=C) (σ:=σ) (α:=α) (f:=fun (s : ENNReal × (P ⊕ T) × S) ↦ s.1 *
        match s.2 with
        | (Sum.inl C', σ') => (i.dop C') X σ'
        | (Sum.inr t, σ') => cost_t P A X (t, σ'))
    simp [this]; clear this
    congr! with ⟨x, hx⟩ ⟨p, hp⟩
    simp [mdp, conf₂_to_conf] at hx
    rcases hx with ⟨α₀, p₀, (⟨_, _, _, _, ⟨_⟩, ⟨_⟩⟩ | ⟨_, _, _, _, ⟨_⟩, ⟨_⟩⟩)⟩
      <;> (simp; congr)

theorem dop_isLeast (b : P → 𝔼[S] →o 𝔼[S]) (h : i.dς b ≤ b) : i.dop ≤ b := by
  rw [dop_eq_iSup_dΦ, iSup_le_iff]
  intro n
  induction n with
  | zero => intros _ _ _; simp
  | succ i ih =>
    refine le_trans (fun C X σ ↦ ?_) h
    simp [Function.iterate_succ', dς, -Function.iterate_succ, cost]
    gcongr with α hα
    rcases α with (_ | α)
    · simp [act] at hα
    · have := please (A:=A) (C:=C) (σ:=σ) (α:=α) (f:=fun (s : ENNReal × (P ⊕ T) × S) ↦ s.1 *
        match s.2 with
        | (Sum.inl C', σ') => (b C') X σ'
        | (Sum.inr t, σ') => cost_t P A X (t, σ'))
      simp [this]; clear this
      simp [mdp]
      simp [← ENNReal.tsum_mul_right]
      gcongr with x p
      obtain ⟨x, hx⟩ := x
      simp [conf₂_to_conf] at hx
      rcases hx with ⟨α₀, p₀, (⟨_, _, _, _, ⟨_⟩, ⟨_⟩⟩ | ⟨_, _, _, _, ⟨_⟩, ⟨_⟩⟩)⟩
      · simp
        gcongr
        apply ih
      · simp [cost]
        split_ifs <;> simp

theorem lfp_dς_eq_dop : lfp i.dς = i.dop :=
  (lfp_le_fixed _ i.dς_dop_eq_dop).antisymm (le_lfp _ i.dop_isLeast)

theorem dop_eq_iter : i.dop = ⨆ n, (i.dς)^[n] ⊥ := by
  apply le_antisymm
  · rw [dop_eq_iSup_dΦ]
    gcongr with n
    intro C X σ
    simp [dς_eq_dς']
    induction n generalizing C X σ with
    | zero => simp
    | succ n ih =>
      simp only [Function.iterate_succ', Function.comp_apply]
      nth_rw 1 [dΦ_simp]
      nth_rw 1 [dς']
      simp [cost]
      gcongr with α hα s
      obtain ⟨s, hs⟩ := s
      simp
      split
      · rename_i t σ'
        simp_all only [dΦ_term_eq, cost]
        split_ifs <;> simp
      · simp [ih]
      · simp
  · rw [dop_eq_iSup_succ_dΦ]
    gcongr with n
    intro C X σ
    simp [dς_eq_dς']
    induction n generalizing C X σ with
    | zero => simp
    | succ n ih =>
      simp only [Function.iterate_succ', Function.comp_apply]
      nth_rw 1 [dΦ_simp]
      nth_rw 1 [dς']
      simp [cost]
      gcongr with α hα s
      obtain ⟨s, hs⟩ := s
      simp
      split
      · rename_i t σ'
        induction n with
        | zero => simp [cost]
        | succ n ih =>
          simp only [Function.iterate_succ', Function.comp_apply]
          simp [cost]
      · simp [ih]
      · simp

class DemonicExpectationTransformer (P S : Type*) where
  det : P → 𝔼[S] →o 𝔼[S]

class SoundDemonicExpectationTransformer (P S T A : Type*) [Nonempty A]
    [i :  SmallStepSemantics P S T A] [i.mdp.FiniteBranching]
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
  simp only [aς, OrderHom.coe_mk, aΦ_simp, cost]
  congr! 4 with α hα
  rcases α with (_ | α)
  · simp [act] at hα
  · conv => right; arg 1; ext; simp [mdp]
    simp [← ENNReal.tsum_mul_right]
    have := please (A:=A) (C:=C) (σ:=σ) (α:=α) (f:=fun (s : ENNReal × (P ⊕ T) × S) ↦ s.1 *
        match s.2 with
        | (Sum.inl C', σ') => (i.aop C') X σ'
        | (Sum.inr t, σ') => cost_t P A X (t, σ'))
    simp [this]; clear this
    congr! with ⟨x, hx⟩ ⟨p, hp⟩
    simp [mdp, conf₂_to_conf] at hx
    rcases hx with ⟨α₀, p₀, (⟨_, _, _, _, ⟨_⟩, ⟨_⟩⟩ | ⟨_, _, _, _, ⟨_⟩, ⟨_⟩⟩)⟩ <;> (simp; congr)

theorem aop_isLeast (b : P → 𝔼[S] →o 𝔼[S]) (h : i.aς b ≤ b) : i.aop ≤ b := by
  rw [aop_eq_iSup_aΦ, iSup_le_iff]
  intro n
  induction n with
  | zero => intros _ _ _; simp
  | succ i ih =>
    refine le_trans (fun C X σ ↦ ?_) h
    simp [Function.iterate_succ', aς, -Function.iterate_succ, cost]
    gcongr with α hα
    rcases α with (_ | α)
    · simp [act] at hα
    · have := please (A:=A) (C:=C) (σ:=σ) (α:=α) (f:=fun (s : ENNReal × (P ⊕ T) × S) ↦ s.1 *
        match s.2 with
        | (Sum.inl C', σ') => (b C') X σ'
        | (Sum.inr t, σ') => cost_t P A X (t, σ'))
      simp [this]; clear this
      simp [mdp]
      simp [← ENNReal.tsum_mul_right]
      gcongr with x p
      obtain ⟨x, hx⟩ := x
      simp [conf₂_to_conf] at hx
      rcases hx with ⟨α₀, p₀, (⟨_, _, _, _, ⟨_⟩, ⟨_⟩⟩ | ⟨_, _, _, _, ⟨_⟩, ⟨_⟩⟩)⟩
      · simp
        gcongr
        apply ih
      · simp [cost]
        split_ifs <;> simp

theorem lfp_aς_eq_aop : lfp i.aς = i.aop :=
  (lfp_le_fixed _ i.aς_aop_eq_aop).antisymm (le_lfp _ i.aop_isLeast)

theorem aop_eq_iter : i.aop = ⨆ n, (i.aς)^[n] ⊥ := by
  apply le_antisymm
  · rw [aop_eq_iSup_aΦ]
    gcongr with n
    intro C X σ
    simp [aς_eq_aς']
    induction n generalizing C X σ with
    | zero => simp
    | succ n ih =>
      simp only [Function.iterate_succ', Function.comp_apply]
      nth_rw 1 [aΦ_simp]
      nth_rw 1 [aς']
      simp [cost]
      gcongr with α hα s
      obtain ⟨s, hs⟩ := s
      simp
      split
      · rename_i t σ'
        simp_all only [aΦ_term_eq, cost]
        split_ifs <;> simp
      · simp [ih]
      · simp
  · rw [aop_eq_iSup_succ_aΦ]
    gcongr with n
    intro C X σ
    simp [aς_eq_aς']
    induction n generalizing C X σ with
    | zero => simp
    | succ n ih =>
      simp only [Function.iterate_succ', Function.comp_apply]
      nth_rw 1 [aΦ_simp]
      nth_rw 1 [aς']
      simp [cost]
      gcongr with α hα s
      obtain ⟨s, hs⟩ := s
      simp
      split
      · rename_i t σ'
        induction n with
        | zero => simp [cost]
        | succ n ih =>
          simp only [Function.iterate_succ', Function.comp_apply]
          simp [cost]
      · simp [ih]
      · simp

class AngelicExpectationTransformer (P S : Type*) where
  aet : P → 𝔼[S] →o 𝔼[S]

class SoundAngelicExpectationTransformer (P S T A : Type*) [Nonempty A]
    [i : SmallStepSemantics P S T A]
    [i' : AngelicExpectationTransformer P S] where
  aet_le_aop : i'.aet ≤ i.aop
  aet_prefixed_point : i.aς i'.aet ≤ i'.aet

variable [i' : AngelicExpectationTransformer P S] [SoundAngelicExpectationTransformer P S T A]

theorem SoundAngelicExpectationTransformer.aet_eq_aop : i'.aet = i.aop :=
  le_antisymm aet_le_aop (aop_isLeast i'.aet aet_prefixed_point)

end Angelic

attribute [-simp] Function.iterate_succ in
theorem dop_le_seq [i.FiniteBranching] (seq : P → P → P) (after : P → (P ⊕ T) × S → (P ⊕ T) × S)
    (h_cost_seq : ∀ C C' σ, i.cost_p (seq C C', σ) = i.cost_p (C, σ))
    (h_seq_act : ∀ C C' σ, i.act (.prog (seq C C') σ) = i.act (.prog C σ))
    (h_succ : ∀ {C C' σ p α s}, (p, s) ∈ i.psucc C σ α → (p, after C' s) ∈ i.psucc (seq C C') σ α)
    (h_after_p : ∀ {C C' σ}, after C' (.inl C, σ) = (.inl (seq C C'), σ))
    (h_after_t : ∀ {t C C' σ}, after C (.inr t, σ) = C' →
      (C' = (.inl C, σ)) ∨ (C' = (.inr t, σ) ∧ ∀ X, i.cost_t X (t, σ) = 0))
    (h_c : ∀ {X t σ}, i.cost_t X (t, σ) ≤ X σ)
    (after_inj : ∀ x, Function.Injective (after x)) :
      i.dop C ∘ i.dop C' ≤ i.dop (seq C C') := by
  intro X σ
  nth_rw 1 [dop_eq_iter]
  simp
  intro n
  induction n generalizing C C' σ with
  | zero => simp
  | succ n ih =>
    nth_rw 2 [← dς_dop_eq_dop]
    rw [Function.iterate_succ', Function.comp_apply]
    nth_rw 1 [dς]
    nth_rw 2 [dς]
    simp [h_cost_seq, h_seq_act]
    refine add_le_add (le_refl _) (iInf₂_mono fun α hα ↦ ?_)
    rcases α with (_ | α)
    · simp [act] at hα
    simp
    apply Summable.tsum_le_tsum_of_inj (fun ⟨⟨p, a⟩, ha⟩ ↦ ⟨⟨p, after C' a⟩, h_succ ha⟩) <;> simp
    · intro ⟨⟨_, c₁⟩, _⟩ ⟨⟨_, c₂⟩, _⟩ h
      simp at h
      have := @after_inj C' c₁ c₂ h.right
      grind
    · intro p
      constructor
      · intro C₁ σ₁ h
        gcongr
        simp [h_after_p]
        apply ih
      · intro t σ₁ h
        gcongr
        split
        · rename_i C₀ σ₀ h
          have := h_after_t h
          simp at this
          obtain ⟨⟨_⟩, ⟨_⟩⟩ := this
          apply h_c
        · rename_i t₀ σ₀ h
          have := h_after_t h
          simp at this
          obtain ⟨⟨⟨_⟩, ⟨_⟩⟩, h'⟩ := this
          simp [h']

attribute [-simp] Function.iterate_succ in
theorem aop_le_seq (seq : P → P → P) (after : P → (P ⊕ T) × S → (P ⊕ T) × S)
    (h_cost_seq : ∀ C C' σ, i.cost_p (seq C C', σ) = i.cost_p (C, σ))
    (h_seq_act : ∀ C C' σ, i.act (.prog (seq C C') σ) = i.act (.prog C σ))
    (h_succ : ∀ {C C' σ p α s}, (p, s) ∈ i.psucc C σ α → (p, after C' s) ∈ i.psucc (seq C C') σ α)
    (h_after_p : ∀ {C C' σ}, after C' (.inl C, σ) = (.inl (seq C C'), σ))
    (h_after_t : ∀ {t C C' σ}, after C (.inr t, σ) = C' →
      (C' = (.inl C, σ)) ∨ (C' = (.inr t, σ) ∧ ∀ X, i.cost_t X (t, σ) = 0))
    (h_c : ∀ {X t σ}, i.cost_t X (t, σ) ≤ X σ)
    (after_inj : ∀ x, Function.Injective (after x)) :
      i.aop C ∘ i.aop C' ≤ i.aop (seq C C') := by
  intro X σ
  nth_rw 1 [aop_eq_iter]
  simp
  intro n
  induction n generalizing C C' σ with
  | zero => simp
  | succ n ih =>
    nth_rw 2 [← aς_aop_eq_aop]
    rw [Function.iterate_succ', Function.comp_apply]
    nth_rw 1 [aς]
    nth_rw 2 [aς]
    simp [h_cost_seq, h_seq_act]
    refine add_le_add (le_refl _) (iSup₂_mono fun α hα ↦ ?_)
    rcases α with (_ | α)
    · simp [act] at hα
    simp
    apply Summable.tsum_le_tsum_of_inj (fun ⟨⟨p, a⟩, ha⟩ ↦ ⟨⟨p, after C' a⟩, h_succ ha⟩) <;> simp
    · intro ⟨⟨_, c₁⟩, _⟩ ⟨⟨_, c₂⟩, _⟩ h
      simp at h
      have := @after_inj C' c₁ c₂ h.right
      grind
    · intro p
      constructor
      · intro C₁ σ₁ h
        gcongr
        simp [h_after_p]
        apply ih
      · intro t σ₁ h
        gcongr
        split
        · rename_i C₀ σ₀ h
          have := h_after_t h
          simp at this
          obtain ⟨⟨_⟩, ⟨_⟩⟩ := this
          apply h_c
        · rename_i t₀ σ₀ h
          have := h_after_t h
          simp at this
          obtain ⟨⟨⟨_⟩, ⟨_⟩⟩, h'⟩ := this
          simp [h']

end SmallStepSemantics
