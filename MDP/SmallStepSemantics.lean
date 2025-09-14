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

  cost_p : 𝔼[S] →o P × S → ENNReal
  cost_t : 𝔼[S] →o T × S → ENNReal

namespace SmallStepSemantics

variable {P S A T : Type*} [Nonempty A] [𝕊 : SmallStepSemantics P S T A]

noncomputable instance : Inhabited A := Classical.inhabited_of_nonempty ‹_›

@[grind]
inductive rr : Conf P S T → Option A → ENNReal → Conf P S T → Prop where
  | bot : rr .bot none 1 .bot
  | term : rr (.term _ _) none 1 .bot
  | prog₀ : 𝕊.r (C, σ) α p (.inl C', σ') → rr (.prog C σ) α p (.prog C' σ')
  | prog₁ : 𝕊.r (C, σ) α p (.inr t, σ') → rr (.prog C σ) α p (.term t σ')

@[simp] theorem rr.bot_to : 𝕊.rr .bot α p c' ↔ α = none ∧ p = 1 ∧ c' = .bot := by grind
@[simp] theorem rr.term_to : 𝕊.rr (.term t σ) α p c' ↔ α = none ∧ p = 1 ∧ c' = .bot := by grind

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
      𝕊.rr (.prog C σ) α p c'
    ↔ ∃ c'' α', 𝕊.r (C, σ) α' p c'' ∧ conf₂_to_conf c'' = c' ∧ some α' = α := by
  simp [conf₂_to_conf]; grind

@[grind]
theorem h₀' : ∀ {c α p c'}, 𝕊.rr c α p c' → ¬p = 0 := by
  intro C α p c'; rintro (_ | _) <;> (try simp_all) <;> try apply 𝕊.h₀ ‹_›
@[grind]
theorem h₁' : ∀ {c α p₀ c'}, 𝕊.rr c α p₀ c' → ∑' (b) (p : { p // 𝕊.rr c α p b }), p.val = 1 := by
  intro C α p c'; rintro (_ | _)
  · rw [tsum_eq_single .bot, tsum_eq_single ⟨1, by grind⟩] <;> simp_all
  · rw [tsum_eq_single .bot, tsum_eq_single ⟨1, by grind⟩] <;> simp_all
  · rename_i h
    conv => right; rw [← 𝕊.h₁ h]
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
    conv => right; rw [← 𝕊.h₁ h]
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

theorem h₂' : ∀ s, ∃ p a x, 𝕊.rr s a p x := by
  rintro (⟨t, σ⟩ | ⟨C, σ⟩ | _)
  · use 1, default, .bot; grind
  · have ⟨p, α, c', h⟩ := 𝕊.h₂ (C, σ)
    use p, α, conf₂_to_conf c'
    grind
  · use 1, default, .bot; grind
theorem h₃ : ∀ {t σ c'}, (∃ α p, 𝕊.rr (Conf.term t σ) α p c') ↔ c' = Conf.bot := by
  intros
  constructor
  · grind
  · rintro ⟨_⟩; use none, 1; grind
theorem h₄ : ∀ {c'}, (∃ α p, 𝕊.rr Conf.bot α p c') ↔ c' = Conf.bot := by
  intro
  constructor
  · grind
  · rintro ⟨_⟩; use none, 1; grind

noncomputable def mdp : MDP (Conf P S T) (Option A) := MDP.ofRelation 𝕊.rr 𝕊.h₀' 𝕊.h₁' 𝕊.h₂'

def psucc (C : P) (σ : S) (α : A) : Set (ENNReal × (P ⊕ T) × S) := {s | 𝕊.r (C, σ) α s.fst s.snd}

theorem please₀ (C : P) (σ : S) (α : A) (f : ENNReal × (P ⊕ T) × S → ENNReal) :
      ∑' (s : (psucc C σ α)), f s.val
    = ∑' (s : {s // ∃ p, 𝕊.r (C, σ) α p s}),
        ∑' (p : {sp : ENNReal × (P ⊕ T) × S // sp.2 = s.val ∧ 𝕊.r (C, σ) α sp.1 sp.2}), f p.val
:= by
  simp [psucc]
  have := ENNReal.tsum_biUnion
            (ι:={s // ∃ p, 𝕊.r (C, σ) α p s})
            (t:=fun s ↦ {sp : ENNReal × (P ⊕ T) × S | sp.2 = s ∧ 𝕊.r (C, σ) α sp.1 sp.2}) (f:=f)
  simp at this
  rw [← this]
  · clear this
    apply tsum_eq_tsum_of_ne_zero_bij (fun ⟨⟨x, _⟩, _⟩ ↦ ⟨x, by simp_all; simp_all⟩)
    · intro ⟨_, _⟩ ⟨_, _⟩; simp_all; grind
    · rintro ⟨⟨p, (C | t), σ⟩, _⟩ <;> simp <;> grind
    · grind
  · clear this
    intro ⟨p₀, s₀, hs₀⟩ _ ⟨p₁, s₁, hs₁⟩ _ h
    intro Z hZ₁ hZ₂ ⟨p', s', σ'⟩ hZ
    specialize hZ₁ hZ
    specialize hZ₂ hZ
    simp_all only [ne_eq, Set.mem_setOf_eq]
theorem please (C : P) (σ : S) (α : A) (f : ENNReal × (P ⊕ T) × S → ENNReal) :
      ∑' (s : (psucc C σ α)), f s.val
    = ∑' (x : ↑(𝕊.mdp.succs_univ (Conf.prog C σ))) (p : {p // rr (Conf.prog C σ) (some α) p x.val}),
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
        simp_all only [Function.mem_support, rr_prog, conf₂_to_conf, Option.some.injEq,
          exists_eq_right_right, Prod.exists, Sum.exists, Conf.prog.injEq, exists_eq_right]
        simp_all only
        obtain ⟨⟨_⟩, _⟩ := h₀
        left; assumption⟩)
      · intro ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩
        simp_all only [Subtype.mk.injEq]
        simp_all only [Function.mem_support, ne_eq]
        grind
      · intro ⟨_, _⟩
        simp_all only [Function.mem_support, Set.mem_range, Subtype.exists]
        grind
      · simp
    · intros C' σ' p h p' h' h''
      apply tsum_eq_tsum_of_ne_zero_bij (fun ⟨⟨⟨p₀, x⟩, h₀⟩, h₁⟩ ↦ ⟨p₀, by
        simp_all only [Function.mem_support, ne_eq, rr_prog, conf₂_to_conf, Option.some.injEq,
          exists_eq_right_right, Prod.exists, Sum.exists, reduceCtorEq, Conf.term.injEq,
          exists_eq_right]
        simp_all only
        obtain ⟨⟨_⟩, _⟩ := h₀
        right; assumption⟩)
      · intro ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩
        simp_all only [Subtype.mk.injEq]
        simp_all only [Function.mem_support, ne_eq]
        grind
      · intro ⟨_, _⟩
        simp_all
        grind
      · simp

def cost (X : 𝔼[S]) : 𝕊.mdp.Costs
  | .bot => 0
  | .term t σ => 𝕊.cost_t X (t, σ)
  | .prog C σ => 𝕊.cost_p X (C, σ)

def cost_mono : Monotone 𝕊.cost := by
  intro a b h c
  simp [cost]
  split
  · rfl
  · apply 𝕊.cost_t.mono h
  · apply 𝕊.cost_p.mono h

@[simp] theorem cost_bot (X) : 𝕊.cost X .bot = 0 := by rfl

def act (c : Conf P S T) : Set (Option A) := {α | ∃ p c', 𝕊.rr c α p c'}

noncomputable def dop (C : P) : 𝔼[S] →o 𝔼[S] :=
  ⟨fun X ↦ (lfp (𝕊.mdp.dΦ <| 𝕊.cost X) <| Conf.prog C ·), fun a b h σ ↦ by
    suffices lfp (𝕊.mdp.dΦ (𝕊.cost a)) ≤ lfp (𝕊.mdp.dΦ (𝕊.cost b)) by exact this _
    gcongr
    apply MDP.dΦ.monotone' (𝕊.cost_mono h)⟩
noncomputable def aop (C : P) : 𝔼[S] →o 𝔼[S] :=
  ⟨fun X ↦ (lfp (𝕊.mdp.aΦ <| 𝕊.cost X) <| Conf.prog C ·), fun a b h σ ↦ by
    suffices lfp (MDP.aΦ (𝕊.cost a)) ≤ lfp (MDP.aΦ (𝕊.cost b)) by exact this _
    gcongr
    apply MDP.aΦ.monotone' (𝕊.cost_mono h)⟩

open scoped Classical in
theorem tsum_succs_univ' (f : 𝕊.mdp.succs_univ c → ENNReal) :
    (∑' s', f s') = ∑' s', if h : _ then f ⟨s', h⟩ else 0 := by
  symm
  apply tsum_eq_tsum_of_ne_zero_bij (↑↑·) _ _ <;> try simp_all
  intro ⟨_, _⟩ ⟨_, _⟩; simp; apply SetCoe.ext

@[simp]
noncomputable def dΦ' (c : 𝕊.mdp.Costs) (C : Conf P S T) (f : 𝕊.mdp.Costs) : ENNReal :=
    c C + ⨅ α ∈ 𝕊.act C, match C with
        | .prog C σ =>
          match α with
          | some α => ∑' (s : 𝕊.psucc C σ α),
            s.val.fst *
              match s.val.snd with
              | (.inl C', σ') => f (.prog C' σ') | (.inr t, σ') => f (.term t σ')
          | none => 0
        | .term _ _ | .bot => match α with | some _ => 0 | none => f .bot

@[simp]
noncomputable def aΦ' (c : 𝕊.mdp.Costs) (C : Conf P S T) (f : 𝕊.mdp.Costs) : ENNReal :=
    c C + ⨆ α ∈ 𝕊.act C, match C with
        | .prog C σ =>
          match α with
          | some α => ∑' (s : 𝕊.psucc C σ α),
            s.val.fst *
              match s.val.snd with
              | (.inl C', σ') => f (.prog C' σ') | (.inr t, σ') => f (.term t σ')
          | none => 0
        | .term _ _ | .bot => match α with | some _ => 0 | none => f .bot

@[simp]
theorem dΦ_simp {C : Conf P S T} :
    𝕊.mdp.dΦ c f C = 𝕊.dΦ' c C f
:= by
  simp [MDP.dΦ, MDP.act, MDP.Φf, iInf_subtype, tsum_succs_univ', -dΦ']
  simp [dΦ']
  congr! with α hα
  · split <;> split
    · rename_i C σ _ _ α _ _
      have := please (A:=A) (C:=C) (σ:=σ) (α:=α) (f:=fun (s : ENNReal × (P ⊕ T) × S) ↦ s.1 *
        match s.2 with
        | (Sum.inl C', σ') => f (.prog C' σ')
        | (Sum.inr t, σ') => f (.term t σ'))
      simp at this
      rw [this]; clear this
      simp [tsum_succs_univ']
      simp [mdp, ← ENNReal.tsum_mul_right]
      grind
    · simp [mdp]
    · simp [mdp]
    · rw [tsum_eq_single .bot]
      · simp [mdp]
        rw [tsum_eq_single ⟨1, by simp⟩] <;> grind
      · simp +contextual [mdp]
    · simp [mdp]
    · rw [tsum_eq_single .bot]
      · simp [mdp]
        rw [tsum_eq_single ⟨1, by simp⟩] <;> grind
      · simp +contextual [mdp]
  · simp [act, mdp, Function.ne_iff]
    grind
@[simp]
theorem aΦ_simp {C : Conf P S T} :
    𝕊.mdp.aΦ c f C = 𝕊.aΦ' c C f
:= by
  simp [MDP.aΦ, MDP.act, MDP.Φf, iSup_subtype, tsum_succs_univ', -aΦ']
  simp [aΦ']
  congr! with α hα
  · split <;> split
    · rename_i C σ _ _ α _ _
      have := please (A:=A) (C:=C) (σ:=σ) (α:=α) (f:=fun (s : ENNReal × (P ⊕ T) × S) ↦ s.1 *
        match s.2 with
        | (Sum.inl C', σ') => f (.prog C' σ')
        | (Sum.inr t, σ') => f (.term t σ'))
      simp at this
      rw [this]; clear this
      simp [tsum_succs_univ']
      simp [mdp, ← ENNReal.tsum_mul_right]
      grind
    · simp [mdp]
    · simp [mdp]
    · rw [tsum_eq_single .bot]
      · simp [mdp]
        rw [tsum_eq_single ⟨1, by simp⟩] <;> grind
      · simp +contextual [mdp]
    · simp [mdp]
    · rw [tsum_eq_single .bot]
      · simp [mdp]
        rw [tsum_eq_single ⟨1, by simp⟩] <;> grind
      · simp +contextual [mdp]
  · simp [act, mdp, Function.ne_iff]
    grind

@[simp, grind]
theorem succs_univ_term : 𝕊.mdp.succs_univ (.term t σ) = {.bot} := by simp [mdp]
@[simp, grind]
theorem succs_univ_bot : 𝕊.mdp.succs_univ .bot = {.bot} := by simp [mdp]
@[simp, grind]
theorem succs_univ_prog :
    𝕊.mdp.succs_univ (.prog C σ) = (conf₂_to_conf '' {c' | ∃ p α, 𝕊.r (C, σ) α p c'}) := by
  ext
  simp [mdp, conf₂_to_conf]
  grind


@[simp]
theorem dΦ_bot_eq : (𝕊.mdp.dΦ (𝕊.cost X))^[n] ⊥ .bot = 0 := by
  induction n <;> simp_all [-Function.iterate_succ, Function.iterate_succ']
  apply le_antisymm
  · have ⟨p, α, C', h⟩ := 𝕊.h₂' Conf.bot
    apply iInf_le_of_le α
    apply iInf_le_of_le (by simp [act]; grind)
    simp only [nonpos_iff_eq_zero]
    grind
  · simp
@[simp]
theorem dΦ_term_eq :
    (𝕊.mdp.dΦ (𝕊.cost X))^[n] ⊥ (.term t σ) = if n = 0 then 0 else 𝕊.cost X (Conf.term t σ) := by
  induction n <;> simp_all [-Function.iterate_succ, Function.iterate_succ']
  nth_rw 2 [← add_zero (𝕊.cost X (Conf.term t σ))]
  congr
  apply le_antisymm
  · have ⟨p, α, C', h⟩ := 𝕊.h₂' (Conf.term t σ)
    apply iInf_le_of_le α
    apply iInf_le_of_le (by simp [act]; grind)
    simp
    grind
  · simp

@[simp]
theorem aΦ_bot_eq : (𝕊.mdp.aΦ (𝕊.cost X))^[n] ⊥ .bot = 0 := by
  induction n <;> simp_all [-Function.iterate_succ, Function.iterate_succ', act]
attribute [-simp] dΦ_simp in
@[simp]
theorem aΦ_term_eq :
    (𝕊.mdp.aΦ (𝕊.cost X))^[n] ⊥ (.term t σ) = if n = 0 then 0 else 𝕊.cost X (Conf.term t σ) := by
  induction n <;> simp_all [-Function.iterate_succ, Function.iterate_succ', act]

noncomputable def dς' : (P → 𝔼[S] →o 𝔼[S]) →o P → 𝔼[S] →o 𝔼[S] :=
  ⟨fun Y ↦ (fun C ↦ ⟨fun X σ ↦
    𝕊.mdp.dΦ (𝕊.cost X)
      (match · with
      | .term t σ' => 𝕊.cost X (.term t σ') | .prog C' σ' => Y C' X σ' | .bot => 0) (.prog C σ),
      fun a b h σ ↦ by
        simp
        gcongr
        · apply 𝕊.cost_mono h
        · split <;> gcongr; split
          · apply (Y _).mono h
          · apply 𝕊.cost_mono h⟩),
    by
      intro _ _ _ _ _ _
      apply (𝕊.mdp.dΦ _).mono
      rintro (_ | ⟨_ , _⟩) <;> try rfl
      apply_assumption⟩

noncomputable def dς : (P → 𝔼[S] →o 𝔼[S]) →o P → 𝔼[S] →o 𝔼[S] :=
  ⟨fun Y ↦ (fun C ↦ ⟨fun X σ ↦ 𝕊.dΦ' (𝕊.cost X) (.prog C σ) (fun s' ↦
    match s' with
    | .prog C' σ' => Y C' X σ'
    | .term t σ' => 𝕊.cost_t X (t, σ')
    | .bot => 0),
  fun a b hab σ ↦ by
    simp
    gcongr
    · apply 𝕊.cost_mono hab
    · split <;> gcongr; split
      · apply (Y _).mono hab
      · apply 𝕊.cost_t.mono hab⟩),
  fun a b hab C X σ ↦ by
    simp
    gcongr; split <;> gcongr; split
    · apply hab
    · rfl⟩

theorem dς_eq_dς' : 𝕊.dς = 𝕊.dς' := by
  ext Y C X σ
  simp [dς, dς', cost]

noncomputable def aς : (P → 𝔼[S] →o 𝔼[S]) →o P → 𝔼[S] →o 𝔼[S] :=
  ⟨fun Y ↦ (fun C ↦ ⟨fun X σ ↦ 𝕊.aΦ' (𝕊.cost X) (.prog C σ) (fun s' ↦
    match s' with
    | .prog C' σ' => Y C' X σ'
    | .term t σ' => 𝕊.cost_t X (t, σ')
    | .bot => 0),
  fun a b hab σ ↦ by
    simp
    gcongr
    · apply 𝕊.cost_mono hab
    · split <;> gcongr; split
      · apply (Y _).mono hab
      · apply 𝕊.cost_t.mono hab⟩),
  fun a b hab C X σ ↦ by
    simp
    gcongr; split <;> gcongr; split
    · apply hab
    · rfl⟩

noncomputable def aς' : (P → 𝔼[S] →o 𝔼[S]) →o P → 𝔼[S] →o 𝔼[S] :=
  ⟨fun Y ↦ (fun C ↦ ⟨fun X σ ↦
    𝕊.mdp.aΦ (𝕊.cost X)
      (match · with
      | .term t σ' => 𝕊.cost X (.term t σ') | .prog C' σ' => Y C' X σ' | .bot => 0) (.prog C σ),
      fun a b h σ ↦ by
        simp
        gcongr
        · apply 𝕊.cost_mono h
        · split <;> gcongr; split
          · apply (Y _).mono h
          · apply 𝕊.cost_mono h⟩),
    by
      intro _ _ _ _ _ _
      apply (𝕊.mdp.aΦ _).mono
      rintro (_ | ⟨_ , _⟩) <;> try rfl
      apply_assumption⟩

theorem aς_eq_aς' : 𝕊.aς = 𝕊.aς' := by
  ext Y C X σ
  simp [aς, aς', cost]

theorem tsum_ite_left {α β : Type*} [AddCommMonoid α] [TopologicalSpace α] (P : Prop) [Decidable P]
    (x : β → α) : (∑' (b : β), if P then x b else 0) = if P then ∑' (b : β), x b else 0 := by
  split_ifs <;> simp

@[mk_iff]
class FiniteBranching (P S T A : Type*) [Nonempty A] [𝕊 : SmallStepSemantics P S T A] : Prop where
  finite : ∀ C, {(α, p, C') | 𝕊.r C α p C'}.Finite

@[simp]
theorem mdp_act_term : 𝕊.mdp.act (Conf.term t σ) = {none} := by
  ext; simp [mdp]
@[simp]
theorem mdp_act_bot : 𝕊.mdp.act Conf.bot = {none} := by
  ext; simp [mdp]

instance instFiniteBrachingMDP [instFin : 𝕊.FiniteBranching] : 𝕊.mdp.FiniteBranching where
  act_fin C := by
    rcases C with (⟨t, σ⟩ | ⟨C, σ⟩ | _) <;> try simp
    have := instFin.finite (C, σ)
    suffices
          (Set.image (some ·.fst) {(α, p, C') | r (C, σ) (α : A) p (C' : (P ⊕ T) × S)})
        = (𝕊.mdp.act (Conf.prog C σ)) by
      rw [← this]
      exact Set.Finite.image _ (instFin.finite (C, σ))
    ext α
    simp [mdp, conf₂_to_conf]
    grind
  succs_fin C α := by
    rcases C with (⟨t, σ⟩ | ⟨C, σ⟩ | _) <;> try simp
    · rcases α with (_ | α)
      · have : (Function.support (𝕊.mdp.P (.term t σ) none)) = {.bot} := by
          ext; simp [mdp]
        simp [this]
      · have : (Function.support (𝕊.mdp.P (.term t σ) α)) = {} := by
          ext; simp [mdp]
        simp [this]
    · rcases α with (_ | α)
      · have : (Function.support (𝕊.mdp.P (.prog C σ) none)) = {} := by
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
      · have : (Function.support (𝕊.mdp.P .bot none)) = {Conf.bot} := by
          ext; simp [mdp]
        simp [this]
      · have : (Function.support (𝕊.mdp.P .bot α)) = {} := by
          ext; simp [mdp]
        simp [this]

section Demonic

variable [𝕊.mdp.FiniteBranching]

@[simp]
theorem lfp_dΦ_term :
    lfp (𝕊.mdp.dΦ (𝕊.cost X)) (Conf.term t σ) = 𝕊.cost X (Conf.term t σ) := by
  rw [MDP.lfp_dΦ_eq_iSup_dΦ]
  simp
  apply le_antisymm
  · simp
    intro 𝕊
    split_ifs <;> simp
  · apply le_iSup_of_le 1
    simp
@[simp]
theorem lfp_dΦ_bot :
    lfp (𝕊.mdp.dΦ (𝕊.cost X)) Conf.bot = 0 := by
  rw [MDP.lfp_dΦ_eq_iSup_dΦ]
  simp

theorem dop_eq_iSup_dΦ :
    𝕊.dop
  = ⨆ n, fun C ↦ ⟨fun X σ ↦ (𝕊.mdp.dΦ (𝕊.cost X))^[n] ⊥ (.prog C σ), fun a b h σ ↦ by
    simp
    suffices (⇑(MDP.dΦ (𝕊.cost a)))^[n] ⊥ ≤ (⇑(MDP.dΦ (𝕊.cost b)))^[n] ⊥ by apply this
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [Function.iterate_succ', Function.comp_apply]
      exact apply_mono (MDP.dΦ.monotone' (𝕊.cost_mono h)) ih⟩ := by
  ext C X σ; rw [dop]
  simp [fixedPoints.lfp_eq_sSup_iterate _ MDP.dΦ_ωScottContinuous]
theorem dop_eq_iSup_succ_dΦ :
      𝕊.dop
    = ⨆ n, fun C ↦ ⟨fun X σ ↦ (𝕊.mdp.dΦ (𝕊.cost X))^[n + 1] ⊥ (.prog C σ), fun a b h σ ↦ by
      simp only
      suffices (⇑(MDP.dΦ (𝕊.cost a)))^[n + 1] ⊥ ≤ (⇑(MDP.dΦ (𝕊.cost b)))^[n + 1] ⊥ by apply this
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
theorem dς_dop_eq_dop : 𝕊.dς 𝕊.dop = 𝕊.dop := by
  ext C X σ
  simp [dop]
  rw [← map_lfp]
  simp [dς, OrderHom.coe_mk, dΦ_simp, cost, dop]

theorem dop_isLeast (b : P → 𝔼[S] →o 𝔼[S]) (h : 𝕊.dς b ≤ b) : 𝕊.dop ≤ b := by
  rw [dop_eq_iSup_dΦ, iSup_le_iff]
  intro n
  induction n with
  | zero => intros _ _ _; simp
  | succ 𝕊 ih =>
    refine le_trans (fun C X σ ↦ ?_) h
    simp [Function.iterate_succ', dς, -Function.iterate_succ, cost]
    gcongr with α hα
    rcases α with (_ | α)
    · simp [act] at hα
    · simp
      gcongr
      split
      · apply ih
      · split_ifs <;> simp

theorem lfp_dς_eq_dop : lfp 𝕊.dς = 𝕊.dop :=
  (lfp_le_fixed _ 𝕊.dς_dop_eq_dop).antisymm (le_lfp _ 𝕊.dop_isLeast)

theorem dop_eq_iter : 𝕊.dop = ⨆ n, (𝕊.dς)^[n] ⊥ := by
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
      split <;> gcongr; split
      · apply ih
      · split_ifs <;> simp
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
      split <;> gcongr; split
      · apply ih
      · rename_i t σ'
        induction n with
        | zero => simp [cost]
        | succ n ih =>
          simp only [Function.iterate_succ', Function.comp_apply]
          simp [cost]

class DemonicET {P S T A : Type*} [Nonempty A] [𝕊 : SmallStepSemantics P S T A]
    (det : P → 𝔼[S] →o 𝔼[S]) where
  det_le_dop : det ≤ 𝕊.dop
  det_prefixed_point : 𝕊.dς det ≤ det

variable {det : P → 𝔼[S] →o 𝔼[S]} [i' : 𝕊.DemonicET det]

theorem DemonicET.det_eq_dop : det = 𝕊.dop := det_le_dop.antisymm (dop_isLeast _ det_prefixed_point)

end Demonic

section Angelic

@[simp]
theorem lfp_aΦ_term :
    lfp (𝕊.mdp.aΦ (𝕊.cost X)) (Conf.term t σ) = 𝕊.cost X (Conf.term t σ) := by
  rw [MDP.lfp_aΦ_eq_iSup_aΦ]
  simp
  apply le_antisymm
  · simp
    intro 𝕊
    split_ifs <;> simp
  · apply le_iSup_of_le 1
    simp
@[simp]
theorem lfp_aΦ_bot :
    lfp (𝕊.mdp.aΦ (𝕊.cost X)) Conf.bot = 0 := by
  rw [MDP.lfp_aΦ_eq_iSup_aΦ]
  simp

theorem aop_eq_iSup_aΦ :
    𝕊.aop
  = ⨆ n, fun C ↦ ⟨fun X σ ↦ (𝕊.mdp.aΦ (𝕊.cost X))^[n] ⊥ (.prog C σ), fun a b h σ ↦ by
    simp
    suffices (⇑(MDP.aΦ (𝕊.cost a)))^[n] ⊥ ≤ (⇑(MDP.aΦ (𝕊.cost b)))^[n] ⊥ by apply this
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [Function.iterate_succ', Function.comp_apply]
      exact apply_mono (MDP.aΦ.monotone' (𝕊.cost_mono h)) ih⟩ := by
  ext C X σ; rw [aop]
  simp [fixedPoints.lfp_eq_sSup_iterate _ MDP.aΦ_ωScottContinuous]
theorem aop_eq_iSup_succ_aΦ :
      𝕊.aop
    = ⨆ n, fun C ↦ ⟨fun X σ ↦ (𝕊.mdp.aΦ (𝕊.cost X))^[n + 1] ⊥ (.prog C σ), fun a b h σ ↦ by
      simp only
      suffices (⇑(MDP.aΦ (𝕊.cost a)))^[n + 1] ⊥ ≤ (⇑(MDP.aΦ (𝕊.cost b)))^[n + 1] ⊥ by apply this
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
theorem aς_aop_eq_aop : 𝕊.aς 𝕊.aop = 𝕊.aop := by
  ext C X σ
  simp [aop]
  rw [← map_lfp]
  simp only [aς, OrderHom.coe_mk, aΦ_simp, cost, aΦ', aop]
  congr!
  simp; rfl

theorem aop_isLeast (b : P → 𝔼[S] →o 𝔼[S]) (h : 𝕊.aς b ≤ b) : 𝕊.aop ≤ b := by
  rw [aop_eq_iSup_aΦ, iSup_le_iff]
  intro n
  induction n with
  | zero => intros _ _ _; simp
  | succ 𝕊 ih =>
    refine le_trans (fun C X σ ↦ ?_) h
    simp [Function.iterate_succ', aς, -Function.iterate_succ, cost]
    gcongr with α hα
    rcases α with (_ | α)
    · simp [act] at hα
    · simp
      gcongr; split
      · apply ih
      · split_ifs <;> simp

theorem lfp_aς_eq_aop : lfp 𝕊.aς = 𝕊.aop :=
  (lfp_le_fixed _ 𝕊.aς_aop_eq_aop).antisymm (le_lfp _ 𝕊.aop_isLeast)

theorem aop_eq_iter : 𝕊.aop = ⨆ n, (𝕊.aς)^[n] ⊥ := by
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
      split <;> gcongr; split
      · apply ih
      · split_ifs <;> simp
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
      split <;> gcongr; split
      · apply ih
      · induction n with
        | zero => simp [cost]
        | succ n ih =>
          simp only [Function.iterate_succ', Function.comp_apply]
          simp [cost]

class AngelicET {P S T A : Type*} [Nonempty A] [𝕊 : SmallStepSemantics P S T A]
    (aet : P → 𝔼[S] →o 𝔼[S]) where
  aet_le_aop : aet ≤ 𝕊.aop
  aet_prefixed_point : 𝕊.aς aet ≤ aet

variable {aet : P → 𝔼[S] →o 𝔼[S]} [i' : 𝕊.AngelicET aet]

theorem AngelicET.aet_eq_aop : aet = 𝕊.aop := aet_le_aop.antisymm (aop_isLeast _ aet_prefixed_point)

end Angelic

attribute [-simp] Function.iterate_succ in
theorem dop_le_seq [𝕊.FiniteBranching] (seq : P → P → P) (after : P → (P ⊕ T) × S → (P ⊕ T) × S)
    (h_cost_seq : ∀ C C' σ X, 𝕊.cost_p X (seq C C', σ) = 𝕊.cost_p (𝕊.dop C' X) (C, σ))
    (h_seq_act : ∀ C C' σ, 𝕊.act (.prog (seq C C') σ) = 𝕊.act (.prog C σ))
    (h_succ : ∀ {C C' σ p α s}, (p, s) ∈ 𝕊.psucc C σ α → (p, after C' s) ∈ 𝕊.psucc (seq C C') σ α)
    (h_after_p : ∀ {C C' σ}, after C' (.inl C, σ) = (.inl (seq C C'), σ))
    (h_after_t : ∀ {t C C' σ}, after C (.inr t, σ) = C' →
      (C' = (.inl C, σ)) ∨ (C' = (.inr t, σ) ∧ ∀ X, 𝕊.cost_t X (t, σ) = 0))
    (h_c : ∀ {X t σ}, 𝕊.cost_t X (t, σ) ≤ X σ)
    (after_inj : ∀ x, Function.Injective (after x)) :
      𝕊.dop C ∘ 𝕊.dop C' ≤ 𝕊.dop (seq C C') := by
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
    simp [h_cost_seq, cost, h_seq_act]
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
    (h_cost_seq : ∀ C C' σ X, 𝕊.cost_p X (seq C C', σ) = 𝕊.cost_p (𝕊.aop C' X) (C, σ))
    (h_seq_act : ∀ C C' σ, 𝕊.act (.prog (seq C C') σ) = 𝕊.act (.prog C σ))
    (h_succ : ∀ {C C' σ p α s}, (p, s) ∈ 𝕊.psucc C σ α → (p, after C' s) ∈ 𝕊.psucc (seq C C') σ α)
    (h_after_p : ∀ {C C' σ}, after C' (.inl C, σ) = (.inl (seq C C'), σ))
    (h_after_t : ∀ {t C C' σ}, after C (.inr t, σ) = C' →
      (C' = (.inl C, σ)) ∨ (C' = (.inr t, σ) ∧ ∀ X, 𝕊.cost_t X (t, σ) = 0))
    (h_c : ∀ {X t σ}, 𝕊.cost_t X (t, σ) ≤ X σ)
    (after_inj : ∀ x, Function.Injective (after x)) :
      𝕊.aop C ∘ 𝕊.aop C' ≤ 𝕊.aop (seq C C') := by
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
    simp [h_cost_seq, cost, h_seq_act]
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
