import Mathlib.Tactic.Monotonicity.Basic
import MDP.Bellman
import MDP.Relational

open OrderHom OmegaCompletePartialOrder

local notation "𝔼[" S "]" => S → ENNReal

inductive Conf (P S T : Type*) where
  | term (t : T) (σ : S)
  | prog (P : P) (σ : S)
  | bot

class SmallStepSemantics (P S T A : Type*) [Nonempty A] where
  r : P × S → A → ENNReal → (P ⊕ T) × S → Prop
  relation_p_pos : ∀ {c α p c'}, r c α p c' → ¬p = 0
  succs_sum_to_one : ∀ {c α p₀ c'}, r c α p₀ c' → ∑' (b) (p : { p // r c α p b }), p.val = 1
  progress : ∀ s, ∃ p a x, r s a p x

  cost_p : P × S → ENNReal
  cost_t : 𝔼[S] →o T × S → ENNReal

namespace SmallStepSemantics

variable {P S A T : Type*} [Nonempty A] [𝕊 : SmallStepSemantics P S T A]

noncomputable
 instance : Inhabited A := Classical.inhabited_of_nonempty ‹_›

@[grind]
inductive rr : Conf P S T → Option A → ENNReal → Conf P S T → Prop where
  | bot : rr .bot none 1 .bot
  | term : rr (.term _ _) none 1 .bot
  | prog₀ : 𝕊.r (C, σ) α p (.inl C', σ') → rr (.prog C σ) α p (.prog C' σ')
  | prog₁ : 𝕊.r (C, σ) α p (.inr t, σ') → rr (.prog C σ) α p (.term t σ')

@[simp, grind =]
theorem rr.bot_to : 𝕊.rr .bot α p c' ↔ α = none ∧ p = 1 ∧ c' = .bot := by grind
@[simp, grind =]
theorem rr.term_to : 𝕊.rr (.term t σ) α p c' ↔ α = none ∧ p = 1 ∧ c' = .bot := by grind

@[simp, grind]
abbrev conf₂_to_conf : (P ⊕ T) × S → Conf P S T
  | (.inl C, σ) => .prog C σ
  | (.inr t, σ) => .term t σ
@[simp, grind]
abbrev conf_to_conf₂ : Conf P S T → Option ((P ⊕ T) × S)
  | .prog C σ => some (.inl C, σ)
  | .term t σ => some (.inr t, σ)
  | .bot => none

@[simp, grind =]
theorem rr_prog :
      𝕊.rr (.prog C σ) α p c'
    ↔ ∃ c'' α', 𝕊.r (C, σ) α' p c'' ∧ conf₂_to_conf c'' = c' ∧ some α' = α := by grind

@[grind .]
theorem relation_p_pos' : ∀ {c α p c'}, 𝕊.rr c α p c' → ¬p = 0 := by
  intro C α p c'; rintro (_ | _) <;> (try simp_all) <;> try apply 𝕊.relation_p_pos ‹_›
@[grind .]
theorem succs_tum_to_one' :
    ∀ {c α p₀ c'}, 𝕊.rr c α p₀ c' → ∑' (b) (p : { p // 𝕊.rr c α p b }), p.val = 1 := by
  intro C α p c'; rintro (_ | _)
  · rw [tsum_eq_single .bot, tsum_eq_single ⟨1, by grind⟩] <;>
      (try simp only [ENNReal.tsum_eq_zero]) <;> grind
  · rw [tsum_eq_single .bot, tsum_eq_single ⟨1, by grind⟩] <;>
      (try simp only [ENNReal.tsum_eq_zero]) <;> grind
  · rename_i h
    conv => right; rw [← 𝕊.succs_sum_to_one h]
    apply tsum_eq_tsum_of_ne_zero_bij
      (fun ⟨x, _⟩ ↦ conf₂_to_conf x)
    · intro _; grind
    · simp only [Function.support_subset_iff, ne_eq, ENNReal.tsum_eq_zero, not_forall,
      Subtype.exists, Set.mem_range, Function.mem_support]
      grind
    · simp
      constructor
      · intros
        congr! <;> grind
      · congr! <;> grind
  · rename_i h
    conv => right; rw [← 𝕊.succs_sum_to_one h]
    apply tsum_eq_tsum_of_ne_zero_bij
      (fun ⟨x, _⟩ ↦ conf₂_to_conf x)
    · intro ⟨_, _⟩ ⟨_, _⟩; grind
    · simp only [Function.support_subset_iff, ne_eq, ENNReal.tsum_eq_zero, not_forall,
      Subtype.exists, Set.mem_range, Function.mem_support]; grind
    · simp
      constructor
      · intros
        congr! <;> grind
      · congr! <;> grind

theorem progress' : ∀ s, ∃ p a x, 𝕊.rr s a p x := by
  rintro (⟨t, σ⟩ | ⟨C, σ⟩ | _)
  · use 1, default, .bot; grind
  · have ⟨p, α, c', h⟩ := 𝕊.progress (C, σ)
    use p, α, conf₂_to_conf c'
    grind
  · use 1, default, .bot; grind

noncomputable def mdp : MDP (Conf P S T) (Option A) :=
  MDP.ofRelation 𝕊.rr 𝕊.relation_p_pos' 𝕊.succs_tum_to_one' 𝕊.progress'

def psucc (C : P) (σ : S) (α : A) : Set (ENNReal × (P ⊕ T) × S) := {s | 𝕊.r (C, σ) α s.fst s.snd}

theorem sub_psucc_eq_sum_r (C : P) (σ : S) (α : A) (f : ENNReal × (P ⊕ T) × S → ENNReal) :
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
    intro ⟨p₀, s₀, hs₀⟩ _ ⟨p₁, s₁, hs₁⟩ _ h Z hZ₁ hZ₂ ⟨p', s', σ'⟩ hZ
    specialize hZ₁ hZ
    specialize hZ₂ hZ
    simp_all only [ne_eq, Set.mem_setOf_eq]
theorem sum_psucc_eq_sub_succ_univ (C : P) (σ : S) (α : A) (f : ENNReal × (P ⊕ T) × S → ENNReal) :
      ∑' (s : (psucc C σ α)), f s.val
    = ∑' (x : ↑(𝕊.mdp.succs_univ (Conf.prog C σ))) (p : {p // rr (Conf.prog C σ) (some α) p x.val}),
        if let some C := conf_to_conf₂ x.val then f (p, C) else 0 := by
  simp [sub_psucc_eq_sum_r]
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
        simp only [Function.mem_support, Set.mem_range, Subtype.exists]
        grind
      · simp

def cost (X : 𝔼[S]) : 𝕊.mdp.Costs
  | .bot => 0
  | .term t σ => 𝕊.cost_t X (t, σ)
  | .prog C σ => 𝕊.cost_p (C, σ)

@[mono]
def cost_mono : Monotone 𝕊.cost := by
  intro a b h c
  simp [cost]
  split
  · rfl
  · apply 𝕊.cost_t.mono h
  · rfl
@[gcongr]
theorem cost_le_apply (h : a ≤ b) : 𝕊.cost a x ≤ 𝕊.cost b x := cost_mono h x

@[simp] theorem cost_bot (X) : 𝕊.cost X .bot = 0 := by rfl

def act (c : Conf P S T) : Set (Option A) := {α | ∃ p c', 𝕊.rr c α p c'}

noncomputable def _root_.Optimization.act (O : Optimization) (C : Conf P S T) :
    (Option A → ENNReal) →o ENNReal :=
  O.sOpt (𝕊.act C)

@[gcongr]
theorem _root_.Optimization.act_gcongr {O : Optimization} {C : Conf P S T}
    {f₁ f₂ : Option A → ENNReal} (h : ∀ α, f₁ α ≤ f₂ α) : O.act C f₁ ≤ O.act C f₂ := by
  gcongr
  apply h

open scoped Optimization.Notation

noncomputable def op (O : Optimization) (C : P) : 𝔼[S] →o 𝔼[S] :=
  ⟨fun X ↦ (lfp (𝕊.mdp.Φ O <| 𝕊.cost X) <| Conf.prog C ·), fun a b h σ ↦ by
    suffices lfp (𝕊.mdp.Φ O (𝕊.cost a)) ≤ lfp (𝕊.mdp.Φ O (𝕊.cost b)) by exact this _
    gcongr
    apply MDP.Φ.monotone' (𝕊.cost_mono h)⟩

open scoped Classical in
theorem tsum_succs_univ' (f : 𝕊.mdp.succs_univ c → ENNReal) :
    (∑' s', f s') = ∑' s', if h : _ then f ⟨s', h⟩ else 0 := by
  symm
  apply tsum_eq_tsum_of_ne_zero_bij (↑↑·) _ _ <;> try simp_all
  intro ⟨_, _⟩ ⟨_, _⟩; simp; apply SetCoe.ext

@[simp]
noncomputable def Φ' (O : Optimization) (c : 𝕊.mdp.Costs) (C : Conf P S T) (f : 𝕊.mdp.Costs) :
    ENNReal :=
  c C + O.act C fun α ↦ match C with
      | .prog C σ =>
        match α with
        | some α => ∑' (s : 𝕊.psucc C σ α),
          s.val.fst *
            match s.val.snd with
            | (.inl C', σ') => f (.prog C' σ') | (.inr t, σ') => f (.term t σ')
        | none => 0
      | .term _ _ | .bot => match α with | some _ => 0 | none => f .bot

@[simp]
theorem Φ_simp {C : Conf P S T} :
    𝕊.mdp.Φ O c f C = 𝕊.Φ' O c C f
:= by
  simp [MDP.Φ, MDP.act, MDP.Φf, tsum_succs_univ', -Φ']
  simp [Φ', Optimization.act]
  congr! with α hα
  · ext; simp [act, mdp, Function.ne_iff]
    grind
  · split <;> split <;> simp [mdp]
    · rename_i C σ _ α
      have := 𝕊.sum_psucc_eq_sub_succ_univ (A:=A) (C:=C) (σ:=σ) (α:=α)
        (f:=fun (s : ENNReal × (P ⊕ T) × S) ↦ s.1 * match s.2 with
                                                    | (Sum.inl C', σ') => f (.prog C' σ')
                                                    | (Sum.inr t, σ') => f (.term t σ'))
      simp at this
      rw [this]; clear this
      simp [tsum_succs_univ']
      simp [mdp, ← ENNReal.tsum_mul_right]
      grind
    · rw [tsum_eq_single .bot]
      · simp
        rw [tsum_eq_single ⟨1, by simp⟩] <;> grind
      · simp +contextual
    · rw [tsum_eq_single .bot]
      · simp
        rw [tsum_eq_single ⟨1, by simp⟩] <;> grind
      · simp +contextual

@[simp, grind =]
theorem succs_univ_term : 𝕊.mdp.succs_univ (.term t σ) = {.bot} := by simp [mdp]
@[simp, grind =]
theorem succs_univ_bot : 𝕊.mdp.succs_univ .bot = {.bot} := by simp [mdp]
@[simp, grind =]
theorem succs_univ_prog :
    𝕊.mdp.succs_univ (.prog C σ) = (conf₂_to_conf '' {c' | ∃ p α, 𝕊.r (C, σ) α p c'}) := by
  ext
  simp only [mdp, MDP.ofRelation_succs_univ, rr_prog, Set.mem_setOf_eq, Set.mem_image]
  grind

@[simp]
theorem Φ_bot_eq : (𝕊.mdp.Φ O (𝕊.cost X))^[n] ⊥ .bot = 0 := by
  induction n <;> simp_all [-Function.iterate_succ, Function.iterate_succ']
  simp [Optimization.act, Optimization.sOpt, act]
  split <;> simp
@[simp]
theorem Φ_term_eq :
    (𝕊.mdp.Φ O (𝕊.cost X))^[n] ⊥ (.term t σ) = if n = 0 then 0 else 𝕊.cost X (Conf.term t σ) := by
  induction n <;> simp_all [-Function.iterate_succ, Function.iterate_succ']
  simp [Optimization.act, Optimization.sOpt, act]
  split <;> simp

noncomputable def ξ (O : Optimization) : (P → 𝔼[S] →o 𝔼[S]) →o P → 𝔼[S] →o 𝔼[S] :=
  ⟨fun Y ↦ (fun C ↦ ⟨fun X σ ↦ 𝕊.Φ' O (𝕊.cost X) (.prog C σ) (fun s' ↦
    match s' with
    | .prog C' σ' => Y C' X σ'
    | .term t σ' => 𝕊.cost_t X (t, σ')
    | .bot => 0),
  fun a b hab σ ↦ by
    simp
    gcongr with α
    split <;> gcongr; split
    · apply (Y _).mono hab
    · apply 𝕊.cost_t.mono hab⟩),
  fun a b hab C X σ ↦ by
    simp only [Φ', DFunLike.coe]
    simp only [toFun_eq_coe]
    gcongr with α
    split <;> try rfl
    gcongr
    split
    · apply hab
    · rfl⟩

theorem ξ_apply : 𝕊.ξ O Y C X = fun σ ↦ 𝕊.Φ' O (𝕊.cost X) (.prog C σ) (match · with
    | .prog C' σ' => Y C' X σ'
    | .term t σ' => 𝕊.cost_t X (t, σ')
    | .bot => 0) := rfl
theorem ξ_apply' : 𝕊.ξ O Y C X σ = 𝕊.Φ' O (𝕊.cost X) (.prog C σ) (match · with
    | .prog C' σ' => Y C' X σ'
    | .term t σ' => 𝕊.cost_t X (t, σ')
    | .bot => 0) := rfl

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

instance instFiniteBranchingMDP [instFin : 𝕊.FiniteBranching] : 𝕊.mdp.FiniteBranching where
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
    set Z := (Function.support (𝕊.mdp.P C α))
    rcases C with (⟨t, σ⟩ | ⟨C, σ⟩ | _) <;> try simp
    · rcases α with (_ | α)
      · have : Z = {.bot} := by
          ext; simp [mdp, Z]
        simp [this]
      · have : Z = {} := by
          ext; simp [mdp, Z]
        simp [this]
    · rcases α with (_ | α)
      · have : Z = {} := by
          ext; simp [mdp, Z]
        simp [this]
      · suffices
            Z ⊆ Set.image (conf₂_to_conf ·.snd.snd)
                  {(α, p, C') | r (C, σ) (α : A) p (C' : (P ⊕ T) × S)} by
          apply Set.Finite.subset (Set.Finite.image _ (instFin.finite (C, σ))) this
        intro
        simp [conf₂_to_conf, mdp, Z]
        grind
    · rcases α with (_ | α)
      · have : Z = {Conf.bot} := by ext; simp [mdp, Z]
        simp [this]
      · have : Z = {} := by ext; simp [mdp, Z]
        simp [this]

@[simp]
theorem lfp_Φ_O_bot [Optimization.ΦContinuous O 𝕊.mdp] :
    lfp (𝕊.mdp.Φ O (𝕊.cost X)) Conf.bot = 0 := by
  rw [MDP.lfp_Φ_eq_iSup_Φ]
  simp
@[simp]
theorem lfp_Φ_O_term [Optimization.ΦContinuous O 𝕊.mdp] :
    lfp (𝕊.mdp.Φ O (𝕊.cost X)) (Conf.term t σ) = 𝕊.cost X (Conf.term t σ) := by
  rw [← map_lfp]
  simp
  simp [cost, Optimization.act, Optimization.sOpt, act]
  split <;> simp

theorem op_eq_iSup_Φ [Optimization.ΦContinuous O 𝕊.mdp] :
    𝕊.op O
  = ⨆ n, fun C ↦ ⟨fun X σ ↦ (𝕊.mdp.Φ O (𝕊.cost X))^[n] ⊥ (.prog C σ), fun a b h σ ↦ by
    simp
    suffices (⇑(MDP.Φ O (𝕊.cost a)))^[n] ⊥ ≤ (⇑(MDP.Φ O (𝕊.cost b)))^[n] ⊥ by apply this
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [Function.iterate_succ', Function.comp_apply]
      mono
      apply MDP.Φ.monotone' (𝕊.cost_mono h)⟩ := by
  unfold op
  ext C
  simp [𝕊.mdp.lfp_Φ_eq_iSup_Φ]
theorem op_eq_iSup_succ_Φ [i : Optimization.ΦContinuous O 𝕊.mdp] :
      𝕊.op O
    = ⨆ n, fun C ↦ ⟨fun X σ ↦ (𝕊.mdp.Φ O (𝕊.cost X))^[n + 1] ⊥ (.prog C σ), fun a b h σ ↦ by
      simp only
      suffices (⇑(MDP.Φ O (𝕊.cost a)))^[n + 1] ⊥ ≤ (⇑(MDP.Φ O (𝕊.cost b)))^[n + 1] ⊥ by apply this
      induction n with
      | zero => simp; apply MDP.Φ.monotone' (cost_mono h)
      | succ n ih =>
        simp only [Function.iterate_succ', Function.comp_apply] at ih ⊢
        exact apply_mono (MDP.Φ.monotone' (cost_mono h)) ih⟩ := by
  ext C X σ; rw [op]
  simp only [coe_mk, _root_.iSup_apply, coe_iSup]
  rw [fixedPoints.lfp_eq_sSup_iterate _ (i.Φ_continuous _)]
  rw [← iSup_iterate_succ]
  simp
theorem ξ_op_eq_op [Optimization.ΦContinuous O 𝕊.mdp] : 𝕊.ξ O (𝕊.op O) = 𝕊.op O := by
  ext C X σ
  simp [op, op]
  rw [← map_lfp]
  simp [ξ_apply, OrderHom.coe_mk, cost, op]

theorem op_isLeast [Optimization.ΦContinuous O 𝕊.mdp] (b : P → 𝔼[S] →o 𝔼[S]) (h : 𝕊.ξ O b ≤ b) :
    𝕊.op O ≤ b := by
  rw [op_eq_iSup_Φ, iSup_le_iff]
  intro n
  induction n with
  | zero => intros _ _ _; simp
  | succ 𝕊 ih =>
    refine le_trans (fun C X σ ↦ ?_) h
    simp [Function.iterate_succ', ξ_apply, -Function.iterate_succ, cost]
    gcongr with α
    rcases α with (_ | α)
    · rfl
    · simp only
      gcongr; split
      · apply ih
      · split_ifs <;> simp

theorem lfp_ξ_eq_op [Optimization.ΦContinuous O 𝕊.mdp] : lfp (𝕊.ξ O) = 𝕊.op O :=
  (lfp_le_fixed _ 𝕊.ξ_op_eq_op).antisymm (le_lfp _ 𝕊.op_isLeast)

attribute [-simp] Φ_simp in
theorem ξ_continuous [i : Optimization.ΦContinuous O 𝕊.mdp] : ωScottContinuous (𝕊.ξ O) := by
  simp only [ξ, ← Φ_simp, coe_mk]
  refine ωScottContinuous.of_apply₂ fun C ↦ ?_
  refine ωScottContinuous.of_monotone_map_ωSup ?_
  simp only [ωSup, OrderHom.ωSup_coe, Chain.coe_map, Pi.evalOrderHom_coe, apply_coe,
    Function.comp_apply, Function.eval]
  fapply Exists.intro
  · intro a b hab X σ; simp only; apply (MDP.Φ _ _).mono; intro; simp; split <;> try gcongr
    apply hab
  · intro c
    ext X σ
    have := ωScottContinuous_iff_map_ωSup_of_orderHom.mp (i.Φ_continuous (𝕊.cost X))
              ⟨fun i ↦ (match · with
                | .prog C' σ' => c i C' X σ'
                | .term t σ' => cost_t P A X ⟨t, σ'⟩
                | .bot => 0),
              fun _ _ _ _ ↦ by simp; split <;> (try gcongr); apply c.mono ‹_›⟩
    convert congrFun this (.prog C σ)
    simp [ωSup]; simp only [DFunLike.coe]; simp only [toFun_eq_coe]
    congr!
    split <;> simp

theorem op_eq_iter [Optimization.ΦContinuous O 𝕊.mdp] : 𝕊.op O = ⨆ n, (𝕊.ξ O)^[n] ⊥ := by
  rw [← lfp_ξ_eq_op, fixedPoints.lfp_eq_sSup_iterate _ ξ_continuous]

class ET {P S T A : Type*} [Nonempty A] (𝕊 : SmallStepSemantics P S T A)
    (O : Optimization) [O.ΦContinuous 𝕊.mdp] (et : P → 𝔼[S] →o 𝔼[S]) where
  et_le_op : et ≤ 𝕊.op O
  et_prefixed_point : 𝕊.ξ O et ≤ et

variable {et : P → 𝔼[S] →o 𝔼[S]} [Optimization.ΦContinuous O 𝕊.mdp] [i' : 𝕊.ET O et]

theorem ET.et_eq_op : et = 𝕊.op O := et_le_op.antisymm (op_isLeast _ et_prefixed_point)

attribute [-simp] Function.iterate_succ in
theorem op_le_seq
    (seq : P → P → P) (after : P → (P ⊕ T) × S → (P ⊕ T) × S) (t_const : 𝔼[S])
    (h_cost_seq : ∀ C C' σ, 𝕊.cost_p (seq C C', σ) = 𝕊.cost_p (C, σ))
    (h_seq_act : ∀ C C' σ, 𝕊.act (.prog (seq C C') σ) = 𝕊.act (.prog C σ))
    (h_succ : ∀ {C C' σ p α s}, (p, s) ∈ 𝕊.psucc C σ α → (p, after C' s) ∈ 𝕊.psucc (seq C C') σ α)
    (h_after_p : ∀ {C C' σ}, after C' (.inl C, σ) = (.inl (seq C C'), σ))
    (h_after_t : ∀ {t C C' σ}, after C (.inr t, σ) = C' →
      (C' = (.inl C, σ)) ∨ (C' = (.inr t, σ) ∧ ∀ X, 𝕊.cost_t X (t, σ) = t_const σ))
    (h_c : ∀ {X t σ C'}, after C' (Sum.inr t, σ) = (Sum.inl C', σ) →
      𝕊.cost_t (𝕊.op O C' X) (t, σ) ≤ (𝕊.op O C' X) σ)
    (after_inj : ∀ x, Function.Injective (after x)) :
      𝕊.op O C ∘ 𝕊.op O C' ≤ 𝕊.op O (seq C C') := by
  nth_rw 1 [← lfp_ξ_eq_op]
  apply lfp_induction (ξ O) (p:=fun f ↦ ∀ C C', f C ∘ op O C' ≤ op O (seq C C'))
  · simp only [ge_iff_le]
    intro f h₁ h₂
    nth_rw 2 [← ξ_op_eq_op]
    intro C C' X σ
    simp [ξ, Optimization.act, h_seq_act]
    gcongr
    · exact ge_of_eq (h_cost_seq C C' σ)
    intro a
    simp
    split
    · apply Summable.tsum_le_tsum_of_inj (fun ⟨⟨p, a⟩, ha⟩ ↦ ⟨⟨p, after C' a⟩, h_succ ha⟩) <;> simp
      · intro ⟨⟨_, c₁⟩, _⟩ ⟨⟨_, c₂⟩, _⟩ h
        grind
      · intro p
        constructor
        · intro C₁ σ₁ h
          gcongr
          simp [h_after_p]
          apply h₁
        · intro t σ₁ h
          gcongr
          grind only
    · rfl
  · simp
    intro Z hZ C C' X
    simp
    intro f hfZ σ
    specialize hZ _ hfZ C C' X σ
    grind only

end SmallStepSemantics
