import PGCL.Conf2
import MDP.SmallStepSemantics

/-!
# Small step operational semantics for `pGCL`

## Main definitions

* `pGCL.SmallStep`: The inductive definition of the probabilistic small step semantics of `pGCL`.
-/

namespace pGCL

variable {ϖ : Type*} [DecidableEq ϖ]

/-- Probabilistic small step operational semantics for `pGCL` -/
@[aesop safe [constructors, cases], grind]
inductive SmallStep : Conf₀ ϖ → Act → ENNReal → Conf₁ ϖ → Prop where
  -- | bot      : SmallStep conf₀[⊥] .N 1 conf[⊥]
  | skip     : SmallStep conf₀[skip, σ]          .N 1 conf₁[⇓, σ]
  -- | term     : SmallStep conf₀[⇓, σ]           .N 1 conf₁[⊥]
  -- | fault    : SmallStep conf₀[↯, σ]           .N 1 conf₁[⊥]
  | assign   : SmallStep conf₀[~x := ~e, σ]       .N 1 conf₁[⇓, σ[x ↦ e σ]]
  | prob     : SmallStep conf₀[{~C} [~p] {~C}, σ]   .N 1 conf₁[~C, σ]
  | prob_L   : (h : ¬C₁ = C₂) → (h' : 0 < p σ) →
    SmallStep conf₀[{~C₁} [~p] {~C₂}, σ] .N (p σ)     conf₁[~C₁, σ]
  | prob_R   : (h : ¬C₁ = C₂) → (h' : p σ < 1) →
    SmallStep conf₀[{~C₁} [~p] {~C₂}, σ] .N (1 - p σ) conf₁[~C₂, σ]
  | nonDet_L : SmallStep conf₀[{~C₁} [] {~C₂}, σ]      .L 1 conf₁[~C₁, σ]
  | nonDet_R : SmallStep conf₀[{~C₁} [] {~C₂}, σ]      .R 1 conf₁[~C₂, σ]
  | tick     : SmallStep conf₀[tick(~ r), σ]       .N 1 conf₁[⇓, σ]
  | observe₁  : b σ → [DecidablePred b] → SmallStep conf₀[observe(~b), σ] .N 1 conf₁[⇓, σ]
  | observe₂  : ¬b σ → [DecidablePred b] → SmallStep conf₀[observe(~b), σ] .N 1 conf₁[↯, σ]
  | seq_L    : SmallStep conf₀[~C₁, σ] α p conf₁[⇓, τ] →
                SmallStep conf₀[~C₁ ; ~C₂, σ] α p conf₁[~C₂, τ]
  | seq_R    : SmallStep conf₀[~C₁, σ] α p conf₁[~C₁', τ] →
                SmallStep conf₀[~C₁ ; ~C₂, σ] α p conf₁[~C₁' ; ~C₂, τ]
  | seq_F    : SmallStep conf₀[~C₁, σ] .N 1 conf₁[↯, σ] →
                SmallStep conf₀[~C₁ ; ~C₂, σ] .N 1 conf₁[↯, σ]
  | loop     : ¬b σ → [DecidablePred b] →
                SmallStep conf₀[while ~b {~C}, σ] .N 1 conf₁[⇓, σ]
  | loop'    : b σ → [DecidablePred b] →
                SmallStep conf₀[while ~b {~C}, σ] .N 1 conf₁[~C ; while ~b {~C}, σ]

@[inherit_doc]
notation c " ⤳[" α "," p "] " c' => SmallStep c α p c'

namespace SmallStep

variable {c : Conf₀ ϖ} {c' : Conf₁ ϖ} {σ : States ϖ}

@[simp] theorem p_pos (h : c ⤳[α,p] c') : 0 < p := by induction h <;> simp_all
@[simp] theorem p_ne_zero (h : c ⤳[α,p] c') : ¬p = 0 :=
  pos_iff_ne_zero.mp <| p_pos h
@[simp] theorem p_le_one (h : c ⤳[α,p] c') : p ≤ 1 := by
  induction h <;> simp_all

@[simp]
theorem skip_iff : (conf₀[skip, σ] ⤳[α,p] c') ↔ p = 1 ∧ α = .N ∧ c' = conf₁[⇓, σ] := by grind
-- @[simp] theorem term_iff : (conf₁[⇓, σ] ⤳[α,p] c') ↔ p = 1 ∧ α = .N ∧ c' = conf[⊥] := by grind
-- @[simp] theorem fault_iff : (conf₁[↯, σ] ⤳[α,p] c') ↔ p = 1 ∧ α = .N ∧ c' = conf[⊥] := by grind
-- @[simp] theorem none_iff : (conf[⊥] ⤳[α,p] c') ↔ p = 1 ∧ α = .N ∧ c' = conf[⊥] := by grind
-- @[simp] theorem to_bot :
--     (c ⤳[α,p] conf₁[⊥]) ↔ ∃ σ, p = 1 ∧ α = .N ∧ (c = conf₁[⇓, σ] ∨ c = conf₁[↯, σ] ∨ c = conf[⊥])
--   := by aesop
-- @[simp] theorem to_term : (c ⤳[α,p] conf₁[⇓, σ]) ↔ p = 1 ∧ α = .N ∧ c = conf[skip, σ] := by grind
theorem to_fault :
      (c ⤳[α,p] conf₁[↯, σ])
    ↔ p = 1 ∧ α = .N ∧ (
      (∃ C₁ C₂, c = conf₀[~C₁ ; ~C₂, σ] ∧ conf₀[~C₁, σ] ⤳[.N,p] conf₁[↯, σ]) ∨
      (∃ b, ∃ (_ : DecidablePred b), c = conf₀[observe(~b), σ] ∧ ¬b σ)) := by
  grind
theorem of_to_fault_p (h : c ⤳[α,p] conf₁[↯, σ]) : p = 1 := by grind
theorem of_to_fault_act (h : c ⤳[α,p] conf₁[↯, σ]) : α = .N := by grind
theorem of_to_fault_mem (h : conf₀[~C, σ] ⤳[α,p] conf₁[↯, σ']) : σ = σ' := by grind
theorem of_to_fault_succ (h : c ⤳[α,p] conf₁[↯, σ]) :
    ∀ α' p' c', (c ⤳[α',p'] c') ↔ (α' = α ∧ p' = p ∧ c' = conf₁[↯, σ]) := by
  intro α' p' c'
  have := of_to_fault_p h; have := of_to_fault_act h; subst_eqs
  constructor
  · intro h'
    induction h' <;> try grind
  · grind
@[simp] theorem assign_iff :
    (conf₀[~x := ~e, σ] ⤳[α,p] c') ↔ p = 1 ∧ α = .N ∧ c' = conf₁[⇓, σ[x ↦ e σ]] := by grind
@[simp] theorem prob_iff :
    (conf₀[{~C₁} [~p] {~C₂},σ] ⤳[α,p'] c') ↔
      α = .N ∧ (if C₁ = C₂ then p' = 1 ∧ c' = conf₁[~C₁,σ] else
      (p' = p σ ∧ 0 < p' ∧ c' = conf₁[~C₁,σ]) ∨ (p' = 1 - p σ ∧ 0 < p' ∧ c' = conf₁[~C₂,σ]))
  := by aesop
@[simp] theorem nonDet_iff :
      (conf₀[{~C₁} [] {~C₂}, σ] ⤳[α,p'] c')
    ↔ p' = 1 ∧ ((α = .L ∧ c' = conf₁[~C₁, σ]) ∨ (α = .R ∧ c' = conf₁[~C₂, σ]))
  := by grind
@[simp] theorem tick_iff : (conf₀[tick(~ r), σ] ⤳[α,p] c') ↔ p = 1 ∧ α = .N ∧ c' = conf₁[⇓, σ]
  := by grind
@[simp] theorem observe_iff [DecidablePred b] :
      (conf₀[observe(~b), σ] ⤳[α,p] c')
    ↔ p = 1 ∧ α = .N ∧ c' = (if b σ then conf₁[⇓, σ] else conf₁[↯, σ])
  := by grind
-- open scoped Classical in
@[simp] theorem seq_iff {C₁ C₂ : pGCL ϖ} :
      (conf₀[~C₁ ; ~C₂, σ] ⤳[α,p] c')
    ↔
          (∃ C' σ', (conf₀[~C₁, σ] ⤳[α,p] conf₁[~C', σ']) ∧ c' = conf₁[~C' ; ~C₂, σ'])
        ∨ (∃ σ', (conf₀[~C₁, σ] ⤳[α,p] conf₁[⇓, σ']) ∧ c' = conf₁[~C₂, σ'])
        ∨ ((conf₀[~C₁, σ] ⤳[α,p] conf₁[↯, σ]) ∧ c' = conf₁[↯, σ] ∧ α = .N ∧ p = 1)
  := by grind
@[simp] theorem loop_iff [DecidablePred b] : (conf₀[while ~b {~C}, σ] ⤳[α,p] c')
    ↔ p = 1 ∧ α = .N ∧ c' = if b σ then conf₁[~C ; while ~b {~C}, σ] else conf₁[⇓, σ] := by grind
def act (c : Conf₀ ϖ) : Set Act := {α | ∃ p c', c ⤳[α,p] c'}

noncomputable instance : Decidable (α ∈ act c) := Classical.propDecidable _

instance : Finite (act c) := Subtype.finite
noncomputable instance : Fintype (act c) := Fintype.ofFinite _


-- @[simp]
-- theorem exists_succ_iff {C : pGCL ϖ} (h : ¬C = .skip) :
--       (∃ c', conf[~C,σ] ⤳[α,p] c')
--     ↔ (∃ C' σ', conf[~C,σ] ⤳[α,p] conf[~C',σ']) ∨ (∃ σ', conf[~C,σ] ⤳[α,p] conf₁[↯,σ'])
-- := by
--   constructor
--   · rintro (_ | ⟨σ' | σ' | C', σ'⟩) <;> (try simp_all) <;> grind
--   · rintro ⟨C', σ', _⟩ <;> grind

-- @[simp] theorem act_bot : act (ϖ:=ϖ) conf[⊥] = {.N} := by simp [act]
-- @[simp] theorem act_term : act conf₁[⇓, σ] = {.N} := by simp [act]
-- @[simp] theorem act_fault : act conf₁[↯, σ] = {.N} := by simp [act]
@[simp] theorem act_skip : act conf₀[skip, σ] = {.N} := by simp [act]
@[simp] theorem act_assign : act conf₀[~x := ~e, σ] = {.N} := by simp [act]
@[simp] theorem act_seq : act conf₀[~C₁ ; ~C₂, σ] = act conf₀[~C₁, σ] := by
  ext α
  simp_all only [act, seq_iff, Set.mem_setOf_eq]
  grind

@[simp] theorem act_prob : act conf₀[{~C₁} [~p] {~C₂}, σ] = {.N} := by
  ext
  simp_all [act]
  rintro ⟨_⟩
  split_ifs
  · simp
  · if 0 < p σ then (use p σ); simp_all; grind else (use 1 - p σ); simp_all
@[simp] theorem act_nonDet : act conf₀[{~C₁} [] {~C₂}, σ] = {.L, .R} := by
  ext; simp [act]; aesop
@[simp] theorem act_loop [DecidablePred b] : act conf₀[while ~b {~C}, σ] = {.N} := by simp [act]
@[simp] theorem act_tick : act conf₀[tick(~ r), σ] = {.N} := by simp [act]
@[simp] theorem act_observe [DecidablePred r] : act conf₀[observe(~ r), σ] = {.N} := by simp [act]

instance act_nonempty (s : Conf₀ ϖ) : Nonempty (act s) := by
  obtain ⟨c, σ⟩ := s; induction c <;> simp_all

theorem progress (s : Conf₀ ϖ) : ∃ p a x, s ⤳[a,p] x :=
  have ⟨α, h⟩ := act_nonempty s
  exists_comm.mp (Exists.intro α (by exact h))

@[simp]
theorem iInf_act_const {C : Conf₀ ϖ} {x : ENNReal} : ⨅ α ∈ act C, x = x :=
  biInf_const Set.Nonempty.of_subtype

noncomputable instance : Decidable (c ⤳[α,p] c') := Classical.propDecidable _
noncomputable instance : Decidable (∃ α p, c ⤳[α,p] c') := Classical.propDecidable _

@[simp]
theorem tsum_p :
    (∑' (p : { p // c ⤳[α,p] c' }), ↑p) = (∑' p, if c ⤳[α,p] c' then p else 0) := by
  apply tsum_eq_tsum_of_ne_zero_bij (fun ⟨x, _⟩ ↦ ⟨x, by simp_all⟩) <;> simp_all
  exact StrictMono.injective fun _ _ a ↦ a

def succs (c : Conf₀ ϖ) (α : Act) : Set (Conf₁ ϖ) := {c' | ∃ p, c ⤳[α, p] c'}
open scoped Classical in
noncomputable def succs_fin (c : Conf₀ ϖ) (α : Act) : Finset (Conf₁ ϖ) :=
  match c, α with
  -- | conf₀[⊥], .N => {conf[⊥]}
  -- | conf₀[⇓, _], .N => {conf[⊥]}
  -- | conf₀[↯, _], .N => {conf[⊥]}
  | conf₀[skip, σ], .N => {conf₁[⇓, σ]}
  | conf₀[tick(~_), σ], .N => {conf₁[skip, σ]}
  | conf₀[observe(~b), σ], .N => if b σ then {conf₁[skip, σ]} else {conf₁[↯, σ]}
  | conf₀[~x := ~E, σ], .N => {conf₁[skip, σ[x ↦ E σ]]}
  | conf₀[{~C₁} [~p] {~C₂}, σ], .N =>
    if p σ = 0
    then {conf₁[~C₂, σ]}
    else if p σ = 1 then {conf₁[~C₁, σ]} else {conf₁[~C₁, σ], conf₁[~C₂, σ]}
  | conf₀[{~C₁} [] {~_}, σ], .L => {conf₁[~C₁, σ]}
  | conf₀[{~_} [] {~C₂}, σ], .R => {conf₁[~C₂, σ]}
  | conf₀[while ~b {~C}, σ], .N => if b σ then {conf₁[~C ; while ~b {~C}, σ]} else {conf₁[skip, σ]}
  | conf₀[skip ; ~C₂, σ], .N => {conf₁[~C₂, σ]}
  | conf₀[~C₁ ; ~C₂, σ], α => succs_fin conf₀[~C₁, σ] α |>.map ⟨C₂.after, C₂.after_inj⟩
  | _, _ => {}
open scoped Classical in
noncomputable def succs_univ_fin (c : Conf₀ ϖ) : Finset (Act × Conf₁ ϖ) :=
  match c with
  -- | conf[⊥] => {⟨.N, conf[⊥]⟩}
  -- | conf₁[⇓, _] => {⟨.N, conf[⊥]⟩}
  -- | conf₁[↯, _] => {⟨.N, conf[⊥]⟩}
  | conf₀[skip, σ] => {⟨.N, conf₁[⇓, σ]⟩}
  | conf₀[tick(~_), σ] => {⟨.N, conf₁[skip, σ]⟩}
  | conf₀[observe(~b), σ] => if b σ then {⟨.N, conf₁[skip, σ]⟩} else {⟨.N, conf₁[↯, σ]⟩}
  | conf₀[~x := ~E, σ] => {⟨.N, conf₁[skip, σ[x ↦ E σ]]⟩}
  | conf₀[{~C₁} [~p] {~C₂}, σ] =>
    if p σ = 0
    then {⟨.N, conf₁[~C₂, σ]⟩}
    else if p σ = 1 then {⟨.N, conf₁[~C₁, σ]⟩} else {⟨.N, conf₁[~C₁, σ]⟩, ⟨.N, conf₁[~C₂, σ]⟩}
  | conf₀[{~C₁} [] {~C₂}, σ] => {⟨.L, conf₁[~C₁, σ]⟩, ⟨.R, conf₁[~C₂, σ]⟩}
  | conf₀[while ~b {~C}, σ] =>
    if b σ then {⟨.N, conf₁[~C ; while ~b {~C}, σ]⟩} else {⟨.N, conf₁[skip, σ]⟩}
  | conf₀[skip ; ~C₂, σ] => {⟨.N, conf₁[~C₂, σ]⟩}
  | conf₀[~C₁ ; ~C₂, σ] =>
    succs_univ_fin conf₀[~C₁, σ]
      |>.map ⟨Prod.map id C₂.after, Function.Injective.prodMap (fun _ _ a ↦ a) C₂.after_inj⟩
open scoped Classical in
noncomputable def succs_univ_fin' (c : Conf₀ ϖ) : Finset (Act × ENNReal × Conf₁ ϖ) :=
  match c with
  -- | conf[⊥] => {⟨.N, 1, conf[⊥]⟩}
  -- | conf₁[⇓, _] => {⟨.N, 1, conf[⊥]⟩}
  -- | conf₁[↯, _] => {⟨.N, 1, conf[⊥]⟩}
  | conf₀[skip, σ] => {⟨.N, 1, conf₁[⇓, σ]⟩}
  | conf₀[tick(~_), σ] => {⟨.N, 1, conf₁[⇓, σ]⟩}
  | conf₀[observe(~b), σ] => if b σ then {⟨.N, 1, conf₁[⇓, σ]⟩} else {⟨.N, 1, conf₁[↯, σ]⟩}
  | conf₀[~x := ~E, σ] => {⟨.N, 1, conf₁[⇓, σ[x ↦ E σ]]⟩}
  | conf₀[{~C₁} [~p] {~C₂}, σ] =>
    if C₁ = C₂ then {⟨.N, 1, conf₁[~C₁, σ]⟩}
    else if p σ = 0 then {⟨.N, 1, conf₁[~C₂, σ]⟩}
    else if p σ = 1 then {⟨.N, 1, conf₁[~C₁, σ]⟩}
    else {⟨.N, p σ, conf₁[~C₁, σ]⟩, ⟨.N, 1 - p σ, conf₁[~C₂, σ]⟩}
  | conf₀[{~C₁} [] {~C₂}, σ] => {⟨.L, 1, conf₁[~C₁, σ]⟩, ⟨.R, 1, conf₁[~C₂, σ]⟩}
  | conf₀[while ~b {~C}, σ] =>
    if b σ then {⟨.N, 1, conf₁[~C ; while ~b {~C}, σ]⟩} else {⟨.N, 1, conf₁[⇓, σ]⟩}
  | conf₀[~C₁ ; ~C₂, σ] =>
    succs_univ_fin' conf₀[~C₁, σ]
      |>.map ⟨Prod.map id (Prod.map id C₂.after),
              Function.Injective.prodMap (fun _ _ a ↦ a)
                (Function.Injective.prodMap (fun _ _ a ↦ a) C₂.after_inj)⟩

-- theorem succs_univ_fin_eq_succs_fin (c : Conf₀ ϖ) :
--     ∀ α c', (α, c') ∈ succs_univ_fin c ↔ c' ∈ succs_fin c α := by
--   intro α
--   induction c, α using succs_fin.induct <;> simp_all [succs_univ_fin, succs_fin] <;> try grind
--   · split_ifs <;> simp
--   · unfold succs_univ_fin
--     intro c'
--     split <;> simp_all
--     · unfold succs_fin
--       split <;> simp_all
--     · grind
--   · rename_i c α _ _ _ _ _ _ _ _ _ _ _ _
--     rcases c with ((_ | _) | P)
--     · simp_all [succs_univ_fin]
--     · simp_all [succs_univ_fin]
--     · simp_all; rcases P <;> simp_all [succs_univ_fin] <;> split_ifs <;> simp_all
--     · simp_all [succs_univ_fin]

theorem succs_univ_fin'_eq_r (c : Conf₀ ϖ) :
    ∀ α p c', (α, p, c') ∈ succs_univ_fin' c ↔ c ⤳[α, p] c' := by
  induction c using succs_univ_fin'.induct <;> simp_all [succs_univ_fin'] <;> try grind
  · intros
    subst_eqs
    constructor
    · simp_all
    · rintro (h | h)
      · simp_all
        obtain ⟨⟨_⟩, _⟩ := h
        simp_all
      · simp_all
  · intros
    subst_eqs
    constructor
    · simp_all
    · rintro (⟨⟨_⟩, _⟩ | ⟨⟨_⟩, _⟩) <;> simp_all
  · intros
    split_ifs
    · simp_all
    · simp_all
    · simp_all
      intro C σ
      constructor
      · rintro (⟨⟨_⟩, _⟩ | ⟨⟨_⟩, _⟩) <;> simp_all
      · grind
  · intro α p
    constructor
    · intro C σ
      constructor
      · simp
        rintro α' p' (⟨_, _, _, ⟨_⟩, ⟨_⟩, _⟩ | ⟨_, _, _, ⟨_⟩, ⟨_⟩, _⟩)
        · left
          rename_i C' _ _ _
          use C'
          simp_all [pGCL.after]
        · simp_all [pGCL.after]
          grind
      · rintro (⟨_, _, ⟨_⟩⟩ | ⟨_, ⟨_⟩⟩)
        · simp_all
        · simp_all
    · rintro t σ
      constructor
      · simp
        rintro α' p' (⟨_, _, _, ⟨_⟩, ⟨_⟩, _⟩ | ⟨(_ | _), _, _, ⟨_⟩, ⟨_⟩, _⟩)
        · simp_all [pGCL.after]
        · simp_all [pGCL.after]
          grind
        · simp_all [pGCL.after]
      · rintro ⟨_, ⟨⟨_⟩, ⟨_⟩, _⟩, ⟨_⟩, ⟨_⟩, _⟩
        use .N, 1
        simp
        right
        use .fault
        simp_all

-- open scoped Classical in
-- theorem succs_eq_succs_fin : succs (ϖ:=ϖ) c α = (succs_fin c α).toSet := by
--   ext ⟨c', σ'⟩
--   obtain ⟨c, σ⟩ := c
--   simp [succs]
--   simp [← succs_univ_fin'_eq_r]
--   constructor
--   · simp
--     intro p h
--     cases c <;> simp_all [succs_fin, succs_univ_fin']
--     · grind
--   sorry
  -- simp [← succs_univ_fin'_eq_r]

--   sorry
--   -- constructor
--   -- · simp
--   --   intro p h
--   --   induction h with try simp_all [succs_fin]
--   --   | seq_R => unfold succs_fin; split <;> simp_all
--   --   | seq_F =>
--   --     unfold succs_fin; split <;> simp_all
--   --     simp [after]
--   --     grind
--   --   | prob_L | prob_R => split_ifs <;> simp_all
--   -- · intro h
--   --   induction c, α using succs_fin.induct generalizing s'
--   --     with (simp [succs_fin] at h ⊢; try subst_eqs) <;> try grind
--   --   | case9 | case10 => simp_all; (use 1); simp
--   --   | case11 => aesop
--   --   | case17 _ _ _ _ _ ih =>
--   --     obtain ⟨((_ | _) | ⟨c', σ'⟩), h, _, _⟩ := h <;> obtain ⟨_, _⟩ := ih _ h <;> simp_all
--   --     · grind
--   --     · grind

set_option maxHeartbeats 500000 in
open scoped Classical in
theorem sums_to_one (h₀ : c ⤳[α,p₀] c₀) :
    (∑' (c' : Conf₁ ϖ) (p : {p // c ⤳[α,p] c'}), p.val) = 1 := by
  induction h₀ with simp_all [ite_and]
  | seq_L =>
    rename_i C₂ h ih
    rw [← ih]
    apply C₂.tsum_after_eq <;> try grind
    · simp
    · simp
      rintro C' σ p (⟨C'', h⟩ | h) hp
      · simp_all
        use p
        grind
      · simp_all
        use p
        grind
    · simp
  | seq_R =>
    rename_i C₂ h ih
    rw [← ih]
    apply C₂.tsum_after_eq <;> try grind
    · simp
    · simp
      rintro C' σ p (⟨C'', h⟩ | h) hp
      on_goal 1 => left; use C'', σ
      on_goal 2 => right; use .term, σ
      all_goals simp_all; use p; grind
    · simp
  | seq_F =>
    rename_i C₂ h ih
    rw [← ih]
    apply C₂.tsum_after_eq <;> try grind
    · simp
    · simp
      rintro C' σ p (⟨C'', h⟩ | h) hp
      on_goal 1 => left; use C'', σ
      on_goal 2 => right; use .term, σ
      all_goals simp_all; use p; grind
    · simp
  | prob_L | prob_R =>
    rename_i C₁ C₂ _ σ _ _
    rw [ENNReal.tsum_eq_add_tsum_ite conf₁[~C₁,σ], ENNReal.tsum_eq_add_tsum_ite conf₁[~C₂,σ]]
    simp_all [ite_and, eq_comm]

end SmallStep

end pGCL
