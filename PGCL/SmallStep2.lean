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
inductive SmallStep : Conf' ϖ → Act → ENNReal → Conf' ϖ → Prop where
  | bot      : SmallStep conf[⊥] .N 1 conf[⊥]
  | skip     : SmallStep conf[skip, σ]          .N 1 conf[⇓, σ]
  | term     : SmallStep conf[⇓, σ]           .N 1 conf[⊥]
  | fault    : SmallStep conf[↯, σ]           .N 1 conf[⊥]
  | assign   : SmallStep conf[~x := ~e, σ]       .N 1 conf[⇓, σ[x ↦ e σ]]
  | prob     : SmallStep conf[{~C} [~p] {~C}, σ]   .N 1 conf[~C, σ]
  | prob_L   : (h : ¬C₁ = C₂) → (h' : 0 < p.val σ) →
    SmallStep conf[{~C₁} [~p] {~C₂}, σ] .N (p.val σ)     conf[~C₁, σ]
  | prob_R   : (h : ¬C₁ = C₂) → (h' : p.val σ < 1) →
    SmallStep conf[{~C₁} [~p] {~C₂}, σ] .N (1 - p.val σ) conf[~C₂, σ]
  | nonDet_L : SmallStep conf[{~C₁} [] {~C₂}, σ]      .L 1 conf[~C₁, σ]
  | nonDet_R : SmallStep conf[{~C₁} [] {~C₂}, σ]      .R 1 conf[~C₂, σ]
  | tick     : SmallStep conf[tick(~ r), σ]       .N 1 conf[⇓, σ]
  | assert₁  : b σ  → SmallStep conf[assert(~b), σ] .N 1 conf[⇓, σ]
  | assert₂  : ¬b σ → SmallStep conf[assert(~b), σ] .N 1 conf[↯, σ]
  | seq_L    : SmallStep conf[~C₁, σ] α p conf[⇓, τ] →
                SmallStep conf[~C₁ ; ~C₂, σ] α p conf[~C₂, τ]
  | seq_R    : SmallStep conf[~C₁, σ] α p conf[~C₁', τ] →
                SmallStep conf[~C₁ ; ~C₂, σ] α p conf[~C₁' ; ~C₂, τ]
  | seq_F    : SmallStep conf[~C₁, σ] .N 1 conf[↯, σ] →
                SmallStep conf[~C₁ ; ~C₂, σ] .N 1 conf[↯, σ]
  | loop     : ¬b σ → SmallStep conf[while ~b {~C}, σ] .N 1 conf[⇓, σ]
  | loop'    : b σ → SmallStep conf[while ~b {~C}, σ] .N 1 conf[~C ; while ~b {~C}, σ]

@[inherit_doc]
notation c " ⤳[" α "," p "] " c' => SmallStep c α p c'

namespace SmallStep

variable {c : Conf' ϖ} {σ : States ϖ}

@[simp] theorem p_pos (h : c ⤳[α,p] c') : 0 < p := by induction h <;> simp_all
@[simp] theorem p_ne_zero (h : c ⤳[α,p] c') : ¬p = 0 :=
  pos_iff_ne_zero.mp <| p_pos h
@[simp] theorem p_le_one (h : c ⤳[α,p] c') : p ≤ 1 := by
  induction h <;> simp_all

@[simp] theorem skip_iff : (conf[skip, σ] ⤳[α,p] c) ↔ p = 1 ∧ α = .N ∧ c = conf[⇓, σ] := by grind
@[simp] theorem term_iff : (conf[⇓, σ] ⤳[α,p] c) ↔ p = 1 ∧ α = .N ∧ c = conf[⊥] := by grind
@[simp] theorem fault_iff : (conf[↯, σ] ⤳[α,p] c) ↔ p = 1 ∧ α = .N ∧ c = conf[⊥] := by grind
@[simp] theorem none_iff : (conf[⊥] ⤳[α,p] c) ↔ p = 1 ∧ α = .N ∧ c = conf[⊥] := by grind
@[simp] theorem to_bot :
    (c ⤳[α,p] conf[⊥]) ↔ ∃ σ, p = 1 ∧ α = .N ∧ (c = conf[⇓, σ] ∨ c = conf[↯, σ] ∨ c = conf[⊥])
  := by aesop
-- @[simp] theorem to_term : (c ⤳[α,p] conf[⇓, σ]) ↔ p = 1 ∧ α = .N ∧ c = conf[skip, σ] := by grind
theorem to_fault :
      (c ⤳[α,p] conf[↯, σ])
    ↔ p = 1 ∧ α = .N ∧ (
      (∃ C₁ C₂, c = conf[~C₁ ; ~C₂, σ] ∧ conf[~C₁, σ] ⤳[.N,p] conf[↯, σ]) ∨
      (∃ b, c = conf[assert(~b), σ] ∧ ¬b σ)) := by
  grind
theorem of_to_fault_p (h : c ⤳[α,p] conf[↯, σ]) : p = 1 := by grind
theorem of_to_fault_act (h : c ⤳[α,p] conf[↯, σ]) : α = .N := by grind
theorem of_to_fault_mem (h : conf[~C, σ] ⤳[α,p] conf[↯, σ']) : σ = σ' := by grind
theorem of_to_fault_succ (h : c ⤳[α,p] conf[↯, σ]) :
    ∀ α' p' c', (c ⤳[α',p'] c') ↔ (α' = α ∧ p' = p ∧ c' = conf[↯, σ]) := by
  intro α' p' c'
  have := of_to_fault_p h; have := of_to_fault_act h; subst_eqs
  constructor
  · intro h'
    induction h' <;> try grind
  · grind
@[simp] theorem assign_iff :
    (conf[~x := ~e, σ] ⤳[α,p] c') ↔ p = 1 ∧ α = .N ∧ c' = conf[⇓, σ[x ↦ e σ]] := by grind
@[simp] theorem prob_iff :
    (conf[{~C₁} [~p] {~C₂},σ] ⤳[α,p'] c') ↔ α = .N ∧ (if C₁ = C₂ then p' = 1 ∧ c' = conf[~C₁,σ] else
      (p' = p.val σ ∧ 0 < p' ∧ c' = conf[~C₁, σ]) ∨ (p' = 1 - p.val σ ∧ 0 < p' ∧ c' = conf[~C₂, σ]))
  := by aesop
@[simp] theorem nonDet_iff :
      (conf[{~C₁} [] {~C₂}, σ] ⤳[α,p'] c')
    ↔ p' = 1 ∧ ((α = .L ∧ c' = conf[~C₁, σ]) ∨ (α = .R ∧ c' = conf[~C₂, σ]))
  := by grind
@[simp] theorem tick_iff : (conf[tick(~ r), σ] ⤳[α,p] c') ↔ p = 1 ∧ α = .N ∧ c' = conf[⇓, σ]
  := by grind
@[simp] theorem assert_iff :
      (conf[assert(~b), σ] ⤳[α,p] c')
    ↔ p = 1 ∧ α = .N ∧ c' = (if b σ then conf[⇓, σ] else conf[↯, σ])
  := by grind
-- open scoped Classical in
@[simp] theorem seq_iff :
      (conf[~C₁ ; ~C₂, σ] ⤳[α,p] c')
    ↔
          (∃ C' σ', (conf[~C₁, σ] ⤳[α,p] conf[~C', σ']) ∧ c' = conf[~C' ; ~C₂, σ'])
        ∨ (∃ σ', (conf[~C₁, σ] ⤳[α,p] conf[⇓, σ']) ∧ c' = conf[~C₂, σ'])
        ∨ ((conf[~C₁, σ] ⤳[α,p] conf[↯, σ]) ∧ c' = conf[↯, σ] ∧ α = .N ∧ p = 1)
  := by grind
@[simp] theorem loop_iff : (conf[while ~b {~C}, σ] ⤳[α,p] c')
    ↔ p = 1 ∧ α = .N ∧ c' = if b σ then conf[~C ; while ~b {~C}, σ] else conf[⇓, σ] := by grind
def act (c : Conf' ϖ) : Set Act := {α | ∃ p c', c ⤳[α,p] c'}

noncomputable instance : Decidable (α ∈ act c) := Classical.propDecidable _

instance : Finite (act c) := Subtype.finite
noncomputable instance : Fintype (act c) := Fintype.ofFinite _


-- @[simp]
-- theorem exists_succ_iff {C : pGCL ϖ} (h : ¬C = .skip) :
--       (∃ c', conf[~C,σ] ⤳[α,p] c')
--     ↔ (∃ C' σ', conf[~C,σ] ⤳[α,p] conf[~C',σ']) ∨ (∃ σ', conf[~C,σ] ⤳[α,p] conf[↯,σ'])
-- := by
--   constructor
--   · rintro (_ | ⟨σ' | σ' | C', σ'⟩) <;> (try simp_all) <;> grind
--   · rintro ⟨C', σ', _⟩ <;> grind

@[simp] theorem act_bot : act (ϖ:=ϖ) conf[⊥] = {.N} := by simp [act]
@[simp] theorem act_term : act conf[⇓, σ] = {.N} := by simp [act]
@[simp] theorem act_fault : act conf[↯, σ] = {.N} := by simp [act]
@[simp] theorem act_skip : act conf[skip, σ] = {.N} := by simp [act]
@[simp] theorem act_assign : act conf[~x := ~e, σ] = {.N} := by simp [act]
@[simp] theorem act_seq : act conf[~C₁ ; ~C₂, σ] = act conf[~C₁, σ] := by
  ext α
  simp_all only [act, seq_iff, Set.mem_setOf_eq]
  grind

@[simp] theorem act_prob : act conf[{~C₁} [~p] {~C₂}, σ] = {.N} := by
  ext
  simp_all [act]
  rintro ⟨_⟩
  split_ifs
  · simp
  · if 0 < p.val σ then (use p.val σ); simp_all else (use 1 - p.val σ); simp_all
@[simp] theorem act_nonDet : act conf[{~C₁} [] {~C₂}, σ] = {.L, .R} := by
  ext; simp [act]; aesop
@[simp] theorem act_loop : act conf[while ~b {~C}, σ] = {.N} := by simp [act]
@[simp] theorem act_tick : act conf[tick(~ r), σ] = {.N} := by simp [act]
@[simp] theorem act_assert : act conf[assert(~ r), σ] = {.N} := by simp [act]

instance act_nonempty (s : Conf' ϖ) : Nonempty (act s) := by
  rcases s with ((_ | _) | c' | _) <;> (try induction c') <;> simp_all

theorem progress (s : Conf' ϖ) : ∃ p a x, s ⤳[a,p] x :=
  have ⟨α, h⟩ := act_nonempty s
  exists_comm.mp (Exists.intro α (by exact h))

@[simp]
theorem iInf_act_const {C : Conf' ϖ} {x : ENNReal} : ⨅ α ∈ act C, x = x :=
  biInf_const Set.Nonempty.of_subtype

noncomputable instance : Decidable (c ⤳[α,p] c') := Classical.propDecidable _
noncomputable instance : Decidable (∃ α p, c ⤳[α,p] c') := Classical.propDecidable _

@[simp]
theorem tsum_p :
    (∑' (p : { p // c ⤳[α,p] c' }), ↑p) = (∑' p, if c ⤳[α,p] c' then p else 0) := by
  apply tsum_eq_tsum_of_ne_zero_bij (fun ⟨x, _⟩ ↦ ⟨x, by simp_all⟩) <;> simp_all
  exact StrictMono.injective fun _ _ a ↦ a

def succs (c : Conf' ϖ) (α : Act) : Set (Conf' ϖ) := {c' | ∃ p, c ⤳[α, p] c'}
open scoped Classical in
noncomputable def succs_fin (c : Conf' ϖ) (α : Act) : Finset (Conf' ϖ) :=
  match c, α with
  | conf[⊥], .N => {conf[⊥]}
  | conf[⇓, _], .N => {conf[⊥]}
  | conf[↯, _], .N => {conf[⊥]}
  | conf[skip, σ], .N => {conf[⇓, σ]}
  | conf[tick(~_), σ], .N => {conf[skip, σ]}
  | conf[assert(~b), σ], .N => if b σ then {conf[skip, σ]} else {conf[↯, σ]}
  | conf[~x := ~E, σ], .N => {conf[skip, σ[x ↦ E σ]]}
  | conf[{~C₁} [~p] {~C₂}, σ], .N =>
    if p.val σ = 0
    then {conf[~C₂, σ]}
    else if p.val σ = 1 then {conf[~C₁, σ]} else {conf[~C₁, σ], conf[~C₂, σ]}
  | conf[{~C₁} [] {~_}, σ], .L => {conf[~C₁, σ]}
  | conf[{~_} [] {~C₂}, σ], .R => {conf[~C₂, σ]}
  | conf[while ~b {~C}, σ], .N => if b σ then {conf[~C ; while ~b {~C}, σ]} else {conf[skip, σ]}
  | conf[skip ; ~C₂, σ], .N => {conf[~C₂, σ]}
  | conf[~C₁ ; ~C₂, σ], α => succs_fin conf[~C₁, σ] α |>.map ⟨C₂.after, C₂.after_inj⟩
  | _, _ => {}
open scoped Classical in
noncomputable def succs_univ_fin (c : Conf' ϖ) : Finset (Act × Conf' ϖ) :=
  match c with
  | conf[⊥] => {⟨.N, conf[⊥]⟩}
  | conf[⇓, _] => {⟨.N, conf[⊥]⟩}
  | conf[↯, _] => {⟨.N, conf[⊥]⟩}
  | conf[skip, σ] => {⟨.N, conf[⇓, σ]⟩}
  | conf[tick(~_), σ] => {⟨.N, conf[skip, σ]⟩}
  | conf[assert(~b), σ] => if b σ then {⟨.N, conf[skip, σ]⟩} else {⟨.N, conf[↯, σ]⟩}
  | conf[~x := ~E, σ] => {⟨.N, conf[skip, σ[x ↦ E σ]]⟩}
  | conf[{~C₁} [~p] {~C₂}, σ] =>
    if p.val σ = 0
    then {⟨.N, conf[~C₂, σ]⟩}
    else if p.val σ = 1 then {⟨.N, conf[~C₁, σ]⟩} else {⟨.N, conf[~C₁, σ]⟩, ⟨.N, conf[~C₂, σ]⟩}
  | conf[{~C₁} [] {~C₂}, σ] => {⟨.L, conf[~C₁, σ]⟩, ⟨.R, conf[~C₂, σ]⟩}
  | conf[while ~b {~C}, σ] =>
    if b σ then {⟨.N, conf[~C ; while ~b {~C}, σ]⟩} else {⟨.N, conf[skip, σ]⟩}
  | conf[skip ; ~C₂, σ] => {⟨.N, conf[~C₂, σ]⟩}
  | conf[~C₁ ; ~C₂, σ] =>
    succs_univ_fin conf[~C₁, σ]
      |>.map ⟨Prod.map id C₂.after, Function.Injective.prodMap (fun _ _ a ↦ a) C₂.after_inj⟩
open scoped Classical in
noncomputable def succs_univ_fin' (c : Conf' ϖ) : Finset (Act × ENNReal × Conf' ϖ) :=
  match c with
  | conf[⊥] => {⟨.N, 1, conf[⊥]⟩}
  | conf[⇓, _] => {⟨.N, 1, conf[⊥]⟩}
  | conf[↯, _] => {⟨.N, 1, conf[⊥]⟩}
  | conf[skip, σ] => {⟨.N, 1, conf[⇓, σ]⟩}
  | conf[tick(~_), σ] => {⟨.N, 1, conf[⇓, σ]⟩}
  | conf[assert(~b), σ] => if b σ then {⟨.N, 1, conf[⇓, σ]⟩} else {⟨.N, 1, conf[↯, σ]⟩}
  | conf[~x := ~E, σ] => {⟨.N, 1, conf[⇓, σ[x ↦ E σ]]⟩}
  | conf[{~C₁} [~p] {~C₂}, σ] =>
    if C₁ = C₂ then {⟨.N, 1, conf[~C₁, σ]⟩}
    else if p.val σ = 0 then {⟨.N, 1, conf[~C₂, σ]⟩}
    else if p.val σ = 1 then {⟨.N, 1, conf[~C₁, σ]⟩}
    else {⟨.N, p.val σ, conf[~C₁, σ]⟩, ⟨.N, 1 - p.val σ, conf[~C₂, σ]⟩}
  | conf[{~C₁} [] {~C₂}, σ] => {⟨.L, 1, conf[~C₁, σ]⟩, ⟨.R, 1, conf[~C₂, σ]⟩}
  | conf[while ~b {~C}, σ] =>
    if b σ then {⟨.N, 1, conf[~C ; while ~b {~C}, σ]⟩} else {⟨.N, 1, conf[⇓, σ]⟩}
  | conf[~C₁ ; ~C₂, σ] =>
    succs_univ_fin' conf[~C₁, σ]
      |>.map ⟨Prod.map id (Prod.map id C₂.after),
              Function.Injective.prodMap (fun _ _ a ↦ a)
                (Function.Injective.prodMap (fun _ _ a ↦ a) C₂.after_inj)⟩

theorem succs_univ_fin_eq_succs_fin (c : Conf' ϖ) :
    ∀ α c', (α, c') ∈ succs_univ_fin c ↔ c' ∈ succs_fin c α := by
  intro α
  induction c, α using succs_fin.induct <;> simp_all [succs_univ_fin, succs_fin] <;> try grind
  · split_ifs <;> simp
  · unfold succs_univ_fin
    intro c'
    split <;> simp_all
    · unfold succs_fin
      split <;> simp_all
    · grind
  · rename_i c α _ _ _ _ _ _ _ _ _ _ _ _
    rcases c with ((_ | _) | P)
    · simp_all [succs_univ_fin]
    · simp_all [succs_univ_fin]
    · simp_all; rcases P <;> simp_all [succs_univ_fin] <;> split_ifs <;> simp_all
    · simp_all [succs_univ_fin]

theorem succs_univ_fin'_eq_r (c : Conf' ϖ) :
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
      constructor
      · rintro (⟨⟨_⟩, _⟩ | ⟨⟨_⟩, _⟩) <;> simp_all
      · grind
  · intro α p c'
    constructor
    · simp_all
      intros _ _ C' _ _ _ _
      subst_eqs
      simp_all
      rcases C' with ((_ | _) | _ | _)
      · simp_all
        have := of_to_fault_p ‹_›
        have := of_to_fault_act ‹_›
        have := of_to_fault_mem ‹_›
        subst_eqs
        simp_all
      · simp_all
      · simp_all
      · simp_all
    · rintro (⟨C', σ', _⟩ | ⟨σ', _⟩ | ⟨_, ⟨_⟩, ⟨_⟩, _, _⟩)
      · simp_all
      · simp_all
      · use .N, 1, Conf.term Termination.fault ‹States ϖ›
        simp_all

-- open scoped Classical in
-- theorem succs_eq_succs_fin : succs (ϖ:=ϖ) c α = (succs_fin c α).toSet := by
--   ext s'
--   simp [succs]
--   -- simp [← succs_univ_fin'_eq_r]
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
    (∑' (c' : Conf' ϖ) (p : {p // c ⤳[α,p] c'}), p.val) = 1 := by
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
      on_goal 1 => use Conf.prog C'' σ
      on_goal 2 => use Conf.term .term σ
      all_goals simp_all; use p; grind
    · simp
  | seq_F =>
    rename_i C₂ h ih
    rw [← ih]
    apply C₂.tsum_after_eq <;> try grind
    · simp
    · simp
      rintro C' σ p (⟨C'', h⟩ | h) hp
      on_goal 1 => use Conf.prog C'' σ
      on_goal 2 => use Conf.term .term σ
      all_goals simp_all; use p; grind
    · simp
  | prob_L | prob_R =>
    rename_i C₁ C₂ _ σ _ _
    rw [ENNReal.tsum_eq_add_tsum_ite conf[~C₁,σ], ENNReal.tsum_eq_add_tsum_ite conf[~C₂,σ]]
    simp_all [ite_and, eq_comm]

end SmallStep

end pGCL
