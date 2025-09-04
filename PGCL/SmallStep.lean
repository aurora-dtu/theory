import PGCL.Conf

/-!
# Small step operational semantics for `pGCL`

## Main definitions

* `pGCL.SmallStep`: The inductive definition of the probabilistic small step semantics of `pGCL`.
-/

namespace pGCL

variable {ϖ : Type*} [DecidableEq ϖ]

/-- Probabilistic small step operational semantics for `pGCL` -/
@[aesop safe [constructors, cases], grind]
inductive SmallStep : Conf ϖ → Act → ENNReal → Conf ϖ → Prop where
  | bot      : SmallStep none .N 1 none
  | skip     : SmallStep conf[skip, σ]          .N 1 conf[⇓, σ]
  | term     : SmallStep conf[⇓, σ]           .N 1 none
  | fault    : SmallStep conf[↯, σ]           .N 1 none
  | assign   : SmallStep conf[~x := ~e, σ]       .N 1 conf[skip, σ[x ↦ e σ]]
  | prob     : SmallStep conf[{~C} [~p] {~C}, σ]   .N 1 conf[~C, σ]
  | prob_L   : (h : ¬C₁ = C₂) → (h' : 0 < p.val σ) →
    SmallStep conf[{~C₁} [~p] {~C₂}, σ] .N (p.val σ)     conf[~C₁, σ]
  | prob_R   : (h : ¬C₁ = C₂) → (h' : p.val σ < 1) →
    SmallStep conf[{~C₁} [~p] {~C₂}, σ] .N (1 - p.val σ) conf[~C₂, σ]
  | nonDet_L : SmallStep conf[{~C₁} [] {~C₂}, σ]      .L 1 conf[~C₁, σ]
  | nonDet_R : SmallStep conf[{~C₁} [] {~C₂}, σ]      .R 1 conf[~C₂, σ]
  | tick     : SmallStep conf[tick(r), σ]       .N 1 conf[skip, σ]
  | assert₁  : b σ  → SmallStep conf[assert(b), σ] .N 1 conf[skip, σ]
  | assert₂  : ¬b σ → SmallStep conf[assert(b), σ] .N 1 conf[↯, σ]
  | seq_L    : SmallStep conf[skip ; ~C₂, σ] .N 1 conf[~C₂, σ]
  | seq_R    : SmallStep conf[~C₁, σ] α p conf[~C₁', τ] →
                SmallStep conf[~C₁ ; ~C₂, σ] α p conf[~C₁' ; ~C₂, τ]
  | seq_F    : SmallStep conf[~C₁, σ] .N 1 conf[↯, σ] →
                SmallStep conf[~C₁ ; ~C₂, σ] .N 1 conf[↯, σ]
  | loop     : ¬b σ → SmallStep conf[while ~b {~C}, σ] .N 1 conf[skip, σ]
  | loop'    : b σ → SmallStep conf[while ~b {~C}, σ] .N 1 conf[~C ; while ~b {~C}, σ]

@[inherit_doc]
notation c " ⤳[" α "," p "] " c' => SmallStep c α p c'

namespace SmallStep

variable {c : Conf ϖ} {σ : States ϖ}

@[simp] theorem p_pos (h : c ⤳[α,p] c') : 0 < p := by induction h <;> simp_all
@[simp] theorem p_ne_zero (h : c ⤳[α,p] c') : ¬p = 0 :=
  pos_iff_ne_zero.mp <| p_pos h
@[simp] theorem p_le_one (h : c ⤳[α,p] c') : p ≤ 1 := by
  induction h <;> simp_all

@[simp] theorem skip_iff : (conf[skip, σ] ⤳[α,p] c) ↔ p = 1 ∧ α = .N ∧ c = conf[⇓, σ] := by grind
@[simp] theorem term_iff : (conf[⇓, σ] ⤳[α,p] c) ↔ p = 1 ∧ α = .N ∧ c = none := by grind
@[simp] theorem fault_iff : (conf[↯, σ] ⤳[α,p] c) ↔ p = 1 ∧ α = .N ∧ c = none := by grind
@[simp] theorem none_iff : (none ⤳[α,p] c) ↔ p = 1 ∧ α = .N ∧ c = none := by grind
@[simp] theorem to_bot :
    (c ⤳[α,p] none) ↔ ∃ σ, p = 1 ∧ α = .N ∧ (c = conf[⇓, σ] ∨ c = conf[↯, σ] ∨ c = none)
  := by aesop
@[simp] theorem to_term : (c ⤳[α,p] conf[⇓, σ]) ↔ p = 1 ∧ α = .N ∧ c = conf[skip, σ] := by grind
theorem to_fault :
      (c ⤳[α,p] conf[↯, σ])
    ↔ p = 1 ∧ α = .N ∧ (
      (∃ C₁ C₂, c = conf[~C₁ ; ~C₂, σ] ∧ conf[~C₁, σ] ⤳[.N,p] conf[↯, σ]) ∨
      (∃ b, c = conf[assert(~b), σ] ∧ ¬b σ)) := by
  grind
theorem of_to_fault_p (h : c ⤳[α,p] conf[↯, σ]) : p = 1 := by grind
theorem of_to_fault_act (h : c ⤳[α,p] conf[↯, σ]) : α = .N := by grind
theorem of_to_fault_succ (h : c ⤳[α,p] conf[↯, σ]) :
    ∀ α' p' c', (c ⤳[α',p'] c') ↔ (α' = α ∧ p' = p ∧ c' = conf[↯, σ]) := by
  intro α' p' c'
  have := of_to_fault_p h; have := of_to_fault_act h; subst_eqs
  constructor
  · intro h'
    induction h' <;> try grind
  · grind
@[simp] theorem assign_iff :
    (conf[~x := ~e, σ] ⤳[α,p] c') ↔ p = 1 ∧ α = .N ∧ c' = conf[skip, σ[x ↦ e σ]] := by grind
@[simp] theorem prob_iff :
    (conf[{~C₁} [~p] {~C₂},σ] ⤳[α,p'] c') ↔ α = .N ∧ (if C₁ = C₂ then p' = 1 ∧ c' = conf[~C₁,σ] else
      (p' = p.val σ ∧ 0 < p' ∧ c' = conf[~C₁, σ]) ∨ (p' = 1 - p.val σ ∧ 0 < p' ∧ c' = conf[~C₂, σ]))
  := by aesop
@[simp] theorem nonDet_iff :
      (conf[{~C₁} [] {~C₂}, σ] ⤳[α,p'] c')
    ↔ p' = 1 ∧ ((α = .L ∧ c' = conf[~C₁, σ]) ∨ (α = .R ∧ c' = conf[~C₂, σ]))
  := by grind
@[simp] theorem tick_iff : (conf[tick(r), σ] ⤳[α,p] c') ↔ p = 1 ∧ α = .N ∧ c' = conf[skip, σ]
  := by grind
@[simp] theorem assert_iff :
      (conf[assert(~b), σ] ⤳[α,p] c')
    ↔ p = 1 ∧ α = .N ∧ c' = (if b σ then conf[skip, σ] else conf[↯, σ])
  := by grind
-- open scoped Classical in
@[simp] theorem seq_iff :
      (conf[~C₁ ; ~C₂, σ] ⤳[α,p] c')
    ↔ if C₁ = .skip then p = 1 ∧ α = .N ∧ c' = conf[~C₂, σ]
      -- else if ∃ b, C₁ = .assert(b) ∧ ¬b σ then p = 1 ∧ α = .N ∧ c' = conf[↯, σ]
      else
          (∃ C' σ', (conf[~C₁, σ] ⤳[α,p] conf[~C', σ']) ∧ c' = conf[~C' ; ~C₂, σ'])
        ∨ (∃ σ', (conf[~C₁, σ] ⤳[α,p] conf[↯, σ']) ∧ c' = conf[↯, σ'])
  := by grind
@[simp] theorem loop_iff : (conf[while ~b {~C}, σ] ⤳[α,p] c')
    ↔ p = 1 ∧ α = .N ∧ c' = if b σ then conf[~C ; while ~b {~C}, σ] else conf[skip, σ] := by grind
def act (c : Conf ϖ) : Set Act := {α | ∃ p c', c ⤳[α,p] c'}

noncomputable instance : Decidable (α ∈ act c) := Classical.propDecidable _

instance : Finite (act c) := Subtype.finite
noncomputable instance : Fintype (act c) := Fintype.ofFinite _


@[simp]
theorem exists_succ_iff {C : pGCL ϖ} (h : ¬C = .skip) :
      (∃ c', conf[~C,σ] ⤳[α,p] c')
    ↔ (∃ C' σ', conf[~C,σ] ⤳[α,p] conf[~C',σ']) ∨ (∃ σ', conf[~C,σ] ⤳[α,p] conf[↯,σ'])
:= by
  constructor
  · rintro (_ | ⟨σ' | σ' | C', σ'⟩) <;> (try simp_all) <;> grind
  · rintro ⟨C', σ', _⟩ <;> grind

@[simp] theorem act_bot : act (ϖ:=ϖ) none = {.N} := by simp [act]
@[simp] theorem act_term : act conf[⇓, σ] = {.N} := by simp [act]
@[simp] theorem act_fault : act conf[↯, σ] = {.N} := by simp [act]
@[simp] theorem act_skip : act conf[skip, σ] = {.N} := by simp [act]
@[simp] theorem act_assign : act conf[~x := ~e, σ] = {.N} := by simp [act]
@[simp] theorem act_seq : act conf[~C₁ ; ~C₂, σ] = act conf[~C₁, σ] := by
  ext α
  simp_all only [act, seq_iff, Set.mem_setOf_eq]
  split_ifs
  · simp_all only [exists_and_left, exists_eq_left, skip_iff, exists_eq, and_true]
  · grind

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
@[simp] theorem act_tick : act conf[tick(r), σ] = {.N} := by simp [act]
@[simp] theorem act_assert : act conf[assert(r), σ] = {.N} := by simp [act]

instance act_nonempty (s : Conf ϖ) : Nonempty (act s) := by
  rcases s with (_ | ⟨σ' | σ' | c', σ'⟩) <;> (try induction c') <;> simp_all

theorem progress (s : Conf ϖ) : ∃ p a x, s ⤳[a,p] x :=
  have ⟨α, h⟩ := act_nonempty s
  exists_comm.mp (Exists.intro α (by exact h))

@[simp]
theorem iInf_act_const {C : Conf ϖ} {x : ENNReal} : ⨅ α ∈ act C, x = x :=
  biInf_const Set.Nonempty.of_subtype

noncomputable instance : Decidable (c ⤳[α,p] c') := Classical.propDecidable _
noncomputable instance : Decidable (∃ α p, c ⤳[α,p] c') := Classical.propDecidable _

@[simp]
theorem tsum_p :
    (∑' (p : { p // c ⤳[α,p] c' }), ↑p) = (∑' p, if c ⤳[α,p] c' then p else 0) := by
  apply tsum_eq_tsum_of_ne_zero_bij (fun ⟨x, _⟩ ↦ ⟨x, by simp_all⟩) <;> simp_all
  exact StrictMono.injective fun _ _ a ↦ a

def succs (c : Conf ϖ) (α : Act) : Set (Conf ϖ) := {c' | ∃ p, c ⤳[α, p] c'}
noncomputable def succs_fin (c : Conf ϖ) (α : Act) : Finset (Conf ϖ) :=
  match c, α with
  | none, .N => {none}
  | conf[⇓, _], .N => {none}
  | conf[↯, _], .N => {none}
  | conf[skip, σ], .N => {conf[⇓, σ]}
  | conf[tick(_), σ], .N => {conf[skip, σ]}
  | conf[assert(b), σ], .N => if b σ then {conf[skip, σ]} else {conf[↯, σ]}
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

theorem succs_eq_succs_fin : succs (ϖ:=ϖ) c α = (succs_fin c α).toSet := by
  ext s'
  simp [succs]
  constructor
  · simp
    intro p h
    induction h with try simp_all [succs_fin]
    | seq_R => unfold succs_fin; split <;> simp_all
    | seq_F =>
      unfold succs_fin; split <;> simp_all
      simp [after]
      grind
    | prob_L | prob_R => split_ifs <;> simp_all
  · intro h
    induction c, α using succs_fin.induct generalizing s'
      with (simp [succs_fin] at h ⊢; try subst_eqs) <;> try grind
    | case9 | case10 => simp_all; (use 1); simp
    | case11 => aesop
    | case17 _ _ _ _ _ ih =>
      obtain ⟨(_ | ⟨σ' | c', σ'⟩), h, _, _⟩ := h <;> obtain ⟨_, _⟩ := ih _ h <;> simp_all
      · grind
      · grind

set_option maxHeartbeats 500000 in
open scoped Classical in
theorem sums_to_one (h₀ : c ⤳[α,p₀] c₀) :
    (∑' (c' : Conf ϖ) (p : {p // c ⤳[α,p] c'}), p.val) = 1 := by
  induction h₀ with simp_all [ite_and]
  | seq_R =>
    rename_i C₂ h ih
    rw [← ih]
    apply C₂.tsum_after_eq <;> simp_all [ite_and] <;> try split_ifs <;> simp_all
    · intro σ' p' h' h'' h'''
      grind
    · intros _ _ _ _ h _ h'
      apply Exists.intro _ ⟨h, h'⟩
  | seq_F =>
    rename_i C₂ h ih
    rw [← ih]
    apply C₂.tsum_after_eq <;> simp_all [ite_and] <;> try split_ifs <;> simp_all
    · intro σ' p' h' h'' h'''
      grind
    · intros _ _ _ _ h _ h'
      apply Exists.intro _ ⟨h, h'⟩
  | prob_L | prob_R =>
    rename_i C₁ C₂ _ σ _ _
    rw [ENNReal.tsum_eq_add_tsum_ite conf[~C₁,σ], ENNReal.tsum_eq_add_tsum_ite conf[~C₂,σ]]
    simp_all [ite_and, eq_comm]

end SmallStep

end pGCL
