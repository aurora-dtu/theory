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
  | skip     : SmallStep (·⟨skip, σ⟩)          .N 1 (·⟨⇓ ϖ, σ⟩)
  | term     : SmallStep (·⟨⇓ ϖ, σ⟩)           .N 1 none
  | fault    : SmallStep (·⟨↯ ϖ, σ⟩)           .N 1 none
  | assign   : SmallStep (·⟨x ::= e, σ⟩)       .N 1 (·⟨.skip, σ[x ↦ e σ]⟩)
  | prob     : SmallStep (·⟨.prob C p C, σ⟩)   .N 1 (·⟨C, σ⟩)
  | prob_L   : (h : ¬C₁ = C₂) → (h' : 0 < p.val σ) →
    SmallStep (·⟨.prob C₁ p C₂, σ⟩) .N (p.val σ)     (·⟨C₁, σ⟩)
  | prob_R   : (h : ¬C₁ = C₂) → (h' : p.val σ < 1) →
    SmallStep (·⟨.prob C₁ p C₂, σ⟩) .N (1 - p.val σ) (·⟨C₂, σ⟩)
  | nonDet_L : SmallStep (·⟨C₁ [] C₂, σ⟩)      .L 1 (·⟨C₁, σ⟩)
  | nonDet_R : SmallStep (·⟨C₁ [] C₂, σ⟩)      .R 1 (·⟨C₂, σ⟩)
  | tick     : SmallStep (·⟨.tick r, σ⟩)       .N 1 (·⟨.skip, σ⟩)
  | assert₁  : b σ  → SmallStep (·⟨.assert b, σ⟩) .N 1 (·⟨.skip, σ⟩)
  | assert₂  : ¬b σ → SmallStep (·⟨.assert b, σ⟩) .N 1 (·⟨↯ ϖ, σ⟩)
  | seq_L    : SmallStep (·⟨.skip ;; C₂, σ⟩) .N 1 (·⟨C₂, σ⟩)
  | seq_R    : SmallStep (·⟨C₁, σ⟩) α p (·⟨C₁', τ⟩) →
                SmallStep (·⟨C₁ ;; C₂, σ⟩) α p (·⟨C₁' ;; C₂, τ⟩)
  | seq_F    : SmallStep (·⟨C₁, σ⟩) .N 1 (·⟨↯ ϖ, σ⟩) →
                SmallStep (·⟨C₁ ;; C₂, σ⟩) .N 1 (·⟨↯ ϖ, σ⟩)
  | loop     : ¬b σ → SmallStep (·⟨.loop b C, σ⟩) .N 1 (·⟨.skip, σ⟩)
  | loop'    : b σ → SmallStep (·⟨.loop b C, σ⟩) .N 1 (·⟨C ;; .loop b C, σ⟩)

@[inherit_doc]
notation c " ⤳[" α "," p "] " c' => SmallStep c α p c'

namespace SmallStep

variable {c : Conf ϖ} {σ : States ϖ}

@[simp] theorem p_pos (h : c ⤳[α,p] c') : 0 < p := by induction h <;> simp_all
@[simp] theorem p_ne_zero (h : c ⤳[α,p] c') : ¬p = 0 :=
  pos_iff_ne_zero.mp <| p_pos h
@[simp] theorem p_le_one (h : c ⤳[α,p] c') : p ≤ 1 := by
  induction h <;> simp_all

@[simp] theorem skip_iff : (·⟨skip, σ⟩ ⤳[α,p] c) ↔ p = 1 ∧ α = .N ∧ c = ·⟨⇓ ϖ, σ⟩ := by grind
@[simp] theorem term_iff : (·⟨⇓ ϖ, σ⟩ ⤳[α,p] c) ↔ p = 1 ∧ α = .N ∧ c = none := by grind
@[simp] theorem fault_iff : (·⟨↯ ϖ, σ⟩ ⤳[α,p] c) ↔ p = 1 ∧ α = .N ∧ c = none := by grind
@[simp] theorem none_iff : (none ⤳[α,p] c) ↔ p = 1 ∧ α = .N ∧ c = none := by grind
@[simp] theorem to_bot :
    (c ⤳[α,p] none) ↔ ∃ σ, p = 1 ∧ α = .N ∧ (c = ·⟨⇓ ϖ, σ⟩ ∨ c = ·⟨↯ ϖ, σ⟩ ∨ c = none)
  := by aesop
@[simp] theorem to_term : (c ⤳[α,p] ·⟨⇓ ϖ, σ⟩) ↔ p = 1 ∧ α = .N ∧ c = ·⟨.skip, σ⟩ := by grind
theorem to_fault :
      (c ⤳[α,p] ·⟨↯ ϖ, σ⟩)
    ↔ p = 1 ∧ α = .N ∧ (
      (∃ C₁ C₂, c = ·⟨.seq C₁ C₂, σ⟩ ∧ ·⟨C₁, σ⟩ ⤳[.N,p] ·⟨↯ ϖ, σ⟩) ∨
      (∃ b, c = ·⟨.assert b, σ⟩ ∧ ¬b σ)) := by
  grind
theorem of_to_fault_p (h : c ⤳[α,p] ·⟨↯ ϖ, σ⟩) : p = 1 := by grind
theorem of_to_fault_act (h : c ⤳[α,p] ·⟨↯ ϖ, σ⟩) : α = .N := by grind
theorem of_to_fault_succ (h : c ⤳[α,p] ·⟨↯ ϖ, σ⟩) :
    ∀ α' p' c', (c ⤳[α',p'] c') ↔ (α' = α ∧ p' = p ∧ c' = ·⟨↯ ϖ, σ⟩) := by
  intro α' p' c'
  have := of_to_fault_p h; have := of_to_fault_act h; subst_eqs
  constructor
  · intro h'
    induction h' <;> try grind
  · grind
@[simp] theorem assign_iff :
    (·⟨x ::= e, σ⟩ ⤳[α,p] c') ↔ p = 1 ∧ α = .N ∧ c' = ·⟨.skip, σ[x ↦ e σ]⟩ := by grind
@[simp] theorem prob_iff :
    (·⟨.prob C₁ p C₂, σ⟩ ⤳[α,p'] c') ↔ α = .N ∧ (if C₁ = C₂ then p' = 1 ∧ c' = ·⟨C₁, σ⟩ else
      (p' = p.val σ ∧ 0 < p' ∧ c' = ·⟨C₁, σ⟩) ∨ (p' = 1 - p.val σ ∧ 0 < p' ∧ c' = ·⟨C₂, σ⟩))
  := by aesop
@[simp] theorem nonDet_iff :
    (·⟨C₁ [] C₂, σ⟩ ⤳[α,p'] c') ↔ p' = 1 ∧ ((α = .L ∧ c' = ·⟨C₁, σ⟩) ∨ (α = .R ∧ c' = ·⟨C₂, σ⟩))
  := by grind
@[simp] theorem tick_iff : (·⟨.tick r, σ⟩ ⤳[α,p] c') ↔ p = 1 ∧ α = .N ∧ c' = ·⟨skip, σ⟩
  := by grind
@[simp] theorem assert_iff :
    (·⟨.assert b, σ⟩ ⤳[α,p] c') ↔ p = 1 ∧ α = .N ∧ c' = (if b σ then ·⟨skip, σ⟩ else ·⟨↯ ϖ, σ⟩)
  := by grind
-- open scoped Classical in
@[simp] theorem seq_iff :
      (·⟨C₁ ;; C₂, σ⟩ ⤳[α,p] c')
    ↔ if C₁ = .skip then p = 1 ∧ α = .N ∧ c' = ·⟨C₂, σ⟩
      -- else if ∃ b, C₁ = .assert b ∧ ¬b σ then p = 1 ∧ α = .N ∧ c' = ·⟨↯ ϖ, σ⟩
      else
          (∃ C' σ', (·⟨C₁, σ⟩ ⤳[α,p] ·⟨C', σ'⟩) ∧ c' = (·⟨C' ;; C₂, σ'⟩))
        ∨ (∃ σ', (·⟨C₁, σ⟩ ⤳[α,p] ·⟨↯ ϖ, σ'⟩) ∧ c' = (·⟨↯ ϖ, σ'⟩))
  := by grind
@[simp] theorem loop_iff : (·⟨.loop b C, σ⟩ ⤳[α,p] c')
    ↔ p = 1 ∧ α = .N ∧ c' = if b σ then ·⟨C ;; .loop b C, σ⟩ else ·⟨skip, σ⟩ := by grind
def act (c : Conf ϖ) : Set Act := {α | ∃ p c', c ⤳[α,p] c'}

noncomputable instance : Decidable (α ∈ act c) := Classical.propDecidable _

instance : Finite (act c) := Subtype.finite
noncomputable instance : Fintype (act c) := Fintype.ofFinite _


@[simp]
theorem exists_succ_iff {C : pGCL ϖ} (h : ¬C = .skip) :
    (∃ c', ·⟨C,σ⟩ ⤳[α,p] c') ↔ (∃ C' σ', ·⟨C,σ⟩ ⤳[α,p] ·⟨C',σ'⟩) ∨ (∃ σ', ·⟨C,σ⟩ ⤳[α,p] ·⟨↯ ϖ,σ'⟩)
:= by
  constructor
  · rintro (_ | ⟨σ' | σ' | C', σ'⟩) <;> (try simp_all) <;> grind
  · rintro ⟨C', σ', _⟩ <;> grind

@[simp] theorem act_bot : act (ϖ:=ϖ) none = {.N} := by simp [act]
@[simp] theorem act_term : act (·⟨⇓ ϖ, σ⟩) = {.N} := by simp [act]
@[simp] theorem act_fault : act (·⟨↯ ϖ, σ⟩) = {.N} := by simp [act]
@[simp] theorem act_skip : act (·⟨skip, σ⟩) = {.N} := by simp [act]
@[simp] theorem act_assign : act (·⟨x ::= e, σ⟩) = {.N} := by simp [act]
@[simp] theorem act_seq : act (·⟨C₁ ;; C₂, σ⟩) = act (·⟨C₁, σ⟩) := by
  ext α
  simp_all only [act, seq_iff, Set.mem_setOf_eq]
  split_ifs
  · simp_all only [exists_and_left, exists_eq_left, skip_iff, exists_eq, and_true]
  · grind

@[simp] theorem act_prob : act (·⟨.prob C₁ p C₂, σ⟩) = {.N} := by
  ext
  simp_all [act]
  rintro ⟨_⟩
  split_ifs
  · simp
  · if 0 < p.val σ then (use p.val σ); simp_all else (use 1 - p.val σ); simp_all
@[simp] theorem act_nonDet : act (·⟨C₁ [] C₂, σ⟩) = {.L, .R} := by
  ext; simp [act]; aesop
@[simp] theorem act_loop : act (·⟨.loop b C, σ⟩) = {.N} := by simp [act]
@[simp] theorem act_tick : act (·⟨.tick r, σ⟩) = {.N} := by simp [act]
@[simp] theorem act_assert : act (·⟨.assert r, σ⟩) = {.N} := by simp [act]

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
  | ·⟨⇓ ϖ, _⟩, .N => {none}
  | ·⟨↯ ϖ, _⟩, .N => {none}
  | ·⟨skip, σ⟩, .N => {·⟨⇓ ϖ, σ⟩}
  | ·⟨tick _, σ⟩, .N => {·⟨skip, σ⟩}
  | ·⟨assert b, σ⟩, .N => if b σ then {·⟨skip, σ⟩} else {·⟨↯ ϖ, σ⟩}
  | ·⟨x ::= E, σ⟩, .N => {·⟨skip, σ[x ↦ E σ]⟩}
  | ·⟨.prob C₁ p C₂, σ⟩, .N =>
    if p.val σ = 0 then {·⟨C₂, σ⟩} else if p.val σ = 1 then {·⟨C₁, σ⟩} else {·⟨C₁, σ⟩, ·⟨C₂, σ⟩}
  | ·⟨C₁ [] _, σ⟩, .L => {(·⟨C₁, σ⟩)}
  | ·⟨_ [] C₂, σ⟩, .R => {(·⟨C₂, σ⟩)}
  | ·⟨.loop b C, σ⟩, .N => if b σ then {·⟨C.seq (.loop b C), σ⟩} else {·⟨.skip, σ⟩}
  | ·⟨.seq .skip C₂, σ⟩, .N => {·⟨C₂, σ⟩}
  | ·⟨.seq C₁ C₂, σ⟩, α => succs_fin (·⟨C₁, σ⟩) α |>.map ⟨C₂.after, C₂.after_inj⟩
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
    rw [ENNReal.tsum_eq_add_tsum_ite (·⟨C₁,σ⟩), ENNReal.tsum_eq_add_tsum_ite (·⟨C₂,σ⟩)]
    simp_all [ite_and, eq_comm]

end SmallStep

end pGCL
