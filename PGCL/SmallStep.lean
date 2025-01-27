import MDP.Cost
import MDP.Relational
import PGCL.Conf
import PGCL.WeakestPre

/-!
# Small step operational semantics for `pGCL`

## Main definitions

* `pGCL.SmallStep`: The inductive definition of the probobalistic small step semantics of `pGCL`.
* `pGCL.OMDP`: The derived `MDP` from the small step semantics.
* `pGCL.OMDP.step`: The characteristic function of doing one step in the `OMDP`.
* `pGCL.dop`: The demonic expected cost given by the least fixed point of the Bellman-operator
  `MDP.Φ`.
* `pGCL.dop_eq_dwp`: The proof connecting the fixed point characteristic of the operational
  semantics to the weakest preexpectation formalization of `pGCL`.

-/

namespace pGCL

variable {ϖ : Type*}
variable [DecidableEq ϖ]

@[simp] theorem seq_ne_right : ¬seq C₁ C₂ = C₂ := (by (absurd congrArg SizeOf.sizeOf ·); simp)
@[simp] theorem right_ne_seq : ¬C₂ = seq C₁ C₂ := (seq_ne_right ·.symm)
@[simp] theorem left_ne_seq : ¬C₁ = seq C₁ C₂ := (by (absurd congrArg SizeOf.sizeOf ·); simp; omega)
@[simp] theorem seq_ne_left : ¬seq C₁ C₂ = C₁ := (left_ne_seq ·.symm)

def after (C' : pGCL ϖ) : Conf ϖ → Conf ϖ
  | some (some c, σ) => some (some (c.seq C'), σ)
  | some (none, σ) => some (some C', σ)
  | none => none

def after_inj (C' : pGCL ϖ) : Function.Injective C'.after := by
  intro c₁ c₂ h
  simp_all [after]
  split at h <;> split at h <;> simp_all

@[simp]
theorem after_eq_seq_iff : C₂.after c = ·⟨C₁ ; C₂, σ⟩ ↔ c = (·⟨C₁, σ⟩) := by
  simp [after]
  split <;> simp_all

@[simp] theorem after_none : after C₂ none = none := by simp [after]
@[simp] theorem after_sink : after C₂ (some (none, σ)) = (·⟨C₂, σ⟩) := by simp [after]
@[simp] theorem after_eq_right : after C₂ a = ·⟨C₂,σ⟩ ↔ a = (some (none, σ)) := by
  simp [after]; split <;> simp
@[simp] theorem after_neq_sink : ¬after C₂ c' = (some (none, σ)) := by simp [after]; split <;> simp
@[simp] theorem after_eq_none : after C₂ c' = none ↔ c' = none := by simp [after]; split <;> simp

omit [DecidableEq ϖ] in
theorem tsum_after_eq (C₂ : pGCL ϖ) {f g : Conf ϖ → ENNReal}
  (hg₁ : f none = 0 → g none = 0)
  (hg₂ : ∀ σ, g (·⟨⇓ ϖ, σ⟩) = 0)
  (hg₃ : ∀ C σ, ¬g (·⟨C, σ⟩) = 0 → ∃ a, ¬f a = 0 ∧ C₂.after a = (·⟨C, σ⟩))
  (hf₁ : ¬f none = 0 → f none = g none)
  (hf₂ : ∀ σ, ¬f (·⟨⇓ ϖ, σ⟩) = 0 → f (·⟨⇓ ϖ, σ⟩) = g (·⟨C₂, σ⟩))
  (hf₃ : ∀ C σ, ¬f (·⟨C, σ⟩) = 0 → f (·⟨C, σ⟩) = g (·⟨C ; C₂, σ⟩)) :
    (∑' s, g s) = ∑' s, f s :=
  tsum_eq_tsum_of_ne_zero_bij (C₂.after ·.val) (fun ⟨_, _⟩ ⟨_, _⟩ ↦ by simp; apply C₂.after_inj)
    (by rintro (_ | _ | _) <;> simp_all [not_imp_not.mpr hg₁])
    (by rintro ⟨(_ | _ | _), h⟩
        · simp [hf₁ h, after]
        · simp [hf₂ _ h]
        · simp [hf₃ _ _ h, after])

omit [DecidableEq ϖ] in
theorem tsum_after_le (C₂ : pGCL ϖ) {f g : Conf ϖ → ENNReal}
  (h₁ : g none ≤ f none)
  (h₂ : ∀ σ, g (·⟨⇓ ϖ, σ⟩) ≤ f (·⟨C₂, σ⟩))
  (h₂ : ∀ C σ, g (·⟨C, σ⟩) ≤ f (·⟨C ; C₂, σ⟩)) :
    (∑' s, g s) ≤ ∑' s, f s :=
  tsum_le_tsum_of_inj C₂.after C₂.after_inj (by simp_all)
    (by rintro (_ | _ | _) <;> simp_all [after]) (by simp) (by simp)

/-- Probobalistic small step operational semantics for `pGCL` -/
@[mk_iff]
inductive SmallStep : Conf ϖ → Act → ENNReal → Conf ϖ → Prop where
  | bot      : SmallStep none .N 1 none
  | skip     : SmallStep (·⟨skip, σ⟩)          .N 1 (·⟨⇓ ϖ, σ⟩)
  | sink     : SmallStep (·⟨⇓ ϖ, σ⟩)           .N 1 none
  | assign   : SmallStep (·⟨x ::= e, σ⟩)       .N 1 (·⟨.skip, σ[x ↦ e σ]⟩)
  | prob     : SmallStep (·⟨.prob C p C, σ⟩)   .N 1 (some (C, σ))
  | prob_L   : (h : ¬C₁ = C₂) → (h' : 0 < p.val σ) →
    SmallStep (·⟨.prob C₁ p C₂, σ⟩) .N (p.val σ)     (some (C₁, σ))
  | prob_R   : (h : ¬C₁ = C₂) → (h' : p.val σ < 1) →
    SmallStep (·⟨.prob C₁ p C₂, σ⟩) .N (1 - p.val σ) (some (C₂, σ))
  | nonDet_L : SmallStep (·⟨C₁ [] C₂, σ⟩)      .L 1 (·⟨C₁, σ⟩)
  | nonDet_R : SmallStep (·⟨C₁ [] C₂, σ⟩)      .R 1 (·⟨C₂, σ⟩)
  | tick     : SmallStep (·⟨.tick r, σ⟩)       .N 1 (·⟨.skip, σ⟩)
  | seq_L    : SmallStep (·⟨.skip ; C₂, σ⟩) .N 1 (·⟨C₂, σ⟩)
  | seq_R    : SmallStep (·⟨C₁, σ⟩) α p (·⟨C₁', τ⟩) → SmallStep (·⟨C₁ ; C₂, σ⟩) α p (·⟨C₁' ; C₂, τ⟩)
  | loop     : ¬b σ → SmallStep (·⟨.loop b C, σ⟩) .N 1 (·⟨.skip, σ⟩)
  | loop'    : b σ → SmallStep (·⟨.loop b C, σ⟩) .N 1 (·⟨C.seq (.loop b C), σ⟩)

@[inherit_doc]
local notation c " ⤳[" α "," p "] " c' => SmallStep c α p c'

namespace SmallStep

variable {c : Conf ϖ} {σ : States ϖ}

@[simp] theorem p_pos (h : c ⤳[α,p] c') : 0 < p := by induction h <;> simp_all
@[simp] theorem p_ne_zero (h : c ⤳[α,p] c') : ¬p = 0 :=
  pos_iff_ne_zero.mp <| p_pos h
@[simp] theorem p_le_one (h : c ⤳[α,p] c') : p ≤ 1 := by
  induction h <;> simp_all

@[simp] theorem skip_iff : (·⟨skip, σ⟩ ⤳[α,p] c) ↔ p = 1 ∧ α = .N ∧ c = ·⟨⇓ ϖ, σ⟩
  := by rw [smallStep_iff]; aesop
@[simp] theorem sink_iff : (·⟨⇓ ϖ, σ⟩ ⤳[α,p] c) ↔ p = 1 ∧ α = .N ∧ c = none
  := by rw [smallStep_iff]; aesop
@[simp] theorem none_iff : (none ⤳[α,p] c) ↔ p = 1 ∧ α = .N ∧ c = none
  := by rw [smallStep_iff]; aesop
@[simp] theorem to_bot : (c ⤳[α,p] none) ↔ ∃ σ, p = 1 ∧ α = .N ∧ (c = (·⟨⇓ ϖ, σ⟩) ∨ c = none)
  := by rw [smallStep_iff]; aesop
@[simp] theorem to_sink : (c ⤳[α,p] ·⟨⇓ ϖ, σ⟩) ↔ p = 1 ∧ α = .N ∧ c = ·⟨.skip, σ⟩
  := by rw [smallStep_iff]; aesop
@[simp] theorem assign_iff : (·⟨x ::= e, σ⟩ ⤳[α,p] c') ↔ p = 1 ∧ α = .N ∧ c' = ·⟨.skip, σ[x ↦ e σ]⟩
  := by rw [smallStep_iff]; aesop
@[simp] theorem prob_iff :
    (·⟨.prob C₁ p C₂, σ⟩ ⤳[α,p'] c') ↔ α = .N ∧ (if C₁ = C₂ then p' = 1 ∧ c' = ·⟨C₁, σ⟩ else
      (p' = p.val σ ∧ 0 < p' ∧ c' = ·⟨C₁, σ⟩) ∨ (p' = 1 - p.val σ ∧ 0 < p' ∧ c' = ·⟨C₂, σ⟩))
  := by rw [smallStep_iff]; aesop
@[simp] theorem nonDet_iff :
    (·⟨C₁ [] C₂, σ⟩ ⤳[α,p'] c') ↔ p' = 1 ∧ ((α = .L ∧ c' = ·⟨C₁, σ⟩) ∨ (α = .R ∧ c' = ·⟨C₂, σ⟩))
  := by rw [smallStep_iff]; aesop
@[simp] theorem tick_iff : (·⟨.tick r, σ⟩ ⤳[α,p] c') ↔ p = 1 ∧ α = .N ∧ c' = ·⟨.skip, σ⟩
  := by rw [smallStep_iff]; aesop
@[simp] theorem seq_iff :
      (·⟨C₁ ; C₂, σ⟩ ⤳[α,p] c')
    ↔ if C₁ = .skip then p = 1 ∧ α = .N ∧ c' = ·⟨C₂, σ⟩
      else (∃ C' σ', (·⟨C₁, σ⟩ ⤳[α,p] ·⟨C', σ'⟩) ∧ c' = (·⟨.seq C' C₂, σ'⟩))
  := by rw [smallStep_iff]; aesop
@[simp] theorem loop_iff : (·⟨.loop b C, σ⟩ ⤳[α,p] c')
    ↔ p = 1 ∧ α = .N ∧ c' = if b σ then ·⟨C.seq (.loop b C), σ⟩ else ·⟨.skip, σ⟩
  := by rw [smallStep_iff]; aesop
def act (c : Conf ϖ) : Set Act := {α | ∃ p c', c ⤳[α,p] c'}

noncomputable instance : Decidable (α ∈ act c) := Classical.propDecidable _

instance : Finite (act c) := Subtype.finite
noncomputable instance : Fintype (act c) := Fintype.ofFinite _

@[simp]
theorem exists_succ_iff {C : pGCL ϖ} (h : ¬C = .skip) :
    (∃ c', ·⟨C,σ⟩ ⤳[α,p] c') ↔ ∃ C' σ', ·⟨C,σ⟩ ⤳[α,p] ·⟨C',σ'⟩ := by
  constructor
  · rintro (_ | ⟨σ' | c', σ'⟩) <;> (try simp_all); use c', σ'
  · rintro ⟨c', σ', _⟩; use ·⟨c', σ'⟩

@[simp] theorem act_bot : act (ϖ:=ϖ) none = {.N} := by simp [act]
@[simp] theorem act_sink : act (·⟨⇓ ϖ, σ⟩) = {.N} := by simp [act]
@[simp] theorem act_skip : act (·⟨.skip, σ⟩) = {.N} := by simp [act]
@[simp] theorem act_assign : act (·⟨.assign x e, σ⟩) = {.N} := by simp [act]
@[simp] theorem act_seq : act (·⟨.seq C₁ C₂, σ⟩) = act (·⟨C₁, σ⟩) := by
  ext
  simp_all [act]
  split_ifs
  · simp_all
  · conv in ∃ c' : Conf ϖ, _ => rw [exists_comm]; arg 1; ext; rw [exists_comm]
    simp_all only [exists_eq_right, not_false_eq_true, exists_succ_iff]
@[simp] theorem act_prob : act (·⟨.prob C₁ p C₂, σ⟩) = {.N} := by
  ext
  simp_all [act]
  rintro ⟨_⟩
  split_ifs
  · simp
  · if 0 < p.val σ then (use p.val σ); simp_all else (use 1 - p.val σ); simp_all
@[simp] theorem act_nonDet : act (·⟨.nonDet C₁ C₂, σ⟩) = {.L, .R} := by
  ext; simp [act]; aesop
@[simp] theorem act_loop : act (·⟨.loop b C, σ⟩) = {.N} := by simp [act]
@[simp] theorem act_tick : act (·⟨.tick r, σ⟩) = {.N} := by simp [act]

instance act_nonempty (s : Conf ϖ) : Nonempty (act s) := by
  rcases s with (_ | ⟨σ' | c', σ'⟩) <;> (try induction c') <;> simp_all

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
    (∑' (p : { p // c ⤳[α,p] c' }), p.val) = (∑' p, if c ⤳[α,p] c' then p else 0) := by
  apply tsum_eq_tsum_of_ne_zero_bij (fun ⟨x, _⟩ ↦ ⟨x, by simp_all⟩) <;> simp_all
  exact StrictMono.injective fun ⦃a b⦄ a ↦ a

def succs (c : Conf ϖ) (α : Act) : Set (Conf ϖ) := {c' | ∃ p, c ⤳[α, p] c'}
noncomputable def succs_fin (c : Conf ϖ) (α : Act) : Finset (Conf ϖ) :=
  match c, α with
  | none, .N => {none}
  | ·⟨⇓ ϖ, _⟩, .N => {none}
  | ·⟨skip, σ⟩, .N => {·⟨⇓ ϖ, σ⟩}
  | ·⟨tick _, σ⟩, .N => {·⟨skip, σ⟩}
  | ·⟨x ::= E, σ⟩, .N => {·⟨skip, σ[x ↦ E σ]⟩}
  | ·⟨.prob C₁ p C₂, σ⟩, .N =>
    if p.val σ = 0 then {·⟨C₂, σ⟩} else if p.val σ = 1 then {·⟨C₁, σ⟩} else {·⟨C₁, σ⟩, ·⟨C₂, σ⟩}
  | ·⟨C₁ [] _, σ⟩, .L => {(·⟨C₁, σ⟩)}
  | ·⟨_ [] C₂, σ⟩, .R => {(·⟨C₂, σ⟩)}
  | ·⟨.loop b C, σ⟩, .N => if b σ then {·⟨C.seq (.loop b C), σ⟩} else {·⟨.skip, σ⟩}
  | ·⟨.seq .skip C₂, σ⟩, .N => {·⟨C₂, σ⟩}
  | ·⟨.seq C₁ C₂, σ⟩, α => succs_fin (·⟨C₁, σ⟩) α |>.map ⟨C₂.after, C₂.after_inj⟩
  | _, _ => {}

theorem succs_eq_succs_fin :
    succs (ϖ:=ϖ) c α = (succs_fin c α).toSet := by
  ext s'
  simp [succs]
  constructor
  · simp
    intro p h
    induction h with try simp_all [succs_fin]
    | seq_R => unfold succs_fin; split <;> simp_all
    | prob_L | prob_R => split_ifs <;> simp_all
  · intro h
    induction c, α using succs_fin.induct generalizing s' with (simp_all [succs_fin]; try subst_eqs)
    | case6 | case7 => (use 1); simp
    | case8 => aesop
    | case14 _ _ _ _ _ ih =>
      obtain ⟨(_ | ⟨σ' | c', σ'⟩), h, _, _⟩ := h <;> obtain ⟨_, _⟩ := ih _ h <;> simp_all
      rintro ⟨_⟩; simp_all

theorem sums_to_one (h₀ : c ⤳[α,p₀] c₀) :
    (∑' (c' : Conf ϖ) (p : {p // c ⤳[α,p] c'}), p.val) = 1 := by
  induction h₀ with simp_all [ite_and]
  | seq_R =>
    rename_i C₂ h ih
    rw [← ih]
    apply C₂.tsum_after_eq <;> simp_all [ite_and] <;> split_ifs <;> simp_all
    intros _ _ _ _ h _ h'
    apply Exists.intro _ ⟨h, h'⟩
  | prob_L | prob_R =>
    rename_i C₁ C₂ _ σ _ _
    rw [ENNReal.tsum_eq_add_tsum_ite (·⟨C₁,σ⟩), ENNReal.tsum_eq_add_tsum_ite (·⟨C₂,σ⟩)]
    simp_all [ite_and, eq_comm]

end SmallStep

noncomputable def OMDP : MDP (Conf ϖ) Act :=
  MDP.ofRelation SmallStep SmallStep.p_ne_zero SmallStep.sums_to_one SmallStep.progress

namespace OMDP

@[simp]
theorem act_eq : OMDP.act = SmallStep.act (ϖ:=ϖ) := by
  ext c α
  simp [OMDP, MDP.ofRelation_act, SmallStep.act]

@[simp]
theorem succs_univ_eq : (OMDP (ϖ:=ϖ)).succs_univ = fun c ↦ {c' | ∃ α p, c ⤳[α,p] c'} := by
  simp [OMDP]

@[simp]
theorem P_eq : (OMDP (ϖ:=ϖ)).P = (fun c α c' ↦ ∑' (p : { p // c ⤳[α,p] c' }), ↑p) := by simp [OMDP]

theorem P_support_eq_succs : (Function.support (OMDP.P c α)) = SmallStep.succs (ϖ:=ϖ) c α := by
  ext c'
  simp [SmallStep.succs]
  constructor
  · simp; intro p h hp; use p
  · simp; intro p h; use p, h, SmallStep.p_ne_zero h

instance : MDP.FiniteBranching (OMDP (ϖ:=ϖ)) where
  act_fin c := Set.toFinite (OMDP.act c)
  succs_fin c α := by
    simp only [OMDP.P_support_eq_succs, SmallStep.succs_eq_succs_fin, Finset.finite_toSet]

@[simp]
noncomputable def cost (X : Exp ϖ)
  | ·⟨⇓ ϖ, σ⟩ => X σ
  | ·⟨tick r, σ⟩ => r σ
  | ·⟨c' ; _, σ⟩ => cost X (·⟨c', σ⟩)
  | _ => 0

@[simp] theorem cost_X_of_pGCL : cost X (·⟨C, σ⟩) = cost 0 (·⟨C, σ⟩) := by induction C <;> simp_all

@[simp]
theorem Φ_simp {C : Conf ϖ} :
    OMDP.Φ c f C = c C + ⨅ α ∈ SmallStep.act C, ∑' s' : OMDP.succs_univ C, OMDP.P C α s' * f s'
:= by simp [MDP.Φ, MDP.Φf, iInf_subtype]

@[simp]
theorem bot_eq {X : Exp ϖ} : (OMDP.Φ (cost X))^[i] ⊥ none = 0 := by
  induction i <;> simp_all [-Function.iterate_succ, Function.iterate_succ']

noncomputable instance : Decidable (s' ∈ (OMDP (ϖ:=ϖ)).succs_univ s) := Classical.propDecidable _

theorem tsum_succs_univ' (f : (OMDP (ϖ:=ϖ)).succs_univ c → ENNReal) :
    (∑' s', f s') = ∑' s', if h : _ then f ⟨s', h⟩ else 0 := by
  symm
  apply tsum_eq_tsum_of_ne_zero_bij (·.val.val) _ _ (by simp_all)
  · intro ⟨_, _⟩ ⟨_, _⟩; simp; apply SetCoe.ext
  · simp_all; intro _ α p _ _; use α, p

variable {X : Exp ϖ}

@[simp]
theorem sink_eq : (OMDP.Φ (cost X))^[i] ⊥ (some (none, σ)) = if i = 0 then 0 else X σ := by
  induction i <;> simp_all [-Function.iterate_succ, Function.iterate_succ', OMDP.tsum_succs_univ']

@[simp]
theorem lfp_Φ_bot : OMDP.lfp_Φ (cost X) none = 0 := by simp [MDP.lfp_Φ_eq_iSup'_Φ, MDP.iSup'_Φ]

@[simp]
theorem lfp_Φ_sink : OMDP.lfp_Φ (cost X) (some (none, σ)) = X σ := by
  rw [← MDP.lfp_Φ_step]; simp_all [tsum_succs_univ']

noncomputable def step : (pGCL ϖ → Exp ϖ → Exp ϖ) →o pGCL ϖ → Exp ϖ → Exp ϖ :=
  ⟨fun Y ↦ (fun C X σ ↦
    OMDP.Φ (cost X) (match · with | ·⟨⇓ ϖ,σ'⟩ => X σ' | ·⟨C',σ'⟩ => Y C' X σ' | ⊥ => 0) (·⟨C, σ⟩))
    , by
      intro _ _ _ _ _ _
      apply (OMDP.Φ _).mono
      rintro (_ | ⟨_ | _, _⟩) <;> try rfl
      apply_assumption⟩

variable {f : pGCL ϖ → Exp ϖ → Exp ϖ}

@[simp] theorem step.skip : step f skip = (· ·) := by simp_all [step, OMDP.tsum_succs_univ']
@[simp] theorem step.assign : step f (.assign x e) = fun X σ ↦ f .skip X (σ[x ↦ e σ]) :=
  by simp_all [step, OMDP.tsum_succs_univ']
@[simp] theorem step.tick : step f (.tick r) = fun X ↦ r + f .skip X := by
  simp_all [step, OMDP.tsum_succs_univ']; rfl
@[simp] theorem step.prob : step f (.prob C₁ p C₂) = fun X ↦ p.pick (f C₁ X) (f C₂ X) := by
  simp_all [step, OMDP.tsum_succs_univ']
  ext X σ
  rw [ENNReal.tsum_eq_add_tsum_ite (·⟨C₁,σ⟩), ENNReal.tsum_eq_add_tsum_ite (·⟨C₂,σ⟩)]
  by_cases C₁ = C₂ <;> simp_all [eq_comm, ite_and]
@[simp] theorem step.nonDet : step f (.nonDet C₁ C₂) = f C₁ ⊓ f C₂ := by
  ext X σ
  simp [step, MDP.Φ, MDP.Φf]
  simp_all [ite_and, OMDP.tsum_succs_univ']
  apply le_antisymm <;> simp
  · constructor
    · apply iInf_le_of_le ⟨.L, by simp⟩
      rw [tsum_eq_single (·⟨C₁,σ⟩) (by simp_all [Imp.swap])]; simp
    · apply iInf_le_of_le ⟨.R, by simp⟩
      rw [tsum_eq_single (·⟨C₂,σ⟩) (by simp_all [Imp.swap])]; simp
  · rintro α (⟨_, _⟩ | ⟨_, _⟩)
    · rw [ENNReal.tsum_eq_add_tsum_ite (·⟨C₁,σ⟩)]; simp
    · rw [ENNReal.tsum_eq_add_tsum_ite (·⟨C₂,σ⟩)]; simp
theorem step.loop :
    step f (.loop b C) = fun X ↦ b.probOf * f (C ; .loop b C) X + b.not.probOf * f .skip X := by
  funext X σ
  simp [step, OMDP.tsum_succs_univ']
  split_ifs <;> simp_all

end OMDP

open OMDP

noncomputable def dop (C : pGCL ϖ) (X : Exp ϖ) : Exp ϖ := (OMDP.lfp_Φ (cost X) <| ·⟨C, ·⟩)

theorem dop_eq_iSup_Φ : dop (ϖ:=ϖ) = ⨆ n, fun C X σ ↦ (OMDP.Φ (cost X))^[n] ⊥ (·⟨C,σ⟩) := by
  ext C X σ; rw [dop, MDP.lfp_Φ_eq_iSup'_Φ, MDP.iSup'_Φ]; apply le_antisymm <;> simp
theorem dop_eq_iSup_succ_Φ :
    dop (ϖ:=ϖ) = ⨆ n, fun C X σ ↦ (OMDP.Φ (cost X))^[n + 1] ⊥ (·⟨C,σ⟩) := by
  ext C X σ; rw [dop, MDP.lfp_Φ_eq_iSup_Φ, MDP.iSup_Φ]; apply le_antisymm <;> simp

theorem step_dop : step (ϖ:=ϖ) dop = dop := by
  funext C X σ
  rw [dop, ← MDP.lfp_Φ_step]
  simp only [step, OrderHom.coe_mk]
  congr! 3 with C'
  rcases C' with ⟨none, σ'⟩ | ⟨C', σ'⟩ | _ <;> simp [dop]

@[simp] theorem dop_skip : dop (ϖ:=ϖ) .skip = (· ·) := by rw [← step_dop]; simp

theorem dop_isLeast (b : pGCL ϖ → Exp ϖ → Exp ϖ) (h : step b ≤ b) : dop ≤ b := by
  rw [dop_eq_iSup_Φ, iSup_le_iff]
  intro n
  induction n with
  | zero => intros _ _ _; simp
  | succ i ih =>
    refine le_trans (fun _ _ _ ↦ ?_) h
    simp [Function.iterate_succ', step, -Function.iterate_succ]
    gcongr; split <;> simp_all [ih _ _ _]; split_ifs <;> simp

variable {C : pGCL ϖ}

attribute [-simp] Function.iterate_succ in
theorem dop_le_seq : C.dop ∘ C'.dop ≤ (C ; C').dop := by
  intro X σ
  nth_rw 1 [dop_eq_iSup_succ_Φ]
  simp
  intro n
  induction n generalizing C C' σ with
  | zero => nth_rw 2 [← step_dop]; simp_all [step, MDP.Φf]
  | succ i ih =>
    nth_rw 2 [← step_dop]
    rw [Function.iterate_succ', Function.comp_apply]
    simp [step, OMDP.tsum_succs_univ']
    refine add_le_add (le_refl _) (iInf₂_mono fun α hα ↦ C'.tsum_after_le (by simp) ?_ ?_)
    all_goals intros; simp_all; split_ifs <;> simp_all [mul_le_mul]

theorem step_dwp : step (ϖ:=ϖ) dwp = dwp := by
  funext C; induction C with try simp_all
  | loop => rw [step.loop, dwp_loop_fp]; rfl
  | seq C₁ C₂ ih₁ ih₂ =>
    ext X σ
    rw [← ih₁]
    simp [step, OMDP.tsum_succs_univ']
    congr! 4
    apply C₂.tsum_after_eq <;> simp_all <;> split_ifs <;> simp_all
    rintro _ _ _ _ _ h ⟨_⟩ _ _ h' ⟨_⟩ hp _
    exact ⟨⟨_, _, h⟩, _, h', hp⟩

theorem dwp_le_dop.loop (ih : C.dwp ≤ C.dop) : dwp (.loop b C) ≤ dop (.loop b C) := by
  refine fun X ↦ OrderHom.lfp_le (dwp_loop_f b C X) (le_trans ?_ <| step_dop.le _ _ ·)
  simp_all [step, OMDP.tsum_succs_univ', dwp_loop_f]
  split_ifs <;> simp_all; apply (ih _).trans (dop_le_seq _)

theorem dwp_le_dop : dwp (ϖ:=ϖ) ≤ dop := by
  intro C
  induction C with
  | skip => simp
  | assign => rw [← step_dop]; simp
  | prob C₁ p C₂ ih₁ ih₂ => rw [← step_dop]; intro X; simp_all [ih₁ X, ih₂ X]
  | nonDet C₁ C₂ ih₁ ih₂ => intro X σ; rw [← step_dop]; simp_all [ih₁ X σ, ih₂ X σ]
  | loop b C ih => exact dwp_le_dop.loop ih
  | seq C₁ C₂ ih₁ ih₂ => intro; exact (dwp.monotone _ (ih₂ _)).trans (ih₁ _) |>.trans (dop_le_seq _)
  | tick => rw [← step_dop]; simp

theorem dop_eq_dwp : dop (ϖ:=ϖ) = dwp := (dop_isLeast _ step_dwp.le).antisymm dwp_le_dop
