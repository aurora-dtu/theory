import Mathlib.Topology.Instances.ENNReal.Lemmas
import MDP.SmallStepSemantics
import PGCL.pGCL

namespace pGCL

inductive Act where | L | R | N
deriving BEq, DecidableEq, Inhabited

noncomputable instance Act.instFintype : Fintype Act where
  elems := {.L, .R, .N}
  complete := fun a ↦ by cases a <;> simp

@[grind]
inductive Termination where | fault | term

@[reducible]
def Conf₀ (ϖ : Type*) := pGCL ϖ × States ϖ
@[reducible]
def Conf₁ (ϖ : Type*) := (pGCL ϖ ⊕ Termination) × States ϖ

@[reducible]
def Conf' (ϖ : Type*) := Conf (pGCL ϖ) (States ϖ) Termination

namespace Conf

variable {ϖ : Type*}
variable [DecidableEq ϖ]

section Syntax

open Lean PrettyPrinter Delaborator SubExpr

declare_syntax_cat cpgcl_conf
syntax "conf[" cpgcl_conf "," term "]" : term
syntax "conf[" "⊥" "]" : term
declare_syntax_cat cpgcl_conf₀
syntax "conf₀[" cpgcl_conf₀ "," term "]" : term
declare_syntax_cat cpgcl_conf₁
syntax "conf₁[" cpgcl_conf₁ "," term "]" : term

syntax "↯" : cpgcl_conf
syntax "↯" term : cpgcl_conf
syntax "⇓" : cpgcl_conf
syntax "⇓" term : cpgcl_conf
syntax cpgcl_prog : cpgcl_conf

syntax cpgcl_prog : cpgcl_conf₀

syntax "↯" : cpgcl_conf₁
syntax "↯" term : cpgcl_conf₁
syntax "⇓" : cpgcl_conf₁
syntax "⇓" term : cpgcl_conf₁
syntax cpgcl_prog : cpgcl_conf₁

macro_rules
| `(conf[↯, $σ]) => `(Conf.term Termination.fault $σ)
| `(conf[↯ $t, $σ]) => `((conf[↯, $σ] : Conf' $t))
| `(conf[⇓, $σ]) => `(Conf.term Termination.term $σ)
| `(conf[⇓ $t, $σ]) => `((conf[⇓, $σ] : Conf' $t))
| `(conf[$c:cpgcl_prog, $σ]) => `(Conf.prog (pgcl {$c}) $σ)
| `(conf[⊥]) => `(Conf.bot)

macro_rules
| `(conf₀[$c:cpgcl_prog, $σ]) => `((pgcl {$c}, $σ))

macro_rules
| `(conf₁[↯, $σ]) => `((Sum.inr Termination.fault, $σ))
| `(conf₁[↯ $t, $σ]) => `((conf₁[↯, $σ] : Conf₁' $t))
| `(conf₁[⇓, $σ]) => `((Sum.inr Termination.term, $σ))
| `(conf₁[⇓ $t, $σ]) => `((conf₁[⇓, $σ] : Conf₁' $t))
| `(conf₁[$c:cpgcl_prog, $σ]) => `((Sum.inl pgcl {$c}, $σ))

#check fun σ ↦ conf[↯, σ]
#check fun σ ↦ conf[⇓, σ]
#check fun σ ↦ conf[skip, σ]

#check fun σ ↦ conf₀[skip, σ]

#check fun σ ↦ conf₁[↯, σ]
#check fun σ ↦ conf₁[⇓, σ]
#check fun σ ↦ conf₁[skip ; skip, σ]

end Syntax

end Conf

@[simp] theorem seq_ne_right : ¬seq C₁ C₂ = C₂ := (by (absurd congrArg SizeOf.sizeOf ·); simp)
@[simp] theorem right_ne_seq : ¬C₂ = seq C₁ C₂ := (seq_ne_right ·.symm)
@[simp] theorem left_ne_seq : ¬C₁ = seq C₁ C₂ := (by (absurd congrArg SizeOf.sizeOf ·); simp; omega)
@[simp] theorem seq_ne_left : ¬seq C₁ C₂ = C₁ := (left_ne_seq ·.symm)

def after (C' : pGCL ϖ) : Conf₁ ϖ → Conf₁ ϖ
  | conf₁[~c, σ] => conf₁[~c ; ~C', σ]
  | conf₁[⇓, σ] => conf₁[~C', σ]
  | conf₁[↯, σ] => conf₁[↯, σ]

@[grind inj]
def after_inj (C' : pGCL ϖ) : Function.Injective C'.after := by
  intro c₁ c₂ h
  simp_all [after]
  split at h <;> split at h <;> simp_all

@[simp]
theorem after_eq_seq_iff : pGCL.after C₂ c = conf₁[~C₁ ; ~C₂, σ] ↔ c = conf₁[~C₁, σ] := by
  simp [after]
  split <;> simp_all

-- @[simp] theorem after_none : after C₂ .bot = .bot := by simp [after]
@[simp] theorem after_term : after C₂ conf₁[⇓, σ] = conf₁[~C₂, σ] := by simp [after]
@[simp] theorem after_fault : after C₂ conf₁[↯, σ] = conf₁[↯, σ] := by simp [after]
@[simp] theorem after_eq_right : after C₂ a = conf₁[~C₂,σ] ↔ a = conf₁[⇓, σ] := by
  simp [after]; split <;> simp
@[simp] theorem after_neq_term : ¬after C₂ c' = conf₁[⇓, σ] := by simp [after]; split <;> simp
-- @[simp] theorem after_eq_none : after C₂ c' = .bot ↔ c' = .bot := by simp [after]; split <;> simp

theorem tsum_after_eq (C₂ : pGCL ϖ) {f g : Conf₁ ϖ → ENNReal}
  (hg₂ : ∀ σ, g conf₁[⇓, σ] = 0)
  (hg₂' : ∀ σ, f conf₁[↯, σ] = 0 → g conf₁[↯, σ] = 0)
  (hg₃ : ∀ C σ, ¬g conf₁[~C, σ] = 0 → ∃ a, ¬f a = 0 ∧ C₂.after a = conf₁[~C, σ])
  (hf₂ : ∀ σ, ¬f conf₁[⇓, σ] = 0 → f conf₁[⇓, σ] = g conf₁[~C₂, σ])
  (hf₂' : ∀ σ, ¬f conf₁[↯, σ] = 0 → f conf₁[↯, σ] = g conf₁[↯, σ])
  (hf₃ : ∀ C σ, ¬f conf₁[~C, σ] = 0 → f conf₁[~C, σ] = g conf₁[~C ; ~C₂, σ]) :
    (∑' s, g s) = ∑' s, f s :=
  tsum_eq_tsum_of_ne_zero_bij (C₂.after ·.val) (fun ⟨_, _⟩ ⟨_, _⟩ ↦ by simp; apply C₂.after_inj)
    (by rintro ⟨(za | _ | _), σ⟩ <;> simp_all
        intro h
        right
        use .fault, σ
        simp
        contrapose! h
        exact hg₂' σ h)
    (by rintro ⟨(za | za | zb), h⟩ <;> simp at h
        · simp [hf₃ _ _ h, after]
        · simp [hf₂' _ h]
        · simp [hf₂ _ h])

theorem tsum_after_eq' (C₂ : pGCL ϖ) {f g : (ENNReal × Conf₁ ϖ) → ENNReal}
  (hg₂ : ∀ p σ, g (p, conf₁[⇓, σ]) = 0)
  (hg₂' : ∀ p σ, f (p, conf₁[↯, σ]) = 0 → g (p, conf₁[↯, σ]) = 0)
  (hg₃ : ∀ p C σ, ¬g (p, conf₁[~C, σ]) = 0 → ∃ a, ¬f (p, a) = 0 ∧ C₂.after a = conf₁[~C, σ])
  (hf₂ : ∀ p σ, ¬f (p, conf₁[⇓, σ]) = 0 → f (p, conf₁[⇓, σ]) = g (p, conf₁[~C₂, σ]))
  (hf₂' : ∀ p σ, ¬f (p, conf₁[↯, σ]) = 0 → f (p, conf₁[↯, σ]) = g (p, conf₁[↯, σ]))
  (hf₃ : ∀ p C σ, ¬f (p, conf₁[~C, σ]) = 0 → f (p, conf₁[~C, σ]) = g (p, conf₁[~C ; ~C₂, σ])) :
    (∑' s, g s) = ∑' s, f s :=
  tsum_eq_tsum_of_ne_zero_bij (fun ⟨(p, C), _⟩ ↦ (p, C₂.after C))
    (fun ⟨⟨_, a⟩, _⟩ ⟨⟨_, b⟩, _⟩ h ↦ by
      simp_all only [Prod.exists, Sum.exists, Prod.mk.injEq, Subtype.mk.injEq, true_and]
      exact C₂.after_inj h.right)
    (by
      rintro ⟨p, ⟨(_ | _ | _), σ⟩⟩ <;> simp_all
      intro h
      right
      use .fault, σ
      simp
      contrapose! h
      exact hg₂' p σ h)
    (by rintro ⟨⟨p, (_ | _ | _), σ⟩, h⟩ <;> simp at h
        · simp [hf₃ p _ _ h, after]
        · simp [hf₂' p _ h]
        · simp [hf₂ p _ h])

theorem tsum_after_eq'' (C₂ : pGCL ϖ) {f g : (ENNReal × Conf₁ ϖ) → ENNReal}
  (hg₂ : ∀ p σ, g (p, conf₁[⇓, σ]) = 0)
  (hg₂' : ∀ p σ, f (p, conf₁[↯, σ]) = 0 → g (p, conf₁[↯, σ]) = 0)
  (hg₃ : ∀ p C σ, ¬g (p, conf₁[~C, σ]) = 0 → ∃ a, ¬f (p, a) = 0 ∧ C₂.after a = conf₁[~C, σ])
  (hf : ∀ (a : ENNReal),
    (∀ (C : pGCL ϖ) (σ : States ϖ),
        ¬f (a, Sum.inl C, σ) = 0 → g (a, C₂.after (Sum.inl C, σ)) = f (a, Sum.inl C, σ)) ∧
      ∀ (t : Termination) (σ : States ϖ),
        ¬f (a, Sum.inr t, σ) = 0 → g (a, C₂.after (Sum.inr t, σ)) = f (a, Sum.inr t, σ)) :
    (∑' s, g s) = ∑' s, f s :=
  tsum_eq_tsum_of_ne_zero_bij (fun ⟨(p, C), _⟩ ↦ (p, C₂.after C))
    (fun ⟨⟨_, a⟩, _⟩ ⟨⟨_, b⟩, _⟩ h ↦ by
      simp_all only [Prod.exists, Sum.exists, Prod.mk.injEq, Subtype.mk.injEq, true_and]
      exact C₂.after_inj h.right)
    (by
      rintro ⟨p, ⟨(_ | _ | _), σ⟩⟩ <;> simp_all
      intro h
      right
      use .fault, σ
      simp
      contrapose! h
      exact hg₂' p σ h)
    (by simp; apply hf)

theorem tsum_after_le (C₂ : pGCL ϖ) {f g : Conf₁ ϖ → ENNReal}
  (h₂ : ∀ σ, g conf₁[⇓, σ] ≤ f conf₁[~C₂, σ])
  (h₂ : ∀ σ, g conf₁[↯, σ] ≤ f conf₁[↯, σ])
  (h₂ : ∀ C σ, g conf₁[~C, σ] ≤ f conf₁[~C ; ~C₂, σ]) :
    (∑' s, g s) ≤ ∑' s, f s :=
  Summable.tsum_le_tsum_of_inj C₂.after C₂.after_inj (by simp_all)
    (by rintro ((_ | _) | _ | _) <;> simp_all [after]) (by simp) (by simp)

theorem tsum_after_le' (C₂ : pGCL ϖ) {f g : (ENNReal × Conf₁ ϖ) → ENNReal}
  (h₁ : ∀ p σ, g (p, conf₁[⇓, σ]) ≤ f (p, conf₁[~C₂, σ]))
  (h₂ : ∀ p σ, g (p, conf₁[↯, σ]) ≤ f (p, conf₁[↯, σ]))
  (h₃ : ∀ p C σ, g (p, conf₁[~C, σ]) ≤ f (p, conf₁[~C ; ~C₂, σ])) :
    (∑' s, g s) ≤ ∑' s, f s :=
  Summable.tsum_le_tsum_of_inj
    (Prod.map id C₂.after) (Function.Injective.prodMap (fun _ _ ↦ id) C₂.after_inj) (by simp_all)
    (by rintro ⟨p, ((_ | _) | _ | _)⟩ <;> simp_all [after]) (by simp) (by simp)

end pGCL
