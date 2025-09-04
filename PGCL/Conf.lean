import Mathlib.Topology.Instances.ENNReal.Lemmas
import PGCL.pGCL

namespace pGCL

inductive Act where | L | R | N
deriving BEq, DecidableEq, Inhabited

noncomputable instance Act.instFintype : Fintype Act where
  elems := {.L, .R, .N}
  complete := fun a ↦ by cases a <;> simp

inductive Point (ϖ : Type*) where
  /-- ↯ -/
  | fault
  /-- ⇓ -/
  | term
  | prog (p : pGCL ϖ)

@[reducible]
def Conf (ϖ : Type*) := Option (Point ϖ × States ϖ)

namespace Conf

variable {ϖ : Type*}
variable [DecidableEq ϖ]

section Syntax

open Lean PrettyPrinter Delaborator SubExpr

declare_syntax_cat cpgcl_conf
syntax "conf[" cpgcl_conf "," term "]" : term

-- syntax:max "~" term:max : cpgcl_conf
-- macro_rules
-- | `(conf { ~$c }) => `($c)

syntax "↯" : cpgcl_conf
syntax "↯" term : cpgcl_conf
syntax "⇓" : cpgcl_conf
syntax "⇓" term : cpgcl_conf
syntax cpgcl_prog : cpgcl_conf

macro_rules
| `(conf[↯, $σ]) => `(some (Point.fault, $σ))
| `(conf[↯ $t, $σ]) => `(some ((Point.fault : Point $t), $σ))
| `(conf[⇓, $σ]) => `(some (Point.term, $σ))
| `(conf[⇓ $t, $σ]) => `(some ((Point.term : Point $t), $σ))
| `(conf[$c:cpgcl_prog, $σ]) => `(some ((Point.prog (pgcl {$c})), $σ))

#check fun σ ↦ conf[↯, σ]
#check fun σ ↦ conf[⇓, σ]
#check fun σ ↦ conf[skip, σ]

end Syntax

-- notation:90 "·⟨⇓" ϖ "," rhs "⟩" => some ((Point.term : Point ϖ), rhs)
-- notation:90 "·⟨↯" ϖ "," rhs "⟩" => some ((Point.fault : Point ϖ), rhs)
-- notation:90 "·⟨" lhs "," rhs "⟩" => some (Point.prog lhs, rhs)
-- notation:90 "·⟨skip," rhs "⟩" => ·⟨pGCL.skip, rhs⟩
-- notation:90 "·⟨if " B " then " C₁ " else " C₂ "," rhs "⟩" => ·⟨pGCL.ite B C₁ C₂, rhs⟩
-- notation:90 "·⟨" C₁ "[]" C₂ "," rhs "⟩" => ·⟨pGCL.nonDet C₁ C₂, rhs⟩
-- notation:90 "·⟨" C₁ "[" p "]" C₂ "," rhs "⟩" => ·⟨pGCL.prob C₁ p C₂, rhs⟩
-- notation:90 "·⟨tick " E "," rhs "⟩" => ·⟨pGCL.tick E, rhs⟩

instance : Bot (Conf ϖ) := ⟨none⟩

instance : Coe (Point ϖ × States ϖ) (Conf ϖ) where
  coe := some

noncomputable instance decidableEq : DecidableEq (Conf ϖ) := Classical.typeDecidableEq _

end Conf

@[simp] theorem seq_ne_right : ¬seq C₁ C₂ = C₂ := (by (absurd congrArg SizeOf.sizeOf ·); simp)
@[simp] theorem right_ne_seq : ¬C₂ = seq C₁ C₂ := (seq_ne_right ·.symm)
@[simp] theorem left_ne_seq : ¬C₁ = seq C₁ C₂ := (by (absurd congrArg SizeOf.sizeOf ·); simp; omega)
@[simp] theorem seq_ne_left : ¬seq C₁ C₂ = C₁ := (left_ne_seq ·.symm)

def after (C' : pGCL ϖ) : Conf ϖ → Conf ϖ
  | conf[~c, σ] => conf[~c ; ~C', σ]
  | conf[⇓, σ] => conf[~C', σ]
  | conf[↯, σ] => conf[↯, σ]
  | none => none

def after_inj (C' : pGCL ϖ) : Function.Injective C'.after := by
  intro c₁ c₂ h
  simp_all [after]
  split at h <;> split at h <;> simp_all

@[simp]
theorem after_eq_seq_iff : pGCL.after C₂ c = conf[~C₁ ; ~C₂, σ] ↔ c = conf[~C₁, σ] := by
  simp [after]
  split <;> simp_all

@[simp] theorem after_none : after C₂ none = none := by simp [after]
@[simp] theorem after_term : after C₂ conf[⇓, σ] = conf[~C₂, σ] := by simp [after]
@[simp] theorem after_fault : after C₂ conf[↯, σ] = conf[↯, σ] := by simp [after]
@[simp] theorem after_eq_right : after C₂ a = conf[~C₂,σ] ↔ a = conf[⇓, σ] := by
  simp [after]; split <;> simp
@[simp] theorem after_neq_term : ¬after C₂ c' = conf[⇓, σ] := by simp [after]; split <;> simp
@[simp] theorem after_eq_none : after C₂ c' = none ↔ c' = none := by simp [after]; split <;> simp

theorem tsum_after_eq (C₂ : pGCL ϖ) {f g : Conf ϖ → ENNReal}
  (hg₁ : f none = 0 → g none = 0)
  (hg₂ : ∀ σ, g conf[⇓, σ] = 0)
  (hg₂' : ∀ σ, f conf[↯, σ] = 0 → g conf[↯, σ] = 0)
  (hg₃ : ∀ C σ, ¬g conf[~C, σ] = 0 → ∃ a, ¬f a = 0 ∧ C₂.after a = conf[~C, σ])
  (hf₁ : ¬f none = 0 → f none = g none)
  (hf₂ : ∀ σ, ¬f conf[⇓, σ] = 0 → f conf[⇓, σ] = g conf[~C₂, σ])
  (hf₂' : ∀ σ, ¬f conf[↯, σ] = 0 → f conf[↯, σ] = g conf[↯, σ])
  (hf₃ : ∀ C σ, ¬f conf[~C, σ] = 0 → f conf[~C, σ] = g conf[~C ; ~C₂, σ]) :
    (∑' s, g s) = ∑' s, f s :=
  tsum_eq_tsum_of_ne_zero_bij (C₂.after ·.val) (fun ⟨_, _⟩ ⟨_, _⟩ ↦ by simp; apply C₂.after_inj)
    (by rintro (_ | _ | _) <;> simp_all [not_imp_not.mpr hg₁]
        rename_i σ
        intro h
        use conf[↯, σ]
        simp
        contrapose! h
        exact hg₂' σ h)
    (by rintro ⟨(_ | _ | _), h⟩
        · simp [hf₁ h, after]
        · simp [hf₂' _ h]
        · simp [hf₂ _ h]
        · simp [hf₃ _ _ h, after])

theorem tsum_after_le (C₂ : pGCL ϖ) {f g : Conf ϖ → ENNReal}
  (h₁ : g none ≤ f none)
  (h₂ : ∀ σ, g conf[⇓, σ] ≤ f conf[~C₂, σ])
  (h₂ : ∀ σ, g conf[↯, σ] ≤ f conf[↯, σ])
  (h₂ : ∀ C σ, g conf[~C, σ] ≤ f conf[~C ; ~C₂, σ]) :
    (∑' s, g s) ≤ ∑' s, f s :=
  Summable.tsum_le_tsum_of_inj C₂.after C₂.after_inj (by simp_all)
    (by rintro (_ | _ | _) <;> simp_all [after]) (by simp) (by simp)

end pGCL
