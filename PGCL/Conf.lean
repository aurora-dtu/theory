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

notation:90 "·⟨⇓" ϖ "," rhs "⟩" => some ((Point.term : Point ϖ), rhs)
notation:90 "·⟨↯" ϖ "," rhs "⟩" => some ((Point.fault : Point ϖ), rhs)
notation:90 "·⟨" lhs "," rhs "⟩" => some (Point.prog lhs, rhs)
notation:90 "·⟨skip," rhs "⟩" => ·⟨pGCL.skip, rhs⟩
notation:90 "·⟨if " B " then " C₁ " else " C₂ "," rhs "⟩" => ·⟨pGCL.ite B C₁ C₂, rhs⟩
notation:90 "·⟨" C₁ "[]" C₂ "," rhs "⟩" => ·⟨pGCL.nonDet C₁ C₂, rhs⟩
notation:90 "·⟨" C₁ "[" p "]" C₂ "," rhs "⟩" => ·⟨pGCL.prob C₁ p C₂, rhs⟩
notation:90 "·⟨tick " E "," rhs "⟩" => ·⟨pGCL.tick E, rhs⟩

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
  | some (.prog c, σ) => some (.prog (c.seq C'), σ)
  | some (.term, σ) => some (.prog C', σ)
  | some (.fault, σ) => some (.fault, σ)
  | none => none

def after_inj (C' : pGCL ϖ) : Function.Injective C'.after := by
  intro c₁ c₂ h
  simp_all [after]
  split at h <;> split at h <;> simp_all

@[simp]
theorem after_eq_seq_iff : C₂.after c = ·⟨C₁ ;; C₂, σ⟩ ↔ c = (·⟨C₁, σ⟩) := by
  simp [after]
  split <;> simp_all

@[simp] theorem after_none : after C₂ none = none := by simp [after]
@[simp] theorem after_term : after C₂ (some (.term, σ)) = (·⟨C₂, σ⟩) := by simp [after]
@[simp] theorem after_fault : after C₂ (some (.fault, σ)) = some ⟨.fault, σ⟩ := by simp [after]
@[simp] theorem after_eq_right : after C₂ a = ·⟨C₂,σ⟩ ↔ a = (some (.term, σ)) := by
  simp [after]; split <;> simp
@[simp] theorem after_neq_term : ¬after C₂ c' = (some (.term, σ)) := by simp [after]; split <;> simp
@[simp] theorem after_eq_none : after C₂ c' = none ↔ c' = none := by simp [after]; split <;> simp

theorem tsum_after_eq (C₂ : pGCL ϖ) {f g : Conf ϖ → ENNReal}
  (hg₁ : f none = 0 → g none = 0)
  (hg₂ : ∀ σ, g (·⟨⇓ ϖ, σ⟩) = 0)
  (hg₂' : ∀ σ, f (·⟨↯ ϖ, σ⟩) = 0 → g (·⟨↯ ϖ, σ⟩) = 0)
  (hg₃ : ∀ C σ, ¬g (·⟨C, σ⟩) = 0 → ∃ a, ¬f a = 0 ∧ C₂.after a = (·⟨C, σ⟩))
  (hf₁ : ¬f none = 0 → f none = g none)
  (hf₂ : ∀ σ, ¬f (·⟨⇓ ϖ, σ⟩) = 0 → f (·⟨⇓ ϖ, σ⟩) = g (·⟨C₂, σ⟩))
  (hf₂' : ∀ σ, ¬f (·⟨↯ ϖ, σ⟩) = 0 → f (·⟨↯ ϖ, σ⟩) = g (·⟨↯ ϖ, σ⟩))
  (hf₃ : ∀ C σ, ¬f (·⟨C, σ⟩) = 0 → f (·⟨C, σ⟩) = g (·⟨C ;; C₂, σ⟩)) :
    (∑' s, g s) = ∑' s, f s :=
  tsum_eq_tsum_of_ne_zero_bij (C₂.after ·.val) (fun ⟨_, _⟩ ⟨_, _⟩ ↦ by simp; apply C₂.after_inj)
    (by rintro (_ | _ | _) <;> simp_all [not_imp_not.mpr hg₁]
        rename_i σ
        intro h
        use ·⟨↯ _, σ⟩
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
  (h₂ : ∀ σ, g (·⟨⇓ ϖ, σ⟩) ≤ f (·⟨C₂, σ⟩))
  (h₂ : ∀ σ, g (·⟨↯ ϖ, σ⟩) ≤ f (·⟨↯ ϖ, σ⟩))
  (h₂ : ∀ C σ, g (·⟨C, σ⟩) ≤ f (·⟨C ;; C₂, σ⟩)) :
    (∑' s, g s) ≤ ∑' s, f s :=
  Summable.tsum_le_tsum_of_inj C₂.after C₂.after_inj (by simp_all)
    (by rintro (_ | _ | _) <;> simp_all [after]) (by simp) (by simp)

end pGCL
