import PGCL.pGCL

namespace pGCL

inductive Act where | L | R | N
deriving BEq, DecidableEq, Inhabited

noncomputable instance Act.instFintype : Fintype Act where
  elems := {.L, .R, .N}
  complete := fun a ↦ by cases a <;> simp only [Finset.mem_insert, reduceCtorEq, Finset.mem_singleton, or_self, or_false, or_true]

@[reducible]
def Conf (ϖ : Type*) := Option (Option (pGCL ϖ) × States ϖ)

namespace Conf

variable {ϖ : Type*}
variable [DecidableEq ϖ]

notation:90 "·⟨⇓" ϖ "," rhs "⟩" => some ((none : Option (pGCL ϖ)), rhs)
notation:90 "·⟨" lhs "," rhs "⟩" => some (some lhs, rhs)
notation:90 "·⟨skip," rhs "⟩" => ·⟨pGCL.skip, rhs⟩
notation:90 "·⟨if " B " then " C₁ " else " C₂ "," rhs "⟩" => ·⟨pGCL.ite B C₁ C₂, rhs⟩
notation:90 "·⟨" C₁ "[]" C₂ "," rhs "⟩" => ·⟨pGCL.nonDet C₁ C₂, rhs⟩
notation:90 "·⟨" C₁ "[" p "]" C₂ "," rhs "⟩" => ·⟨pGCL.prob C₁ p C₂, rhs⟩
-- notation:90 "·⟨while (" B ") " C "," rhs "⟩" => ·⟨pGCL.loop B C, rhs⟩
notation:90 "·⟨tick " E "," rhs "⟩" => ·⟨pGCL.tick E, rhs⟩

instance : Bot (Conf ϖ) := ⟨none⟩

instance : Coe (Option (pGCL ϖ) × States ϖ) (Conf ϖ) where
  coe := some

def isNone_iff (c : Conf ϖ) : Option.isNone c ↔ c = ⊥ := by
  simp [Bot.bot]
def isSome_iff (c : Conf ϖ) : Option.isSome c ↔ c ≠ ⊥ := by
  simp [Bot.bot]
  symm
  exact Option.ne_none_iff_isSome

-- @[reducible]
-- def C (c' : Conf ϖ) (h : c' ≠ ⊥) : pGCL ϖ := (c'.get (by simp [isSome_iff, h])).1
-- @[reducible]
-- def σ (c' : Conf ϖ) (h : c' ≠ ⊥) : States ϖ := (c'.get (by simp [isSome_iff, h])).2

noncomputable instance decidableEq : DecidableEq (Conf ϖ) := Classical.typeDecidableEq (Conf ϖ)

@[reducible]
def Choice (ϖ : Type*) := Act × Conf ϖ × { p : ENNReal // 0 < p ∧ p ≤ 1 }

namespace Choice

@[reducible]
def Act  (c: Choice ϖ) : Act      := c.1
@[reducible]
def Conf (c: Choice ϖ) : Conf ϖ   := c.2.1
-- @[reducible]
-- def C    (c: Choice ϖ) (h : c.Conf ≠ ⊥) : pGCL ϖ   := c.Conf.C h
-- @[reducible]
-- def σ    (c: Choice ϖ) (h : c.Conf ≠ ⊥) : States ϖ := c.Conf.σ h
@[reducible]
def P    (c: Choice ϖ) : { p : ENNReal // 0 < p ∧ p ≤ 1 }  := c.2.2

noncomputable instance : One { p : ENNReal // 0 < p ∧ p ≤ 1 } := ⟨1, by simp⟩

-- @[simp]
-- theorem one_prob_is₀₁ : is₀₁ (1 : { p : ENNReal // 0 < p ∧ p ≤ 1 }).val := Or.inr rfl

end Choice

end Conf
