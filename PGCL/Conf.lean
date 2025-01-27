import PGCL.pGCL

namespace pGCL

inductive Act where | L | R | N
deriving BEq, DecidableEq, Inhabited

noncomputable instance Act.instFintype : Fintype Act where
  elems := {.L, .R, .N}
  complete := fun a ↦ by cases a <;> simp

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

noncomputable instance decidableEq : DecidableEq (Conf ϖ) := Classical.typeDecidableEq (Conf ϖ)

end pGCL.Conf
