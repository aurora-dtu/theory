import Mathlib.Data.ENNReal.Operations

namespace pGCL

variable {ϖ : Type*}
def States (ϖ : Type*) := ϖ → ENNReal

instance : Nonempty (States ϖ) := ⟨fun _ ↦ Inhabited.default⟩

abbrev Exp (ϖ : Type*) := States ϖ → ENNReal
abbrev BExpr (ϖ : Type*) := States ϖ → Bool
def ProbExp (ϖ : Type*) := {e : Exp ϖ // e ≤ 1}

def States.subst [DecidableEq ϖ] (σ : States ϖ) (x : ϖ) (v : ENNReal) : States ϖ :=
  fun α ↦ if x = α then v else σ α

notation σ "[" x " ↦ " v "]" => States.subst σ x v

def Exp.subst [DecidableEq ϖ] (e : Exp ϖ) (x : ϖ) (A : Exp ϖ) : Exp ϖ := fun σ ↦ e (σ[x ↦ A σ])

@[simp]
theorem Exp.subst_lift [DecidableEq ϖ] (e : Exp ϖ) : e.subst x A σ = e (σ[x ↦ A σ]) := rfl

@[gcongr]
theorem Exp.add_le_add (a b c d : Exp ϖ) (hac : a ≤ c) (hac : b ≤ d) : a + b ≤ c + d := by
  intro; simp; gcongr <;> apply_assumption
@[gcongr]
theorem Exp.mul_le_mul (a b c d : Exp ϖ) (hac : a ≤ c) (hac : b ≤ d) : a * b ≤ c * d := by
  intro; simp; gcongr <;> apply_assumption

namespace BExpr

def not (b : BExpr ϖ) : BExpr ϖ := (!b ·)
def iver (b : BExpr ϖ) : Exp ϖ := (if b · then 1 else 0)
def probOf (b : BExpr ϖ) : ProbExp ϖ := ⟨(if b · then 1 else 0), by intro; simp; split <;> simp⟩

variable {b : BExpr ϖ}

@[simp] theorem true_iver (h : b σ = true) : b.iver σ = 1 := by simp [iver, h]
@[simp] theorem false_iver (h : b σ = false) : b.iver σ = 0 := by simp [iver, h]
@[simp] theorem true_not_iver (h : b σ = true) : b.not.iver σ = 0 := by simp [iver, not, h]
@[simp] theorem false_not_iver (h : b σ = false) : b.not.iver σ = 1 := by simp [iver, not, h]

end BExpr

namespace ProbExp

variable (p : ProbExp ϖ) (σ : States ϖ)

@[simp] theorem add_one : p.val σ + (1 - p.val σ) = 1 := add_tsub_cancel_of_le (p.prop σ)

@[simp] theorem le_one : p.val σ ≤ 1 := p.prop σ
@[simp] theorem lt_one_iff : ¬p.val σ = 1 ↔ p.val σ < 1 := by simp
@[simp] theorem sub_one_le_one : 1 - p.val σ ≤ 1 := by simp
@[simp] theorem ne_top : p.val σ ≠ ⊤ := by intro h; have := p.le_one σ; simp_all
@[simp] theorem top_ne : ⊤ ≠ p.val σ := by intro h; symm at h; simp_all
@[simp] theorem not_zero_off : ¬p.val σ = 0 ↔ 0 < p.val σ := pos_iff_ne_zero.symm

@[simp]
theorem lt_one_iff' : 1 - p.val σ < 1 ↔ ¬p.val σ = 0 :=
  ⟨fun _ _ ↦ by simp_all,
    fun _ ↦ ENNReal.sub_lt_of_sub_lt (p.le_one σ) (.inl (by simp)) (by simp_all)⟩

@[simp]
theorem top_ne_one_sub : ¬⊤ = 1 - p.val σ :=
  by intro h; have := h.trans_le <| p.sub_one_le_one σ; simp at this

@[simp] theorem one_le_iff : 1 ≤ p.val σ ↔ p.val σ = 1 := LE.le.ge_iff_eq (p.le_one σ)

@[simp] theorem ite_eq_zero : (if 0 < p.val σ then p.val σ * x else 0) = p.val σ * x :=
  by split_ifs <;> simp_all
@[simp] theorem ite_eq_one : (if p.val σ < 1 then (1 - p.val σ) * x else 0) = (1 - p.val σ) * x :=
  by split_ifs <;> simp_all

@[simp] theorem ite_eq_zero' : (if 0 < p.val σ then p.val σ else 0) = p.val σ :=
  by split_ifs <;> simp_all
@[simp] theorem ite_eq_one' : (if p.val σ < 1 then (1 - p.val σ) else 0) = 1 - p.val σ :=
  by split_ifs <;> simp_all

noncomputable def pick (x y : Exp ϖ) : Exp ϖ := p.val * x + (1 - p.val) * y

@[simp, gcongr]
theorem pick_le (h₁ : x ≤ z) (h₂ : y ≤ w) : p.pick x y ≤ p.pick z w := by
  intro; simp [pick]; gcongr <;> apply_assumption
@[simp]
theorem pick_le' (h₁ : x ≤ z) (h₂ : y ≤ w) : p.pick x y σ ≤ p.pick z w σ := p.pick_le h₁ h₂ σ

@[simp] theorem pick_same : p.pick x x = x := by ext σ; simp [pick, ← add_mul]

@[simp] theorem pick_of : p.val σ * x σ + (1 - p.val σ) * y σ = p.pick x y σ := rfl

end ProbExp

end pGCL
