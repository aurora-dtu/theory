import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Inv
import Mathlib.Order.OmegaCompletePartialOrder
import STDX.Subst

/-! # Custom operators -/

/-- Syntax typeclass for Heyting co-implication `↜`. -/
@[notation_class]
class HCoImp (α : Type*) where
  /-- Heyting co-implication `↜` -/
  hcoimp : α → α → α

@[notation_class]
class HCoNot (α : Type*) where
  /-- Co-necation `~` -/
  hconot : α → α

@[notation_class]
class Validate (α : Type*) where
  /-- Validate `▵` -/
  validate : α → α

@[notation_class]
class Covalidate (α : Type*) where
  /-- Co-validate `▿` -/
  covalidate : α → α

export HCoImp (hcoimp)
export HCoNot (hconot)
export Validate (validate)
export Covalidate (covalidate)

@[inherit_doc] infixr:60 " ↜ " => hcoimp
@[inherit_doc] prefix:72 "~ " => hconot
@[inherit_doc] prefix:72 "▵ " => validate
@[inherit_doc] prefix:72 "▿ " => covalidate


instance {α : Type*} [HNot α] : Validate α := ⟨fun x ↦ ￢￢x⟩
instance {α : Type*} [HCoNot α] : Covalidate α := ⟨fun x ↦ ~~x⟩

noncomputable instance {α β : Type*} [HCoImp β] : HCoImp (α → β) := ⟨fun φ ψ σ ↦ φ σ ↜ ψ σ⟩
noncomputable instance {α β : Type*} [HCoNot β] : HCoNot (α → β) := ⟨fun φ σ ↦ ~φ σ⟩

noncomputable instance : HCoImp ENNReal := ⟨fun φ ψ ↦ if φ ≥ ψ then 0 else ψ⟩
noncomputable instance : HCoNot ENNReal := ⟨fun φ ↦ φ ⇨ 0⟩
example {φ : ENNReal} : φᶜ = φ ⇨ 0 := by simp [compl, himp]
example {φ : ENNReal} : ￢φ = φ ↜ ⊤ := by simp [hnot, hcoimp]

@[notation_class]
class Iverson (α : Type*) (β : outParam Type*) where
  /-- Iverson brackets `i[b]` -/
  iver : α → β

@[inherit_doc] notation "i[" b "]" => Iverson.iver b

class LawfulIverson (α : Type*) (β : outParam Type*) [Iverson α β] [LE β] [One β] where
  iver_le_one : ∀ (b : α), i[b] ≤ 1

attribute [grind ., simp] LawfulIverson.iver_le_one

namespace Iverson

instance : Iverson Bool ℕ := ⟨fun b ↦ if b then 1 else 0⟩
instance : LawfulIverson Bool ℕ := ⟨by simp [Iverson.iver]⟩
noncomputable instance : Iverson Prop ℕ :=
  ⟨fun b ↦ have : Decidable b := Classical.propDecidable _; if b then 1 else 0⟩
noncomputable instance : LawfulIverson Prop ℕ := ⟨by simp [Iverson.iver]; grind⟩

@[grind =, simp] theorem iver_true : i[true] = 1 := by rfl
@[grind =, simp] theorem iver_True : i[True] = 1 := by simp [iver]
@[grind =, simp] theorem iver_false : i[false] = 0 := by rfl
@[grind =, simp] theorem iver_False : i[False] = 0 := by simp [iver]

@[grind .] theorem iver_not : i[¬b] = 1 - i[b] := by simp [iver]; grind

end Iverson

export Iverson (iver)


/-! # Expressions & States -/

namespace pGCL

variable {ϖ : Type*}
def States (ϖ : Type*) := ϖ → ENNReal

instance : Nonempty (States ϖ) := ⟨fun _ ↦ Inhabited.default⟩

-- def NExp (ϖ : Type*) := States ϖ → ℕ
abbrev Exp (ϖ : Type*) := States ϖ → ENNReal
-- alias NExp := Exp

-- instance States.instSubst [DecidableEq ϖ] : Subst (States ϖ) ϖ (fun _ ↦ ENNReal) where
--   subst σ x v := fun α ↦ if x = α then v else σ α
instance States.instSubst [DecidableEq ϖ] : Substitution (States ϖ) (fun (_ : ϖ) ↦ ENNReal) where
  subst σ := fun v α ↦ if v.1 = α then v.2 else σ α

@[ext] theorem States.ext {σ₁ σ₂ : States ϖ} (h : ∀ v, σ₁ v = σ₂ v) : σ₁ = σ₂ := _root_.funext h

@[grind =, simp] theorem States.subst_apply [DecidableEq ϖ] {σ : States ϖ} :
    σ[x ↦ v] y = if x = y then v else σ y := rfl

namespace Exp

noncomputable section

@[ext]
theorem ext {a b : Exp ϖ} (h : ∀ σ, a σ = b σ) : a = b := funext h

@[coe] def ennreal_coe : ENNReal → Exp ϖ := fun x _ ↦ x
instance : Coe ENNReal (Exp ϖ) := ⟨ennreal_coe⟩

@[grind =, simp] theorem ennreal_coe_apply : ennreal_coe x σ = x := by rfl

-- instance : CommSemiring (Exp ϖ) := inferInstanceAs (CommSemiring (States ϖ → ENNReal))
-- instance : DivInvOneMonoid (Exp ϖ) := inferInstanceAs (DivInvOneMonoid (States ϖ → ENNReal))
-- instance : Sub (Exp ϖ) := inferInstanceAs (Sub (States ϖ → ENNReal))
-- instance : CompleteLattice (Exp ϖ) :=
--   inferInstanceAs (CompleteLattice (States ϖ → ENNReal))

@[simp] theorem bot_eq_0 : (⊥ : Exp ϖ) = 0 := by rfl
@[grind =, simp] theorem top_apply : (⊤ : Exp ϖ) x = ⊤ := by rfl

@[grind =, simp] theorem zero_apply : (@OfNat.ofNat (Exp ϖ) 0 _) x = 0 := rfl
@[grind =, simp] theorem one_apply : (@OfNat.ofNat (Exp ϖ) 1 _) x = 1 := rfl
@[grind =, simp] theorem ofNat_apply {n : ℕ} : (n : Exp ϖ) x = n := rfl
@[grind =, simp] theorem ofNat_apply' [Nat.AtLeastTwo n] :
    @OfNat.ofNat (Exp ϖ) n instOfNatAtLeastTwo x = n := rfl

instance instSubst [DecidableEq ϖ] : Substitution (Exp ϖ) (fun (_ : ϖ) ↦ Exp ϖ) where
  subst X := fun x σ ↦ X (σ[x.1 ↦ x.2 σ])
-- instance instSubst_ennreal [DecidableEq ϖ] : Subst (Exp ϖ) ϖ (fun _ ↦ ENNReal) where
--   subst X x A := X[x ↦ (A : Exp ϖ)]
-- instance instSubst_nat [DecidableEq ϖ] : Subst (Exp ϖ) ϖ (fun _ ↦ ℕ) where
--   subst X x A := X[x ↦ (A : Exp ϖ)]
theorem subst₀_apply [DecidableEq ϖ] {b : Exp ϖ} : Substitution.subst b x σ = b σ[x.1 ↦ x.2 σ] :=
  rfl

@[grind =, simp] theorem subst_ennreal_eq [DecidableEq ϖ] {X : Exp ϖ} {x : ϖ} {A : ENNReal} :
    X[x ↦ ↑A] = X[x ↦ (A : Exp ϖ)] := rfl
@[grind =, simp] theorem subst_nat_eq [DecidableEq ϖ] {X : Exp ϖ} {x : ϖ} {A : ℕ} :
    X[x ↦ ↑A] = X[x ↦ (A : Exp ϖ)] := rfl

section

variable {a b : Exp ϖ}

@[grind =, simp] theorem add_apply : (a + b) x = a x + b x := rfl
@[grind =, simp] theorem sub_apply : (a - b) x = a x - b x := rfl
@[grind =, simp] theorem mul_apply : (a * b) x = a x * b x := rfl
@[grind =, simp] theorem div_apply : (a / b) x = a x / b x := rfl
@[grind =, simp] theorem max_apply : (a ⊔ b) x = a x ⊔ b x := rfl
@[grind =, simp] theorem min_apply : (a ⊓ b) x = a x ⊓ b x := rfl
@[simp] theorem iSup_apply (f : ι → Exp ϖ) : (⨆ i, f i) x = ⨆ i, f i x := _root_.iSup_apply
@[simp] theorem iInf_apply (f : ι → Exp ϖ) : (⨅ i, f i) x = ⨅ i, f i x := _root_.iInf_apply

instance : AddLeftMono (Exp ϖ) := ⟨fun a b c h σ ↦ by
  simp only [add_apply]; gcongr; apply h⟩
instance : AddRightMono (Exp ϖ) := ⟨fun a b c h σ ↦ by
  simp only [Function.swap, add_apply]; gcongr; apply h⟩

@[gcongr]
theorem div_le_div {a b c d : Exp ϖ} (hac : a ≤ c) (hdb : d ≤ b) :
    a / b ≤ c / d := by
  intro σ; simp; gcongr <;> apply_assumption

@[grind =, simp] theorem inv_apply {X : Exp ϖ} : X⁻¹ σ = (X σ)⁻¹ := by rfl
@[grind =, simp] theorem pow_apply {X : Exp ϖ} {n : ℕ} : (X^n) σ = (X σ)^n := by rfl

@[simp] theorem one_sub_one : (1 : Exp ϖ) - 1 = 0 := by ext; simp
@[grind =, simp] theorem sub_zero : (x : Exp ϖ) - 0 = x := by ext; simp

variable [DecidableEq ϖ] {v : ϖ} {e : Exp ϖ}

@[simp] theorem add_subst :
    (a + b)[..xs] = a[..xs] + b[..xs] := Substitution.substs_of_binary fun _ _ ↦ congrFun rfl
@[simp] theorem sub_subst :
    (a - b)[..xs] = a[..xs] - b[..xs] := Substitution.substs_of_binary fun _ _ ↦ congrFun rfl
@[simp] theorem mul_subst :
    (a * b)[..xs] = a[..xs] * b[..xs] := Substitution.substs_of_binary fun _ _ ↦ congrFun rfl
@[simp] theorem div_subst :
    (a / b)[..xs] = a[..xs] / b[..xs] := Substitution.substs_of_binary fun _ _ ↦ congrFun rfl
@[simp] theorem max_subst :
    (a ⊔ b)[..xs] = a[..xs] ⊔ b[..xs] := Substitution.substs_of_binary fun _ _ ↦ congrFun rfl
@[simp] theorem min_subst :
    (a ⊓ b)[..xs] = a[..xs] ⊓ b[..xs] := Substitution.substs_of_binary fun _ _ ↦ congrFun rfl
@[simp] theorem himp_subst :
    (a ⇨ b)[..xs] = a[..xs] ⇨ b[..xs] := Substitution.substs_of_binary fun _ _ ↦ congrFun rfl
@[simp] theorem hcoimp_subst :
    (a ↜ b)[..xs] = a[..xs] ↜ b[..xs] := Substitution.substs_of_binary fun _ _ ↦ congrFun rfl

@[grind =, simp] theorem ennreal_coe_subst {Y : ENNReal} : (↑Y : Exp ϖ)[v ↦ e] = ↑Y := rfl

@[grind =, simp] theorem zero_subst : (@OfNat.ofNat (Exp ϖ) 0 _)[v ↦ e] = 0 := rfl
@[grind =, simp] theorem one_subst : (@OfNat.ofNat (Exp ϖ) 1 _)[v ↦ e] = 1 := rfl
@[grind =, simp] theorem ofNat_subst {n : ℕ} : (n : Exp ϖ)[v ↦ e] = n := rfl
@[grind =, simp] theorem ofNat_subst' [Nat.AtLeastTwo n] :
    (@OfNat.ofNat (Exp ϖ) n instOfNatAtLeastTwo)[v ↦ e] = n := rfl
@[grind =, simp] theorem pow_subst {X : Exp ϖ} {x} {e : Exp ϖ} : (X^n)[x ↦ e] = X[x ↦ e]^n := rfl
@[grind =, simp] theorem inv_subst {X : Exp ϖ} {x} {e : Exp ϖ} : X⁻¹[x ↦ e] = X[x ↦ e]⁻¹ := rfl

omit [DecidableEq ϖ]

theorem himp_apply {φ ψ : Exp ϖ} :
    (φ ⇨ ψ) σ = φ σ ⇨ ψ σ := rfl
@[grind =, simp] theorem hcoimp_apply {φ ψ : Exp ϖ} :
    (φ ↜ ψ) σ = φ σ ↜ ψ σ := rfl
@[grind =, simp] theorem hconot_apply {φ : Exp ϖ} :
    (~φ) σ = ~φ σ := rfl

@[grind =, simp] theorem validate_apply {φ : Exp ϖ} :
    (▵ φ) σ = ▵ φ σ := rfl
@[grind =, simp] theorem covalidate_apply {φ : Exp ϖ} :
    (▿ φ) σ = ▿ φ σ := rfl

example {φ ψ : Exp ϖ} : φ ⇨ ψ = fun σ ↦ if φ σ ≤ ψ σ then ⊤ else ψ σ := by ext σ; simp [himp]
example {φ ψ : Exp ϖ} : φ ↜ ψ = fun σ ↦ if ψ σ ≤ φ σ then 0 else ψ σ := by ext σ; simp [hcoimp]
example {φ : Exp ϖ} : ￢ φ = φ ↜ ⊤ := by ext σ; simp [hnot, hcoimp]
example {φ : Exp ϖ} : ~ φ = φ ⇨ 0 := by ext σ; simp [hconot, himp]
example {φ : Exp ϖ} : ￢ φ = fun σ ↦ if φ σ = ⊤ then 0 else ⊤ := by ext σ; simp [hnot]
example {φ : Exp ϖ} : ~ φ = fun σ ↦ if φ σ = 0 then ⊤ else 0 := by ext σ; simp [hconot, himp]

example {φ : Exp ϖ} : ▵ φ = ￢￢φ := by ext σ; simp [validate]
example {φ : Exp ϖ} : ▿ φ = ~~φ := by ext σ; simp [covalidate]
example {φ : Exp ϖ} : ▵ φ = fun σ ↦ if φ σ = ⊤ then ⊤ else 0 := by
  ext σ; simp [validate, hnot]
example {φ : Exp ϖ} : ▿ φ = fun σ ↦ if φ σ = 0 then 0 else ⊤ := by
  ext σ; simp [covalidate, hconot, himp]

end

@[grind =, simp]
theorem subst_apply [DecidableEq ϖ] (e : Exp ϖ) (x : ϖ) (A : Exp ϖ) :
    e[x ↦ A] σ = e (σ[x ↦ A σ]) := rfl
@[grind =, simp]
theorem subst₂_apply [DecidableEq ϖ] (e : Exp ϖ) (x : ϖ) (A : Exp ϖ) :
    e[x ↦ A, y ↦ B] σ = e (σ[y ↦ B σ[x ↦ A σ], x ↦ A σ]) := by
  simp_all [Substitution.substs_cons, Substitution.subst]
-- @[grind =, simp]
-- theorem substs_apply [DecidableEq ϖ] (e : Exp ϖ) (xs : List (ϖ × Exp ϖ)) :
--     e[..xs] σ = e (σ[..xs.reverse.map (fun (x, v) ↦ (x, v σ))]) := by
--   simp
--   induction xs generalizing e σ with
--   | nil => simp
--   | cons x xs ih =>
--     obtain ⟨x, X⟩ := x
--     simp_all [Substitution.substs_cons]
--     simp [Substitution.substs_append]
--     simp [Substitution.subst, ih]
--     congr! 1
--     nth_rw 2 [Substitution.substs]
--     nth_rw 4 [Substitution.substs]
--     simp
--     simp [Substitution.substs]
--     apply?
--     ext a
--     simp [Substitution.subst]
--     simp [Substitution.substs]
--     simp [Substitution.subst]
--     apply?
--     split_ifs
--     · subst_eqs
--       sorry
--     · nth_rw 2 [Substitution.substs]
--       simp_all [Substitution.subst]
--       sorry
-- @[grind =, simp]
-- theorem subst_apply_ennreal [DecidableEq ϖ] (e : Exp ϖ) (x : ϖ) (n : ENNReal) :
--     e[x ↦ n] σ = e (σ[x ↦ n]) := rfl
-- @[grind =, simp]
-- theorem subst_apply_nat [DecidableEq ϖ] (e : Exp ϖ) (x : ϖ) (n : ℕ) :
--     e[x ↦ n] σ = e (σ[x ↦ (n : ENNReal)]) := rfl

@[gcongr]
theorem add_le_add (a b c d : Exp ϖ) (hac : a ≤ c) (hbd : b ≤ d) : a + b ≤ c + d := by
  intro; simp; gcongr <;> apply_assumption
@[gcongr]
theorem mul_le_mul (a b c d : Exp ϖ) (hac : a ≤ c) (hbd : b ≤ d) : a * b ≤ c * d := by
  intro; simp; gcongr <;> apply_assumption

end

end Exp

structure BExpr (ϖ : Type*) where
  toFun : States ϖ → Prop
  decidable : DecidablePred toFun
def ProbExp (ϖ : Type*) := {e : Exp ϖ // e ≤ 1}

namespace ProbExp

instance instFunLike : FunLike (ProbExp ϖ) (States ϖ) ENNReal where
  coe := Subtype.val
  coe_injective' := Subtype.val_injective

@[grind =, simp] theorem coe_apply {f : Exp ϖ} {h : f ≤ 1} : instFunLike.coe ⟨f, h⟩ σ = f σ := rfl
@[grind ., simp] theorem mk_val {f : Exp ϖ} {h : f ≤ 1} : (⟨f, h⟩ : ProbExp ϖ).val = f := rfl
@[grind =, simp] theorem mk_vcoe {f : Exp ϖ} {h : f ≤ 1} :
    @DFunLike.coe _ _ _ instFunLike (Subtype.mk f h : ProbExp ϖ) = f := by rfl

end ProbExp

namespace BExpr

instance : FunLike (BExpr ϖ) (States ϖ) Prop where
  coe := BExpr.toFun
  coe_injective' := fun ⟨b, _⟩ ⟨b', _⟩ h ↦ by simp at h; subst_eqs; simp; ext; grind
instance {b : BExpr ϖ} : Decidable (b σ) := b.decidable σ

@[ext] theorem ext {a b : BExpr ϖ} (h : ∀ σ, a σ ↔ b σ) : a = b := by
  cases a; cases b;
  simp [DFunLike.coe] at h
  congr
  · ext; apply h
  · refine Function.hfunext rfl ?_; simp; grind

def not (b : BExpr ϖ) : BExpr ϖ :=
  ⟨(¬b ·), fun σ ↦ if h : b σ then .isFalse (by simp_all) else .isTrue (by simp_all)⟩
instance : Iverson (BExpr ϖ) (Exp ϖ) := ⟨fun b σ ↦ i[decide (b σ)]⟩
instance : LawfulIverson (BExpr ϖ) (Exp ϖ) := ⟨by intro b σ; simp [instIversonExp]⟩
def probOf (b : BExpr ϖ) : ProbExp ϖ :=
  ⟨i[b], by intro; simp [Iverson.iver]; split <;> simp⟩
notation "p[" b "]" => BExpr.probOf b

noncomputable def forall_ [DecidableEq ϖ] (x : ϖ) (b : BExpr ϖ) : BExpr ϖ :=
  ⟨fun σ ↦ ∀ (v : ENNReal), b σ[x ↦ v], Classical.decPred _⟩
noncomputable def exists_ [DecidableEq ϖ] (x : ϖ) (b : BExpr ϖ) : BExpr ϖ :=
  ⟨fun σ ↦ ∃ (v : ENNReal), b σ[x ↦ v], Classical.decPred _⟩

@[grind =, simp] theorem not_apply : (not b) σ = ¬b σ := by rfl

instance : HNot (BExpr α) where hnot := .not

variable {b : BExpr ϖ}

@[coe] def coe_bool : Bool → BExpr ϖ := fun b ↦ ⟨fun _ ↦ b, fun _ ↦ inferInstance⟩
instance : Coe Bool (BExpr ϖ) := ⟨coe_bool⟩

@[grind =, simp] theorem iver_apply : i[b] σ = i[b σ] := by simp [Iverson.iver]
@[grind ., simp] theorem iver_le_one : i[b] ≤ 1 := by intro σ; simp
@[simp] theorem iver_mul_le_apply {X : Exp ϖ} : i[b σ] * X σ ≤ X σ := by calc
  _ ≤ 1 * X σ := by gcongr; simp
  _ = _ := by simp
@[grind ., simp] theorem iver_mul_le : i[b] * X ≤ X := by intro; simp
@[simp] theorem mul_iver_le_apply {X : Exp ϖ} : X σ * i[b] σ ≤ X σ := by calc
  _ ≤ X σ * 1 := by gcongr; simp
  _ = _ := by simp
@[grind ., simp] theorem mul_iver_le : i[b] * X ≤ X := by intro; simp

@[grind =, simp] theorem true_iver (h : b σ = true) : i[b σ] = 1 := by simp [h]
@[grind =, simp] theorem false_iver (h : b σ = false) : i[b σ] = 0 := by simp [h]
@[grind =, simp] theorem true_not_iver (h : b σ = true) : i[b.not σ] = 0 := by simp [h]
@[grind =, simp] theorem false_not_iver (h : b σ = false) : i[b.not σ] = 1 := by simp [h]

@[grind =, simp] theorem true_probOf (h : b σ = true) : p[b] σ = 1 := by simp [probOf, h]
@[grind =, simp] theorem false_probOf (h : b σ = false) : p[b] σ = 0 := by simp [probOf, h]
@[grind =, simp] theorem true_not_probOf (h : b σ = true) : p[b.not] σ = 0 := by simp [probOf, h]
@[grind =, simp] theorem false_not_probOf (h : b σ = false) : p[b.not] σ = 1 := by simp [probOf, h]

@[grind =, simp] theorem probOf_apply (b : BExpr ϖ) : p[b] σ = i[b σ] := by simp [probOf]

instance [DecidableEq ϖ] : Substitution (BExpr ϖ) (fun (_ : ϖ) ↦ Exp ϖ) where
  subst b := fun x ↦ ⟨fun σ ↦ b (σ[x.1 ↦ x.2 σ]), fun σ ↦ by simp only; exact inferInstance⟩
theorem subst_apply [DecidableEq ϖ] {b : BExpr ϖ} : Substitution.subst b x σ = b σ[x.1 ↦ x.2 σ] :=
  rfl

noncomputable def lt (l r : Exp ϖ) : BExpr ϖ := ⟨fun σ ↦ l σ < r σ, inferInstance⟩
noncomputable def le (l r : Exp ϖ) : BExpr ϖ := ⟨fun σ ↦ l σ ≤ r σ, inferInstance⟩
noncomputable def eq (l r : Exp ϖ) : BExpr ϖ := ⟨fun σ ↦ l σ = r σ, inferInstance⟩
def and (l r : BExpr ϖ) : BExpr ϖ := ⟨fun σ ↦ l σ ∧ r σ, inferInstance⟩
def or (l r : BExpr ϖ) : BExpr ϖ := ⟨fun σ ↦ l σ ∨ r σ, inferInstance⟩
def ite (b l r : BExpr ϖ) : BExpr ϖ := ⟨fun σ ↦ if b σ then l σ else r σ, inferInstance⟩

@[grind =, simp] theorem lt_apply {l r : Exp ϖ} : lt l r σ ↔ l σ < r σ := by rfl
@[grind =, simp] theorem le_apply {l r : Exp ϖ} : le l r σ ↔ l σ ≤ r σ := by rfl
@[grind =, simp] theorem eq_apply {l r : Exp ϖ} : eq l r σ ↔ l σ = r σ := by rfl
@[grind =, simp] theorem and_apply {l r : BExpr ϖ} : and l r σ ↔ l σ ∧ r σ := by rfl
@[grind =, simp] theorem or_apply {l r : BExpr ϖ} : or l r σ ↔ l σ ∨ r σ := by rfl
@[grind =, simp] theorem ite_apply (b l r : BExpr ϖ) : ite b l r σ = if b σ then l σ else r σ := rfl

@[simp] theorem eq_subst [DecidableEq ϖ] {a b : Exp ϖ} :
    (BExpr.eq a b)[..xs] = BExpr.eq a[..xs] b[..xs] :=
  Substitution.substs_of_binary fun _ _ ↦ congrFun rfl

end BExpr

namespace ProbExp

variable (p : ProbExp ϖ) (σ : States ϖ)

@[grind =, simp] theorem add_one_apply : p σ + (1 - p σ) = 1 := add_tsub_cancel_of_le (p.prop σ)

@[grind ., simp] theorem le_one : p σ ≤ 1 := p.prop σ
@[grind ., simp] theorem val_le_one : p.val ≤ 1 := p.prop
@[grind ., simp] theorem zero_le : 0 ≤ p σ := by simp
@[grind ., simp] theorem zero_val_le : 0 ≤ p.val := by apply zero_le
@[grind =, simp] theorem lt_one_iff : ¬p σ = 1 ↔ p σ < 1 := by simp
@[grind ., simp] theorem sub_one_le_one : 1 - p σ ≤ 1 := by simp
@[grind ., simp] theorem ne_top : p σ ≠ ⊤ := by intro h; have := p.le_one σ; simp_all
@[grind ., simp] theorem top_ne : ⊤ ≠ p σ := by intro h; symm at h; simp_all
@[grind =, simp] theorem not_zero_off : ¬p σ = 0 ↔ 0 < p σ := pos_iff_ne_zero.symm

@[grind =, simp]
theorem lt_one_iff' : 1 - p σ < 1 ↔ ¬p σ = 0 :=
  ⟨fun _ _ ↦ by simp_all,
    fun _ ↦ ENNReal.sub_lt_of_sub_lt (p.le_one σ) (.inl (by simp)) (by simp_all)⟩

@[grind ., simp]
theorem top_ne_one_sub : ¬⊤ = 1 - p σ :=
  by intro h; have := h.trans_le <| p.sub_one_le_one σ; simp at this

@[grind =, simp] theorem one_le_iff : 1 ≤ p σ ↔ p σ = 1 := LE.le.ge_iff_eq (p.le_one σ)

@[grind ., simp] theorem ite_eq_zero : (if 0 < p σ then p σ * x else 0) = p σ * x :=
  by split_ifs <;> simp_all
@[grind ., simp] theorem ite_eq_one : (if p σ < 1 then (1 - p σ) * x else 0) = (1 - p σ) * x :=
  by split_ifs <;> simp_all

@[grind ., simp] theorem ite_eq_zero' : (if 0 < p σ then p σ else 0) = p σ :=
  by split_ifs <;> simp_all
@[grind ., simp] theorem ite_eq_one' : (if p σ < 1 then (1 - p σ) else 0) = 1 - p σ :=
  by split_ifs <;> simp_all

instance [DecidableEq ϖ] : Substitution (ProbExp ϖ) (fun (_ : ϖ) ↦ Exp ϖ) where
  subst b := fun x ↦ ⟨fun σ ↦ b (σ[x.1 ↦ x.2 σ]), fun σ ↦ by simp⟩

@[grind =, simp] theorem subst_apply [DecidableEq ϖ] {a : ProbExp ϖ} {x : ϖ} {A : Exp ϖ} :
    a[x ↦ A] σ = a σ[x ↦ A σ] := rfl

@[coe] def exp_coe : ProbExp ϖ → Exp ϖ := Subtype.val
instance : Coe (ProbExp ϖ) (Exp ϖ) := ⟨exp_coe⟩

@[grind =, simp] theorem exp_coe_apply : exp_coe p σ = p σ := by rfl

@[grind =, simp] theorem coe_exp_coe : ↑(exp_coe ⟨x, hx⟩) = x := by rfl

noncomputable instance : HMul (ProbExp ϖ) (Exp ϖ) (Exp ϖ) where
  hMul p x := p.val * x
noncomputable instance : HMul (Exp ϖ) (ProbExp ϖ) (Exp ϖ) where
  hMul x p := x * p.val
@[grind =, simp] theorem hMul_Exp_apply {p : ProbExp ϖ} {x : Exp ϖ} : (p * x) σ = p σ * x σ := rfl
@[grind =, simp] theorem Exp_hMul_apply {p : ProbExp ϖ} {x : Exp ϖ} : (x * p) σ = x σ * p σ := rfl

@[ext]
theorem ext {p q : ProbExp ϖ} (h : ∀ σ, p σ = q σ) : p = q := by
  cases p; cases q; congr; apply funext h

instance instOfNat0 : OfNat (ProbExp ϖ) 0 := ⟨⟨fun _ ↦ 0, by intro; simp⟩⟩
instance instOfNat1 : OfNat (ProbExp ϖ) 1 := ⟨⟨fun _ ↦ 1, by intro; simp⟩⟩

@[grind =, simp] theorem zero_apply : instOfNat0.ofNat σ = 0 := rfl
@[grind =, simp] theorem one_apply : instOfNat1.ofNat σ = 1 := rfl

section

noncomputable instance : Mul (ProbExp ϖ) where
  mul a b := ⟨fun σ ↦ a σ * b σ, by intro σ; simp; refine Left.mul_le_one ?_ ?_ <;> simp⟩

noncomputable instance : Add (ProbExp ϖ) where
  add a b := ⟨fun σ ↦ (a σ + b σ) ⊓ 1, by intro σ; simp⟩

noncomputable instance : Sub (ProbExp ϖ) where
  sub a b := ⟨fun σ ↦ a σ - b σ, by intro σ; simp; exact le_add_right (by simp)⟩

variable {a b : ProbExp ϖ}

@[grind =, simp] theorem add_apply : (a + b) σ = (a σ + b σ) ⊓ 1 := by rfl
@[grind =, simp] theorem mul_apply : (a * b) σ = a σ * b σ := by rfl
@[grind =, simp] theorem sub_apply : (a - b) σ = a σ - b σ := by rfl

variable [DecidableEq ϖ] {x : ϖ} {A : Exp ϖ}

@[grind =, simp] theorem add_subst : (a + b)[x ↦ A] = a[x ↦ A] + b[x ↦ A] := by rfl
@[grind =, simp] theorem mul_subst : (a * b)[x ↦ A] = a[x ↦ A] * b[x ↦ A] := by rfl
@[grind =, simp] theorem sub_subst : (a - b)[x ↦ A] = a[x ↦ A] - b[x ↦ A] := by rfl

@[grind =, simp] theorem zero_subst : (0 : ProbExp ϖ)[x ↦ A] = 0 := by rfl
@[grind =, simp] theorem one_subst : (1 : ProbExp ϖ)[x ↦ A] = 1 := by rfl

end

noncomputable def pick (x y : Exp ϖ) : Exp ϖ := p * x + (1 - p) * y
noncomputable def pick' (x y : Exp ϖ →o Exp ϖ) : Exp ϖ →o Exp ϖ :=
  ⟨fun X ↦ p * x X + (1 - p) * y X, by intro a b hab; simp_all; gcongr⟩
noncomputable def pickProb (x y : ProbExp ϖ) : ProbExp ϖ := p * x + (1 - p) * y

@[grind =, simp] theorem pick'_apply : p.pick' x y X = p.pick (x X) (y X) := rfl
@[grind =, simp] theorem pick'_apply2 : p.pick' x y X σ = p.pick (x X) (y X) σ := rfl

@[grind =, simp]
theorem pick_true {x y : Exp ϖ} (h : b σ) : p[b].pick x y σ = x σ := by
  simp [h, pick, BExpr.probOf]
@[grind =, simp]
theorem pick_false {x y : Exp ϖ} (h : ¬b σ) : p[b].pick x y σ = y σ := by
  simp [h, pick, BExpr.probOf]

@[simp, gcongr]
theorem pick_le (h₁ : x ≤ z) (h₂ : y ≤ w) : p.pick x y ≤ p.pick z w := by
  intro; simp [pick]; gcongr <;> apply_assumption
@[grind ., simp]
theorem pick_le' (h₁ : x ≤ z) (h₂ : y ≤ w) : p.pick x y σ ≤ p.pick z w σ := p.pick_le h₁ h₂ σ

@[grind =, simp]
theorem pickProb_coe : exp_coe (p.pickProb x y) = p.pick x y := by
  ext σ; simp [pickProb, pick]
  have := p.pick_le x.prop y.prop σ
  simp [pick] at this
  exact this

@[grind =, simp]
theorem pickProb_DFunLike_coe : DFunLike.coe (p.pickProb x y) = p.pick x y := by
  rw [← pickProb_coe]; rfl

@[grind =, simp]
theorem pickProb_apply : (p.pickProb x y) σ = p.pick x y σ := by
  simp [pickProb, pick]
  have := p.pick_le x.prop y.prop σ
  simp [pick] at this
  exact this

@[grind =, simp] theorem pick_same : p.pick x x = x := by ext σ; simp [pick, ← add_mul]

instance instLE : LE (ProbExp ϖ) where
  le a b := ∀ x, a x ≤ b x

@[grind =, simp] theorem coe_le {f g : Exp ϖ} {hf : f ≤ 1} {hg : g ≤ 1} :
    instLE.le (⟨f, hf⟩) ⟨g, hg⟩ ↔ f ≤ g := by rfl

instance : PartialOrder (ProbExp ϖ) where
  le_refl a σ := by rfl
  le_trans a b c hab hbc σ := by exact (hab σ).trans (hbc σ)
  le_antisymm a b hab hba := by ext σ; exact (hab σ).antisymm (hba σ)

/-- The expression `1/n` where is defined to be `1` if `n ≤ 1`. -/
noncomputable def inv (n : Exp ϖ) : ProbExp ϖ :=
  ⟨fun σ ↦ if h : n σ ≤ 1 then 1 else (n σ)⁻¹, fun _ ↦ by
    simp
    split_ifs with h
    · rfl
    · simp [le_of_not_ge h]⟩

@[grind =, simp] theorem inv_apply : inv n σ = if n σ ≤ 1 then (1 : ENNReal) else (n σ)⁻¹ := by rfl

instance : Bot (ProbExp ϖ) := ⟨0⟩
instance : Top (ProbExp ϖ) := ⟨1⟩

@[simp] theorem bot_eq_0 : (instBot (ϖ:=ϖ)).bot = 0 := by rfl
@[simp] theorem top_eq_1 : (instTop (ϖ:=ϖ)).top = 1 := by rfl

open scoped Classical in
noncomputable instance : CompleteLattice (ProbExp ϖ) where
  sup := fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ ⟨a ⊔ b, by simp; grind⟩
  le_sup_left a b σ := by split; split; simp
  le_sup_right a b σ := by split; split; simp
  sup_le := fun ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ _ _ ↦ by simp_all
  inf := fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ ⟨a ⊓ b, by intro σ; simp; left; exact ha σ⟩
  inf_le_left a b σ := by split; split; simp
  inf_le_right a b σ := by split; split; simp
  le_inf := fun ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ _ _ ↦ by simp_all
  sSup S := ⟨⨆ x ∈ S, x.val, by simp⟩
  le_sSup := by intro S ⟨a, ha⟩ ha'; simp; apply le_iSup₂_of_le ⟨a, ha⟩ ha'; rfl
  sSup_le := by intro S ⟨a, ha⟩ ha'; simp_all; apply ha'
  sInf S := ⟨if S = ∅ then 1 else ⨅ x ∈ S, x.val, by
    split_ifs with h
    · simp
    · apply iInf_le_iff.mpr
      simp
      intro b hb
      replace h : S.Nonempty := by exact Set.nonempty_iff_ne_empty.mpr h
      obtain ⟨⟨q, hq'⟩, hq⟩ := h
      specialize hb ⟨q, hq'⟩ hq
      simp_all
      apply hb.trans hq'⟩
  sInf_le S a ha := by
    have : S ≠ ∅ := ne_of_mem_of_not_mem' ha id
    simp [this]
    obtain ⟨a, ha'⟩ := a
    simp_all
    apply iInf₂_le_of_le ⟨a, ha'⟩ ha; rfl
  le_sInf S a ha := by
    obtain ⟨a, ha'⟩ := a
    split_ifs
    · simp_all
    · simp_all
      apply ha
  le_top := by simp; intro; apply le_one
  bot_le := by simp; intro; apply zero_le

@[simp]
theorem iSup_apply (f : ι → ProbExp ϖ) : (⨆ i, f i) x = ⨆ i, f i x := by
  rw [iSup]
  simp [instCompleteLattice, CompleteLattice.toConditionallyCompleteLattice]
  apply le_antisymm
  · simp
    intro i
    apply le_iSup_of_le i
    rfl
  · simp
    intro i
    apply le_iSup₂_of_le (f i) i
    simp; rfl
@[simp]
theorem iInf_apply [Nonempty ι] (f : ι → ProbExp ϖ) : (⨅ i, f i) x = ⨅ i, f i x := by
  rw [iInf]
  simp [instCompleteLattice, CompleteLattice.toConditionallyCompleteLattice]
  apply le_antisymm
  · simp; intro i; apply iInf₂_le_of_le (f i) i; simp; rfl
  · simp_all; intro i; apply iInf_le_of_le i; rfl
@[grind =, simp]
theorem sSup_apply (S : Set (ProbExp ϖ)) : sSup S x = ⨆ i : S, i.val x := by
  simp [instCompleteLattice, CompleteLattice.toConditionallyCompleteLattice]
  exact iSup_subtype'
@[grind =, simp]
theorem sInf_apply (S : Set (ProbExp ϖ)) [Nonempty S] : sInf S x = ⨅ i : S, i.val x := by
  simp [instCompleteLattice, CompleteLattice.toConditionallyCompleteLattice]
  split_ifs
  · simp_all
  · simp_all
    exact iInf_subtype'
@[grind =, simp] theorem sup_apply {f g : ProbExp ϖ} : (f ⊔ g) σ = f σ ⊔ g σ := rfl
@[grind =, simp] theorem inf_apply {f g : ProbExp ϖ} : (f ⊓ g) σ = f σ ⊓ g σ := rfl
@[grind =, simp] theorem sup_coe_apply {f g : ProbExp ϖ} : (f ⊔ g).val σ = f σ ⊔ g σ := rfl
@[grind =, simp] theorem inf_coe_apply {f g : ProbExp ϖ} : (f ⊓ g).val σ = f σ ⊓ g σ := rfl
@[grind =, simp] theorem max_apply {f g : ProbExp ϖ} : (max f g) σ = max (f σ) (g σ) := rfl
@[grind =, simp] theorem min_apply {f g : ProbExp ϖ} : (min f g) σ = min (f σ) (g σ) := rfl
@[grind =, simp] theorem max_coe_apply {f g : ProbExp ϖ} : (max f g).val σ = max (f σ) (g σ) := rfl
@[grind =, simp] theorem min_coe_apply {f g : ProbExp ϖ} : (min f g).val σ = min (f σ) (g σ) := rfl

@[grind =, simp] theorem one_mul : (1 : ProbExp ϖ) * p = p := by ext; simp
@[grind =, simp] theorem zero_mul : (0 : ProbExp ϖ) * p = 0 := by ext; simp

@[grind =, simp] theorem mul_one : p * (1 : ProbExp ϖ) = p := by ext; simp
@[grind =, simp] theorem mul_zero : p * (0 : ProbExp ϖ) = 0 := by ext; simp

@[grind =, simp] theorem one_add : 1 + p = 1 := by ext; simp
@[grind =, simp] theorem add_one : p + 1 = 1 := by ext; simp
@[grind =, simp] theorem zero_add : 0 + p = p := by ext; simp
@[grind =, simp] theorem add_zero : p + 0 = p := by ext; simp
@[grind =, simp] theorem sub_one : p - 1 = 0 := by ext σ; exact tsub_eq_zero_of_le (le_one p σ)
@[grind =, simp] theorem zero_sub : 0 - p = 0 := by ext; simp
@[grind =, simp] theorem sub_zero : p - 0 = p := by ext; simp

@[grind =, simp] theorem coe_one : exp_coe (ϖ:=ϖ) 1 = 1 := by rfl
@[grind =, simp] theorem coe_zero : exp_coe (ϖ:=ϖ) 0 = 0 := by rfl

@[gcongr]
theorem mul_le_mul (a b c d : ProbExp ϖ) (hac : a ≤ c) (hbd : b ≤ d) : a * b ≤ c * d := by
  intro; simp; gcongr <;> apply_assumption

@[gcongr]
theorem add_le_add (a b c d : ProbExp ϖ) (hac : a ≤ c) (hbd : b ≤ d) : a + b ≤ c + d := by
  intro; simp only [add_apply]; gcongr <;> apply_assumption

@[gcongr]
theorem sub_le_sub (a b c d : ProbExp ϖ) (hac : a ≤ c) (hdb : d ≤ b) : a - b ≤ c - d := by
  intro; simp only [sub_apply]; gcongr <;> apply_assumption

@[simp, gcongr]
theorem pickProb_le (h₁ : x ≤ z) (h₂ : y ≤ w) : p.pickProb x y ≤ p.pickProb z w := by
  intro; simp only [pickProb, add_apply, mul_apply, sub_apply, one_apply]
  gcongr <;> apply_assumption
@[grind ., simp]
theorem pickProb_le' (h₁ : x ≤ z) (h₂ : y ≤ w) : p.pickProb x y σ ≤ p.pickProb z w σ :=
  p.pickProb_le h₁ h₂ σ

@[grind ., simp]
theorem pick_of_prob_le_one {x y : ProbExp ϖ} : p.pick x y σ ≤ 1 := by
  have hx : x ≤ 1 := x.prop; have hy : y ≤ 1 := y.prop
  have := p.pickProb_le hx hy σ; simpa

@[grind =, simp] theorem coe_inv {X : Exp ϖ} :
    exp_coe (inv X) = X⁻¹ ⊓ 1 := by
      ext σ
      simp [inv]
      split_ifs with h
      · simp_all
      · simp_all
        exact h.le

variable [DecidableEq ϖ]

@[grind =, simp] theorem exp_coe_subst {X : ProbExp ϖ} {x : ϖ} {e : Exp ϖ} :
    (exp_coe X)[x ↦ e] = (exp_coe X[x ↦ e]) := by rfl
-- TODO
-- @[grind =, simp] theorem mk_subst {x : ϖ} {e : Exp ϖ} :
--     (instSubstExpOfDecidableEq.subst ⟨q, hp⟩ x e) = ⟨q[x ↦ e], by
--       intro σ; simp; apply hp⟩ := by rfl
@[grind =, simp] theorem inv_subst {X : Exp ϖ} {x : ϖ} {e : Exp ϖ} :
    (inv X)[x ↦ e] = inv X[x ↦ e] := by rfl

end ProbExp

end pGCL

open pGCL

namespace OrderHom

variable {α β : Type*} [Preorder α] [Preorder β] [Add β] [AddLeftMono β] [AddRightMono β]

instance : AddLeftMono (States ϖ → ENNReal) where
  elim a _ _ hbc := fun σ ↦ add_le_add_right (hbc σ) (a σ)
instance : AddRightMono (States ϖ → ENNReal) where
  elim a _ _ hbc := fun σ ↦ add_le_add_left (hbc σ) (a σ)

instance instAdd : Add (α →o β) where
  add a b := ⟨fun x ↦ a x + b x, fun x y h ↦ by simp; gcongr⟩
@[simp] theorem add_apply (f g : α →o β) : (f + g) x = f x + g x := by rfl
@[simp] theorem add_apply' (f g : α →o Exp ϖ) : (f + g) x = f x + g x := by rfl
@[simp] theorem add_apply2 (f g : α →o Exp ϖ) : (f + g) x y = f x y + g x y := by rfl
@[simp] theorem add_apply2' (f g : α →o States ϖ → ENNReal) : (f + g) x y = f x y + g x y := by rfl

instance [OfNat β n] : OfNat (α →o β) n := ⟨fun _ ↦ OfNat.ofNat n, by intro; simp⟩
omit [Add β] [AddLeftMono β] [AddRightMono β] in
@[grind =, simp]
theorem ofNat_apply [OfNat β n] : (OfNat.ofNat n : α →o β) a = OfNat.ofNat n := by rfl

instance {β : Type*} [Preorder β] [AddZeroClass β] [AddLeftMono β] [AddRightMono β] :
    AddZeroClass (α →o β) where
  zero_add f := by ext; simp; rw [ofNat_apply]; simp
  add_zero f := by ext; simp; rw [ofNat_apply]; simp

instance {α β : Type*} [Preorder β] [Add β] [i : AddRightMono β] : AddRightMono (α → β) where
  elim a b c h i := by simp [Function.swap]; gcongr; apply h
instance {α β : Type*} [Preorder β] [Add β] [i : AddLeftMono β] : AddLeftMono (α → β) where
  elim a b c h i := by simp only [Pi.add_apply]; gcongr; apply h

variable {ι : Type*}

omit [Add β] [AddLeftMono β] [AddRightMono β] in
@[simp, grind =]
theorem mk_apply {f} {h} {b : ι} :
    ({toFun := f, monotone' := h} : α →o (ι → β)) a b = f a b := by rfl
omit [Add β] [AddLeftMono β] [AddRightMono β] in
@[simp, grind =]
theorem mk_apply' {f} {h} {b : ι} :
    DFunLike.coe ({toFun := f, monotone' := h} : α →o (ι → β)) a b = f a b := by rfl
omit [Add β] [AddLeftMono β] [AddRightMono β] in
@[simp, grind =]
theorem comp_apply' {ι : Type*} {γ : Type*} [Preorder γ] {f : β →o (ι → γ)} {g : α →o β} {b : ι} :
    (OrderHom.comp f g) a b = f (g a) b := rfl

end OrderHom
