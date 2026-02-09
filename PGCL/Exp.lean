import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations
import Mathlib.Order.FixedPoints
import Mathlib.Order.OmegaCompletePartialOrder
import MDP.Optimization
import STDX.Subst

/-! # Custom operators -/

@[notation_class]
class Validate (α : Type*) where
  /-- Validate `▵` -/
  validate : α → α

@[notation_class]
class Covalidate (α : Type*) where
  /-- Co-validate `▿` -/
  covalidate : α → α

export Validate (validate)
export Covalidate (covalidate)

/-- Heyting co-implication `↜` -/
notation:60 x:61 " ↜ " y:60 => y \ x
@[inherit_doc] prefix:72 "~ " => compl
@[inherit_doc] prefix:72 "▵ " => validate
@[inherit_doc] prefix:72 "▿ " => covalidate

instance {α : Type*} [HNot α] : Validate α := ⟨fun x ↦ ￢￢x⟩
instance {α : Type*} [Compl α] : Covalidate α := ⟨fun x ↦ xᶜᶜ⟩

noncomputable instance {α β : Type*} [SDiff β] : SDiff (α → β) := inferInstance

noncomputable instance : SDiff ENNReal := inferInstance
example {φ : ENNReal} : φᶜ = φ ⇨ 0 := by simp [compl, himp]
example {φ : ι → ENNReal} : φᶜ = φ ⇨ 0 := by simp [compl, himp]
example {φ : ENNReal} : ￢φ = φ ↜ ⊤ := by simp [hnot]
example {φ : ι → ENNReal} : ￢φ = φ ↜ ⊤ := by simp [hnot]
example {φ : ENNReal} : ψ \ φ = φ ↜ ψ := by simp [sdiff]

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

@[grind .] theorem iver_neg : i[¬b] = 1 - i[b] := by simp [iver]; grind
@[grind .] theorem iver_not : i[!b] = 1 - i[b] := by simp [iver]; grind

end Iverson

export Iverson (iver)

section

variable {α β ι : Type*} {γ : ι → Type*} [Substitution α γ]

instance Pi.instSubstitution : Substitution (α → β) fun (a : ι) ↦ α → γ a where
  subst f := fun ⟨i, x⟩ σ ↦ f σ[i ↦ x σ]

@[grind =, simp]
theorem Pi.substs_cons (f : α → β) (x₀ : ((a : ι) × (α → γ a))) (xs : List ((a : ι) × (α → γ a))) :
  f[..x₀ :: xs] σ = f[..xs] σ[x₀.1 ↦ x₀.2 σ] := by rfl

end

namespace Pi

noncomputable instance instIverson {α : Type*} : Iverson (α → Prop) (α → ENNReal) where
  iver v := fun σ ↦ i[v σ]
noncomputable instance instIversonBool {α : Type*} : Iverson (α → Bool) (α → ENNReal) where
  iver v := fun σ ↦ i[v σ]
instance instLawfulIverson {α : Type*} : LawfulIverson (α → Prop) (α → ENNReal) where
  iver_le_one b := by intro σ; simp [instIverson]
instance instLawfulIversonBool {α : Type*} : LawfulIverson (α → Bool) (α → ENNReal) where
  iver_le_one b := by intro σ; simp [instIversonBool]
@[grind =, simp] theorem iver_apply {α : Type*} (f : α → Prop) (a : α) :
    i[f] a = i[f a] := rfl
@[grind =, simp] theorem iver_subst {α ι : Type*} {γ : ι → Type*}
    [Substitution α γ]
    (f : α → Prop) (x : ι) (y : α → γ x) : i[f][x ↦ y] = i[f[x ↦ y]] := by
  rfl
@[grind =, simp] theorem iver_bool_apply {α : Type*} (f : α → Bool) (a : α) :
    i[f] a = i[f a] := rfl
@[grind =, simp] theorem iver_bool_subst {α ι : Type*} {γ : ι → Type*}
    [Substitution α γ]
    (f : α → Bool) (x : ι) (y : α → γ x) : i[f][x ↦ y] = i[f[x ↦ y]] := by
  rfl

end Pi


/-! # Expressions & States -/

namespace pGCL

notation "Γ[" ϖ "]" => ϖ → Type*
def States {𝒱 : Type*} (Γ : Γ[𝒱]) := (s : 𝒱) → Γ s

variable {𝒱 : Type*} {ϖ : Γ[𝒱]}

notation "𝔼[" ϖ "," α "]" => States ϖ → α

instance States.instSubstitution [DecidableEq 𝒱] : Substitution (States ϖ) ϖ where
  subst σ := fun ⟨v, t⟩ α ↦ if h : v = α then cast (congrArg ϖ h) t else σ α

@[ext] theorem States.ext {σ₁ σ₂ : States ϖ} (h : ∀ v, σ₁ v = σ₂ v) : σ₁ = σ₂ := _root_.funext h

@[grind =, simp] theorem States.subst_apply [DecidableEq 𝒱] {σ : States ϖ} :
    σ[x ↦ v] y = if h : x = y then cast (congrArg ϖ h) v else σ y := rfl

namespace Exp

variable {a b : 𝔼[ϖ, α]}

instance {ι : Type*} [Add α] [LE α] [AddLeftMono α] : AddLeftMono (ι → α) := ⟨fun a b c h σ ↦ by
  simp only [Pi.add_apply]; gcongr; apply h⟩
instance {ι : Type*} [Add α] [LE α] [AddRightMono α] : AddRightMono (ι → α) := ⟨fun a b c h σ ↦ by
  simp only [Pi.add_apply, Function.swap]; gcongr; apply h⟩

variable [DecidableEq 𝒱] {v : 𝒱} {e : 𝔼[ϖ, α]}

@[simp] theorem add_subst [Add α] :
    (a + b)[..xs] = a[..xs] + b[..xs] := Substitution.substs_of_binary fun _ _ ↦ congrFun rfl
@[simp] theorem sub_subst [Sub α] :
    (a - b)[..xs] = a[..xs] - b[..xs] := Substitution.substs_of_binary fun _ _ ↦ congrFun rfl
@[simp] theorem mul_subst [Mul α] :
    (a * b)[..xs] = a[..xs] * b[..xs] := Substitution.substs_of_binary fun _ _ ↦ congrFun rfl
@[simp] theorem div_subst [Div α] :
    (a / b)[..xs] = a[..xs] / b[..xs] := Substitution.substs_of_binary fun _ _ ↦ congrFun rfl
@[simp] theorem max_subst [Max α] :
    (a ⊔ b)[..xs] = a[..xs] ⊔ b[..xs] := Substitution.substs_of_binary fun _ _ ↦ congrFun rfl
@[simp] theorem min_subst [Min α] :
    (a ⊓ b)[..xs] = a[..xs] ⊓ b[..xs] := Substitution.substs_of_binary fun _ _ ↦ congrFun rfl
@[simp] theorem himp_subst [HImp α] :
    (a ⇨ b)[..xs] = a[..xs] ⇨ b[..xs] := Substitution.substs_of_binary fun _ _ ↦ congrFun rfl
@[simp] theorem sdiff_subst [SDiff α] :
    (a ↜ b)[..xs] = a[..xs] ↜ b[..xs] := Substitution.substs_of_binary fun _ _ ↦ congrFun rfl

omit [DecidableEq 𝒱]

@[grind =, simp] theorem validate_apply [HNot α] {φ : 𝔼[ϖ, α]} :
    (▵ φ) σ = ▵ φ σ := rfl
@[grind =, simp] theorem covalidate_apply [Compl α] {φ : 𝔼[ϖ, α]} :
    (▿ φ) σ = ▿ φ σ := rfl

@[grind =, simp]
theorem subst_apply [DecidableEq 𝒱] (e : 𝔼[ϖ, α]) (x : 𝒱) (A : 𝔼[ϖ, ϖ x]) :
    e[x ↦ A] σ = e (σ[x ↦ A σ]) := rfl
@[grind =, simp]
theorem subst₂_apply [DecidableEq 𝒱] (e : 𝔼[ϖ, α]) (x : 𝒱) (A : 𝔼[ϖ, ϖ x]) :
    e[x ↦ A, y ↦ B] σ = e (σ[y ↦ B σ[x ↦ A σ], x ↦ A σ]) := by
  simp_all [Substitution.substs_cons, Substitution.subst]

@[gcongr]
theorem add_le_add [Add α] [Preorder α] [AddLeftMono α] [AddRightMono α] (a b c d : 𝔼[ϖ, α])
    (hac : a ≤ c) (hbd : b ≤ d) : a + b ≤ c + d := by
  intro; simp; gcongr <;> apply_assumption
@[gcongr]
theorem mul_le_mul [Mul α] [Preorder α] [MulLeftMono α] [MulRightMono α] (a b c d : 𝔼[ϖ, α])
    (hac : a ≤ c) (hbd : b ≤ d) : a * b ≤ c * d := by
  intro; simp; gcongr <;> apply_assumption

end Exp

abbrev BExpr (ϖ : Γ[𝒱]) := 𝔼[ϖ, Prop]

namespace BExpr

noncomputable def forall_ [DecidableEq 𝒱] (x : 𝒱) (b : BExpr ϖ) : BExpr ϖ :=
  fun σ ↦ ∀ (v : ϖ x), b σ[x ↦ v]
noncomputable def exists_ [DecidableEq 𝒱] (x : 𝒱) (b : BExpr ϖ) : BExpr ϖ :=
  fun σ ↦ ∃ (v : ϖ x), b σ[x ↦ v]

instance : HNot (BExpr α) where hnot := compl

variable {b : BExpr ϖ}

@[coe] def coe_prop : Prop → BExpr ϖ := fun b ↦ fun _ ↦ b
instance : Coe Prop 𝔼[ϖ, Prop] := ⟨coe_prop⟩
@[grind =, simp] theorem coe_prop_apply {b} : coe_prop (ϖ:=ϖ) b σ = b := by rfl

@[simp] theorem iver_mul_le_apply {X : 𝔼[ϖ, ENNReal]} : i[b σ] * X σ ≤ X σ := by calc
  _ ≤ 1 * X σ := by gcongr; simp
  _ = _ := by simp
@[grind ., simp] theorem iver_mul_le : i[b] * X ≤ X := by intro; simp
@[simp] theorem mul_iver_le_apply {X : 𝔼[ϖ, ENNReal]} : X σ * i[b σ] ≤ X σ := by calc
  _ ≤ X σ * 1 := by gcongr; simp
  _ = _ := by simp
@[grind ., simp] theorem mul_iver_le : X * i[b] ≤ X := by intro; simp

variable [PartialOrder α]

noncomputable def lt (l r : 𝔼[ϖ, α]) : BExpr ϖ :=
  fun σ ↦ l σ < r σ
noncomputable def le (l r : 𝔼[ϖ, α]) : BExpr ϖ :=
  fun σ ↦ l σ ≤ r σ
noncomputable def eq (l r : 𝔼[ϖ, α]) : BExpr ϖ :=
  fun σ ↦ l σ = r σ
def and (l r : BExpr ϖ) : BExpr ϖ := fun σ ↦ l σ ∧ r σ
def or (l r : BExpr ϖ) : BExpr ϖ := fun σ ↦ l σ ∨ r σ
noncomputable def ite (b l r : BExpr ϖ) : BExpr ϖ :=
  letI := Classical.decPred b
  fun σ ↦ if (b σ) then l σ else r σ

@[grind =, simp] theorem lt_apply {l r : 𝔼[ϖ, α]} : lt l r σ ↔ l σ < r σ := by rfl
@[grind =, simp] theorem le_apply {l r : 𝔼[ϖ, α]} : le l r σ ↔ l σ ≤ r σ := by rfl
omit [PartialOrder α] in
@[grind =, simp] theorem eq_apply {l r : 𝔼[ϖ, α]} : eq l r σ ↔ l σ = r σ := by rfl
@[grind =, simp] theorem and_apply {l r : BExpr ϖ} : and l r σ ↔ l σ ∧ r σ := by rfl
@[grind =, simp] theorem or_apply {l r : BExpr ϖ} : or l r σ ↔ l σ ∨ r σ := by rfl
open scoped Classical in
@[grind =, simp] theorem ite_apply (b l r : BExpr ϖ) : ite b l r σ = if b σ then l σ else r σ := rfl

omit [PartialOrder α] in
@[simp] theorem eq_subst [DecidableEq 𝒱] {a b : 𝔼[ϖ, α]} :
    (BExpr.eq a b)[..xs] = BExpr.eq a[..xs] b[..xs] :=
  Substitution.substs_of_binary fun _ _ ↦ congrFun rfl

end BExpr

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
@[simp] theorem add_apply2' (f g : α →o States ϖ → ENNReal) : (f + g) x y = f x y + g x y := by rfl

instance [OfNat β n] : OfNat (α →o β) n := ⟨fun _ ↦ OfNat.ofNat n, by intro; simp⟩
omit [Add β] [AddLeftMono β] [AddRightMono β] in
@[simp]
theorem ofNat_apply [OfNat β n] : (ofNat(n) : α →o β) a = ofNat(n) := by rfl

instance {β : Type*} [Preorder β] [AddZeroClass β] [AddLeftMono β] [AddRightMono β] :
    AddZeroClass (α →o β) where
  zero_add f := by ext; simp
  add_zero f := by ext; simp

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
