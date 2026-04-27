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

theorem ENNReal.hnot_def {a : ENNReal} : ￢a = if a = ⊤ then 0 else ⊤ := by
  simp [hnot]; rfl
theorem ENNReal.compl_def {a : ENNReal} : aᶜ = if a = 0 then ⊤ else 0 := by
  simp [compl]; rfl
theorem ENNReal.himp_def {a b : ENNReal} : (a ⇨ b) = if a ≤ b then ⊤ else b := by
  simp [himp]; rfl
theorem ENNReal.sdiff_def {a b : ENNReal} : (a \ b) = if a ≤ b then 0 else a := by
  simp [sdiff]; rfl

theorem ENNReal.covalidate_sdiff {a b : ENNReal} : ▿ (a \ b) = if a ≤ b then 0 else ⊤ := by
  simp [covalidate, sdiff_def, compl_def]
  split_ifs with h₁ h₂ h₃ <;> try grind [zero_ne_top, _root_.not_lt_zero]

theorem ENNReal.le_covalidate_sdiff {a b : ENNReal} : x ≤ ▿ (a \ b) ↔ a ≤ b → x = 0 := by
  simp [ENNReal.covalidate_sdiff]
  split_ifs <;> simp_all
theorem ENNReal.le_covalidate_sdiff_of_lt {a b : ENNReal} (h : b < a) : x ≤ ▿ (a \ b) := by
  simp [ENNReal.le_covalidate_sdiff, h]
theorem ENNReal.validate_himp_le_of_lt {a b : ENNReal} (h : b < a) : ▵ (a ⇨ b) ≤ x := by
  simp [validate, himp_def, h, hnot_def, LT.lt.ne_top h]

@[grind =, simp]
theorem ENNReal.himp_zero_le (x y : ENNReal) : x ⇨ 0 ≤ y ↔ (x = 0 → y = ⊤) := by
  simp only [himp_def]; grind [zero_le, nonpos_iff_eq_zero]
@[grind =, simp]
theorem ENNReal.himp_zero_eq_zero (x : ENNReal) : x ⇨ 0 = 0 ↔ (¬x = 0) := by
  suffices x ⇨ 0 ≤ 0 ↔ (¬x = 0) by simpa
  simp only [himp_zero_le, zero_ne_top, imp_false]
@[grind =, simp]
theorem ENNReal.sdiff_zero_eq_zero (x y : ENNReal) : x \ y = 0 ↔ x ≤ y := by
  simp only [sdiff_def]; constructor <;> grind [zero_le]

@[grind =, simp]
theorem ENNReal.max_sdiff (x y : ENNReal) : max x (⊤ ↜ y) = x := by simp
@[grind =, simp]
theorem ENNReal.lt_himp (x y z : ENNReal) (hx : x < ⊤) : x < y ⇨ z ↔ (z < y → x < z) := by
  simp_all [himp_def]; grind
@[grind =, simp]
theorem ENNReal.zero_himp (x : ENNReal) : 0 ⇨ x = ⊤ := by
  simp_all [ENNReal.himp_def]

noncomputable instance : SDiff ENNReal := inferInstance
example {φ ψ : ENNReal} : φ ⇨ ψ = if φ ≤ ψ then ⊤ else ψ := by simp [ENNReal.himp_def]
example {φ ψ : ENNReal} : φ ↜ ψ = (if ψ ≤ φ then 0 else ψ) := by simp [ENNReal.sdiff_def]
example {φ : ENNReal} : φᶜ = φ ⇨ 0 := by simp [ENNReal.compl_def, ENNReal.himp_def]
example {φ : ι → ENNReal} : φᶜ = φ ⇨ 0 := by ext; simp [ENNReal.compl_def, ENNReal.himp_def]
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
@[grind =, simp] theorem iver_prop_apply {α : Type*} {f : α → Prop} {σ : α} : i[f] σ = i[f σ] := rfl
@[grind =, simp] theorem iver_bool_apply {α : Type*} {f : α → Bool} {σ : α} : i[f] σ = i[f σ] := rfl
instance instLawfulIverson {α : Type*} : LawfulIverson (α → Prop) (α → ENNReal) where
  iver_le_one b := by intro σ; simp
instance instLawfulIversonBool {α : Type*} : LawfulIverson (α → Bool) (α → ENNReal) where
  iver_le_one b := by intro σ; simp
@[grind =, simp] theorem iver_subst {α ι : Type*} {γ : ι → Type*}
    [Substitution α γ]
    (f : α → Prop) (x : ι) (y : α → γ x) : i[f][x ↦ y] = i[f[x ↦ y]] := by
  rfl
@[grind =, simp] theorem iver_bool_subst {α ι : Type*} {γ : ι → Type*}
    [Substitution α γ]
    (f : α → Bool) (x : ι) (y : α → γ x) : i[f][x ↦ y] = i[f[x ↦ y]] := by
  rfl

variable {α : Type*}
@[simp] theorem iver_True : i[fun (_ : α) ↦ True] = 1 := by ext; simp
@[simp] theorem iver_True_compl : i[(fun (_ : α) ↦ True)ᶜ] = 0 := by ext; simp
@[simp] theorem iver_False : i[fun (_ : α) ↦ False] = 0 := by ext; simp
@[simp] theorem iver_False_compl : i[(fun (_ : α) ↦ False)ᶜ] = 1 := by ext; simp

@[grind =_, simp] theorem iver_bool_eq_true {b : Bool} : i[b = true] = i[b] := by simp [iver]
@[simp] theorem iver_bool_eq_false {b : Bool} : i[b = false] = i[¬b] := by simp [iver]

end Pi

@[simp]
theorem ENNReal.iver_eq_zero_himp_le (x y z : ENNReal) (hz : z ≠ ⊤) :
    (i[x = 0] : ENNReal) * (⊤ : ENNReal) ⇨ y ≤ z ↔ x = 0 ∧ y ≤ z := by
  simp [himp_def]
  if x = 0 then
    simp_all only [Iverson.iver_True]
    grind
  else
    simp_all only [Iverson.iver_False]
    grind [zero_le]


/-! # Expressions & State -/

namespace pGCL

notation  "Γ[" Γ "]" => Γ → Type*
def State {𝒱 : Type*} (Γ : Γ[𝒱]) := (s : 𝒱) → Γ s
variable {𝒱 : Type*} {Γ : Γ[𝒱]}
notation "𝔼[" Γ "," α "]" => State Γ → α

instance State.instSubstitution [DecidableEq 𝒱] : Substitution (State Γ) Γ where
  subst σ := fun ⟨v, t⟩ α ↦ if h : v = α then cast (congrArg Γ h) t else σ α

@[ext] theorem State.ext {σ₁ σ₂ : State Γ} (h : ∀ v, σ₁ v = σ₂ v) : σ₁ = σ₂ := _root_.funext h

@[grind =, simp] theorem State.subst_apply [DecidableEq 𝒱] {σ : State Γ} :
    σ[x ↦ v] y = if h : x = y then cast (congrArg Γ h) v else σ y := rfl

namespace Exp

variable {a b : 𝔼[Γ, α]}

instance {ι : Type*} [Add α] [LE α] [AddLeftMono α] : AddLeftMono (ι → α) := ⟨fun a b c h σ ↦ by
  simp only [Pi.add_apply]; gcongr; apply h⟩
instance {ι : Type*} [Add α] [LE α] [AddRightMono α] : AddRightMono (ι → α) := ⟨fun a b c h σ ↦ by
  simp only [Pi.add_apply, Function.swap]; gcongr; apply h⟩

variable [DecidableEq 𝒱] {v : 𝒱} {e : 𝔼[Γ, α]}

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

@[grind =, simp] theorem validate_apply [HNot α] {φ : 𝔼[Γ, α]} :
    (▵ φ) σ = ▵ φ σ := rfl
@[grind =, simp] theorem covalidate_apply [Compl α] {φ : 𝔼[Γ, α]} :
    (▿ φ) σ = ▿ φ σ := rfl

@[grind =, simp]
theorem subst_apply [DecidableEq 𝒱] (e : 𝔼[Γ, α]) (x : 𝒱) (A : 𝔼[Γ, Γ x]) :
    e[x ↦ A] σ = e (σ[x ↦ A σ]) := rfl
@[grind =, simp]
theorem subst₂_apply [DecidableEq 𝒱] (e : 𝔼[Γ, α]) (x : 𝒱) (A : 𝔼[Γ, Γ x]) :
    e[x ↦ A, y ↦ B] σ = e (σ[y ↦ B σ[x ↦ A σ], x ↦ A σ]) := by
  simp_all [Substitution.substs_cons, Substitution.subst]

@[gcongr]
theorem add_le_add [Add α] [Preorder α] [AddLeftMono α] [AddRightMono α] (a b c d : 𝔼[Γ, α])
    (hac : a ≤ c) (hbd : b ≤ d) : a + b ≤ c + d := by
  intro; simp; gcongr <;> apply_assumption
@[gcongr]
theorem mul_le_mul [Mul α] [Preorder α] [MulLeftMono α] [MulRightMono α] (a b c d : 𝔼[Γ, α])
    (hac : a ≤ c) (hbd : b ≤ d) : a * b ≤ c * d := by
  intro; simp; gcongr <;> apply_assumption

end Exp

abbrev BExpr (Γ : Γ[𝒱]) := 𝔼[Γ, Prop]

namespace BExpr

noncomputable def forall_ [DecidableEq 𝒱] (x : 𝒱) (b : BExpr Γ) : BExpr Γ :=
  fun σ ↦ ∀ (v : Γ x), b σ[x ↦ v]
noncomputable def exists_ [DecidableEq 𝒱] (x : 𝒱) (b : BExpr Γ) : BExpr Γ :=
  fun σ ↦ ∃ (v : Γ x), b σ[x ↦ v]

instance : HNot (BExpr α) where hnot := compl

variable {b : BExpr Γ}

@[coe] def coe_prop : Prop → BExpr Γ := fun b ↦ fun _ ↦ b
instance : Coe Prop 𝔼[Γ, Prop] := ⟨coe_prop⟩
@[grind =, simp] theorem coe_prop_apply {b} : coe_prop (Γ:=Γ) b σ = b := by rfl

@[simp] theorem iver_mul_le_apply {X : 𝔼[Γ, ENNReal]} : i[b σ] * X σ ≤ X σ := by calc
  _ ≤ 1 * X σ := by gcongr; simp
  _ = _ := by simp
@[grind ., simp] theorem iver_mul_le : i[b] * X ≤ X := by intro; simp
@[simp] theorem mul_iver_le_apply {X : 𝔼[Γ, ENNReal]} : X σ * i[b σ] ≤ X σ := by calc
  _ ≤ X σ * 1 := by gcongr; simp
  _ = _ := by simp
@[grind ., simp] theorem mul_iver_le : X * i[b] ≤ X := by intro; simp

variable [PartialOrder α]

noncomputable def lt (l r : 𝔼[Γ, α]) : BExpr Γ :=
  fun σ ↦ l σ < r σ
noncomputable def le (l r : 𝔼[Γ, α]) : BExpr Γ :=
  fun σ ↦ l σ ≤ r σ
noncomputable def eq (l r : 𝔼[Γ, α]) : BExpr Γ :=
  fun σ ↦ l σ = r σ
def and (l r : BExpr Γ) : BExpr Γ := fun σ ↦ l σ ∧ r σ
def or (l r : BExpr Γ) : BExpr Γ := fun σ ↦ l σ ∨ r σ
noncomputable def ite (b l r : BExpr Γ) : BExpr Γ :=
  letI := Classical.decPred b
  fun σ ↦ if (b σ) then l σ else r σ

@[grind =, simp] theorem lt_apply {l r : 𝔼[Γ, α]} : lt l r σ ↔ l σ < r σ := by rfl
@[grind =, simp] theorem le_apply {l r : 𝔼[Γ, α]} : le l r σ ↔ l σ ≤ r σ := by rfl
omit [PartialOrder α] in
@[grind =, simp] theorem eq_apply {l r : 𝔼[Γ, α]} : eq l r σ ↔ l σ = r σ := by rfl
@[grind =, simp] theorem and_apply {l r : BExpr Γ} : and l r σ ↔ l σ ∧ r σ := by rfl
@[grind =, simp] theorem or_apply {l r : BExpr Γ} : or l r σ ↔ l σ ∨ r σ := by rfl
open scoped Classical in
@[grind =, simp] theorem ite_apply (b l r : BExpr Γ) : ite b l r σ = if b σ then l σ else r σ := rfl

omit [PartialOrder α] in
@[simp] theorem eq_subst [DecidableEq 𝒱] {a b : 𝔼[Γ, α]} :
    (BExpr.eq a b)[..xs] = BExpr.eq a[..xs] b[..xs] :=
  Substitution.substs_of_binary fun _ _ ↦ congrFun rfl

end BExpr

end pGCL

open pGCL

namespace OrderHom

variable {α β : Type*} [Preorder α] [Preorder β] [Add β] [AddLeftMono β] [AddRightMono β]

instance : AddLeftMono (State Γ → ENNReal) where
  elim a _ _ hbc := fun σ ↦ add_le_add_right (hbc σ) (a σ)
instance : AddRightMono (State Γ → ENNReal) where
  elim a _ _ hbc := fun σ ↦ add_le_add_left (hbc σ) (a σ)

instance instAdd : Add (α →o β) where
  add a b := ⟨fun x ↦ a x + b x, fun x y h ↦ by simp; gcongr⟩
@[simp] theorem add_apply (f g : α →o β) : (f + g) x = f x + g x := by rfl
@[simp] theorem add_apply2' (f g : α →o State Γ → ENNReal) : (f + g) x y = f x y + g x y := by rfl

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
