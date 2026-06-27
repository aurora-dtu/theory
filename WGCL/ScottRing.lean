module

public import Mathlib.Algebra.Order.Hom.Ring
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Countable.Defs
public import Mathlib.Order.OmegaCompletePartialOrder

@[expose] public section

open OmegaCompletePartialOrder

instance {𝒮 : Type*} [AddMonoid 𝒮] [PartialOrder 𝒮] [IsBotZeroClass 𝒮] [AddLeftMono 𝒮] :
    Subsingleton (AddUnits 𝒮) where
  allEq := by
    intro ⟨a, b, hab, hba⟩ ⟨c, d, hcd, hdc⟩
    simp_all only [AddUnits.mk.injEq]
    have h₁ := hab.le
    have h₂ := hcd.le
    grw [← (by simp [le_add_of_nonneg_right] : a ≤ a + b)] at h₁
    grw [← (by simp [le_add_of_nonneg_right] : c ≤ c + d)] at h₂
    simp_all only [nonpos_iff_eq_zero, true_and, zero_add, add_zero]

namespace OmegaCompletePartialOrder

theorem ωSup_map {α β : Type*} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β] {c : Chain α}
    (f : α →o β) : ωSup (c.map f) = ωSup ⟨fun i ↦ f (c i), by intro _ _ _; simp; gcongr⟩ := by
  rfl

@[simp]
theorem Chain.mk_apply {β : Type*} [Preorder β] (f : ℕ → β) (hf : Monotone f) (a : ℕ) :
    Chain.instFunLikeNat.coe (⟨f, hf⟩ : Chain β) a = f a := rfl

@[gcongr]
theorem Chain.pi_mono {ι α : Type*} [Preorder α] {C : Chain (ι → α)} {i j : ℕ} (h : i ≤ j) {a : ι} :
    C i a ≤ C j a := by apply C.toOrderHom.mono h
@[simp]
theorem Chain.orderHom_mono {ι α : Type*} [Preorder ι] [Preorder α] {C : Chain (ι →o α)} {i j : ℕ} (h : i ≤ j) {a : ι} :
    C i a ≤ C j a := by apply C.toOrderHom.mono h
@[simp]
theorem Chain.le_of_apply {α : Type*} [Preorder α] {C₁ C₂ : Chain α} (h : ∀ i, C₁ i ≤ C₂ i) :
    C₁ ≤ C₂ := by intro i; use i, h _

variable {ι κ α : Type*} [Countable ι] [Countable κ]
variable [OmegaCompletePartialOrder α]

@[simp]
theorem ωSup_const {x : α} : ωSup ⟨fun _ ↦ x, monotone_const⟩ = x := by
  apply le_antisymm <;> simp [le_ωSup_of_le 0]

@[simp]
theorem ωSup_eq_zero_iff [Zero α] [IsBotZeroClass α] (c : Chain α) : ωSup c = 0 ↔ ∀ i, c i = 0 := by
  constructor
  · intro this
    replace this := ωSup_le_iff.mp this.le
    simpa
  · intro
    apply le_antisymm
    · apply ωSup_le; simp_all
    · simp

theorem ωSup_ωSup_eq_ωSup (f : ℕ →o ℕ →o α) :
      ωSup ⟨fun i ↦ ωSup ⟨fun j ↦ f i j, (f i).mono⟩, fun _ _ hij ↦ ωSup_le _ _ fun k ↦ le_ωSup_of_le k (f.mono hij k)⟩
    = ωSup ⟨fun i ↦ f i i, fun i j hij ↦ le_trans (f.mono hij i) ((f j).mono hij)⟩ := by
  apply le_antisymm
  · refine ωSup_le _ _ fun i ↦ ωSup_le _ _ fun j ↦ le_ωSup_of_le (i ⊔ j) ?_
    simp only [Chain.mk_apply]
    (repeat apply OrderHom.apply_mono) <;> grind
  · apply ωSup_le _ _ fun i ↦ le_ωSup_of_le i (le_ωSup_of_le i (by rfl))

theorem ωSup_ωSup_eq_ωSup' {α : Type*} [OmegaCompletePartialOrder α] (f : ℕ → ℕ → α) (hf : Monotone f) (hf' : ∀ i, Monotone (f i)) :
      ωSup ⟨fun i ↦ ωSup ⟨fun j ↦ f i j, hf' i⟩, fun _ _ hij ↦ ωSup_le _ _ fun k ↦ le_ωSup_of_le k (hf hij k)⟩
    = ωSup ⟨fun i ↦ f i i, fun i j hij ↦ le_trans (hf hij i) (hf' j hij)⟩ :=
  OmegaCompletePartialOrder.ωSup_ωSup_eq_ωSup ⟨fun i ↦ ⟨fun j ↦ f i j, hf' i⟩, hf⟩

section ωScottContinuousAdd

class ωScottContinuousLeftAdd (α : Type*) [OmegaCompletePartialOrder α] [Add α] : Prop where
  add_right_ωScottContinuous (a : α) : ωScottContinuous (a + ·)
attribute [simp] ωScottContinuousLeftAdd.add_right_ωScottContinuous

instance (priority := 100) (α : Type*) [OmegaCompletePartialOrder α] [Add α] [ωScottContinuousLeftAdd α] :
    AddLeftMono α where
  elim a _ _ h :=
    le_of_le_of_eq ((ωScottContinuousLeftAdd.add_right_ωScottContinuous a).monotone h) rfl

class ωScottContinuousRightAdd (α : Type*) [OmegaCompletePartialOrder α] [Add α] : Prop where
  add_left_ωScottContinuous (a : α) : ωScottContinuous (· + a)
attribute [simp] ωScottContinuousRightAdd.add_left_ωScottContinuous

instance (priority := 100) (α : Type*) [OmegaCompletePartialOrder α] [Add α] [ωScottContinuousRightAdd α] :
    AddRightMono α where
  elim a _ _ h :=
    le_of_le_of_eq ((ωScottContinuousRightAdd.add_left_ωScottContinuous a).monotone h) rfl

@[reducible]
def ωScottContinuousLeftAdd_of_add_ωSup {α : Type*} [OmegaCompletePartialOrder α] [Add α] [AddLeftMono α]
    (h : ∀ (a : α) (c : Chain α), a + ωSup c = ωSup (c.map ⟨(a + ·), add_right_mono⟩)) :
    ωScottContinuousLeftAdd α where
  add_right_ωScottContinuous x := by
    simp [ωScottContinuous_iff_monotone_map_ωSup, add_right_mono, h]

class ωScottContinuousAdd (α : Type*) [OmegaCompletePartialOrder α] [Add α] : Prop
  extends ωScottContinuousLeftAdd α, ωScottContinuousRightAdd α

@[reducible]
def ωScottContinuousRightAdd_of_ωSup_add {α : Type*} [OmegaCompletePartialOrder α] [Add α] [AddRightMono α]
    (h : ∀ (a : α) (c : Chain α), ωSup c + a = ωSup (c.map ⟨(· + a), add_left_mono⟩)) :
    ωScottContinuousRightAdd α where
  add_left_ωScottContinuous x := by
    simp [ωScottContinuous_iff_monotone_map_ωSup, add_left_mono, h]

instance (priority := 100) {α : Type*} [OmegaCompletePartialOrder α] [AddCommMagma α] [ωScottContinuousLeftAdd α] :
    ωScottContinuousRightAdd α where
  add_left_ωScottContinuous a := by simp [add_comm]

instance (priority := 100) {α : Type*} [OmegaCompletePartialOrder α] [AddCommMagma α] [ωScottContinuousRightAdd α] :
    ωScottContinuousLeftAdd α where
  add_right_ωScottContinuous a := by
    conv => enter [1, x]; rw [add_comm]
    exact ωScottContinuousRightAdd.add_left_ωScottContinuous a

instance (priority := 100) {α : Type*} [OmegaCompletePartialOrder α] [AddCommMagma α] [ωScottContinuousRightAdd α] :
    ωScottContinuousAdd α where

theorem ωSup_add {α : Type*} [OmegaCompletePartialOrder α] [Add α] [ωScottContinuousRightAdd α]
    (a : α) (c : Chain α) : ωSup c + a = ωSup (c.map ⟨(· + a), add_left_mono⟩) :=
  (ωScottContinuousRightAdd.add_left_ωScottContinuous a).map_ωSup _
theorem add_ωSup {α : Type*} [OmegaCompletePartialOrder α] [Add α] [ωScottContinuousLeftAdd α]
    (a : α) (c : Chain α) : a + ωSup c = ωSup (c.map ⟨(a + ·), add_right_mono⟩) :=
  (ωScottContinuousLeftAdd.add_right_ωScottContinuous a).map_ωSup _
theorem ωSup_add_ωSup {α : Type*} [OmegaCompletePartialOrder α] [Add α] [ωScottContinuousAdd α]
    (c₁ c₂ : Chain α) : ωSup c₁ + ωSup c₂ = ωSup ⟨fun i ↦ c₁ i + c₂ i, by intro _ _ _; simp; gcongr⟩ := by
  simp [add_ωSup, ωSup_add, ωSup_map]
  rw [ωSup_ωSup_eq_ωSup']
  intro _ _ _ _; simp; gcongr

end ωScottContinuousAdd

section ωScottContinuousSMul

class SMulMono (α β : Type*) [SMul α β] [Preorder β] : Prop where
  smul_le_smul_left : ∀ ⦃a : α⦄, ∀ ⦃b₁ b₂ : β⦄, b₁ ≤ b₂ → a • b₁ ≤ a • b₂

attribute [gcongr] SMulMono.smul_le_smul_left

instance {ι α β : Type*} [SMul α β] [Preorder β] [SMulMono α β] : SMulMono α (ι → β) :=
  ⟨fun a b c h i ↦ by simp; gcongr; apply h⟩

class ωScottContinuousSMul (ι α : Type*) [OmegaCompletePartialOrder α] [SMul ι α] where
  smul_continuous (i : ι) : ωScottContinuous fun (x : α) ↦ i • x

theorem ωScottContinuousSMul.of_smul_continuous {ι α : Type*} [OmegaCompletePartialOrder α] [SMul ι α] [SMulMono ι α]
    (h : ∀ a (c : Chain α), (a : ι) • ωSup c = ωSup (c.map ⟨(a • ·), fun _ _ _ ↦ by simp; gcongr⟩)) :
    ωScottContinuousSMul ι α where
  smul_continuous _ := ωScottContinuous_iff_monotone_map_ωSup.mpr ⟨by intro a b h; simp; gcongr, h _⟩

instance {ι : Type*} [SMul ι α] [ωScottContinuousSMul ι α] : SMulMono ι α where
  smul_le_smul_left a _ _ h := (ωScottContinuousSMul.smul_continuous a).monotone h

theorem smul_ωSup {ι : Type*} [SMul ι α] [ωScottContinuousSMul ι α] {a : ι} {c : Chain α} :
    a • ωSup c = ωSup (c.map ⟨(a • ·), fun _ _ _ ↦ by simp; gcongr⟩) :=
  (ωScottContinuousSMul.smul_continuous a).map_ωSup _

instance {ι α β : Type*} [SMul α β] [OmegaCompletePartialOrder β] [ωScottContinuousSMul α β] :
    ωScottContinuousSMul α (ι → β) := ωScottContinuousSMul.of_smul_continuous <| by
  intro a c; ext i
  show a • ωSup (c.map ⟨(· i), _⟩) = _
  simp [smul_ωSup]
  rfl

end ωScottContinuousSMul

section ωScottContinuousMul

class ωScottContinuousLeftMul (α : Type*) [OmegaCompletePartialOrder α] [Mul α] : Prop where
  mul_right_ωScottContinuous (a : α) : ωScottContinuous (a * ·)
attribute [simp] ωScottContinuousLeftMul.mul_right_ωScottContinuous

instance (priority := 100) (α : Type*) [OmegaCompletePartialOrder α] [Mul α] [ωScottContinuousLeftMul α] :
    MulLeftMono α where
  elim a _ _ h :=
    le_of_le_of_eq ((ωScottContinuousLeftMul.mul_right_ωScottContinuous a).monotone h) rfl

class ωScottContinuousRightMul (α : Type*) [OmegaCompletePartialOrder α] [Mul α] : Prop where
  mul_left_ωScottContinuous (a : α) : ωScottContinuous (· * a)
attribute [simp] ωScottContinuousRightMul.mul_left_ωScottContinuous

instance (priority := 100) (α : Type*) [OmegaCompletePartialOrder α] [Mul α] [ωScottContinuousRightMul α] :
    MulRightMono α where
  elim a _ _ h :=
    le_of_le_of_eq ((ωScottContinuousRightMul.mul_left_ωScottContinuous a).monotone h) rfl

@[reducible]
def ωScottContinuousLeftMul_of_Mul_ωSup {α : Type*} [OmegaCompletePartialOrder α] [Mul α] [MulLeftMono α]
    (h : ∀ (a : α) (c : Chain α), a * ωSup c = ωSup (c.map ⟨(a * ·), mul_right_mono⟩)) :
    ωScottContinuousLeftMul α where
  mul_right_ωScottContinuous x := by
    simp [ωScottContinuous_iff_monotone_map_ωSup, mul_right_mono, h]

class ωScottContinuousMul (α : Type*) [OmegaCompletePartialOrder α] [Mul α] : Prop
  extends ωScottContinuousLeftMul α, ωScottContinuousRightMul α

@[reducible]
def ωScottContinuousRightMul_of_ωSup_Mul {α : Type*} [OmegaCompletePartialOrder α] [Mul α] [MulRightMono α]
    (h : ∀ (a : α) (c : Chain α), ωSup c * a = ωSup (c.map ⟨(· * a), mul_left_mono⟩)) :
    ωScottContinuousRightMul α where
  mul_left_ωScottContinuous x := by
    simp [ωScottContinuous_iff_monotone_map_ωSup, mul_left_mono, h]

instance (priority := 100) {α : Type*} [OmegaCompletePartialOrder α] [CommMagma α] [ωScottContinuousLeftMul α] :
    ωScottContinuousRightMul α where
  mul_left_ωScottContinuous a := by simp [mul_comm]

instance (priority := 100) {α : Type*} [OmegaCompletePartialOrder α] [CommMagma α] [ωScottContinuousRightMul α] :
    ωScottContinuousLeftMul α where
  mul_right_ωScottContinuous a := by
    conv => enter [1, x]; rw [mul_comm]
    exact ωScottContinuousRightMul.mul_left_ωScottContinuous a

instance (priority := 100) {α : Type*} [OmegaCompletePartialOrder α] [CommMagma α] [ωScottContinuousRightMul α] :
    ωScottContinuousMul α where

theorem ωSup_mul {α : Type*} [OmegaCompletePartialOrder α] [Mul α] [ωScottContinuousRightMul α]
    (a : α) (c : Chain α) : ωSup c * a = ωSup (c.map ⟨(· * a), mul_left_mono⟩) :=
  (ωScottContinuousRightMul.mul_left_ωScottContinuous a).map_ωSup _
theorem mul_ωSup {α : Type*} [OmegaCompletePartialOrder α] [Mul α] [ωScottContinuousLeftMul α]
    (a : α) (c : Chain α) : a * ωSup c = ωSup (c.map ⟨(a * ·), mul_right_mono⟩) :=
  (ωScottContinuousLeftMul.mul_right_ωScottContinuous a).map_ωSup _
theorem ωSup_mul_ωSup {α : Type*} [OmegaCompletePartialOrder α] [Mul α] [ωScottContinuousMul α]
    (c₁ c₂ : Chain α) : ωSup c₁ * ωSup c₂ = ωSup ⟨fun i ↦ c₁ i * c₂ i, by intro a b h; simp; gcongr⟩ := by
  simp [ωSup_mul, mul_ωSup, Chain.map, OrderHom.comp]
  unfold Function.comp
  rw [ωSup_ωSup_eq_ωSup']
  refine monotone_lam fun i ↦ Monotone.const_mul' c₂.mono _

end ωScottContinuousMul

class IsScottAddMonoid (α : Type*) [AddCommMonoid α] [OmegaCompletePartialOrder α] extends
    IsBotZeroClass α, ωScottContinuousAdd α, IsOrderedAddMonoid α where

class IsScottRing (α : Type*) [NonUnitalNonAssocSemiring α] [OmegaCompletePartialOrder α] extends
    ωScottContinuousMul α, IsScottAddMonoid α where

section Pi

variable {ι α : Type*}

instance [Add α] [OmegaCompletePartialOrder α] [ωScottContinuousLeftAdd α] :
    ωScottContinuousLeftAdd (ι → α) where
  add_right_ωScottContinuous f := by
    refine ωScottContinuous_iff_apply₂.mpr fun i ↦ ωScottContinuous.fun_comp ?_ ?_
    · exact ωScottContinuousLeftAdd.add_right_ωScottContinuous _
    · exact ωScottContinuous.apply i

instance [Mul α] [OmegaCompletePartialOrder α] [ωScottContinuousLeftMul α] :
    ωScottContinuousLeftMul (ι → α) where
  mul_right_ωScottContinuous f := by
    refine ωScottContinuous_iff_apply₂.mpr fun i ↦ ωScottContinuous.fun_comp ?_ ?_
    · exact ωScottContinuousLeftMul.mul_right_ωScottContinuous _
    · exact ωScottContinuous.apply i
instance [Mul α] [OmegaCompletePartialOrder α] [ωScottContinuousRightMul α] :
    ωScottContinuousRightMul (ι → α) where
  mul_left_ωScottContinuous f := by
    refine ωScottContinuous_iff_apply₂.mpr fun i ↦ ωScottContinuous.of_monotone_map_ωSup ?_
    apply Exists.intro
    · intro; simp [ωSup_mul, ωSup]; rfl
    · apply Monotone.mul_const'; exact Function.monotone_eval i

instance [AddCommMonoid α] [Preorder α] [IsOrderedAddMonoid α] :
    IsOrderedAddMonoid (ι → α) where
  add_le_add_left a b hab _ _ := by simp; gcongr; apply hab

instance [AddCommMonoid α] [OmegaCompletePartialOrder α] [IsScottAddMonoid α] :
    IsScottAddMonoid (ι → α) where
  isBot_zero f i := by simp
  add_le_add_left := by simp_all [add_le_add_left]

instance [NonUnitalNonAssocSemiring α] : NonUnitalNonAssocSemiring (ι → α) where
  left_distrib a b c := by simp [mul_add, funext_iff]
  right_distrib a b c := by simp [add_mul, funext_iff]
  zero_mul := by simp [funext_iff]
  mul_zero := by simp [funext_iff]

instance [NonUnitalNonAssocSemiring α] [OmegaCompletePartialOrder α] [IsScottRing α] :
    IsScottRing (ι → α) where
  isBot_zero f i := by simp
  add_le_add_left := by simp_all [add_le_add_left]

end Pi


theorem apply_ωSup {α β : Type*} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]
    {F : Type*} [EquivLike F α β] [OrderIsoClass F α β] (e : F)
    (c : Chain α) :
    e (ωSup c) = ωSup (c.map e) := by
  let g := OrderIsoClass.toOrderIso e
  show g (ωSup c) = ωSup (c.map ↑g)
  apply le_antisymm
  · apply (map_le_map_iff g.symm).mp
    simp
    intro i
    apply (map_le_map_iff g).mp
    simp
    apply le_ωSup_of_le i
    rfl
  · simp [le_ωSup]

theorem ωScottContinuous_of_left_equiv {ι α β : Type*} [OmegaCompletePartialOrder ι] [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]
    {F : Type*} [EquivLike F α β] [OrderIsoClass F α β] (e : F)
    (f : ι → α) (h : ωScottContinuous f) :
    ωScottContinuous (e ∘ f) := by
  let g := OrderIsoClass.toOrderIso e
  show ωScottContinuous (g ∘ f)
  simp_all [ωScottContinuous_iff_monotone_map_ωSup]
  obtain ⟨h₁, h₂⟩ := h
  exists by intro a b h; simp_all; exact le_of_le_of_eq (h₁ h) rfl
  intro c₁
  simp_all [ωSup_map]
  apply le_antisymm
  · apply (map_le_map_iff g.symm).mp
    simp
    intro i
    apply (map_le_map_iff g).mp
    simp
    apply le_ωSup_of_le i
    rfl
  · simp; intro i; apply le_ωSup_of_le i; simp
theorem ωScottContinuous_iff_left_equiv {ι α β : Type*} [OmegaCompletePartialOrder ι] [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]
    {F : Type*} [EquivLike F α β] [OrderIsoClass F α β] (e : F)
    (f : ι → α) :
    ωScottContinuous f ↔ ωScottContinuous (e ∘ f) := by
  let g := OrderIsoClass.toOrderIso e
  show _ ↔ ωScottContinuous (g ∘ f)
  constructor
  · exact ωScottContinuous_of_left_equiv e f
  · intro h
    have : g.symm ∘ g ∘ f = f := by ext; simp
    rw [← this]
    exact ωScottContinuous_of_left_equiv _ _ h

theorem ωScottContinuous_of_right_equiv {ι κ α : Type*} [OmegaCompletePartialOrder ι] [OmegaCompletePartialOrder κ] [OmegaCompletePartialOrder α]
    {F : Type*} [EquivLike F κ ι] [OrderIsoClass F κ ι] (e : F)
    (f : ι → α) (h : ωScottContinuous f) :
    ωScottContinuous (f ∘ e) := by
  let g := OrderIsoClass.toOrderIso e
  show ωScottContinuous (f ∘ g)
  simp_all [ωScottContinuous_iff_monotone_map_ωSup, apply_ωSup]
  obtain ⟨h₁, h₂⟩ := h
  exists by intro a b h; simp_all; apply h₁; exact (OrderIso.le_iff_le g).mpr h
  intro c₁
  simp_all [ωSup_map]
theorem ωScottContinuous_iff_right_equiv {ι κ α : Type*} [OmegaCompletePartialOrder ι] [OmegaCompletePartialOrder κ] [OmegaCompletePartialOrder α]
    {F : Type*} [EquivLike F κ ι] [OrderIsoClass F κ ι] (e : F)
    (f : ι → α) :
    ωScottContinuous f ↔ ωScottContinuous (f ∘ e) := by
  let g := OrderIsoClass.toOrderIso e
  show _ ↔ ωScottContinuous (f ∘ g)
  constructor
  · exact ωScottContinuous_of_right_equiv e f
  · intro h
    have : f ∘ g ∘ g.symm = f := by ext; simp
    rw [← this]
    exact ωScottContinuous_of_right_equiv _ _ h
theorem ωScottContinuous_iff_equiv {ι κ : Type*} [OmegaCompletePartialOrder ι] [OmegaCompletePartialOrder κ]
    {F : Type*} [EquivLike F κ ι] [OrderIsoClass F κ ι] (e : F)
    (f : ι → ι) :
    ωScottContinuous f ↔ ωScottContinuous ((e : κ ≃o ι).symm ∘ f ∘ e) := by
  rw [ωScottContinuous_iff_right_equiv e]
  rw [ωScottContinuous_iff_left_equiv e]
  congr!
  ext
  exact EquivLike.inv_apply_eq.mp rfl

theorem ωScottContinuous_iff_orderAddIso {ι κ : Type*} [OmegaCompletePartialOrder ι] [OmegaCompletePartialOrder κ]
    [Add ι] [Add κ]
    (e : κ ≃+o ι)
    (f : ι → ι) :
    ωScottContinuous f ↔ ωScottContinuous fun i ↦ e.symm (f (e i)) := by
  rw [ωScottContinuous_iff_right_equiv e]
  rw [ωScottContinuous_iff_left_equiv e]
  congr!
  ext
  exact EquivLike.inv_apply_eq.mp rfl

theorem ωScottContinuous_iff_orderRingIso {ι κ : Type*} [OmegaCompletePartialOrder ι] [OmegaCompletePartialOrder κ]
    [Mul ι] [Add ι] [Mul κ] [Add κ]
    (e : κ ≃+*o ι)
    (f : ι → ι) :
    ωScottContinuous f ↔ ωScottContinuous fun i ↦ e.symm (f (e i)) := by
  rw [ωScottContinuous_iff_right_equiv e]
  rw [ωScottContinuous_iff_left_equiv e]
  congr!
  ext
  exact EquivLike.inv_apply_eq.mp rfl

@[simp]
theorem OrderIsoClass.toOrderIso_symm_apply {ι κ : Type*} [OmegaCompletePartialOrder ι] [OmegaCompletePartialOrder κ]
    [Mul ι] [Add ι] [Mul κ] [Add κ]
    {F : Type*} [EquivLike F κ ι] [OrderIsoClass F κ ι] [RingEquivClass F κ ι] (e : F) (i : ι) :
    (e : κ ≃o ι).symm i = (e : κ ≃+*o ι).symm i := by rfl

@[reducible]
def IsScottAddMonoid.lift {α β : Type*} [AddCommMonoid α] [OmegaCompletePartialOrder α] [IsScottAddMonoid α]
    [AddCommMonoid β] [OmegaCompletePartialOrder β] (f : α ≃+o β) : IsScottAddMonoid β where
  isBot_zero a := by apply (map_le_map_iff f.symm).mp; simp
  add_le_add_left a b h c := by apply (map_le_map_iff f.symm).mp; simp; gcongr
  add_right_ωScottContinuous a := by simp [ωScottContinuous_iff_orderAddIso f]
  add_left_ωScottContinuous a := by simp [ωScottContinuous_iff_orderAddIso f]

@[reducible]
def IsScottRing.lift {α β : Type*} [NonUnitalNonAssocSemiring α] [OmegaCompletePartialOrder α] [IsScottRing α]
    [NonUnitalNonAssocSemiring β] [OmegaCompletePartialOrder β] (f : α ≃+*o β) : IsScottRing β :=
  { isBot_zero a := by apply (map_le_map_iff f.symm).mp; simp
    add_le_add_left a b h c := by apply (map_le_map_iff f.symm).mp; simp; gcongr
    mul_right_ωScottContinuous a := by simp [ωScottContinuous_iff_orderRingIso f]
    mul_left_ωScottContinuous a := by simp [ωScottContinuous_iff_orderRingIso f]
    add_right_ωScottContinuous a := by simp [ωScottContinuous_iff_orderRingIso f]
    add_left_ωScottContinuous a := by simp [ωScottContinuous_iff_orderRingIso f]
  }

end OmegaCompletePartialOrder
