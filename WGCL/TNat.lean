import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Topology.Instances.ENat
import Mathlib.Data.ENat.Lattice

namespace TNat

noncomputable instance (priority := 0) instTAdd : Add ℕ∞ where
  add a b := a ⊓ b
@[simp] theorem instTAdd_Add_eq_inf : instTAdd.add a b = a ⊓ b := rfl
@[simp] theorem instTAdd_HAdd_eq_inf : (@instHAdd ℕ∞ instTAdd).hAdd a b = a ⊓ b := rfl
instance (priority := 0) instTMul : Mul ℕ∞ where
  mul a b := a + b
@[simp] theorem instTMul_Mul_eq_add : instTMul.mul a b = a + b := rfl
@[simp] theorem instTMul_HMul_eq_add : (@instHMul ℕ∞ instTMul).hMul a b = a + b := rfl

protected def test_add {α : Type} [inst : Add α] (a b c : α) := a + b = c
protected def test_mul {α : Type} [inst : Mul α] (a b c : α) := a * b = c

-- + => ⊓
-- * => +
-- 0 => ⊤
-- 1 => 0

example : @TNat.test_add ℕ∞ instTAdd 2 3 2 := by
  simp [TNat.test_add]
  norm_cast
example : @TNat.test_add ℕ∞ _ 2 3 5 := by
  simp [TNat.test_add]
  norm_cast
example : @TNat.test_mul ℕ∞ instTMul 2 3 5 := by
  simp [TNat.test_mul]
  norm_cast
example : @TNat.test_mul ℕ∞ _ 2 3 6 := by
  simp [TNat.test_mul]
  norm_cast

instance (priority := 0) instTZero : Zero ℕ∞ where zero := ⊤
instance (priority := 0) instTOne : One ℕ∞ where one := 0

protected def test_zero {α : Type} [inst : Zero α] := inst.zero
protected def test_one {α : Type} [inst : One α] := inst.one
@[simp] theorem instTZero_eq_top : instTZero.zero = ⊤ := rfl
@[simp] theorem instTOne_eq_zero : instTOne.one = 0 := rfl

example : @TNat.test_zero ℕ∞ instTZero = ⊤ := by simp [TNat.test_zero]
example : @TNat.test_zero ℕ∞ _ = 0 := by simp [TNat.test_zero]; rfl
example : @TNat.test_one ℕ∞ instTOne = 0 := by simp [TNat.test_one]
example : @TNat.test_one ℕ∞ _ = 1 := by simp [TNat.test_one]; rfl

instance (priority := 0) instTLE : LE ℕ∞ where le a b := b ≤ a
instance (priority := 0) instTLT : LT ℕ∞ where lt a b := b < a

protected def test_le {α : Type} [inst : LE α] (a b : α) := inst.le a b
example : @TNat.test_le ℕ∞ instTLE 2 1 := by simp [TNat.test_le]; norm_cast
example : @TNat.test_le ℕ∞ _ 1 2 := by simp [TNat.test_le]

protected def test_lt {α : Type} [inst : LT α] (a b : α) := inst.lt a b
example : @TNat.test_lt ℕ∞ instTLT 2 1 := by simp [TNat.test_lt]; norm_cast
example : @TNat.test_lt ℕ∞ _ 1 2 := by simp [TNat.test_lt]

@[simp] theorem instTLE_le : instTLE.le a b ↔ b ≤ a := by simp [instTLE]
@[simp] theorem instTLT_lt : instTLT.lt a b ↔ b < a := by simp [instTLT]

instance (priority := 0) instTBot : Bot ℕ∞ := ⟨⊤⟩

instance (priority := 0) instTPreorder : Preorder ℕ∞ := { instTLE, instTLT with
  le_refl := by simp
  le_trans a b c h₁ h₂ := by simp_all; exact le_trans h₂ h₁
  lt_iff_le_not_le a b := by simp_all; exact fun a_1 ↦ le_of_lt a_1
}
instance (priority := 0) instTOrderBot : @OrderBot ℕ∞ instTPreorder.toLE :=
  { instTBot with
    bot_le a := by
      simp
  }
-- instance (priority := 0) instTOfNatZero : OfNat ℕ∞ 0 := ⟨instTZero.zero⟩
instance (priority := 0) instTNatCast : NatCast ℕ∞ where
  natCast n := if n = 0 then ⊤ else 0
instance (priority := 0) instTOfNat {n : ℕ} : OfNat ℕ∞ n where
  ofNat := instTNatCast.natCast n

@[simp] theorem instTNatCast_zero_eq_top : instTNatCast.natCast 0 = ⊤ := rfl
@[simp] theorem instTNatCast_one_eq_zero : instTNatCast.natCast 1 = 0 := rfl

@[simp] theorem instTOfNat_zero : (@instTOfNat 0).ofNat = ⊤ := rfl
@[simp] theorem instTOfNat_one : (@instTOfNat 1).ofNat = 0 := rfl

noncomputable instance (priority := 0) instTSemiring : Semiring ℕ∞ := {
    instTMul, instTAdd, instTOne, instTZero, instTNatCast
      with
    natCast_zero := by rfl
    natCast_succ n := by simp [instTNatCast]
    add_assoc := by simp [inf_assoc]
    zero_add n := by simp
    add_zero n := by simp
    nsmul n a := if n = 0 then ⊤ else a
    add_comm := by simp [inf_comm]
    left_distrib := by simp [min_add_add_left]
    right_distrib := by simp [min_add_add_right]
    zero_mul := by simp
    mul_zero a := by simp
    mul_assoc := by simp [add_assoc]
    one_mul a := by simp
    mul_one a := by simp
    nsmul_succ n a := by simp; split_ifs <;> simp
  }

noncomputable instance (priority := 0) instTOmegaCompletePartialOrder :
    OmegaCompletePartialOrder ℕ∞ := {
  instTLE, instTLT with
  le_antisymm a b h₁ h₂ := le_antisymm h₂ h₁
  ωSup c := ⨅ i, c i
  lt_iff_le_not_le a b := by simp; exact fun a_1 ↦ le_of_lt a_1
  le_ωSup c i := by simp; exact iInf_le_iff.mpr fun b a ↦ a i
  ωSup_le c := by simp
}

instance (priority := 0) instTAddLeftMono : AddLeftMono ℕ∞ := { instTSemiring with
  elim := by
    intro a b c h
    simp
    exact add_le_add_left h a
}
instance (priority := 0) instTMulLeftMono : MulLeftMono ℕ∞ := { instTSemiring with
  elim := by
    intro a b c h
    simp
    exact mul_le_mul_left' h a
}


end TNat
