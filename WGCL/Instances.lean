import Mathlib.Algebra.Tropical.Basic
import Mathlib.Computability.Language
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.EReal.Basic
import Mathlib.Order.OmegaCompletePartialOrder
import WGCL.WeakestPre
import WGCL.Park

namespace WGCL

section General

variable [OmegaCompletePartialOrder W] [OrderBot W]
variable [Semiring W]
variable [AddLeftMono W] [MulLeftMono W]

open scoped Classical in
example [SupSet W] (h : (0 : W) ≤ 1) :
    wp[ℕ,W,W,Var]⟦if (~(· x < 2)) { ⊙ 1 } else { ⊙ 2 }⟧(1) ≤ wght {2} := by
  intro σ
  simp [wGCL.wp, Subst.subst, BExpr.iver, BExpr.not]
  if h' : σ x < 2 then
    simp_all [Nat.not_le_of_lt]
    rw [← one_add_one_eq_two]
    refine le_add_of_nonneg_left h
  else
    simp_all [Nat.not_lt.mpr]

end General

section Boolean

/-- `Boolean`s are `Bool`s where `b₁ + b₂ = b₁ ∨ b₂` rather than `b₁ ^^ b₂`. -/
def Boolean := Bool

instance : PartialOrder Boolean := inferInstanceAs (PartialOrder Bool)
instance : OrderBot Boolean := inferInstanceAs (OrderBot Bool)
instance : OrderTop Boolean := inferInstanceAs (OrderTop Bool)

open scoped Classical in
noncomputable instance : OmegaCompletePartialOrder Boolean where
  ωSup C := if ∃ n, C n = ⊤ then ⊤ else ⊥
  le_ωSup C n := by
    split_ifs with h
    · simp_all
    · simp_all
      have := h n
      exact not_bot_lt_iff.mp (h n)
  ωSup_le C n h := by
    split_ifs with h'
    · obtain ⟨n', h'⟩ := h'
      simp_all
      have := h n'
      simp_all
    · simp_all

instance : Add Boolean := ⟨fun a b ↦ a || b⟩
instance : Mul Boolean := ⟨fun a b ↦ a && b⟩
instance : Zero Boolean := ⟨⊥⟩

@[simp] theorem Boolean.add_eq_inf (a b : Boolean) : a + b = (a || b) := rfl
@[simp] theorem Boolean.mul_eq_add (a b : Boolean) : a * b = (a && b) := rfl
@[simp] theorem Boolean.bot_or (a : Boolean) : (⊥ || a) = a := rfl
@[simp] theorem Boolean.or_bot (a : Boolean) : (a || ⊥) = a := by rw [Bool.or_comm]; rfl
@[simp] theorem Boolean.bot_le (a : Boolean) : ⊥ ≤ a := OrderBot.bot_le a
@[simp] theorem Boolean.le_top (a : Boolean) : a ≤ ⊤ := OrderTop.le_top a
@[simp] theorem Boolean.zero_eq_bot : (0 : Boolean) = ⊥ := rfl

instance : Semiring Boolean where
  add_assoc a b c := by simp [Bool.or_assoc]
  zero_add := by simp; exact Boolean.bot_or
  add_zero := by simp; exact Boolean.or_bot
  nsmul n x := if n = 0 then ⊥ else x
  add_comm := by simp [Bool.or_comm]
  left_distrib := by simp [Bool.and_or_distrib_left]
  right_distrib := by simp [Bool.and_or_distrib_right]
  zero_mul _ := by rfl
  mul_zero _ := by simp; rw [Bool.and_comm]; rfl
  mul_assoc := by simp [Bool.and_assoc]
  one := ⊤
  one_mul _ := by simp; exact rfl
  mul_one _ := by simp; exact Bool.and_true _
  nsmul_zero := by simp
  nsmul_succ n _ := by split_ifs <;> simp_all; exact Bool.false_or _ |>.symm

instance : AddLeftMono Boolean := ⟨fun b₁ b₂ b₃ h h' ↦ by
  simp_all [LE.le]; exact Or.imp_right h h'⟩
instance : MulLeftMono Boolean := ⟨fun b₁ b₂ b₃ h ↦ by simp_all [LE.le]⟩

open scoped Classical in
/- **Verification/Debugging** via the **Boolean semiring** -/
example : wp[ℕ,Boolean,Boolean,String]⟦{⊙1} ⊕ {⊙0}⟧(1) = wght {1} := by
  simp [wGCL.wp]

end Boolean

section Combinatorics

open scoped Classical in
/- **Combinatorics** via the (extended) **Natural Numbers semiring** -/
example : wp[ℕ,ℕ∞,ℕ∞,String]⟦{⊙3} ⊕ {⊙4}⟧(1) = wght {7} := by
  simp [wGCL.wp]
  norm_cast

open scoped Classical in
/- **Combinatorics** via the (extended) **Natural Numbers semiring** -/
example : wp[ℕ,ℕ∞,ℕ∞,String]⟦x := 1; {⊙ x} ⊕ {⊙2}⟧(1) = wght {3} := by
  simp [wGCL.wp, Subst.subst]
  norm_cast

end Combinatorics

noncomputable section ENat

/-- A version of ℕ∞ where `a + b = a ⊓ b` and `a * b = a + b`. -/
def ENat' := ℕ∞

instance : PartialOrder ENat' := inferInstanceAs (PartialOrder ℕ∞)
instance : OrderBot ENat' := inferInstanceAs (OrderBot ℕ∞)
instance : OrderTop ENat' := inferInstanceAs (OrderTop ℕ∞)
instance : OmegaCompletePartialOrder ENat' := inferInstanceAs (OmegaCompletePartialOrder ℕ∞)
instance : Min ENat' := inferInstanceAs (Min ℕ∞)

instance : Add ENat' := ⟨fun a b ↦ a ⊓ b⟩
instance : Mul ENat' := ⟨fun a b ↦
  let a' : ℕ∞ := a
  let b' : ℕ∞ := b
  a' + b'⟩
instance : Zero ENat' := ⟨⊤⟩
instance : One ENat' := ⟨⊥⟩

@[simp] theorem ENat'.add_eq_inf (a b : ENat') : a + b = (a ⊓ b) := rfl
@[simp] theorem ENat'.mul_eq_add (a b : ENat') : a * b =
  let a' : ℕ∞ := a
  let b' : ℕ∞ := b
  a' + b' := rfl
@[simp] theorem ENat'.bot_le (a : ENat') : ⊥ ≤ a := OrderBot.bot_le a
@[simp] theorem ENat'.le_top (a : ENat') : a ≤ ⊤ := OrderTop.le_top a
@[simp] theorem ENat'.zero_eq_top : (0 : ENat') = ⊤ := rfl
@[simp] theorem ENat'.one_eq_zero : (1 : ENat') = (0 : ℕ∞) := rfl

instance : Semiring ENat' where
  add_assoc a b c := by simp [inf_assoc]
  zero_add := by simp
  add_zero := by simp
  nsmul n x := if n = 0 then ⊤ else x
  add_comm := by simp [inf_comm]
  left_distrib a b c := by simp [add_min]
  right_distrib := by simp [min_add]
  zero_mul _ := by rfl
  mul_zero _ := by simp
  mul_assoc := by simp [add_assoc]
  one_mul _ := by simp
  mul_one _ := by simp
  nsmul_zero := by simp
  nsmul_succ n := by simp; split_ifs <;> simp_all

instance : AddLeftMono ENat' := ⟨fun b₁ b₂ b₃ h n ↦ by
  simp_all; intro h''
  have : (none : ℕ∞) = (⊤ : ℕ∞) := rfl
  if b₁ = ⊤ then
    subst_eqs
    simp_all
    rcases b₂ with _ | b₂ <;> try simp_all
    · exact h n rfl
    · exact h n rfl
  else
    rcases b₂ with _ | b₂ <;> rcases b₁ with _ | b₁ <;> rcases b₃ with _ | b₃ <;> simp_all
    · have : b₁ = n := ENat.coe_inj.mp h''
      subst_eqs
      exists n ⊓ b₂
      simp_all
      rfl
    · suffices n = b₁ ⊓ b₃ by
        simp_all
        subst_eqs
        exists b₁ ⊓ b₂ ⊓ b₃
        simp_all
        have : b₂ ≤ b₃ := ENat.coe_le_coe.mp h
        have : b₂ ⊓ b₃ = b₂ := by simp_all
        simp_all
        rfl
      refine ENat.coe_inj.mp ?_
      symm at h''
      simp_all
      rfl⟩
instance : MulLeftMono ENat' := ⟨fun b₁ b₂ b₃ h ↦ by
  simp_all
  have : ∀ {b₁ b₂ b₃ : ℕ∞} (h : b₂ ≤ b₃), b₁ + b₂ ≤ b₁ + b₃ := fun h ↦ add_le_add_left h _
  apply this h⟩

open scoped Classical in
/- **Combinatorics** via the (extended) **Natural Numbers semiring** -/
example : wp[ℕ,ENat',ENat',String]⟦x := 1; {⊙ x} ⊕ {⊙2}⟧(1) = wght {3} := by
  simp [wGCL.wp, Subst.subst]
  norm_cast

end ENat

section Bottleneck

def Bottleneck := EReal

noncomputable instance : LinearOrder Bottleneck := inferInstanceAs (LinearOrder EReal)
noncomputable instance : CompleteLattice Bottleneck := inferInstanceAs (CompleteLattice EReal)
noncomputable instance : OmegaCompletePartialOrder Bottleneck :=
  inferInstanceAs (OmegaCompletePartialOrder EReal)
noncomputable instance : OrderBot Bottleneck := inferInstanceAs (OrderBot EReal)
noncomputable instance : OrderTop Bottleneck := inferInstanceAs (OrderTop EReal)

noncomputable instance : Add Bottleneck := ⟨fun a b ↦ a ⊔ b⟩
noncomputable instance : Mul Bottleneck := ⟨fun a b ↦ a ⊓ b⟩
noncomputable instance : Zero Bottleneck := ⟨⊥⟩

@[simp] theorem Bottleneck.add_eq_inf (a b : Bottleneck) : a + b = a ⊔ b := rfl
@[simp] theorem Bottleneck.mul_eq_add (a b : Bottleneck) : a * b = a ⊓ b := rfl
@[simp] theorem Bottleneck.bot_le (a : Bottleneck) : ⊥ ≤ a := OrderBot.bot_le a
@[simp] theorem Bottleneck.le_top (a : Bottleneck) : a ≤ ⊤ := OrderTop.le_top a
@[simp] theorem Bottleneck.zero_eq_bot : (0 : Bottleneck) = ⊥ := rfl

noncomputable instance : Semiring Bottleneck where
  add_assoc a b c := max_assoc a b c
  zero_add := by simp
  add_zero := by simp
  nsmul n x := if n = 0 then ⊥ else x
  add_comm := by simp [max_comm]
  left_distrib := by simp [inf_sup_left]
  right_distrib := by simp [inf_sup_right]
  zero_mul := by simp
  mul_zero := by simp
  mul_assoc := by simp [min_assoc]
  one := ⊤
  one_mul := by simp; exact fun _ ↦ le_top
  mul_one := by simp; exact fun _ ↦ le_top
  nsmul_zero := by simp
  nsmul_succ n := by split_ifs <;> simp_all

instance : AddLeftMono Bottleneck := ⟨fun a b c h ↦ by simp_all; exact LE.le.le_or_le h a⟩
instance : MulLeftMono Bottleneck := ⟨fun a b c h ↦ by simp_all⟩

/- **Optimization** via the **Bottleneck semiring** -/
open scoped Classical in
example :
    wp[ℕ,Bottleneck,Bottleneck,Var]⟦if (~(· x < 2)) { ⊙ 1 } else { ⊙ 2 }⟧(1) ≤ wght {2} := by
  intro σ
  simp [wGCL.wp, Subst.subst, BExpr.iver, BExpr.not]
  if h' : σ x < 2 then simp_all [Nat.not_le_of_lt]; exact Preorder.le_refl 1
  else simp_all [Nat.not_lt.mpr]

end Bottleneck

section FormalLanguages

variable {Γ : Type}

attribute [local simp] HSMul.hSMul attribute [local simp] SMul.smul
attribute [local simp] HMul.hMul   attribute [local simp] Mul.mul
attribute [local simp] HAdd.hAdd   attribute [local simp] Add.add

abbrev ε : List Γ := []

scoped instance : Monoid (List Γ) where
  mul := List.append
  mul_assoc := List.append_assoc
  one := ε
  one_mul := by simp; rfl
  mul_one := by simp [HMul.hMul]; rfl

@[simp] theorem one_append {w : List Γ} : 1 ++ w = w := List.append_left_eq_self.mpr rfl

scoped instance : DistribMulAction (List Γ) (Language Γ) where
  smul w S := (w ++ ·) '' S
  one_smul S := by ext w'; simp
  mul_smul w₁ w₂ S := by ext w; simp; rw [Set.mem_image, Set.mem_image]; simp
  smul_zero w := by simp; apply Set.image_empty
  smul_add w S₁ S₂ := by
    ext w'; simp; rw [Set.mem_image, Set.mem_union, Set.mem_image, Set.mem_image]; aesop

scoped instance : CovariantClass (List Γ) (Language Γ) HSMul.hSMul LE.le :=
  ⟨fun _ _ _ _ _ ↦ by aesop⟩

@[simp] scoped instance : Coe (List Γ) (𝕎 (List Γ) (Mem ℕ Var)) := ⟨fun S _ ↦ S⟩
@[simp] scoped instance : Singleton (List Γ) (Weighting ℕ (Language Γ) Var) := ⟨fun S _ ↦ {S}⟩
@[simp] scoped instance : Insert (List Γ) (Weighting ℕ (Language Γ) Var) :=
  ⟨fun w S σ ↦ insert w (S σ)⟩

@[simp] theorem Language.mem_singleton_iff : a ∈ ({b} : Language Γ) ↔ a = b := Eq.to_iff rfl
@[simp] theorem Language.mem_insert_iff {S : Language Γ} : a ∈ insert b S ↔ a = b ∨ a ∈ S :=
  Set.mem_insert_iff

/- **Model Checking** via the **Formal languages semiring** -/
open scoped Classical in
example {a b c d : Γ} :
    wp[ℕ,Language Γ,List Γ,Var]⟦
      ⊙ ~[a] ;
      skip ;
      ⊙ ~[b] ;
      { ⊙ ~[c] } ⊕ { ⊙ ~[d] }
    ⟧(~{ε}) = {[a,b,c], [a,b,d]} := by
  ext σ w; simp [wGCL.wp]; rw [Set.mem_image]; aesop

/- **Model Checking** via the **Formal languages semiring** -/
open scoped Classical in
example {a b c: Γ} :
    wp[ℕ,Language Γ,List Γ,Var]⟦
      ⊙ ~[a] ;
      ⊙ ~(if · x = 12 then [b] else [c])
    ⟧(~{ε}) ≤ {[a,b], [a,c]} := by
  intro σ w; simp [wGCL.wp]
  intro w' h h'
  have := Language.mem_singleton_iff.mp h; subst_eqs
  split_ifs <;> simp_all [Language.mem_insert_iff.mpr]

end FormalLanguages

section Tropical

open OmegaCompletePartialOrder

open scoped Classical in
noncomputable instance : SupSet (Tropical ℕ∞) where
  -- TODO: this is a bogus instance loosely based on the Real.instSupSet
  sSup S := if h : S.Nonempty ∧ BddAbove S then h.right.choose else 0

/-- The set of upper bounds of a set. -/
def Chain.upperBounds [Preorder α] (s : Chain α) : Set α :=
  { x | ∀ ⦃a⦄, a ∈ s → a ≤ x }

/-- A set is bounded above if there exists an upper bound. -/
def Chain.BddAbove [Preorder α] (s : Chain α) :=
  (upperBounds s).Nonempty

def Chain.BddAbove_choose_spec [Preorder α] {s : Chain α} (h : Chain.BddAbove s) :
    ∀ ⦃a : α⦄, a ∈ s → a ≤ h.choose := h.choose_spec

instance : OrderBot (Tropical ℕ∞) where
  bot := ⊤
  bot_le a := sorry

noncomputable instance : CompleteLinearOrder ℕ∞ := inferInstance
noncomputable instance : CompleteLattice ℕ∞ := inferInstance
noncomputable instance : PartialOrder (Tropical ℕ∞) := inferInstance

open scoped Classical in
noncomputable instance : OmegaCompletePartialOrder (Tropical ℕ∞) where
  ωSup S := if h : Chain.BddAbove S then h.choose else ⊤
  le_ωSup C n := by
    split_ifs with h
    · apply Chain.BddAbove_choose_spec h
      simp [Chain.instMembership]
    · simp_all
  ωSup_le C n h := by
    split_ifs with h'
    · have := Chain.BddAbove_choose_spec h'
      simp_all
      sorry
    · simp [Chain.BddAbove, Chain.upperBounds, Set.Nonempty] at h'
      have := h' n
      sorry

/- **Optimization** via the **Tropical semiring** -/
open scoped Classical in
example : wp[ℕ,Tropical ℕ∞,Tropical ℕ∞,Var]⟦if (~(· x < 2)) {⊙ 1} else {⊙ 2}⟧(1) ≤ wght {2} := by
  intro σ
  simp [wGCL.wp, Subst.subst, BExpr.iver, BExpr.not]
  if h : σ x < 2 then simp_all [Nat.not_le_of_lt]; norm_cast
  else simp_all [Nat.not_lt.mpr]

end Tropical

def SkiRental (n : Var) (y : Var) [∀ n, OfNat W n] : wGCL ℕ W Var := wgcl {
  while (~(0 < · n)) {
    ~n := ~(· n - 1) ;
    {⊙ 1} ⊕ { ⊙ ~(OfNat.ofNat <| · y); ~n := 0 }
  }
}

variable [DecidableEq Var]
variable [(B : BExpr ℕ String) → (σ : Mem ℕ String) → Decidable (B σ)]

@[simp] noncomputable instance {n : ℕ} : OfNat ENat' n := ⟨n⟩

example :
    wp[ℕ,ENat',ENat',String]⟦~(SkiRental n y)⟧(1) ≤ fun σ ↦ (σ n : ENat') + σ y := by
  simp [SkiRental]
  apply wGCL.wp_le_of_le
  intro σ
  simp [wGCL.Φ, BExpr.iver, BExpr.not, wGCL.wp, Subst.subst]
  split_ifs with h₁ h₂ h₃ <;> subst_eqs <;> (try simp_all) <;> norm_cast
  · left
    generalize h : σ n = m
    rw [h] at h₃
    rcases m with _ | m
    · simp
    · simp_all
      clear h
      sorry
  · left; left; left
    sorry
  · right
    sorry

end WGCL
