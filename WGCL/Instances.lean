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

noncomputable section TNat

def TNat := ℕ∞

@[simp] def TNat.ofENat (n : ℕ∞) : TNat := n
@[simp] def TNat.toENat (n : TNat) : ℕ∞ := n

@[simp] instance : LE TNat where le a b := a.toENat ≤ b

@[simp] instance : Bot TNat := ⟨TNat.ofENat 0⟩
@[simp] instance : Top TNat := ⟨TNat.ofENat ⊤⟩
instance : OrderBot TNat where
  bot_le a := by simp

instance : PartialOrder TNat where
  le_refl a := by simp
  le_trans a b c := by
    intro x hx
    have := le_trans (a:=a.toENat) (b:=b.toENat) (c:=c.toENat)
    simp_all
  le_antisymm a b := by
    simp_all
    intro x hx
    have := le_antisymm (a:=a.toENat) (b:=b.toENat)
    simp_all

instance : SemilatticeInf TNat where
  inf a b := if a ≤ b then a else b
  inf_le_left a b := by
    split_ifs with h
    · simp_all
    · have := inf_le_left (a:=a.toENat) (b:=b.toENat)
      simp_all
      exact h.le
  inf_le_right a b := by
    split_ifs with h
    · simp_all
    · have := inf_le_left (a:=a.toENat) (b:=b.toENat)
      simp_all
  le_inf a b c hab hac := by
    simp_all
    split_ifs
    · simp_all
    · simp_all

instance : OmegaCompletePartialOrder TNat := inferInstanceAs (OmegaCompletePartialOrder ℕ∞)

@[simp] instance : One TNat := ⟨TNat.ofENat 0⟩
@[simp] instance : Zero TNat := ⟨TNat.ofENat ⊤⟩
@[simp] instance : Add TNat := ⟨fun x y ↦ x.toENat ⊓ y.toENat⟩
@[simp] instance : Mul TNat := ⟨fun x y ↦ x.toENat + y.toENat⟩

instance : Monoid TNat where
  mul_assoc a b c := by simp_all [HMul.hMul, add_assoc]
  one_mul a := by show (TNat.ofENat 0) * a = a; simp [HMul.hMul]
  mul_one a := by show a * (TNat.ofENat 0) = a; simp [HMul.hMul]

@[simp] theorem TNat.add_eq_inf {a b : TNat} : a + b = a ⊓ b := rfl
@[simp] theorem TNat.mul_eq_add {a b : TNat} : a * b = a.toENat + b.toENat := rfl
@[simp] theorem TNat.zero_eq : (0 : TNat) = TNat.ofENat ⊤ := rfl
@[simp] theorem TNat.one_eq : (1 : TNat) = TNat.ofENat 0 := rfl
@[simp] theorem TNat.top_eq : (⊤ : TNat) = TNat.ofENat ⊤ := rfl
@[simp] theorem TNat.bot_eq : (⊥ : TNat) = TNat.ofENat ⊥ := rfl

instance : AddCommMonoid TNat where
  add_assoc a b c := by simp_all [HAdd.hAdd, inf_assoc]
  zero_add a := by
    simp_all [HAdd.hAdd, inf_assoc]
    show a ≤ TNat.ofENat ⊤; simp
  add_zero a := by
    simp_all [HAdd.hAdd, inf_assoc]
    show a ≤ TNat.ofENat ⊤; simp
  add_comm := by simp [HAdd.hAdd, inf_comm]
  nsmul n a := if n = 0 then 0 else a
  nsmul_zero := by simp
  nsmul_succ n a := by
    simp [HAdd.hAdd]; split_ifs
    · show a ≤ TNat.ofENat ⊤; simp
    · simp_all

instance : AddLeftMono TNat := ⟨fun _ ↦ by simp_all [inf_le_of_right_le]⟩

instance : CovariantClass TNat TNat HSMul.hSMul LE.le := ⟨fun _ ↦ by simp_all [add_le_add_left]⟩

instance : Semiring TNat where
  left_distrib a b c := by
    simp_all
    if h : b ≤ c then
      simp_all
      show a.toENat + b.toENat ≤ a.toENat + c.toENat
      exact add_le_add_left h a.toENat
    else
      simp_all
      replace h := h.le
      simp_all
      show a.toENat + c.toENat ≤ a.toENat + b.toENat
      exact add_le_add_left h a.toENat
  right_distrib a b c := by
    simp_all
    if h : a ≤ b then
      simp_all
      show a.toENat + c.toENat ≤ b.toENat + c.toENat
      exact add_le_add_right h c.toENat
    else
      simp_all
      replace h := h.le
      simp_all
      show b.toENat + c.toENat ≤ a.toENat + c.toENat
      exact add_le_add_right h c.toENat
  zero_mul a := by rfl
  mul_zero a := by show a.toENat + ⊤ = ⊤; exact add_top a.toENat

@[simp]
theorem ahsjdahsd : @min TNat SemilatticeInf.toMin x (@Top.top ℕ∞ WithTop.top) = x := by
  simp
  cases x
  · rfl
  · exact right_eq_inf.mp rfl

@[simp]
theorem TNat.le_top {x : ℕ∞} : @LE.le TNat Preorder.toLE x ⊤ := by
  show x ≤ ⊤; exact OrderTop.le_top x

open scoped Classical in
example :
    wp[ℕ,TNat,TNat,Var]⟦
      if (~(· x > 0)) {
        ⊙ ~fun _ ↦ .ofENat 1;
        ⊙ ~fun _ ↦ .ofENat 1
      } else {
        {⊙ ~fun _ ↦ .ofENat 2} ⊕ {⊙ ~fun _ ↦ .ofENat 3}
      }
    ⟧(~fun _ ↦ 1) = fun _ ↦ .ofENat 2 := by
  ext σ
  have : (1 : ℕ∞) + 1 = 2 := rfl
  simp [wGCL.wp, BExpr.iver, BExpr.not, HMul.hMul, Mul.mul, instENatTop, this]
  simp only [HAdd.hAdd, Add.add, instENatTop]
  have : (2 : ℕ∞) ⊓ 3 = 2 := rfl
  if 0 < σ x then
    have : ¬σ x = 0 := by omega
    simp_all
  else
    simp_all
    apply TNat.le_top

def SkiRental (n : Var) (y : Var) : wGCL ℕ TNat Var := wgcl {
  while (~(0 < · n)) {
    ~n := ~(· n - 1) ;
    {⊙ ~fun _ ↦ .ofENat 1} ⊕ { ⊙ ~(.ofENat <| · y); ~n := 0 }
  }
}

open scoped Classical in
example :
  wp[ℕ,TNat,TNat,Var]⟦~(SkiRental n y)⟧(~fun _ ↦ .ofENat 1) ≤ fun σ ↦ .ofENat (σ n * σ y)
:= by
  simp [SkiRental]
  apply wGCL.wp_le_of_le
  intro σ
  simp [wGCL.Φ, BExpr.iver, BExpr.not, wGCL.wp, Subst.subst, instENatTop]

  split_ifs <;> (try omega) <;> subst_eqs <;> try simp_all
  · generalize h : σ n = u
    have : 0 < u := by omega
    clear! n
    sorry
  · generalize hu : σ n = u
    generalize hv : σ y = v
    have : 0 < u := by omega
    clear! n y
    sorry
  · generalize hv : σ y = v
    clear! n y
    sorry

end TNat

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

/- **Model Checking** via the **Formal languages module** -/
open scoped Classical in
example {a b c d : Γ} :
    wp[ℕ,Language Γ,List Γ,Var]⟦
      ⊙ ~[a] ;
      skip ;
      ⊙ ~[b] ;
      { ⊙ ~[c] } ⊕ { ⊙ ~[d] }
    ⟧(~{ε}) = {[a,b,c], [a,b,d]} := by
  ext σ w; simp [wGCL.wp]; rw [Set.mem_image]; aesop

/- **Model Checking** via the **Formal languages module** -/
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

end WGCL
