import WGCL.Syntax
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.ENNReal.Operations
import Mathlib.Order.FixedPoints
import Mathlib.Order.Notation
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Order

class Subst (W Var E : Type) where
  /-- Written using `a[x ↦ e]`. Substitutes all `x` in `a` with `e`. -/
  subst : W → Var → E → W

@[inherit_doc Subst.subst]
syntax:max term noWs "[" withoutPosition(term) ppHardSpace "↦" ppHardSpace withoutPosition(term) "]"
  : term
macro_rules | `($x[$i ↦ $j]) => `(Subst.subst $x $i $j)

open Lean PrettyPrinter Delaborator SubExpr in
@[app_unexpander Subst.subst]
def Subst.substUnexpander : Unexpander
| `($(_) $m $x $v) => `($m[$x ↦ $v])
| _ => throw ()

instance [BEq α] [Hashable α] : Subst (Std.HashMap α β) α β where
  subst m x v := m.insert x v

section

variable (𝒲 : Type) (ℳ : Type)
variable [Monoid 𝒲] [AddCommMonoid ℳ]

alias MonoidModule := DistribMulAction

variable [DistribMulAction 𝒲 ℳ] (v w : 𝒲) (a b : ℳ)

/-- (1) Scalar multiplication is associative. -/
example : (v * w) • a = v • (w • a) := MulAction.mul_smul v w a
/-- (2) Scalar multiplication is distributive. -/
example : v • (a + b) = (v • a) + (v • b) := DistribSMul.smul_add v a b
/-- (3) Scalar multiplication by one is identity. -/
example : v • (0 : ℳ) = 0 := DistribMulAction.smul_zero v

variable (Var : Type)

abbrev 𝕎 (ℳ : Type) (Var : Type) := Var → ℳ

instance Pi.instDistribMulAction : DistribMulAction 𝒲 (ι → ℳ) where
  smul_zero := by simp
  smul_add := by simp

instance : DistribMulAction 𝒲 (𝕎 ℳ Var) := Pi.instDistribMulAction 𝒲 ℳ

instance {𝒮 : Type} [inst : Semiring 𝒮] : DistribMulAction 𝒮 𝒮 where
  smul_zero := by simp
  smul_add a b c := by simp [left_distrib]

class OmegaCompleteSemiring (𝒮 : Type) [TopologicalSpace 𝒮] extends Semiring 𝒮 where
  protected sum_mul_left {f : ι → 𝒮} {a : 𝒮} : ∑' x, a * f x = a * ∑' x, f x
  protected sum_mul_right {f : ι → 𝒮} {a : 𝒮} : ∑' x, f x * a = (∑' x, f x) * a
  protected sum_biUnion {S : Set ι} {f : α → 𝒮} {t : ι → Set α}
    (h : S.PairwiseDisjoint t) : ∑' x : ⋃ i ∈ S, t i, f x = ∑' (i : S), ∑' (x : t i), f x

end

namespace List

def pairs (l : List α) : List (α × α) := match l with
  | a :: b :: tail => (a, b) :: (b :: tail).pairs
  | _ => []

variable {l : List α}

@[simp]
theorem pairs_cons (h : 0 < l.length) : (a :: l).pairs = (a, l[0]) :: l.pairs := by
  induction l with
  | nil => simp_all [pairs]; simp_all [pairs]
  | cons head tail ih => simp_all [pairs]

theorem pairs_of_tail (h : (a, b) ∈ l.tail.pairs) : (a, b) ∈ l.pairs := by
  induction l with
  | nil => simp_all [pairs]
  | cons head tail ih =>
    simp_all [pairs]
    if 0 < tail.length then
      simp_all
    else
      simp_all [pairs]

@[simp] theorem pairs_empty : ([] : List α).pairs = [] := by simp [pairs]

@[simp]
theorem succ_mem_pairs (h : n + 1 < l.length) : (l[n], l[n + 1]) ∈ l.pairs := by
  induction l generalizing n with
  | nil => simp_all; simp_all
  | cons head tail ih =>
    simp at h
    simp_all
    rw [getElem_cons]
    split_ifs
    · subst_eqs
      rw [List.pairs_cons h]
      simp
    · rw [List.pairs_cons]
      · simp_all
        right
        have := ih (n:=n - 1) (by simp_all; omega)
        convert this
        omega
      · omega

end List

namespace WGCL

variable {W Var : Type}

variable [Semiring W]
variable [CompleteLattice W]

set_option linter.unusedVariables false in
def AExpr.eval (E : AExpr Var) (σ : Mem W Var) : W :=
  match E with
  | .Const n => n
  | .Var x => σ x
  | wgcl_aexpr {~l + ~ r} => l.eval σ + r.eval σ
  | wgcl_aexpr {~l - ~ r} => 0 -- TODO: l.eval σ - r.eval σ
  | wgcl_aexpr {~l * ~ r} => l.eval σ * r.eval σ
  | wgcl_aexpr {~l / ~ r} => 0 -- TODO: l.eval σ / r.eval σ
  | wgcl_aexpr {-~l} => 0 -- TODO: -l.eval σ
def BExpr.eval (B : BExpr Var) (σ : Mem W Var) : Prop :=
  match B with
  | .Const b => b
  | wgcl_bexpr { ~l ∧ ~ r } => l.eval σ ∧ r.eval σ
  | wgcl_bexpr { ~l ∨ ~ r } => l.eval σ ∨ r.eval σ
  | wgcl_bexpr { ~l → ~ r } => l.eval σ → r.eval σ
  | wgcl_bexpr { ~l ↔ ~ r } => l.eval σ ↔ r.eval σ
  | wgcl_bexpr { ~l < ~ r } => l.eval σ < r.eval σ
  | wgcl_bexpr { ~l ≤ ~ r } => l.eval σ ≤ r.eval σ
  | wgcl_bexpr { ~l ≥ ~ r } => l.eval σ ≥ r.eval σ
  | wgcl_bexpr { ~l > ~ r } => l.eval σ > r.eval σ
  | wgcl_bexpr { ~l = ~ r } => l.eval σ = r.eval σ
  | wgcl_bexpr { ~l ≠ ~ r } => l.eval σ ≠ r.eval σ
  | .Uni .Not l => ¬l.eval σ

def BExpr.not (B : BExpr Var) : BExpr Var := .Uni .Not B

variable [DecidableEq Var]

instance : Subst (Mem W Var) Var W where
  subst σ x v := fun y ↦ if x = y then v else σ y

instance : Subst (Weigting W Var) Var (AExpr Var) where
  subst f x E := fun σ ↦ f σ[x ↦ E.eval σ]

theorem Weigting.subst_mono {f₁ f₂ : Weigting W Var} (h : f₁ ≤ f₂) (x : Var) (y : AExpr Var) :
    f₁[x ↦ y] ≤ f₂[x ↦ y] := by
  intro σ
  exact h fun y_1 => if x = y_1 then y.eval σ else σ y_1

variable [∀ (B : BExpr Var) (σ : Mem W Var), Decidable (B.eval σ)]

def BExpr.iver (B : BExpr Var) : Weigting W Var := fun σ ↦ if B.eval σ then 1 else 0

/-- A version of `OrderHom.lfp` that does not require `f` the `Monotone` upfront. -/
protected def wp.lfp {α} [CompleteLattice α] (f : α → α) : α := sInf {a | f a ≤ a}

namespace wp.lfp

variable [CompleteLattice α]

theorem monotone : Monotone (wp.lfp (α:=α)) := by
  intro f g h
  simp_all [wp.lfp]
  intro x h'
  apply sInf_le
  simp [le_trans (h x) h']

@[simp] theorem wp_lfp_eq_lfp (f : α → α) (h : Monotone f) : wp.lfp f = OrderHom.lfp ⟨f, h⟩ := rfl
@[simp] theorem wp_lfp_eq_lfp_OrderHom (f : α →o α) : wp.lfp f = OrderHom.lfp f := rfl

end wp.lfp

instance : Semiring (Weigting W Var) := Pi.semiring
instance : CompleteLattice (Weigting W Var) := Pi.instCompleteLattice

@[simp]
instance : HMul W (Weigting W Var) (Weigting W Var) where
  hMul w f := fun σ ↦ w * f σ

def wGCL.wp (C : wGCL W Var) (f : Weigting W Var) : Weigting W Var := match C with
| wgcl { ~x := ~E }                     => f[x ↦ E]
| wgcl { ~C₁; ~C₂ }                     => C₁.wp (C₂.wp f)
| wgcl { if (~φ) { ~C₁ } else { ~C₂ } } => φ.iver * C₁.wp f + φ.not.iver * C₂.wp f
| wgcl { { ~C₁ } ⊕ { ~C₂ } }            => C₁.wp f + C₂.wp f
| wgcl { ⊙ ~a }                         => a * f
| wgcl { while (~φ) { ~C' } }           => wp.lfp fun X ↦ φ.iver * C'.wp X + φ.not.iver * f

@[simp] theorem wGCL.wp_assign {f : Weigting W Var} :
    (wgcl{~x := ~E}).wp f = f[x ↦ E] := by simp [wp]
@[simp] theorem wGCL.wp_seq {f : Weigting W Var} :
    (wgcl{~C₁; ~C₂}).wp f = C₁.wp (C₂.wp f) := by simp [wp]
@[simp] theorem wGCL.wp_ite {f : Weigting W Var} :
    (wgcl{if (~φ) {~C₁} else {~C₂}}).wp f = φ.iver * C₁.wp f + φ.not.iver * C₂.wp f := by simp [wp]
@[simp] theorem wGCL.wp_branch {f : Weigting W Var} :
    (wgcl{{ ~C₁ } ⊕ { ~C₂ }}).wp f = C₁.wp f + C₂.wp f := by simp [wp]
@[simp] theorem wGCL.wp_weight {f : Weigting W Var} :
    (wgcl{⊙ ~a}).wp f = a * f := by simp [wp]

variable [AddRightMono W] [AddLeftMono W] [MulLeftMono W]

attribute [local simp] Function.swap
instance : AddRightMono (Weigting W Var) := ⟨by intro f₁ f₂ f₃ h σ; simp; gcongr; apply_assumption⟩
instance : AddLeftMono  (Weigting W Var) := ⟨by intro f₁ f₂ f₃ h σ; simp; gcongr; apply_assumption⟩
instance : MulLeftMono  (Weigting W Var) := ⟨by intro f₁ f₂ f₃ h σ; simp; gcongr; apply_assumption⟩

theorem wGCL.wp_monotone (C : wGCL W Var) : Monotone C.wp := by
  induction C with (intro f₁ f₂ h; simp only [wp])
  | Branch C₁ C₂ ih₁ ih₂ => gcongr <;> (apply_assumption; assumption)
  | Weighting => gcongr
  | Assign => apply Weigting.subst_mono h
  | Ite => gcongr <;> apply_assumption <;> assumption
  | Seq => repeat (first | apply_assumption | assumption)
  | While => exact wp.lfp.monotone fun f ↦ by gcongr

@[simp]
theorem wGCL.wp_while {C' : wGCL W Var} :
    wgcl { while (~φ) { ~C' } }.wp = fun f ↦ OrderHom.lfp ⟨fun X ↦ φ.iver * C'.wp X + φ.not.iver * f, by
      intro f₁ f₂ h
      simp
      gcongr
      exact wp_monotone _ h⟩
:= rfl

instance {n : ℕ} : OfNat Bool n := ⟨n % 2 == 1⟩
-- instance : Semiring Bool where

def P₁ : wGCL ℕ String := wgcl {
  x := 0; y := 1;
  while (x ≠ p) {
    if (x < y) { ⊙1; x := x + 1 }
    else { ⊙1; x := x - 1 };
    if (x = y) { y := -2 * y }
  }
}

/--
info: wgcl {x := 0; y := 1; while (x ≠ p) {
        if (x < y) {
            ⊙1; x := x + 1
          } else {
            ⊙1; x := x - 1
          }; if (x = y) {
            y := -2 * y
          }
      }}
-/
#guard_msgs in
#eval P₁

inductive Act | N | L | R deriving Lean.ToExpr

structure Conf (W : Type) (Var : Type) where
  C : WithBot (wGCL W Var)
  σ : Mem W Var
  n : W
  β : List Act

section Syntax

open Lean PrettyPrinter Delaborator SubExpr

syntax "conf" ppHardSpace "⟨" cwgcl_progr "," term "," term "," term "⟩" : term
syntax "conf" ppHardSpace "⟨" "⊥" "," term "," term "," term "⟩" : term

macro_rules
| `(conf ⟨⊥, $σ, $n, $β⟩) => `(({C:=⊥,σ:=$σ,n:=$n,β:=$β} : Conf _ _))
| `(conf ⟨$C, $σ, $n, $β⟩) => `(({C:=some wgcl{$C},σ:=$σ,n:=$n,β:=$β} : Conf _ _))

@[app_unexpander Conf.mk]
def Conf.unexpand : Unexpander
| `($(_) ⊥ $σ $n $β) => `(conf ⟨⊥, $σ, $n, $β⟩)
| `($(_) $C $σ $n $β) =>
  match C with
  | `($_ wgcl {$C}) => `(conf ⟨$C, $σ, $n, $β⟩)
  | _ => throw ()
-- | `($(_) (some (wgcl{$C})) $σ $n $β) => `(conf ⟨$C, $σ, $n, $β⟩)
| _ => throw ()

end Syntax

/-- info: fun σ n β ↦ conf ⟨⊥,σ,n,β⟩ : Mem W String → W → List Act → Conf W String -/
#guard_msgs in
#check fun (σ : Mem W String) n β ↦ conf ⟨⊥, σ, n, β⟩

/-- info: fun σ n β ↦ conf ⟨x := E,σ,n,β⟩ : Mem W String → W → List Act → Conf W String -/
#guard_msgs in
#check fun (σ : Mem W String) n β ↦ conf ⟨x := E, σ, n, β⟩

syntax "op_rule" ppHardSpace
  "⟨" cwgcl_progr "," term "," term "," term "⟩"
  "⊢[" term "]"
  "⟨" cwgcl_progr "," term "," term "," term "⟩"
  : term
syntax "⊥" : cwgcl_progr

@[aesop safe [constructors, cases]]
inductive Op : Conf W Var → W → Conf W Var → Prop where
  | Assign : Op (conf ⟨~x := ~E, σ, n, β⟩) 1 (conf ⟨⊥, σ[x ↦ E.eval σ], n+1, β⟩)
  | Weight : Op (conf ⟨⊙ ~a, σ, n, β⟩) a (conf ⟨⊥, σ, n+1, β⟩)
  | Seq₁ :
      Op (conf ⟨~C₁, σ, n, β⟩) a (conf ⟨⊥, σ', n+1, β⟩) →
    Op (conf ⟨~C₁ ; ~C₂, σ, n, β⟩) a (conf ⟨~C₂, σ', n+1, β⟩)
  | Seq₂ :
      Op (conf ⟨~C₁, σ, n, β⟩) a (conf ⟨~C₁', σ', n+1, β⟩) →
    Op (conf ⟨~C₁ ; ~C₂, σ, n, β⟩) a (conf ⟨~C₁' ; ~C₂, σ', n+1, β⟩)
  | If : (h : φ.eval σ) →
    Op (conf ⟨if (~φ) {~C₁} else {~C₂}, σ, n, β⟩) 1 (conf ⟨~C₁, σ, n+1, β⟩)
  | Else : (h : ¬φ.eval σ) →
    Op (conf ⟨if (~φ) {~C₁} else {~C₂}, σ, n, β⟩) 1 (conf ⟨~C₂, σ, n+1, β⟩)
  | BranchL :
    Op (conf ⟨{~C₁} ⊕ {~C₂}, σ, n, β⟩) 1 (conf ⟨~C₁, σ, n+1, .L::β⟩)
  | BranchR :
    Op (conf ⟨{~C₁} ⊕ {~C₂}, σ, n, β⟩) 1 (conf ⟨~C₂, σ, n+1, .R::β⟩)
  | While : (h : φ.eval σ) →
    Op (conf ⟨while (~φ) {~C}, σ, n, β⟩) 1 (conf ⟨~C ; while (~φ) {~C}, σ, n+1, β⟩)
  | Break : (h : ¬φ.eval σ) →
    Op (conf ⟨while (~φ) {~C}, σ, n, β⟩) 1 (conf ⟨⊥, σ, n+1, β⟩)

set_option quotPrecheck false in
macro_rules
| `(wgcl {⊥}) => `(⊥)
| `(op_rule ⟨$C, $σ, $n, $β⟩ ⊢[$a] ⟨$C', $σ', $n', $β'⟩) =>
  `(Op (conf ⟨$C,$σ,$n,$β⟩) $a (conf ⟨$C',$σ',$n',$β'⟩))

@[simp]
theorem Op.branch_iff {C₁ C₂ : wGCL W Var} :
      Op (conf ⟨{~C₁} ⊕ {~C₂}, σ, n, β⟩) a r
    ↔ a = 1 ∧ (r = conf ⟨~C₁, σ, n+1, .L::β⟩ ∨ r = conf ⟨~C₂, σ, n+1, .R::β⟩) := by aesop

structure Paths (W : Type) (Var : Type) [Semiring W] [CompleteLattice W] [DecidableEq Var] where
  states : List (Conf W Var)
  h_pos : 0 < states.length
  pairwise : ∀ 𝒦₁ 𝒦₂, (𝒦₁, 𝒦₂) ∈ states.pairs → ∃ a, Op 𝒦₁ a 𝒦₂

@[simp] def Paths.length_pos (π : Paths W Var) : 0 < π.states.length := π.h_pos
@[simp] def Paths.nonempty (π : Paths W Var) : π.states ≠ [] :=
  List.ne_nil_of_length_pos (π.length_pos)
def Paths.last (π : Paths W Var) : Conf W Var := π.states.getLast (by simp)
def Paths.IsTerminal (π : Paths W Var) : Prop := π.last.C = ⊥

def TPaths (𝒦₀ : Conf W Var) : Set (Paths W Var) :=
  ⋃ n, {π | π.states.length = n ∧ π.states[0] = 𝒦₀ ∧ π.IsTerminal}

noncomputable def Conf.wgt (𝒦₁ 𝒦₂ : Conf W Var) : W :=
  have : Decidable (∃ α, Op 𝒦₁ α 𝒦₂) := Classical.propDecidable _
  if h : ∃ α, Op 𝒦₁ α 𝒦₂ then h.choose else 0

noncomputable def Paths.wgt (π : Paths W Var) : W :=
  π.states.pairs.map (fun (𝒦₁, 𝒦₂) ↦ 𝒦₁.wgt 𝒦₂) |>.sum

variable [TopologicalSpace W]

noncomputable def wGCL.op (C : wGCL W Var) (f : Weigting W Var) : Weigting W Var :=
  fun σ ↦ ∑' π : TPaths (conf ⟨~C, σ, 0, []⟩), π.val.wgt * f π.val.last.σ

def Succs (C : wGCL W Var) (σ : Mem W Var) :=
  { (a, C', σ') | ∃ n β β', Op (conf ⟨~C, σ, n, β⟩) a ⟨C', σ', n+1, β'⟩ }

noncomputable def wGCL.Φ (c : wGCL W Var → Weigting W Var → Weigting W Var) (C : wGCL W Var)
    (f : Weigting W Var) : Weigting W Var :=
  fun σ ↦ ∑' X : Succs C σ, match X with | ⟨⟨a, some C', σ'⟩, _⟩ => a * c C' f σ' | _ => 0


open OrderHom

variable [DecidableEq Var]
variable [Semiring W] [CompleteLattice W]
variable [TopologicalSpace W]
variable [IsOrderedAddMonoid W]
variable [SupConvergenceClass W] [CanonicallyOrderedAdd W]

@[simp] theorem W_hasSum {f : α → W} : HasSum f (⨆ s : Finset α, ∑ a ∈ s, f a) :=
  tendsto_atTop_iSup fun _ _ ↦ Finset.sum_le_sum_of_subset
@[simp] theorem W_summable {f : α → W} : Summable f := ⟨_, W_hasSum⟩

variable [OrderClosedTopology W]
variable [AddRightMono W] [AddLeftMono W] [MulLeftMono W]

variable [(B : BExpr Var) → (σ : Mem W Var) → Decidable (B.eval σ)]

def wGCL.Φ_mono : Monotone (Φ (W:=W) (Var:=Var)) := by
  intro v₁ v₂ h C f σ
  simp only [Φ]
  apply Summable.tsum_le_tsum _ (by simp) (by simp)
  intro
  split
  · gcongr
    apply_assumption
  · rfl

@[simp]
def Succs_Branch {σ : Mem W Var} :
    Succs (wgcl { {~C₁} ⊕ {~C₂} }) σ = {(1, some C₁, σ), (1, some C₂, σ)} := by
  ext X
  simp [Succs]
  constructor
  · aesop
  · aesop
@[simp]
def Succs_Assign {σ : Mem W Var} : Succs (wgcl {~x := ~E}) σ = {(1, ⊥, σ[x ↦ E.eval σ])} := by
  ext X
  simp [Succs]
  constructor
  · aesop
  · rintro ⟨_⟩; have n := 0; use n, [], []; apply Op.Assign
@[simp]
def Succs_Weight {σ : Mem W Var} : Succs (wgcl {⊙ ~E}) σ = {(E, ⊥, σ)} := by
  ext X
  simp [Succs]
  constructor
  · aesop
  · rintro ⟨_⟩; have n := 0; use n, [], []; apply Op.Weight
@[simp]
def Succs_Ite {σ : Mem W Var} :
      Succs (wgcl {if (~φ) { ~C₁ } else { ~C₂ }}) σ
    = if φ.eval σ then {(1, some C₁, σ)} else {(1, some C₂, σ)} := by
  ext X
  simp [Succs]
  constructor
  · aesop
  · split_ifs
    · rintro ⟨_⟩; have n := 0; use n, [], []; apply Op.If (by assumption)
    · rintro ⟨_⟩; have n := 0; use n, [], []; apply Op.Else (by assumption)
@[simp]
def Succs_Ite_If {σ : Mem W Var} (h : φ.eval σ) :
    Succs (wgcl {if (~φ) { ~C₁ } else { ~C₂ }}) σ = {(1, some C₁, σ)} := by
  simp_all
@[simp]
def Succs_Ite_Else {σ : Mem W Var} (h : ¬φ.eval σ) :
    Succs (wgcl {if (~φ) { ~C₁ } else { ~C₂ }}) σ = {(1, some C₂, σ)} := by
  simp_all
@[simp]
def Succs_While {σ : Mem W Var} :
      Succs (wgcl {while (~φ) { ~C }}) σ
    = if φ.eval σ then {(1, some wgcl {~C ; while (~φ) { ~C }}, σ)} else {(1, none, σ)} := by
  ext X
  simp [Succs]
  constructor
  · aesop
  · split_ifs
    · rintro ⟨_⟩; have n := 0; use n, [], []; apply Op.While (by assumption)
    · rintro ⟨_⟩; have n := 0; use n, [], []; apply Op.Break (by assumption)

theorem tsum_eq_pair {α : Type u_1} {β : Type u_2} [DecidableEq β] [AddCommMonoid α]
    [TopologicalSpace α] {f : β → α} (b₁ b₂ : β) (hf : ∀ (b' : β), b' ≠ b₁ ∧ b' ≠ b₂ → f b' = 0) :
∑' (b : β), f b = if b₁ = b₂ then f b₁ else f b₁ + f b₂ := by
  rw [tsum_eq_sum (s:={b₁, b₂})]
  · split_ifs <;> simp_all
  · simp_all

def Paths.prepend (π : Paths W Var) (c : Conf W Var) : Paths W Var where
  states := c :: π.states
  h_pos := by simp
  pairwise := by
    simp [π.pairwise]
    rintro 𝒦₁ 𝒦₂ (⟨_, h⟩ | h)
    · subst_eqs
      sorry
    · simp_all [π.pairwise]
def Paths.tail (π : Paths W Var) : Paths W Var where
  states := if π.states.length = 1 then π.states else π.states.tail
  h_pos := by split_ifs <;> simp_all; have := π.h_pos; omega
  pairwise := by
    split_ifs
    · simp_all [π.pairwise]
    · intro 𝒦₁ 𝒦₂
      exact π.pairwise 𝒦₁ 𝒦₂ ∘ List.pairs_of_tail

@[simp]
theorem TPaths.branch {C₁ C₂ : wGCL W Var} :
      TPaths (conf ⟨{~C₁} ⊕ {~C₂}, σ, 0, []⟩)
    = (·.prepend (conf ⟨{~C₁} ⊕ {~C₂}, σ, 0, []⟩))
      '' (TPaths (conf ⟨~C₁, σ, 1, .L::[]⟩) ∪ TPaths (conf ⟨~C₂, σ, 1, .R::[]⟩)) := by
  ext π
  simp [TPaths, Paths.prepend]
  constructor
  · intro ⟨h₁, h₂⟩
    have : ¬π.states.length = 1 := by
      intro h
      simp_all [Paths.tail, Paths.IsTerminal, Paths.last, List.getLast_eq_getElem]
    use π.tail
    simp_all [Paths.tail, Paths.IsTerminal, Paths.last]
    obtain ⟨a, h⟩ := π.pairwise π.states[0] (π.states[1]'(by have := π.h_pos; omega)) (by simp)
    simp_all
    obtain ⟨_, _, _⟩ := π
    obtain ⟨_, (⟨_⟩ | ⟨_⟩)⟩ := h
    · subst_eqs; simp_all [List.cons_head?_tail, List.head?_eq_getElem?]
    · subst_eqs; simp_all [List.cons_head?_tail, List.head?_eq_getElem?]
  · rintro ⟨_, (⟨_, _⟩ | ⟨_, _⟩), _, _⟩
    · simp_all [Paths.tail, Paths.IsTerminal, Paths.last]
    · simp_all [Paths.tail, Paths.IsTerminal, Paths.last]

@[simp]
theorem wGCP.op_branch {C₁ C₂ : wGCL W Var} : (C₁.Branch C₂).op = C₁.op + C₂.op := by
  ext f σ
  simp [wGCL.op]
  rw [TPaths.branch]
  rw [@Set.image_union]
  -- rw [Summable.tsum_union_disjoint]


  sorry

theorem wGCL.Φ_op_le_op : Φ (W:=W) (Var:=Var) op ≤ op := by
  have : DecidableEq (W × WithBot (wGCL W Var) × Mem W Var) := Classical.typeDecidableEq _
  intro C
  induction C with
  | Branch C₁ C₂ ih₁ ih₂ =>
    intro f σ; simp [Φ]
    sorry
    -- rw [tsum_eq_pair ⟨(1, some C₁, σ), by simp⟩ ⟨(1, some C₂, σ), by simp⟩]
    -- · split_ifs <;> simp_all
    -- · simp_all only [ne_eq, and_imp, Subtype.forall, Succs_Branch, Set.mem_insert_iff,
    --   Set.mem_singleton_iff, Subtype.mk.injEq, Prod.forall, Prod.mk.injEq, not_and]
    --   rintro w C' σ (⟨_, _, _⟩ | ⟨_, _, _⟩) <;> subst_eqs
    --   · simp
    --   · simp
  | Weighting => intro f σ; simp [Φ]
  | Assign x E => intro f σ; simp [Φ]
  | Ite => sorry
  | Seq => sorry
  | While => sorry

theorem wGCL.Φ_seq_le (v) (C₁ C₂ : wGCL W Var) : Φ v (wgcl {~C₁; ~C₂}) ≤ Φ v C₁ ∘ Φ v C₂ := by
  intro f σ
  simp
  sorry

omit [IsOrderedAddMonoid W] [SupConvergenceClass W] [CanonicallyOrderedAdd W]
  [OrderClosedTopology W] [AddRightMono W] [AddLeftMono W] [MulLeftMono W] in
theorem wGCL.Φ_while {C : wGCL W Var} (h : v wgcl {skip} = 0) :
      Φ v (wgcl { while (~φ) {~C} })
    = fun X ↦ φ.iver * v (wgcl {~C; while (~φ) {~C}}) X + φ.not.iver * v (wgcl {skip}) X := by
  ext f σ
  if h : φ.eval σ then
    simp [Φ]
    rw [tsum_eq_single ⟨(1, wgcl {~C; while (~φ) {~C}}, σ), by simp_all; rfl⟩]
    · simp_all [BExpr.iver, BExpr.not, BExpr.eval]
    · simp_all [BExpr.iver, BExpr.not, BExpr.eval]
      contrapose!
      intro; rfl
  else
    simp [Φ]
    rw [tsum_eq_single ⟨(1, ⊥, σ), by simp_all; rfl⟩]
    · simp_all [BExpr.iver, BExpr.not, BExpr.eval]
    · simp_all [BExpr.iver, BExpr.not, BExpr.eval]

theorem wGCL.Φ_wp_le_wp : Φ (W:=W) (Var:=Var) wp ≤ wp := by
  have : DecidableEq (W × WithBot (wGCL W Var) × Mem W Var) := Classical.typeDecidableEq _
  intro C
  induction C with
  | Branch C₁ C₂ ih₁ ih₂ =>
    intro f σ
    simp [Φ]
    rw [tsum_eq_pair ⟨(1, some C₁, σ), by simp⟩ ⟨(1, some C₂, σ), by simp⟩]
    · split_ifs <;> simp_all
    · simp_all only [ne_eq, and_imp, Subtype.forall, Succs_Branch, Set.mem_insert_iff,
      Set.mem_singleton_iff, Subtype.mk.injEq, Prod.forall, Prod.mk.injEq, not_and]
      rintro w C' σ (⟨_, _, _⟩ | ⟨_, _, _⟩) <;> subst_eqs
      · simp
      · simp
  | Weighting => intro f σ; simp [Φ]
  | Assign => intro f σ; simp [Φ]
  | Ite φ C₁ C₂ ih₁ ih₂ =>
    intro f σ
    if h : φ.eval σ then
      simp_all [Φ]
      rw [tsum_eq_single ⟨(1, some C₁, σ), by simp_all⟩]
      · simp_all [BExpr.iver]
      · simp_all [BExpr.iver]
    else
      simp_all [Φ]
      rw [tsum_eq_single ⟨(1, some C₂, σ), by simp_all⟩]
      · simp_all [BExpr.iver, BExpr.not, BExpr.eval]
      · simp_all [BExpr.iver]
  | Seq C₁ C₂ ih₁ ih₂ =>
    exact fun f ↦ (Φ_seq_le wp C₁ C₂ f).trans (ih₁ (Φ wp C₂ f) |>.trans (wp_monotone C₁ (ih₂ f)))
  | While φ C ih =>
    rw [wGCL.Φ_while]
    rw [wp_while]
    · intro f
      simp
      nth_rw 2 [← map_lfp]
      simp only [coe_mk]
      gcongr
      intro σ
      simp_all
    · ext; simp

theorem wGCL.op_eq_lfp_Φ : wGCL.op (W:=W) (Var:=Var) = lfp ⟨Φ, Φ_mono⟩ := by
  apply le_antisymm (le_lfp _ _) (lfp_le _ Φ_op_le_op)
  intro b h C
  simp_all only [coe_mk]
  sorry

theorem wGCL.op_isLeast (b : wGCL W Var → Weigting W Var → Weigting W Var) (h : Φ b ≤ b) : op ≤ b := by
  sorry

-- theorem wGCL.Φ_op_le_op : Φ (W:=W) (Var:=Var) op = op := by
--   funext C X σ
--   rw [op, ← MDP.map_lfp_Φ]
--   simp only [ς, OrderHom.coe_mk]
--   congr! 3 with C'
--   rcases C' with ⟨none, σ'⟩ | ⟨C', σ'⟩ | _ <;> simp [op]


theorem wGCL.wp_le_op : wp (W:=W) (Var:=Var) ≤ op := by
  intro C
  induction C with simp_all only
  | Branch C₁ C₂ ih₁ ih₂ =>
    sorry
  | Weighting => sorry
  | Assign => sorry
  | Ite φ C₁ C₂ ih₁ ih₂ => sorry
  | Seq C₁ C₂ ih₁ ih₂ => sorry
  | While φ C ih => sorry

theorem wGCL.wp.soundness :
    op (W:=W) (Var:=Var) = wp := by
  apply le_antisymm ?_ wp_le_op
  rw [op_eq_lfp_Φ]
  exact lfp_le _ Φ_wp_le_wp
