import WGCL.Subst
import WGCL.wGCL
import WGCL.WeakestPre
import Mathlib.Topology.Algebra.InfiniteSum.Order

namespace WGCL

variable {D : Type} {M : Type} {W : Type} {Var : Type}

variable [DecidableEq Var]

inductive Act | N | L | R deriving Lean.ToExpr

structure Conf (D : Type) (W : Type) (Var : Type) where
  C : WithBot (wGCL D W Var)
  σ : Mem D Var
  n : ℕ
  β : List Act
section Syntax

noncomputable def Conf.size (κ : Conf D W Var) : ℕ :=
  match κ.C with | ⊥ => 0 | some C => 1 + sizeOf C

open Lean PrettyPrinter Delaborator SubExpr

syntax "conf" ppHardSpace "⟨" cwgcl_prog "," term "," term "," term "⟩" : term
syntax "conf" ppHardSpace "⟨" "⊥" "," term "," term "," term "⟩" : term

macro_rules
| `(conf ⟨⊥, $σ, $n, $β⟩) => `({C:=⊥,σ:=$σ,n:=$n,β:=$β : Conf _ _ _})
| `(conf ⟨$C, $σ, $n, $β⟩) => `({C:=some wgcl{$C},σ:=$σ,n:=$n,β:=$β : Conf _ _ _})

@[app_unexpander Conf.mk]
def Conf.unexpand : Unexpander
| `($(_) ⊥ $σ $n $β) => `(conf ⟨⊥, $σ, $n, $β⟩)
| `($(_) $C $σ $n $β) =>
  match C with
  | `($_ wgcl {$C}) => `(conf ⟨$C, $σ, $n, $β⟩)
  | _ => throw ()
| _ => throw ()

end Syntax

/-- info: fun σ n β ↦ conf ⟨⊥,σ,n,β⟩ : Mem D String → ℕ → List Act → Conf D ℕ String -/
#guard_msgs in
#check fun σ n β ↦ (conf ⟨⊥, σ, n, β⟩ : Conf D ℕ String)

/-- info: fun σ n β ↦ conf ⟨skip,σ,n,β⟩ : Mem D String → ℕ → List Act → Conf D ℕ String -/
#guard_msgs in
#check fun σ n β ↦ (conf ⟨skip, σ, n, β⟩ : Conf D ℕ String)

variable [Zero W] [One W]

@[aesop safe [constructors, cases]]
inductive Op : Conf D W Var → W → Conf D W Var → Prop where
  | Assign : {E : AExpr D Var} → Op (conf ⟨~x := ~E, σ, n, β⟩) 1 (conf ⟨⊥, σ[x ↦ E σ], n+1, β⟩)
  | Weight : Op (conf ⟨⊙ ~a, σ, n, β⟩) (a σ) (conf ⟨⊥, σ, n+1, β⟩)
  | Seq₁ :
      Op (conf ⟨~C₁, σ, n, β⟩) a (conf ⟨⊥, σ', n+1, β⟩) →
    Op (conf ⟨~C₁ ; ~C₂, σ, n, β⟩) a (conf ⟨~C₂, σ', n+1, β⟩)
  | Seq₂ :
      Op (conf ⟨~C₁, σ, n, β⟩) a (conf ⟨~C₁', σ', n+1, β⟩) →
    Op (conf ⟨~C₁ ; ~C₂, σ, n, β⟩) a (conf ⟨~C₁' ; ~C₂, σ', n+1, β⟩)
  | If : (h : φ σ) →
    Op (conf ⟨if (~φ) {~C₁} else {~C₂}, σ, n, β⟩) 1 (conf ⟨~C₁, σ, n+1, β⟩)
  | Else : (h : ¬φ σ) →
    Op (conf ⟨if (~φ) {~C₁} else {~C₂}, σ, n, β⟩) 1 (conf ⟨~C₂, σ, n+1, β⟩)
  | BranchL :
    Op (conf ⟨{~C₁} ⊕ {~C₂}, σ, n, β⟩) 1 (conf ⟨~C₁, σ, n+1, .L::β⟩)
  | BranchR :
    Op (conf ⟨{~C₁} ⊕ {~C₂}, σ, n, β⟩) 1 (conf ⟨~C₂, σ, n+1, .R::β⟩)
  | While : (h : φ σ) →
    Op (conf ⟨while (~φ) {~C}, σ, n, β⟩) 1 (conf ⟨~C ; while (~φ) {~C}, σ, n+1, β⟩)
  | Break : (h : ¬φ σ) →
    Op (conf ⟨while (~φ) {~C}, σ, n, β⟩) 1 (conf ⟨⊥, σ, n+1, β⟩)

def Conf.succ (κ : Conf D W Var) : Set (Conf D W Var) := {κ' | ∃ a, Op κ a κ'}

variable [DecidableEq (wGCL D W Var)]

def Conf.wgt (κ κ' : Conf D W Var) : W :=
  match _ : κ, κ' with
  | conf ⟨⊥,_,_,_⟩, conf ⟨⊥,_,_,_⟩ => 1
  | conf ⟨⊙ ~a,σ,_,_⟩, _ => a σ
  | conf ⟨~C₁ ; ~C₂,σ,n,β⟩, conf ⟨~C₁' ; ~C₂',σ',n',β'⟩ =>
    if C₂ = C₂' then conf ⟨~C₁,σ,n,β⟩.wgt conf ⟨~C₁',σ',n',β'⟩
    else 0
  | conf ⟨~C₁ ; ~C₂,σ,n,β⟩, conf ⟨~C₂',σ',n',β'⟩ =>
    if C₂ = C₂' then conf ⟨~C₁,σ,n,β⟩.wgt conf ⟨⊥,σ',n',β'⟩
    else 0
  | conf ⟨~_ := ~_,_,_,_⟩, _ => 1
  | conf ⟨{ ~_ } ⊕ { ~_},_,_,_⟩, _ => 1
  | conf ⟨if (~_) { ~_ } else { ~_},_,_,_⟩, _ => 1
  | conf ⟨while (~_) { ~_ },_,_,_⟩, _ => 1
  | _, _ => 0
termination_by κ.size
decreasing_by
· simp [Conf.size]; omega
· simp [Conf.size]; omega

attribute [simp] Conf.wgt
attribute [simp] Conf.succ

theorem Conf.exists_a_iff {κ κ' : Conf D W Var} : (∃ a, Op κ a κ') ↔ Op κ (κ.wgt κ') κ' := by
  rcases κ with ⟨(_ | C), σ, n, β⟩
  · constructor
    · rintro ⟨_, (_ | _)⟩
    · rintro (_ | _)
  · induction C generalizing κ' <;> constructor <;> try simp_all
    · rintro _ (_ | _) <;> simp [Op.BranchL, Op.BranchR]
    · rintro (_ | _) <;> apply Exists.intro
      · apply Op.BranchL
      · apply Op.BranchR
    · rintro _ (_ | _); exact Op.Weight
    · rintro (_ | _)
      apply Exists.intro
      exact Op.Weight
    · rintro _ (_ | _)
      exact Op.Assign
    · rintro (_ | _)
      apply Exists.intro
      apply Op.Assign
    · rintro _ (_ | _)
      · apply Op.If; assumption
      · apply Op.Else; assumption
    · rintro (_ | _)
      · apply Exists.intro; apply Op.If; assumption
      · apply Exists.intro; apply Op.Else; assumption
    · rename_i C₁ C₂ ih₁ ih₂
      rintro a (_ | _)
      · rename_i σ' h
        apply Op.Seq₁
        have := ih₁ (κ':=conf ⟨⊥,σ',n + 1,β⟩) |>.mp
        simp at this
        replace := this a h
        rw [wgt]
        · simp_all
        · simp_all
          sorry
      · rename_i C₁' σ' h
        apply Op.Seq₂
        simp_all
        have := ih₁ (κ':=conf ⟨~C₁',σ',n + 1,β⟩) |>.mp
        simp at this
        replace := this _ h
        apply this
    · rename_i C₁ C₂ ih₁ ih₂
      sorry
    · rintro _ (_ | _)
      · apply Op.While; assumption
      · apply Op.Break; assumption
    · rintro (_ | _)
      · apply Exists.intro; apply WGCL.Op.While; assumption
      · apply Exists.intro; apply WGCL.Op.Break; assumption

theorem Conf.succ_eq_wgt {κ κ' : Conf D W Var} : κ' ∈ κ.succ ↔ Op κ (κ.wgt κ') κ' := by
  simp [Conf.exists_a_iff]

omit [DecidableEq (wGCL D W Var)] [Zero W] in
theorem Conf.succ_unique {κ κ' : Conf D W Var} (h : κ' ∈ κ.succ) : ∃! a, Op κ a κ' := by
  rcases κ with ⟨(_ | C), σ, n, β⟩
  · exists 1; obtain ⟨a, h, _⟩ := h
  · obtain ⟨a, h⟩ := h
    induction C generalizing κ'
    · exists 1; aesop
    · rename_i a; exists a σ; aesop
    · exists a; aesop
    · exists a; aesop
    · rename_i C₁ C₂ ih₁ ih₂
      cases h
      · rename_i σ' h
        exists a
        aesop
      · rename_i C₁' σ' h
        obtain ⟨a', _, h'⟩ := ih₁ h
        exists a'
        constructor
        · exact Op.Seq₂ (by assumption)
        · intro _ h''
          apply h' _ (by cases h''; assumption)
    · exists 1; aesop

structure Path (D W Var : Type) [DecidableEq Var] [One W] where
  confs : List (Conf D W Var)
  prop : ∀ i (hi : i < confs.length - 1), confs[i + 1] ∈ confs[i].succ

variable [Monoid W] [AddCommMonoid M]
variable [inst : DistribMulAction W M]

def Path.wgt (π : Path D W Var) : W :=
  List.range (π.confs.length - 1)
    |>.attach.map (fun ⟨i, hi⟩ ↦
      (π.confs[i]'(by simp_all; omega)).wgt (π.confs[i + 1]'(by simp_all; omega)))
    |>.prod

def Path.terminal (π : Path D W Var) : Prop := π.confs.getLast?.map (·.C) = some ⊥

def TPath (κ₀ : Conf D W Var) : Set (Path D W Var) :=
  {π : Path D W Var | π.confs[0]? = some κ₀ ∧ π.terminal}

@[simp]
def TPath.nonempty {κ₀ : Conf D W Var} (π : TPath κ₀) : ¬π.val.confs = []:= by
  have h := π.prop.right
  simp_all [Path.terminal]
  obtain ⟨last, h, h'⟩ := h
  have ⟨p, h'⟩ := List.getLast?_eq_some_iff.mp h
  simp_all

def TPath.getLast {κ₀ : Conf D W Var} (π : TPath κ₀) : Conf D W Var :=
  π.val.confs.getLast (by simp)

variable [TopologicalSpace M]

noncomputable def op (C : wGCL D W Var) : Weighting D M Var → Weighting D M Var :=
  fun f σ ↦ ∑' π : TPath (conf ⟨~C,σ,0,[]⟩), π.val.wgt • f (TPath.getLast π).σ

variable [OmegaCompletePartialOrder M] [OrderBot M]

variable [AddLeftMono M]
variable [CovariantClass W M HSMul.hSMul LE.le]

variable [OrderClosedTopology M]
variable [IsOrderedAddMonoid M]

-- @[simp] theorem W_hasSum {f : Weighting D M Var} : HasSum f (⨆ s : Finset α, ∑ a ∈ s, f a) :=
--   tendsto_atTop_iSup fun _ _ ↦ Finset.sum_le_sum_of_subset
-- @[simp] theorem W_summable {f : Weighting D M Var} : Summable f := ⟨_, W_hasSum⟩

noncomputable def op' (C : wGCL D W Var) : Weighting D M Var →o Weighting D M Var :=
  ⟨fun f σ ↦ ∑' π : TPath (conf ⟨~C,σ,0,[]⟩), π.val.wgt • f (TPath.getLast π).σ, by
    intro f₁ f₂ h σ
    simp_all
    apply Summable.tsum_le_tsum
    · simp
      intro π h'
      gcongr
      apply h
    · sorry -- summable π.wgt • f₁ ...
    · sorry -- summable π.wgt • f₂ ...
  ⟩

end WGCL
