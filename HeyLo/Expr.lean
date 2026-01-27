import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Control.LawfulFix
import Mathlib.Control.Traversable.Instances
import Mathlib.Data.NNRat.Order
import Mathlib.Tactic.DeriveTraversable
import Mathlib.Tactic.Eval
import PGCL.Exp

open pGCL

/-- Logarithm of `x` in base `b` -/
noncomputable def ENNReal.logb (x : ENNReal) (b : ENNReal) : EReal := x.log / b.log
noncomputable abbrev ENNReal.log₂ (x : ENNReal) : EReal := x.logb 2

namespace HeyLo

inductive Ty where
  | Bool
  | ENNReal
deriving Lean.ToExpr, DecidableEq, Inhabited

open Ty

inductive BinOp : Ty → Ty → Type where
  /- The `+` operator (addition). -/
  | Add : BinOp ENNReal ENNReal
  /- The `-` operator (subtraction). -/
  | Sub : BinOp ENNReal ENNReal
  /- The `*` operator (multiplication). -/
  | Mul : BinOp ENNReal ENNReal
  /- The `/` operator (divison). -/
  | Div : BinOp ENNReal ENNReal
  -- NOTE: This does not really make sense when we only have ENNReals and no integers
  -- /- The `%` operator (modulo). -/
  -- | Mod : BinOp ENNReal ENNReal
  /- The `&&` operator (logical and). -/
  | And : BinOp Bool Bool
  /- The `||` operator (logical or). -/
  | Or : BinOp Bool Bool
  /- The `==` operator (equality). -/
  | Eq : BinOp ENNReal Bool
  /- The `<` operator (less than). -/
  | Lt : BinOp ENNReal Bool
  /- The `<=` operator (less than or equal to). -/
  | Le : BinOp ENNReal Bool
  /- The `!=` operator (not equal to). -/
  | Ne : BinOp ENNReal Bool
  /- The `>=` operator (greater than or equal to). -/
  | Ge : BinOp ENNReal Bool
  /- The `>` operator (greater than). -/
  | Gt : BinOp ENNReal Bool
  /- The `⊓` operator (infimum). -/
  | Inf : BinOp ENNReal ENNReal
  /- The `⊔` operator (supremum). -/
  | Sup : BinOp ENNReal ENNReal
  /- The `→` operator (implication). -/
  | Impl : BinOp ENNReal ENNReal
  /- The `←` operator (co-implication). -/
  | CoImpl : BinOp ENNReal ENNReal
deriving Lean.ToExpr, DecidableEq

inductive UnOp : Ty → Ty → Type where
  /- The `!` operator (negation). -/
  | Not : UnOp α α
  /- The `~` operator (dual of negation), -/
  | Non : UnOp ENNReal ENNReal
  /- Boolean embedding (maps true to top in the lattice). -/
  | Embed : UnOp Bool ENNReal
  /- Iverson bracket (maps true to 1). -/
  | Iverson : UnOp Bool ENNReal
deriving Lean.ToExpr, DecidableEq

inductive QuantOp : Ty → Type where
  /- The infimum of a set. -/
  | Inf : QuantOp ENNReal
  /- The supremum of a set. -/
  | Sup : QuantOp ENNReal
  /- Boolean forall (equivalent to `Inf` on the lattice of booleans). -/
  | Forall : QuantOp Bool
  /- Boolean exists (equivalent to `Sup` on the lattice of booleans). -/
  | Exists : QuantOp Bool
deriving Lean.ToExpr, DecidableEq

instance : Inhabited (QuantOp α) where
  default :=
    match α with
    | .Bool => .Forall
    | .ENNReal => .Inf

structure Ident where
  name : String
deriving Lean.ToExpr, DecidableEq, Hashable, Inhabited

namespace Ident

@[ext] theorem ext {i j : Ident} (h : i.name = j.name) : i = j := by grind [Ident]
@[grind inj] theorem name_inj : Function.Injective name := by intro i j; grind [Ident]

instance instLE : LE Ident := ⟨(·.name ≤ ·.name)⟩

attribute [local simp] instLE

instance : IsTrans Ident (· ≤ ·) := ⟨fun _ _ _ ↦ String.le_trans⟩
instance : IsTotal Ident (· ≤ ·) := ⟨(String.le_total ·.name ·.name)⟩
instance : DecidableRel (· ≤ · : Ident → Ident → Prop) := fun a b ↦ a.name.decLE b.name
instance : Std.Antisymm (· ≤ · : Ident → Ident → Prop) :=
    ⟨by rintro ⟨a⟩ ⟨b⟩; simp; exact String.le_antisymm⟩
instance : IsAntisymm Ident (· ≤ ·) :=
  ⟨by rintro ⟨a⟩ ⟨b⟩; simp; exact String.le_antisymm⟩

end Ident

abbrev Ty.lit : Ty → Type
  | .Bool => Prop
  | .ENNReal => _root_.ENNReal
abbrev Ty.expr (ϖ : Type) : Ty → Type
  | .Bool => BExpr ϖ
  | .ENNReal => Exp ϖ

-- inductive QuantVar where
--   | Shadow : ϖ → QuantVar
--   | Fresh : ϖ → QuantVar
--   | DeBrujin : QuantVar
-- deriving Lean.ToExpr, DecidableEq, Inhabited

open Lean in
instance : Lean.ToExpr Rat where
  toExpr r := mkApp2 (.const ``mkRat []) (toExpr r.num) (toExpr r.den)
  toTypeExpr := .const ``Rat []

open Lean in
instance : Lean.ToExpr NNRat where
  toExpr r :=
    mkApp (.const ``Rat.toNNRat [])
      (mkApp2 (.const ``mkRat []) (mkApp (.const ``Int.ofNat []) (toExpr r.num)) (toExpr r.den))
  toTypeExpr := .const ``NNRat []

inductive Literal : Ty → Type where
  -- /- A string literal (`"something"`). -/
  -- | Str : String → Literal String
  /- An unsigned integer literal (`123`). -/
  | UInt : Nat → Literal ENNReal
  /- A number literal represented by a fraction. -/
  | Frac : NNRat → Literal ENNReal
  /- Infinity, -/
  | Infinity : Literal ENNReal
  /- A boolean literal. -/
  | Bool : Bool → Literal Bool
deriving DecidableEq, Lean.ToExpr

inductive Fun : Ty → Ty → Type where
  | NFloor : Fun ENNReal ENNReal
  | NLog₂ : Fun ENNReal ENNReal
  | IsNat : Fun ENNReal Bool
deriving DecidableEq, Lean.ToExpr

end HeyLo

-- a ↙ b = (a ≤ )

open HeyLo HeyLo.Ty in
inductive HeyLo (ϖ : Type) : Ty → Type where
  -- /- A variable. -/
  -- | Var : Ident → HeyLo ϖ ENNReal
  /- A call to a procedure or function. -/
  | Call : {α β : Ty} → Fun α β → HeyLo ϖ α → HeyLo ϖ β
  -- /- Boolean if-then-else -/
  -- | Ite : HeyLo ϖ Bool → HeyLo ϖ ENNReal → HeyLo ϖ ENNReal → HeyLo ϖ ENNReal
  | Unary : UnOp α β → HeyLo ϖ α → HeyLo ϖ β
  | Binary : BinOp α β → HeyLo ϖ α → HeyLo ϖ  α → HeyLo ϖ β
  -- /- Type casting. -/
  -- | Cast : HeyLo ϖ ENNReal → HeyLo ϖ ENNReal
  -- /- A quantifier over some variables. -/
  -- | Quant : QuantOp → Ident → HeyLo ϖ ENNReal → HeyLo ϖ ENNReal
  -- /- A substitution. -/
  -- | Subst : Ident → HeyLo ϖ ENNReal → HeyLo ϖ ENNReal → HeyLo ϖ ENNReal
  /- A value literal. -/
  -- /- A de Bruijn index. -/
  -- | DeBruijn : DeBruijnIndex → HeyLo ϖ ENNReal
-- deriving Lean.ToExpr, Inhabited

  /- A variable. -/
  | Var : ϖ → HeyLo ϖ ENNReal
  -- /- A call to a procedure or function. -/
  -- | Call : Ident → List HeyLo ϖ ENNReal → HeyLo ϖ ENNReal
  /- Boolean if-then-else -/
  | Ite : HeyLo ϖ Bool → HeyLo ϖ α → HeyLo ϖ  α → HeyLo ϖ α
  -- /- Type casting. -/
  -- | Cast : HeyLo ϖ ENNReal → HeyLo ϖ ENNReal
  /- A quantifier over some variables. -/
  | Quant : QuantOp α → ϖ → HeyLo ϖ  α → HeyLo ϖ α
  /- A substitution. -/
  | Subst : ϖ → HeyLo ϖ ENNReal → HeyLo ϖ α → HeyLo ϖ  α
  /- A value literal. -/
  | Lit : Literal α → HeyLo ϖ  α
  -- /- A de Bruijn index. -/
  -- | DeBruijn : DeBruijnIndex → HeyLo ϖ ENNReal
deriving DecidableEq, Lean.ToExpr

open HeyLo

namespace HeyLo

scoped notation "𝔼r[" ϖ "]" => HeyLo ϖ Ty.ENNReal
scoped notation "𝔼b[" ϖ "]" => HeyLo ϖ Ty.Bool

end HeyLo

instance : Top 𝔼r[ϖ] := ⟨.Lit .Infinity⟩
instance : OfNat 𝔼r[ϖ] n := ⟨.Lit (.UInt n)⟩
instance : Add 𝔼r[ϖ] := ⟨.Binary .Add⟩
instance : Sub 𝔼r[ϖ] := ⟨.Binary .Sub⟩
instance : Mul 𝔼r[ϖ] := ⟨.Binary .Mul⟩
instance : Div 𝔼r[ϖ] := ⟨.Binary .Div⟩
instance : Min 𝔼r[ϖ] := ⟨.Binary .Inf⟩
instance : Max 𝔼r[ϖ] := ⟨.Binary .Sup⟩
instance : HImp 𝔼r[ϖ] := ⟨.Binary .Impl⟩
instance : HCoImp 𝔼r[ϖ] := ⟨.Binary .CoImpl⟩
instance : HNot (HeyLo ϖ α) := ⟨.Unary .Not⟩
noncomputable instance {α : Ty} : HNot (α.expr ϖ) :=
  match α with
  | .Bool => inferInstance
  | .ENNReal => inferInstance
instance : HCoNot 𝔼r[ϖ] := ⟨.Unary .Non⟩
instance : Iverson 𝔼b[String] 𝔼r[String] := ⟨.Unary .Iverson⟩

def HeyLo.subst (X : HeyLo ϖ α) (x : ϖ) (Y : 𝔼r[ϖ]) : HeyLo ϖ  α :=
  .Subst x Y X

instance : Substitution (HeyLo ϖ α) (fun (_ : ϖ) ↦ 𝔼r[ϖ]) := ⟨fun X x ↦ HeyLo.subst X x.1 x.2⟩

instance : Inhabited (BExpr ϖ) where
  default := ⟨fun _ ↦ false, inferInstance⟩

@[grind =, simp]
def HeyLo.Literal.lit (l : Literal α) : α.lit :=
  match l with
  | .UInt n => n
  | .Frac n => n
  | .Bool b => b
  | .Infinity => ⊤
@[grind =, simp]
def HeyLo.Literal.sem (l : Literal α) : α.expr ϖ :=
  match l with
  | .UInt n => n
  | .Frac n => (n : ENNReal)
  | .Bool b => b
  | .Infinity => ⊤

noncomputable def HeyLo.BinOp.sem
    (op : BinOp α β) (l r : α.expr ϖ) : β.expr ϖ :=
  match op with
  | .CoImpl => l ↜ r
  | .Impl => l ⇨ r
  | .Sup => l ⊔ r
  | .Inf => l ⊓ r
  | .Gt => BExpr.lt r l
  | .Ge => BExpr.le r l
  | .Ne => (BExpr.eq l r).not
  | .Le => BExpr.le l r
  | .Lt => BExpr.lt l r
  | .Eq => BExpr.eq l r
  | .Or => BExpr.or l r
  | .And => BExpr.and l r
  | .Div => l / r
  | .Mul => l * r
  | .Sub => l - r
  | .Add => l + r

noncomputable def HeyLo.UnOp.sem (op : UnOp α β) (x : α.expr ϖ) : β.expr ϖ :=
  match op with
  | .Not => ￢ x
  | .Non => ~ x
  | .Iverson => i[x]
  | .Embed => i[x] * ⊤

noncomputable def HeyLo.QuantOp.sem [DecidableEq ϖ] (op : HeyLo.QuantOp α) (x : ϖ) (m : α.expr ϖ) :
    α.expr ϖ :=
  match op with
  | .Inf => ⨅ (v : ENNReal), m[x ↦ v]
  | .Sup => ⨆ (v : ENNReal), m[x ↦ v]
  | .Forall => BExpr.forall_ x m
  | .Exists => BExpr.exists_ x m

theorem HeyLo.iSup_sem_eq_iSup_exp [DecidableEq ϖ] {x : ϖ} :
    HeyLo.QuantOp.Sup.sem x e = ⨆ (v : Exp ϖ), e[x ↦ ↑v] := by
  ext σ
  simp [QuantOp.sem]
  apply le_antisymm
  · refine iSup_mono' ?_
    intro v
    use v
    rfl
  · refine iSup_mono' ?_
    intro v
    use v σ
@[grind =, simp]
theorem HeyLo.QuantOp.Sup_sem_eq_iSup_ennreal [DecidableEq ϖ] {x : ϖ} :
    HeyLo.QuantOp.Sup.sem x e = ⨆ (v : ENNReal), e[x ↦ ↑v] := by
  rfl
theorem HeyLo.iInf_sem_eq_iInf_exp [DecidableEq ϖ] {x : ϖ} :
    HeyLo.QuantOp.Inf.sem x e = ⨅ (v : Exp ϖ), e[x ↦ ↑v] := by
  ext σ
  simp [QuantOp.sem]
  apply le_antisymm
  · refine iInf_mono' ?_
    intro v
    use v σ
  · refine iInf_mono' ?_
    intro v
    use v
    rfl
@[grind =, simp]
theorem HeyLo.QuantOp.Sup_sem_eq_iInf_ennreal [DecidableEq ϖ] {x : ϖ} :
    HeyLo.QuantOp.Inf.sem x e = ⨅ (v : ENNReal), e[x ↦ ↑v] := by
  rfl

noncomputable def HeyLo.Fun.sem [DecidableEq ϖ] (f : HeyLo.Fun α β) (m : α.expr ϖ) :
    β.expr ϖ :=
  match f with
  | .NFloor => fun σ ↦ ⌊(m σ).toReal⌋.toNat
  | .NLog₂ => fun σ ↦ Nat.log2 ⌊(m σ).toReal⌋.toNat
  | .IsNat => ⟨fun σ ↦ ∃ (n : ℕ), m σ = n, Classical.decPred _⟩

@[reducible]
instance [DecidableEq ϖ] {α : Ty} : Substitution (α.expr ϖ) (fun (_ : ϖ) ↦ Ty.ENNReal.expr ϖ) :=
  match α with
  | .Bool => inferInstance
  | .ENNReal => inferInstance

noncomputable def HeyLo.sem [DecidableEq ϖ] (X : HeyLo ϖ α) : α.expr ϖ :=
  match X with
  | .Binary op l r => op.sem l.sem r.sem
  | .Lit l => l.sem
  | .Subst x v m => m.sem[x ↦ v.sem]
  | .Quant op x m => op.sem x m.sem
  | .Call f x => f.sem x.sem
  | .Ite b l r =>
    match α with
    | .Bool => BExpr.ite b.sem l.sem r.sem
    | .ENNReal => i[b.sem] * l.sem + i[b.sem.not] * r.sem
  | .Var x => fun σ ↦ σ x
  | .Unary op m => op.sem m.sem

@[reducible]
instance {α : Ty} : FunLike (α.expr ϖ) (States ϖ) α.lit :=
  match α with
  | .Bool => inferInstanceAs (FunLike (BExpr ϖ) (States ϖ) Prop)
  | .ENNReal => {coe := id, coe_injective' := fun _ _ a ↦ a}

attribute [simp] Ty.expr
attribute [simp] Ty.lit
attribute [simp] instFunLikeExprStatesLit

@[grind =, simp]
theorem HeyLo.Sup_sem_eq_iSup_ennreal [DecidableEq ϖ] {x : ϖ} :
    (HeyLo.Quant HeyLo.QuantOp.Sup x e).sem = ⨆ (v : ENNReal), e.sem[x ↦ ↑v] := by
  rfl
@[grind =, simp]
theorem HeyLo.Sup_sem_eq_iInf_ennreal [DecidableEq ϖ] {x : ϖ} :
    (HeyLo.Quant HeyLo.QuantOp.Inf x e).sem = ⨅ (v : ENNReal), e.sem[x ↦ ↑v] := by
  rfl

variable [DecidableEq ϖ]

@[grind =, simp]
theorem HeyLo.sem_subst {X : HeyLo ϖ α} : X[x ↦ v].sem = X.sem[x ↦ v.sem] := rfl
@[grind =, simp]
theorem UnOp.sem_subst {op : UnOp α β} {a : α.expr ϖ} : (op.sem a)[x ↦ v] = op.sem a[x ↦ v] := by
  cases op <;> try rfl
  · cases α <;> rfl
@[grind =, simp]
theorem BinOp.sem_subst {op : BinOp α β} {a : α.expr ϖ} :
    (op.sem a b)[x ↦ v] = op.sem a[x ↦ v] b[x ↦ v] := by cases op <;> try rfl
@[grind =, simp]
theorem HeyLo.sem_Forall_apply {c : 𝔼b[ϖ]} :
    (HeyLo.Quant QuantOp.Forall x c).sem σ ↔ ∀ (v : ENNReal), c.sem σ[x ↦ ↑v] := by
  rfl
@[grind =, simp]
theorem HeyLo.sem_Exists_apply {c : 𝔼b[ϖ]} :
    (HeyLo.Quant QuantOp.Exists x c).sem σ ↔ ∃ (v : ENNReal), c.sem σ[x ↦ ↑v] := by
  rfl

theorem Array.flatMap_sum {α β : Type*} {A : Array α} {f : α → Array β} [AddMonoid β] :
    (A.flatMap f).sum = (A.map (fun a ↦ (f a).sum)).sum := by
  obtain ⟨A⟩ := A
  simp
  induction A with
  | nil => simp
  | cons a A ih => simp_all only [List.flatMap_cons, List.sum_append, sum_eq_sum_toList,
    List.map_cons, List.sum_cons]
theorem Array.map_mul_sum {α β : Type*} [MonoidWithZero β] [AddMonoid β] [LeftDistribClass β]
    {A : Array α} {s : β} {f : α → β} : (A.map (fun x ↦ s * f x)).sum = s * (A.map f).sum := by
  obtain ⟨A⟩ := A
  induction A with grind [mul_zero, left_distrib]

structure Distribution (ϖ : Type) [DecidableEq ϖ] where
  values : Array (𝔼r[ϖ] × 𝔼r[ϖ])
  prop : ∀ (σ : States ϖ), (values.map (·.fst.sem σ)).sum = 1
-- deriving DecidableEq

attribute [simp] Distribution.prop

open Lean in
instance [ToExpr ϖ] : Lean.ToExpr (Distribution ϖ) where
  toExpr μ :=
    toExpr μ.values
  toTypeExpr := .const ``Distribution []

def Distribution.pure (v : 𝔼r[ϖ]) : Distribution ϖ := ⟨#[(1, v)], by simp [sem]⟩
def Distribution.bind (μ : Distribution ϖ) (f : 𝔼r[ϖ] → Distribution ϖ) : Distribution ϖ :=
  let values := μ.values.flatMap (fun (p, v) ↦ (f v).values.map (fun (p', v') ↦ (p * p', v')))
  {values, prop := by
    intro σ
    simp only [Array.map_flatMap, Array.map_map, values]
    unfold Function.comp
    simp only [sem, BinOp.sem, Ty.expr, Pi.mul_apply, Array.flatMap_sum, Array.map_mul_sum, prop,
      mul_one]
  }
def Distribution.map (μ : Distribution ϖ) (f : 𝔼r[ϖ] → 𝔼r[ϖ]) : Distribution ϖ :=
  ⟨μ.values.map (fun (p, v) ↦ (p, f v)), by simp; unfold Function.comp; simp⟩

@[grind ., simp]
theorem Distribution.values_ne_empty (μ : Distribution ϖ) : μ.values ≠ #[] := by
  have := μ.prop fun _ ↦ 0
  grind [zero_ne_one]
@[simp]
theorem Distribution.exists_in_values (μ : Distribution ϖ) : ∃ x v, (x, v) ∈ μ.values := by
  have : ∃ x, x ∈ μ.values := by simp [Array.isEmpty_eq_false_iff_exists_mem.mp]
  grind

@[grind =, simp]
theorem Array.sum_replicate {α : Type*} {x : α} [Semiring α] :
    (Array.replicate n x).sum = n * x := by
  induction n with
  | zero => grind
  | succ n ih => grind [push, toList_replicate, List.sum_replicate]

def Distribution.unif (vs : Array 𝔼r[ϖ]) (h : vs ≠ #[]) : Distribution ϖ :=
  ⟨vs.map fun v ↦ (.Binary .Div (1 : 𝔼r[ϖ]) (OfNat.ofNat vs.size), v), by
    intro σ
    simp only [Array.map_map]
    unfold Function.comp
    simp [sem, BinOp.sem, Array.map_const', h, ENNReal.mul_inv_cancel]⟩
def Distribution.bin (a : 𝔼r[ϖ]) (p : 𝔼r[ϖ]) (b : 𝔼r[ϖ]) : Distribution ϖ :=
  ⟨#[(p ⊓ 1, a), (1 - (p ⊓ 1), b)], by intro σ; simp [sem, BinOp.sem]⟩

@[grind =, simp]
theorem Distribution.pure_map {e : 𝔼r[ϖ]} :
    (Distribution.pure e).map f = Distribution.pure (f e) := by
  simp [pure, map]
@[grind =, simp]
theorem Distribution.bin_map {a b : 𝔼r[ϖ]} :
    (Distribution.bin a p b).map f = Distribution.bin (f a) p (f b) := by
  simp [bin, map]

def Distribution.toExpr (μ : Distribution ϖ) : 𝔼r[ϖ] :=
  μ.values.map (fun (p, v) ↦ p * v) |>.sum
@[grind =, simp]
theorem Distribution.pure_toExpr {a : 𝔼r[ϖ]} :
    (Distribution.pure a).toExpr = 1 * a + 0 := by
  simp [pure, toExpr]
@[grind =, simp]
theorem Distribution.bin_toExpr {a b : 𝔼r[ϖ]} :
    (Distribution.bin a p b).toExpr = (p ⊓ 1) * a + ((1 - (p ⊓ 1)) * b + 0) := by
  simp [bin, toExpr]

inductive HeyVL (ϖ : Type) [DecidableEq ϖ] where
  --
  | Assign (x : ϖ) (μ : Distribution ϖ)
  | Reward (a : 𝔼r[ϖ])
  | Seq (S₁ S₂ : HeyVL ϖ)
  --
  | IfInf (S₁ S₂ : HeyVL ϖ)
  | Assert (φ : 𝔼r[ϖ])
  | Assume (φ : 𝔼r[ϖ])
  | Havoc (xs : ϖ)
  | Validate
  --
  | IfSup (S₁ S₂ : HeyVL ϖ)
  | Coassert (φ : 𝔼r[ϖ])
  | Coassume (φ : 𝔼r[ϖ])
  | Cohavoc (x : ϖ)
  | Covalidate
-- deriving Lean.ToExpr

def HeyVL.vp (C : HeyVL ϖ) : 𝔼r[ϖ] → 𝔼r[ϖ] := fun φ ↦
  match C with
  --
  | .Assign x μ => μ.map (fun v ↦ φ[x ↦ v]) |>.toExpr
  | .Reward a => φ + a
  | .Seq S₁ S₂ => S₁.vp (S₂.vp φ)
  --
  | IfInf S₁ S₂ => S₁.vp φ ⊓ S₂.vp φ
  | Assert ψ => ψ ⊓ φ
  | Assume ψ => ψ ⇨ φ
  | Havoc x => .Quant .Inf x φ
  | Validate => ▵ φ
  --
  | IfSup S₁ S₂ => S₁.vp φ ⊔ S₂.vp φ
  | Coassert ψ => ψ ⊔ φ
  | Coassume ψ => ψ ↜ φ
  | Cohavoc x => .Quant .Sup x φ
  | Covalidate => ▿ φ
