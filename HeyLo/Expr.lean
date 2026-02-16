import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Control.LawfulFix
import Mathlib.Control.Traversable.Instances
import Mathlib.Data.Fintype.Order
import Mathlib.Data.NNRat.Order
import Mathlib.Data.String.Basic
import Mathlib.Tactic.DeriveTraversable
import Mathlib.Tactic.Eval
import PGCL.Exp

open pGCL

/-- Logarithm of `x` in base `b` -/
noncomputable def ENNReal.logb (x : ENNReal) (b : ENNReal) : EReal := x.log / b.log
noncomputable abbrev ENNReal.log₂ (x : ENNReal) : EReal := x.logb 2

namespace HeyLo

@[grind]
inductive Ty where
  | Bool
  | Nat
  | ENNReal
deriving Lean.ToExpr, DecidableEq, Hashable, Inhabited

def Ty.toNat : Ty → ℕ
| .Bool => 0
| .Nat => 1
| .ENNReal => 2

instance Ty.instLinearOrder : LinearOrder Ty := LinearOrder.lift' Ty.toNat (by intro; grind [toNat])

abbrev Ty.lit : Ty → Type
  | .Bool => Prop
  | .ENNReal => _root_.ENNReal
  | .Nat => _root_.Nat

open Ty

inductive Yes where | yes
deriving Lean.ToExpr, DecidableEq, Hashable, Inhabited
inductive No
deriving Lean.ToExpr, DecidableEq, Hashable

abbrev Ty.Compare : Ty → Type
  | .Bool => No
  | .ENNReal => Yes
  | .Nat => Yes
abbrev Ty.Arith : Ty → Type
  | .Bool => No
  | .ENNReal => Yes
  | .Nat => Yes

open Lean in
instance {α : Ty} : Lean.ToExpr α.Compare where
  toExpr h :=
    match α with
    | .ENNReal | .Nat => Lean.ToExpr.toExpr Yes.yes
    | .Bool => False.elim (by cases h)
  -- TODO
  toTypeExpr := sorry
open Lean in
instance {α : Ty} : Lean.ToExpr α.Arith where
  toExpr h :=
    match α with
    | .ENNReal | .Nat => Lean.ToExpr.toExpr Yes.yes
    | .Bool => False.elim (by cases h)
  -- TODO
  toTypeExpr := sorry

instance {α : Ty} : DecidableEq α.Compare := fun a b ↦ by
  cases α <;> cases a
  all_goals cases b; simp only; exact instDecidableTrue
instance {α : Ty} : DecidableEq α.Arith := fun a b ↦ by
  cases α <;> cases a
  all_goals cases b; simp only; exact instDecidableTrue

inductive BinOp : Ty → Ty → Type where
  /-- The `+` operator (addition). -/
  | Add : {α : Ty} → α.Arith → BinOp α α
  /-- The `-` operator (subtraction). -/
  | Sub : {α : Ty} → α.Arith → BinOp α α
  /-- The `*` operator (multiplication). -/
  | Mul : {α : Ty} → α.Arith → BinOp α α
  /-- The `/` operator (divison). -/
  | Div : {α : Ty} → α.Arith → BinOp α α
  /-- The `%` operator (modulo). -/
  | Mod : BinOp Nat Nat
  /-- The `&&` operator (logical and). -/
  | And : BinOp Bool Bool
  /-- The `||` operator (logical or). -/
  | Or : BinOp Bool Bool
  /-- The `==` operator (equality). -/
  | Eq : BinOp α Bool
  /-- The `<` operator (less than). -/
  | Lt : {α : Ty} → α.Compare → BinOp α Bool
  /-- The `<=` operator (less than or equal to). -/
  | Le : {α : Ty} → α.Compare → BinOp α Bool
  /-- The `!=` operator (not equal to). -/
  | Ne : {α : Ty} → α.Compare → BinOp α Bool
  /-- The `>=` operator (greater than or equal to). -/
  | Ge : {α : Ty} → α.Compare → BinOp α Bool
  /-- The `>` operator (greater than). -/
  | Gt : {α : Ty} → α.Compare → BinOp α Bool
  /-- The `⊓` operator (infimum). -/
  | Inf : BinOp ENNReal ENNReal
  /-- The `⊔` operator (supremum). -/
  | Sup : BinOp ENNReal ENNReal
  /-- The `→` operator (implication). -/
  | Impl : BinOp ENNReal ENNReal
  /-- The `←` operator (co-implication). -/
  | CoImpl : BinOp ENNReal ENNReal
deriving Lean.ToExpr, DecidableEq

#check eval% @BinOp.Lt .ENNReal .yes

inductive UnOp : Ty → Ty → Type where
  /-- The `!` operator (negation). -/
  | Not : UnOp α α
  /-- The `~` operator (dual of negation), -/
  | Non : UnOp ENNReal ENNReal
  /-- Boolean embedding (maps true to top in the lattice). -/
  | Embed : UnOp Bool ENNReal
  /-- Iverson bracket (maps true to 1). -/
  | Iverson : UnOp Bool ENNReal
  /-- Cast Nat to ENNReal -/
  | NatToENNReal : UnOp Nat ENNReal
deriving Lean.ToExpr, DecidableEq

inductive QuantOp : Ty → Type where
  /-- The infimum of a set. -/
  | Inf : QuantOp ENNReal
  /-- The supremum of a set. -/
  | Sup : QuantOp ENNReal
  /-- Boolean forall (equivalent to `Inf` on the lattice of booleans). -/
  | Forall : QuantOp Bool
  /-- Boolean exists (equivalent to `Sup` on the lattice of booleans). -/
  | Exists : QuantOp Bool
deriving Lean.ToExpr, DecidableEq

structure Ident where
  name : String
  type : Ty
deriving Lean.ToExpr, DecidableEq, Hashable, Inhabited

namespace Ident

@[ext] theorem ext {i j : Ident} (h : i.name = j.name) (h' : i.type = j.type) : i = j := by
  grind [Ident]

def toLex (i : Ident) : Lex (String × Ty) := (i.name, i.type)

instance instLinearOrder : LinearOrder Ident :=
  LinearOrder.lift' toLex (by grind [Function.Injective, toLex, Ident])

end Ident

abbrev Ty.ϖ : Ident → Type := fun (x : Ident) ↦ Ty.lit (Ident.type x)

notation "𝔼'[" t "]" => 𝔼[Ty.ϖ, t]

abbrev Ty.expr (t : Ty) : Type :=
  𝔼'[t.lit]

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
  -- /-- A string literal (`"something"`). -/
  -- | Str : Ident → Literal Ident
  /-- An unsigned integer literal (`123`). -/
  | UInt : {α : Ty} → (h : α.Arith) → Nat → Literal α
  /-- A number literal represented by a fraction. -/
  | Frac : NNRat → Literal ENNReal
  /-- Infinity, -/
  | Infinity : Literal ENNReal
  /-- A boolean literal. -/
  | Bool : Bool → Literal Bool
deriving DecidableEq, Lean.ToExpr

inductive Fun : Ty → Ty → Type where
  | nfloor : Fun ENNReal Nat
  | nlog2 : Fun Nat Nat
deriving DecidableEq, Lean.ToExpr

end HeyLo

-- a ↙ b = (a ≤ )

open HeyLo HeyLo.Ty in
inductive HeyLo : Ty → Type where
  /-- A call to a procedure or function. -/
  | Call : {α β : Ty} → Fun α β → HeyLo α → HeyLo β
  | Unary : UnOp α β → HeyLo α → HeyLo β
  | Binary : BinOp α β → HeyLo α → HeyLo α → HeyLo β
  /-- A variable. -/
  | Var : String → (α : Ty) → HeyLo α
  /-- Boolean if-then-else -/
  | Ite : HeyLo Bool → HeyLo α → HeyLo α → HeyLo α
  /-- A quantifier over some variables. -/
  | Quant : QuantOp α → Ident → HeyLo α → HeyLo α
  /-- A substitution. -/
  | Subst : (v : Ident) → HeyLo v.type → HeyLo α → HeyLo α
  /-- A value literal. -/
  | Lit : Literal α → HeyLo α
deriving Lean.ToExpr, DecidableEq

  -- /-- Type casting. -/
  -- | Cast : HeyLo ENNReal → HeyLo ENNReal
  -- /-- A de Bruijn index. -/
  -- | DeBruijn : DeBruijnIndex → HeyLo ENNReal

open HeyLo

namespace HeyLo

scoped notation "𝔼r" => HeyLo Ty.ENNReal
scoped notation "𝔼b" => HeyLo Ty.Bool

end HeyLo


instance : Top 𝔼r := ⟨.Lit .Infinity⟩
instance HeyLo.instOfNat (h : α.Arith := by exact default) : OfNat (HeyLo α) n := ⟨.Lit (.UInt h n)⟩
instance HeyLo.instAdd (h : α.Arith := by exact default) : Add (HeyLo α) := ⟨.Binary (.Add h)⟩
instance HeyLo.instSub (h : α.Arith := by exact default) : Sub (HeyLo α) := ⟨.Binary (.Sub h)⟩
instance HeyLo.instMul (h : α.Arith := by exact default) : Mul (HeyLo α) := ⟨.Binary (.Mul h)⟩
instance HeyLo.instDiv (h : α.Arith := by exact default) : Div (HeyLo α) := ⟨.Binary (.Div h)⟩
instance : Min 𝔼r := ⟨.Binary .Inf⟩
instance : Max 𝔼r := ⟨.Binary .Sup⟩
instance : HImp 𝔼r := ⟨.Binary .Impl⟩
instance : SDiff 𝔼r := ⟨fun a b ↦ .Binary .CoImpl b a⟩
instance : HNot (HeyLo α) := ⟨.Unary .Not⟩
instance : Compl 𝔼r := ⟨.Unary .Non⟩
instance : Iverson 𝔼b 𝔼r := ⟨.Unary .Iverson⟩

@[reducible] instance : OfNat (HeyLo .ENNReal) n := HeyLo.instOfNat
@[reducible] instance : OfNat (HeyLo .Nat) n := HeyLo.instOfNat

@[reducible] instance : Add (HeyLo .ENNReal) := HeyLo.instAdd
@[reducible] instance : Add (HeyLo .Nat) := HeyLo.instAdd
@[reducible] instance : Sub (HeyLo .ENNReal) := HeyLo.instSub
@[reducible] instance : Sub (HeyLo .Nat) := HeyLo.instSub
@[reducible] instance : Mul (HeyLo .ENNReal) := HeyLo.instMul
@[reducible] instance : Mul (HeyLo .Nat) := HeyLo.instMul
@[reducible] instance : Div (HeyLo .ENNReal) := HeyLo.instDiv
@[reducible] instance : Div (HeyLo .Nat) := HeyLo.instDiv

def HeyLo.subst (X : HeyLo α) (x : Ident) (Y : HeyLo x.type) : HeyLo α :=
  .Subst x Y X

instance : Substitution (HeyLo α) (fun (v : Ident) ↦ HeyLo v.type) :=
  ⟨fun X x ↦ HeyLo.subst X x.1 x.2⟩

-- instance : Inhabited (BExpr ϖ) where
--   default := ⟨fun _ ↦ false, inferInstance⟩

@[grind =, simp]
def HeyLo.Literal.lit (l : Literal α) : α.lit :=
  match l with
  | .UInt _ n => match α with | .ENNReal | .Nat => n
  | .Frac n => n
  | .Bool b => b
  | .Infinity => ⊤
@[grind =, simp]
def HeyLo.Literal.sem (l : Literal α) : α.expr :=
  match l with
  | .UInt _ n => match α with | .ENNReal | .Nat => n
  | .Frac n => fun _ ↦ n
  | .Bool b => fun _ ↦ b
  | .Infinity => ⊤

open scoped Classical in
noncomputable def HeyLo.BinOp.sem
    (op : BinOp α β) (l r : α.expr) : β.expr :=
  match op with
  | .CoImpl => l ↜ r
  | .Impl => l ⇨ r
  | .Sup => l ⊔ r
  | .Inf => l ⊓ r
  | .Gt h => match α with | .ENNReal | .Nat => fun σ ↦ r σ > l σ
  | .Ge h => match α with | .ENNReal | .Nat => fun σ ↦ l σ ≥ r σ
  | .Ne h => match α with | .ENNReal | .Nat => fun σ ↦ l σ ≠ r σ
  | .Le h => match α with | .ENNReal | .Nat => fun σ ↦ l σ ≤ r σ
  | .Lt h => match α with | .ENNReal | .Nat => fun σ ↦ l σ < r σ
  | .Eq => fun σ ↦ l σ = r σ
  | .Or => fun σ ↦ l σ ∨ r σ
  | .And => fun σ ↦ l σ ∧ r σ
  | .Mod => fun σ ↦ l σ % r σ
  | .Div h => match β with | .ENNReal | .Nat => l / r
  | .Mul h => match β with | .ENNReal | .Nat => l * r
  | .Sub h => match β with | .ENNReal | .Nat => l - r
  | .Add h => match β with | .ENNReal | .Nat => l + r

noncomputable def HeyLo.UnOp.sem (op : UnOp α β) (x : α.expr) : β.expr :=
  match op with
  | .Not =>
    match α with
    | .ENNReal => ￢ x
    | .Bool => ￢ x
    -- NOTE: this should be unreacable
    | .Nat => x
  | .Non => ~ x
  | .Iverson => i[x]
  | .Embed => i[x] * ⊤
  | .NatToENNReal => (x ·)

@[simp]
theorem Bool.iInf_eq {α : Type*} (f : α → Bool) : ⨅ x, f x ↔ ∀ x, f x := by
  rw [← antisymm_iff (r:=LE.le)]
  simp_all
  exact { mp := fun a x ↦ a x rfl, mpr := fun a i a_1 ↦ a i }
@[simp]
theorem Bool.iSup_eq {α : Type*} (f : α → Bool) : ⨆ x, f x ↔ ∃ x, f x := by
  contrapose
  simp
  rw [← antisymm_iff (r:=LE.le)]
  simp_all
  grind [Bool.le_iff_imp]

noncomputable def HeyLo.QuantOp.sem (op : HeyLo.QuantOp α) (x : Ident) (m : α.expr) :
    α.expr :=
  match op with
  | .Inf => ⨅ (v : x.type.lit), m[x ↦ fun _ ↦ v]
  | .Sup => ⨆ (v : x.type.lit), m[x ↦ fun _ ↦ v]
  | .Forall => ⨅ (v : x.type.lit), m[x ↦ fun _ ↦ v]
  | .Exists => ⨆ (v : x.type.lit), m[x ↦ fun _ ↦ v]

@[simp]
theorem HeyLo.QuantOp.Sup_sem_eq_iSup_ennreal [DecidableEq 𝒱] {x : Ident} :
    HeyLo.QuantOp.Sup.sem x e = ⨆ (v : x.type.lit), e[x ↦ fun _ ↦ v] := by
  rfl
@[simp]
theorem HeyLo.QuantOp.Sup_sem_eq_iInf_ennreal {x : Ident} :
    HeyLo.QuantOp.Inf.sem x e = ⨅ (v : x.type.lit), e[x ↦ fun _ ↦ v] := by
  rfl

noncomputable def HeyLo.Fun.sem (f : HeyLo.Fun α β) (m : α.expr) :
    β.expr :=
  match f with
  | .nfloor => fun σ ↦ ⌊(m σ).toReal⌋.toNat
  | .nlog2 => fun σ ↦ Nat.log2 (m σ)
open scoped Classical in
noncomputable def HeyLo.sem (X : HeyLo α) : α.expr :=
  match X with
  | .Binary op l r => op.sem l.sem r.sem
  | .Lit l => l.sem
  | .Subst x v m => m.sem[x ↦ v.sem]
  | .Quant op x m => op.sem x m.sem
  | .Call f x => f.sem x.sem
  | .Ite b l r =>
    match α with
    | .Bool => fun σ ↦ if b.sem σ then l.sem σ else r.sem σ
    | .ENNReal => i[b.sem] * l.sem + i[￢b.sem] * r.sem
    | .Nat => fun σ ↦ if b.sem σ then l.sem σ else r.sem σ
  | .Var x α => fun σ ↦ σ ⟨x, α⟩
  | .Unary op m => op.sem m.sem

theorem QuantOp.Forall_sem_aux : (QuantOp.sem .Forall x m) σ = ∀ v, m[x ↦ v] σ := by
  simp [QuantOp.sem]
  exact { mp := fun a v ↦ a (v σ), mpr := fun a x ↦ a fun {σ} ↦ x }
@[grind =, simp]
theorem QuantOp.Forall_sem :
    (QuantOp.sem .Forall x m) σ = ∀ (v : x.type.lit), m[x ↦ fun _ ↦ v] σ := by
  simp [Forall_sem_aux]
  exact { mp := fun a v ↦ a fun {σ} ↦ v, mpr := fun a v ↦ a (v σ) }
theorem QuantOp.Exists_sem_aux : (QuantOp.sem .Exists x m) σ = ∃ v, m[x ↦ v] σ := by
  simp [QuantOp.sem]
  apply Function.Surjective.exists
  intro y
  simp
  use fun _ ↦ y
@[grind =, simp]
theorem QuantOp.Exists_sem :
    (QuantOp.sem .Exists x m) σ = ∃ (v : x.type.lit), m[x ↦ fun _ ↦ v] σ := by
  simp [Exists_sem_aux]
  refine Iff.symm (Function.Surjective.exists ?_)
  intro y
  simp
  use fun _ ↦ y

attribute [simp] Ty.expr
attribute [simp] Ty.lit

@[grind =, simp]
theorem HeyLo.Sup_sem_eq_iSup_ennreal {x : Ident} :
    (HeyLo.Quant HeyLo.QuantOp.Sup x e).sem = ⨆ (v : x.type.lit), e.sem[x ↦ fun _ ↦ v] := by
  rfl
@[grind =, simp]
theorem HeyLo.Sup_sem_eq_iInf_ennreal {x : Ident} :
    (HeyLo.Quant HeyLo.QuantOp.Inf x e).sem = ⨅ (v : x.type.lit), e.sem[x ↦ fun _ ↦ v] := by
  rfl

variable [DecidableEq 𝒱]

@[grind =, simp]
theorem HeyLo.sem_subst {X : HeyLo α} : X[x ↦ v].sem = X.sem[x ↦ v.sem] := rfl
@[grind =, simp]
theorem UnOp.sem_subst {op : UnOp α β} {a : α.expr} : (op.sem a)[x ↦ v] = op.sem a[x ↦ v] := by
  cases op <;> try rfl
  · cases α <;> rfl
@[grind =, simp]
theorem BinOp.sem_subst {op : BinOp α β} {a : α.expr} :
    (op.sem a b)[x ↦ v] = op.sem a[x ↦ v] b[x ↦ v] := by
  cases op <;> try rfl
  all_goals cases α <;> try rfl
  all_goals cases ‹Ty.Bool.Compare›
@[grind =, simp]
theorem HeyLo.sem_Forall_apply {c : 𝔼b} :
    (HeyLo.Quant QuantOp.Forall x c).sem σ ↔ ∀ (v : x.type.lit), c.sem σ[x ↦ v] := by
  simp [sem]
@[grind =, simp]
theorem HeyLo.sem_Exists_apply {c : 𝔼b} :
    (HeyLo.Quant QuantOp.Exists x c).sem σ ↔ ∃ (v : x.type.lit), c.sem σ[x ↦ v] := by
  simp [sem]

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

structure HeyLo.Distribution (α : Ty) where
  values : Array (𝔼r × HeyLo α)
  prop : ∀ (σ : States Ty.ϖ), (values.map (·.fst.sem σ)).sum = 1
deriving DecidableEq

attribute [simp] Distribution.prop

open Lean in
instance : Lean.ToExpr (Distribution α) where
  toExpr μ :=
    toExpr μ.values
  toTypeExpr := .const ``Distribution []

def HeyLo.Distribution.pure (v : HeyLo α) : Distribution α := ⟨#[(1, v)], by simp [sem]⟩
def HeyLo.Distribution.bind {α β : Ty} (μ : Distribution α) (f : HeyLo α → Distribution β) :
    Distribution β :=
  let values := μ.values.flatMap (fun (p, v) ↦ (f v).values.map (fun (p', v') ↦ (p * p', v')))
  {values, prop := by
    intro σ
    simp only [Array.map_flatMap, Array.map_map, values]
    unfold Function.comp
    simp only [sem, BinOp.sem, Ty.expr, Pi.mul_apply, Array.flatMap_sum, Array.map_mul_sum]
    conv => enter [1, 1, 1, a, 2]; rw [prop]
    simp only [mul_one]
    rw [prop]
  }
def HeyLo.Distribution.map (μ : Distribution α) (f : HeyLo α → HeyLo β) : Distribution β :=
  ⟨μ.values.map (fun (p, v) ↦ (p, f v)), by simp; unfold Function.comp; simp; apply prop⟩

instance {x : Ident} : Inhabited (x.type.lit) where
  default := by simp; split <;> exact default

@[grind ., simp]
theorem HeyLo.Distribution.values_ne_empty (μ : Distribution α) : μ.values ≠ #[] := by
  have := μ.prop fun x ↦ default
  grind [zero_ne_one]
@[simp]
theorem HeyLo.Distribution.exists_in_values (μ : Distribution α) : ∃ x v, (x, v) ∈ μ.values := by
  have : ∃ x, x ∈ μ.values := by simp [Array.isEmpty_eq_false_iff_exists_mem.mp]
  grind

@[grind =, simp]
theorem Array.sum_replicate {α : Type*} {x : α} [Semiring α] :
    (Array.replicate n x).sum = n * x := by
  induction n with
  | zero => grind
  | succ n ih => grind [push, toList_replicate, List.sum_replicate]

def HeyLo.Distribution.unif (vs : Array (HeyLo α)) (h : vs ≠ #[]) : Distribution α :=
  ⟨vs.map fun v ↦ (.Binary (.Div .yes) (1 : 𝔼r) (OfNat.ofNat vs.size), v), by
    intro σ
    simp only [Array.map_map]
    unfold Function.comp
    simp [sem, BinOp.sem, Array.map_const', h, ENNReal.mul_inv_cancel]⟩
def HeyLo.Distribution.bin (a : HeyLo α) (p : 𝔼r) (b : HeyLo α) : Distribution α :=
  ⟨#[(p ⊓ 1, a), (1 - (p ⊓ 1), b)], by intro σ; simp [sem, BinOp.sem]⟩
def HeyLo.Distribution.flip (p : 𝔼r) : Distribution .Bool :=
  bin (HeyLo.Lit (.Bool true)) p (HeyLo.Lit (.Bool false))

@[grind =, simp]
theorem HeyLo.Distribution.pure_map {e : HeyLo α} :
    (Distribution.pure e).map f = Distribution.pure (f e) := by
  simp [pure, map]
@[grind =, simp]
theorem HeyLo.Distribution.bin_map {a b : HeyLo α} :
    (Distribution.bin a p b).map f = Distribution.bin (f a) p (f b) := by
  simp [bin, map]

def HeyLo.Distribution.toExpr (μ : Distribution .ENNReal) : 𝔼r :=
  μ.values.map (fun (p, v) ↦ p * v) |>.sum
@[grind =, simp]
theorem HeyLo.Distribution.pure_toExpr {a : 𝔼r} :
    (Distribution.pure a).toExpr = 1 * a + 0 := by
  simp [pure, toExpr]
@[grind =, simp]
theorem HeyLo.Distribution.bin_toExpr {a b : 𝔼r} :
    (Distribution.bin a p b).toExpr = (p ⊓ 1) * a + ((1 - (p ⊓ 1)) * b + 0) := by
  simp [bin, toExpr]

def HeyLo.not (x : 𝔼b) : 𝔼b := .Unary .Not x
def HeyLo.iver (x : 𝔼b) : 𝔼r := .Unary .Iverson x
def HeyLo.embed (x : 𝔼b) : 𝔼r := .Unary .Embed x
def HeyLo.coembed (x : 𝔼b) : 𝔼r := .Unary .Embed x.not

inductive HeyVL where
  /-- `x :≈ μ` -/
  | Assign (x : Ident) (μ : Distribution x.type)
  /-- `reward μ` -/
  | Reward (a : 𝔼r)
  /-- `S₁ ; S₂` -/
  | Seq (S₁ S₂ : HeyVL)
  --
  /-- `if (⊓) { S₁ } else { S₂ }` -/
  | IfInf (S₁ S₂ : HeyVL)
  /-- `assert φ` -/
  | Assert (φ : 𝔼r)
  /-- `assume φ` -/
  | Assume (φ : 𝔼r)
  /-- `havoc x` -/
  | Havoc (x : Ident)
  /-- `validate` -/
  | Validate
  --
  /-- `if (⊔) { S₁ } else { S₂ }` -/
  | IfSup (S₁ S₂ : HeyVL)
  /-- `coassert φ` -/
  | Coassert (φ : 𝔼r)
  /-- `coassume φ` -/
  | Coassume (φ : 𝔼r)
  /-- `cohavoc x` -/
  | Cohavoc (x : Ident)
  /-- `covalidate` -/
  | Covalidate
deriving Lean.ToExpr, DecidableEq

infixr:50 " ;; " => HeyVL.Seq

def HeyVL.Skip : HeyVL := .Reward 0
def HeyVL.If (b : 𝔼b) (S₁ S₂ : HeyVL) : HeyVL :=
  .IfInf (.Assume b.embed ;; S₁) (.Assume b.not.embed ;; S₂)
def HeyVL.Havocs (xs : List Ident) : HeyVL :=
  match xs with
  | [] => .Skip
  | [x] => .Havoc x
  | x::xs => .Havoc x ;; .Havocs xs
def HeyVL.Cohavocs (xs : List Ident) : HeyVL :=
  match xs with
  | [] => .Skip
  | [x] => .Cohavoc x
  | x::xs => .Cohavoc x ;; .Cohavocs xs
