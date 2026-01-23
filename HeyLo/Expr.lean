import Mathlib.Data.NNRat.Order
import PGCL.Exp

open pGCL

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
abbrev Ty.expr : Ty → Type
  | .Bool => BExpr Ident
  | .ENNReal => Exp Ident

inductive QuantVar where
  | Shadow : Ident → QuantVar
  | Fresh : Ident → QuantVar
  | DeBrujin : QuantVar
deriving Lean.ToExpr, DecidableEq, Inhabited

open Lean in
instance : Lean.ToExpr Rat where
  toExpr r :=
    if r.den == 1 then toExpr r.num else  mkApp2 (.const ``Div.div []) (toExpr r.num) (toExpr r.den)
  toTypeExpr := .const ``Rat []

open Lean in
instance : Lean.ToExpr NNRat where
  toExpr r :=
    if r.den == 1 then toExpr r.num else  mkApp2 (.const ``Div.div []) (toExpr r.num) (toExpr r.den)
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

end HeyLo

-- a ↙ b = (a ≤ )

open HeyLo HeyLo.Ty in
inductive HeyLo : Ty → Type where
  -- /- A variable. -/
  -- | Var : Ident → HeyLo  ENNReal
  -- /- A call to a procedure or function. -/
  -- | Call : Ident → List HeyLo  ENNReal → HeyLo  ENNReal
  -- /- Boolean if-then-else -/
  -- | Ite : HeyLo Bool → HeyLo  ENNReal → HeyLo  ENNReal → HeyLo  ENNReal
  | Unary : UnOp α β → HeyLo α → HeyLo β
  | Binary : BinOp α β → HeyLo α → HeyLo α → HeyLo β
  -- /- Type casting. -/
  -- | Cast : HeyLo  ENNReal → HeyLo  ENNReal
  -- /- A quantifier over some variables. -/
  -- | Quant : QuantOp → Ident → HeyLo  ENNReal → HeyLo  ENNReal
  -- /- A substitution. -/
  -- | Subst : Ident → HeyLo  ENNReal → HeyLo  ENNReal → HeyLo  ENNReal
  /- A value literal. -/
  -- /- A de Bruijn index. -/
  -- | DeBruijn : DeBruijnIndex → HeyLo  ENNReal
-- deriving Lean.ToExpr, Inhabited

  /- A variable. -/
  | Var : Ident → HeyLo  ENNReal
  -- /- A call to a procedure or function. -/
  -- | Call : Ident → List HeyLo  ENNReal → HeyLo  ENNReal
  /- Boolean if-then-else -/
  | Ite : HeyLo Bool → HeyLo α → HeyLo α → HeyLo α
  -- /- Type casting. -/
  -- | Cast : HeyLo  ENNReal → HeyLo  ENNReal
  /- A quantifier over some variables. -/
  | Quant : QuantOp α → Ident → HeyLo α → HeyLo α
  /- A substitution. -/
  | Subst : Ident → HeyLo  ENNReal → HeyLo α → HeyLo α
  /- A value literal. -/
  | Lit : Literal α → HeyLo α
  -- /- A de Bruijn index. -/
  -- | DeBruijn : DeBruijnIndex → HeyLo  ENNReal
deriving DecidableEq, Lean.ToExpr

open HeyLo

namespace HeyLo

scoped notation "𝔼r" => HeyLo Ty.ENNReal
scoped notation "𝔼b" => HeyLo Ty.Bool

end HeyLo

structure Distribution where
  values : Array (NNRat × 𝔼r)
  prop : (values.map (·.fst)).sum = 1
deriving DecidableEq

open Lean in
instance : Lean.ToExpr Distribution where
  toExpr μ :=
    toExpr μ.values
  toTypeExpr := .const ``Distribution []

inductive HeyVL where
  --
  | Assign (x : Ident) (μ : Distribution)
  | Reward (a : 𝔼r)
  | Seq (S₁ S₂ : HeyVL)
  --
  | IfInf (S₁ S₂ : HeyVL)
  | Assert (φ : 𝔼r)
  | Assume (φ : 𝔼r)
  | Havoc (xs : Ident)
  | Validate
  --
  | IfSup (S₁ S₂ : HeyVL)
  | Coassert (φ : 𝔼r)
  | Coassume (φ : 𝔼r)
  | Cohavoc (x : Ident)
  | Covalidate
deriving Lean.ToExpr

/-- Syntax typeclass for Heyting co-implication `↜`. -/
@[notation_class]
class HCoImp (α : Type*) where
  /-- Heyting co-implication `↜` -/
  hcoimp : α → α → α

@[notation_class]
class HCoNot (α : Type*) where
  /-- Co-necation `~` -/
  hconot : α → α

@[notation_class]
class Validate (α : Type*) where
  /-- Validate `▵` -/
  validate : α → α

@[notation_class]
class Covalidate (α : Type*) where
  /-- Co-validate `▿` -/
  covalidate : α → α

export HCoImp (hcoimp)
export HCoNot (hconot)
export Validate (validate)
export Covalidate (covalidate)

@[inherit_doc] infixr:60 " ↜ " => hcoimp
@[inherit_doc] prefix:72 "~ " => hconot
@[inherit_doc] prefix:72 "▵ " => validate
@[inherit_doc] prefix:72 "▿ " => covalidate

instance : Top 𝔼r := ⟨.Lit .Infinity⟩
instance : OfNat 𝔼r n := ⟨.Lit (.UInt n)⟩
instance : Add 𝔼r := ⟨.Binary .Add⟩
instance : Sub 𝔼r := ⟨.Binary .Sub⟩
instance : Mul 𝔼r := ⟨.Binary .Mul⟩
instance : Min 𝔼r := ⟨.Binary .Inf⟩
instance : Max 𝔼r := ⟨.Binary .Sup⟩
instance : HImp 𝔼r := ⟨.Binary .Impl⟩
instance : HCoImp 𝔼r := ⟨.Binary .CoImpl⟩
instance : HNot (HeyLo α) := ⟨.Unary .Not⟩
noncomputable instance {α : Ty} : HNot α.expr :=
  match α with
  | .Bool => inferInstance
  | .ENNReal => inferInstance
instance : HCoNot 𝔼r := ⟨.Unary .Non⟩

instance {α : Type*} [HNot α] : Validate α := ⟨fun x ↦ ￢￢x⟩
instance {α : Type*} [HCoNot α] : Covalidate α := ⟨fun x ↦ ~~x⟩

noncomputable instance {α β : Type*} [HCoImp β] : HCoImp (α → β) := ⟨fun φ ψ σ ↦ φ σ ↜ ψ σ⟩
noncomputable instance {α β : Type*} [HCoNot β] : HCoNot (α → β) := ⟨fun φ σ ↦ ~φ σ⟩

noncomputable instance : HCoImp ENNReal := ⟨fun φ ψ ↦ if φ ≥ ψ then 0 else ψ⟩
noncomputable instance : HCoNot ENNReal := ⟨fun φ ↦ φ ⇨ 0⟩
theorem Exp.himp_apply {φ ψ : Exp ϖ} :
    (φ ⇨ ψ) σ = φ σ ⇨ ψ σ := rfl
@[grind =, simp] theorem Exp.hcoimp_apply {φ ψ : Exp ϖ} :
    (φ ↜ ψ) σ = φ σ ↜ ψ σ := rfl
@[grind =, simp] theorem Exp.hconot_apply {φ : Exp ϖ} :
    (~φ) σ = ~φ σ := rfl

example {φ : ENNReal} : φᶜ = φ ⇨ 0 := by simp [compl, himp]
example {φ : ENNReal} : ￢φ = φ ↜ ⊤ := by simp [hnot, hcoimp]

example {φ ψ : Exp ϖ} : φ ⇨ ψ = fun σ ↦ if φ σ ≤ ψ σ then ⊤ else ψ σ := by ext σ; simp [himp]
example {φ ψ : Exp ϖ} : φ ↜ ψ = fun σ ↦ if ψ σ ≤ φ σ then 0 else ψ σ := by ext σ; simp [hcoimp]
example {φ : Exp ϖ} : ￢ φ = φ ↜ ⊤ := by ext σ; simp [hnot, hcoimp]
example {φ : Exp ϖ} : ~ φ = φ ⇨ 0 := by ext σ; simp [hconot, himp]
example {φ : Exp ϖ} : ￢ φ = fun σ ↦ if φ σ = ⊤ then 0 else ⊤ := by ext σ; simp [hnot]
example {φ : Exp ϖ} : ~ φ = fun σ ↦ if φ σ = 0 then ⊤ else 0 := by ext σ; simp [hconot, himp]

example {φ : Exp ϖ} : ▵ φ = ￢￢φ := by ext σ; simp [validate]
example {φ : Exp ϖ} : ▿ φ = ~~φ := by ext σ; simp [covalidate]
example {φ : Exp ϖ} : ▵ φ = fun σ ↦ if φ σ = ⊤ then ⊤ else 0 := by
  ext σ; simp [validate, hnot]
example {φ : Exp ϖ} : ▿ φ = fun σ ↦ if φ σ = 0 then 0 else ⊤ := by
  ext σ; simp [covalidate, hconot, himp]

@[grind =, simp] theorem Exp.validate_apply {φ : Exp ϖ} :
    (▵ φ) σ = ▵ φ σ := rfl
@[grind =, simp] theorem Exp.covalidate_apply {φ : Exp ϖ} :
    (▿ φ) σ = ▿ φ σ := rfl

def HeyLo.subst (X : HeyLo α) (x : Ident) (Y : 𝔼r) : HeyLo α :=
  .Subst x Y X

instance : Substitution (HeyLo α) (fun (_ : Ident) ↦ 𝔼r) := ⟨fun X x ↦ HeyLo.subst X x.1 x.2⟩

attribute [grind =, simp] Distribution.prop

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

def Distribution.pure (v : 𝔼r) : Distribution := ⟨#[(1, v)], by simp⟩
def Distribution.bind (μ : Distribution) (f : 𝔼r → Distribution) : Distribution :=
  let values := μ.values.flatMap (fun (p, v) ↦ (f v).values.map (fun (p', v') ↦ (p * p', v')))
  {values, prop := by
    simp only [Array.map_flatMap, Array.map_map, values]
    unfold Function.comp
    simp only [Array.flatMap_sum, Array.map_mul_sum, prop, mul_one]
  }
def Distribution.map (μ : Distribution) (f : 𝔼r → 𝔼r) : Distribution :=
  ⟨μ.values.map (fun (p, v) ↦ (p, f v)), by simp; unfold Function.comp; simp⟩

@[grind ., simp]
theorem Distribution.values_ne_empty (μ : Distribution) : μ.values ≠ #[] := by
  have := μ.prop
  grind [zero_ne_one]
@[simp]
theorem Distribution.exists_in_values (μ : Distribution) : ∃ x v, (x, v) ∈ μ.values := by
  have : ∃ x, x ∈ μ.values := by simp [Array.isEmpty_eq_false_iff_exists_mem.mp]
  grind

@[grind =, simp]
theorem Array.sum_replicate {α : Type*} {x : α} [Semiring α] :
    (Array.replicate n x).sum = n * x := by
  induction n with
  | zero => grind
  | succ n ih => grind [push, toList_replicate, List.sum_replicate]

def Distribution.unif (vs : Array 𝔼r) (h : vs ≠ #[]) : Distribution :=
  ⟨vs.map fun v ↦ (1 / vs.size, v), by simp; refine mul_inv_cancel₀ ?_; simp [h]⟩
def Distribution.bin (a : 𝔼r) (p : NNRat) (b : 𝔼r) (hp : p ≤ 1) : Distribution :=
  ⟨#[(p, a), (1 - p, b)], by simp; exact add_tsub_cancel_of_le hp⟩

@[grind =, simp]
theorem Distribution.pure_map {e : 𝔼r} :
    (Distribution.pure e).map f = Distribution.pure (f e) := by
  simp [pure, map]
@[grind =, simp]
theorem Distribution.bin_map {a b : 𝔼r} :
    (Distribution.bin a p b hp).map f = Distribution.bin (f a) p (f b) hp := by
  simp [bin, map]

def Distribution.toExpr (μ : Distribution) : 𝔼r :=
  μ.values.map (fun (p, v) ↦ .Lit (.Frac p) * v) |>.sum
@[grind =, simp]
theorem Distribution.pure_toExpr {a : 𝔼r} :
    (Distribution.pure a).toExpr = .Lit (.Frac 1) * a + 0 := by
  simp [pure, toExpr]
@[grind =, simp]
theorem Distribution.bin_toExpr {a b : 𝔼r} :
    (Distribution.bin a p b hp).toExpr = .Lit (.Frac p) * a + (.Lit (.Frac (1 - p)) * b + 0) := by
  simp [bin, toExpr]

def HeyVL.vp (C : HeyVL) : 𝔼r → 𝔼r := fun φ ↦
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

instance : Inhabited (BExpr Ident) where
  default := ⟨fun _ ↦ false, inferInstance⟩

@[grind =, simp]
def HeyLo.Literal.lit (l : Literal α) : α.lit :=
  match l with
  | .UInt n => n
  | .Frac n => n
  | .Bool b => b
  | .Infinity => ⊤
@[grind =, simp]
def HeyLo.Literal.sem (l : Literal α) : α.expr :=
  match l with
  | .UInt n => n
  | .Frac n => (n : ENNReal)
  | .Bool b => b
  | .Infinity => ⊤

noncomputable def HeyLo.BinOp.sem
    (op : BinOp α β) (l r : α.expr) : β.expr :=
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

noncomputable def HeyLo.UnOp.sem (op : UnOp α β) (x : α.expr) : β.expr :=
  match op with
  | .Not => ￢ x
  | .Non => ~ x
  | .Iverson => i[x]
  | .Embed => i[x] * ⊤

noncomputable def HeyLo.QuantOp.sem (op : HeyLo.QuantOp α) (x : Ident) (m : α.expr) : α.expr :=
  match op with
  | .Inf => ⨅ v, m[x ↦ v]
  | .Sup => ⨆ v, m[x ↦ v]
  | .Forall => BExpr.forall_ x m
  | .Exists => BExpr.exists_ x m

@[reducible]
instance {α : Ty} : Substitution α.expr (fun (_ : Ident) ↦ Ty.ENNReal.expr) :=
  match α with
  | .Bool => inferInstance
  | .ENNReal => inferInstance

noncomputable def HeyLo.sem (X : HeyLo α) : α.expr :=
  match X with
  | .Binary op l r => op.sem l.sem r.sem
  | .Lit l => l.sem
  | .Subst x v m => m.sem[x ↦ v.sem]
  | .Quant op x m => op.sem x m.sem
  | .Ite b l r =>
    match α with
    | .Bool => BExpr.ite b.sem l.sem r.sem
    | .ENNReal => i[b.sem] * l.sem + i[b.sem.not] * r.sem
  | .Var x => fun σ ↦ σ x
  | .Unary op m => op.sem m.sem

@[reducible]
instance {α : Ty} : FunLike α.expr (States Ident) α.lit :=
  match α with
  | .Bool => inferInstanceAs (FunLike (BExpr Ident) (States Ident) Prop)
  | .ENNReal => {coe := id, coe_injective' := fun _ _ a ↦ a}

attribute [simp] Ty.expr
attribute [simp] Ty.lit
attribute [simp] instFunLikeExprStatesIdentLit

@[grind =, simp]
theorem HeyLo.sem_subst {X : HeyLo α} : X[x ↦ v].sem = X.sem[x ↦ v.sem] := rfl
@[grind =, simp]
theorem UnOp.sem_subst {op : UnOp α β} : (op.sem a)[x ↦ v] = op.sem a[x ↦ v] := by
  cases op <;> try rfl
  · cases α <;> rfl
@[grind =, simp]
theorem BinOp.sem_subst {op : BinOp α β} : (op.sem a b)[x ↦ v] = op.sem a[x ↦ v] b[x ↦ v] := by
  cases op <;> try rfl

theorem HeyLo.sem_Inf' : (HeyLo.Quant QuantOp.Inf x c).sem = ⨅ v, c.sem[x ↦ v] := rfl
theorem HeyLo.sem_Sup' : (HeyLo.Quant QuantOp.Sup x c).sem = ⨆ v, c.sem[x ↦ v] := rfl
@[grind =, simp]
theorem HeyLo.sem_Inf : (HeyLo.Quant QuantOp.Inf x c).sem = ⨅ (v : ENNReal), c.sem[x ↦ ↑v] := by
  apply le_antisymm
  · simp [HeyLo.sem_Inf']
    intro y σ
    simp
    apply iInf_le_of_le ↑y
    rfl
  · simp [HeyLo.sem_Inf']
    intro y σ
    simp
    apply iInf_le_of_le (y σ)
    rfl
@[grind =, simp]
theorem HeyLo.sem_Sup : (HeyLo.Quant QuantOp.Sup x c).sem = ⨆ (v : ENNReal), c.sem[x ↦ ↑v] := by
  apply le_antisymm
  · simp [HeyLo.sem_Sup']
    intro y σ
    simp
    apply le_iSup_of_le (y σ)
    rfl
  · simp [HeyLo.sem_Sup']
    intro y σ
    simp
    apply le_iSup_of_le ↑y
    rfl
@[grind =, simp]
theorem HeyLo.sem_Forall_apply :
    (HeyLo.Quant QuantOp.Forall x c).sem σ ↔ ∀ (v : ENNReal), c.sem σ[x ↦ ↑v] := by
  rfl
@[grind =, simp]
theorem HeyLo.sem_Exists_apply :
    (HeyLo.Quant QuantOp.Exists x c).sem σ ↔ ∃ (v : ENNReal), c.sem σ[x ↦ ↑v] := by
  rfl
