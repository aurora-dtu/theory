import HeyLo.Expr

open HeyLo

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
