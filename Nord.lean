import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Data.Rat.Lemmas
import Mathlib.Order.FixedPoints
import Mathlib.Order.Hom.Basic
import Mathlib.Algebra.Order.Monoid.Canonical.Defs

variable (Var : Type)

open Lean Lean.ToExpr in
instance : Lean.ToExpr Rat where
  toExpr r :=
    if r.den == 1 then toExpr r.num else  mkApp2 (.const ``Div.div []) (toExpr r.num) (toExpr r.den)
  toTypeExpr := .const ``Rat []

inductive Literal where
| num : Rat → Literal
| bool : Bool → Literal
deriving Lean.ToExpr

inductive Op where
-- arithmetic
| add | sub | mul | div
-- relational
| lt | le | gt | ge | eq | ne
deriving Lean.ToExpr

inductive Expr where
| lit : Literal -> Expr
| var : Var → Expr
| bin : Op → Expr → Expr → Expr
deriving Lean.ToExpr

inductive Stmt where
| skip
| assign : Var → Expr Var → Stmt
| seq : Stmt → Stmt → Stmt
| ite : Expr Var → Stmt → Stmt → Stmt
| loop : Expr Var → Stmt → Stmt
deriving Lean.ToExpr

section Syntax

open Lean

declare_syntax_cat nord_bool
syntax "[nord_bool|" nord_bool "]" : term
declare_syntax_cat nord_lit
syntax "[nord_lit|" nord_lit "]" : term
declare_syntax_cat nord_var
syntax "[nord_var|" nord_var "]" : term
declare_syntax_cat nord_op
syntax "[nord_op| " nord_op " ]" : term
declare_syntax_cat nord_expr
syntax "[nord_expr|" nord_expr "]" : term
syntax "[nord_expr(" term ")|" nord_expr "]" : term
declare_syntax_cat nord_stmt
syntax "[nord_stmt|" nord_stmt "]" : term
syntax "[nord_stmt(" term ")|" nord_stmt "]" : term

syntax "true" : nord_bool
syntax "false" : nord_bool
syntax num : nord_lit
syntax nord_bool : nord_lit
syntax "~" term:max : nord_lit

syntax ident : nord_var
syntax "~" term:max : nord_var

syntax nord_lit : nord_expr

syntax nord_var : nord_expr

syntax "*" : nord_op
syntax "/" : nord_op
syntax "+" : nord_op
syntax "-" : nord_op
syntax "<" : nord_op
syntax "≤" : nord_op
syntax "<=" : nord_op
syntax ">=" : nord_op
syntax "≥" : nord_op
syntax ">" : nord_op
syntax "=" : nord_op
syntax "!=" : nord_op
syntax "≠" : nord_op

syntax:70 nord_expr:70 " * " nord_expr:71 : nord_expr
syntax:70 nord_expr:70 " / " nord_expr:71 : nord_expr

syntax:65 nord_expr:65 " + " nord_expr:66 : nord_expr
syntax:65 nord_expr:65 " - " nord_expr:66 : nord_expr

syntax:75 "¬" nord_expr:75 : nord_expr

syntax:50 nord_expr:50 " < " nord_expr:51 : nord_expr
syntax:50 nord_expr:50 " ≤ " nord_expr:51 : nord_expr
syntax:50 nord_expr:50 " <= " nord_expr:51 : nord_expr
syntax:50 nord_expr:50 " >= " nord_expr:51 : nord_expr
syntax:50 nord_expr:50 " ≥ " nord_expr:51 : nord_expr
syntax:50 nord_expr:50 " > " nord_expr:51 : nord_expr
syntax:45 nord_expr:45 " = " nord_expr:46 : nord_expr
syntax:45 nord_expr:45 " != " nord_expr:46 : nord_expr
syntax:45 nord_expr:45 " ≠ " nord_expr:46 : nord_expr

syntax:35 nord_expr:35 " ∧ " nord_expr:36 : nord_expr
syntax:35 nord_expr:35 " ∨ " nord_expr:36 : nord_expr

syntax "(" nord_expr ")" : nord_expr

syntax nord_expr "~" term:max nord_expr : nord_expr

syntax "~" term:max : nord_expr

syntax "skip" : nord_stmt
syntax "let " ident " := " nord_expr : nord_stmt
syntax "let " "~" term:max " := " nord_expr : nord_stmt
syntax nord_var " := " nord_expr : nord_stmt
syntax nord_stmt " ; " nord_stmt : nord_stmt
syntax "if " nord_expr "{" nord_stmt "}" " else " "{" nord_stmt "}" : nord_stmt
syntax "while " nord_expr "{" nord_stmt "}" : nord_stmt

syntax "~" term:max : nord_stmt

macro_rules
| `([nord_bool| true ]) => `(True)
| `([nord_bool| false ]) => `(False)

macro_rules
| `([nord_lit| ~$n:term ]) => `($n)
| `([nord_lit| $n:num ]) => `(Literal.num $n)
| `([nord_lit| $b:nord_bool ]) => `(Literal.bool [nord_bool|$b])

macro_rules
| `([nord_var| $n:ident ]) => `(term|$(quote n.getId.toString))
| `([nord_var| ~$n:term ]) => `($n)

macro_rules
| `([nord_op| *  ]) => `(Op.mul)
| `([nord_op| /  ]) => `(Op.div)
| `([nord_op| +  ]) => `(Op.add)
| `([nord_op| -  ]) => `(Op.sub)
| `([nord_op| <  ]) => `(Op.lt)
| `([nord_op| ≤  ]) => `(Op.le)
| `([nord_op| <= ]) => `(Op.le)
| `([nord_op| >  ]) => `(Op.gt)
| `([nord_op| ≥  ]) => `(Op.ge)
| `([nord_op| >= ]) => `(Op.ge)
| `([nord_op| =  ]) => `(Op.eq)
| `([nord_op| != ]) => `(Op.ne)
| `([nord_op| ≠  ]) => `(Op.ne)

macro_rules
-- literals
| `([nord_expr| $l:nord_lit ]) => `(Expr.lit [nord_lit|$l])
-- | `([nord_expr| @lit $l:nord_lit ]) => `(Expr.lit [nord_lit|$l])
-- | `([nord_expr| @lit ~$l:term ]) => `(Expr.lit $l)
| `([nord_expr| $l:nord_var ]) => `(Expr.var [nord_var|$l])
-- arithmetic
| `([nord_expr| $l * $r ]) => `(Expr.bin .mul [nord_expr|$l] [nord_expr|$r])
| `([nord_expr| $l / $r ]) => `(Expr.bin .div [nord_expr|$l] [nord_expr|$r])
| `([nord_expr| $l + $r ]) => `(Expr.bin .add [nord_expr|$l] [nord_expr|$r])
| `([nord_expr| $l - $r ]) => `(Expr.bin .sub [nord_expr|$l] [nord_expr|$r])
-- relational
| `([nord_expr| $l < $r  ]) => `(Expr.bin [nord_op| <  ] [nord_expr|$l] [nord_expr|$r])
| `([nord_expr| $l ≤ $r  ]) => `(Expr.bin [nord_op| ≤  ] [nord_expr|$l] [nord_expr|$r])
| `([nord_expr| $l <= $r ]) => `(Expr.bin [nord_op| <= ] [nord_expr|$l] [nord_expr|$r])
| `([nord_expr| $l >= $r ]) => `(Expr.bin [nord_op| >= ] [nord_expr|$l] [nord_expr|$r])
| `([nord_expr| $l ≥ $r  ]) => `(Expr.bin [nord_op| ≥  ] [nord_expr|$l] [nord_expr|$r])
| `([nord_expr| $l > $r  ]) => `(Expr.bin [nord_op| >  ] [nord_expr|$l] [nord_expr|$r])
| `([nord_expr| $l = $r  ]) => `(Expr.bin [nord_op| =  ] [nord_expr|$l] [nord_expr|$r])
| `([nord_expr| $l != $r ]) => `(Expr.bin [nord_op| != ] [nord_expr|$l] [nord_expr|$r])
| `([nord_expr| $l ≠ $r  ]) => `(Expr.bin [nord_op| ≠  ] [nord_expr|$l] [nord_expr|$r])
-- logic
-- syntax:35 nord_expr:35 " ∧ " nord_expr:36 : nord_expr
-- syntax:35 nord_expr:35 " ∨ " nord_expr:36 : nord_expr
| `([nord_expr| $l ~$op $r  ]) => `(Expr.bin $op [nord_expr|$l] [nord_expr|$r])
-- rest
| `([nord_expr| ($t:nord_expr) ]) => `([nord_expr|$t])
| `([nord_expr| ~ $t:term ]) => `($t)
| `([nord_expr( $ty )| $e:nord_expr ]) => `(([nord_expr|$e] : Expr $ty))

macro_rules
| `([nord_stmt|skip]) => `(Stmt.skip)
| `([nord_stmt|let $x:ident := $e]) => `(Stmt.assign $(quote x.getId.toString) [nord_expr|$e])
| `([nord_stmt|let ~ $x := $e]) => `(Stmt.assign $x [nord_expr|$e])
| `([nord_stmt|$x:nord_var := $e]) => `(Stmt.assign [nord_var|$x] [nord_expr|$e])
| `([nord_stmt|$c₁:nord_stmt ; $c₂]) => `(Stmt.seq [nord_stmt|$c₁] [nord_stmt|$c₂])
| `([nord_stmt|if $c { $c₁ } else { $c₂ }]) => `(Stmt.ite [nord_expr|$c] [nord_stmt|$c₁] [nord_stmt|$c₂])
| `([nord_stmt|while $c { $c₁ }]) => `(Stmt.loop [nord_expr|$c] [nord_stmt|$c₁])
| `([nord_stmt|~$c:term]) => `($c)
| `([nord_stmt( $ty )| $e:nord_stmt ]) => `(([nord_stmt|$e] : Stmt $ty))

#check [nord_lit|12]
#check [nord_stmt|x := 13 + 3]

end Syntax

structure Memory (Val : Type) where
  read : Var → Val
deriving Inhabited

section ToExpr

open Lean (ToExpr mkApp mkApp2 mkApp3 mkApp4)
open Lean.ToExpr

#eval ((1 : Rat) / (13 : Rat))

-- instance : ToExpr Literal where
--   toExpr l := match l with
--     | .num n => mkApp (.const ``Literal.num []) (toExpr n)
--     | .bool b => mkApp (.const ``Literal.bool []) (toExpr b)
--   toTypeExpr := .const ``Literal []

-- instance : ToExpr Op where
--   toExpr op := match op with
--     | [nord_op| * ] => .const ``Op.mul []
--     | [nord_op| / ] => .const ``Op.div []
--     | [nord_op| + ] => .const ``Op.add []
--     | [nord_op| - ] => .const ``Op.sub []
--     -- relational
--     | [nord_op| < ] => .const ``Op.lt []
--     | [nord_op| ≤ ] => .const ``Op.le []
--     | [nord_op| ≥ ] => .const ``Op.ge []
--     | [nord_op| > ] => .const ``Op.gt []
--     | [nord_op| = ] => .const ``Op.eq []
--     | [nord_op| ≠ ] => .const ``Op.ne []
--   toTypeExpr := .const ``Op []

#check [nord_expr(String)|12]

-- def Expr.toExpr [ToExpr Var] : Expr Var → Lean.Expr
--   | .lit l => mkApp2 (.const ``Expr.lit []) (toTypeExpr Var) (ToExpr.toExpr l)
--   | .var x => mkApp2 (.const ``Expr.var []) (toTypeExpr Var) (ToExpr.toExpr x)
--   -- arithmetic
--   | [nord_expr| ~l * ~r ] => mkBin [nord_op| * ] l.toExpr r.toExpr
--   | [nord_expr| ~l / ~r ] => mkBin [nord_op| / ] l.toExpr r.toExpr
--   | [nord_expr| ~l + ~r ] => mkBin [nord_op| + ] l.toExpr r.toExpr
--   | [nord_expr| ~l - ~r ] => mkBin [nord_op| - ] l.toExpr r.toExpr
--   -- relational
--   | [nord_expr| ~l < ~r ] => mkBin [nord_op| < ] l.toExpr r.toExpr
--   | [nord_expr| ~l ≤ ~r ] => mkBin [nord_op| ≤ ] l.toExpr r.toExpr
--   | [nord_expr| ~l ≥ ~r ] => mkBin [nord_op| ≥ ] l.toExpr r.toExpr
--   | [nord_expr| ~l > ~r ] => mkBin [nord_op| > ] l.toExpr r.toExpr
--   | [nord_expr| ~l = ~r ] => mkBin [nord_op| = ] l.toExpr r.toExpr
--   | [nord_expr| ~l ≠ ~r ] => mkBin [nord_op| ≠ ] l.toExpr r.toExpr
-- where mkBin o l r :=
--   mkApp4 (.const ``Expr.bin []) (toTypeExpr Var) (ToExpr.toExpr o) l r

-- instance [ToExpr Var] : ToExpr (Expr Var) where
--   toExpr e := e.toExpr
--   toTypeExpr := mkApp (.const ``Expr []) (toTypeExpr Var)

#eval [nord_expr(String)|true]
#eval [nord_expr(String)|12]

-- instance [ToExpr Var] [ToExpr Val] : ToExpr (Memory Var Val) where
--   toExpr m := .const ``Bool []
--   toTypeExpr := .const ``Memory []

end ToExpr

section Delab

open Lean PrettyPrinter Delaborator SubExpr

@[app_unexpander _root_.Op.add] def Op.unexpandAdd : Unexpander | `($_op) => `([nord_op|+])
@[app_unexpander _root_.Op.sub] def Op.unexpandSub : Unexpander | `($_op) => `([nord_op|-])
@[app_unexpander _root_.Op.mul] def Op.unexpandMul : Unexpander | `($_op) => `([nord_op|*])
@[app_unexpander _root_.Op.div] def Op.unexpandDiv : Unexpander | `($_op) => `([nord_op|/])
@[app_unexpander _root_.Op.le] def Op.unexpandLe : Unexpander | `($_op) => `([nord_op|≤])
@[app_unexpander _root_.Op.eq] def Op.unexpandEq : Unexpander | `($_op) => `([nord_op|=])

#check [nord_op| + ]
#check [nord_op| - ]
#check [nord_op| ≤ ]

@[app_unexpander _root_.Literal.num]
def Literal.unexpandNum : Unexpander
  | `($_num $e:num) => `([nord_lit|$e:num])
  | _ => throw ()

#check [nord_lit|12]

#check [nord_var|xyz]

@[app_unexpander _root_.Expr.lit]
def Expr.unexpandLit : Unexpander
  | `($_lit [nord_lit|$e:nord_lit]) => `([nord_expr|$e:nord_lit])
  | _ => throw ()

#check [nord_expr|12]

instance : Coe NumLit (TSyntax `nord_expr) where
  coe s := ⟨s.raw⟩

instance : Coe Ident (TSyntax `nord_expr) where
  coe s := ⟨s.raw⟩

@[app_unexpander _root_.Expr.var]
def Expr.unexpandVar : Unexpander
  | `($_x $y:str) =>
    let str := y.getString
    let name := mkIdent $ Name.mkSimple str
    `([nord_expr|$name])
  | _ => throw ()

/-- info: [nord_expr|x] : _root_.Expr String -/
#guard_msgs in
#check [nord_expr|x]

@[app_unexpander _root_.Expr.bin]
def Expr.unexpandBin : Unexpander
  | `($_bin [nord_op| + ] [nord_expr|$l] [nord_expr|$r]) => `([nord_expr|$l + $r])
  | `($_bin [nord_op| - ] [nord_expr|$l] [nord_expr|$r]) => `([nord_expr|$l - $r])
  | `($_bin [nord_op| * ] [nord_expr|$l] [nord_expr|$r]) => `([nord_expr|$l * $r])
  | `($_bin [nord_op| = ] [nord_expr|$l] [nord_expr|$r]) => `([nord_expr|$l = $r])
  | `($_bin [nord_op| ≤ ] [nord_expr|$l] [nord_expr|$r]) => `([nord_expr|$l ≤ $r])
  | _ => throw ()

/-- info: [nord_expr|420 + 10 - x * 3 = 12] : _root_.Expr String -/
#guard_msgs in
#check [nord_expr(String)|420 + 10  - x * 3 = 12]

/-- info: [nord_expr|a + b * c] : _root_.Expr String -/
#guard_msgs in
#check [nord_expr(String)|a + b * c]
/-- info: [nord_expr|a + b * c] : _root_.Expr String -/
#guard_msgs in
#check [nord_expr(String)|(a + b) * c]

@[app_unexpander _root_.Stmt.skip]
def Stmt.unexpandSkip : Unexpander
  | `($_skip) => `([nord_stmt|skip])

/-- info: [nord_stmt|skip] : Stmt String -/
#guard_msgs in
#check [nord_stmt(String)|skip]

@[app_unexpander _root_.Stmt.assign]
def Stmt.unexpandAssign : Unexpander
  | `($_assign $x:str [nord_expr|$e]) =>
    let s := x.getString
    let name := mkIdent $ Name.mkSimple s
    `([nord_stmt|let $name := $e:nord_expr])
  | _ => throw ()

/-- info: [nord_stmt|let z := x + y] : Stmt String -/
#guard_msgs in
#check [nord_stmt|z := x + y]

@[app_unexpander _root_.Stmt.seq]
def Stmt.unexpandSeq : Unexpander
  | `($_skip [nord_stmt|$c₁] [nord_stmt|$c₂]) =>
    `([nord_stmt|$c₁ ; $c₂])
  | _ => throw ()

/-- info: [nord_stmt|let a := b ; let c := d] : Stmt String -/
#guard_msgs in
#check [nord_stmt|a := b ; c := d]

end Delab

variable {Var : Type} [DecidableEq Var]

def Memory.set (σ : Memory Var Val) (x : Var) (v : Val) : Memory Var Val := sorry

@[simp]
theorem Memory.set_read (σ : Memory Var Val) :
    (σ.set x v).read y = if x = y then v else σ.read y := sorry

section Semantics

variable {Var : Type}
variable (σ : Memory Var Rat)

def Expr.eval : Expr Var → Memory Var Rat → Rat
| .lit (.num x), _ => x
| .lit (.bool b), _ => if b = True then 1 else 0
| .var x, σ => σ.read x
| [nord_expr| ~l ~op ~r ], σ =>
  match op with
  -- arithmetic
  | [nord_op| * ] => l.eval σ * r.eval σ
  | [nord_op| / ] => l.eval σ / r.eval σ
  | [nord_op| + ] => l.eval σ + r.eval σ
  | [nord_op| - ] => l.eval σ - r.eval σ
  -- relational
  | [nord_op| <  ] => q <| l.eval σ < r.eval σ
  | [nord_op| ≤  ] => q <| l.eval σ ≤ r.eval σ
  | [nord_op| ≥  ] => q <| l.eval σ ≥ r.eval σ
  | [nord_op| >  ] => q <| l.eval σ > r.eval σ
  | [nord_op| =  ] => q <| l.eval σ = r.eval σ
  | [nord_op| ≠  ] => q <| l.eval σ ≠ r.eval σ
where
  q : Bool → Rat := (if · then 1 else 0)

attribute [simp] Expr.eval.q

#eval [nord_expr(String)|12 + 13 * 15 ≥ 10 * x].eval default

structure Configuration (Var : Type) (Val : Type) where
  val : WithBot (WithBot (Stmt Var) × Memory Var Val)

instance : Bot (Configuration Var Val) where
  bot := ⟨⊥⟩

syntax:max "conf " "⟨" "⊥" "," term:max "⟩" : term
syntax:max "conf " "⟨" nord_stmt "," term "⟩" : term

macro_rules
| `(conf ⟨⊥,$σ⟩) => `((⟨some ⟨⊥, $σ⟩⟩ : Configuration _ _))
| `(conf ⟨$c,$σ⟩) => `((⟨some ⟨some [nord_stmt|$c], $σ⟩⟩ : Configuration _ _))

syntax:max term noWs "[" withoutPosition(term) " ↦ " withoutPosition(term) "]" : term
macro_rules | `($x[$i ↦ $j]) => `(Memory.set $x $i $j)

def Configuration.seq (c : Configuration Var Val) (c' : Stmt Var) (σ : Memory Var Val) :
    Configuration Var Val :=
  match c with
  | conf ⟨~c, σ'⟩ => conf ⟨~c ; ~c', σ'⟩
  | conf ⟨⊥, σ'⟩ => conf ⟨~c', σ'⟩
  | ⊥ => conf ⟨~c', σ⟩

def Configuration.next (c : Configuration Var ℚ) : Set (Configuration Var ℚ) :=
  match _ : c with
  | conf ⟨skip, σ⟩ => {conf ⟨⊥, σ⟩}
  | conf ⟨let ~x := ~e, σ⟩ => {conf ⟨⊥, σ[x ↦ e.eval σ]⟩}
  | conf ⟨~c₁ ; ~c₂, σ⟩ => {c'.seq c₂ σ | c' ∈ Configuration.next conf ⟨~c₁, σ⟩}
  | conf ⟨if ~c {~c₁} else {~c₂}, σ⟩ => if c.eval σ = 1 then {conf ⟨~c₁, σ⟩} else {conf ⟨~c₂, σ⟩}
  | conf ⟨while ~c {~c'}, σ⟩ => {conf ⟨if ~c { ~c' ; while ~c {~c'} } else { skip }, σ⟩}
  | conf ⟨⊥, _⟩ => ⊥
  | ⊥  => ⊥
termination_by match c with | conf ⟨~c, _⟩ => SizeOf.sizeOf c | _ => 0
decreasing_by simp_all; omega

end Semantics

section WeakestPrecondition

@[simp]
def Expr.subst : Expr Var → Var → Expr Var → Expr Var
| .lit x, _, _ => .lit x
| .var x, v, e => if x = v then e else .var x
| [nord_expr| ~l ~op ~r ], v, e => [nord_expr| ~(l.subst v e) ~op ~(r.subst v e) ]

@[simp]
theorem Expr.subst_eval (e : Expr Var) (x : Var) :
    (e.subst x a).eval σ = e.eval (σ.set x (a.eval σ)) := by
  induction e with
  | lit l => cases l <;> simp [subst, eval]
  | var y =>
    if x = y then
      simp_all [subst, eval]
    else
      simp_all [subst, eval, eq_comm]
  | bin op => cases op <;> simp_all [subst, eval]

/-- A version of `OrderHom.lfp` that does not require `f` the `Monotone` upfront. -/
protected def wpc.lfp {α} [CompleteLattice α] (f : α → α) : α := sInf {a | f a ≤ a}

namespace wpc.lfp

variable [CompleteLattice α]

theorem monotone : Monotone (wpc.lfp (α:=α)) := by
  intro f g h
  simp_all [wpc.lfp]
  intro x h'
  apply sInf_le
  simp [le_trans (h x) h']

@[simp] theorem wp_lfp_eq_lfp (f : α → α) (h : Monotone f) : wpc.lfp f = OrderHom.lfp ⟨f, h⟩ := rfl
@[simp] theorem wp_lfp_eq_lfp_OrderHom (f : α →o α) : wpc.lfp f = OrderHom.lfp f := rfl

end wpc.lfp

def Stmt.wpc : Stmt Var → Expr Var → Expr Var
| [nord_stmt| skip ] => id
| [nord_stmt| ~x := ~e ] => (·.subst x e)
| [nord_stmt| ~c₁ ; ~c₂ ] => c₁.wpc ∘ c₂.wpc
| [nord_stmt| if ~c { ~c₁ } else { ~c₂ }] =>
  fun X ↦ [nord_expr| ~c * ~(c₁.wpc X) + (1 - ~c) * ~(c₂.wpc X)]
| [nord_stmt| while ~c { ~c' }] => fun _ ↦ [nord_expr|0]
  -- fun X ↦ wpc.lfp (c * c₁.wpc · + (1 - c) * X)


  -- fun X ↦ [nord_expr| ~c * ~(c₁.wpc X) + (1 - ~c) * ~(c₁.wpc X)]

instance : Preorder (Expr Var) where
  le e₁ e₂ := ∀ σ, e₁.eval σ ≤ e₂.eval σ
  le_refl := by simp
  le_trans a b c hab hbc σ := le_trans (hab σ) (hbc σ)

instance [Preorder Val] : Preorder (Memory Var Val) where
  le m₁ m₂ := ∀ x, m₁.read x ≤ m₂.read x
  le_refl := by simp
  le_trans a b c hab hbc σ := le_trans (hab σ) (hbc σ)

theorem Stmt.wpc_mono (c : Stmt Var) : Monotone c.wpc := by
  induction c
  next n => exact fun ⦃a b⦄ a => a
  next x e =>
    simp [wpc]
    intro a b h σ
    simp_all [instPreorderExpr]
  next c₁ c₂ ih₁ ih₂ =>
    intro a b h σ
    simp_all [wpc, instPreorderExpr]
    exact ih₁ (ih₂ h) σ
  next c c₁ c₂ ih₁ ih₂ =>
    intro a b h σ
    simp_all [wpc, instPreorderExpr, Expr.eval]
    have ht : ∀ {a b c : ℚ}, b ≤ c → a * b ≤ a * c := by
      sorry
    gcongr
    · apply ht (ih₁ h σ)
    · apply ht (ih₂ h σ)
  next c c' ih => intro a b h σ; rfl

syntax "triple " "{" nord_expr "} " nord_stmt " {" nord_expr "}" : term

def Expr.valid (e : Expr Var) : Prop := ∀ σ, e.eval σ = 1

@[mk_iff]
structure Triple (P : Expr Var) (C : Stmt Var) (Q : Expr Var) : Prop where
  valid : [nord_expr|~P ≤ ~(C.wpc Q)].valid

macro_rules
-- | `(triple { $P } $C { $Q }) => `([nord_expr|$P ≤ ~([nord_stmt|$C].wpc [nord_expr|$Q])].valid)
| `(triple { $P } $C { $Q }) => `(Triple [nord_expr|$P] [nord_stmt|$C] [nord_expr|$Q])

/-- info: [nord_expr|12 + 2] -/
#guard_msgs in
#eval [nord_stmt|x := 12].wpc [nord_expr|x + 2]

theorem Rule.consequense (P Q : Expr Var) (c : Stmt Var)
  (h₁ : P ≤ P')
  (h₂ : Q' ≤ Q)
  (h₃ : triple { ~P' } ~c { ~Q' }) :
    triple { ~P } ~c { ~Q } := by
  simp_all [triple_iff]
  intro σ
  simp_all [Stmt.wpc, Expr.valid, Expr.eval]
  apply le_trans h₁ <| le_trans h₃ (c.wpc_mono h₂)

theorem Rule.seq {P Q} (O : Expr Var)
  (h₁ : triple {~P} ~c₁ {~O})
  (h₂ : triple {~O} ~c₂ {~Q}) :
    triple { ~P } ~c₁ ; ~c₂ { ~Q } := by
  simp_all [triple_iff]
  intro σ
  simp_all [Stmt.wpc, Expr.valid, Expr.eval]
  apply le_trans (h₁ σ) (c₁.wpc_mono h₂ σ)

end WeakestPrecondition

section Simplify

def Literal.asRat : Literal → Rat
| .num n => n
| .bool b => if b then 1 else 0

@[simp]
def Expr.simplify : Expr Var → Expr Var
| .lit l => .lit l
| .var x => .var x
| [nord_expr| ~l ~op ~r ] =>
  match l.simplify, r.simplify with
  | .lit l, .lit r =>
    let l := l.asRat
    let r := r.asRat
    let res := match op with
      -- arithmetic
      | [nord_op| * ] => l * r
      | [nord_op| / ] => l / r
      | [nord_op| + ] => l + r
      | [nord_op| - ] => l - r
      -- relational
      | [nord_op| <  ] => q <| l < r
      | [nord_op| ≤  ] => q <| l ≤ r
      | [nord_op| ≥  ] => q <| l ≥ r
      | [nord_op| >  ] => q <| l > r
      | [nord_op| =  ] => q <| l = r
      | [nord_op| ≠  ] => q <| l ≠ r
    .lit (.num res)
  | l, r => [nord_expr|~l ~op ~r]
where
  q : Bool → Rat := (if · then 1 else 0)

attribute [simp] Expr.simplify.q

@[simp]
  theorem Expr.lit_eval : (Expr.lit l).eval σ = l.asRat := by
  cases l <;> simp_all [eval, Literal.asRat]

omit [DecidableEq Var]

attribute [local simp] Expr.simplify in
theorem Expr.simplify_preserve (e : Expr Var) : e.simplify.eval = e.eval := by
  induction e
  next l => cases l <;> simp_all
  next v => simp
  next op l r ih₁ ih₂ =>
    simp_all
    ext σ
    split
    · simp_all [eval]
      symm at ih₁ ih₂
      cases op <;> simp_all [eval]
    · simp_all [eval]

/-- info: [nord_expr|14] -/
#guard_msgs in
#eval [nord_stmt|x := 12].wpc [nord_expr|x + 2] |>.simplify

theorem Expr.valid_simplify (e : Expr Var) : e.simplify.valid = e.valid := by
  simp [valid, simplify_preserve]

attribute [simp] Stmt.wpc

example : triple { x = 1 } z := x + y ; w := z * 2 { w = 2*y + 2 } := by
  simp_all [triple_iff, Expr.valid, Expr.eval, add_comm, add_mul, mul_comm, mul_add]

section Unexpand

open Lean PrettyPrinter Delaborator SubExpr

@[app_unexpander _root_.Triple]
def Triple.unexpand : Unexpander
| `($_triple [nord_expr|$x] [nord_stmt|$y] [nord_expr|$z]) => `(triple {$x} $y {$z})
| _ => throw ()

/-- info: triple {x = 1} skip {x = 2} : Prop -/
#guard_msgs in
#check triple {x = 1} skip {x = 2}

end Unexpand

variable [DecidableEq Var] in
theorem Triple.assign {P Q : Expr Var} (h : [nord_expr|~P ≤ ~(Q.subst x e)].valid) :
    triple {~P} ~x := ~e {~Q} := by
  simp_all [triple_iff, Expr.valid, Expr.eval]
  -- intro σ
  -- have := h σ
  -- simp_all

syntax "hoare " "seq " nord_expr : tactic
syntax "hoare " "simp" : tactic

macro_rules
| `(tactic| hoare seq $x) => `(tactic| apply Rule.seq [nord_expr|$x])
| `(tactic| hoare simp) => `(tactic| repeat (first | apply Triple.assign | simp))

end Simplify

















example : triple { x = 1 } z := x + y ; w := z * 2 { w = 2*y + 2 } := by
  hoare seq z = y + 1
  · hoare simp
    intro σ; simp_all [Expr.eval, add_comm]
  · hoare simp
    intro σ; simp_all [Expr.valid, Expr.eval, add_comm, add_mul, mul_comm, mul_add]
    split_ifs <;> try simp_all [mul_add]
    rfl
