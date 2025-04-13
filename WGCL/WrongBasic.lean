import Mathlib.Algebra.Ring.Defs

inductive BExpr (B : Type) where
  | Test : B → BExpr B
  | Zero
  | One
  | Mul : BExpr B → BExpr B → BExpr B
  | Add : BExpr B → BExpr B → BExpr B
  | Neg : BExpr B → BExpr B
deriving Lean.ToExpr

inductive Weighting (F : Type) where
  | Test : F → Weighting F
  | Zero
  | One
  | Mul : Weighting F → Weighting F → Weighting F
  | Add : Weighting F → Weighting F → Weighting F
deriving Lean.ToExpr

inductive Program (P B F : Type) where
  | Atomic : P → Program P B F
  | BTest : BExpr B → Program P B F
  | WTest : Weighting F → Program P B F
  | Mul : Program P B F → Program P B F → Program P B F
  | Add : Program P B F → Program P B F → Program P B F
  | Star : Program P B F → Program P B F
deriving Lean.ToExpr

variable {P B F : Type}

declare_syntax_cat cwyt_bexpr
syntax "wyt_bexpr " "{" cwyt_bexpr "}" : term
declare_syntax_cat cwyt_weigh
syntax "wyt_weigh " "{" cwyt_weigh "}" : term
declare_syntax_cat cwyt_progr
syntax "wyt " "{" cwyt_progr "}" : term

syntax "b0" : cwyt_bexpr
syntax "b1" : cwyt_bexpr

syntax:75 "¬" cwyt_bexpr:75 : cwyt_bexpr

syntax:50 cwyt_bexpr:50 " ⬝ " cwyt_bexpr:51 : cwyt_bexpr
syntax:50 cwyt_bexpr:50 " + " cwyt_bexpr:51 : cwyt_bexpr

syntax "w0" : cwyt_weigh
syntax "w1" : cwyt_weigh

syntax:50 cwyt_weigh:50 " ⬝ " cwyt_weigh:51 : cwyt_weigh
syntax:50 cwyt_weigh:50 " + " cwyt_weigh:51 : cwyt_weigh

syntax cwyt_bexpr:max : cwyt_progr
syntax cwyt_weigh:max : cwyt_progr
syntax:50 cwyt_progr:50 " ⬝ " cwyt_progr:51 : cwyt_progr
syntax:50 cwyt_progr:50 " + " cwyt_progr:51 : cwyt_progr
syntax:75 cwyt_progr:75 "*" : cwyt_progr

macro_rules
-- bexpr
| `(wyt_bexpr { b0 }) => `(BExpr.Zero)
| `(wyt_bexpr { b1 }) => `(BExpr.One)
| `(wyt_bexpr { ¬ $x }) => `(BExpr.Neg wyt_bexpr {$x})
| `(wyt_bexpr { $l ⬝ $r }) => `(BExpr.Mul (wyt_bexpr {$l}) (wyt_bexpr {$r}))
| `(wyt_bexpr { $l + $r }) => `(BExpr.Add (wyt_bexpr {$l}) (wyt_bexpr {$r}))
-- weigh
| `(wyt_weigh { w0 }) => `(Weighting.Zero)
| `(wyt_weigh { w1 }) => `(Weighting.One)
| `(wyt_weigh { $l ⬝ $r }) => `(Weighting.Mul (wyt_weigh {$l}) (wyt_weigh {$r}))
| `(wyt_weigh { $l + $r }) => `(Weighting.Add (wyt_weigh {$l}) (wyt_weigh {$r}))
-- progr
| `(wyt { $b:cwyt_bexpr }) => `(Program.BTest (wyt_bexpr {$b}))
| `(wyt { $w:cwyt_weigh }) => `(Program.WTest (wyt_weigh {$w}))
| `(wyt { $l ⬝ $r }) => `(Program.Mul (wyt {$l}) (wyt {$r}))
| `(wyt { $l + $r }) => `(Program.Add (wyt {$l}) (wyt {$r}))
| `(wyt { $l * }) => `(Program.Star (wyt {$l}))

/-- info: (BExpr.Zero.Mul BExpr.One).Add BExpr.Zero -/
#guard_msgs in
#eval (wyt_bexpr { b0 ⬝ b1 + b0 } : BExpr Unit)

section

open Lean PrettyPrinter Delaborator SubExpr

@[app_unexpander BExpr.Zero]
def BExpr.unexpandZero : Unexpander
| `($(_)) => `(wyt_bexpr { b0 })
@[app_unexpander BExpr.One]
def BExpr.unexpandOne : Unexpander
| `($(_)) => `(wyt_bexpr { b1 })
@[app_unexpander BExpr.Neg]
def BExpr.unexpandNeg : Unexpander
| `($(_) wyt_bexpr {$l}) => `(wyt_bexpr { ¬ $l })
| _ => throw ()
@[app_unexpander BExpr.Mul]
def BExpr.unexpandMul : Unexpander
| `($(_) wyt_bexpr {$l} wyt_bexpr {$r}) => `(wyt_bexpr { $l ⬝ $r })
| _ => throw ()
@[app_unexpander BExpr.Add]
def BExpr.unexpandAdd : Unexpander
| `($(_) wyt_bexpr {$l} wyt_bexpr {$r}) => `(wyt_bexpr { $l + $r })
| _ => throw ()

@[app_unexpander Weighting.Zero]
def Weighting.unexpandZero : Unexpander
| `($(_)) => `(wyt_weigh { w0 })
@[app_unexpander Weighting.One]
def Weighting.unexpandOne : Unexpander
| `($(_)) => `(wyt_weigh { w1 })
@[app_unexpander Weighting.Mul]
def Weighting.unexpandMul : Unexpander
| `($(_) wyt_weigh {$l} wyt_weigh {$r}) => `(wyt_weigh { $l ⬝ $r })
| _ => throw ()
@[app_unexpander Weighting.Add]
def Weighting.unexpandAdd : Unexpander
| `($(_) wyt_weigh {$l} wyt_weigh {$r}) => `(wyt_weigh { $l + $r })
| _ => throw ()

/-- info: wyt_bexpr {b0} -/
#guard_msgs in
#eval (wyt_bexpr { b0 } : BExpr Unit)

/-- info: wyt_bexpr {b0 ⬝ b1 + b0} -/
#guard_msgs in
#eval (wyt_bexpr { b0 ⬝ b1 + b0 } : BExpr Unit)

/-- info: wyt_bexpr {b0 ⬝ ¬b1 + b0} -/
#guard_msgs in
#eval (wyt_bexpr { b0 ⬝ ¬b1 + b0 } : BExpr Unit)

/-- info: wyt_weigh {w0} -/
#guard_msgs in
#eval (wyt_weigh { w0 } : Weighting Unit)

/-- info: wyt_weigh {w0 ⬝ w1 + w0} -/
#guard_msgs in
#eval (wyt_weigh { w0 ⬝ w1 + w0 } : Weighting Unit)

@[app_unexpander Program.BTest]
def Program.unexpandBTest : Unexpander
| `($(_) wyt_bexpr {$l}) => `(wyt { $l:cwyt_bexpr })
| _ => throw ()
@[app_unexpander Program.WTest]
def Program.unexpandWTest : Unexpander
| `($(_) wyt_weigh {$l}) => `(wyt { $l:cwyt_weigh })
| _ => throw ()
@[app_unexpander Program.Add]
def Program.unexpandAdd : Unexpander
| `($(_) wyt {$l} wyt {$r}) => `(wyt { $l + $r })
| _ => throw ()
@[app_unexpander Program.Mul]
def Program.unexpandMul : Unexpander
| `($(_) wyt {$l} wyt {$r}) => `(wyt { $l ⬝ $r })
| _ => throw ()
@[app_unexpander Program.Star]
def Program.unexpandStar : Unexpander
| `($(_) wyt {$l}) => `(wyt { $l * })
| _ => throw ()

/-- info: wyt {w0 + w1 ⬝ b0} -/
#guard_msgs in
#eval (wyt { w0 + w1 ⬝ b0 } : Program Unit Unit Unit)

/-- info: wyt {w0 + w1*} -/
#guard_msgs in
#eval (wyt { w0 + w1* } : Program Unit Unit Unit)
