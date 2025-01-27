import Mathlib.Algebra.BigOperators.Group.List.Defs
import Mathlib.Algebra.Field.Rat

namespace Ex

inductive Act where | N | L | R
deriving Inhabited, Repr

inductive State where
| s : Nat → State
| s' : Nat → State
| st : Nat → State
| sL : Nat → State
| sR : Nat → State
deriving Inhabited, Repr

def State.complete (n : Nat) : List State :=
  List.range n |>.map (fun i ↦ [.s i, .s' i, .st i, .sL i, .sR i]) |>.flatten

def act : State → List Act
| .s' _ => [.L, .R]
| _ => [.N]

def succs : State → List State
| .s i => [.s' i, .st i]
| .st i => [.st i]
| .s' i => [.sL i, .sR i]
| .sL i => [.s i]
| .sR i => [.s (i + 1)]

def P : State → Act → State → Rat
| .s i, .N, .s' j => if i = j then 1/i else 0
| .s i, .N, .st j => if i = j then 1 - 1/i else 0
| .st i, .N, .st j => if i = j then 1 else 0
| .s' i, .L, .sL j => if i = j then 1 else 0
| .s' i, .R, .sR j => if i = j then 1 else 0
| .sL i, .N, .s j => if i = j then 1 else 0
| .sR i, .N, .s j => if i + 1 = j then 1 else 0
| _, _, _ => 0

def cost : State → Rat
| .sL _ => 1
| .sR _ => 10
-- | .sR _ => 1.3
| _ => 0

def φ (v : State → Rat) (s : State) : Rat :=
  cost s + ((act s).map fun (α : Act) ↦ (succs s).map (P s α * v) |>.sum).min?.getD 0

def φ' (S : State → Act) (v : State → Rat) (s : State) : Rat :=
  cost s + ((succs s).map (P s (S s) * v) |>.sum)

-- n=0 => 1
-- n=1 => 5.25
-- n=2 => 6.75
-- n=3 => 7.1
-- n=4 => 7.1683
-- n=5 => 7.182540
-- n=6 => 7.182540
-- n=7 => 7.182816
-- n=8 => 7.182818
-- n=9 => 7.182818

def S : State → Act
| .s' i => if i = 3 then .L else .R
-- | .s' 3 => .R
-- | .s' 4 => .R
-- | .s' 5 => .R
-- | .s' 6 => .R
-- | .s' 7 => .R
-- | .s' 8 => .R
-- | .s' 9 => .R
-- | .s' 10 => .R
-- | .s' 11 => .R
-- | .s' _ => .L
| _ => .N

def Paths (n : Nat) (s : State) : List (List State) :=
  match n with
  | 0 => [[s]]
  | n+1 => Paths n s |>.map (fun p ↦ succs p.getLast! |>.map (p ++ [·])) |>.flatten

def Prob (S : State → Act) (p : List State) : Rat :=
  List.range (p.length - 1) |>.map (fun i ↦ P p[i]! (S p[i]!) p[i + 1]!) |>.prod
def Prob' (S : List State → Act) (p : List State) : Rat :=
  List.range (p.length - 1) |>.map (fun i ↦ P p[i]! (S (p.take (i + 1))) p[i + 1]!) |>.prod
def Cost (p : List State) : Rat := List.range p.length |>.map (fun i ↦ cost p[i]!) |>.sum
def EC (S : State → Act) (p : List State) : Rat := Prob S p * Cost p
def EC' (S : List State → Act) (p : List State) : Rat := Prob' S p * Cost p

instance : Repr State where
  reprPrec s _ := match s with
  | .s i => "a(" ++ i.repr ++ ")"
  | .s' i => "b(" ++ i.repr ++ ")"
  | .st i => "t(" ++ i.repr ++ ")"
  | .sL i => "L(" ++ i.repr ++ ")"
  | .sR i => "L(" ++ i.repr ++ ")"

instance : Repr State where
  reprPrec s _ := match s with
  | .s i => "\\nSa{" ++ i.repr ++ "}"
  | .s' i => "\\nSb{" ++ i.repr ++ "}"
  | .st i => "\\nSt{" ++ i.repr ++ "}"
  | .sL i => "\\nSL{" ++ i.repr ++ "}"
  | .sR i => "\\nSR{" ++ i.repr ++ "}"

def S' (p : List State) : Act :=
  match p.getLast! with
  | .s' _ =>
    if p.length = 2 then .L else .R
  | _ => .N

-- #eval Paths 2 (.s 2)
-- #eval Paths 2 (.s 2) |>.map (Prob S)
-- #eval Paths 2 (.s 2) |>.map Cost
-- #eval Paths 2 (.s 2) |>.map (EC S)
#eval Paths 8 (.s 2) |>.map (fun p ↦ (p, Prob S p, Cost p, EC S p))
#eval Paths 8 (.s 2) |>.map (fun p ↦ (Prob S p * Cost p)) |>.sum
#eval Paths 8 (.s 2) |>.filter (fun p ↦ 0 < Prob S p)
-- #eval Paths 20 (.s 2) |>.map (EC S) |>.sum |>.toFloat
-- #eval Paths 20 (.s 2) |>.map (EC' S') |>.sum |>.toFloat

-- #eval (φ' S)^[5] (fun _ ↦ 0) (.s 2) |>.toFloat
-- #eval (φ' S)^[10] (fun _ ↦ 0) (.s 2) |>.toFloat
-- #eval (φ' S)^[15] (fun _ ↦ 0) (.s 2) |>.toFloat
-- #eval (φ' S)^[20] (fun _ ↦ 0) (.s 2) |>.toFloat
-- #eval (φ' S)^[25] (fun _ ↦ 0) (.s 2) |>.toFloat
-- #eval (φ' S)^[30] (fun _ ↦ 0) (.s 2) |>.toFloat
-- #eval (φ' S)^[35] (fun _ ↦ 0) (.s 2) |>.toFloat
-- #eval (φ' S)^[40] (fun _ ↦ 0) (.s 2) |>.toFloat
-- #eval (φ' S)^[45] (fun _ ↦ 0) (.s 2) - 5.25
-- #eval (φ' S)^[50] (fun _ ↦ 0) (.s 2) - 5.25

-- #eval "---"

-- #eval φ^[5] (fun _ ↦ 0) (.s 2) |>.toFloat
-- #eval φ^[10] (fun _ ↦ 0) (.s 2) |>.toFloat
-- #eval φ^[15] (fun _ ↦ 0) (.s 2) |>.toFloat
-- #eval φ^[20] (fun _ ↦ 0) (.s 2) |>.toFloat
-- #eval φ^[25] (fun _ ↦ 0) (.s 2) |>.toFloat
-- #eval φ^[30] (fun _ ↦ 0) (.s 2) |>.toFloat


end Ex
