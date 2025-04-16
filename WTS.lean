import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Order

structure WTS (W : Type*) [Semiring W] (State : Type*) (Act : Type*) where
  trans : State → Act → State → W
  enabled_action : ∀ s, (trans s).support.Nonempty
  progress : ∀ s α, (trans s α).support.Nonempty

namespace WTS

variable {W : Type*} [Semiring W] {State : Type*} {Act : Type*} {𝒲 : WTS W State Act}

def succ (𝒲 : WTS W State Act) (s : State) (α : Act) (s' : State) : Prop := 𝒲.trans s α s' ≠ 0
def succ_univ (𝒲 : WTS W State Act) (s : State) (s' : State) : Prop := ∃ α, 𝒲.trans s α s' ≠ 0

def succs (𝒲 : WTS W State Act) (s : State) (α : Act) := {s' // 𝒲.succ s α s'}
def preds (𝒲 : WTS W State Act) (α : Act) (s' : State) := {s // 𝒲.succ s α s'}
def succs_univ (𝒲 : WTS W State Act) (s : State) := {s' // 𝒲.succ_univ s s'}
def preds_univ (𝒲 : WTS W State Act) (s' : State) := {s // 𝒲.succ_univ s s'}

section Syntax

open Lean PrettyPrinter Delaborator SubExpr

syntax:max term:max ppHardSpace "-[" term "," term "]>" ppHardSpace term:max : term
syntax:max "_-[" term "," term "]>" ppHardSpace term:max : term
syntax:max term:max ppHardSpace "-[" term "," term "]>_" : term
syntax:max term:max ppHardSpace "-[" term ",_" "]>" ppHardSpace term:max : term
syntax:max term:max ppHardSpace "-[" term ",_" "]>_" : term
syntax:max "_-[" term ",_" "]>" ppHardSpace term:max : term

macro_rules
| `($s -[$𝒲, $α]> $s') => `(WTS.succ $𝒲 $s $α $s')
| `(_-[$𝒲, $α]> $s') => `(WTS.preds $𝒲 $α $s')
| `($s -[$𝒲, $α]>_) => `(WTS.succs $𝒲 $s $α)
| `($s -[$𝒲,_]> $s') => `(WTS.succ_univ $𝒲 $s $s')
| `($s -[$𝒲,_]>_) => `(WTS.succs_univ $𝒲 $s)
| `(_-[$𝒲,_]> $s') => `(WTS.preds_univ $𝒲 $s')

@[app_unexpander WTS.succ]
def succUnexpander : Unexpander
| `($(_) $𝒲 $s $α $s') => `($s -[$𝒲,$α]> $s')
| _ => throw ()
@[app_unexpander WTS.succ_univ]
def succ_univUnexpander : Unexpander
| `($(_) $𝒲 $s $s') => `($s -[$𝒲,_]> $s')
| _ => throw ()
@[app_unexpander WTS.succs]
def succsvUnexpander : Unexpander
| `($(_) $𝒲 $s $α) => `($s -[$𝒲,$α]>_)
| _ => throw ()
@[app_unexpander WTS.preds]
def predsUnexpander : Unexpander
| `($(_) $𝒲 $α $s') => `(_-[$𝒲,$α]> $s')
| _ => throw ()
@[app_unexpander WTS.succs_univ]
def succs_univvUnexpander : Unexpander
| `($(_) $𝒲 $s) => `($s -[$𝒲,_]>_)
| _ => throw ()
@[app_unexpander WTS.preds_univ]
def preds_univUnexpander : Unexpander
| `($(_) $𝒲 $s') => `(_-[$𝒲,_]> $s')
| _ => throw ()

/-- info: fun s α s' => s -[𝒲,α]> s' : State → Act → State → Prop -/
#guard_msgs in
#check fun s α s' ↦ s -[𝒲,α]> s'
/-- info: fun s α => s -[𝒲,α]>_ : State → Act → Type u_2 -/
#guard_msgs in
#check fun s α ↦ s -[𝒲,α]>_
/-- info: fun α s' => _-[𝒲,α]> s' : Act → State → Type u_2 -/
#guard_msgs in
#check fun α s' ↦ _-[𝒲,α]> s'
/-- info: fun s s' => s -[𝒲,_]> s' : State → State → Prop -/
#guard_msgs in
#check fun s s' ↦ s -[𝒲,_]> s'
/-- info: fun s => s -[𝒲,_]>_ : State → Type u_2 -/
#guard_msgs in
#check fun s ↦ s -[𝒲,_]>_

end Syntax

structure Path (𝒲 : WTS W State Act) where
  states : List State
  succs : ∀ i, (h : i + 1 < states.length) → states[i] -[𝒲,_]> states[i+1]

notation "‖" a "‖" => List.length (Path.states a)

structure Scheduler (𝒲 : WTS W State Act) where
  toFun : 𝒲.Path → Act

notation "𝔖[" 𝒲 "]" => Scheduler 𝒲

namespace Scheduler

attribute [coe] Scheduler.toFun

instance : Coe 𝒲.Scheduler (𝒲.Path → Act) := ⟨Scheduler.toFun⟩

instance : DFunLike 𝔖[𝒲] 𝒲.Path (fun _ ↦ Act) where
  coe := Scheduler.toFun
  coe_injective' := by rintro 𝒮₁ 𝒮₂ h; cases 𝒮₁; cases 𝒮₂; simp_all

end Scheduler

namespace Path

@[simp]
theorem getElem_succ_is_succ (π : 𝒲.Path) (h : i + 1 < π.states.length) :
    π.states[i] -[𝒲,_]> π.states[i + 1] := π.succs i h

def take (π : 𝒲.Path) (n : ℕ) : 𝒲.Path where
  states := π.states.take n
  succs := by simp

def last (π : 𝒲.Path) : Option State := π.states.getLast?

def wgt (π : 𝒲.Path) (𝒮 : 𝔖[𝒲]) : W :=
  ∑ ⟨i, hi⟩ : Finset.range (‖π‖ - 1),
    𝒲.trans
      (π.states[i]'(by simp at hi ⊢; omega))
      (𝒮 (π.take i))
      (π.states[i + 1]'(by simp at hi ⊢; omega))

end Path

/-- Paths starting in `s` with length `n` -/
def Path_eq (n : ℕ) (s : State) :=
  { π : 𝒲.Path | ‖π‖ = n ∧ ((h : 0 < ‖π‖) → π.states[0] = s) }
/-- Paths starting in `s` with length at most `n` -/
def Path_le (n : ℕ) (s : State) :=
  { π : 𝒲.Path | ‖π‖ ≤ n ∧ ((h : 0 < ‖π‖) → π.states[0] = s) }

@[inherit_doc]
notation "Path[" 𝒲 "," s "," "=" n "]" => WTS.Path_eq (𝒲:=𝒲) n s
@[inherit_doc]
notation "Path[" 𝒲 "," s "," "≤" n "]" => WTS.Path_le (𝒲:=𝒲) n s

noncomputable def EW [TopologicalSpace W] (𝒮 : 𝔖[𝒲]) (s : State) (n : ℕ) (f : State → W) : W :=
  ∑' π : Path[𝒲,s,=n], π.val.wgt 𝒮 * f π.val.last

noncomputable def TotalEW [TopologicalSpace W] (𝒮 : 𝔖[𝒲]) (s : State) (n : ℕ) : W :=
  ∑' π : Path[𝒲,s,=n], π.val.wgt 𝒮


end WTS
