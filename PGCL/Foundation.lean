import Mathlib.Data.ENNReal.Basic

open Lean

class Scope (α : Sort*) where
  root : Type*
  names : Array Name
  fields : Array (Name × Type*)

def Scope.coe (α : Sort*) {β : Sort*} [inst : Scope α] : Scope β where
  root := inst.root
  names := inst.names
  fields := inst.fields

instance Pi.instScope {α β : Type*} [i : Scope α] : Scope (α → β) := i.coe
instance LE.instScope {α : Type*} [i : Scope α] [LE α] {a b : α} : Scope (a ≤ b) := i.coe

structure Vars where
  a : ℕ
  b : Bool
  c : Bool

universe u v
def ReturnType {α : Type u} {β : Type v} (_ : α → β) : Type v := β

structure Vars' (α : Type*) where
  a : ℕ
  b : Bool → α
  c : Bool

#check Vars'.b

abbrev Vars.isName (n : Lean.Name) : Prop := n = `a ∨ n = `b ∨ n = `c

abbrev Vars.typeOf (n : Lean.Name) (h : Vars.isName n) : Type :=
  match h : n with
  | `a => ℕ
  | `b => Bool
  | `c => Bool
  | _ => False.elim sorry

def Vars.subst (V : Vars) (n : Lean.Name) (h : Vars.isName n := by grind) :
    Vars.typeOf n h → Vars := fun v ↦
  match n with
  | `a => {V with a := v}
  | `b => {V with b := v}
  | `c => {V with c := v}
  | _ => V

#eval! ((Vars.mk 1 True False).subst `a) 10

instance : Scope Vars where
  root := Vars
  names := #[`a, `b, `c]
  fields := #[(`a, ℕ), (`b, Bool → Bool), (`c, ENNReal)]

def collectNames (e : Expr) : Array Name :=
  match e with
  | .app (.app _ (.app _ (.lit (.strVal n)))) r =>
    #[.mkSimple n] ++ collectNames r
  | _ => #[]
def collectArgs (e : Expr) : Array (Name × Expr) :=
  match e with
  | .app (.app _ (.app (.app _ (.app _ (.lit (.strVal n)))) t)) r =>
    #[(.mkSimple n, t)] ++ collectArgs r
  | _ => #[]

open Lean Elab Command Term Meta in
def scopeMem (name : TSyntax `term) : TermElabM Expr := do
  let memExpr ← (elabTermAndSynthesize (← `(term|Scope.root $name)) none)
  return ← whnf memExpr
open Lean Elab Command Term Meta in
def scopeFields (name : TSyntax `term) : TermElabM (Array (Name × Expr)) := do
  let fieldsExpr ← (elabTermAndSynthesize (← `(term|Scope.fields $name)) none)
  return collectArgs ((← whnf fieldsExpr).getArg! 1)
open Lean Elab Command Term Meta in
def scopeNames (name : TSyntax `term) : TermElabM (Array Name) := do
  let namesExpr ← (elabTermAndSynthesize (← `(term|Scope.names $name)) none)
  return collectNames ((← whnf namesExpr).getArg! 1)
open Lean Elab Command Term Meta in
def scopeFieldsExpr (name : Expr) : TermElabM (Array (Name × Expr)) := do
  let fieldsExpr : Expr := .app (.const `Scope.fields []) name
  return collectArgs ((← whnf fieldsExpr).getArg! 1)

syntax (name := scope_macro) "scope " term : command
open Lean Elab Command Term Meta in
@[command_elab scope_macro]
def scopeMacro : CommandElab := fun stx ↦ do
  let `(scope $name) := stx | throwUnsupportedSyntax
  let root ← liftTermElabM <| scopeMem name
  let names ← liftTermElabM <| scopeNames name
  let fields ← liftTermElabM <| scopeFields name
  dbg_trace f!"Scope of : {← liftTermElabM (elabTermAndSynthesize name none)}"
  dbg_trace f!"  root   : {root}"
  dbg_trace f!"  names  : {names}"
  dbg_trace f!"  fields : {fields}"

scope Vars

structure Program (V : Type*) [Scope V] where

instance {V : Type*} [inst : Scope V] : Scope (Program V) := inst.coe

scope Program Vars
scope Vars → ENNReal

elab "intro_scope" : tactic => do
  let goal ← Elab.Tactic.getMainGoal
  let goal_type ← goal.getType
  let fields ← scopeFields (← goal_type.toSyntax)
  let idents := fields.map fun (n, _) ↦ mkIdent n
  Lean.Elab.Tactic.evalTactic (← `(tactic|rintro ⟨$idents,*⟩))

example {f g : Vars → ENNReal} : f ≤ g := by
  intro_scope
  sorry

syntax (name := scoped_infer_macro) "scoped " "{" term "}" : term
syntax (name := scoped_macro) "scoped[" term "] " "{" term "}" : term
open Lean Elab Command Term Meta in
@[term_elab scoped_macro]
def scopedMacro : TermElab := fun stx et ↦ do
  let `(scoped[$name] { $t }) := stx | throwUnsupportedSyntax
  let root ← scopeMem name
  let fields ← scopeFields name
  dbg_trace f!"{t}"
  dbg_trace f!"hello({root}): {fields}"
  elabTerm (← `(12)) et

#check scoped[Vars] { fun (a : ℕ) (b : Bool → Bool) (c : ENNReal) ↦ a + a }
#check scoped[Vars] { if b then a else 2 * a }
