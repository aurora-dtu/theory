import Mathlib.Data.ENNReal.Inv
import Mathlib.Order.FixedPoints
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Inv
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Order.BooleanAlgebra.Defs
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Order.BooleanSubalgebra
import STDX.Subst
import ENNRealArith
import PGCL.KInduction
-- import Smt
-- import Smt.Real

open OrderHom

@[simp]
theorem ENNReal.toReal_ite {b : Prop} [Decidable b] {x y : ENNReal} :
    (if b then x else y).toReal = if b then x.toReal else y.toReal := by grind

@[simp]
theorem ENNReal.ite_ne_top {b : Prop} [Decidable b] {x y : ENNReal}
    (hx : b → x ≠ ⊤) (hy : ¬b → y ≠ ⊤) :
    (if b then x else y) ≠ ⊤ := by grind

structure Method where
  input : Type*
  output : Type*
  pre : input → Prop
  post : input → output → Prop

structure pGCL.Context (ϖ : Type*) where
  decidableEq : DecidableEq ϖ
  types : ϖ → Type*

abbrev pGCL.Context.Mem (Γ : pGCL.Context ϖ) := (v : ϖ) → Γ.types v

-- alias PReal := ENNReal

inductive pGCL (Γ : pGCL.Context ϖ) where
  | tick (t : Γ.Mem → ENNReal)
  | skip
  | observe (b : Γ.Mem → Bool)
  | assign (v : ϖ) (e : Γ.Mem → Γ.types v)
  | seq (C₁ C₂ : pGCL Γ)
  | prob (C₁ : pGCL Γ) (p : Γ.Mem → ENNReal) (C₂ : pGCL Γ)
  | nondet (C₁ C₂ : pGCL Γ)
  | loop (b : Γ.Mem → Bool) (C : pGCL Γ)

namespace pGCL

def ite {ϖ : Type} [DecidableEq ϖ] {Γ : Context ϖ} (b : Γ.Mem → Bool) (C₁ C₂ : pGCL Γ) : pGCL Γ :=
  .prob C₁ (fun σ ↦ if b σ then 1 else 0) C₂

namespace Syntax

open Lean Parser Command

class Variables {α : Type*} (Γ : Context α) (lift : outParam ((f g : Γ.Mem → ENNReal) → Prop)) where
  elim : ∀ f g, lift f g → f ≤ g

syntax "declare_vars " ident " where" ppLine withPosition((ident " : " term)*) : command

open Term in
def declare_vars_impl
    (vars : TSyntax `ident) (name : TSyntaxArray `ident) (ty : TSyntaxArray `term) :
    MacroM Syntax := do
  let ctors : TSyntaxArray `Lean.Parser.Command.ctor ← name.mapM fun n ↦ `(ctor| | $n:ident)
  let inductive_vars : TSyntax `command ← `(command|
    inductive $vars where $ctors*
    deriving DecidableEq
    )
  let varsName : Array Ident :=
    name.map (fun n ↦ mkIdent (.mkStr2 s!"{vars.getId.toString}" s!"{n.getId.toString}"))
  let types : TSyntaxArray `Lean.Parser.Term.matchAlt ←
    (varsName.zip ty).mapM (fun (n, t) ↦ `(matchAltExpr| | $n => $t))
  let typesMatchBody : TSyntax `Lean.Parser.Term.matchAlts := mkNode _ #[mkListNode types]
  let nΓ := mkIdent (Name.mkStr2 vars.getId.toString "Γ")
  let nΓMem := mkIdent (Name.mkStr3 vars.getId.toString "Γ" "Mem")
  let Γ ← `(command|
    abbrev $nΓ : Context $vars where
      decidableEq := inferInstance
      types := fun x ↦ match x with $typesMatchBody
  )
  let ntypes := mkIdent (Name.mkStr2 vars.getId.toString "types")
  let defTys : TSyntaxArray `Lean.Parser.Term.bracketedBinder ←
    (name.zip ty).mapM (fun (n, t) ↦ `(bracketedBinder|($n:ident : $t)))
  let vals : TSyntaxArray `Lean.Parser.Term.matchAlt ←
    (varsName.zip name).mapM (fun (n, t) ↦ `(matchAltExpr| | $n => $t))
  let varsMatchBody : TSyntax `Lean.Parser.Term.matchAlts := mkNode _ #[mkListNode vals]
  let specializeArgs : TSyntaxArray `term ← varsName.mapM (fun n ↦ `((σ $n)))
  let lift2 ← `(command|
    instance : Variables $nΓ (fun (f g : $nΓMem → ENNReal) ↦
          ∀ $defTys*, let σ : $nΓMem := (fun v ↦ match v with $varsMatchBody); f σ ≤ g σ) where
      elim f g h := by
        intro σ
        specialize h $specializeArgs*
        convert h <;> split <;> rfl
    )
  let structureCases : TSyntaxArray `Lean.Parser.Command.structSimpleBinder ←
    (name.zip ty).mapM fun (n, t) ↦ `(structSimpleBinder|$n:ident : $t)
  let typeStructure ← `(command|
    structure $ntypes where $[$structureCases]*
  )
  let structureCases' := sorry
  let typeStructure' ← `(command|
    structure $ntypes where $[$structureCases']*
  )
  return mkNullNode #[inductive_vars, Γ, lift2, typeStructure]

structure Program (Vars : List (Name × Type)) where

def Program.seq (P₁ : Program V) (P₂ : Program V) : Program V where

def P₁ : Program [(`y, ℕ), (`x, ℕ)] where
def P₂ : Program [(`y, ℕ), (`x, ℕ)] where

#check P₁.seq P₂

open Term in
macro_rules
| `(declare_vars $vars where $[$name : $ty]*) => do
  declare_vars_impl vars name ty

syntax (name := expMacro) "exp[" term "]" "{" term "}" : term
syntax (name := expMacro') "exp" "{" term "}" : term

open Lean Elab Command Term Meta in
def expImplAux (Vars : Expr) (body : TSyntax `term) : TermElabM Expr := do
  dbg_trace f!"{Vars}"
  let .const name [] := Vars | throwError f!"here 0: {Vars}"
  let env ← getEnv
  let id := name.append (.mkSimple "types")
  if isStructure env id then
    let fields := getStructureFieldsFlattened env id (includeSubobjectFields := false)
    let fieldTys ← fields.mapM fun f ↦ do
      let ty ← inferType (← elabTerm (mkIdent (id.append f)) none)
      let .forallE _ _ q _ := ty | throwUnsupportedSyntax
      return q
    dbg_trace f!"fields: {fields.zip fieldTys}"
    let args ← (fields.zip fieldTys).mapM (fun (f, t) ↦ do
      `(Lean.Parser.Term.funBinder| ($(mkIdent f) : $(← t.toSyntax))))
    let applyArgs ← fields.mapM (fun f ↦ do
      `(term| (σ $(mkIdent (name.append f)))))
    let ΓMem := mkIdent ((name.append (.mkSimple "Γ")).append (.mkSimple "Mem"))
    elabTerm (← `(fun (σ : $ΓMem) ↦ (fun $args* ↦ $body) $applyArgs*)) none
  else
    throwUnsupportedSyntax

open Lean Elab Command Term Meta in
@[term_elab expMacro]
def expImpl : TermElab := fun stx _ ↦ do
  let `(exp[$Vars] { $body }) := stx | throwUnsupportedSyntax
  expImplAux (← elabTerm Vars none) body

open Lean Elab Command Term Meta in
@[term_elab expMacro']
def expImpl' : TermElab := fun stx type? ↦ do
  let some type := type? | throwError m!"could not infer type from: {type?}"
  let .forallE _ (.app _ Γ) _ _ := type | throwError "here 1"
  -- dbg_trace f!"Γ: {Γ}"
  let y ← Lean.Meta.inferType Γ
  let (_, #[Vars]) ← getInductiveUniverseAndParams y | throwError "here 3"
  -- dbg_trace f!"Vars: {Vars}"
  let Vars ← whnf Vars

  let `(exp { $body }) := stx | throwError "here 4"
  expImplAux Vars body

declare_vars Vars where
  a : ℕ → Bool
  b : ℕ

#check exp[Vars] { a b }
#check (exp { a b } : Vars.Γ.Mem → Bool)
#check (pGCL.assign Vars.b (exp { if a b then 1 else 0 }))
#check_failure (exp { a b })

syntax "unhyg_intros" : tactic
def unhyg_intros_impl (g : Lean.Expr) : Array Lean.Name :=
  match g with
  | .forallE n _ x _ => #[n] ++ unhyg_intros_impl x
  | _ => #[]
elab "unhyg_intros" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalDecl ← goal.getDecl
    let goalType := goalDecl.type
    let names := unhyg_intros_impl goalType
    let idents := names.map Lean.mkIdent
    if ¬names.isEmpty then
      Lean.Elab.Tactic.evalTactic (← `(tactic|intro $idents*))

declare_syntax_cat cpgcl

syntax term:max " := " term : cpgcl
syntax:39 cpgcl:39 " ; " cpgcl:38 : cpgcl
syntax "{" cpgcl "}" : cpgcl
syntax cpgcl:40 "[""]" cpgcl:40 : cpgcl
syntax cpgcl:40 "[" term "]" cpgcl:40 : cpgcl
syntax "while " term:max "{" cpgcl "}" : cpgcl
syntax "if " term:max "{" cpgcl "}" " else " "{" cpgcl "}" : cpgcl
-- TODO: use &"tick "
syntax "tick(" term ")" : cpgcl
-- syntax "skip" : cpgcl
syntax ident : cpgcl

syntax "pgcl " "{" cpgcl "}" : term

macro_rules
| `(pgcl { $x:term := $t }) =>
  `(pGCL.assign $x exp {$t})
| `(pgcl { $C₁:cpgcl ; $C₂ }) =>
  `(pGCL.seq pgcl {$C₁} pgcl {$C₂})
| `(pgcl { $C₁:cpgcl [] $C₂ }) =>
  `(pGCL.nondet pgcl {$C₁} pgcl {$C₂})
| `(pgcl { $C₁:cpgcl [$p] $C₂ }) =>
  `(pGCL.prob pgcl {$C₁} exp {($p : ENNReal)} pgcl {$C₂})
| `(pgcl { while $b { $C:cpgcl } }) =>
  `(pGCL.loop exp {$b} pgcl {$C})
| `(pgcl { if $b { $C₁:cpgcl } else { $C₂ } }) =>
  `(pGCL.ite exp {$b} pgcl {$C₁} pgcl {$C₂})
| `(pgcl { tick($b) }) =>
  `(pGCL.tick exp {$b})
| `(pgcl { skip }) =>
  `(pGCL.skip)
| `(pgcl {{ $C:cpgcl }}) =>
  `(pgcl {$C})

open Vars in
#check (pgcl { while (b < 1) { {b := b + 2} [1/b] {b := b + 3} } } : pGCL Vars.Γ)

declare_syntax_cat pgcl_method_arg

syntax "(" ident " : " term ")" : pgcl_method_arg

syntax "method " ident pgcl_method_arg* " := " withPosition(cpgcl) : command

open Macro in
macro_rules
| `(method $name $args* := $body ) => do
  let (arg, ty) :=
    Array.unzip (← args.mapM fun a ↦
      match a with
      | `(pgcl_method_arg|($n : $t)) => pure (n, t)
      | _ => throwUnsupported)
  -- let vars := name.getId.append (.mkSimple "Vars")
  let vars := name.getId
  let Γ := vars.append (.mkSimple "Γ")
  let methodName := vars.append (.mkSimple "body")
  dbg_trace f!"arg: {arg}"
  dbg_trace f!"ty: {ty}"
  let q := ← declare_vars_impl (mkIdent vars) arg ty
  -- return mkNullNode #[q]
  let m ← `(def $(mkIdent methodName) : pGCL $(mkIdent Γ) := pgcl { $body })
  return mkNullNode #[q, m]

set_option trace.Elab.debug true

method cool (x : ℕ) (y : Bool) :=
  x := if y then 1 else 0 ;
  y := false

method alt (x : ℕ) (y : Bool) :=
  x := if y then 1 else 0 ;
  y := false

#print cool
#print cool.body

end Syntax

section

variable {ϖ : Type} [DecidableEq ϖ] {Γ : Context ϖ}

instance : DecidableEq ϖ := Γ.decidableEq

instance : Substitution Γ.Mem Γ.types where
  subst σ := fun v w ↦ if h : v.1 = w then (h ▸ v.2) else σ w

local notation "𝔼[" Γ "]" => Context.Mem Γ → ENNReal

instance instExpSubst {α : Type*} : Substitution (Γ.Mem → α) (Γ.Mem → Γ.types ·) where
  subst X v := fun σ ↦ X σ[v.1 ↦ v.2 σ]

section

variable {v v' : ϖ} {e : Γ.Mem → Γ.types v}
variable {w : Γ.types v}
variable {α : Type*} {X Y : Γ.Mem → α}

@[grind, simp] theorem add_subst [Add α] :
    let q : (v : ϖ) × (Γ.Mem → Γ.types v) := Sigma.mk v e
    (X + Y)[..[q]] = X[v ↦ e] + Y[v ↦ e] := by rfl
@[grind, simp] theorem sub_subst [Sub α] : (X - Y)[v ↦ e] = X[v ↦ e] - Y[v ↦ e] := by rfl
@[grind, simp] theorem mul_subst [Mul α] : (X * Y)[v ↦ e] = X[v ↦ e] * Y[v ↦ e] := by rfl
@[grind, simp] theorem min_subst [Min α] : (X ⊓ Y)[v ↦ e] = X[v ↦ e] ⊓ Y[v ↦ e] := by rfl
@[grind, simp] theorem max_subst [Max α] : (X ⊔ Y)[v ↦ e] = X[v ↦ e] ⊔ Y[v ↦ e] := by rfl
theorem fun_subst {f : Γ.Mem → β} : (fun σ ↦ f σ)[v ↦ e] = (fun σ ↦ f σ[v ↦ e σ]) := by rfl
@[grind, simp] theorem subst_apply_same {σ : Γ.Mem} : σ[v ↦ w] v = w := by
  simp [Substitution.subst_singleton, Substitution.subst]
@[grind, simp] theorem subst_apply_diff {σ : Γ.Mem} (h : v ≠ v') : σ[v ↦ w] v' = σ v' := by
  simp [Substitution.subst_singleton, Substitution.subst, h]
@[grind, simp] theorem subst_subst {σ : Γ.Mem} : σ[v ↦ w][v ↦ w'] = σ[v ↦ w'] := by
  simp only [Substitution.subst_singleton, Substitution.subst]
  grind

@[gcongr]
theorem subst_le_subst [LE α] (h : X ≤ Y) : X[v ↦ e] ≤ Y[v ↦ e] := by
  intro σ
  simp [Substitution.subst_singleton, Substitution.subst]
  apply h

@[simp, grind] theorem one_subst : (1 : 𝔼[Γ])[v ↦ e] = 1 := by rfl

@[coe] def var_coe_exp {Γ : Context ϖ} (v : ϖ) : Γ.Mem → Γ.types v := fun σ ↦ σ v
instance {Γ : Context ϖ} (v : ϖ) : CoeDep ϖ v (Γ.Mem → Γ.types v) := ⟨var_coe_exp v⟩

@[grind, simp] theorem var_coe_exp_subst {Γ : Context ϖ} {x : ϖ} {e : Γ.Mem → Γ.types x} :
    (var_coe_exp v)[x ↦ e] = if h : v = x then (h ▸ e) else (var_coe_exp v) := by
  ext σ
  simp only [Substitution.subst_singleton, Substitution.subst, var_coe_exp]
  split_ifs
  · subst_eqs
    simp
  · subst_eqs
    contradiction
  · subst_eqs
    contradiction
  · simp [var_coe_exp]

end

class Iverson (α : Type*) (β : outParam Type*) where
  iver : α → β

namespace Iverson

notation "i[" x "]" => Iverson.iver x

instance : Iverson Bool ENNReal where
  iver b := if b then 1 else 0
instance : Iverson (Γ.Mem → Bool) 𝔼[Γ] where
  iver b := fun σ ↦ i[b σ]
open scoped Classical in
noncomputable instance : Iverson Prop ENNReal where
  iver b := if b then 1 else 0
open scoped Classical in
noncomputable instance : Iverson (Γ.Mem → Prop) 𝔼[Γ] where
  iver b := fun σ ↦ i[b σ]

@[simp] theorem iver_bool_ne_top : i[(b : Bool)] ≠ ⊤ := by simp [iver]
@[simp] theorem iver_prop_ne_top : i[(b : Prop)] ≠ ⊤ := by simp [iver]
@[simp] theorem iver_false_eq_zero : i[false] = 0 := by simp [iver]
@[simp] theorem iver_true_eq_one : i[true] = 1 := by simp [iver]
@[simp] theorem iver_False_eq_zero : i[False] = 0 := by simp [iver]
@[simp] theorem iver_True_eq_one : i[True] = 1 := by simp [iver]

variable {P Q : Γ.Mem → Prop} {b : Γ.Mem → Bool}

@[simp] theorem iver_subst {x : ϖ} {e : Γ.Mem → Γ.types x} : i[P][x ↦ e] = i[P[x ↦ e]] := by rfl

omit [DecidableEq ϖ]

@[simp] theorem apply_true (hP : P σ) : i[P] σ = 1 := by simp [iver, hP]
@[simp] theorem apply_false (hP : ¬P σ) : i[P] σ = 0 := by simp [iver, hP]
@[simp] theorem apply_True (hb : b σ = true) : i[b] σ = 1 := by simp [iver, hb]
@[simp] theorem apply_False (hb : b σ = false) : i[b] σ = 0 := by simp [iver, hb]
@[simp] theorem apply_bool : i[b] σ = i[b σ] := by simp [iver]
@[simp] theorem apply_prop {p : Γ.Mem → Prop} : i[p] σ = i[p σ] := by simp [iver]
@[simp] theorem le_apply_iff : i[Q] σ ≤ i[P] σ ↔ (Q σ → P σ) := by
  simp [iver]
  split_ifs <;> simp [*]
@[simp] theorem one_le_apply_iff : 1 ≤ i[P] σ ↔ P σ := by
  simp [iver]
  split_ifs <;> simp [*]
theorem le_apply_iff' {X : 𝔼[Γ]} : i[Q] σ ≤ X σ ↔ (Q σ → 1 ≤ X σ) := by
  simp [iver]
  split_ifs <;> simp [*]

@[simp] theorem mul_neg {b : Bool} : i[b] * i[b = false] = 0 := by by_cases b <;> simp_all

end Iverson

class Eeq (α : Type*) (β : outParam Type*) where
  eeq : α → α → β

infixr:50 "===" => Eeq.eeq

instance {α β : Type*} : Eeq (α → β) (α → Prop) where
  eeq f g := fun σ ↦ f σ = g σ

attribute [grind] Bool.le_iff_imp
attribute [grind] Pi.sup_apply
attribute [grind] Pi.inf_apply
theorem Prop.le_iff_imp : ∀ {x y : Prop}, x ≤ y ↔ x → y := by simp
attribute [grind] Prop.le_iff_imp

-- noncomputable def Ξ (b : Γ.Mem → Prop) (et : 𝔼[Γ] →o 𝔼[Γ]) (X : 𝔼[Γ]) :
--     𝔼[Γ] →o 𝔼[Γ] :=
--   ⟨fun Y ↦ i[b] * et Y + i[bᶜ] * X, sorry⟩
noncomputable def Ξ (b : Γ.Mem → Prop) (et : 𝔼[Γ] →o 𝔼[Γ]) : 𝔼[Γ] →o 𝔼[Γ] →o 𝔼[Γ] :=
  ⟨fun X ↦ ⟨fun Y ↦ i[b] * et Y + i[bᶜ] * X, sorry⟩, sorry⟩
noncomputable def Ξ' (b : Γ.Mem → Prop) (et : (Γ.Mem → Prop) →o (Γ.Mem → Prop)) (X : Γ.Mem → Prop) :
    (Γ.Mem → Prop) →o (Γ.Mem → Prop) :=
  ⟨fun Y ↦ (b ⊓ et Y) ⊔ (bᶜ ⊓ X), by
    intro x y h σ
    simp
    have := et.mono (h : x ≤ y) σ
    grind⟩

noncomputable def wp (C : pGCL Γ) : 𝔼[Γ] →o 𝔼[Γ] :=
  match C with
  | tick t => ⟨fun X ↦ t + X, fun _ _ h σ ↦ by simp; gcongr; apply h⟩
  | skip => ⟨fun X ↦ X, fun _ _ h ↦ by simp [h]⟩
  | observe b => ⟨fun X ↦ i[b] * X, fun _ _ h σ ↦ by simp; gcongr; apply h⟩
  | assign v e => ⟨fun X ↦ X[v ↦ e], sorry⟩
  | seq C₁ C₂ => C₁.wp.comp C₂.wp
  | prob C₁ p C₂ => ⟨fun X ↦ p * C₁.wp X + (1 - p) * C₂.wp X, sorry⟩
  | nondet C₁ C₂ => ⟨fun X ↦ C₁.wp X ⊓ C₂.wp X, sorry⟩
  | loop b C => ⟨fun X ↦ lfp (Ξ (b ·) (wp C) X), by sorry⟩

noncomputable def wlp (C : pGCL Γ) : 𝔼[Γ] →o 𝔼[Γ] :=
  match C with
  | tick t => ⟨fun X ↦ t + X, fun _ _ h σ ↦ by simp; gcongr; apply h⟩
  | skip => ⟨fun X ↦ X, fun _ _ h ↦ by simp [h]⟩
  | observe b => ⟨fun X ↦ i[b] * X, fun _ _ h σ ↦ by simp; gcongr; apply h⟩
  | assign v e => ⟨fun X ↦ X[v ↦ e], sorry⟩
  | seq C₁ C₂ => C₁.wlp.comp C₂.wlp
  | prob C₁ p C₂ => ⟨fun X ↦ p * C₁.wlp X + (1 - p) * C₂.wlp X, sorry⟩
  | nondet C₁ C₂ => ⟨fun X ↦ C₁.wlp X ⊓ C₂.wlp X, sorry⟩
  | loop b C => ⟨fun X ↦ gfp (Ξ (b ·) (wlp C) X), by sorry⟩

variable {X : 𝔼[Γ]}

@[grind, simp] theorem wp_tick_apply : wp (.tick t) X = t + X := rfl
@[grind, simp] theorem wp_observe_apply : wp (.observe b) X = i[b] * X := rfl
@[grind, simp] theorem wp_skip_apply : wp .skip X = X := rfl
@[grind, simp] theorem wp_assign_apply : wp (.assign v e) X = X[v ↦ e] := rfl
@[grind, simp] theorem wp_seq_apply {C₁ C₂ : pGCL Γ} : wp (.seq C₁ C₂) X = wp C₁ (wp C₂ X) := rfl
@[grind, simp] theorem wp_prop_apply {C₁ C₂ : pGCL Γ} :
    wp (.prob C₁ p C₂) X = p * wp C₁ X + (1 - p) * wp C₂ X := rfl
@[grind, simp] theorem wp_nondet_apply {C₁ C₂ : pGCL Γ} :
    wp (.nondet C₁ C₂) X = wp C₁ X ⊓ wp C₂ X := rfl
@[grind, simp] theorem wp_ite_apply {C₁ C₂ : pGCL Γ} :
    wp (.ite b C₁ C₂) X = i[b] * wp C₁ X + i[bᶜ] * wp C₂ X := by
  ext σ
  simp [ite, Iverson.iver]
  split_ifs <;> simp_all

@[grind, simp] theorem wlp_tick_apply : wlp (.tick t) X = t + X := rfl
@[grind, simp] theorem wlp_observe_apply : wlp (.observe b) X = i[b] * X := rfl
@[grind, simp] theorem wlp_skip_apply : wlp .skip X = X := rfl
@[grind, simp] theorem wlp_assign_apply : wlp (.assign v e) X = X[v ↦ e] := rfl
@[grind, simp] theorem wlp_seq_apply {C₁ C₂ : pGCL Γ} : wlp (.seq C₁ C₂) X = wlp C₁ (wlp C₂ X) :=
  rfl
@[grind, simp] theorem wlp_prop_apply {C₁ C₂ : pGCL Γ} :
    wlp (.prob C₁ p C₂) X = p * wlp C₁ X + (1 - p) * wlp C₂ X := rfl
@[grind, simp] theorem wlp_nondet_apply {C₁ C₂ : pGCL Γ} :
    wlp (.nondet C₁ C₂) X = wlp C₁ X ⊓ wlp C₂ X := rfl
@[grind, simp] theorem wlp_ite_apply {C₁ C₂ : pGCL Γ} :
    wlp (.ite b C₁ C₂) X = i[b] * wlp C₁ X + i[bᶜ] * wlp C₂ X := by
  ext σ
  simp [ite, Iverson.iver]
  split_ifs <;> simp_all

theorem park_induction {b} {C : pGCL Γ} {f}
    (I) (h : (Ξ (b ·) (wp C) f) I ≤ I) : (pGCL.loop b C).wp f ≤ I :=
  lfp_le _ (by exact h)
theorem park_coinduction {b} {C : pGCL Γ} {f}
    (I) (h : I ≤ (Ξ (b ·) (wlp C) f) I) : (pGCL.loop b C).wlp f ≥ I :=
  le_gfp _ (by exact h)

theorem park_k_induction (k : ℕ) {b} {C : pGCL Γ} {f}
    (I : 𝔼[Γ]) (h : (Ξ (b ·) C.wp f) (((k_induction.Ψ I (Ξ (b ·) C.wp f)))^[k] I) ≤ I) :
    (pGCL.loop b C).wp f ≤ I := k_induction k h
theorem park_k_coinduction (k : ℕ) {b} {C : pGCL Γ} {f}
    (I : 𝔼[Γ]) (h : I ≤ (Ξ (b ·) C.wlp f) (((k_coinduction.Ψ I (Ξ (b ·) C.wlp f)))^[k] I)) :
    (pGCL.loop b C).wlp f ≥ I := k_coinduction k h

infixr:50 " ;; " => pGCL.seq

end

namespace Syntax

declare_syntax_cat pgcl_ind_tactic

syntax "ind " term : pgcl_ind_tactic
syntax "coind " term : pgcl_ind_tactic
syntax "coind(" term ") " term : pgcl_ind_tactic

syntax "pgcl_attack " "[" pgcl_ind_tactic,* "]" : tactic

macro_rules
| `(tactic|pgcl_attack [coind $i]) => do
  `(tactic|nth_grw 1 [park_coinduction $i] <;>
      (try simp only [Ξ, coe_mk, k_coinduction.Ψ, coe_mk, Function.iterate_zero,
                      Function.iterate_succ', Function.comp_apply, id_eq, wlp_seq_apply]) <;>
      try pgcl_attack [])
| `(tactic|pgcl_attack [coind $i, $rest,*]) => do
  `(tactic|nth_grw 1 [park_coinduction $i] <;>
      (try simp only [Ξ, coe_mk, k_coinduction.Ψ, coe_mk, Function.iterate_zero,
                      Function.iterate_succ', Function.comp_apply, id_eq, wlp_seq_apply]) <;>
      try pgcl_attack [$rest,*])
| `(tactic|pgcl_attack [coind($n) $i]) => do
  `(tactic|nth_grw 1 [park_k_coinduction $n $i] <;>
      (try simp only [Ξ, coe_mk, k_coinduction.Ψ, coe_mk, Function.iterate_zero,
                      Function.iterate_succ', Function.comp_apply, id_eq, wlp_seq_apply]) <;>
      try pgcl_attack [])
| `(tactic|pgcl_attack [coind($n) $i, $rest,*]) => do
  `(tactic|nth_grw 1 [park_k_coinduction $n $i] <;>
      (try simp only [Ξ, coe_mk, k_coinduction.Ψ, coe_mk, Function.iterate_zero,
                      Function.iterate_succ', Function.comp_apply, id_eq, wlp_seq_apply]) <;>
      try pgcl_attack [$rest,*])
| `(tactic|pgcl_attack [ind $i]) => do
  `(tactic|nth_grw 1 [park_induction $i] <;>
      (try simp only [Ξ, coe_mk, k_coinduction.Ψ, coe_mk, Function.iterate_zero,
                      Function.iterate_succ', Function.comp_apply, id_eq, wlp_seq_apply]) <;>
      try pgcl_attack [])
| `(tactic|pgcl_attack [ind $i, $rest,*]) => do
  `(tactic|nth_grw 1 [park_induction $i] <;>
      (try simp only [Ξ, coe_mk, k_coinduction.Ψ, coe_mk, Function.iterate_zero,
                      Function.iterate_succ', Function.comp_apply, id_eq, wlp_seq_apply]) <;>
      try pgcl_attack [$rest,*])
| `(tactic|pgcl_attack [$_, $_]) =>
  `(tactic|apply Syntax.Variables.elim; unhyg_intros; try simp only)
| `(tactic|pgcl_attack [$_]) =>
  `(tactic|apply Syntax.Variables.elim; unhyg_intros; try simp only)
| `(tactic|pgcl_attack []) =>
  `(tactic|apply Syntax.Variables.elim; unhyg_intros; try simp only)

example : AddRightMono ENNReal := inferInstance
instance {α : Type*} : AddRightMono (α → ENNReal) where
  elim a b c h := by
    intro σ
    simp_all [Function.swap]
    gcongr
    apply h
instance {α : Type*} : AddLeftMono (α → ENNReal) where
  elim a b c h := by
    intro σ
    simp_all
    gcongr
    apply h
instance {α : Type*} : MulRightMono (α → ENNReal) where
  elim a b c h := by
    intro σ
    simp_all [Function.swap]
    gcongr
    apply h
instance {α : Type*} : MulLeftMono (α → ENNReal) where
  elim a b c h := by
    intro σ
    simp_all
    gcongr
    apply h

end Syntax

namespace Examples

namespace Simple

declare_vars Vars where
  a : ENNReal
  b : ENNReal

open Vars

@[grind]
noncomputable def C : pGCL Γ := pgcl {
  a := 0 ;
  while true { {a := b} [1/2] {b := a} } ;
  while true { {a := b} [1/2] {b := a} }
}

-- theorem asdasd {f g : Γ.Mem → ENNReal} (h : ∀ (a : ℕ) (b : ℕ),
--     let σ : Γ.Mem :=
--       (fun v ↦
--         match v with
--         | .a => a
--         | .b => b); f σ ≤ g σ) : f ≤ g := by
--   intro σ
--   specialize h (σ .a) (σ .b)
--   convert h <;> split <;> rfl

example : C.wlp (exp {a}) ≥ exp[Vars] {i[a = b]} := by
  simp [C]
  let I : Γ.Mem → ENNReal := sorry
  let I' : Γ.Mem → ENNReal := sorry
  pgcl_attack [coind(1) I, coind I']
  · apply Syntax.Variables.elim; try simp only; unhyg_intros
    sorry
  · simp
    simp [Iverson.iver, I, I', Subst.subst]

    sorry
  · sorry

  -- · sorry
  -- nth_grw 1 [park_coinduction ?_]; rotate_right

  -- simp only [ge_iff_le]
  -- apply Vars.lift fun a b ↦ ?_; simp only
  -- simp [C]
  -- grw [park_coinduction ?_]

end Simple

namespace Cowboys

inductive Cowboy where
  | A
  | B
deriving DecidableEq

declare_vars Vars where
  turn : Cowboy
  done : Bool

open Vars

#check i[(done : Γ.Mem → _) === fun _ ↦ true] + i[(turn : Γ.Mem → _) === (fun _ ↦ Cowboy.A)]

@[grind]
noncomputable def C (a b : ENNReal) : pGCL Γ :=
  .seq
    (.prob (.assign .turn (fun _ ↦ Cowboy.A)) (1/2) (.assign .turn (fun _ ↦ Cowboy.B))) <|.seq
    (.assign .done (fun _ ↦ false))
    (.loop (fun σ ↦ σ .done = false)
      (.ite (fun σ ↦ σ .turn = .A)
        (.prob (.assign .done (fun _ ↦ true)) (fun _ ↦ a) (.assign .turn (fun _ ↦ Cowboy.B)))
        (.prob (.assign .done (fun _ ↦ true)) (fun _ ↦ b) (.assign .turn (fun _ ↦ Cowboy.A)))))

@[grind]
noncomputable def C' (a b : ENNReal) : pGCL Γ := pgcl {
  {turn := .A} [1/2] {turn := .B} ;
  done := false ;
  while (done = false) {
    if (turn = .A) {
      {done := true} [a] {turn := .B}
    } else {
      {done := true} [b] {turn := .A}
    }
  }
}

example : C = C' := by ext; simp [C, C']; rfl

attribute [simp] ENNReal.inv_two_add_inv_two

noncomputable def α (a b : ENNReal) : ENNReal := a / (a + b - a * b)
noncomputable def β (a b : ENNReal) : ENNReal := (1 - b) * α a b
theorem hα (ha : a = 1/2) (hb : b = 1/2) : α a b = 2/3 := by
  simp [α, ha, hb]
  refine (ENNReal.div_eq_div_iff ?_ ?_ ?_ ?_).mpr ?_ <;> try simp
  · refine pos_iff_ne_zero.mp ?_; simp
  · simp [ENNReal.sub_mul, mul_assoc, ENNReal.inv_mul_cancel]
    eq_as_reals
theorem hβ (ha : a = 1/2) (hb : b = 1/2) : β a b = 1/3 := by
  simp [hα ha hb, β]
  simp [hb]
  rw [mul_div]
  have : 2⁻¹ * 2 = (1 : ENNReal) := by refine ENNReal.inv_mul_cancel ?_ ?_ <;> simp
  simp [this]

noncomputable def I (a b : ENNReal) : Γ.Mem → ENNReal := exp {
    i[turn = .A] * i[done = true] +
    i[turn = .A] * i[done = false] * α a b +
    i[turn = .B] * i[done = false] * β a b
}

example : (C (1/2) (1/2)).wlp (exp {i[turn = .A]}) ≥ 2⁻¹ := by
  simp only [C, one_div, Bool.decide_eq_false, wlp_seq_apply, wlp_assign_apply]
  grw [park_coinduction (I (1/2) (1/2))]
  · simp
    unfold I
    simp
    simp [hα, hβ,]
    intro σ
    simp [Subst.subst, Iverson.iver]
    simp [← mul_add]
    refine (ENNReal.mul_le_iff_le_inv ?_ ?_).mp ?_ <;> try simp
    have : (2 * 2⁻¹ : ENNReal) = 1 := by refine ENNReal.mul_inv_cancel ?_ ?_ <;> simp
    simp [this]; clear this
    apply le_of_eq
    rw [@ENNReal.div_eq_inv_mul]
    eq_as_reals
  · simp [Ξ]
    intro σ
    simp [I, hα, hβ, Subst.subst, Iverson.iver]
    split_ifs <;> try simp_all
    · refine (ENNReal.div_le_iff ?_ ?_).mpr ?_ <;> try simp [add_mul, mul_assoc]
      simp [← @ENNReal.div_eq_inv_mul, ENNReal.div_add_div_same]
      have : 3 / 3 = (1 : ENNReal) := by refine (ENNReal.div_eq_one_iff ?_ ?_).mpr rfl <;> simp
      simp [this]
      ring_nf
      refine (ENNReal.le_div_iff_mul_le ?_ ?_).mpr ?_ <;> eq_as_reals
    · simp [← @ENNReal.div_eq_inv_mul]
      refine (ENNReal.le_div_iff_mul_le ?_ ?_).mpr ?_ <;> try simp
      rw [mul_comm]
      rfl

syntax "to_reals" : tactic

macro_rules
| `(tactic| to_reals) =>
  `(tactic|
    first
    | (refine (ENNReal.toReal_le_toReal ?_ ?_).mp ?_ <;> to_reals)
    | (refine (ENNReal.toReal_eq_toReal ?_ ?_).mp ?_ <;> to_reals)
    | (rw [ENNReal.toReal_ite] <;> to_reals)
    | (rw [ENNReal.toReal_add] <;> to_reals)
    | (rw [ENNReal.toReal_mul] <;> to_reals)
    | (rw [ENNReal.toReal_div] <;> to_reals)
    | (rw [ENNReal.toReal_inv] <;> to_reals)
    -- | (rw [ENNReal.toReal_pow] <;> to_reals)
    | (rw [ENNReal.toReal_sub_of_le] <;> to_reals)
    | (apply ENNReal.add_ne_top.mpr; split_ands <;> to_reals)
    | (apply ENNReal.mul_ne_top <;> to_reals)
    | (apply ENNReal.div_ne_top <;> to_reals)
    | (apply ENNReal.inv_ne_top.mpr <;> to_reals)
    | (apply ENNReal.ite_ne_top <;> to_reals)
    | (refine ne_of_gt (tsub_pos_of_lt ?_) <;> to_reals)
    | (simp only [ENNReal.one_ne_top])
    | (try finiteness)
    )

example (a b : ENNReal) (ha : a ≤ 1) (hb : b ≤ 1) :
    a ≤ 2⁻¹ * (a / (a + b - a * b) + (1 - b) * (a / (a + b - a * b))) := by
  have : a ≠ 0 := sorry
  have : b ≠ 0 := sorry
  have : a ≠ ⊤ := LT.lt.ne_top (ha.trans_lt ENNReal.one_lt_top)
  have : b ≠ ⊤ := LT.lt.ne_top (hb.trans_lt ENNReal.one_lt_top)
  have : a * b < a + b := by
    refine ENNReal.mul_lt_of_lt_div ?_
    simp [ENNReal.add_div]
    rw [ENNReal.div_self] <;> try assumption
    have : a / b ≠ 0 := by refine ENNReal.div_ne_zero.mpr ?_ <;> simp_all
    sorry
  to_reals
  · simp
    set a' := a.toReal
    set b' := b.toReal
    have : a' ≠ 0 := by simp_all [ENNReal.toReal_eq_zero_iff, a']
    have : b' ≠ 0 := by simp_all [ENNReal.toReal_eq_zero_iff, b']
    have : a' ≤ 1 := by refine ENNReal.toReal_le_of_le_ofReal ?_ ?_ <;> simp [*]
    have : b' ≤ 1 := by refine ENNReal.toReal_le_of_le_ofReal ?_ ?_ <;> simp [*]
    have : a' ≠ 2 := by grind
    have : b' ≠ 2 := by grind
    simp_all
    field_simp
    ring_nf
    simp
    field_simp
    simp [← mul_div]
    gcongr
    sorry
  · sorry
  · sorry

example {p : Prop} {q : ℕ → Prop} :
    (∀ i, p → q i) ↔ (p → ∀ i, q i) := by
  grind


example (ha : a ≤ 1) (hb : b ≤ 1) : (C a b).wlp (exp { i[turn = .A] }) ≥ fun _ ↦ a := by
  have : a ≠ ⊤ := LT.lt.ne_top (ha.trans_lt ENNReal.one_lt_top)
  have : b ≠ ⊤ := LT.lt.ne_top (hb.trans_lt ENNReal.one_lt_top)
  simp only [C, one_div, Bool.decide_eq_false, wlp_seq_apply, wlp_assign_apply]
  grw [park_coinduction (I a b)]
  · simp
    unfold I
    simp
    intro σ
    simp [Subst.subst, Iverson.iver, α, β]
    simp [← mul_add]
    refine (ENNReal.mul_le_iff_le_inv ?_ ?_).mp ?_ <;> try simp
    eq_as_reals
    have : (2 * 2⁻¹ : ENNReal) = 1 := by refine ENNReal.mul_inv_cancel ?_ ?_ <;> simp
    simp [this]; clear this
    apply le_of_eq
    rw [@ENNReal.div_eq_inv_mul]
    eq_as_reals
  · simp [Ξ]
    intro σ
    simp [I, hα, hβ, Subst.subst, Iverson.iver]
    simp [α, β]
    split_ifs <;> try simp_all
    refine (ENNReal.div_le_iff ?_ ?_).mpr ?_
    · apply pos_iff_ne_zero.mp
      simp
      refine ENNReal.mul_lt_of_lt_div' ?_
      simp [ENNReal.add_div]
      rw [ENNReal.div_self]
      · sorry
      · sorry
      · sorry
    · finiteness
    · refine (ENNReal.div_le_iff ?_ ?_).mpr ?_ <;> try simp [add_mul, mul_assoc]
      simp [← @ENNReal.div_eq_inv_mul, ENNReal.div_add_div_same]
      have : 3 / 3 = (1 : ENNReal) := by refine (ENNReal.div_eq_one_iff ?_ ?_).mpr rfl <;> simp
      simp [this]
      ring_nf
      refine (ENNReal.le_div_iff_mul_le ?_ ?_).mpr ?_ <;> eq_as_reals
    · simp [← @ENNReal.div_eq_inv_mul]
      refine (ENNReal.le_div_iff_mul_le ?_ ?_).mpr ?_ <;> try simp
      rw [mul_comm]
      rfl

end Cowboys

namespace RandomWalk

declare_vars Vars where
  x : ℕ
  x' : ℕ
  n : ℕ
  n' : ℕ

open Vars

@[grind]
noncomputable def C : pGCL Γ :=
  .seq
    (.assign .x fun σ ↦ σ .x') <|.seq
    (.assign .n fun σ ↦ σ .n')
    (.loop (fun σ ↦ σ .x < σ .n)
      (.seq
        (.prob (.assign .x (fun σ ↦ σ .x + 2)) (fun _ ↦ 1/2)  (.assign .x (fun σ ↦ σ .x - 1)))
        (.tick 1)))

@[grind]
noncomputable def C' : pGCL Γ := pgcl {
  x := x' ;
  n := n' ;
  while (x < n) {
    {x := x + 2} [1/2] {x := x - 1} ;
    tick(1)
  }
}

example : (fun σ ↦ 2 * (σ .n' + 1) - σ .x' : Γ.Mem → ENNReal) ≤ C.wlp 0 := by
  simp only [C, one_div, wlp_seq_apply, wlp_assign_apply]
  let I : Γ.Mem → ENNReal := fun σ ↦ 2 * (σ .n + 1) - 1
  grw [park_coinduction I]
  · simp [I]; intro σ; simp [Subst.subst]
    have : 0 ≤ (↑(σ x') : ℝ) := by simp
    have : 0 ≤ (↑(σ n') : ℝ) := by simp
    simp [mul_add]
    to_reals
    · simp
      ring_nf
      grind
    · simp
      grind
  · simp [Ξ]
    simp [I]
    intro σ
    simp [Iverson.iver, Subst.subst]
    to_reals
    · simp
      split_ifs
      · grind
      · simp [mul_add]
        ring_nf
        sorry
    · simp
      have : 0 ≤ (↑(σ n) : ℝ) := by simp
      grind

end RandomWalk

namespace RabinMutualExclusion

declare_vars Vars where
  i : ℕ
  n : ℕ

open Vars

@[grind]
noncomputable def C : pGCL Γ :=
    (.loop (exp[Vars] {1 < i})
      (.seq
        (.assign .n fun (σ : Γ.Mem) ↦ σ .i)
        (.loop (fun (σ : Γ.Mem) ↦ 0 < σ .n)
          (.seq
            (.prob (.assign .i (fun (σ : Γ.Mem) ↦ σ .i - 1)) (fun _ ↦ 1/2)  .skip)
            (.assign .n (fun (σ : Γ.Mem) ↦ σ .n - 1))))))

@[grind]
noncomputable def C' : pGCL Γ := pgcl {
  while (1 < i) {
    n := i ;
    while (0 < n) {
      {i := i - 1} [1/2] { tick(0) } ;
      n := n - 1
    }
  }
}

noncomputable def invar₁ (i n : ℕ) : ENNReal :=
  1 - (i[i = n] * (n + 1) / (2^n) + i[i = n + 1] / (2^n))
noncomputable def invar₂ (i n : ℕ) : ENNReal :=
  i[i = n] * n / (2^n) + i[i = n + 1] / (2^n)

noncomputable def I₀ : Γ.Mem → ENNReal := exp { i[i = 1] + i[1 < i] * 2/3 }
noncomputable def I₁ : Γ.Mem → ENNReal := exp { i[0 ≤ n ∧ n ≤ i] * (2/3) * invar₁ i n + invar₂ i n }

@[gcongr]
theorem Exp.add_le_add {a b c d : Γ.Mem → ENNReal} (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d := by
  intro; simp; gcongr <;> apply_assumption
@[gcongr]
theorem Exp.mul_le_mul {a b c d : Γ.Mem → ENNReal} (hab : a ≤ b) (hcd : c ≤ d) : a * c ≤ b * d := by
  intro; simp; gcongr <;> apply_assumption

set_option maxHeartbeats 5000000 in
-- set_option maxRecDepth 5000 in
example : I₀ ≤ C.wlp exp {i[i = 1]} := by
  simp [C]
  grw [park_coinduction I₀]
  simp [Ξ]
  grw [park_coinduction I₁]
  · unfold I₀ I₁ invar₁ invar₂
    intro σ
    simp [Subst.subst, Iverson.iver]
    split_ifs <;> try simp
    · grind
    · grind
    · grind
    · have : 0 ≤ (↑(σ i) : ℝ) := by simp
      set i : ℕ := σ i
      to_reals
      · simp
        field_simp
        ring_nf
        simp
        grind
      · simp
        field_simp
        induction i
        · simp
        · simp
          rw [pow_succ]
          linarith
  · unfold I₀ I₁
    intro σ
    simp [Subst.subst, Iverson.iver, Ξ, invar₁, invar₂]
    ring_nf
    generalize σ i = i'
    generalize σ n = n'
    clear! σ
    ring_nf
    rcases i' with (_ | i) <;>  rcases n' with (_ | n)
    · simp
    · simp
      ring_nf
      split_ifs <;> try grind
      · simp
      · simp
    · simp
      split_ifs <;> simp
      grind
    · simp
      ring_nf
      simp
      split_ifs <;> subst_eqs <;> (try simp) <;> try grind
      · to_reals
        · simp
          linarith
        · simp; field_simp; refine one_le_pow₀ ?_; simp
        · simp; field_simp; simp [one_le_mul_of_one_le_of_one_le, one_le_pow₀]
      · to_reals
        · simp; field_simp; grind
        · simp; field_simp; simp [one_le_pow₀]
        · simp; field_simp
          rename_i h₁ h₂ h₃ h₄; clear h₁ h₂ h₃ h₄
          induction i with
          | zero => simp
          | succ i ih =>
            simp; ring_nf
            linarith
        · simp; field_simp
          rename_i h₁ h₂ h₃ h₄; clear h₁ h₂ h₃ h₄
          induction i with
          | zero => simp
          | succ i ih =>
            simp; ring_nf; linarith
      · to_reals
        simp; linarith

set_option maxHeartbeats 5000000 in
-- set_option maxRecDepth 5000 in
example : I₀ ≤ C.wlp exp {i[i = 1]} := by
  simp [C]
  pgcl_attack [coind I₀, coind I₁] <;> unhyg_intros
  · simp [I₀, I₁, Subst.subst, Iverson.iver, invar₁, invar₂]
    ring_nf
    to_reals
    · simp
    · simp
      split_ifs <;> try linarith
      simp
      field_simp
      ring_nf
      simp
      grind
    · simp
      ring_nf
      sorry
    · simp
  · simp [I₀, I₁, Subst.subst, invar₁, invar₂]
    ring_nf
    rcases i with (_ | i) <;>  rcases n with (_ | n)
    · simp
    · simp
      ring_nf
      sorry
    · simp [zero_lt_iff]
      by_cases i = 0 <;> simp_all
    · simp
      ring_nf
      if hin : i = n then
        subst_eqs
        simp
        to_reals
        · simp
          field_simp
          ring_nf
          linarith
        · simp
          sorry
        · simp
          field_simp
          sorry
        · simp
          field_simp
          sorry
      else
        simp [hin]
        sorry

  -- grw [park_coinduction I₀]
  -- simp [Ξ]
  -- grw [park_coinduction I₁]
  -- · unfold I₀ I₁ invar₁ invar₂
  --   intro σ
  --   simp [Subst.subst, Iverson.iver]
  --   split_ifs <;> try simp
  --   · grind
  --   · grind
  --   · grind
  --   · have : 0 ≤ (↑(σ i) : ℝ) := by simp
  --     set i : ℕ := σ i
  --     to_reals
  --     · simp
  --       field_simp
  --       ring_nf
  --       simp
  --       grind
  --     · simp
  --       field_simp
  --       induction i
  --       · simp
  --       · simp
  --         rw [pow_succ]
  --         linarith
  -- · unfold I₀ I₁
  --   intro σ
  --   simp [Subst.subst, Iverson.iver, Ξ, invar₁, invar₂]
  --   ring_nf
  --   generalize σ i = i'
  --   generalize σ n = n'
  --   clear! σ
  --   ring_nf
  --   rcases i' with (_ | i) <;>  rcases n' with (_ | n)
  --   · simp
  --   · simp
  --     ring_nf
  --     split_ifs <;> try grind
  --     · simp
  --     · simp
  --   · simp
  --     split_ifs <;> simp
  --     grind
  --   · simp
  --     ring_nf
  --     simp
  --     split_ifs <;> subst_eqs <;> (try simp) <;> try grind
  --     · to_reals
  --       · simp
  --         linarith
  --       · simp; field_simp; refine one_le_pow₀ ?_; simp
  --       · simp; field_simp; simp [one_le_mul_of_one_le_of_one_le, one_le_pow₀]
  --     · to_reals
  --       · simp; field_simp; grind
  --       · simp; field_simp; simp [one_le_pow₀]
  --       · simp; field_simp
  --         rename_i h₁ h₂ h₃ h₄; clear h₁ h₂ h₃ h₄
  --         induction i with
  --         | zero => simp
  --         | succ i ih =>
  --           simp; ring_nf
  --           linarith
  --       · simp; field_simp
  --         rename_i h₁ h₂ h₃ h₄; clear h₁ h₂ h₃ h₄
  --         induction i with
  --         | zero => simp
  --         | succ i ih =>
  --           simp; ring_nf; linarith
  --     · to_reals
  --       simp; linarith

end RabinMutualExclusion

namespace MatrixMulCheck
open Matrix

abbrev n : ℕ := 4

declare_vars Vars where
  A : Matrix (Fin n) (Fin n) (Fin 2)
  B : Matrix (Fin n) (Fin n) (Fin 2)
  C : Matrix (Fin n) (Fin n) (Fin 2)
  r : Fin n → Fin 2
  equal : Bool

def vec_set (v : Fin n → Fin 2) (i : Fin n) (j : Fin 2) : Fin n → Fin 2 :=
  fun x ↦ if x = i then j else v x

open Vars

noncomputable abbrev choose_i (i : Fin n) : pGCL Γ :=
  .prob (.assign .r exp {vec_set r i 0}) (1/2) (.assign .r exp {vec_set r i 1})

@[grind]
noncomputable def C : pGCL Γ :=
    choose_i 0 ;;
    choose_i 1 ;;
    choose_i 2 ;;
    choose_i 3 ;;
    .assign .equal exp {A *ᵥ B *ᵥ r = C *ᵥ r}
    -- .assign .equal fun σ ↦ σ .A *ᵥ σ .B *ᵥ σ .r = σ .C *ᵥ σ .r

def vec_mk₄ (v₀ v₁ v₂ v₃ : Fin 2) : Fin n → Fin 2 :=
  (match · with | 0 => v₀ | 1 => v₁ | 2 => v₂ | 3 => v₃)

@[simp]
theorem vec_set₄_all {v : Fin n → Fin 2} :
    vec_set (vec_set (vec_set (vec_set v 0 v₀) 1 v₁) 2 v₂) 3 v₃ = vec_mk₄ v₀ v₁ v₂ v₃
:= by
  grind [vec_set, vec_mk₄]

example (hp : p ≠ ⊤) : C.wp (exp {i[equal]}) ≥ exp[Vars] {i[A * B ≠ C] * p} := by
  simp [C]
  pgcl_attack []; unhyg_intros
  simp [Subst.subst]
  ring_nf
  if h : A * B = C then
    subst_eqs
    simp [Iverson.iver]
    -- ring_nf
    -- to_reals
    -- · simp [hp]
    -- have : (2 ^ 4)⁻¹ * (16 : ℝ) = 1 := by linarith
    -- simp [this]
    -- linarith
  else
    simp [← mul_add, h]
    simp [add_assoc]

    set D := A * B - C
    have D_ne_zero : D ≠ 0 := sub_ne_zero_of_ne h
    have h : ∀ (r : Fin n → Fin 2), (A * B) *ᵥ r = C *ᵥ r → D *ᵥ r = 0 := by
      intro r hr; simp [D, Matrix.sub_mulVec, hr]
    obtain ⟨i, j, hij⟩ : ∃ i j, D i j ≠ 0 := by
      contrapose! D_ne_zero; ext; simp_all



    simp [Iverson.iver]
    ring_nf
    have : 2⁻¹ ^ 4 * (16 : ENNReal) = 1 := by
      refine (ENNReal.toReal_eq_toReal ?_ ?_).mp ?_
      to_reals
      · exact ENNReal.one_ne_top
      · simp
        linarith
    simp [this]

    sorry


end MatrixMulCheck

namespace PolynomialIdentities

abbrev d : ℕ := 4

declare_vars Vars where
  F : Vector ℕ d
  G : Vector ℕ d
  equal : Bool

structure PolyCanonical (d : ℕ) where
  a : Vector ℕ d

structure PolyProduct (d : ℕ) where
  a : Vector ℕ d

def PolyCanonical.eval (p : PolyCanonical d) : ℝ → ℝ :=
  fun x ↦ ∑ i : Fin d, p.a[i] * x^i.val
def PolyProduct.eval (p : PolyProduct d) : ℝ → ℝ :=
  fun x ↦ ∏ i : Fin d, (x^i.val - p.a[i])

-- def PolyProduct.toCanonical (p : PolyProduct d)

-- abbrev d : ℕ := 4

-- abbrev Γ : Context Vars where
--   decidableEq := inferInstance
--   types
--   | .F => Vector ℕ d
--   | .G => Vector ℕ d
--   | .r => Fin n → Fin 2
--   | .equal => Bool

-- open Vars


-- noncomputable abbrev choose_i (i : Fin n) : pGCL Γ :=
--   .prob (.assign .r fun σ ↦ vec_set (σ .r) i 0) (1/2) (.assign .r fun σ ↦ vec_set (σ .r) i 1)


-- @[grind]
-- noncomputable def C : pGCL Γ :=
--     choose_i 0 ;;
--     choose_i 1 ;;
--     choose_i 2 ;;
--     choose_i 3 ;;
--     .assign .equal fun σ ↦ σ .A *ᵥ σ .B *ᵥ σ .r = σ .C *ᵥ σ .r

-- def vec_mk₄ (v₀ v₁ v₂ v₃ : Fin 2) : Fin n → Fin 2 :=
--   (match · with | 0 => v₀ | 1 => v₁ | 2 => v₂ | 3 => v₃)

-- @[simp]
-- theorem vec_set₄_all {v : Fin n → Fin 2} :
--     vec_set (vec_set (vec_set (vec_set v 0 v₀) 1 v₁) 2 v₂) 3 v₃ = vec_mk₄ v₀ v₁ v₂ v₃
-- := by
--   grind [vec_set, vec_mk₄]

-- example (hp : p ≠ ⊤) : C.wp (fun σ ↦ i[σ .equal]) ≥ fun σ ↦ i[σ .A * σ .B ≠ σ .C] * p := by -- (fun σ ↦ i[σ .A * σ .B = σ .C]) := by
--   simp [C]
--   intro σ
--   simp [Subst.subst]
--   ring_nf
--   generalize σ .A =  A
--   generalize σ .B =  B
--   generalize σ .C =  C
--   if h : A * B = C then
--     subst_eqs
--     simp [Iverson.iver]
--     ring_nf
--     to_reals
--     · simp [hp]
--     have : (2 ^ 4)⁻¹ * (16 : ℝ) = 1 := by linarith
--     simp [this]
--     linarith
--   else
--     simp [← mul_add, h]
--     simp [add_assoc]

--     set D := A * B - C
--     have D_ne_zero : D ≠ 0 := sub_ne_zero_of_ne h
--     have h : ∀ (r : Fin n → Fin 2), (A * B) *ᵥ r = C *ᵥ r → D *ᵥ r = 0 := by
--       intro r hr; simp [D, Matrix.sub_mulVec, hr]
--     obtain ⟨i, j, hij⟩ : ∃ i j, D i j ≠ 0 := by
--       contrapose! D_ne_zero; ext; simp_all



--     simp [Iverson.iver]
--     ring_nf
--     have : 2⁻¹ ^ 4 * (16 : ENNReal) = 1 := by
--       refine (ENNReal.toReal_eq_toReal ?_ ?_).mp ?_
--       to_reals
--       · exact ENNReal.one_ne_top
--       · simp
--         linarith
--     simp [this]

--     sorry


end PolynomialIdentities

namespace UniformDist

declare_vars Vars where
  r : ℕ
  n : ℕ
  done : Bool
  cool : Bool → Bool

open Vars

@[grind]
noncomputable def C (high : ℕ) : pGCL Γ :=
    (assign .done exp { false }) ;;
    (assign .n (exp { high })) ;;
    (.loop (exp { ¬done })
      (.prob (.assign .done exp { true }) (exp {(1/(n + 1) : ENNReal)}) (.assign .n exp {n - 1})))

@[grind]
noncomputable def C' (high : ℕ) : pGCL Γ := pgcl {
  done := false ;
  n := high ;
  while (!done) {
    {done := true} [1/(n + 1 : ENNReal)] {n := n - 1}
  }
}

example {high m : ℕ} (hm : m ≤ high) : 1/high ≤ (C high).wlp exp {i[n = m]} := by
  simp only [C, Bool.not_eq_true, Bool.decide_eq_false, one_div, wlp_seq_apply, wlp_assign_apply]
  let I := exp[Vars] { i[done] * (i[n = m] * 1 / high + i[n < m] * (m - 1) / high + i[n < m] * (high - m) / high) + i[¬done] * (high : ENNReal)⁻¹ }
  have I_ne_top : ∀ x, I x ≠ ⊤ := by sorry
  pgcl_attack [coind(1) I] <;> unhyg_intros
  · simp [I, Iverson.iver]
    simp [Subst.subst]
  · simp [I]
    simp [fun_subst]
    simp [Subst.subst]
    ring_nf
    simp
    cases done
    · simp

    · simp
    simp [Iverson.apply_False]
    sorry
  grw [park_k_coinduction 1 I]
  · simp
    intro σ
    simp [I]
    simp [fun_subst]
  · simp [Ξ, k_coinduction.Ψ]
    intro σ
    simp [Iverson.iver]
    simp [I]
    if hdone : σ .done then
      simp [hdone]
      split_ifs
      · simp [*]
      · simp [*]
    else
      simp [hdone]
      ring_nf
      generalize σ .n = n
      simp [fun_subst]
      to_reals
      · apply I_ne_top
      · simp
        contrapose!
        simp
        intro h
        exact False.elim (I_ne_top σ[Vars.n ↦ n - 1] h)
      -- · exact I_ne_top σ
      · simp [ENNReal.toReal_max, *]
        -- rw [ENNReal.toReal_max]
        -- · rw [ENNReal.toReal_add]
        --   rw [ENNReal.toReal_add] <;> simp
        --   · simp

        --     sorry
        --   · simp [ENNReal.mul_ne_top, I_ne_top]
        --   · simp [ENNReal.mul_ne_top, I_ne_top]
        -- · simp [ENNReal.mul_ne_top, I_ne_top]
        -- · simp [I_ne_top]
      · simp [ENNReal.mul_ne_top, I_ne_top, inv_le_one_of_one_le₀]
      · simp [ENNReal.mul_ne_top, I_ne_top, inv_le_one_of_one_le₀]
      · simp [ENNReal.mul_ne_top, I_ne_top, inv_le_one_of_one_le₀]


      rcases n with _ | _ | n
      · simp
      · simp
        ring_nf
        simp [ENNReal.one_sub_inv_two, ← mul_add]
      · simp
        ring_nf
      if hn : σ .n = 0 then
        simp [hn]
      else
        sorry
      sorry
    split_ifs <;> subst_eqs <;> try grind
    · simp
      sorry
    · simp [Subst.subst]
      sorry
    · simp
      sorry
    · simp

      sorry
    · simp
      sorry
    · simp
  intro σ
  simp [Subst.subst]
  ring_nf
  generalize σ .A =  A
  generalize σ .B =  B
  generalize σ .C =  C
  if h : A * B = C then
    subst_eqs
    simp [Iverson.iver]
    ring_nf
    to_reals
    · simp [hp]
    have : (2 ^ 4)⁻¹ * (16 : ℝ) = 1 := by linarith
    simp [this]
    linarith
  else
    simp [← mul_add, h]
    simp [add_assoc]

    set D := A * B - C
    have D_ne_zero : D ≠ 0 := sub_ne_zero_of_ne h
    have h : ∀ (r : Fin n → Fin 2), (A * B) *ᵥ r = C *ᵥ r → D *ᵥ r = 0 := by
      intro r hr; simp [D, Matrix.sub_mulVec, hr]
    obtain ⟨i, j, hij⟩ : ∃ i j, D i j ≠ 0 := by
      contrapose! D_ne_zero; ext; simp_all



    simp [Iverson.iver]
    ring_nf
    have : 2⁻¹ ^ 4 * (16 : ENNReal) = 1 := by
      refine (ENNReal.toReal_eq_toReal ?_ ?_).mp ?_
      to_reals
      · exact ENNReal.one_ne_top
      · simp
        linarith
    simp [this]

    sorry


end UniformDist

end Examples

end pGCL
