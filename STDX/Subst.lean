import Mathlib.Data.Finset.Insert
import Lean.PrettyPrinter.Delaborator.Basic

class Substitution (α : Type*) {ι : outParam Type*} (β : outParam (ι → Type*)) where
  subst : α → Sigma β → α

namespace Substitution

instance [BEq ι] [Hashable ι] : Substitution (Std.HashMap ι β) (fun (_ : ι) ↦ β) where
  subst map := Sigma.uncurry map.insert

def substs [Substitution α β] (m : α) (xs : List (Sigma β)) : α :=
    xs.foldr (fun b acc ↦ Substitution.subst acc b) m

declare_syntax_cat substitution_arg
syntax withoutPosition(term) ppHardSpace "↦" ppHardSpace withoutPosition(term) : substitution_arg
syntax ".." withoutPosition(term) : substitution_arg
syntax:max term noWs "[" substitution_arg,* "]" : term
macro_rules
| `($x[ $[$i:term ↦ $j:term],* ]) => `(substs $x ([$[⟨$i, $j⟩],*]))
| `($x[ .. $xs:term ]) => `(substs $x $xs)

open Lean PrettyPrinter Delaborator SubExpr in
@[app_unexpander Substitution.substs]
def substsUnexpander : Unexpander
| `($(_) $m [$[⟨$x, $y⟩],*]) => `($m[$[$x:term ↦ $y],*])
| `($(_) $m $xs:term) => `($m[..$xs])
| _ => throw ()

#check fun (x : Std.HashMap String ℕ) ↦ x["a" ↦ 12]
#check fun (x : Std.HashMap String ℕ) ↦ x["a" ↦ 12, "b" ↦ 13]
#check fun (x : Std.HashMap String ℕ) ↦ x["a" ↦ 12]["b" ↦ 13] = x["a" ↦ 12, "b" ↦ 13]
#check fun (x : Std.HashMap String ℕ) ↦ x["b" ↦ 13]["a" ↦ 12]
#check fun (x : Std.HashMap String ℕ) ↦ x[..[Sigma.mk "a" 12]]
#check fun (x : Std.HashMap String ℕ) (xs : List ((_ : String) × ℕ)) ↦ x[..xs]

-- theorem substs_of_subst {α β : Type*} [Substitution α β] {m : α} {xs : List β}
--     (p : α → Prop) (h : ∀ m (b : β), p m[..[b]]) : p (m[..xs]) := by
--   induction xs generalizing m p with
--   | nil =>
--     simp [substs]
--     sorry
--   | cons x xs ih =>
--     simp_all [substs]

variable {α ι : Type*} {β : ι → Type*} [Substitution α β]

@[grind =, simp]
theorem substs_nil {m : α} :
    substs m [] = m := rfl
theorem substs_cons {m : α} {x : Sigma β} {xs : List (Sigma β)} :
    substs m (x :: xs) = subst (substs m xs) x := rfl
theorem substs_cons_substs {m : α} {x : Sigma β} {xs : List (Sigma β)} :
    substs m (x :: xs) = substs (substs m xs) [x] := rfl
theorem substs_append {m : α} {xs ys : List (Sigma β)} :
    substs m (xs ++ ys) = substs (substs m ys) xs := by
  simp [substs]
theorem subst_singleton {m : α} {x : Sigma β} :
    substs m [x] = subst m x := by
  simp [substs]

-- theorem substs_of_binary {α β : Type*} [Substitution α β] {m n : α} {xs : List β}
--     {f : α → α → α} (h : ∀ m n (b : β), (f m n)[..[b]] = (f m[..[b]] n[..[b]])) :
--     (f m n)[..xs] = f m[..xs] n[..xs] := by
--   induction xs generalizing m n f with
--   | nil => simp
--   | cons x xs ih => simp_all [substs_cons]

theorem substs_of_binary {α₁ α₂ α₃ ι : Type*} {β : ι → Type*}
    [Substitution α₁ β] [Substitution α₂ β] [Substitution α₃ β]
    {m : α₁} {n : α₂} {xs : List (Sigma β)}
    {f : α₁ → α₂ → α₃} (h : ∀ m n (b : Sigma β), (f m n)[..[b]] = (f m[..[b]] n[..[b]])) :
    (f m n)[..xs] = f m[..xs] n[..xs] := by
  induction xs generalizing m n f with
  | nil => simp
  | cons x xs ih => simp_all [substs_cons]

def IsIndepPair (m : α) (x : ι) : Prop :=
  ∀ v, m[x ↦ v] = m

@[mk_iff]
class IndepPair (m : α) (x : ι) : Prop where
  is_indep : IsIndepPair m x

attribute [grind ., simp] IndepPair.is_indep

@[grind =, simp]
theorem indep_pair {m : α} {x : ι}
    (h : IsIndepPair m x) {v} : m[x ↦ v] = m := h v

namespace Example

structure Context (ϖ : Type*) where
  types : ϖ → Type*

abbrev Context.Mem (Γ : Context ϖ) := (v : ϖ) → Γ.types v

variable {ϖ α : Type*} {Γ : Context ϖ} [DecidableEq ϖ]

instance : Substitution Γ.Mem Γ.types where
  subst σ := Sigma.uncurry fun x e y ↦ if h : x = y then (h ▸ e) else σ y

instance : Substitution (Γ.Mem → α) (Γ.Mem → Γ.types ·) where
  subst X := Sigma.uncurry fun v e σ ↦ X σ[v ↦ e σ]

end Example

end Substitution
