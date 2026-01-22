import Mathlib.Data.Finset.Insert
import Lean.PrettyPrinter.Delaborator.Basic

class Substitution (α : Type*) (β : outParam Type*) where
  subst : α → β → α

namespace Substitution

instance [BEq α] [Hashable α] : Substitution (Std.HashMap α β) (α × β) where
  subst map := fun (x, v) ↦ map.insert x v

def substs [Substitution α β] (m : α) (xs : List β) : α :=
    xs.foldr (fun b acc ↦ Substitution.subst acc b) m

declare_syntax_cat substitution_arg
syntax withoutPosition(term) ppHardSpace "↦" ppHardSpace withoutPosition(term) : substitution_arg
syntax ".." withoutPosition(term) : substitution_arg
syntax:max term noWs "[" substitution_arg,* "]" : term
macro_rules
| `($x[ $[$i:term ↦ $j:term],* ]) => `(substs $x ([$[($i, $j)],*]))
| `($x[ .. $xs:term ]) => `(substs $x $xs)

open Lean PrettyPrinter Delaborator SubExpr in
@[app_unexpander Substitution.substs]
def substsUnexpander : Unexpander
| `($(_) $m [$[($x, $y)],*]) => `($m[$[$x:term ↦ $y],*])
| `($(_) $m $xs:term) => `($m[..$xs])
| _ => throw ()

#check fun (x : Std.HashMap String ℕ) ↦ x["a" ↦ 12]
#check fun (x : Std.HashMap String ℕ) ↦ x["a" ↦ 12, "b" ↦ 13]
#check fun (x : Std.HashMap String ℕ) ↦ x["a" ↦ 12]["b" ↦ 13] = x["a" ↦ 12, "b" ↦ 13]
#check fun (x : Std.HashMap String ℕ) ↦ x["b" ↦ 13]["a" ↦ 12]
#check fun (x : Std.HashMap String ℕ) ↦ x[..[("a", 12)]]
#check fun (x : Std.HashMap String ℕ) (xs : List (String × ℕ)) ↦ x[..xs]

-- theorem substs_of_subst {α β : Type*} [Substitution α β] {m : α} {xs : List β}
--     (p : α → Prop) (h : ∀ m (b : β), p m[..[b]]) : p (m[..xs]) := by
--   induction xs generalizing m p with
--   | nil =>
--     simp [substs]
--     sorry
--   | cons x xs ih =>
--     simp_all [substs]

@[grind =, simp]
theorem substs_nil {α β : Type*} [Substitution α β] {m : α} :
    substs m [] = m := rfl
theorem substs_cons {α β : Type*} [Substitution α β] {m : α} {x : β} {xs : List β} :
    substs m (x :: xs) = subst (substs m xs) x := rfl
theorem substs_cons_substs {α β : Type*} [Substitution α β] {m : α} {x : β} {xs : List β} :
    substs m (x :: xs) = substs (substs m xs) [x] := rfl
theorem substs_append {α β : Type*} [Substitution α β] {m : α} {xs ys : List β} :
    substs m (xs ++ ys) = substs (substs m ys) xs := by
  simp [substs]
theorem subst_singleton {α β : Type*} [Substitution α β] {m : α} {x : β} :
    substs m [x] = subst m x := by
  simp [substs]

-- theorem substs_of_binary {α β : Type*} [Substitution α β] {m n : α} {xs : List β}
--     {f : α → α → α} (h : ∀ m n (b : β), (f m n)[..[b]] = (f m[..[b]] n[..[b]])) :
--     (f m n)[..xs] = f m[..xs] n[..xs] := by
--   induction xs generalizing m n f with
--   | nil => simp
--   | cons x xs ih => simp_all [substs_cons]

theorem substs_of_binary {α β γ ι : Type*} [Substitution α ι] [Substitution β ι] [Substitution γ ι]
    {m : α} {n : β} {xs : List ι}
    {f : α → β → γ} (h : ∀ m n (b : ι), (f m n)[..[b]] = (f m[..[b]] n[..[b]])) :
    (f m n)[..xs] = f m[..xs] n[..xs] := by
  induction xs generalizing m n f with
  | nil => simp
  | cons x xs ih => simp_all [substs_cons]

def IsIndepPair {α β ι : Type*} [Substitution α (ι × β)] (m : α) (x : ι) : Prop :=
  ∀ v, m[x ↦ v] = m

@[mk_iff]
class IndepPair {α β ι : Type*} [Substitution α (ι × β)] (m : α) (x : ι) : Prop where
  is_indep : IsIndepPair m x

attribute [grind ., simp] IndepPair.is_indep

@[grind =, simp]
theorem indep_pair {α β ι : Type*} [Substitution α (ι × β)] {m : α} {x : ι}
    (h : IsIndepPair m x) {v} : m[x ↦ v] = m := h v

end Substitution
