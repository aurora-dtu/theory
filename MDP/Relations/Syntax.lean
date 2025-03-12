import MDP.OptimalCost

namespace MDP.Relations

declare_syntax_cat relation

scoped syntax "≤" : relation
scoped syntax "≥" : relation
scoped syntax "=" : relation
scoped syntax "=ᶠ" : relation
scoped syntax "∃<" : relation
scoped syntax "∃>" : relation
scoped syntax "?" : relation

scoped syntax "relations "
  "[" term "]" relation "[" term "]" relation relation "[" term "]" relation "[" term "]" :
    term
scoped syntax "rela " "{" "["term"]" relation "["term"]" "}" : term

open Lean in
macro_rules
  | `(rela { [$a] ≤ [$b] }) =>
    `(∀ {State Act} [DecidableEq State] ($(mkIdent `M) : MDP State Act)
        ($(mkIdent `c) : $(mkIdent `M).Costs), $a ≤ $b)
  | `(rela { [$a] ≥ [$b] }) => `(rela {[$b] ≤ [$a]})
  | `(rela { [$a] = [$b] }) =>
    `(∀ {State Act} [DecidableEq State] ($(mkIdent `M) : MDP State Act)
        ($(mkIdent `c) : $(mkIdent `M).Costs), $a = $b)
  | `(rela { [$a] =ᶠ [$b] }) =>
    `(∀ {State Act} [DecidableEq State] ($(mkIdent `M) : MDP State Act)
        ($(mkIdent `c) : $(mkIdent `M).Costs), MDP.FiniteBranching $(mkIdent `M) → $a = $b)
  | `(rela { [$a] ∃< [$b] }) =>
    `(∃ (State : Type) (Act : Type),
      Exists fun ($(mkIdent `M) : MDP State Act) ↦
      Exists fun ($(mkIdent `c) : $(mkIdent `M).Costs) ↦
      ∃ (s : State), $a s < $b s)
  | `(rela { [$a] ∃> [$b] }) => `(rela { [$b] ∃< [$a] })
  | `(rela { [$_] ? [$_] }) => `(true)

open Lean in
macro_rules
  | `(relations [$a] $ab [$b] $ac $bd [$c] $cd [$d]) => `(
      (rela { [$a] $ab [$b] }) ∧
      (rela { [$a] $ac [$c] }) ∧
      (rela { [$b] $bd [$d] }) ∧
      (rela { [$c] $cd [$d] }))

end MDP.Relations
