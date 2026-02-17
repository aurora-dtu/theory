import HeyVL.Verify

namespace Paper

syntax "paper_link[" num "]" ppHardSpace term : command
syntax docComment "paper_link[" num "]" ppHardSpace term : command
syntax "paper_thm[" num "]" ppHardSpace term : command
syntax docComment "paper_thm[" num "]" ppHardSpace term : command

def Link {α : Sort*} (_ : α) : Prop := True
def LinkThm (_ : Sort*) : Type := Unit

axiom paperAx {α : Sort*} : α

open Lean in
macro_rules
| `($c:docComment paper_link[$n] $t) =>
  let name : TSyntax `ident := mkIdent (.mkSimple s!"link{Nat.toSubscriptString n.getNat}")
  `(
    $c:docComment
    def $name : Link $t := True.intro
  )
| `(paper_link[$n] $t) =>
  let name : TSyntax `ident := mkIdent (.mkSimple s!"link{Nat.toSubscriptString n.getNat}")
  `(
    def $name : Link $t := True.intro
  )

end Paper
