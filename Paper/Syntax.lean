import HeyVL.Verify

namespace Paper

syntax docComment ? "paper_link[" num "]" ppHardSpace term : command
syntax docComment ? "paper_thm[" num "]" ppHardSpace term : command

def Link {α : Sort*} (_ : α) : Prop := True
def LinkThm (α : Sort*) {_ : α} : Prop := True
def LinkLem (α : Sort*) {_ : α} : Prop := True

axiom paperAx {α : Sort*} : α

open Lean in
macro_rules
| `($[$c:docComment]? paper_link[$n] $t) =>
  let name : TSyntax `ident := mkIdent (.mkSimple s!"link{Nat.toSubscriptString n.getNat}")
  `(
    $[$c:docComment]?
    def $name : Link $t := True.intro
  )
| `($[$c:docComment]? paper_thm[$n] $t) =>
  let name : TSyntax `ident := mkIdent (.mkSimple s!"thm{Nat.toSubscriptString n.getNat}")
  `(
    $[$c:docComment]?
    def $name : @LinkThm _ $t := True.intro
  )

declare_syntax_cat pkind
syntax "Definition " : pkind
syntax "Theorem " : pkind
syntax "Lemma " : pkind
syntax "@" term : pkind
syntax "[pkind|" pkind "]" : term

syntax docComment ? "Section " num ", " pkind num ": " term : command

macro_rules
| `([pkind|Definition]) => `("Definition")
| `([pkind|Theorem]) => `("Theorem")
| `([pkind|Lemma]) => `("Lemma")
| `([pkind|@$_]) => `("??")
| `($[$d]? Section $s:num, $k $n:num: $t) => do
  let kind : String :=
    match k with
    | `(pkind|Definition) => "Definition"
    | `(pkind|Theorem) => "Theorem"
    | `(pkind|Lemma) => "Lemma"
    | _ => "??"
  let name : Lean.TSyntax `ident :=
    Lean.mkIdent (.mkStr2 s!"Section{s.getNat}" s!"{kind}{n.getNat}")
  match k with
  | `(pkind|Definition) => `($[$d]? def $name : Link $t := True.intro)
  | `(pkind|Theorem) => `($[$d]? theorem $name : @LinkThm _ $t := True.intro)
  | `(pkind|Lemma) => `($[$d]? lemma $name : @LinkLem _ $t := True.intro)
  | _ => `(def broken := True)

end Paper
