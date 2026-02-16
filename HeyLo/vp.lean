import HeyLo.Syntax

open HeyLo

def HeyVL.vp (C : HeyVL) (φ : HeyLo .ENNReal) : HeyLo .ENNReal :=
  match C with
  | heyvl {@x :≈ @μ} => (μ.map (fun v ↦ φ[x ↦ v])).toExpr
  | heyvl {reward(@a)} => φ + a
  | heyvl {@S₁ ; @S₂} => S₁.vp (S₂.vp φ)
  --
  | heyvl {if (⊓) {@S₁} else {@S₂}} => S₁.vp φ ⊓ S₂.vp φ
  | heyvl {assert(@ψ)} => ψ ⊓ φ
  | heyvl {assume(@ψ)} => ψ ⇨ φ
  | heyvl {havoc(@x)} => heylo {⨅ x, @φ}
  | heyvl {validate} => ▵ φ
  --
  | heyvl {if (⊔) {@S₁} else {@S₂}} => S₁.vp φ ⊔ S₂.vp φ
  | heyvl {coassert(@ψ)} => ψ ⊔ φ
  | heyvl {coassume(@ψ)} => ψ ↜ φ
  | heyvl {cohavoc(@x)} => heylo {⨆ x, @φ}
  | heyvl {covalidate} => ▿ φ

syntax "vp⟦" cheyvl "⟧" : term
syntax "vp⟦" cheyvl "⟧(" cheylo ")" : term

macro_rules
| `(vp⟦ $p ⟧) => `(HeyVL.vp heyvl {$p})
| `(vp⟦ $p ⟧($φ)) => `(HeyVL.vp heyvl {$p} heylo {$φ})

@[app_unexpander HeyVL.vp]
def vpUnexpander : Lean.PrettyPrinter.Unexpander
| `($(_) $c) => do
    let c ← match c with | `(heyvl {$c}) => pure c | _ => `(cheyvl|@$c)
    `(vp⟦$c⟧)
| _ => throw ()

namespace HeyVL.vp.example

abbrev x : Ident := ⟨"x", .Bool⟩
example : (vp⟦x :≈ @(.flip p)⟧([x])).sem = p.sem ⊓ 1 := by
  ext σ; simp [HeyVL.vp, Distribution.flip, sem, BinOp.sem, UnOp.sem]

end HeyVL.vp.example
