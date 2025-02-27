import pGCL.WeakestPre

namespace pGCL

def ite (b : BExpr ϖ) (c₁ c₂ : pGCL ϖ) : pGCL ϖ :=
  pGCL.prob c₁ ⟨b.probOf, sorry⟩ c₂

declare_syntax_cat varname
syntax ident : varname

syntax:min "var " "{ " varname " }" : term

syntax:max "~" term:max : varname

open Lean in
macro_rules
  | `(var { $x:ident }) =>
    `(term|$(quote x.getId.toString))

declare_syntax_cat exp
declare_syntax_cat bexp

syntax varname : exp
syntax num : exp

syntax:65 exp:65 " + " exp:66 : exp

syntax:max "~" term:max : exp

syntax:65 exp:65 " < " exp:66 : bexp

syntax:max "~" term:max : bexp

declare_syntax_cat stmt
syntax "skip" : stmt
syntax stmt ";" ppDedent(ppLine stmt) : stmt
syntax varname " := " exp : stmt
syntax "while " "(" bexp ")" ppHardSpace "{ " stmt " }" : stmt
syntax "{ " stmt " }" "[]" "{ " stmt " }" : stmt
syntax "{ " stmt " }" "[" exp "]" "{ " stmt " }" : stmt
syntax "if " "(" bexp ")" ppHardSpace "{ " stmt " }" " else " "{ " stmt " }" : stmt

syntax:max "~" term:max : stmt

syntax:min "pgcl " ppHardSpace "{" ppLine stmt ppDedent(ppLine "}") : term

syntax:min "expr " "{ " exp " }" : term
syntax:min "bexpr " "{ " bexp " }" : term

noncomputable def Exp.add (e₁ e₂ : Exp ϖ) : Exp ϖ := fun σ ↦ e₁ σ + e₂ σ
def Exp.ofString (s : String) : Exp String := fun σ ↦ σ s

noncomputable def BExpr.lt (e₁ e₂ : Exp ϖ) : BExpr ϖ := fun σ ↦ e₁ σ < e₂ σ

open Lean in
macro_rules
  | `(expr{$x:ident}) => `(Exp.ofString $(quote x.getId.toString))
  | `(expr{$n:num}) => `($(quote n.getNat))
  | `(expr{$e1 + $e2}) => `(Exp.add (expr{$e1}) (expr{$e2}))
  | `(expr{~$stx}) => pure stx

open Lean in
macro_rules
  | `(bexpr{$e1:exp < $e2}) => `(BExpr.lt (expr{$e1}) (expr{$e2}))
  | `(bexpr{~$stx}) => pure stx

open Lean in
macro_rules
  | `(pgcl { skip }) =>
    `(pGCL.skip)
  | `(pgcl { $x:varname := $e:exp }) =>
    `(pGCL.assign (var {$x}) (expr {$e}))
  | `(pgcl { $p1 ; $p2 }) =>
    `(pGCL.seq (pgcl{$p1}) (pgcl{$p2}))
  | `(pgcl { if ($b) { $s1 } else { $s2 } }) =>
    `(pGCL.ite (bexpr{$b}) (pgcl{$s1}) (pgcl{$s2}))
  | `(pgcl { while ($b) { $s } }) =>
    `(pGCL.loop (bexpr{$b}) (pgcl{$s}))
  | `(pgcl { { $p1 } [$p] { $p2 } }) =>
    `(pGCL.prob (pgcl{$p1}) (expr{$p}) (pgcl{$p2}))
  | `(pgcl {~$stx}) => pure stx

-- noncomputable def p : pGCL String := pgcl {
--   x := 15 ;
--   y := 1 + 2
-- }
-- noncomputable def q : pGCL String := pgcl {
--   x := 15 ;
--   y := 1
-- }

open Lean PrettyPrinter.Delaborator SubExpr

def annAsTerm {any} (stx : TSyntax any) : DelabM (TSyntax any) :=
  (⟨·⟩) <$> annotateTermInfo ⟨stx.raw⟩

def delabNameInner : DelabM (TSyntax `varname) := do
  let e ← getExpr
  match e with
  | .lit (.strVal s) =>
    let x := mkIdent <| .mkSimple s
    pure <| ⟨x.raw⟩
  | _ => `(varname| ~($(← delab))) >>= annAsTerm

partial def delabExprInner : DelabM (TSyntax `exp) := do
  let e ← getExpr
  let stx ←
    match_expr e with
    | OfNat.ofNat _ n =>
      if let some n' := n.nat? then
        pure <| ⟨Syntax.mkNumLit (toString n') |>.raw⟩
      else if let .lit (.natVal n') := n then
        pure <| ⟨Syntax.mkNumLit (toString n') |>.raw⟩
      else
        withAppArg `(exp| ~$(← delab))
    | _ =>
      `(exp| ~$(← delab))
  annAsTerm stx

partial def delabBExprInner : DelabM (TSyntax `bexp) := do
  let e ← getExpr
  let stx ←
    match_expr e with
    -- | OfNat.ofNat _ n =>
    --   if let some n' := n.nat? then
    --     pure <| ⟨Syntax.mkNumLit (toString n') |>.raw⟩
    --   else if let .lit (.natVal n') := n then
    --     pure <| ⟨Syntax.mkNumLit (toString n') |>.raw⟩
    --   else
    --     withAppArg `(bexp| ~$(← delab))
    | _ =>
      `(bexp| ~$(← delab))
  annAsTerm stx

partial def delabExpr : Delab := do
  guard <| match_expr ← getExpr with
    | _ => true
  match ← delabExprInner with
  | `(exp|~$e) => pure e
  | e => `(term|expr {$(⟨e⟩)})

partial def delabPgclInner : DelabM (TSyntax `stmt) := do
  let e ← getExpr
  let stx ←
    match_expr e with
    | pGCL.skip _ => `(stmt| skip)
    | pGCL.seq _ _ _ =>
      let s1 ← withAppFn <| withAppArg delabPgclInner
      let s2 ← withAppArg delabPgclInner
      `(stmt| $s1 ; $s2)
    | pGCL.assign _ _ _ =>
      let x ← withAppFn <| withAppArg delabNameInner
      let e ← withAppArg delabExprInner
      `(stmt| $x:varname := $e)
    | pGCL.loop _ _ _ =>
      let x ← withAppFn <| withAppArg delabBExprInner
      let e ← withAppArg delabPgclInner
      `(stmt| while ($x) { $e })
    | _ =>
      `(stmt| ~$(← delab))

@[delab app.pGCL.skip, delab app.pGCL.assign, delab app.pGCL.seq, delab app.pGCL.loop]
partial def delabPgcl : Delab := do
  guard <| match_expr ← getExpr with
    | pGCL.skip _ => true
    | pGCL.assign _ _ _ => true
    | pGCL.seq _ _ _ => true
    | pGCL.loop _ _ _ => true
    | _ => false
  match ← delabPgclInner with
  | `(stmt|~$e) => pure e
  | s => `(term|pgcl{$s})

/--
info: pgcl {
  skip;
  x := ~3
} : pGCL String
-/
#guard_msgs in
#check (pgcl { skip ; x := 3 } : pGCL String)

def strip_skip : pGCL ϖ → pGCL ϖ
| pGCL.seq .skip s => s.strip_skip
| pGCL.seq s .skip => s.strip_skip
| pGCL.seq s₁ s₂ => s₁.strip_skip.seq s₂.strip_skip
| pGCL.loop b c => .loop b c.strip_skip
| s => s


noncomputable def prog₁ := pgcl {
  skip;
  x := 1;
  y := x + 1;
  while (~((fun _ ↦ true))) { skip; x := 2; skip }
}

example : prog₁.strip_skip = q := by
  simp [prog₁, strip_skip]
  sorry

noncomputable def prog₂ := pgcl {
  x := 1;
  y := x + 1
}

structure Triple (ϖ : Type*) where
  pre : Exp ϖ
  program : pGCL ϖ
  post : Exp ϖ

-- noncomputable instance : HImp (Exp ϖ) where
--   himp a b :=
--     have : Decidable (a ≤ b) := Classical.propDecidable _
--     if a ≤ b then 1 else 0

variable [DecidableEq ϖ]

noncomputable def Triple.valid_wp (t : Triple ϖ) := t.program.wp t.post ≤ t.pre

@[simp] def States.subst_apply [DecidableEq ϖ] {σ : States ϖ} :
  (σ[x ↦ v]) y = if x = y then v else σ y := by simp [subst]

syntax "triple " "{" exp "} " stmt "{" exp "}" : term

macro_rules
  | `(triple { $pre } $prog { $post }) =>
    `(Triple.mk (expr {$pre}) (pgcl {$prog}) (expr {$post}) |>.valid_wp)

theorem asdhjasdhjsas {P Q : Exp ϖ} (h : b.probOf * C.wp P + b.not.probOf * Q ≤ P) :
    (pgcl { while (~b) { ~C } }).wp Q ≤ P := by
  simp [wp_loop, wp_loop_f]
  apply OrderHom.lfp_le
  simp_all
theorem asdhjasdhjs {P Q : Exp ϖ} (h : ∀ Y, b.probOf * C.wp Y + b.not.probOf * Q ≤ Y → P ≤ Y) :
    P ≤ (pgcl { while (~b) { ~C } }).wp Q := by
  simp [wp_loop, wp_loop_f]
  apply OrderHom.le_lfp
  simp_all
theorem asdhjasdhjs' {Q : Exp ϖ}
  (h : ∀ Y, b.probOf * C.wp Y + b.not.probOf * Q ≤ Y → (fun _ ↦ p) ≤ Y) :
    p ≤ (pgcl { while (~b) { ~C } }).wp Q σ := by
  simp [wp_loop, wp_loop_f]
  apply asdhjasdhjs
  simp_all
theorem asdhjasdhjsas' {Q : Exp ϖ}
  (h : (b.probOf * C.wp fun _ ↦ p) + b.not.probOf * Q ≤ fun _ ↦ p) :
    (pgcl { while (~b) { ~C } }).wp Q σ ≤ p := by
  simp [wp_loop, wp_loop_f]
  -- apply?
  apply asdhjasdhjsas
  simp_all

syntax "check " "triple " "{" exp "}" stmt "{" exp "}" ":=" term : command

macro_rules
  | `(check triple { $pre } $prog { $post } := $proof) =>
    `(example : triple {$pre} $prog {$post} := by
      simp [Triple.valid_wp, Nat.ofNat_le]; exact $proof)

attribute [simp] Nat.ofNat_le
attribute [simp] Exp.ofString

syntax "assert " bexp : stmt

macro_rules
  | `(pgcl { assert $b }) =>
    `(pgcl {if (~(bexpr {$b})) { skip } else { skip } })

check triple {10} assert 10 < 9 ; x := 10; if (x < 10) { x := x + 1 } else { skip } {x} := by
  intro σ; simp [ite, ProbExp.pick, BExpr.lt]

example : triple {10} x := 69; while (x < 10) { x := x + 1 } {x} := by
  simp [Triple.valid_wp, Exp.ofString, Exp.add]
  intro σ
  simp_all [BExpr.probOf, BExpr.not, BExpr.lt, Exp.ofString]
  apply asdhjasdhjsas'
  simp_all
  clear σ
  intro σ
  simp_all [BExpr.probOf, BExpr.not, BExpr.lt, Exp.ofString]
  split_ifs with h' h'' <;> try simp_all
  · contrapose h'; simp_all
  · sorry
  -- simp_all

  -- intro Y h σ
  -- have := h σ
  -- split_ifs at this with h' h''
  -- · contrapose h'; simp_all
  -- · simp_all


  -- simp [wp_loop, wp_loop_f]
  -- apply OrderHom.le_lfp

  -- ring_nf; rfl

end pGCL
