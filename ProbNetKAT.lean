import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import WGCL.Subst
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Kernel.Basic
import Mathlib.Topology.Order.ScottTopology
import Mathlib.Topology.Order.Real

namespace ProbNetKAT

variable (F : Type)

inductive Predicate where
  | Drop
  | Skip
  | Test (f : F) (n : ℕ)
  | Dis (t u : Predicate)
  | Con (t u : Predicate)
  | Neg (t : Predicate)
deriving Lean.ToExpr

abbrev Probability := { r : ENNReal // r ≤ 1 }

instance : Lean.ToExpr Probability where
  toExpr p := .const ``Probability []
  toTypeExpr := .const ``Probability []

structure Packet where
  toFun : F → ℕ

structure History where
  head : Packet F
  packets' : List (Packet F)


alias H := History

inductive Program where
  | Filter (t : Predicate F)
  | Mod (f : F) (n : ℕ)
  | Dup
  | Par (p q : Program)
  | Seq (p q : Program)
  | Choice (r : Probability) (p q : Program)
  | Iter (p : Program)
deriving Lean.ToExpr

omit F
variable {F : Type} [DecidableEq F]

instance : Subst (Packet F) F ℕ where
  subst p f n := ⟨fun f' ↦ if f = f' then n else p.toFun f'⟩
instance : Subst (History F) F ℕ where
  subst := fun ⟨π, h⟩ f n ↦ ⟨π[f ↦ n], h⟩

section Syntax

open Lean

declare_syntax_cat pnk_nat
declare_syntax_cat pnk_predicate
declare_syntax_cat pnk_field
declare_syntax_cat pnk_program

syntax:max "~" term:max : pnk_nat
syntax "pnkn" ppHardSpace "{" pnk_nat "}" : term
syntax:max "~" term:max : pnk_predicate
syntax "pnkp" ppHardSpace "{" pnk_predicate "}" : term
syntax:max "~" term:max : pnk_field
syntax "pnkf" ppHardSpace "{" pnk_field "}" : term
syntax:max "~" term:max : pnk_program
syntax "pnk" ppHardSpace "{" pnk_program "}" : term

syntax num : pnk_nat

macro_rules
| `(pnkn { $n:num }) => `($n)
| `(pnkn { ~ $n }) => `($n)

syntax ident : pnk_field

macro_rules
| `(pnkf { f₁ }) => `("f₁")
| `(pnkf { ~$f }) => `($f)

syntax pnk_nat : pnk_predicate
syntax pnk_field "=" pnk_nat : pnk_predicate
syntax "¬" pnk_predicate : pnk_predicate
syntax:52 pnk_predicate:52 "&" pnk_predicate:53 : pnk_predicate
syntax:52 pnk_predicate:52 ";" pnk_predicate:53 : pnk_predicate
syntax "(" pnk_predicate ")" : pnk_predicate

macro_rules
| `(pnkp { 0 }) => `(Predicate.Drop)
| `(pnkp { 1 }) => `(Predicate.Skip)
| `(pnkp { $f:pnk_field = $n }) => `(Predicate.Test (pnkf {$f}) (pnkn {$n}))
| `(pnkp { $t:pnk_predicate & $u }) => `(Predicate.Dis (pnkp {$t}) (pnkp {$u}))
| `(pnkp { $t:pnk_predicate ; $u }) => `(Predicate.Con (pnkp {$t}) (pnkp {$u}))
| `(pnkp { ¬ $t }) => `(Predicate.Neg (pnkp {$t}))
| `(pnkp { ~ $t }) => `($t)
| `(pnkp { ($p:pnk_predicate) }) => `(pnkp {$p})

syntax:54 pnk_predicate:54 : pnk_program
syntax:54 "filter" ppHardSpace pnk_predicate:54 : pnk_program
syntax pnk_field " ← " pnk_nat : pnk_program
syntax "dup" : pnk_program
syntax:48 pnk_program:48 " & " pnk_program:49 : pnk_program
syntax:48 pnk_program:48 " ; " pnk_program:49 : pnk_program
syntax pnk_program " ⊕[" term:max "] " pnk_program : pnk_program
syntax pnk_program "*" : pnk_program
syntax "(" pnk_program ")" : pnk_program

macro_rules
| `(pnk { $t:pnk_predicate }) => `(Program.Filter (pnkp {$t}))
| `(pnk { filter $t:pnk_predicate }) => `(Program.Filter (pnkp {$t}))
| `(pnk { $f:pnk_field ← $n }) => `(Program.Mod (pnkf {$f}) (pnkn {$n}))
| `(pnk { dup }) => `(Program.Dup)
| `(pnk { $p & $q }) => `(Program.Par (pnk {$p}) (pnk {$q}))
| `(pnk { $p ; $q }) => `(Program.Seq (pnk {$p}) (pnk {$q}))
| `(pnk { $p ⊕[ $r ] $q }) => `(Program.Choice $r (pnk {$p}) (pnk {$q}))
| `(pnk { $p * }) => `(Program.Iter (pnk {$p}))
| `(pnk { ~ $p }) => `($p)
| `(pnk { ($p:pnk_program) }) => `(pnk {$p})

syntax "if" pnk_predicate "then" pnk_program "else" pnk_program : pnk_program
syntax "while" pnk_predicate "do" pnk_program : pnk_program

macro_rules
| `(pnk { if $t then $p else $q }) => `(pnk { (filter $t ; $p) & ((filter ¬$t) ; $q) })
| `(pnk { while $t do $p }) => `(pnk { (filter $t ; $p)* ; ¬$t })

section Expander

open Lean PrettyPrinter

@[app_unexpander Program.Mod]
def Program.unexpandMod : Unexpander
| `($(_) pnkf {$f} pnkn {$b}) => `(pnk {$f:pnk_field ← $b})
| `($(_) $f $b) => `(pnk {~$f ← ~$b})
| _ => throw ()
@[app_unexpander Program.Dup]
def Program.unexpandDup : Unexpander
| `($(_)) => `(pnk {dup})
@[app_unexpander Program.Par]
def Program.unexpandPar : Unexpander
| `($(_) $p $q) => `(pnk {~$p & ~$q})
| _ => throw ()
@[app_unexpander Program.Seq]
def Program.unexpandSeq : Unexpander
| `($(_) $p $q) => `(pnk {~$p ; ~$q})
| _ => throw ()
@[app_unexpander Program.Choice]
def Program.unexpandChoice : Unexpander
| `($(_) $r $p $q) => `(pnk {~$p ⊕[$r] ~$q})
| _ => throw ()

/-- info: pnk {~"f₁" ← ~1} : Program String -/
#guard_msgs in #check pnk {f₁ ← 1}
/-- info: pnk {dup} : Program String -/
#guard_msgs in #check (pnk {dup} : Program String)
/-- info: fun p q => pnk {~p & ~q} : Program String → Program String → Program String -/
#guard_msgs in #check fun p q ↦ (pnk {~p & ~q} : Program String)
/-- info: fun p q => pnk {~p ; ~q} : Program String → Program String → Program String -/
#guard_msgs in #check fun p q ↦ (pnk {~p ; ~q} : Program String)
/--
info: fun r p q => pnk {~p ⊕[r] ~q} : Probability → Program String → Program String → Program String
-/
#guard_msgs in #check fun r p q ↦ (pnk {~p ⊕[r] ~q} : Program String)

end Expander

end Syntax

open MeasureTheory.Measure

def ℳ (X : Type) [MeasurableSpace X] := MeasureTheory.Measure X

noncomputable alias η := dirac

instance History.instTopologicalSpace : TopologicalSpace (Set (History F)) :=
  -- NOTE: this requires [Preorder (Set (History F))], which uses the natural ⊆ of sets
  Topology.scott _ Set.univ
instance History.instMeasurableSpace : MeasurableSpace (Set (History F)) :=
  -- NOTE: Construct the smallest measure space containing a collection of basic sets.
  --       The basic sets are the open sets of the Scott topology.
  MeasurableSpace.generateFrom History.instTopologicalSpace.IsOpen

-- NOTE: This would (maybe?) mean that:
--    𝒪 = History.instTopologicalSpace.IsOpen
--    ℬ = History.instMeasurableSpace.MeasurableSpace

-- QUESTION: Perhaps one too many nested `Set ...`?
def 𝒪 : Set (Set (Set (History F))) := History.instTopologicalSpace.IsOpen
def ℬ : Set (Set (Set (History F))) := History.instMeasurableSpace.MeasurableSet'

def History.test (h : History F) (f : F) (n : ℕ) : Prop :=
  match h with | ⟨π, _⟩ => π.toFun f = n
def History.dup (h : History F) : History F := ⟨h.head, h.head :: h.packets'⟩

def Probability.not (p : Probability) : Probability := ⟨1 - p.val, by simp⟩
instance : HasCompl Probability where
  compl := .not

@[simp]
def Program.rep (p : Program F) : ℕ → Program F
  | 0 => pnk {1}
  | n+1 => pnk {1 & ~p ; ~(p.rep n)}

noncomputable section

-- variable [MeasurableSpace X] [TopologicalSpace X]

instance : Add (ℳ (Set (History F))) := inferInstanceAs (Add (MeasureTheory.Measure (Set (History F))))
instance : HSMul ENNReal (ℳ (Set (History F))) (ℳ (Set (History F))) := inferInstanceAs (HSMul ENNReal (MeasureTheory.Measure (Set (History F))) _)
instance : HSMul Probability (ℳ (Set (History F))) (ℳ (Set (History F))) := ⟨fun r μ ↦ r.val • μ⟩
instance : FunLike (ℳ (Set (History F))) (Set (Set (History F))) ENNReal := inferInstanceAs (FunLike (MeasureTheory.Measure (Set (History F))) _ _)

instance : Topology.IsScott (Set (History F)) Set.univ := ⟨rfl⟩

@[simp]
instance History.instLE : LE (ℳ (Set (History F))) where
  le μ ν := ∀ B, IsOpen B → μ B ≤ ν B

instance : PartialOrder (ℳ (Set (History F))) where
  le_refl μ := fun B a => le_refl (μ B)
  le_trans μ ν κ hμν hνκ B hb := le_trans (hμν B hb) (hνκ B hb)
  le_antisymm μ ν h h' := by
    simp_all
    have : ∀ (B : Set (Set (History F))), IsOpen B → μ B = ν B := by
      intro B hB
      apply le_antisymm (h B hB) (h' B hB)
    -- (see [3, p. 185, Theorem 21])
    simp_all only [le_refl, implies_true]
    apply MeasureTheory.Measure.FiniteSpanningSetsIn.ext (by rfl) _ _ this
    · simp
      sorry
    · simp
      sorry



    apply MeasureTheory.Measure.ext fun B hb ↦ le_antisymm ?_ ?_
    · if hO : IsOpen B then
        apply h B hO
      else
        simp only at hO

        apply (Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (D:=Set.univ)).not.mp at hO

        replace hO : ¬IsUpperSet B ∨ ¬DirSupInaccOn Set.univ B :=
          Classical.not_and_iff_not_or_not.mp hO
        rcases hO with h' | h'
        · simp_all [IsUpperSet]
          obtain ⟨s, t, hst, hs, ht⟩ := h'
          -- simp_all [MeasurableSet, History.instMeasurableSpace, History.instTopologicalSpace, MeasurableSpace.generateFrom, Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (D:=Set.univ)]

        · simp_all
          simp_all [DirSupInacc]


        have := Topology.IsScott.isOpen_iff_Iic_compl_or_univ B

        simp_all [History.instTopologicalSpace]
        sorry
    · apply h'
      sorry
  -- le_antisymm μ ν h h' := MeasureTheory.Measure.ext fun B hb ↦ le_antisymm (h B hb) (h' B hb)

instance : SupSet (ℳ (Set (History F))) where
  sSup := sorry

open ProbabilityTheory

@[simp]
def Program.iterDepth : Program F → ℕ
| pnk {filter ~_} | pnk {~_ ← ~_} | pnk {dup} => 0
| pnk {~p & ~q} | pnk {~p ; ~q} | pnk {~p ⊕[_] ~q} => p.iterDepth ⊔ q.iterDepth
| pnk {~p *} => p.iterDepth + 1

@[simp]
theorem Program.iterDepth_rep : (Program.rep p n).iterDepth = if n = 0 then 0 else p.iterDepth := by
  rcases n with _ | n <;> simp_all; induction n with simp_all

def Predicate.sem (t : Predicate F) (a : Set (History F)) :
    ℳ (Set (History F)) :=
  match t with
  | pnkp {0} => η ∅
  | pnkp {1} => η a
  | pnkp {~f = ~n} => η { h ∈ a | h.test f n }
  | pnkp {¬ ~t} => (pnkp {~t}).sem a |>.bind fun b ↦ η (a \ b)
  | pnkp {~p & ~q} => p.sem a |>.bind fun b₁ ↦ q.sem a |>.bind fun b₂ ↦ η (b₁ ∪ b₂)
  | pnkp {~p ; ~q} => p.sem a |>.bind q.sem
def Program.sem (p : Program F) :
    Set (History F) → @ℳ (Set (History F)) History.instMeasurableSpace :=
  match _ : p with
  | pnk {filter ~t} => t.sem
  | pnk {~f ← ~n} => fun a ↦ η ((·[f ↦ n]) '' a)
  | pnk {dup} => fun a ↦  η (.dup '' a)
  | pnk {~p & ~q} => fun a ↦ p.sem a |>.bind fun b₁ ↦ q.sem a |>.bind fun b₂ ↦ η (b₁ ∪ b₂)
  | pnk {~p ; ~q} => fun a ↦ p.sem a |>.bind q.sem
  | pnk {~p ⊕[r] ~q} => fun a ↦ r • p.sem a + rᶜ • q.sem a
  | pnk {~p *} => fun a ↦ ⨆ n, (p.rep n).sem a
termination_by (p.iterDepth, sizeOf p)
decreasing_by all_goals simp_all; (try split_ifs) <;> omega

omit [DecidableEq F] in
theorem History.subset_IsOpen {B : Set (Set (History F))}
    (h : @IsOpen _ History.instTopologicalSpace B) (hst : s ⊆ t) (hsB : s ∈ B) : t ∈ B := by
  have ⟨h₂, h₃⟩ := (Topology.IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open (D:=Set.univ)).mp h
  simp_all [IsUpperSet]
  exact h₂ hst hsB

omit [DecidableEq F] in
theorem History.dirac_mono {s t : Set (History F)} (h : s ≤ t) :
    History.instLE.le (@η _ History.instMeasurableSpace s) (@η _ History.instMeasurableSpace t) := by
  simp [η]
  intro B hB
  have := MeasurableSpace.measurableSet_generateFrom hB
  rw [MeasureTheory.Measure.dirac_apply' _ this, MeasureTheory.Measure.dirac_apply' _ this]
  simp [Set.indicator]
  split_ifs with hs ht <;> simp_all
  contrapose! ht
  exact subset_IsOpen hB h hs

def Predicate.sem_mono (t : Predicate F) : Monotone t.sem := by
  induction t with simp [sem]
  | Drop => apply fun _ _ _ ↦ History.dirac_mono (by rfl)
  | Skip => exact fun _ _ ↦ History.dirac_mono
  | Test =>
    intro f g h
    apply History.dirac_mono
    simp_all
    exact fun _ h' _ => h h'
  | Dis t u iht ihu =>
    intro f g h
    simp_all
    have := iht h
    have := ihu h
    simp_all only [ge_iff_le]
    sorry
  | Con => sorry
  | Neg => sorry
def Program.sem_mono (p : Program F) : Monotone p.sem := by
  induction p with simp [sem]
  | Filter t => exact fun _ _ h ↦ t.sem_mono h
  | Dup =>
    intro f g h
    exact History.dirac_mono (Set.image_mono h)
  | Choice r p q ihp ihq =>
    intro f g h
    simp_all
    intro B hB

    sorry
  | _ => sorry
    -- apply History.dirac_mono
    -- simp
    -- simp [η, dirac, MeasureTheory.OuterMeasure.dirac, MeasureTheory.OuterMeasure.toMeasure, ofMeasurable]
    -- simp only [DFunLike.coe]
    -- simp [MeasureTheory.inducedOuterMeasure, MeasureTheory.OuterMeasure.ofFunction]
    -- simp only [DFunLike.coe]
    -- gcongr with f' h' n
    -- simp only [MeasureTheory.extend]
    -- gcongr with Z
    -- simp [Set.indicator]
    -- split_ifs with h₁ h₂ <;> try simp
    -- simp_all
    -- have : History.dup '' f ⊆ History.dup '' g := Set.image_mono h
    -- contrapose! h₂
    -- simp_all only [not_false_eq_true]




    -- simp_all [History.dup]

    -- apply?
    -- show (dirac (History.dup '' f)) S ≤ (dirac (History.dup '' g)) S
    -- suffices (dirac (History.dup '' f)) ≤ (dirac (History.dup '' g)) by
    --   exact this S

def Program.sem' (p : Program F) : ℳ (Set (History F)) →o ℳ (Set (History F)) :=
  ⟨(·.bind p.sem), by
    induction p with
    | Dup =>
      intro f g h S hS
      simp [sem]
      rw [MeasureTheory.Measure.bind_apply hS ?_]
      · rw [MeasureTheory.Measure.bind_apply hS ?_]
        · refine MeasureTheory.lintegral_mono_fn' (fun _ ↦ by rfl) (le_iff.mpr h)
        · sorry
      · sorry
    | _ => sorry
  ⟩

end

end ProbNetKAT

/-
- In the paper, the semantics function does not define ⟦t & u⟧ and ⟦t ; u⟧, but simply uses ⟦p & q⟧
  by indirection.
- The semantics function on ⟦p*⟧(a) does not immediately terminate.
-/

noncomputable def nonterminating_example (n : ℕ) : {i : ℕ // 1 = 2} :=
  nonterminating_example (n + 1)
decreasing_by
  sorry

example : False := by
  let x := nonterminating_example 0
  have := x.prop
  simp at this
