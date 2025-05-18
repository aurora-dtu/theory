import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Order.CompletePartialOrder
import WGCL.Subst
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Kernel.Basic
import Mathlib.Topology.Order.ScottTopology
import Mathlib.Topology.Order.Real
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Order.Real
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.MeasureTheory.SetAlgebra
import Canonical

set_option grind.warning false

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

syntax "H[" term "]" : term

macro_rules | `(H[$F]) => `(H $F)

instance : Inhabited (Packet F) := ⟨⟨fun _ ↦ 0⟩⟩
instance : Inhabited H[F] := ⟨default, default⟩

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
instance : Subst H[F] F ℕ where
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

open MeasureTheory Measure

def B_h (h : H[F]) := {c : Set H[F] | h ∈ c}
def B_b (b : Set H[F]) := {c : Set H[F] | b ⊆ c}

notation "B[" h "]" => B_h h
notation "B{" b "}" => B_b b

def ℬ_b (b : Set H[F]) := generateSetAlgebra {B[h] | h ∈ b}
notation "ℬ{" b "}" => ℬ_b b

def ℘ω (X : Set α) := {Y ⊆ X | Y.Finite}

section Lemma1

omit [DecidableEq F]

example : B[h] = B{{h}} := by simp [B_h, B_b]

@[simp]
theorem B_b_subset_iff {b c : Set H[F]} : B{c} ⊆ B{b} ↔ b ⊆ c := by
  simp_all [B_b]
  constructor
  · intro h
    exact h c (by rfl)
  · intro h d h'
    exact h.trans h'

@[simp]
theorem B_b_union {b c : Set H[F]} : B{b ∪ c} = B{b} ∩ B{c} := by ext d; simp_all [B_b]

@[simp]
theorem B_b_empty : B{∅} = (Set.univ : Set (Set H[F])) := by simp [B_b]

-- NOTE: this is not a nice proof to do, as one needs to do the closure and show that that is finite
-- open scoped Classical in
-- example {b : Set H[F]} (h : b.Finite) : (generateSetAlgebra ℬ{b}).Finite := by
--   let S : Finset (Set (Set H[F])) := {{b, {}, bᶜ}}
--   refine Set.Finite.ofFinset S fun x => ?_
--   simp [S]
--   constructor
--   · rintro (⟨_⟩ | ⟨_⟩ | ⟨_⟩)
--     · apply generateSetAlgebra.base _ (by simp_all)
--     · simp_all; apply generateSetAlgebra.empty
--     · simp_all; apply generateSetAlgebra.compl _ (generateSetAlgebra.base _ (by simp))
--   · intro h
--     sorry

-- NOTE: MeasureTheory.Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite !!!

theorem ℬ_b_eq_iUnion : ℬ{(Set.univ : Set H[F])} = ⋃ b ∈ ℘ω Set.univ, ℬ{b} := by
  ext A
  simp only [℘ω, Set.subset_univ, true_and, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  constructor
  · intro h
    induction h with
    | base B hB =>
      obtain ⟨h, hh⟩ := hB
      use {h}, Set.finite_singleton h
      exact generateSetAlgebra.base _ (by simp_all)
    | empty => use {}; simp; exact generateSetAlgebra.empty
    | compl B hB ih =>
      obtain ⟨C, hC, hC'⟩ := ih
      use C, hC
      exact generateSetAlgebra.compl _ hC'
    | union B C hB hC ihB ihC =>
      replace hB : B ∈ ℬ{Set.univ} := hB
      replace hC : C ∈ ℬ{Set.univ} := hC
      obtain ⟨X, hX₁, hX₂⟩ := ihB
      obtain ⟨Y, hY₁, hY₂⟩ := ihC
      use X ∪ Y
      constructor
      · exact Set.Finite.union hX₁ hY₁
      · apply generateSetAlgebra.union _ _ <;> show _ ∈ ℬ{X ∪ Y}
        · apply generateSetAlgebra_mono _ hX₂
          simp_all only [Set.mem_union, Set.setOf_subset_setOf, forall_exists_index, and_imp,
            forall_apply_eq_imp_iff₂]
          intro h hh; use h
          simp_all only [true_or, and_self]
        · apply generateSetAlgebra_mono _ hY₂
          simp_all only [Set.mem_union, Set.setOf_subset_setOf, forall_exists_index, and_imp,
            forall_apply_eq_imp_iff₂]
          intro h hh; use h
          simp_all only [or_true, and_self]
  · rintro ⟨B, hB, hB'⟩; apply MeasureTheory.generateSetAlgebra_mono (by simp) hB'

end Lemma1

example : CompletePartialOrder (Set H[F]) := inferInstance
noncomputable example : CompletePartialOrder ENNReal := inferInstance

def cool : Set (Set (Set H[F])) := {B[h] | h ∈ Set.univ}

omit [DecidableEq F] in
theorem cool_eq : cool (F:=F) = Set.range (B[·]) := by
  simp [cool]; rfl

def cool_topo : TopologicalSpace (Set H[F]) := Topology.scott _ cool

instance cool_topo_IsScott : @Topology.IsScott _ cool _ (cool_topo (F:=F)) :=
  let _ : TopologicalSpace (Set (H F)) := cool_topo
  ⟨rfl⟩

instance 𝒪.topology : TopologicalSpace (Set H[F]) := Topology.scott _ cool
def 𝒪 : Set (Set (Set H[F])) := 𝒪.topology.IsOpen
instance 𝒪.IsScott : @Topology.IsScott (Set H[F]) cool _ 𝒪.topology := ⟨rfl⟩

@[simp]
theorem B_h_nonempty : B[a].Nonempty := by simp [B_h]; exact Set.nonempty_of_mem rfl
@[simp]
theorem B_h_directed : DirectedOn (· ⊆ ·) B[a] := by
  intro A hA B hB
  simp_all [B_h]
  exists A ∪ B
  simp_all

-- example : cool_topo (F:=F) = 𝒪.topology := by
--   simp [cool_topo, 𝒪.topology]
--   refine TopologicalSpace.ext ?_
--   ext S
--   simp_all only [@Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn _ _ _ cool_topo _
--       cool_topo_IsScott]
--   simp_all only [@Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn _ _ _ 𝒪.topology _
--       𝒪.IsScott]
--   simp_all only [and_congr_right_iff]
--   intro hSU
--   simp only [cool, Set.mem_univ, true_and]
--   constructor
--   · intro h
--     simp [DirSupInaccOn,] at h ⊢
--     intro X hX hXD A hXA hAS
--     suffices ∃ a, B[a] = X by
--       obtain ⟨a, ha⟩ := this
--       subst_eqs
--       exact h a hXA hAS
--     simp [B_h]
--     simp [IsLUB, IsLeast, upperBounds, lowerBounds] at hXA
--     obtain ⟨h₁, h₂⟩ := hXA
--     sorry
--   · intro h
--     simp [DirSupInaccOn,] at h ⊢
--     intro a A haA hAS
--     exact h (d:=B[a]) (by simp) (by simp) (a:=A) haA hAS


@[simp] theorem 𝒪.mem_iff : S ∈ 𝒪 ↔ @IsOpen _ (Topology.scott _ cool) S := by rfl
-- omit [DecidableEq F] in
-- @[simp] theorem 𝒪.isOpen_iff {S : Set (Set H[F])} :
--     @IsOpen _ (Topology.scott _ cool) S ↔ IsUpperSet S ∧ DirSupInacc S := by
--   simp [@Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (s:=S) _ _ _ _ 𝒪.IsScott]
-- omit [DecidableEq F] in
-- @[simp] theorem 𝒪.isClosed_iff {S : Set (Set H[F])} :
--     @IsClosed _ (Topology.scott _ cool) S ↔ IsLowerSet S ∧ DirSupClosed S := by
--   simp [Topology.IsScott.isClosed_iff_isLowerSet_and_dirSupClosed]

-- /-- The sets `B[h]` and `∼B[h]` are the subbasic open sets of the Cantor space topology on 2H. -/
-- instance 𝒞.topology : TopologicalSpace (Set H[F]) :=
--   TopologicalSpace.generateFrom (((B[·]) '' Set.univ) ∪ ((B[·]ᶜ) '' Set.univ))
-- def 𝒞 : Set (Set (Set H[F])) := 𝒞.topology.IsOpen
/-- The family of Borel sets B is the smallest σ-algebra containing the Cantor-open sets, or the
  smallest σ-algebra generated by the Scott-open sets. -/
instance ℬ.measurableSpace : MeasurableSpace (Set H[F]) := @borel _ 𝒪.topology
def ℬ : Set (Set (Set H[F])) := ℬ.measurableSpace.MeasurableSet'

-- instance ℬ.measurableSpace_eq : MeasurableSpace.generateFrom ℬ{Set.univ} = ℬ.measurableSpace (F:=F) := by
--   symm
--   simp [ℬ_b, Set.mem_univ, true_and, generateFrom_generateSetAlgebra_eq, measurableSpace]

--   sorry

instance : BorelSpace (Set H[F]) := ⟨rfl⟩

-- @[simp] theorem 𝒞.mem_iff :
--   S ∈ 𝒞 ↔ @IsOpen _ (TopologicalSpace.generateFrom (((B[·]) '' Set.univ) ∪ ((B[·]ᶜ) '' Set.univ))) S := by rfl

-- theorem generateFrom_𝒞_eq_𝒪 :
--     MeasurableSpace.generateFrom (𝒞 (F:=F)) = @borel _ 𝒪.topology := by
--   ext S
--   constructor
--   · intro h
--     induction S, h using MeasurableSpace.generateFrom_induction
--     next S' h h' =>

--       simp_all
--       sorry
--     next => simp
--     next S' h₁ h₂ => simp_all
--     next f h₁ h₂ => exact MeasurableSet.iUnion fun b => h₂ b

--   · intro h
--     induction S, h using MeasurableSpace.generateFrom_induction
--     next S' h h' =>


--       simp_all
--       sorry
--     next => simp
--     next S' h₁ h₂ => simp_all
--     next f h₁ h₂ => exact MeasurableSet.iUnion fun b => h₂ b

@[simp]
instance ℬ.measurableSpace_eq : ℬ.measurableSpace (F:=F) = @borel _ 𝒪.topology := by
  simp [measurableSpace]

theorem ℬ_b_OpensMeasurableSpace :
    @OpensMeasurableSpace _ 𝒪.topology
      (MeasurableSpace.generateFrom (ℬ{Set.univ} : Set (Set (Set H[F])))) := by
  simp [opensMeasurableSpace_iff_forall_measurableSet, ℬ_b_eq_iUnion, ℘ω]
  intro s hs
  refine MeasurableSpace.measurableSet_generateFrom ?_
  sorry

@[simp]
theorem B_h_IsOpen (w : H[F]) : @IsOpen _ 𝒪.topology B[w] := by
  sorry
@[simp]
theorem B_h_MeasurableSet (w : H[F]) : MeasurableSet B[w] :=
  MeasurableSpace.measurableSet_generateFrom (B_h_IsOpen w)
@[simp]
theorem ℬ_b_of_IsOpen {S : Set (Set H[F])} (h : @IsOpen _ 𝒪.topology S) : S ∈ ℬ{Set.univ} := by
  replace h := (@Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn _ _ _ 𝒪.topology _ 𝒪.IsScott).mp h
  simp_all [IsUpperSet, DirSupInaccOn, cool]
  sorry

-- TODO: **The connection between the Cantor generated measurable space and the Scott**
@[simp]
theorem ℬ_b_measurableSpace_is_ℬ :
    MeasurableSpace.generateFrom ℬ{Set.univ} = ℬ.measurableSpace (F:=F) := by
  apply le_antisymm _ ?_ -- ℬ_b_OpensMeasurableSpace.borel_le
  · refine MeasurableSpace.generateFrom_le ?_
    simp [ℬ_b_eq_iUnion, ℘ω]
    intro t x hx htx
    induction htx with
    | base s hs => obtain ⟨_, _, _, _⟩ := hs; simp
    | empty => simp
    | compl => simp_all
    | union => simp_all
  · simp
    rw [borel_eq_generateFrom_isClosed]
    refine MeasurableSpace.generateFrom_mono ?_
    intro S
    simp [ℬ_b_eq_iUnion, ℘ω]
    sorry

open ProbabilityTheory

omit [DecidableEq F] in
theorem 𝒪.IsPiSystem : IsPiSystem (𝒪 (F:=F)) :=
  fun A hA B hB _ ↦ @IsOpen.inter _ 𝒪.topology A B hA hB

-- TODO: Show that DCPO's are actually CompletePartialOrder in Lean.
--       We need to establish that the two notions of directed are equivalent.

/-- Validation of cantor-scott definition of directed is the same as Lean's:
  > A non-empty subset `C ⊆ D` is directed if for any two `x,y ∈ C` there exists some upper bound
  > `x,y ⊑ z in C`.
  The only difference is that Lean's definition does not require `Nonempty`.
-/
example {C : Set α} [PartialOrder α] :
    (∀ x ∈ C, ∀ y ∈ C, ∃ z ∈ C, x ≤ z ∧ y ≤ z) ↔ DirectedOn (· ≤ ·) C := by
  grind only [DirectedOn]

@[simp]
noncomputable instance : PartialOrder (FiniteMeasure (Set H[F])) where
  le μ ν := ∀ B ∈ 𝒪, μ B ≤ ν B
  lt μ ν := (∀ B ∈ 𝒪, μ B ≤ ν B) ∧ ¬∀ B ∈ 𝒪, ν B ≤ μ B
  le_refl := by simp
  le_trans _ _ _ h₁ h₂ B a := (h₁ B a).trans (h₂ B a)
  le_antisymm := by
    intro μ ν hμν hνμ
    obtain ⟨μ, hμ⟩ := μ
    obtain ⟨ν, hν⟩ := ν
    simp_all only [FiniteMeasure.mk_apply, ne_eq, measure_ne_top, not_false_eq_true,
      ENNReal.toNNReal_le_toNNReal]
    have h : ∀ B ∈ 𝒪, μ B = ν B := fun B h ↦ (hμν B h).antisymm (hνμ B h)
    simp_all only [le_refl, implies_true]
    suffices μ = ν by exact FiniteMeasure.eq_of_forall_toMeasure_apply_eq_iff.mpr (by simp_all)
    apply MeasureTheory.ext_of_generate_finite _ rfl 𝒪.IsPiSystem h (h _ _); simp

-- @[simp]
-- noncomputable instance : PartialOrder (ProbabilityMeasure (Set H[F])) where
--   le μ ν := ∀ B ∈ 𝒪, μ B ≤ ν B
--   lt μ ν := (∀ B ∈ 𝒪, μ B ≤ ν B) ∧ ¬∀ B ∈ 𝒪, ν B ≤ μ B
--   le_refl := by simp
--   le_trans _ _ _ h₁ h₂ B a := (h₁ B a).trans (h₂ B a)
--   le_antisymm := by
--     intro μ ν hμν hνμ
--     obtain ⟨μ, hμ⟩ := μ
--     obtain ⟨ν, hν⟩ := ν
--     simp_all only [𝒪.mem_iff, ProbabilityMeasure.mk_apply, ne_eq, measure_ne_top, not_false_eq_true,
--       ENNReal.toNNReal_le_toNNReal]
--     have h : ∀ B ∈ 𝒪, μ B = ν B := fun B h ↦ (hμν B h).antisymm (hνμ B h)
--     simp_all only [𝒪.mem_iff, le_refl, implies_true]
--     suffices μ = ν by apply ProbabilityMeasure.eq_of_forall_toMeasure_apply_eq_iff.mpr (by simp_all)
--     apply MeasureTheory.ext_of_generate_finite _ rfl 𝒪.IsPiSystem h (h _ _); simp

noncomputable def 𝒪.setAlgebra : Set (Set (Set H[F])) := generateSetAlgebra 𝒪
noncomputable def 𝒪.isSetAlgebra : IsSetAlgebra (𝒪.setAlgebra (F:=F)) :=
  MeasureTheory.isSetAlgebra_generateSetAlgebra

omit [DecidableEq F] in
theorem 𝒪.setAlgebraIsPiSystem : _root_.IsPiSystem (𝒪.setAlgebra (F:=F)) :=
  fun A hA B hB _ ↦ by
    simp [setAlgebra]
    exact IsSetRing.inter_mem (IsSetAlgebra.isSetRing isSetAlgebra_generateSetAlgebra) hA hB

@[simp]
noncomputable instance : PartialOrder (ProbabilityMeasure (Set H[F])) where
  le μ ν := ∀ B ∈ 𝒪, μ B ≤ ν B
  lt μ ν := (∀ B ∈ 𝒪, μ B ≤ ν B) ∧ ¬∀ B ∈ 𝒪, ν B ≤ μ B
  le_refl := by simp
  le_trans _ _ _ h₁ h₂ B a := (h₁ B a).trans (h₂ B a)
  le_antisymm := by
    intro μ ν hμν hνμ
    obtain ⟨μ, hμ⟩ := μ
    obtain ⟨ν, hν⟩ := ν
    simp_all only [ProbabilityMeasure.mk_apply, ne_eq, measure_ne_top,
      not_false_eq_true, ENNReal.toNNReal_le_toNNReal]
    have h : ∀ B ∈ 𝒪, μ B = ν B := fun B h ↦ (hμν B h).antisymm (hνμ B h)
    simp_all only [𝒪.mem_iff, le_refl, implies_true]
    suffices μ = ν by apply ProbabilityMeasure.eq_of_forall_toMeasure_apply_eq_iff.mpr (by simp_all)
    apply MeasureTheory.ext_of_generate_finite _ rfl 𝒪.IsPiSystem h (by simp)

def gens : Set (Set (Set H[F])) := (B{·}) '' {b : Set H[F] | b.Finite}
def setAlg := (generateSetAlgebra (gens (F:=F)))

-- TODO: This should probably be for `{B[b] | Finite b}` not all of `𝒪`
-- TODO: After trying this, I think it must be an algebra, which us closed under difference
noncomputable def 𝒪.IsSetSemiring_f : IsSetSemiring (setAlg (F:=F)) where
  empty_mem := by simp [gens, setAlg]; refine IsSetAlgebra.empty_mem isSetAlgebra_generateSetAlgebra
  inter_mem _ h _ _ := IsSetAlgebra.inter_mem isSetAlgebra_generateSetAlgebra h (by simp_all)
  diff_eq_sUnion' A hA B hB := by
    use {A \ B}
    simp
    refine IsSetAlgebra.diff_mem ?_ hA hB
    exact isSetAlgebra_generateSetAlgebra

noncomputable def 𝒪.IsSetSemiring : IsSetSemiring (𝒪 (F:=F)) where
  empty_mem := by simp
  inter_mem _ h _ := by simp; exact IsOpen.inter h
  diff_eq_sUnion' A hA B hB := by

    exists {A \ B}
    simp_all only [mem_iff, Finset.coe_singleton, Set.singleton_subset_iff,
      Set.pairwiseDisjoint_singleton, Set.sUnion_singleton, and_self, and_true]
    simp_all only [@Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn _ _ _ 𝒪.topology _
        𝒪.IsScott]
    simp_all only [cool_eq]
    constructor
    ·
      sorry
    · intro X hX hXN hXD x hXx hxAB
      sorry
      -- simp_all
      -- obtain ⟨w, _, _⟩ := hX
      -- simp_all
      -- exists {w}
      -- simp_all [B_h]
      -- have : w ∈ x := by
      --   have := hXx.left
      --   exact this (a:={w}) (by simp) rfl
      -- constructor
      -- · replace hA := hA.right
      --   simp [DirSupInaccOn] at hA
      --   replace := hA w B_h_nonempty B_h_directed hXx hxAB.left

      --   simp_all



    -- simp_all only [mem_iff, Finset.coe_singleton, Set.singleton_subset_iff,
    --   Set.pairwiseDisjoint_singleton, Set.sUnion_singleton, and_self, and_true]
    -- simp
    -- intro D hD hDD x hX
    -- simp_all
    -- refine isLUB_iff_le_iff.mpr ?_
    -- simp_all [IsLUB, IsLeast, upperBounds]
    -- intro p
    -- constructor
    -- · intro h p' S hS hS' hp'
    --   simp_all
    --   sorry
    -- · intro h h' h''
    --   simp_all [IsLUB]
    --   simp_all

noncomputable def 𝒪.IsSetRing' := (𝒪.isSetAlgebra (F:=F)).isSetRing

-- noncomputable def 𝒪.IsSetSemiring : IsSetSemiring (𝒪 (F:=F)) := 𝒪.IsSetRing.isSetSemiring
noncomputable def 𝒪.IsSetSemiring' := (𝒪.IsSetRing' (F:=F)).isSetSemiring

open scoped Classical in
noncomputable def 𝒪.AddContent (D : Set (ProbabilityMeasure (Set H[F])))
    (hD : DirectedOn (∀ B ∈ 𝒪, · B ≤ · B) D) : AddContent (𝒪 (F:=F)) where
  toFun S := ⨆ μ ∈ D, μ S
  empty' := by simp
  sUnion' := by
    simp only [mem_iff, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    intro S hS hdis hUO
    conv =>
      left
      arg 1
      ext μ
      rw [MeasureTheory.measure_sUnion (Finset.countable_toSet S) hdis
          (fun _ ↦ (MeasurableSpace.measurableSet_generateFrom <| hS ·))]
    simp only [Finset.coe_sort_coe, Finset.tsum_subtype]
    symm
    rw [← Finset.sum_attach]
    conv => right; arg 1; ext; rw [← Finset.sum_attach]
    have := ENNReal.finsetSum_iSup (s:=S.attach) (ι:=D) (f:=fun B μ ↦ μ.val B) ?_
    · convert this <;> simp [iSup_subtype']
    simp_all only [instPartialOrderProbabilityMeasureSetH, mem_iff, not_forall, Classical.not_imp,
      not_le, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, Subtype.forall, Subtype.exists,
      exists_prop]
    intro μ hμ ν hν
    have ⟨m, hmD, hm⟩ := hD μ hμ ν hν
    use m, hmD
    intro B hB
    have hl := hm.left B (hS hB)
    have hr := hm.right B (hS hB)
    have hμ_top : μ.val B ≠ ⊤ := by
      simp_all only [ProbabilityMeasure.val_eq_to_measure, ne_eq, measure_ne_top, not_false_eq_true]
    have hν_top : ν.val B ≠ ⊤ := by
      simp_all only [ProbabilityMeasure.val_eq_to_measure, ne_eq, measure_ne_top, not_false_eq_true]
    have hm_top : m.val B ≠ ⊤ := by
      simp_all only [ProbabilityMeasure.val_eq_to_measure, ne_eq, measure_ne_top, not_false_eq_true]
    constructor
    · exact (ENNReal.toNNReal_le_toNNReal hμ_top hm_top).mp hl
    · exact (ENNReal.toNNReal_le_toNNReal hν_top hm_top).mp hr

-- open scoped Classical in
-- noncomputable def 𝒪.AddContent_f (D : Set (ProbabilityMeasure (Set H[F])))
--     (hD : DirectedOn (∀ B ∈ 𝒪, · B ≤ · B) D) : MeasureTheory.AddContent (setAlg (F:=F)) where
--   toFun S := ⨆ μ ∈ D, μ S
--   empty' := by simp
--   sUnion' := by
--     simp only [mem_iff, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
--     intro S hS hdis hUO
--     conv =>
--       left
--       arg 1
--       ext μ
--       rw [MeasureTheory.measure_sUnion (Finset.countable_toSet S) hdis (by
--         simp_all [setAlg, gens]
--         sorry)]
--     simp only [Finset.coe_sort_coe, Finset.tsum_subtype]
--     symm
--     rw [← Finset.sum_attach]
--     conv => right; arg 1; ext; rw [← Finset.sum_attach]
--     have := ENNReal.finsetSum_iSup (s:=S.attach) (ι:=D) (f:=fun B μ ↦ μ.val B) ?_
--     · convert this <;> simp [iSup_subtype']
--     simp_all only [instPartialOrderProbabilityMeasureSetH, mem_iff, not_forall, Classical.not_imp,
--       not_le, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, Subtype.forall, Subtype.exists,
--       exists_prop]
--     intro μ hμ ν hν
--     have ⟨m, hmD, hm⟩ := hD μ hμ ν hν
--     use m, hmD
--     intro B hB
--     have hl := hm.left B (hS hB)
--     have hr := hm.right B (hS hB)
--     have hμ_top : μ.val B ≠ ⊤ := by
--       simp_all only [ProbabilityMeasure.val_eq_to_measure, ne_eq, measure_ne_top, not_false_eq_true]
--     have hν_top : ν.val B ≠ ⊤ := by
--       simp_all only [ProbabilityMeasure.val_eq_to_measure, ne_eq, measure_ne_top, not_false_eq_true]
--     have hm_top : m.val B ≠ ⊤ := by
--       simp_all only [ProbabilityMeasure.val_eq_to_measure, ne_eq, measure_ne_top, not_false_eq_true]
--     constructor
--     · exact (ENNReal.toNNReal_le_toNNReal hμ_top hm_top).mp hl
--     · exact (ENNReal.toNNReal_le_toNNReal hν_top hm_top).mp hr

open scoped Classical in
noncomputable def 𝒪.AddContentℬ (D : Set (ProbabilityMeasure (Set H[F])))
    (hD : DirectedOn (∀ B ∈ 𝒪, · B ≤ · B) D) : MeasureTheory.AddContent (ℬ{Set.univ} : Set (Set (Set H[F]))) where
  toFun S := ⨆ μ ∈ D, μ S
  empty' := by simp
  sUnion' := by
    simp_all only [mem_iff, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    intro I hI hID hIU
    conv =>
      left; arg 1; ext μ
      rw [MeasureTheory.measure_sUnion (Finset.countable_toSet I) hID (by
        simp_all [setAlg, gens]
        -- TODO: this is doable
        sorry)]
    simp only [Finset.coe_sort_coe, Finset.tsum_subtype]
    simp_all only [ℬ_b_eq_iUnion, ℘ω, Set.subset_univ, true_and, Set.mem_setOf_eq, Set.mem_iUnion,
      exists_prop]
    obtain ⟨G, hG, hIG⟩ := hIU
    clear! hI hID hIG
    symm
    induction I using Finset.induction with
    | empty => simp
    | insert s I hsI ih =>
      simp_all only [not_false_eq_true, Finset.sum_insert]
      simp [iSup_subtype']
      have : IsDirected (Subtype (Membership.mem D)) fun x1 x2 => ∀ B ∈ 𝒪, x1.val B ≤ x2.val B := by
        simp_all
        sorry
      rw [ENNReal.iSup_add_iSup_of_monotone]
      · simp
        intro μ ν h
        simp
        sorry
      · intro μ ν h
        simp
        gcongr
        sorry

-- open scoped Classical in
-- noncomputable def 𝒪.AddContent_no (D : Set (ProbabilityMeasure (Set H[F])))
--     (hD : DirectedOn instPartialOrderProbabilityMeasureSetH.le D) :
--     MeasureTheory.AddContent (𝒪.setAlgebra (F:=F)) := by apply?

-- example {a b : Set α} (h : ¬Disjoint a b) : ∃ t, Disjoint (a \ t) (b \ t)  := by
--   use a ∩ b
--   simp_all
--   exact disjoint_sdiff_sdiff

open scoped Classical in
noncomputable def 𝒪.AddContent' (D : Set (ProbabilityMeasure (Set H[F])))
    (hD : DirectedOn (∀ B ∈ 𝒪.setAlgebra, · B ≤ · B) D) :
    MeasureTheory.AddContent (𝒪.setAlgebra (F:=F)) where
  toFun S := ⨆ μ ∈ D, μ S
  empty' := by simp
  sUnion' := by
    simp only [setAlgebra, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    intro S hS hdis hUO
    conv =>
      left; arg 1; ext μ; arg 1; ext
      rw [MeasureTheory.measure_sUnion (Finset.countable_toSet S) hdis (by
        intro s hs
        have := MeasurableSpace.measurableSet_generateFrom (hS hs)
        simp_all only [generateFrom_generateSetAlgebra_eq])]
    simp only [Finset.coe_sort_coe, Finset.tsum_subtype]
    symm
    rw [← Finset.sum_attach]
    conv => right; arg 1; ext; rw [← Finset.sum_attach]
    have := ENNReal.finsetSum_iSup (s:=S.attach) (ι:=D) (f:=fun B μ ↦ μ.val B) ?_
    · convert this <;> simp [iSup_subtype']
    simp_all only [instPartialOrderProbabilityMeasureSetH, mem_iff, not_forall, Classical.not_imp,
      not_le, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, Subtype.forall, Subtype.exists,
      exists_prop]
    intro μ hμ ν hν
    have ⟨m, hmD, hm⟩ := hD μ hμ ν hν
    use m, hmD
    intro B hB
    -- simp_all only [setAlgebra]
    -- have := (hS hB : generateSetAlgebra 𝒪 B)
    -- clear! S
    -- induction this generalizing μ ν m with
    -- | base B hB' =>
    --   have hl := hm.left B hB'; have hr := hm.right B hB'; clear hm
    --   have hμ_top : μ.val B ≠ ⊤ := by
    --     simp_all only [ProbabilityMeasure.val_eq_to_measure, ne_eq, measure_ne_top, not_false_eq_true]
    --   have hν_top : ν.val B ≠ ⊤ := by
    --     simp_all only [ProbabilityMeasure.val_eq_to_measure, ne_eq, measure_ne_top, not_false_eq_true]
    --   have hm_top : m.val B ≠ ⊤ := by
    --     simp_all only [ProbabilityMeasure.val_eq_to_measure, ne_eq, measure_ne_top, not_false_eq_true]
    --   constructor
    --   · exact (ENNReal.toNNReal_le_toNNReal hμ_top hm_top).mp hl
    --   · exact (ENNReal.toNNReal_le_toNNReal hν_top hm_top).mp hr
    -- | empty => simp_all only [measure_empty, le_refl, and_self]
    -- | union s t hs ht ihs iht =>
    --   sorry
    --   -- if hDis : Disjoint s t then
    --   --   have hMs : MeasurableSet s := sorry
    --   --   have hMt : MeasurableSet t := sorry
    --   --   simp_all only [ℬ.measurableSpace_eq, measure_union]
    --   --   constructor
    --   --   · gcongr <;> simp_all
    --   --   · gcongr <;> simp_all
    --   -- else
    --   --   simp_all only [Set.not_disjoint_iff]
    --   --   sorry
    -- | compl B h ih =>
    --   simp only [MeasureTheory.measure_compl sorry sorry, measure_univ]
    --   constructor
    --   · gcongr

    --     sorry
    --   · gcongr
    --     sorry

    -- TODO : we need IsOpen B of B ∈ S. idk how
    have hl := hm.left B (hS hB); have hr := hm.right B (hS hB); clear hm
    clear! S
    have hμ_top : μ.val B ≠ ⊤ := by
      simp_all only [ProbabilityMeasure.val_eq_to_measure, ne_eq, measure_ne_top, not_false_eq_true]
    have hν_top : ν.val B ≠ ⊤ := by
      simp_all only [ProbabilityMeasure.val_eq_to_measure, ne_eq, measure_ne_top, not_false_eq_true]
    have hm_top : m.val B ≠ ⊤ := by
      simp_all only [ProbabilityMeasure.val_eq_to_measure, ne_eq, measure_ne_top, not_false_eq_true]
    constructor
    · exact (ENNReal.toNNReal_le_toNNReal hμ_top hm_top).mp hl
    · exact (ENNReal.toNNReal_le_toNNReal hν_top hm_top).mp hr

@[simp] theorem 𝒪.AddContent_apply : 𝒪.AddContent D hD S = ⨆ μ ∈ D, (μ S : ENNReal) := by rfl
@[simp] theorem 𝒪.AddContent'_apply : 𝒪.AddContent' D hD S = ⨆ μ ∈ D, (μ S : ENNReal) := by rfl
@[simp] theorem 𝒪.AddContentℬ_apply : 𝒪.AddContentℬ D hD S = ⨆ μ ∈ D, (μ S : ENNReal) := by rfl

theorem 𝒪.AddContent_IsSigmaSubadditive : (𝒪.AddContent D hD).IsSigmaSubadditive := by
  intro f h₁ h₂
  simp only [AddContent_apply, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, iSup_le_iff]
  intro μ hμ
  apply le_trans (measure_iUnion_le (μ:=μ.val) (s:=f))
  gcongr with i
  apply le_iSup₂_of_le μ hμ; rfl
theorem 𝒪.AddContent'_IsSigmaSubadditive : (𝒪.AddContent' D hD).IsSigmaSubadditive := by
  refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum 𝒪.IsSetRing' ?_
  intro f h₁ h₂ h₃
  simp only [AddContent'_apply, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  have hf : ∀ i, MeasurableSet (f i) := by
    intro i
    have := MeasurableSpace.measurableSet_generateFrom (h₁ i)
    simp_all [setAlgebra]
  conv =>
    left; arg 1; ext μ; arg 1; ext hμ
    rw [MeasureTheory.measure_iUnion h₃ hf]
  simp [@ENNReal.tsum_eq_iSup_sum]
  simp_all only [instPartialOrderProbabilityMeasureSetH, not_forall, Classical.not_imp, not_le,
    ℬ.measurableSpace_eq]
  simp [iSup_subtype']
  rw [iSup_comm]
  congr with S
  symm
  rw [← Finset.sum_attach]
  conv => right; arg 1; ext; rw [← Finset.sum_attach]
  have := ENNReal.finsetSum_iSup (s:=S.attach) (ι:=D) (f:=fun i μ ↦ μ.val (f i)) ?_
  · convert this <;> simp [iSup_subtype']
  simp_all only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, Subtype.forall,
    Subtype.exists, exists_prop]
  intro μ hμ ν hν
  have ⟨m, hmD, hm⟩ := hD μ hμ ν hν
  use m, hmD
  intro B hB
  simp_all only [setAlgebra]
  have hl := hm.left (f B) (h₁ B); have hr := hm.right (f B) (h₁ B); clear hm
  clear! S
  have hμ_top : μ.val (f B) ≠ ⊤ := by
    simp_all only [ProbabilityMeasure.val_eq_to_measure, ne_eq, measure_ne_top, not_false_eq_true]
  have hν_top : ν.val (f B) ≠ ⊤ := by
    simp_all only [ProbabilityMeasure.val_eq_to_measure, ne_eq, measure_ne_top, not_false_eq_true]
  have hm_top : m.val (f B) ≠ ⊤ := by
    simp_all only [ProbabilityMeasure.val_eq_to_measure, ne_eq, measure_ne_top, not_false_eq_true]
  constructor
  · exact (ENNReal.toNNReal_le_toNNReal hμ_top hm_top).mp hl
  · exact (ENNReal.toNNReal_le_toNNReal hν_top hm_top).mp hr
theorem 𝒪.AddContentℬ_IsSigmaSubadditive : (𝒪.AddContentℬ D hD).IsSigmaSubadditive := by
  intro f h₁ h₂
  simp only [AddContentℬ_apply, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, iSup_le_iff]
  intro μ hμ
  apply le_trans (measure_iUnion_le (μ:=μ.val) (s:=f))
  gcongr with i
  apply le_iSup₂_of_le μ hμ; rfl

noncomputable def 𝒪.measure (D : Set (ProbabilityMeasure (Set H[F])))
    (hD : DirectedOn (∀ B ∈ 𝒪, · B ≤ · B) D) :=
  (𝒪.AddContent D hD).measure 𝒪.IsSetSemiring (by rfl) 𝒪.AddContent_IsSigmaSubadditive
noncomputable def 𝒪.measure' (D : Set (ProbabilityMeasure (Set H[F])))
    (hD : DirectedOn (∀ B ∈ 𝒪.setAlgebra, · B ≤ · B) D) :=
  (𝒪.AddContent' D hD).measure 𝒪.IsSetSemiring' (by simp [setAlgebra]; rfl) 𝒪.AddContent'_IsSigmaSubadditive
noncomputable def 𝒪.measureℬ (D : Set (ProbabilityMeasure (Set H[F])))
    (hD : DirectedOn (∀ B ∈ 𝒪, · B ≤ · B) D) :=
  (𝒪.AddContentℬ D hD).measure (isSetAlgebra_generateSetAlgebra.isSetRing.isSetSemiring)
    (by simp) 𝒪.AddContentℬ_IsSigmaSubadditive

-- @[simp]
-- theorem 𝒪.measure_apply (h : @IsOpen _ 𝒪.topology S) : 𝒪.measure D hD S = 𝒪.AddContent D hD S :=
--   MeasureTheory.AddContent.measure_eq _ _ (by rfl) _ (by assumption)
@[simp]
theorem 𝒪.measure'_apply (h : @IsOpen _ 𝒪.topology S) : 𝒪.measure' D hD S = 𝒪.AddContent' D hD S :=
  MeasureTheory.AddContent.measure_eq _ _ (by simp [setAlgebra]; rfl) _
    (MeasureTheory.self_subset_generateSetAlgebra h)
@[simp]
theorem 𝒪.measure'_apply' (h : S ∈ 𝒪.setAlgebra) : 𝒪.measure' D hD S = 𝒪.AddContent' D hD S :=
  MeasureTheory.AddContent.measure_eq _ _ (by simp [setAlgebra]; rfl) _ h
@[simp]
theorem 𝒪.measureℬ_apply' {S : Set (Set (H F))} (h : S ∈ 𝒪) : 𝒪.measureℬ D hD S = 𝒪.AddContentℬ D hD S :=
  MeasureTheory.AddContent.measure_eq _ _ (by simp) _ (by simp_all)

open scoped Classical in
@[simp]
noncomputable def my_sSup (D : Set (ProbabilityMeasure (Set H[F])))
    (hD : DirectedOn (∀ B ∈ 𝒪, · B ≤ · B) D) : ProbabilityMeasure (Set H[F]) :=
  ⟨if D.Nonempty then 𝒪.measureℬ D hD else dirac {},
    by split_ifs <;> simp_all [isProbabilityMeasure_iff, biSup_const]⟩

@[simp]
theorem IsUpperSet.eq_univ_of_empty_mem {S : Set (Set α)} (hS : IsUpperSet S) (h : ∅ ∈ S) :
    S = Set.univ := by
  ext A
  simp only [Set.mem_univ, iff_true]
  exact hS (Set.empty_subset A) h

@[simp]
theorem History.eq_univ_of_empty_mem (hS : S ∈ 𝒪) (h : ∅ ∈ S) : S = Set.univ := by
  ext A
  simp_all [Topology.IsScott.isUpperSet_of_isOpen]
  exact @Topology.IsScott.isUpperSet_of_isOpen _ _ _ _ _ 𝒪.IsScott hS _ _ (Set.empty_subset A) h

omit [DecidableEq F] in
@[simp]
theorem dirac_bot (μ : ProbabilityMeasure (Set H[F])) : ∀ B ∈ 𝒪, dirac {} B ≤ μ B := by
  intro B hB
  simp [dirac_apply', MeasurableSpace.measurableSet_generateFrom hB, Set.indicator]
  split_ifs <;> simp_all

open scoped Classical in
noncomputable instance : CompletePartialOrder (ProbabilityMeasure (Set H[F])) :=
  {instPartialOrderProbabilityMeasureSetH with
    sSup D := if hD : DirectedOn (∀ B ∈ 𝒪, · B ≤ · B) D then my_sSup D hD else default
    lubOfDirected := by
      intro D hD
      simp_all only [instPartialOrderProbabilityMeasureSetH, 𝒪.mem_iff, not_forall,
        Classical.not_imp, not_le, my_sSup, dite_true]
      split_ifs with hDE
      · refine isLUB_iff_le_iff.mpr ?_
        intro μ
        simp_all only [𝒪.mem_iff, instPartialOrderProbabilityMeasureSetH, not_forall,
          Classical.not_imp, not_le, ProbabilityMeasure.mk_apply, 𝒪.measureℬ_apply',
          𝒪.AddContentℬ_apply, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, upperBounds,
          Set.mem_setOf_eq]
        simp_all only [instPartialOrderProbabilityMeasureSetH, 𝒪.mem_iff, not_forall,
          Classical.not_imp, not_le]
        constructor
        · intro h ν hν B hB
          apply le_trans _ (h B hB)
          suffices ν B ≤ ⨆ μ ∈ D, μ.val B by
            sorry -- TODO: done, just needs coe
          apply le_iSup₂_of_le ν hν
          simp only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
            ProbabilityMeasure.val_eq_to_measure, le_refl]
        · intro h B hB
          suffices ⨆ μ ∈ D, (μ.val B) ≤ (ENNReal.ofNNReal <| μ B) by
            sorry -- TODO: done, just needs coe
          apply iSup₂_le fun ν hν ↦ ?_
          have := h hν B hB
          simp only [ProbabilityMeasure.val_eq_to_measure,
            ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ge_iff_le]
          sorry -- TODO: done, just needs coe
      · refine isLUB_iff_le_iff.mpr ?_
        intro μ
        simp only [instPartialOrderProbabilityMeasureSetH, 𝒪.mem_iff, not_forall, Classical.not_imp,
          not_le, ProbabilityMeasure.mk_apply, upperBounds, Set.mem_setOf_eq]
        constructor
        · intro h ν hν B hB
          contrapose! hDE; use ν
        · intro h B hB
          have := dirac_bot μ B hB
          simp_all only [instPartialOrderProbabilityMeasureSetH, 𝒪.mem_iff, not_forall,
            Classical.not_imp, not_le, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
            ge_iff_le]
          sorry -- TODO: done, just needs coe
    }

def Kernel.IsContinuous (P : Kernel (Set H[F]) (ℬ (F:=F))) : Prop := by
  let inst₁ : Preorder (Set (H F)) := inferInstance
  let inst₂ : Preorder (Measure (ℬ (F:=F))) := inferInstance
  have : ∀ (a b : Measure (ℬ (F:=F))), inst₂.le a b ↔ ∀ x, a x ≤ b x := by
    intro a b
    simp [inst₂]
    rfl
  exact @ScottContinuous _ _ inst₁ _ P.toFun

def ℳ (X : Type) [MeasurableSpace X] := MeasureTheory.Measure X

noncomputable alias η := dirac

instance History.instTopologicalSpace : TopologicalSpace (Set H[F]) :=
  -- NOTE: this requires [Preorder (Set H[F])], which uses the natural ⊆ of sets
  Topology.scott _ cool
instance History.instMeasurableSpace : MeasurableSpace (Set H[F]) :=
  -- NOTE: Construct the smallest measure space containing a collection of basic sets.
  --       The basic sets are the open sets of the Scott topology.
  MeasurableSpace.generateFrom History.instTopologicalSpace.IsOpen

-- NOTE: This would (maybe?) mean that:
--    𝒪 = History.instTopologicalSpace.IsOpen
--    ℬ = History.instMeasurableSpace.MeasurableSpace

def History.test (h : H F) (f : F) (n : ℕ) : Prop :=
  match h with | ⟨π, _⟩ => π.toFun f = n
def History.dup (h : H F) : H F := ⟨h.head, h.head :: h.packets'⟩

def Probability.not (p : Probability) : Probability := ⟨1 - p.val, by simp⟩
instance : HasCompl Probability where
  compl := .not

@[simp]
def Program.rep (p : Program F) : ℕ → Program F
  | 0 => pnk {1}
  | n+1 => pnk {1 & ~p ; ~(p.rep n)}

noncomputable section

-- variable [MeasurableSpace X] [TopologicalSpace X]

instance : Add (ℳ (Set H[F])) := inferInstanceAs (Add (MeasureTheory.Measure (Set H[F])))
instance : HSMul ENNReal (ℳ (Set H[F])) (ℳ (Set H[F])) := inferInstanceAs (HSMul ENNReal (MeasureTheory.Measure (Set H[F])) _)
instance : HSMul Probability (ℳ (Set H[F])) (ℳ (Set H[F])) := ⟨fun r μ ↦ r.val • μ⟩
instance : FunLike (ℳ (Set H[F])) (Set (Set H[F])) ENNReal := inferInstanceAs (FunLike (MeasureTheory.Measure (Set H[F])) _ _)

instance : Topology.IsScott (Set H[F]) Set.univ := ⟨rfl⟩

@[simp]
instance History.instLE : LE (ℳ (Set H[F])) where
  le μ ν := ∀ B, IsOpen B → μ B ≤ ν B

instance : PartialOrder (ℳ (Set H[F])) where
  le_refl μ := fun B a => le_refl (μ B)
  le_trans μ ν κ hμν hνκ B hb := le_trans (hμν B hb) (hνκ B hb)
  le_antisymm μ ν h h' := by
    simp_all
    have : ∀ (B : Set (Set H[F])), IsOpen B → μ B = ν B := by
      intro B hB
      apply le_antisymm (h B hB) (h' B hB)
    -- (see [3, p. 185, Theorem 21])
    simp_all only [le_refl, implies_true]
    apply MeasureTheory.Measure.FiniteSpanningSetsIn.ext (by rfl) _ _ this
    · simp
      sorry
    · simp
      sorry

instance : SupSet (ℳ (Set H[F])) where
  sSup := sorry

@[simp]
def Program.iterDepth : Program F → ℕ
| pnk {filter ~_} | pnk {~_ ← ~_} | pnk {dup} => 0
| pnk {~p & ~q} | pnk {~p ; ~q} | pnk {~p ⊕[_] ~q} => p.iterDepth ⊔ q.iterDepth
| pnk {~p *} => p.iterDepth + 1

@[simp]
theorem Program.iterDepth_rep : (Program.rep p n).iterDepth = if n = 0 then 0 else p.iterDepth := by
  rcases n with _ | n <;> simp_all; induction n with simp_all

def Predicate.sem (t : Predicate F) (a : Set H[F]) :
    ℳ (Set H[F]) :=
  match t with
  | pnkp {0} => η ∅
  | pnkp {1} => η a
  | pnkp {~f = ~n} => η { h ∈ a | History.test h f n }
  | pnkp {¬ ~t} => (pnkp {~t}).sem a |>.bind fun b ↦ η (a \ b)
  | pnkp {~p & ~q} => p.sem a |>.bind fun b₁ ↦ q.sem a |>.bind fun b₂ ↦ η (b₁ ∪ b₂)
  | pnkp {~p ; ~q} => p.sem a |>.bind q.sem
def Program.sem (p : Program F) :
    Set H[F] → @ℳ (Set H[F]) History.instMeasurableSpace :=
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

-- omit [DecidableEq F] in
-- theorem History.subset_IsOpen {B : Set (Set H[F])}
--     (h : @IsOpen _ History.instTopologicalSpace B) (hst : s ⊆ t) (hsB : s ∈ B) : t ∈ B := by
--   have ⟨h₂, h₃⟩ := (Topology.IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open (D:=Set.univ)).mp h
--   simp_all [IsUpperSet]
--   exact h₂ hst hsB

-- omit [DecidableEq F] in
-- theorem History.dirac_mono {s t : Set H[F]} (h : s ≤ t) :
--     History.instLE.le (@η _ History.instMeasurableSpace s) (@η _ History.instMeasurableSpace t) := by
--   simp [η]
--   intro B hB
--   have := MeasurableSpace.measurableSet_generateFrom hB
--   rw [MeasureTheory.Measure.dirac_apply' _ this, MeasureTheory.Measure.dirac_apply' _ this]
--   simp [Set.indicator]
--   split_ifs with hs ht <;> simp_all
--   contrapose! ht
--   exact subset_IsOpen hB h hs

-- def Predicate.sem_mono (t : Predicate F) : Monotone t.sem := by
--   induction t with simp [sem]
--   | Drop => apply fun _ _ _ ↦ History.dirac_mono (by rfl)
--   | Skip => exact fun _ _ ↦ History.dirac_mono
--   | Test =>
--     intro f g h
--     apply History.dirac_mono
--     simp_all
--     exact fun _ h' _ => h h'
--   | Dis t u iht ihu =>
--     intro f g h
--     simp_all
--     have := iht h
--     have := ihu h
--     simp_all only [ge_iff_le]
--     sorry
--   | Con => sorry
--   | Neg => sorry
-- def Program.sem_mono (p : Program F) : Monotone p.sem := by
--   induction p with simp [sem]
--   | Filter t => exact fun _ _ h ↦ t.sem_mono h
--   | Dup =>
--     intro f g h
--     exact History.dirac_mono (Set.image_mono h)
--   | Choice r p q ihp ihq =>
--     intro f g h
--     simp_all
--     intro B hB

--     sorry
--   | _ => sorry
--     -- apply History.dirac_mono
--     -- simp
--     -- simp [η, dirac, MeasureTheory.OuterMeasure.dirac, MeasureTheory.OuterMeasure.toMeasure, ofMeasurable]
--     -- simp only [DFunLike.coe]
--     -- simp [MeasureTheory.inducedOuterMeasure, MeasureTheory.OuterMeasure.ofFunction]
--     -- simp only [DFunLike.coe]
--     -- gcongr with f' h' n
--     -- simp only [MeasureTheory.extend]
--     -- gcongr with Z
--     -- simp [Set.indicator]
--     -- split_ifs with h₁ h₂ <;> try simp
--     -- simp_all
--     -- have : History.dup '' f ⊆ History.dup '' g := Set.image_mono h
--     -- contrapose! h₂
--     -- simp_all only [not_false_eq_true]




--     -- simp_all [History.dup]

--     -- apply?
--     -- show (dirac (History.dup '' f)) S ≤ (dirac (History.dup '' g)) S
--     -- suffices (dirac (History.dup '' f)) ≤ (dirac (History.dup '' g)) by
--     --   exact this S

-- def Program.sem' (p : Program F) : ℳ (Set H[F]) →o ℳ (Set H[F]) :=
--   ⟨(·.bind p.sem), by
--     induction p with
--     | Dup =>
--       intro f g h S hS
--       simp [sem]
--       sorry
--       -- rw [MeasureTheory.Measure.bind_apply hS ?_]
--       -- · rw [MeasureTheory.Measure.bind_apply hS ?_]
--       --   · refine MeasureTheory.lintegral_mono_fn' (fun _ ↦ by rfl) (le_iff.mpr h)
--       --   · sorry
--       -- · sorry
--     | _ => sorry
--   ⟩

end

end ProbNetKAT

/-
- In the paper, the semantics function does not define ⟦t & u⟧ and ⟦t ; u⟧, but simply uses ⟦p & q⟧
  by indirection.
- The semantics function on ⟦p*⟧(a) does not immediately terminate.
- Fubini's theorem: integral_fin_nat_prod_eq_prod
- MeasureTheory.OuterMeasure.caratheodory
- Measurable.ennreal_induction
- Measurable.ennreal_sigmaFinite_induction
-/

noncomputable def nonterminating_example (n : ℕ) : {i : ℕ // 1 = 2} :=
  nonterminating_example (n + 1)
decreasing_by
  sorry

example : False := by
  let x := nonterminating_example 0
  have := x.prop
  simp at this
