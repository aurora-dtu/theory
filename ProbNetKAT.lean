import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Order.CompletePartialOrder
import WGCL.Subst
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Kernel.Basic
import Mathlib.Topology.Order.ScottTopology
import Mathlib.Topology.Order.Real
import Mathlib.MeasureTheory.Measure.FiniteMeasure
-- import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

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

section Lemma1

example : B[h] = B{{h}} := by simp [B_h, B_b]

example {b c : Set H[F]} : b ⊆ c ↔ B{c} ⊆ B{b} := by
  simp_all [B_b]
  constructor
  · intro h d h'
    exact h.trans h'
  · intro h
    exact h c (by rfl)

example {b c : Set H[F]} : B{b} ∩ B{c} = B{b ∪ c} := by ext d; simp_all [B_b]

-- NOTE: this is different from the notes, they have `B{∅} = 2^H` but it seems to be `B{∅} = 2^2^H`.
example : B{∅} = (Set.univ : Set (Set H[F])) := by simp [B_b]

end Lemma1

example : CompletePartialOrder (Set H[F]) := inferInstance
noncomputable example : CompletePartialOrder ENNReal := inferInstance

instance 𝒪.topology : TopologicalSpace (Set H[F]) := Topology.scott _ Set.univ
def 𝒪 : Set (Set (Set H[F])) := 𝒪.topology.IsOpen
instance 𝒪.IsScott : @Topology.IsScott (Set H[F]) Set.univ _ 𝒪.topology := ⟨rfl⟩

@[simp] theorem 𝒪.mem_iff : S ∈ 𝒪 ↔ @IsOpen _ (Topology.scott _ Set.univ) S := by rfl
-- omit [DecidableEq F] in
-- @[simp] theorem 𝒪.isOpen_iff {S : Set (Set H[F])} :
--     @IsOpen _ (Topology.scott _ Set.univ) S ↔ IsUpperSet S ∧ DirSupInacc S := by
--   simp [@Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (s:=S) _ _ _ _ 𝒪.IsScott]
omit [DecidableEq F] in
@[simp] theorem 𝒪.isClosed_iff {S : Set (Set H[F])} :
    @IsClosed _ (Topology.scott _ Set.univ) S ↔ IsLowerSet S ∧ DirSupClosed S := by
  simp [Topology.IsScott.isClosed_iff_isLowerSet_and_dirSupClosed]

/-- The sets `B[h]` and `∼B[h]` are the subbasic open sets of the Cantor space topology on 2H. -/
instance 𝒞.topology : TopologicalSpace (Set H[F]) :=
  TopologicalSpace.generateFrom (((B[·]) '' Set.univ) ∪ ((B[·]ᶜ) '' Set.univ))
def 𝒞 : Set (Set (Set H[F])) := 𝒞.topology.IsOpen
/-- The family of Borel sets B is the smallest σ-algebra containing the Cantor-open sets, or the
  smallest σ-algebra generated by the Scott-open sets. -/
instance ℬ.measurableSpace : MeasurableSpace (Set H[F]) := @borel _ 𝒪.topology
def ℬ : Set (Set (Set H[F])) := ℬ.measurableSpace.MeasurableSet'

@[simp] theorem 𝒞.mem_iff :
  S ∈ 𝒞 ↔ @IsOpen _ (TopologicalSpace.generateFrom (((B[·]) '' Set.univ) ∪ ((B[·]ᶜ) '' Set.univ))) S := by rfl

theorem generateFrom_𝒞_eq_𝒪 :
    MeasurableSpace.generateFrom (𝒞 (F:=F)) = @borel _ 𝒪.topology := by
  ext S
  constructor
  · intro h
    induction S, h using MeasurableSpace.generateFrom_induction
    next S' h h' =>

      simp_all
      sorry
    next => simp
    next S' h₁ h₂ => simp_all
    next f h₁ h₂ => exact MeasurableSet.iUnion fun b => h₂ b

  · intro h
    induction S, h using MeasurableSpace.generateFrom_induction
    next S' h h' =>


      simp_all
      sorry
    next => simp
    next S' h₁ h₂ => simp_all
    next f h₁ h₂ => exact MeasurableSet.iUnion fun b => h₂ b

@[simp]
instance ℬ.measurableSpace_eq : ℬ.measurableSpace (F:=F) = @borel _ 𝒪.topology := by
  simp [measurableSpace, generateFrom_𝒞_eq_𝒪]

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

open scoped Classical in
@[simp]
noncomputable def my_sSup (D : Set (FiniteMeasure (Set H[F])))
    (hD : DirectedOn instPartialOrderFiniteMeasureSetH.le D) : FiniteMeasure (Set H[F]) :=
  ⟨
      -- NOTE: define measure
      Measure.ofMeasurable
        (fun B hB ↦ if B ∈ 𝒪 then ⨆ μ ∈ D, μ B else 0)
        (by simp)
        (by
          simp_all only [instPartialOrderFiniteMeasureSetH, 𝒪.mem_iff, not_forall,
            Classical.not_imp, not_le, ℬ.measurableSpace_eq,
            FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
          intro f h h'
          split_ifs
          · have : ∀ i, f i ∈ 𝒪 := by
              simp_all
              sorry
            simp_all
            sorry
          · sorry


          -- apply le_antisymm
          -- · simp_all
          --   intro μ hμ
          --   rw [MeasureTheory.measure_iUnion h' h]
          --   gcongr with i
          --   apply le_iSup₂_of_le μ hμ
          --   rfl
          -- · suffices ∑' (i : ℕ), ⨆ μ ∈ D, μ.val (f i) = ⨆ μ ∈ D, ∑' (i : ℕ), μ.val (f i) by
          --     simp_all only [FiniteMeasure.val_eq_toMeasure]
          --     gcongr with B hB
          --     rw [MeasureTheory.measure_iUnion h' h]
          --   simp [@ENNReal.tsum_eq_iSup_sum]
          --   simp [iSup_subtype']
          --   rw [iSup_comm]
          --   congr with S
          --   induction S using Finset.induction with
          --   | empty => simp
          --   | insert n Z h₁ h₂ =>
          --     simp_all only [not_false_eq_true, Finset.sum_insert]
          --     clear h₁ h₂
          --     have : Nonempty (Subtype (Membership.mem D)) := by
          --       simp
          --       sorry
          --     apply le_antisymm
          --     · apply ENNReal.iSup_add_iSup_le
          --       simp
          --       intro B₁ h₁ B₂ h₂
          --       simp_all [DirectedOn]
          --       have ⟨B', hB'D, hB₁, hB₂⟩ := hD B₁ h₁ B₂ h₂
          --       apply le_iSup_of_le ⟨B', hB'D⟩
          --       simp
          --       gcongr
          --       sorry
          --     · simp
          --       intro B hB
          --       simp [ENNReal.add_iSup, ENNReal.iSup_add]
          --       apply le_iSup₂_of_le ⟨B, hB⟩ ⟨B, hB⟩
          --       rfl
        )
      ,
      -- NOTE: is finite measure
      by sorry
    ⟩

open scoped Classical in
noncomputable instance : CompletePartialOrder (FiniteMeasure (Set H[F])) := {instPartialOrderFiniteMeasureSetH with
  sSup D :=
    if hD : DirectedOn instPartialOrderFiniteMeasureSetH.le D then
      my_sSup D hD
    else
      default
  lubOfDirected := by
    intro D h
    simp_all only [instPartialOrderFiniteMeasureSetH, 𝒪.mem_iff, not_forall, not_le, my_sSup,
      FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, dite_eq_ite, ite_true]
    refine isLUB_iff_le_iff.mpr ?_
    intro μ
    simp_all only [instPartialOrderFiniteMeasureSetH, 𝒪.mem_iff, not_forall, not_le,
      FiniteMeasure.mk_apply, upperBounds, Set.mem_setOf_eq]
    constructor
    · intro h ν hν B hB
      obtain ⟨μ, hμF⟩ := μ
      obtain ⟨ν, hνF⟩ := ν
      simp_all only [FiniteMeasure.mk_apply, ne_eq, measure_ne_top, not_false_eq_true,
        ENNReal.toNNReal_le_toNNReal]
      have := h B hB
      rw [ENNReal.toNNReal_le_toNNReal sorry (measure_ne_top μ B)] at this
      apply le_trans _ this
      clear h this
      rw [MeasureTheory.Measure.ofMeasurable_apply _ sorry]
      simp only [DFunLike.coe]; simp [OuterMeasure.trim, Measure.trim]
      sorry
      -- apply le_iSup₂_of_le ⟨ν, hνF⟩ hν
      -- rfl
    · intro h B hB
      simp only [DFunLike.coe]; simp [OuterMeasure.trim, Measure.trim]
      rw [ENNReal.toNNReal_le_toNNReal sorry (measure_ne_top (↑μ) B)]
      rw [MeasureTheory.Measure.ofMeasurable_apply _ sorry]
      sorry
      -- simp
      -- intro ν hν
      -- obtain ⟨μ, hμF⟩ := μ
      -- obtain ⟨ν, hνF⟩ := ν
      -- simp_all only [FiniteMeasure.mk_apply]
      -- have := h hν B hB
      -- simp_all only [FiniteMeasure.mk_apply, ne_eq, measure_ne_top, not_false_eq_true,
      --   ENNReal.toNNReal_le_toNNReal, ge_iff_le]
      -- exact this
  }


    -- -- NOTE: v1 using `sUnion`
    -- let T : Set (Set (Set H[F])) := sorry
    -- have h_sub : T ⊆ 𝒪 := sorry
    -- have hc : T.Countable := sorry
    -- have hU : ⋃₀ T = Set.univ := sorry
    -- have htop : ∀ t ∈ T, μ t ≠ ⊤ := sorry
    -- exact MeasureTheory.Measure.ext_of_generateFrom_of_cover_subset rfl 𝒪.IsPiSystem h_sub hc hU htop h

    -- -- NOTE: v2 using `iUnion`
    -- apply FiniteSpanningSetsIn.ext rfl 𝒪.IsPiSystem ?_ h
    -- sorry

    -- NOTE: v3 using finite measures, i.e. `μ Set.univ < ⊤`
    -- obtain ⟨μ, hμ⟩ := μ
    -- obtain ⟨ν, hν⟩ := ν

    -- apply MeasureTheory.ext_of_generate_finite _ rfl 𝒪.IsPiSystem h (h _ _); simp
    -- suffices IsFiniteMeasure μ by


    -- refine sigmaFinite_trim_bot_iff.mp ?_

    -- refine sigmaFinite_iff_measure_singleton_lt_top.mpr ?_

    -- apply (@isFiniteMeasure_iff_isFiniteMeasureOnCompacts_of_compactSpace _ 𝒪.topology _ _ instCompactSpaceSetH).mpr ?_

    -- sorry


    -- ext B hB
    -- if B ∈ 𝒪 then exact h B ‹B ∈ 𝒪› else
    -- simp_all
    -- induction B, hB using MeasurableSpace.generateFrom_induction
    -- next => simp_all
    -- next => simp_all
    -- next Z h' h'' h''' =>
    --   simp_all
    --   suffices μ Z ≠ ⊤ ∧ ν Z ≠ ⊤ by
    --     simp_all [MeasureTheory.measure_compl]
    --     congr! 1
    --     · apply h _ (fun ⦃a b⦄ a_1 a => a) (IsLowerSet.dirSupInacc fun ⦃a b⦄ a_1 a => a)
    --     · apply h''
    --       contrapose! h'''
    --       simp_all
    --       constructor
    --       · refine isLowerSet_iff_forall_lt.mpr ?_
    --         simp
    --         intro a b hba haZ
    --         simp_all [IsUpperSet, DirSupInacc]
    --         replace h''' := h Z h'''.left h'''.right
    --         symm at h'''
    --         simp_all
    --         sorry


    --       sorry

    --   apply?
    --   rw [MeasureTheory.measure_compl, MeasureTheory.measure_compl]
    --   simp_all
    --   sorry
    -- next f h₁ h₂ h' =>
    --   subst_eqs
    --   simp_all
    --   sorry

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
  Topology.scott _ Set.univ
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

omit [DecidableEq F] in
theorem History.subset_IsOpen {B : Set (Set H[F])}
    (h : @IsOpen _ History.instTopologicalSpace B) (hst : s ⊆ t) (hsB : s ∈ B) : t ∈ B := by
  have ⟨h₂, h₃⟩ := (Topology.IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open (D:=Set.univ)).mp h
  simp_all [IsUpperSet]
  exact h₂ hst hsB

omit [DecidableEq F] in
theorem History.dirac_mono {s t : Set H[F]} (h : s ≤ t) :
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

def Program.sem' (p : Program F) : ℳ (Set H[F]) →o ℳ (Set H[F]) :=
  ⟨(·.bind p.sem), by
    induction p with
    | Dup =>
      intro f g h S hS
      simp [sem]
      sorry
      -- rw [MeasureTheory.Measure.bind_apply hS ?_]
      -- · rw [MeasureTheory.Measure.bind_apply hS ?_]
      --   · refine MeasureTheory.lintegral_mono_fn' (fun _ ↦ by rfl) (le_iff.mpr h)
      --   · sorry
      -- · sorry
    | _ => sorry
  ⟩

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
