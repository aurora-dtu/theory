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
  toExpr _ := .const ``Probability []
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

section

variable {F : Type} [DecidableEq F]

instance : Subst (Packet F) F ℕ where
  subst p f n := ⟨fun f' ↦ if f = f' then n else p.toFun f'⟩
instance : Subst H[F] F ℕ where
  subst := fun ⟨π, h⟩ f n ↦ ⟨π[f ↦ n], h⟩

end

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

variable {F : Type}

def B_h (h : H[F]) := {c : Set H[F] | h ∈ c}
def B_b (b : Set H[F]) := {c : Set H[F] | b ⊆ c}

notation "B[" h "]" => B_h h
notation "B{" b "}" => B_b b

def ℬ_b (b : Set H[F]) := generateSetAlgebra {B[h] | h ∈ b}
notation "ℬ{" b "}" => ℬ_b b

def A_ab (a b : Set H[F]) := {c | c ∩ b = a}
notation "A{" a "," b "}" => A_ab a b

def ℘ω (X : Set α) := {Y ⊆ X | Y.Finite}

section Lemma1

@[simp] theorem B_b_eq_B_h : B{{h}} = B[h] := by simp [B_h, B_b]
@[simp] theorem B_b_subset_iff {b c : Set H[F]} : B{c} ⊆ B{b} ↔ b ⊆ c := by
  simp only [B_b, Set.setOf_subset_setOf]
  exact ⟨fun h ↦ h c (by rfl), fun h d h' ↦ h.trans h'⟩
@[simp] theorem B_b_union {b c : Set H[F]} : B{b ∪ c} = B{b} ∩ B{c} := by ext d; simp_all [B_b]
@[simp] theorem B_b_empty : B{∅} = (Set.univ : Set (Set H[F])) := by simp [B_b]

-- NOTE: this is not a nice proof to do, as one needs to do the closure and show that that is finite
-- open scoped Classical in
-- example {b : Set H[F]} (h : b.Finite) : ℬ{b}.Finite := by
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

@[simp] theorem B_h_nonempty : B[a].Nonempty := Set.nonempty_of_mem rfl
@[simp] theorem B_h_directed : DirectedOn (· ⊆ ·) B[a] := by
  intro A hA B hB
  exists A ∪ B
  simp_all [B_h]
@[simp] theorem B_h_upperSet {a : H[F]} : IsUpperSet B[a] := fun ⦃_ _⦄ ↦ (· ·)
@[simp] theorem B_h_univ_mem {a : H[F]} : Set.univ ∈ B[a] := by simp [B_h]

end Lemma1

section Lemma2

theorem A_ab_eq_1 (hab : a ⊆ b) : A{a,b} = (⋂ h ∈ a, B[h]) ∩ (⋂ h ∈ (b \ a), B[h]ᶜ) := by
  ext c
  simp only [A_ab, Set.mem_setOf_eq, B_h, Set.mem_diff, Set.mem_inter_iff, Set.mem_iInter,
    Set.mem_compl_iff, and_imp]
  constructor
  · rintro ⟨_⟩
    simp_all only [Set.mem_inter_iff, implies_true, and_true, not_false_eq_true, and_self]
  · simp_all only [and_imp]
    intro h h'
    simp [not_imp_not] at h'
    replace h' : ∀ i, i ∈ b → i ∈ c → i ∈ a := h'
    replace h' : ∀ i, i ∈ c → i ∈ b → i ∈ a := by exact fun i h₁ h₂ => h' i h₂ h₁
    ext v
    simp_all
    constructor
    · intro ⟨h₁, h₂⟩
      exact h' v h₁ h₂
    · intro h₁
      exact ⟨h v h₁, hab h₁⟩

theorem A_ab_eq_2 (hab : a ⊆ b) : A{a,b} = B{a} \ ⋃ (c : {c | a ⊂ c ∧ c ⊆ b}), B{c} := by
  ext c
  constructor
  · rintro ⟨_⟩
    simp [A_ab, B_b]
    intro c hcbc hcb
    contrapose! hcbc
    simp_all [not_ssubset_of_subset]
  · simp_all [A_ab_eq_1 hab, B_h, B_b]
    intro h h'
    contrapose h'
    simp_all
    replace h' := h' h
    obtain ⟨w, hwb, hwa, hwc⟩ := h'
    use (b ∩ c) ∪ {w}
    constructor
    · simp
      refine (Set.ssubset_iff_of_subset ?_).mpr ?_
      · simp_all
      · use w; simp_all
    · simp_all

-- example (hab : a ⊆ b) (hab' : a' ⊆ b') : A{a,b} ⊆ A{a',b'} ↔ a' ⊆ a ∧ b' \ a' ⊆ b \ a := by
--   sorry

end Lemma2

instance 𝒪.topology : TopologicalSpace (Set H[F]) := Topology.scott _ (Set.range (B[·]))
def 𝒪 : Set (Set (Set H[F])) := fun S ↦ @IsOpen _ 𝒪.topology S
instance 𝒪.IsScott : @Topology.IsScott (Set H[F]) (Set.range (B[·])) _ 𝒪.topology := ⟨rfl⟩

@[simp] theorem 𝒪.IsOpen_iff_mem : @IsOpen _ 𝒪.topology S ↔ S ∈ 𝒪 := by rfl

@[simp] theorem 𝒪.empty_mem : ∅ ∈ 𝒪 (F:=F) := IsOpen_iff_mem.mp isOpen_empty
@[simp] theorem 𝒪.univ_mem : Set.univ ∈ 𝒪 (F:=F) := IsOpen_iff_mem.mp isOpen_univ

theorem 𝒪.mem_iff : S ∈ 𝒪 (F:=F) ↔ IsUpperSet S ∧ DirSupInaccOn (Set.range (B[·])) S :=
  @Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn _ _ _ 𝒪.topology S 𝒪.IsScott

/-- The family of Borel sets B is the smallest σ-algebra generated by the Scott-open sets. -/
instance ℬ.measurableSpace : MeasurableSpace (Set H[F]) := @borel _ 𝒪.topology
def ℬ : Set (Set (Set H[F])) := ℬ.measurableSpace.MeasurableSet'

instance : BorelSpace (Set H[F]) := ⟨rfl⟩

@[simp]
instance ℬ.measurableSpace_eq : ℬ.measurableSpace (F:=F) = @borel _ 𝒪.topology := by
  simp [measurableSpace]

@[simp] theorem B_h_IsOpen (w : H[F]) : B[w] ∈ 𝒪 := by
  simp [𝒪.mem_iff, IsUpperSet]
  constructor
  · intro S T hST hsW; exact hST hsW
  · rintro _ ⟨_, _, _⟩ _ _ _ _ _
    use Set.univ
    simp

@[simp]
theorem B_h_MeasurableSet (w : H[F]) : MeasurableSet B[w] :=
  MeasurableSpace.measurableSet_generateFrom (B_h_IsOpen w)
theorem ℬ_b_MeasurableSet_univ {s : Set (Set H[F])} (h : s ∈ ℬ{Set.univ}) : MeasurableSet s := by
  induction h with
  | base w hw =>
    simp only [Set.mem_univ, true_and, Set.mem_setOf_eq] at hw
    obtain ⟨w, _, _⟩ := hw
    exact B_h_MeasurableSet w
  | empty => simp [IsUpperSet]
  | compl X hX ih => simp_all
  | union => simp_all
@[simp]
theorem ℬ_b_MeasurableSet {s : Set (Set H[F])} (h : s ∈ ℬ{S}) : MeasurableSet s :=
  ℬ_b_MeasurableSet_univ (generateSetAlgebra_mono (by simp) h)

theorem ℬ_b_OpensMeasurableSpace :
    @OpensMeasurableSpace _ 𝒪.topology (MeasurableSpace.generateFrom ℬ{(Set.univ : Set H[F])}) := by
  simp [opensMeasurableSpace_iff_forall_measurableSet, ℬ_b_eq_iUnion, ℘ω]
  intro s hs
  sorry

-- @[simp]
-- theorem ℬ_b_of_IsOpen {S : Set (Set H[F])} (h : S ∈ 𝒪) : S ∈ ℬ{Set.univ} := by
--   apply MeasurableSet.induction_on_open
--   -- have := 𝒪.mem_iff.mp h
--   -- simp_all [IsUpperSet, DirSupInaccOn]
--   -- sorry

@[simp]
theorem 𝒪_open_Measurable (h : S ∈ 𝒪) : MeasurableSet S :=
  MeasurableSpace.measurableSet_generateFrom h

-- TODO: **The connection between the Cantor generated measurable space and the Scott**
@[simp]
theorem ℬ_b_measurableSpace_le_ℬ :
    MeasurableSpace.generateFrom ℬ{Set.univ} ≤ ℬ.measurableSpace (F:=F) := by
  refine MeasurableSpace.generateFrom_le ?_
  simp [ℬ_b_eq_iUnion, ℘ω]
  intro t x hx htx
  induction htx with simp_all
  | base s hs => obtain ⟨_, _, _, _⟩ := hs; simp
@[simp]
theorem ℬ_b_measurableSpace_is_ℬ :
    MeasurableSpace.generateFrom ℬ{Set.univ} = ℬ.measurableSpace (F:=F) := by
  apply le_antisymm ℬ_b_measurableSpace_le_ℬ ?_ -- ℬ_b_OpensMeasurableSpace.borel_le
  simp

  -- apply MeasurableSet.induction_on_open
  -- · simp_all
  -- · simp_all
  -- · intro f hf g₁ g₂
  --   exact MeasurableSet.iUnion fun b => g₂ b

  -- rw [borel_eq_generateFrom_isClosed]

  -- refine MeasurableSpace.generateFrom_mono ?_
  -- intro S
  -- simp [ℬ_b_eq_iUnion, ℘ω]
  sorry

open ProbabilityTheory

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

noncomputable def 𝒪.setAlgebra : Set (Set (Set H[F])) := generateSetAlgebra 𝒪
noncomputable def 𝒪.isSetAlgebra : IsSetAlgebra (𝒪.setAlgebra (F:=F)) :=
  MeasureTheory.isSetAlgebra_generateSetAlgebra

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
    simp_all only [le_refl, implies_true]
    suffices μ = ν by apply ProbabilityMeasure.eq_of_forall_toMeasure_apply_eq_iff.mpr (by simp_all)
    apply MeasureTheory.ext_of_generate_finite _ rfl 𝒪.IsPiSystem h (by simp)

def gens : Set (Set (Set H[F])) := (B{·}) '' {b : Set H[F] | b.Finite}
def setAlg := (generateSetAlgebra (gens (F:=F)))

noncomputable def 𝒪.IsSetRing' := (𝒪.isSetAlgebra (F:=F)).isSetRing
noncomputable def 𝒪.IsSetSemiring' := (𝒪.IsSetRing' (F:=F)).isSetSemiring

theorem ENNReal.finsetSum_iSup' [DecidableEq α] [Preorder ι] (hD : DirectedOn (· ≤ ·) D)
    (f : ι → α → ENNReal) (hf : ∀ s ∈ I, Monotone (fun (a : D) ↦ f a s)) :
    ∑ x ∈ I, ⨆ μ ∈ D, f μ x = ⨆ μ ∈ D, ∑ x ∈ I, f μ x := by
  induction I using Finset.induction with
  | empty => simp
  | insert s I hsI ih =>
    simp_all [not_false_eq_true, Finset.sum_insert]
    simp [iSup_subtype']
    have : IsDirected (Subtype (Membership.mem D)) (· ≤ ·) := by
      refine directedOn_univ_iff.mp ?_
      intro ⟨B, hB⟩ _ ⟨C, hC⟩ _
      have ⟨z, hzD, hz⟩ := hD B hB C hC
      use ⟨z, hzD⟩, by assumption
      exact hz
    rw [ENNReal.iSup_add_iSup_of_monotone]
    · intro ⟨a, ha⟩ ⟨b, hb⟩ hab; exact hf.left hab
    · intro ⟨a, ha⟩ ⟨b, hb⟩ hab
      simp only
      gcongr
      apply hf.right _ ‹_ ∈ I› hab

theorem ENNReal.tsum_iSup' [DecidableEq α] [Preorder ι] (hD : DirectedOn (· ≤ ·) D)
    (f : ι → α → ENNReal) (hf : ∀ s, Monotone (fun (a : D) ↦ f a s)) :
    ∑' x, ⨆ μ ∈ D, f μ x = ⨆ μ ∈ D, ∑' x, f μ x := by
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  have : ⨆ μ ∈ D, ⨆ s, ∑ x ∈ s, f μ x = ⨆ s, ⨆ μ ∈ D, ∑ x ∈ s, f μ x := by
    simp [iSup_subtype']; rw [iSup_comm]
  rw [this]
  congr with I
  apply ENNReal.finsetSum_iSup' hD
  intro _ _; apply hf

open scoped Classical in
noncomputable def 𝒪.AddContent (D : Set (ProbabilityMeasure (Set H[F])))
    (hD : DirectedOn (∀ B ∈ 𝒪, · B ≤ · B) D) : AddContent (𝒪 (F:=F)) where
  toFun S := ⨆ μ ∈ D, μ S
  empty' := by simp
  sUnion' := by
    simp only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    intro S hS hdis hUO; clear hUO
    simp_rw [MeasureTheory.measure_sUnion (Finset.countable_toSet S) hdis
        (fun _ ↦ (𝒪_open_Measurable <| hS ·))]
    simp only [Finset.coe_sort_coe, Finset.tsum_subtype]
    symm
    apply ENNReal.finsetSum_iSup' hD
    intro B hB ⟨μ, hμ⟩ ⟨ν, hν⟩ h
    exact (ENNReal.toNNReal_le_toNNReal (by simp_all) (by simp_all)).mp (h B (hS hB))

@[simp]
theorem ProbabilityMeasure.eq_iff {μ ν : ProbabilityMeasure (Set H[F])} :
    μ.val = ν.val ↔ μ = ν := by
  obtain ⟨μ, hμ⟩ := μ
  obtain ⟨ν, hν⟩ := ν
  constructor
  · rintro ⟨_⟩; rfl
  · intro h
    ext B hB
    exact ProbabilityMeasure.eq_of_forall_toMeasure_apply_eq_iff.mp h B hB

@[simp]
theorem ProbabilityMeasure.apply_eq_iff {μ ν : ProbabilityMeasure (Set H[F])} :
    μ B = ν B ↔ μ.val B = ν.val B := by
  constructor
  · intro h
    obtain ⟨μ, hμ⟩ := μ; obtain ⟨ν, hν⟩ := ν
    simp_all
    rw [ENNReal.toNNReal_eq_toNNReal_iff] at h
    simp_all
  · intro h
    obtain ⟨μ, hμ⟩ := μ; obtain ⟨ν, hν⟩ := ν
    simp_all

theorem ProbabilityMeasure.measure_union' {μ : ProbabilityMeasure (Set H[F])} (hT : MeasurableSet T) :
    μ.val (S ∪ T) = μ.val S + μ.val T - μ.val (S ∩ T) := by
  suffices μ.val (S ∪ T) + μ.val (S ∩ T) = μ.val S + μ.val T by
    exact ENNReal.eq_sub_of_add_eq' (by simp_all) this
  simp [MeasureTheory.measure_union_add_inter (μ:=μ) (s:=S) (t:=T) hT]
theorem ProbabilityMeasure.measure_union {μ : ProbabilityMeasure (Set H[F])} (hT : MeasurableSet T) :
    μ (S ∪ T) = μ S + μ T - μ (S ∩ T) := by
  suffices μ (S ∪ T) + μ (S ∩ T) = μ S + μ T by exact eq_tsub_of_add_eq this
  obtain ⟨μ, hμ⟩ := μ
  simp_all
  rw [← ENNReal.toNNReal_add (by simp_all) (by simp_all),
    ← ENNReal.toNNReal_add (by simp_all) (by simp_all)]
  refine (ENNReal.toNNReal_eq_toNNReal_iff' ?_ ?_).mpr ?_
  · simp
  · simp
  · rw [MeasureTheory.measure_union_add_inter (μ:=μ) (s:=S) (t:=T) hT]

@[simp]
theorem ashdjasasd {μ : ProbabilityMeasure (Set H[F])} (h : MeasurableSet B) : μ.val Bᶜ = 1 - μ.val B := by
  rw [measure_compl] <;> simp_all
@[simp]
theorem ashdjasasd' {μ : ProbabilityMeasure (Set H[F])} (h : B ∈ ℬ{b}) : μ.val Bᶜ = 1 - μ.val B := by
  rw [measure_compl]
  · simp_all
  · apply ℬ_b_MeasurableSet h
  · simp_all

@[simp]
def ℬ_b_IsSetAlgebra : IsSetAlgebra ℬ{b} := isSetAlgebra_generateSetAlgebra
@[simp]
def ℬ_b_IsSetRing : IsSetRing ℬ{b} := ℬ_b_IsSetAlgebra.isSetRing

open scoped Classical in
@[simp]
theorem B_b_mem_ℬ_b_fin : B{Finset.toSet b} ∈ ℬ{Finset.toSet b} := by
  induction b using Finset.induction with
  | empty => simp [IsSetAlgebra.univ_mem]
  | insert x B hxB ih =>
    simp_all only [Finset.coe_insert]
    have : B{insert x ↑B} = B[x] ∩ B{↑B} := by rw [@Set.insert_eq]; simp [-Set.singleton_union]
    simp_all only
    have h₁ : B{insert x ↑B} ⊆ B{↑B} := by simp_all
    have : ℬ{↑B} ⊆ ℬ{insert x ↑B} := generateSetAlgebra_mono (by simp_all)
    simp_all
    apply IsSetAlgebra.inter_mem ℬ_b_IsSetAlgebra
    · apply generateSetAlgebra.base _ (by simp)
    · apply generateSetAlgebra_mono _ ih
      simp_all

@[simp]
theorem B_b_mem_ℬ_b (h : b.Finite) : B{b} ∈ ℬ{b} := by
  have := B_b_mem_ℬ_b_fin (b:=h.toFinset)
  simp_all

theorem A_ab_mem_ℬ_b (hb : b.Finite) (hab : a ⊆ b) : A{a,b} ∈ ℬ{b} := by
  rw [A_ab_eq_2 hab]
  refine IsSetRing.diff_mem ℬ_b_IsSetRing ?_ ?_
  · have : B{a} ∈ ℬ{a} := B_b_mem_ℬ_b (Set.Finite.subset hb hab)
    apply generateSetAlgebra_mono _ this
    simp_all only [Set.setOf_subset_setOf, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro w hw; use w, hab hw
  · have : {c | a ⊂ c ∧ c ⊆ b}.Finite :=
      Set.Finite.subset (Set.Finite.finite_subsets hb) (by simp_all)
    set C : Finset _ := this.toFinset
    convert_to ⋃ c ∈ C, B{c} ∈ ℬ{b}
    · simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.iUnion_subtype]
      congr! 3 with c
      simp_all [C]
    · apply MeasureTheory.IsSetAlgebra.biUnion_mem ℬ_b_IsSetAlgebra
      simp_all only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, and_imp, C]; clear C
      intro c hac hcb
      have : ℬ{c} ⊆ ℬ{b} := by
        apply MeasureTheory.IsSetAlgebra.generateSetAlgebra_subset _ ℬ_b_IsSetAlgebra
        intro
        simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
        rintro w hw ⟨_, _⟩
        apply generateSetAlgebra.base _
        use w, hcb hw
      exact this (B_b_mem_ℬ_b (Set.Finite.subset hb hcb))

theorem B_b_decompose (h : a ⊆ b) : B{a} = ⋃ c ∈ {c | a ⊆ c ∧ c ⊆ b}, A{c,b} := by
  symm
  calc
    ⋃ c ∈ {c | a ⊆ c ∧ c ⊆ b}, A{c,b} = ⋃ c ∈ {c | a ⊆ c ∧ c ⊆ b}, {d | d ∩ b = c} := by simp [A_ab]
    _ = {d | a ⊆ d} := by ext; simp_all

theorem ashjdsjahd' {μ ν : ProbabilityMeasure (Set H[F])}
    (hO : ∀ B ∈ ((B{·}) '' {b : Set H[F] | b.Finite}), μ B = ν B) : μ = ν := by
  have := MeasureTheory.ext_of_generate_finite (μ:=μ.toMeasure) (ν:=ν.toMeasure) ℬ{Set.univ} (by simp) (IsSetSemiring.isPiSystem (IsSetRing.isSetSemiring isSetAlgebra_generateSetAlgebra.isSetRing)) ?_ (by simp)
  · ext; simp_all
  · intro S hS
    simp [ℬ_b_eq_iUnion, ℘ω] at hS
    obtain ⟨b, hb, hb'⟩ := hS
    simp_all
    obtain ⟨A, hAF, hAF', h, _, _⟩ := MeasureTheory.mem_generateSetAlgebra_elim hb'
    simp_all
    have h₁μ : ∀ f : Set (Set (Set H[F])) → Set (Set H[F]),
        (μ.val (⋃ a ∈ A, f a) : ENNReal) = (⨆ a ∈ A, μ.val (f a) : ENNReal) := by
      intro f
      refine measure_biUnion_eq_iSup (Set.Finite.countable hAF) ?_
      sorry
    have h₁ν : ∀ f : Set (Set (Set H[F])) → Set (Set H[F]),
        (ν.val (⋃ a ∈ A, f a) : ENNReal) = (⨆ a ∈ A, ν.val (f a) : ENNReal) := by
      intro f
      refine measure_biUnion_eq_iSup (Set.Finite.countable hAF) ?_
      sorry
    simp_all
    congr! 3 with t ht
    clear h₁μ h₁ν
    have h₂μ : ∀ f : Set (Set H[F]) → Set (Set H[F]),
        (μ.val (⋂ a ∈ t, f a) : ENNReal) = (⨅ a ∈ t, μ.val (f a) : ENNReal) := by
      intro f
      sorry
    have h₂ν : ∀ f : Set (Set H[F]) → Set (Set H[F]),
        (ν.val (⋂ a ∈ t, f a) : ENNReal) = (⨅ a ∈ t, ν.val (f a) : ENNReal) := by
      intro f
      sorry
    simp_all
    clear h₂μ h₂ν
    congr! 3 with B hB
    obtain (⟨w, hw, _, _⟩ | ⟨w, hw, hw'⟩) := h t ht B hB
    · have := hO {w}
      simp_all
    · have := hO {w}
      simp_all
      have : MeasurableSet B := by
        apply MeasurableSet.compl_iff.mp
        rw [← hw']
        exact B_h_MeasurableSet w
      have : IsZeroOrProbabilityMeasure μ.val := ⟨by simp⟩
      have : IsZeroOrProbabilityMeasure ν.val := ⟨by simp⟩
      have : μ.val B ≤ 1 := MeasureTheory.prob_le_one
      have : ν.val B ≤ 1 := MeasureTheory.prob_le_one
      suffices 1 - μ.val Bᶜ = 1 - ν.val Bᶜ by
        have h₁ := measure_compl (μ:=μ.val) (s:=B) (by assumption) (by simp_all)
        have h₂ := measure_compl (μ:=ν.val) (s:=B) (by assumption) (by simp_all)
        rw [h₁, h₂] at this
        simp at this
        simp_all
        apply (ENNReal.sub_right_inj (a:=1) ?_ ?_ ?_).mp h₂ <;> simp_all
      congr! 1

theorem asjhdas (h : S ∈ ℬ{w}) : ∃ A : Finset (Finset (Set (Set H[F]))),
      S = ⋃ a ∈ A, ⋂ t ∈ a, t
    ∧ (∀ a ∈ A, ∀ t ∈ a, (∃ h ∈ w, B[h] = t) ∨ ∃ h ∈ w, B[h] = tᶜ) := by
  obtain ⟨A, hAF, hAF', hAw, _, _⟩ := MeasureTheory.mem_generateSetAlgebra_elim h
  set A' : Set (Finset (Set (Set H[F]))) := Set.range (fun (x : A) ↦ (hAF' x.val x.prop).toFinset)
  have : A'.Finite := by
    simp [A']
    have : Fintype ↑A := hAF.fintype
    apply Set.finite_range
  have := this.fintype
  use A'.toFinset
  simp [A']
  clear! A'
  simp_all
  constructor
  · simp only [Set.biUnion_eq_iUnion]
    apply le_antisymm
    · simp
      intro t ht
      have htF := hAF' t ht
      refine Set.subset_iUnion_of_subset htF.toFinset fun ⦃a⦄ => ?_
      simp_all
    · simp
      rintro t' t htA ⟨_⟩
      simp
      exact Set.subset_iUnion₂_of_subset t htA fun ⦃a⦄ a => a
  · rintro t' t htA ⟨_⟩ s hs
    simp_all only [Set.Finite.mem_toFinset]
    exact hAw t htA s hs

def B_fin := ((B{·}) '' {b : Set H[F] | b.Finite})

open scoped Classical in
theorem ℬ_b_finite_if (h : b.Finite) : ℬ{b}.Finite := by
  induction b, h using Set.Finite.induction_on_subset with
  | empty =>
    simp [ℬ_b]
    refine Set.Finite.ofFinset {∅, Set.univ} fun x => ?_
    simp
    constructor
    · rintro (⟨_, _⟩ | ⟨_, _⟩)
      · apply generateSetAlgebra.empty
      · refine IsSetAlgebra.univ_mem (isSetAlgebra_generateSetAlgebra)
    · intro h
      induction h with
      | base => simp_all
      | empty => simp
      | compl => aesop
      | union => aesop
  | insert s h x hF =>
    rename_i F w S
    sorry
open scoped Classical in
theorem ℬ_b_compact_if (h : b.Finite) (h : s ∈ ℬ{b}) : IsCompact s := by
  sorry

theorem unique_decomposition (hb : b.Finite) (h : B ∈ ℬ{b}) : ∃ X ⊆ {a | a ⊆ b}, B = ⋃ a ∈ X, A{a, b} := by
  rename_i F
  apply MeasureTheory.mem_generateSetAlgebra_elim at h
  obtain ⟨A, hAF, hAF', hAw, _, _⟩ := h
  simp_all only [Set.mem_setOf_eq]
  replace hAw : ∀ a ∈ A, ∀ t ∈ a, ∃ h ∈ b, (B[h] = t ∨ B[h] = tᶜ) := by
    intro a ha t ht
    obtain (⟨w, hw⟩ | ⟨w, hw⟩) := hAw a ha t ht <;> use w <;> simp_all
  -- let w (a : {a // a ∈ A}) (t : {t // t ∈ a}) : H[F] := hAw a t
  let A' : Set (Set (H[F])) := (fun (⟨a, ha⟩ : A) ↦ (fun (⟨t, ht⟩) ↦ hAw a ha t ht |>.choose) '' (Set.univ : Set a)) '' (Set.univ : Set A)
  use A'; simp [A']; clear A'
  constructor
  · intro t'
    simp_all
    rintro a ha ⟨_⟩
    intro h
    simp_all
    rintro x hx ⟨_⟩
    sorry
  · ext t
    simp_all
    sorry

def unique_decomposition_set {b : Set H[F]} (hb : b.Finite) (h : B ∈ ℬ{b}) : Set (Set (H F)) :=
  (unique_decomposition hb h).choose
def unique_decomposition_spec {b : Set H[F]} (hb : b.Finite) (h : B ∈ ℬ{b}) :
    unique_decomposition_set hb h ⊆ {a | a ⊆ b} ∧ B = ⋃ a ∈ unique_decomposition_set hb h, A{a, b} :=
  (unique_decomposition hb h).choose_spec

open scoped Classical in
noncomputable def 𝒪.extend_μ_to_A_ab {b : Set H[F]} (hb : b.Finite) (μ : B_fin (F:=F) → ENNReal) :
    {A{a,b} | a ⊆ b} → ENNReal :=
  fun ⟨B, hB⟩ ↦
    let a := hB.choose
    have ⟨ha₁, ha₂⟩ : a ⊆ b ∧ B = A{a,b} := ⟨hB.choose_spec.left, hB.choose_spec.right.symm⟩
    have : Fintype {c | a ⊆ c ∧ c ⊆ b} :=
      Set.Finite.fintype <| Set.Finite.subset (Set.Finite.finite_subsets hb) (by simp)
    have c_fin : ∀ c : {c | a ⊆ c ∧ c ⊆ b}, c.val.Finite := (Set.Finite.subset hb ·.prop.right)
    have : Fintype ↑a := (Set.Finite.subset hb ha₁).fintype
    ∑ c : {c | a ⊆ c ∧ c ⊆ b}, (1)^(Finset.card ((c_fin c).toFinset \ a.toFinset)) * μ ⟨B{c.val}, by use c; simp [c_fin]⟩

open scoped Classical in
noncomputable def 𝒪.extend_μ {b : Set H[F]} (hb : b.Finite) (μ : {A{a,b} | a ⊆ b} → ENNReal) :
    ℬ{b} → ENNReal :=
  fun ⟨B, hB⟩ ↦
    ∑' a : unique_decomposition_set hb hB,
      μ ⟨A{a.val,b}, ⟨a, (unique_decomposition_spec hb hB).left a.prop, rfl⟩⟩

open scoped Classical in
noncomputable def 𝒪.extend_AddContentℬ (hb : b.Finite) (μ : B_fin (F:=F) → ENNReal) : MeasureTheory.AddContent ℬ{(b : Set H[F])} where
  toFun S :=
    if h : S ∈ ℬ{b} then
      𝒪.extend_μ hb (𝒪.extend_μ_to_A_ab hb μ) ⟨S, h⟩
    else
      0
  empty' := by sorry
  sUnion' := by
    simp_all
    intro I hI hID hIU
    have :
          (∑ u ∈ I, if h : u ∈ ℬ{b} then extend_μ hb (extend_μ_to_A_ab hb μ) ⟨u, h⟩ else 0)
        = ∑ u : I, extend_μ hb (extend_μ_to_A_ab hb μ) ⟨u, hI u.prop⟩ := by
      apply Finset.sum_dite_of_true
    rw [this]; clear this
    simp
    induction I using Finset.induction with
    | empty =>
      simp [extend_μ, extend_μ_to_A_ab]
      intro a ha
      split

      sorry
    | insert =>
      simp_all
      sorry

open scoped Classical in
noncomputable def 𝒪.AddContentℬ (D : Set (ProbabilityMeasure (Set H[F])))
    (hD : DirectedOn (∀ B ∈ 𝒪, · B ≤ · B) D) : MeasureTheory.AddContent ℬ{(Set.univ : Set H[F])} where
  toFun S := ⨆ μ ∈ D, μ S
  empty' := by simp
  sUnion' := by
    simp_all only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    intro I hI hID hIU
    simp_rw [MeasureTheory.measure_sUnion (Finset.countable_toSet I) hID
      (fun _ ↦ (ℬ_b_MeasurableSet <| hI ·))]
    simp_all only [ℬ_b_eq_iUnion, ℘ω, Set.subset_univ, true_and, Set.mem_setOf_eq, Set.mem_iUnion,
      exists_prop, Finset.coe_sort_coe, Finset.tsum_subtype]
    symm
    obtain ⟨w, hwF, hIw⟩ := hIU
    apply ENNReal.finsetSum_iSup' hD
    intro B hB μ ν h_le
    simp_all only [instPartialOrderProbabilityMeasureSetH, not_forall, Classical.not_imp, not_le]
    have := h_le B
    simp at this

    have ⟨_, ⟨a, ha⟩, haF⟩ := hI hB
    simp_all only [ge_iff_le]
    subst_eqs
    simp_all only [Set.mem_iUnion, exists_prop]
    obtain ⟨haF, hBa⟩ := haF
    obtain ⟨A, hAF, hAF', h, _, _⟩ := MeasureTheory.mem_generateSetAlgebra_elim hBa
    simp_all only [Set.mem_setOf_eq]
    simp only [measure_biUnion_eq_iSup sorry sorry]
    gcongr with t ht
    sorry
    -- suffices μ.val (⋂ x ∈ t, x) = ⨅ x ∈ t, μ.val (x) ∧ ν.val (⋂ x ∈ t, x) = ⨅ x ∈ t, ν.val x by
    --   simp_all only [Subtype.mk_le_mk, ProbabilityMeasure.val_eq_to_measure]
    --   clear this
    --   gcongr with B hB
    --   obtain (⟨w, _, _, _⟩ | ⟨w, _, hw⟩) := h t ht B hB
    --   · have := h_le B[w] (B_h_IsOpen w)
    --     clear h_le
    --     obtain ⟨μ, _⟩ := μ
    --     obtain ⟨ν, _⟩ := ν
    --     simp_all
    --   ·

    --     sorry


    -- constructor
    -- · sorry
    -- · sorry

@[simp] theorem 𝒪.AddContentℬ_apply : 𝒪.AddContentℬ D hD S = ⨆ μ ∈ D, (μ S : ENNReal) := by rfl
theorem 𝒪.AddContentℬ_IsSigmaSubadditive : (𝒪.AddContentℬ D hD).IsSigmaSubadditive := by
  intro f h₁ h₂
  simp only [AddContentℬ_apply, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, iSup_le_iff]
  intro μ hμ
  apply le_trans (measure_iUnion_le (μ:=μ.val) (s:=f))
  gcongr with i
  apply le_iSup₂_of_le μ hμ; rfl

noncomputable def 𝒪.measureℬ (D : Set (ProbabilityMeasure (Set H[F])))
    (hD : DirectedOn (∀ B ∈ 𝒪, · B ≤ · B) D) :=
  (𝒪.AddContentℬ D hD).measure (isSetAlgebra_generateSetAlgebra.isSetRing.isSetSemiring)
    (by simp) 𝒪.AddContentℬ_IsSigmaSubadditive

@[simp]
theorem 𝒪.measureℬ_apply' {S : Set (Set (H F))} (h : S ∈ 𝒪) : 𝒪.measureℬ D hD S = 𝒪.AddContentℬ D hD S :=
  MeasureTheory.AddContent.measure_eq _ _ (by simp) _ (by sorry)

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
      simp_all only [instPartialOrderProbabilityMeasureSetH, not_forall,
        Classical.not_imp, not_le, my_sSup, dite_true]
      split_ifs with hDE
      · refine isLUB_iff_le_iff.mpr ?_
        intro μ
        simp_all only [instPartialOrderProbabilityMeasureSetH, not_forall,
          Classical.not_imp, not_le, ProbabilityMeasure.mk_apply, 𝒪.measureℬ_apply',
          𝒪.AddContentℬ_apply, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, upperBounds,
          Set.mem_setOf_eq]
        simp_all only [instPartialOrderProbabilityMeasureSetH, not_forall,
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
        simp only [instPartialOrderProbabilityMeasureSetH, not_forall, Classical.not_imp,
          not_le, ProbabilityMeasure.mk_apply, upperBounds, Set.mem_setOf_eq]
        constructor
        · intro h ν hν B hB
          contrapose! hDE; use ν
        · intro h B hB
          have := dirac_bot μ B hB
          simp_all only [instPartialOrderProbabilityMeasureSetH, not_forall,
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
  Topology.scott _ (Set.range (B[·]))
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

-- instance : Topology.IsScott (Set H[F]) Set.univ := ⟨rfl⟩

@[simp]
instance History.instLE : LE (ℳ (Set H[F])) where
  le μ ν := ∀ B, IsOpen B → μ B ≤ ν B

instance : PartialOrder (ℳ (Set H[F])) where
  le_refl μ := fun B a => le_refl (μ B)
  le_trans μ ν κ hμν hνκ B hb := le_trans (hμν B hb) (hνκ B hb)
  le_antisymm μ ν h h' := by
    simp_all
    have : ∀ (B : Set (Set H[F])), B ∈ 𝒪 → μ B = ν B := by
      intro B hB
      apply le_antisymm (h B hB) (h' B hB)
    -- (see [3, p. 185, Theorem 21])
    simp_all only [le_refl, implies_true]
    apply MeasureTheory.Measure.FiniteSpanningSetsIn.ext (by rfl) _ _ this
    · exact 𝒪.IsPiSystem
    · sorry

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

variable [DecidableEq F]

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
