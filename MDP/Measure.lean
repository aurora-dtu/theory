import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Probability.ProductMeasure
import MDP.Bellman
import MDP.Relational
import MDP.SupSup

open MeasurableSpace MeasureTheory

namespace MeasurableSpace.GenerateMeasurable

variable {α : Type*} {S : Set (Set α)}

open GenerateMeasurable

def union {s t : Set α} (hs : GenerateMeasurable S s) (ht : GenerateMeasurable S t) :
    GenerateMeasurable S (s ∪ t) := by
  have := GenerateMeasurable.iUnion (s:=S) (fun i ↦ if i = 0 then s else t) (by grind)
  simp at this
  convert this
  ext x; simp;
  constructor
  · rintro (h | h)
    · use 0; simp [h]
    · use 1; simp [h]
  · grind
def inter {s t : Set α} (hs : GenerateMeasurable S s) (ht : GenerateMeasurable S t) :
    GenerateMeasurable S (s ∩ t) := by
  rw [Set.inter_eq_compl_compl_union_compl s t]
  refine GenerateMeasurable.compl (sᶜ ∪ tᶜ) (union (hs.compl _) (ht.compl _))
def diff {s t : Set α} (hs : GenerateMeasurable S s) (ht : GenerateMeasurable S t) :
    GenerateMeasurable S (s \ t) := inter hs (ht.compl _)
def univ : GenerateMeasurable S Set.univ := by
  have := GenerateMeasurable.compl (s:=S) _ GenerateMeasurable.empty
  simpa

end MeasurableSpace.GenerateMeasurable

namespace MDP

@[grind]
structure Path' (M : MDP State Act) where
  states : ℕ → State
  property : ∀ i,
    states (i + 1) ∈ M.succs_univ (states i)

attribute [simp, grind] Path'.property

variable {State : Type*} {Act : Type*}
variable {M : MDP State Act}

noncomputable instance {π : M.Path} : Inhabited ↑(M.succs_univ π.last) where
  default := Classical.choice M.instNonemptySuccsUniv

namespace Path

noncomputable def extendArb (π : M.Path) (n : ℕ) : M.Path :=
  match n with
  | 0 => π
  | n + 1 => (π.extend default).extendArb n

@[grind, simp]
theorem extendArb_length {π : M.Path} {n : ℕ} : ‖π.extendArb n‖ = ‖π‖ + n := by
  fun_induction extendArb with
  | case1 => rfl
  | case2 => simp_all only [extend_length, Nat.succ_eq_add_one]; omega

@[grind, simp]
theorem extendArb_getElem {π : M.Path} {n : ℕ} (i : ℕ) (hi : i < ‖π‖) :
    (π.extendArb n)[i]'(by simp; omega) = π[i] := by
  fun_induction extendArb with
  | case1 => rfl
  | case2 n n' ih =>
    simp_all only [extend_length, extend_getElem_nat, Nat.succ_eq_add_one]
    simp_all [extendArb]
    rw [ih]
    omega

theorem extendArb_add {π : M.Path} {n m : ℕ} :
    π.extendArb (n + m) = (π.extendArb n).extendArb m := by
  fun_induction extendArb generalizing m with grind [extendArb]

theorem extendArb_one {π : M.Path} :
    π.extendArb 1 = π.extend default := by rfl
@[grind, simp]
theorem extendArb_zero {π : M.Path} :
    π.extendArb 0 = π := by rfl

theorem extendArb_succ_getElem {π : M.Path} {n : ℕ} (i : ℕ) (hn : i < ‖π‖ + n) :
    -- (π.extendArb n)[i]'(by simp; omega) = (π.extendArb (i - ‖π‖ + 1))[i]'(by simp; omega) := by
    (π.extendArb (n + 1))[i]'(by simp; omega) = (π.extendArb n)[i]'(by simp; omega) := by
  induction n generalizing π with
  | zero => simp; grind
  | succ i ih =>
    simp_all [extendArb]
    grind

theorem extendArb_getElem' {π : M.Path} {n m : ℕ} (i : ℕ) (h : i < ‖π‖ + n) (h' : i < ‖π‖ + m) :
    (π.extendArb n)[i]'(by simp; omega) = (π.extendArb m)[i]'(by simp; omega) := by
  wlog h : n ≤ m
  · grind
  induction m, h using Nat.le_induction with grind [extendArb_succ_getElem]

noncomputable def setLength (π : M.Path) (n : ℕ) : M.Path :=
  if n ≤ ‖π‖ then π.take (n - 1) else π.extendArb (n - ‖π‖)

@[grind, simp]
theorem setLength_length {π : M.Path} {n : ℕ} (h : n ≠ 0) : ‖π.setLength n‖ = n := by
  grind [setLength]

@[grind, simp]
theorem setLength_getElem {π : M.Path} {n : ℕ} (hn : n ≠ 0) (i : ℕ) (hi : i < n) :
    (π.setLength n)[i]'(by simp [hn, hi]) = (π.setLength (i + 1))[i]'(by simp_all) := by
  grind [setLength, extendArb_getElem', take]

noncomputable def infinite (π : M.Path) : M.Path' :=
  {
    states n := (π.setLength (n + 1))[n]'(by grind)
    property := by
      intro i
      rw [← setLength_getElem (n:=i + 1 + 1)] <;> try omega
      grind
  }

end Path

namespace Path'

variable (π π' : M.Path')

def take (n : ℕ) : M.Path := ⟨
  List.ofFn (n:=n+1) (π.states ·.val),
  by simp,
  by simp only [List.length_ofFn, add_tsub_cancel_right, List.getElem_ofFn, π.property,
    implies_true]⟩

def prepend (s : M.prev_univ (π.states 0)) : M.Path' :=
  ⟨fun n ↦ match n with | 0 => s | n+1 => π.states n, by grind⟩

/-- The set of finite prefixes of an infinite path -/
def pref : Set M.Path := {⟨List.ofFn (n:=n+1) (π.states ·.val), by simp, by grind⟩ | n : ℕ}

noncomputable def Prob (𝒮 : M.Scheduler) : ENNReal :=
  ∏' i : ℕ, M.P (π.states i) (𝒮 (π.take i)) (π.states i.succ)

theorem eq_iff : π = π' ↔ π.states = π'.states := by grind

@[simp] theorem take_length (n : ℕ) : ‖π.take n‖ = n + 1 := by simp [take]
@[simp] theorem take_getElem (n : ℕ) (i : Fin n) : (π.take n)[i] = π.states i := by
  simp only [take, Fin.getElem_fin, Path.mk_getElem, List.getElem_ofFn]
@[simp] theorem take_getElem' (n : ℕ) (i : ℕ) (h : i < ‖π.take n‖) :
    (π.take n)[i] = π.states i := by
  simp only [take, Path.mk_getElem, List.getElem_ofFn]

-- def cast {s' : State} (h : s = s') : M.Path' s' := ⟨π.states, by grind, by grind⟩

end Path'

section Measure

variable {State : Type*}
variable {M : MDP State Unit}

/--
info: MeasureTheory.Measure.infinitePi.{u_1, u_2} {ι : Type u_1} {X : ι → Type u_2} {mX : (i : ι) → MeasurableSpace (X i)}
  (μ : (i : ι) → Measure (X i)) : Measure ((i : ι) → X i)
-/
#guard_msgs in
#check Measure.infinitePi

/-

infintiePi (α → Measure β) : Measure (α → β)

infintiePi (State → Measure State) : Measure (State → State)

infintiePi (ℕ → Measure State) : Measure (ℕ → State)

infintiePi (Path → Measure State) : Measure (Path → State)
infintiePi (Path → Measure Path) : Measure (Path → Path)

(infintiePi (Path → Measure State)).map (fun π ↦ ‖π‖) : Measure (ℕ → State)

-/

instance : MeasurableSpace State := generateFrom Set.univ
noncomputable def succsAddContent (s : State) :
    AddContent (α:=State) Set.univ where
  toFun S := ∑' s' : S, M.P s () s'
  empty' := by simp
  sUnion' := by
    intro I hI hI_disjoint hI_union
    rw [@Set.sUnion_eq_iUnion]
    simp only [Finset.coe_sort_coe, ← Finset.tsum_subtype]
    rw [ENNReal.tsum_biUnion'']
    intro ⟨a, ha⟩ _ ⟨b, hb⟩ hb hab
    simp_all only [Set.mem_univ, ne_eq, Subtype.mk.injEq]
    exact hI_disjoint ha hb hab
noncomputable def succsMeasure (s : State) : Measure State :=
  (M.succsAddContent s).measure
    (by
      constructor <;> try simp
      intro s t
      use {s \ t}
      simp)
    (by simp [instMeasurableSpace])
    (by
      intro I
      simp only [Set.mem_univ, implies_true, DFunLike.coe, succsAddContent, forall_const]
      apply ENNReal.tsum_iUnion_le_tsum)

instance : IsProbabilityMeasure (M.succsMeasure s) := ⟨by
  simp [succsMeasure]
  rw [AddContent.measure_eq]
  · simp only [DFunLike.coe, succsAddContent, tsum_univ]
    refine (P_sum_one_iff M).mpr ?_
    obtain ⟨⟨_⟩, h⟩ := M.instNonemptyAct (s:=s)
    exact h
  · ext; simp
  · simp⟩

noncomputable def Path.succsAddContent (π : M.Path) :
    AddContent (α:=State) Set.univ where
  toFun S := ∑' s' : S, M.P π.last () s'
  empty' := by simp
  sUnion' := by
    intro I hI hI_disjoint hI_union
    rw [@Set.sUnion_eq_iUnion]
    simp only [Finset.coe_sort_coe, ← Finset.tsum_subtype]
    rw [ENNReal.tsum_biUnion'']
    intro ⟨a, ha⟩ _ ⟨b, hb⟩ hb hab
    simp_all only [Set.mem_univ, ne_eq, Subtype.mk.injEq]
    exact hI_disjoint ha hb hab
noncomputable def Path.succsMeasure (π : M.Path) : Measure State :=
  (Path.succsAddContent (M:=M) π).measure
    (by
      constructor <;> try simp
      intro s t
      use {s \ t}
      simp)
    (by simp [instMeasurableSpace])
    (by
      intro I
      simp only [Set.mem_univ, implies_true, DFunLike.coe, succsAddContent, forall_const]
      apply ENNReal.tsum_iUnion_le_tsum)

instance : IsProbabilityMeasure (Path.succsMeasure (M:=M) π) := ⟨by
  simp [Path.succsMeasure]
  rw [AddContent.measure_eq]
  · simp only [DFunLike.coe, Path.succsAddContent, tsum_univ]
    refine (P_sum_one_iff M).mpr ?_
    obtain ⟨⟨_⟩, h⟩ := M.instNonemptyAct (s:=π.last)
    exact h
  · ext; simp
  · simp⟩

noncomputable def Path.succsAddContent' (s : State) (π : {π : M.Path // π[0] = s}) :
    AddContent (α:=State) Set.univ where
  toFun S := ∑' s' : S, M.P π.val.last () s'
  empty' := by simp
  sUnion' := by
    intro I hI hI_disjoint hI_union
    rw [@Set.sUnion_eq_iUnion]
    simp only [Finset.coe_sort_coe, ← Finset.tsum_subtype]
    rw [ENNReal.tsum_biUnion'']
    intro ⟨a, ha⟩ _ ⟨b, hb⟩ hb hab
    simp_all only [Set.mem_univ, ne_eq, Subtype.mk.injEq]
    exact hI_disjoint ha hb hab
noncomputable def Path.succsMeasure' (s : State) (π : {π : M.Path // π[0] = s}) : Measure State :=
  (Path.succsAddContent (M:=M) π).measure
    (by
      constructor <;> try simp
      intro s t
      use {s \ t}
      simp)
    (by simp [instMeasurableSpace])
    (by
      intro I
      simp only [Set.mem_univ, implies_true, DFunLike.coe, succsAddContent, forall_const]
      apply ENNReal.tsum_iUnion_le_tsum)

instance : IsProbabilityMeasure (Path.succsMeasure' s (M:=M) π) := ⟨by
  simp [Path.succsMeasure']
  rw [AddContent.measure_eq]
  · simp only [DFunLike.coe, Path.succsAddContent, tsum_univ]
    refine (P_sum_one_iff M).mpr ?_
    obtain ⟨⟨_⟩, h⟩ := M.instNonemptyAct (s:=π.val.last)
    exact h
  · ext; simp
  · simp⟩

noncomputable def Idk.succsAddContent (s : State) (n : ℕ) :
    AddContent (α:=Path[M,s,=n+1]) Set.univ where
  toFun S := ∑' π : S, π.val.val.Prob default
  empty' := by simp
  sUnion' := by
    intro I hI hI_disjoint hI_union
    rw [@Set.sUnion_eq_iUnion]
    simp only [Finset.coe_sort_coe, ← Finset.tsum_subtype]
    rw [ENNReal.tsum_biUnion'']
    intro ⟨a, ha⟩ _ ⟨b, hb⟩ hb hab
    simp_all only [Set.mem_univ, ne_eq, Subtype.mk.injEq]
    exact hI_disjoint ha hb hab
noncomputable def Idk.succsMeasure (s : State) (n : ℕ) : Measure Path[M,s,=n+1] :=
  (Idk.succsAddContent (M:=M) s n).measure
    (by
      constructor <;> try simp
      intro s t
      use {s \ t}
      simp)
    (by
      simp [Subtype.instMeasurableSpace]
      refine measurable_iff_comap_le.mp ?_
      intro s h
      exact measurableSet_generateFrom trivial)
    (by
      intro I
      simp only [Set.mem_univ, implies_true, DFunLike.coe, succsAddContent, forall_const]
      apply ENNReal.tsum_iUnion_le_tsum (t:=I) (f:=fun π ↦ π.val.Prob default))

instance : IsProbabilityMeasure (Idk.succsMeasure (M:=M) s n) := ⟨by
  simp [Idk.succsMeasure]
  rw [AddContent.measure_eq]
  · simp only [DFunLike.coe, Idk.succsAddContent]
    have := Path.tsum_Prob_eq_one (M:=M) (s:=s) (𝒮:=default) n
    rw [← this]
    apply tsum_eq_tsum_of_ne_zero_bij fun ⟨x, hx⟩ ↦ ⟨x, by simp⟩ <;> simp
    exact Set.inclusion_injective fun ⦃a⦄ a ↦ trivial
  · simp [Subtype.instMeasurableSpace]
    apply le_antisymm
    · refine measurable_iff_comap_le.mp ?_
      intro s h
      exact measurableSet_generateFrom trivial
    · refine generateFrom_le ?_
      simp
      intro t
      refine MeasurableSet.of_subtype_image ?_
      exact measurableSet_generateFrom trivial
  · simp⟩

noncomputable def piMeasure : Measure (State → State) :=
  Measure.infinitePi M.succsMeasure
noncomputable def Path.piMeasure (s : State) : Measure ({π : M.Path // π[0] = s} → State) :=
  Measure.infinitePi (Path.succsMeasure' s)

def embed : (ℕ → State) → ({π : M.Path // π[0] = s} → State) := fun f π ↦ f (‖π.val‖ - 1)
def embed.injective : Function.Injective (embed (M:=M) (s:=s)) := by
  intro f g h
  ext n
  unfold embed at h
  let π : M.Path := {s}
  have := congrFun h ⟨π.setLength (n + 1), sorry⟩
  simp at this
  exact this

def embed.measurable : MeasurableEmbedding (embed (M:=M) (s:=s)) := by
  constructor
  · exact injective
  · refine measurable_cylinderEvents_lambda embed ?_
    simp [embed]
    intro π h
    sorry
  · sorry

noncomputable def Idk.piMeasure' (s : State) : Measure (ℕ → State) :=
  (Path.piMeasure s (M:=M)).comap embed

open scoped Classical in
example {s' : State} (h : s' ∈ M.succs_univ s) :
      Path.piMeasure s (M:=M) (cylinder [
        (⟨({s} : M.Path), by simp⟩ : {π : M.Path // π[0] = s}),
        (⟨({s} : M.Path).extend ⟨s', h⟩, by simp⟩ : {π : M.Path // π[0] = s})
      ].toFinset (Set.pi Set.univ fun ⟨⟨π, hπ'⟩, hπ⟩ ↦ if π = {s} then {s'} else M.succs_univ π.last))
    = M.P s () s' := by
  simp [Path.piMeasure]
  rw [Measure.infinitePi_cylinder]
  · simp
    simp [Path.succsMeasure', Path.succsAddContent]
    conv =>
      left
      arg 2
      ext
      rw [AddContent.measure_eq _ _ sorry _ sorry]
    simp [DFunLike.coe]
    rw [Finset.prod_eq_single]
    -- on_goal 2 => exact ⟨(⟨({s} : M.Path).extend ⟨s', h⟩, by simp⟩ : {π : M.Path // π[0] = s}), by simp⟩
    on_goal 2 => exact ⟨(⟨({s} : M.Path), by simp⟩ : {π : M.Path // π[0] = s}), by simp⟩
    · simp
      rw [tsum_eq_single ⟨s', by simp⟩]
      simp
    · simp
      intro h'

      rw [tsum_eq_single ⟨s', by simp [h']⟩]
      · simp
      · simp
    · simp
  · sorry

noncomputable instance : IsProbabilityMeasure (Path.piMeasure (M:=M) s) :=
  Measure.instIsProbabilityMeasureForallInfinitePi _

-- noncomputable instance : CountablySeparated ({ π : M.Path // π[0] = s } → State) := by
--   apply?
--   sorry
-- noncomputable instance : StandardBorelSpace (ℕ → M.Path) := sorry

noncomputable def re (f : { π : M.Path // π[0] = s } → State) : ℕ → M.Path
  | 0 => {s}
  | n+1 => (re f n).extend ⟨f ⟨(re f n), sorry⟩, sorry⟩

@[simp]
theorem re_length {f : { π : M.Path // π[0] = s } → State} : ‖re f n‖ = n + 1 := by
  induction n with
  | zero => simp [re]
  | succ => simp_all [re]

noncomputable def re' (f : { π : M.Path // π[0] = s } → State) (n : ℕ) : State := (re f n).last

noncomputable instance : IsProbabilityMeasure (Idk.piMeasure' (M:=M) s) := by
  simp [Idk.piMeasure']
  refine MeasurableEmbedding.isProbabilityMeasure_comap ?_ ?_
  · apply MeasurableEmbedding.of_measurable_inverse (g:=re')
    · sorry
    · refine MeasurableSet.of_mem_measurableCylinders ?_
      simp
      use {⟨{s}, by simp⟩}
      -- let m := Set.pi {⟨s, by simp⟩} (fun (s' : ({s} : Set State)) ↦ M.succs_univ s')
      use Set.pi {⟨⟨{s}, by simp⟩, by simp⟩} (fun _ ↦ M.succs_univ s)
      simp
      constructor
      · refine MeasurableSet.of_mem_measurableCylinders ?_
        simp
        sorry
      · ext f
        simp
        constructor
        · sorry
        · sorry
    · refine measurable_pi_lambda re' ?_
      intro n
      simp [re', re]
      refine measurable_generateFrom ?_
      simp
      sorry
    · intro f
      simp
      funext n
      induction n with
      | zero =>
        simp [re', re]
      | succ n ih =>
        simp [re', re] at ih ⊢
  · simp
    sorry


noncomputable def Idk.piMeasure (s : State) : Measure ((i : ℕ) → Path[M,s,=i + 1]) :=
  Measure.infinitePi (Idk.succsMeasure (M:=M) s)

noncomputable instance : IsProbabilityMeasure (Idk.piMeasure (M:=M) s) :=
  Measure.instIsProbabilityMeasureForallInfinitePi _

noncomputable def Path'.piMeasure (s : State) : Measure {π : M.Path' // π.states 0 = s} :=
    (Idk.piMeasure (M:=M) s).comap fun ⟨π, h⟩ n ↦ ⟨π.take n, by simp_all⟩

noncomputable def Idk.piMeasure' (s : State) : Measure (ℕ → M.Path) :=
    (Idk.piMeasure (M:=M) s).map fun a n ↦ (a n).val

noncomputable def Idk.piMeasure'' (s : State) : Measure (ℕ → State) :=
    (Idk.piMeasure (M:=M) s).map fun a n ↦ (a n).val.last

noncomputable instance : IsProbabilityMeasure (Idk.piMeasure'' (M:=M) s) := by
  simp [Idk.piMeasure'']
  apply MeasureTheory.Measure.isProbabilityMeasure_map
  apply aemeasurable_pi_lambda
  intro n
  apply?

noncomputable instance : IsProbabilityMeasure (Path'.piMeasure (M:=M) s) := by
  apply MeasureTheory.isProbabilityMeasure_comap
  · intro ⟨π₁, h₁⟩ ⟨π₂, h₂⟩ h
    simp_all
    apply (Path'.eq_iff _ _).mpr
    ext i
    replace h := congrFun h i
    simp_all
    rw [Path.ext_iff] at h
    simp at h
    exact h i (by simp)
  · simp
    simp [Filter.Eventually, ae]
    have : {x | ∃ (a : M.Path'), ∃ (h : a.states 0 = s), (fun n ↦ (⟨a.take n, by simp [h]⟩ : Path[M,s,=n+1])) = x} = Set.univ := by
      ext π
      simp
      sorry
      -- have := π.Cyl
    -- apply?
    refine (ae_iff_measure_eq ?_).mpr ?_
    · sorry
    · simp [Idk.piMeasure]
      sorry
  · simp
    sorry

  -- refine aemeasurable_pi_iff.mpr ?_
  -- intro n
  -- simp [Idk.piMeasure]
  -- refine Measurable.aemeasurable ?_
  -- refine measurable_generateFrom ?_
  -- simp
  -- refine Measurable.aemeasurable ?_
  -- intro s hs
  -- refine MeasurableSet.of_mem_measurableCylinders ?_
  -- simp

end Measure

/-- The cylinder set spanning from a finite path -/
def Path.Cyl (π : M.Path) : Set M.Path' := {π' | π ∈ π'.pref}

def isValidPath {n : ℕ} (f : Fin n → State) : Prop :=
    ∀ i, (h : i + 1 < n) → (f ⟨i + 1, by omega⟩) ∈ M.succs_univ (f ⟨i, by omega⟩)

theorem Cyl_eq_cylinder (π : M.Path) :
    -- (·.states) '' π.Cyl = MeasureTheory.cylinder (Finset.range ‖π‖) {π' | M.isValidPath (n:=‖π‖) fun i ↦ π' ⟨i, by simp_all⟩} := by
    (·.states) '' π.Cyl = MeasureTheory.cylinder (Finset.range ‖π‖) {π' | (∀ i, (h : i < ‖π‖) → π' ⟨i, by simp_all⟩ = π[i]) ∧ M.isValidPath (n:=‖π‖) fun i ↦ π' ⟨i, by simp_all⟩} := by
  ext π'
  simp [Path.Cyl]
  constructor
  · simp
    rintro π' h ⟨_⟩
    obtain ⟨n, _, _⟩ := h
    simp_all only [Path.mk_getElem, List.getElem_ofFn]
    simp [isValidPath]
  · intro h
    use ⟨π', by simp_all [isValidPath]; grind⟩
    use π.infinite
    simp

theorem Cyl_eq_cylinder' :
    -- (·.states) '' π.Cyl = MeasureTheory.cylinder (Finset.range ‖π‖) {π' | M.isValidPath (n:=‖π‖) fun i ↦ π' ⟨i, by simp_all⟩} := by
    {(·.states) '' π.Cyl | π : M.Path} = MeasureTheory.measurableCylinders (α:=fun (x : ℕ) ↦ State) := by
  ext S
  simp [Path.Cyl]
  constructor
  · simp
    rintro π ⟨_⟩
    use Finset.range ‖π‖
    apply Exists.intro Set.univ
    constructor
    · exact MeasurableSet.univ
    · ext π'
      simp
      unfold Finset.restrict
      constructor
      · simp
      · intro h

        simp
    obtain ⟨n, _, _⟩ := h
    simp_all only [Path.mk_getElem, List.getElem_ofFn]
    simp [isValidPath]
  · intro h
    use ⟨π', by simp_all [isValidPath]; grind⟩
    use π.infinite
    simp


@[simp]
def Path.Cyl_ne_empty (π : M.Path) : π.Cyl ≠ ∅ := by
  refine Set.nonempty_iff_ne_empty'.mp ?_
  sorry

/-- The set of cylinder sets spanned from finite paths starting in `s` -/
def Cyl (s : State) (𝒮 : M.Scheduler) : Set (Set M.Path') :=
  (fun π ↦ π.Cyl) '' {π : M.Path | π[0] = s ∧ π.Prob 𝒮 ≠ 0}

instance (s : State) (𝒮 : M.Scheduler) : MeasurableSpace M.Path' := generateFrom (M.Cyl s 𝒮)
instance (π : M.Path) : MeasurableSpace π.Cyl := sorry

example (s : State) : Set (Set ((i : M.Path) → i.Cyl)) :=
  MeasureTheory.measurableCylinders (ι:=M.Path) fun a ↦ a.Cyl

attribute [-simp] List.ofFn_succ

theorem asdsa (n : ℕ) : @Set.univ M.Path' = ⋃ y : M.Path, ⋃ (_ : ‖y‖ = n + 1), y.Cyl := by
  induction n with
  | zero =>
    ext x
    simp
    use x.take 0
    simp [Path'.take, Path.Cyl, Path'.pref]
    use 0
    simp
  | succ n ih =>
    simp_all; clear ih
    ext π
    simp
    constructor
    · simp
      intro π' h h'
      use π.take (n + 1)
      simp only [Path'.take, Path.mk_length, List.length_ofFn, Path.Cyl, Path'.pref,
        Set.mem_setOf_eq, Path.mk.injEq, exists_apply_eq_apply, and_self]
    · simp
      intro π' h h'
      use π.take n
      simp only [Path'.take, Path.mk_length, List.length_ofFn, Path.Cyl, Path'.pref,
        Set.mem_setOf_eq, Path.mk.injEq, exists_apply_eq_apply, and_self]

theorem Path'.univ_eq_Cyl : {π : M.Path' | π.states 0 = s} = Path.Cyl {s} := by
  ext π
  simp [Path.Cyl, Path'.pref]
  constructor
  · rintro ⟨_⟩
    use 0
    ext <;> simp
  · simp
    rintro n h
    obtain ⟨π, prop⟩ := π
    simp_all
    simp [Path.eq_iff, Path.instSingleton] at h
    have : (List.ofFn fun x ↦ π ↑x)[0]'(by rw [h]; simp) = s := by grind
    grind

-- theorem Cyl_eq_succ_Cyl (π : M.Path) : π.Cyl =  := by
theorem Cyl_eq_succ_Cyl (π : M.Path) : π.Cyl = ⋃ π' ∈ π.succs_univ, {π''.prepend ⟨π[0], by simp; sorry⟩ | π'' ∈ π'.Cyl} := by
  ext π'
  simp
  constructor
  · intro h
    use π.extend ⟨π'.states (‖π‖ + 1), by
      have := π'.property ‖π‖
      convert this
      sorry
      ⟩
    constructor
    · sorry
    · sorry
  · sorry

-- def SigmaAlgebra' (s : State) : Set (Set M.Path') := GenerateMeasurable (M.Cyl s)
-- def SigmaAlgebra (s : State) : MeasurableSpace M.Path' := generateFrom (M.Cyl s)

-- theorem isSetRing_SigmaAlgebra {s : State} : IsSetRing (SigmaAlgebra' (M:=M) s) :=
--   ⟨GenerateMeasurable.empty, fun _ _ ↦ GenerateMeasurable.union, fun _ _ ↦ GenerateMeasurable.diff⟩
-- theorem isSetSemiring_SigmaAlgebra {s : State} : IsSetSemiring (SigmaAlgebra' (M:=M) s) :=
--   IsSetRing.isSetSemiring isSetRing_SigmaAlgebra

-- -- open scoped Classical in
-- -- noncomputable def Cyl.AddContent (s : State) (𝒮 : M.Scheduler) : AddContent (M.Cyl s) where
-- --   toFun πs := ∑' π : M.Path, if π.Cyl = πs then π.Prob 𝒮 else 0
-- --   empty' := by simp
-- --   sUnion' I hI hI_disjoint hI_union := by
-- --     simp
-- --     sorry

-- -- noncomputable def addContent (s : State) (𝒮 : M.Scheduler) : AddContent (M.SigmaAlgebra' s) := by
-- --   apply IsSetRing.addContent_of_union ?_ isSetRing_SigmaAlgebra ?_ ?_
-- --   · exact fun πs ↦
-- --       -- if h : πs ∈ SigmaAlgebra' s then

-- --       --   sorry
-- --       -- else
-- --       --   sorry
-- --       ∑' π : M.Path, if π.Cyl = πs then π.Prob 𝒮 else 0
-- --   · simp
-- --   · intro I J hI hJ hIJ

-- --     sorry

-- -- open scoped Classical in
-- -- noncomputable def addContent (s : State) (𝒮 : M.Scheduler) : AddContent (M.SigmaAlgebra' s) where
-- --   toFun πs := ∑' π : M.Path, if π.Cyl = πs then π.Prob 𝒮 else 0
-- --   empty' := by simp
-- --   sUnion' I hI hI_disjoint hI_union := by

-- --     rw [@Set.sUnion_eq_iUnion]
-- --     simp only [Finset.coe_sort_coe, ← Finset.tsum_subtype]
-- --     rw [ENNReal.tsum_comm]
-- --     apply tsum_eq_tsum_of_ne_zero_bij fun ⟨x, h⟩ ↦ x
-- --     · simp
-- --     · simp
-- --       simp_all
-- --       intro π h h'
-- --       sorry
-- --     · simp
-- --       intro π hπ h'
-- --       split_ifs
-- --       · rw [tsum_eq_single ⟨π.Cyl, hπ⟩]
-- --         · simp_all
-- --         · simp_all
-- --           grind
-- --       · symm
-- --         simp_all
-- --         grind

-- theorem addContent_apply {s : State} {𝒮 : M.Scheduler} (πs : Set M.Path') :
--     addContent s 𝒮 πs = ∑' π : πs, π.val.Prob 𝒮 := rfl

-- theorem addContent_IsSigmaSubadditive {s : State} {𝒮 : M.Scheduler} :
--     (addContent s 𝒮).IsSigmaSubadditive := by
--   refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum isSetRing_SigmaAlgebra ?_
--   simp [addContent_apply]
--   intro f hf hf_union hf_disjoint
--   rw [ENNReal.tsum_biUnion'']
--   exact fun _ _ _ _ a ↦ hf_disjoint a

-- instance MS (s : State) (𝒮 : M.Scheduler) : MeasurableSpace M.Path' :=
--     (inducedOuterMeasure
--       (fun x _ ↦ addContent s 𝒮 x)
--       (isSetSemiring_SigmaAlgebra (s:=s)).empty_mem
--       addContent_empty).caratheodory

-- noncomputable def measure (s : State) (𝒮 : M.Scheduler) : Measure[MS s 𝒮] M.Path' :=
--   (addContent s 𝒮).measureCaratheodory isSetSemiring_SigmaAlgebra addContent_IsSigmaSubadditive

-- theorem measure_apply {s : State} {𝒮 : M.Scheduler} (πs : Set M.Path')
--     (hπs : GenerateMeasurable (Cyl s) πs) : measure s 𝒮 πs = ∑' π : πs, π.val.Prob 𝒮 := by
--   simp [measure]
--   rw [AddContent.measureCaratheodory_eq _ _ _ hπs]
--   rw [addContent_apply]

-- -- example {s s' : State} {𝒮 : M.Scheduler} : measure s 𝒮 ({s'} : M.Path).Cyl = ⊤ := by
-- --   simp [measure]
-- --   rw [AddContent.measureCaratheodory_eq_inducedOuterMeasure]
-- --   rw [inducedOuterMeasure_eq_extend]
-- --   -- rw [MeasureTheory.measure_eq_zero_iff_ae_notMem]
-- --   -- apply?

-- theorem measure_IsProb {s : State} {𝒮 : M.Scheduler} : MeasureTheory.IsZeroOrProbabilityMeasure (measure s 𝒮) := by
--   refine isZeroOrProbabilityMeasure_iff.mpr ?_
--   rw [measure_apply _ GenerateMeasurable.univ]
--   simp
--   -- refine isProbabilityMeasure_iff.mpr ?_
--   -- sorry
--   -- simp
--   -- rw [ENNReal.tsum_biUnion'']
--   -- · simp
--   --   rw [tsum_eq_single {s}]
--   --   · rw [← addContent_apply]
--   --     simp
--   --     rw [addContent_apply]
--   --     have : ⨆ n, ∑' (π : ↑Path[M,s,=n + 1]), Path.Prob 𝒮 ↑π = 1 := by simp
--   --     convert this
--   --     apply le_antisymm
--   --     · apply le_iSup_of_le 0
--   --       simp
--   --       sorry
--   --     · apply iSup_le fun n ↦ ?_
--   --       simp
--   --       sorry
--   --   · simp [Path.Cyl, Path'.pref]
--   --     rintro ⟨xs, h₁, h₂⟩ h
--   --     simp_all
--   --     contrapose! h
--   --     congr
--   --     simp_all
--   --     obtain ⟨_, _, ⟨_, _, _⟩, _⟩ := h
--   --     simp_all [Path'.prop_first]
--   -- · intro s hs t ht hst Z hs' ht' x hx
--   --   simp_all
--   --   obtain ⟨s, hs₀, hs₁⟩ := s
--   --   obtain ⟨t, ht₀, ht₁⟩ := t
--   --   simp_all [Path.Cyl, Path'.pref]
--   --   specialize hs' hx
--   --   specialize ht' hx
--   --   simp_all
--   --   obtain ⟨hs', sn, hsn⟩ := hs'
--   --   obtain ⟨ht', tn, htn⟩ := ht'
--   --   subst_eqs
--   --   simp_all

end MDP
