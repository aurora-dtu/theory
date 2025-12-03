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

noncomputable def piMeasure := Measure.infinitePi M.succsMeasure
noncomputable def Path.piMeasure := Measure.infinitePi (Path.succsMeasure (M:=M))
noncomputable def Idk.piMeasure (s : State) := Measure.infinitePi (Idk.succsMeasure (M:=M) s)

noncomputable instance : IsProbabilityMeasure (Idk.piMeasure (M:=M) s) :=
  Measure.instIsProbabilityMeasureForallInfinitePi _

noncomputable def Path'.piMeasure (s : State) : Measure {π : M.Path' // π.states 0 = s} :=
    (Idk.piMeasure (M:=M) s).comap fun ⟨π, h⟩ n ↦ ⟨π.take n, by simp_all⟩

noncomputable def Idk.piMeasure' (s : State) : Measure (ℕ → M.Path) :=
    (Idk.piMeasure (M:=M) s).map fun a n ↦ (a n).val

noncomputable instance {π : M.Path} : Inhabited ↑(M.succs_univ π.last) where
  default := Classical.choice M.instNonemptySuccsUniv

noncomputable def Path.extendArb (π : M.Path) (n : ℕ) : M.Path :=
  match n with
  | 0 => π
  | n + 1 => (π.extend default).extendArb n

@[grind, simp]
theorem Path.extendArb_length {π : M.Path} {n : ℕ} : ‖π.extendArb n‖ = ‖π‖ + n := by
  fun_induction extendArb with
  | case1 => rfl
  | case2 => simp_all only [extend_length, Nat.succ_eq_add_one]; omega

noncomputable def Path.setLength (π : M.Path) (n : ℕ) : M.Path :=
  if n ≤ ‖π‖ then π.take (n - 1) else π.extendArb (n - ‖π‖)

@[grind, simp]
theorem Path.setLength_length {π : M.Path} {n : ℕ} (h : n ≠ 0) : ‖π.setLength n‖ = n := by
  grind [setLength]

noncomputable def Path.continue (π : M.Path) : M.Path' :=
  {
    states n := (π.setLength (n + 1))[n]'(by grind)
    property := sorry
  }

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
