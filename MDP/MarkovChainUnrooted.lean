import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.Stream.Init
import Mathlib.Probability.ProbabilityMassFunction.Monad

open MeasureTheory

attribute [grind =] List.take_append_getElem
attribute [grind =] List.take_left'
attribute [simp, grind =] Stream'.get

structure MarkovChain (State : Type*) where
  P : State → PMF State

namespace MarkovChain

variable {State : Type*} {M : MarkovChain State}

@[grind]
structure Path (M : MarkovChain State) where
  states : List State
  length_pos : states.length ≠ 0 := by grind
  nonempty : states ≠ [] := List.length_eq_zero_iff.not.mp length_pos
  property : ∀ i, (h : i + 1 < states.length) → M.P states[i] states[i + 1] ≠ 0 := by grind
deriving DecidableEq

@[grind] instance [Inhabited State] : Inhabited M.Path := ⟨{states := [default]}⟩

attribute [grind ., simp] Path.nonempty
attribute [grind ., simp] Path.length_pos

abbrev Path.length (π : M.Path) := List.length π.states

scoped notation "‖" a "‖" => Path.length a

@[grind =, simp]
theorem Path.states_length_eq_length {π : M.Path} : List.length π.states = ‖π‖ := by rfl

@[simp]
theorem Path.mk_length {states : List State} {length_pos nonempty property} :
    ‖({states, length_pos, nonempty, property} : M.Path)‖ = states.length := rfl

attribute [grind =] List.length_eq_zero_iff

@[grind]
structure Path' (M : MarkovChain State) where
  states : Stream' State
  -- initial : states 0 = ι
  property : ∀ i, M.P (states i) (states (i + 1)) ≠ 0

attribute [grind ., simp] Path'.property
-- attribute [grind ., simp] Path'.initial

@[grind]
instance : GetElem M.Path ℕ State (fun π n ↦ n < ‖π‖) where
  getElem π i h := π.states[i]
@[grind]
instance : GetElem M.Path' ℕ State (fun _ _ ↦ true) where
  getElem π i _ := π.states i

def Path.eq_iff {a b : M.Path} : a = b ↔ a.states = b.states := by
  grind [List.ext_getElem]

@[ext]
def Path.ext {a b : M.Path} (h₀ : ‖a‖ = ‖b‖)
    (h : ∀ i, (ha : i < ‖a‖) → (hb : i < ‖b‖) → a.states[i] = b.states[i]) :
    a = b := by
  grind [List.ext_getElem]
@[ext]
def Path'.ext {a b : M.Path'} (h : a.states = b.states) : a = b := by
  grind

@[grind =, simp]
theorem Path.mk_getElem {states : List State} {length_pos nonempty property}
    (i : ℕ) (hi : i < states.length) :
    ({states, length_pos, nonempty, property} : M.Path)[i] = states[i] := rfl

theorem Path.length_eq_of_eq {a b : M.Path} (h : a = b) : ‖a‖ = ‖b‖ := by
  grind

noncomputable def measure [MeasurableSpace State] (M : MarkovChain State) (s : State) :
    Measure State := (M.P s).toMeasure
instance [MeasurableSpace State] : IsProbabilityMeasure (M.measure s) :=
  PMF.toMeasure.isProbabilityMeasure _

@[grind]
def Path.take (π : M.Path) (i : Fin ‖π‖) : M.Path := { states := π.states.take (i + 1) }
def Path.take_inj (π : M.Path) : Function.Injective π.take := by intro i j hi; grind [take]

@[grind =, simp]
theorem Path.take_length {π : M.Path} (i : Fin ‖π‖) :
    ‖π.take i‖ = i + 1 := by grind [Path.take]

@[grind]
def Path'.take (π' : M.Path') (n : ℕ) : M.Path := {
  states := π'.states.take (n + 1)
  length_pos := by simp
  property := by simp [Stream'.get]
}
@[grind =, simp]
theorem Path'.take_length {π : M.Path'} (i : ℕ) :
    ‖π.take i‖ = i + 1 := by simp [Path'.take]

theorem Path'.ext_tail {π₁ π₂ : M.Path'} (h : ∀ i, π₁.take i = π₂.take i) : π₁ = π₂ := by
  ext n
  specialize h n
  simp_all [take]
  simp [List.ext_get_iff] at h
  grind

def Path.pref (π : M.Path) : Finset M.Path := Finset.univ.map ⟨π.take, π.take_inj⟩

@[simp]
theorem Path.mem_pref {π : M.Path} :
    π' ∈ π.pref ↔ ∃ i, π' = π.take i := by
  simp [pref]; grind

@[grind ., simp]
theorem Path.take_mem_pref {π : M.Path} {i} (hi) : π.take ⟨i, hi⟩ ∈ π.pref := by
  simp [take, pref]
  use ⟨i, by grind⟩
  simp [hi]

@[grind ., simp]
theorem Path'.take_take {π : M.Path'} {i} (hi) : (π.take j).take ⟨i, hi⟩ = π.take i := by
  ext
  · simp
  · simp [Path.take, Path'.take]

def Path'.pref (π' : M.Path') : Set M.Path := Set.range π'.take
def Path.Cyl (π : M.Path) : Set M.Path' := {π' | π ∈ π'.pref}

@[simp]
theorem Path'.mem_pref {π : M.Path'} :
    π' ∈ π.pref ↔ ∃ i, π' = π.take i := by
  simp [pref]; grind

abbrev PathFrom (M : MarkovChain State) (ι : State) : Set M.Path := {π | π[0]'(by grind) = ι}
-- def PathFrom.succs (π : M.PathFrom ι) : Set (M.PathFrom ι) :=
--   {⟨π'.val, by obtain ⟨π', h⟩ := π'; simp_all; sorry⟩ | π' : π.val.succs}

@[simp]
instance Path'.Ω (ι : State) : MeasurableSpace M.Path' :=
    MeasurableSpace.generateFrom (Path.Cyl '' M.PathFrom ι)

noncomputable def Path.succs (π : M.Path) : Set M.Path :=
    {π' | ‖π'‖ = ‖π‖ + 1 ∧ π'.states.take ‖π‖ = π.states}

@[grind =, grind ., simp]
theorem Path.succs_length {π : M.Path} (π' : π.succs) : ‖π'.val‖ = ‖π‖ + 1 := by
  grind [succs]
@[grind ., simp]
theorem Path.succs_length' {π π' : M.Path} (hπ' : π' ∈ π.succs) : ‖π'‖ = ‖π‖ + 1 := by
  grind [succs]
@[grind =, simp]
theorem Path.succs_getElem {π : M.Path} (π' : π.succs) (i : ℕ) (h : i < ‖π‖) :
    π'.val[i]'(by simp; grind) = π[i] := by
  grind [succs]
@[grind =, simp]
theorem Path.succs_states_getElem {π : M.Path} (π' : π.succs) (i : ℕ) (h : i < ‖π‖) :
    π'.val.states[i]'(by simp; grind) = π[i] := by
  grind [succs]
@[grind ., simp]
theorem Path.succs_states_getElem' {π π' : M.Path} (hπ' : π' ∈ π.succs) (i : ℕ) (h : i < ‖π‖) :
    π'.states[i]'(by simp; grind) = π[i] := by
  grind [succs]

/-- NOTE: this is the dependent version of `pmf'` -/
noncomputable def Path.pmf (π : M.Path) : PMF π.succs :=
  (M.P (π.states[‖π‖ - 1]'(by grind))).bindOnSupport
    (fun s hs ↦
      PMF.pure
        ⟨⟨π.states ++ [s],
            by simp, by simp, by grind [PMF.mem_support_iff]⟩, by simp [succs]⟩)
noncomputable def Path.pmf' (π : M.Path) : PMF M.Path :=
  (M.P (π.states[‖π‖ - 1]'(by grind))).bindOnSupport
    (fun s hs ↦
      PMF.pure
        ⟨π.states ++ [s], by simp, by simp, by grind [PMF.mem_support_iff]⟩)

theorem Path.pmf_apply {π : M.Path} {π' : π.succs} : π.pmf π' = π.pmf' π'.val := by
  simp [pmf, pmf']
  congr!
  grind only

variable [DecidableEq State] in
theorem Path.pmf'_apply {π : M.Path} {π' : M.Path} :
      π.pmf' π'
    = if h : π'.states.take ‖π‖ = π.states ∧ ‖π'‖ = ‖π‖ + 1 then
        M.P (π'.states[‖π'‖ - 2]'(by grind)) (π'.states[‖π'‖ - 1]'(by grind))
      else
        0 := by
  simp [pmf']
  split_ifs with h
  · obtain ⟨h, h'⟩ := h
    have : π = π'.take ⟨‖π'‖ - 2, by grind⟩ := by grind [take]
    simp [this, take, eq_iff]
    have h₁ : ‖π'‖ - 2 + 1 = ‖π'‖ - 1 := by grind
    have h₂ : ‖π‖ = ‖π'‖ - 1 := by grind
    simp [h₁]
    rw [tsum_eq_single (π'.states[‖π'‖ - 1]'(by grind))]
    · grind
    · simp; grind
  · simp_all; grind

@[implicit_reducible]
def Path.ofLength_countable [Countable State] (n : ℕ) : Countable {π : M.Path | ‖π‖ = n} := by
  rcases n with _ | n
  · simp
  induction n with
  | zero =>
    -- have : State ≃ { π : M.Path | ‖π‖ = 1 } := by
    apply Countable.of_equiv State
    refine (Equiv.ofBijective (fun s ↦ ⟨⟨[s], by grind, by grind, by grind⟩, by simp⟩) ?_)
    constructor
    · intro; grind
    · rintro ⟨π, _⟩; simp_all; simp_all; use π[0]; ext <;> simp <;> grind
  | succ n ih =>
    have : Countable {π : M.Path // ‖π‖ = n + 1} := by simp_all
    have :
          {π : M.Path | ‖π‖ = n + 1 + 1}
        = ⋃ π : {π : M.Path // ‖π‖ = n + 1}, π.val.succs := by
      ext π
      simp
      constructor
      · intro h
        use π.take ⟨n, by omega⟩
        grind [Path.succs, Path.take]
      · simp
        intro π' h h'
        have := π'.succs_length ⟨π, h'⟩
        grind
    rw [this]
    simp
    intro π h
    have := (M.P (π.states[‖π‖ - 1]'(by grind))).support_countable
    let equiv : π.succs ≃ (M.P (π.states[‖π‖ - 1]'(by grind))).support :=
      Set.BijOn.equiv (fun π' ↦ π'[‖π'‖ - 1]'(by grind)) ?_
    · have := Equiv.countable_iff equiv.symm
      simp_all
    · simp_all only [Set.coe_setOf, add_tsub_cancel_right]
      constructor
      · intro; grind [succs, PMF.mem_support_iff]
      · constructor
        · intro a ha b hb h
          simp_all [Path.succs, Path.eq_iff]
          ext i s
          have := congrArg (GetElem?.getElem? · i) (ha.right.trans hb.right.symm)
          grind
        · intro s h'
          simp [Path.succs]
          simp at h'
          use {states:=π.states ++ [s]}
          simp

theorem Path.complete : ⋃ n, {π : M.Path | ‖π‖ = n} = Set.univ := by ext; simp

instance [Countable State] : Countable M.Path := by
  have : Countable (Set.univ : Set M.Path) := by
    rw [← Path.complete]; simp
    exact Path.ofLength_countable
  exact Set.countable_univ_iff.mp this
@[simp]
instance : MeasurableSpace M.Path := MeasurableSpace.generateFrom Set.univ
instance : MeasurableSingletonClass M.Path := by
  constructor; exact fun _ ↦ MeasurableSpace.measurableSet_generateFrom trivial
instance : DiscreteMeasurableSpace M.Path := by
  constructor; exact fun s ↦ MeasurableSpace.measurableSet_generateFrom trivial

theorem Path.pmf_toMeasure_apply [Countable State] {π : M.Path} {S : Set π.succs} :
    π.pmf.toMeasure S = π.pmf'.toMeasure ((·.val) '' S) := by
  repeat rw [PMF.toMeasure_apply _ (by measurability)]
  simp [Set.indicator, Path.pmf_apply]
  symm
  apply tsum_eq_tsum_of_ne_zero_bij fun ⟨x, hx⟩ ↦ x.val
  · intro; grind
  · intro; simp
  · grind

variable [DecidableEq State] in
@[grind =, simp]
theorem Path.pmf'_toMeasure_apply {π : M.Path} {S : Set M.Path} [∀ π' , Decidable (π' ∈ S)] :
      π.pmf'.toMeasure S
    = ∑' π' : M.Path,
        if h : List.take ‖π‖ π'.states = π.states ∧ ‖π'‖ = ‖π‖ + 1 then
          if π' ∈ S then
            (M.P (π'.states[‖π'‖ - 2]'(by grind))) (π'.states[‖π'‖ - 1]'(by grind))
          else 0
        else 0 := by
  repeat rw [PMF.toMeasure_apply _ (by measurability)]
  simp [Set.indicator]
  congr with π'
  rw [pmf'_apply]
  grind

noncomputable def Path.measure (π : M.Path) : Measure π.succs := π.pmf.toMeasure
instance {π : M.Path} : IsProbabilityMeasure π.measure := PMF.toMeasure.isProbabilityMeasure _

noncomputable def Path.lifted : Measure ((π : M.Path) → π.succs) :=
  Measure.infinitePi Path.measure

instance : IsProbabilityMeasure (Path.lifted (M:=M)) :=
  Measure.instIsProbabilityMeasureForallInfinitePi _

noncomputable instance {π : M.Path} : Inhabited π.succs :=
  let h := (M.P (π.states.getLast π.nonempty)).support_nonempty
  let s' := h.choose
  let hs' : s' ∈ (M.P (π.states.getLast π.nonempty)).support := h.choose_spec
  ⟨⟨{states := π.states ++ [s'], property := by simp at hs'; grind}, by simp [Path.succs]⟩⟩

@[grind]
noncomputable def embed.help (ι : State) (f : (π : M.Path) → π.succs) :
    ℕ → M.PathFrom ι
  | 0 => ⟨⟨[ι], by grind, by grind, by grind⟩, by simp⟩
  | n + 1 => ⟨f (help ι f n), by simp; grind⟩
theorem embed.help_eq (f : (π : M.Path) → π.succs) :
    embed.help ι f n = (f ·)^[n] ⟨[ι], by grind, by grind, by grind⟩ := by
  fun_induction help with simp_all [-Function.iterate_succ, Function.iterate_succ'] <;> grind
theorem embed.help_eq' (f : (π : M.Path) → π.succs) :
    embed.help ι f = fun n ↦ ⟨(f ·)^[n] ⟨[ι], by grind, by grind, by grind⟩, by simp [← embed.help_eq]⟩ := by
  ext
  · simp [embed.help_eq]
  · simp [embed.help_eq]

theorem embed.help_eq'' (f : M.Path → M.Path) (hf : ∀ π, f π ∈ π.succs) :
    embed.help ι (fun π ↦ ⟨f π, hf π⟩) = fun n ↦ ⟨f^[n] ⟨[ι], by grind, by grind, by grind⟩, by simp [← embed.help_eq]⟩ := by
  ext
  · simp [embed.help_eq]
  · simp [embed.help_eq]

@[grind =, simp]
theorem embed.help_length : ‖(embed.help (M:=M) ι f n).val‖ = n + 1 := by
  fun_induction help with try grind
@[grind =, simp]
theorem embed.help_getElem (i : ℕ) (h : i < n + 1) :
    (embed.help (M:=M) ι f n).val[i]'(by simp_all) = (embed.help (M:=M) ι f i).val[i] := by
  fun_induction help ι f n with try grind
@[grind =, simp]
theorem embed.help_states_getElem (i : ℕ) (h : i < n + 1) :
    (embed.help (M:=M) ι f n).val.states[i]'(by grind) = (embed.help (M:=M) ι f i).val.states[i]
  := embed.help_getElem _ h
noncomputable def embed (ι : State) (f : (π : M.Path) → π.succs) : M.Path' :=
  ⟨fun n ↦ (embed.help ι f n).val[n], by
    simp [embed.help]
    intro i
    have : (f (embed.help ι f i)).val[i]'(by grind) = (embed.help ι f i).val[i] := by grind
    rw [← this]
    exact (f (embed.help ι f i)).val.property i (by simp)⟩

theorem embed_eq_iter :
    (embed (M:=M) ι f).states = fun i ↦ ((f ·)^[i] ⟨[ι], by grind, by grind, by grind⟩)[i]'(by sorry) := by
  ext i
  simp [embed, embed.help_eq']

open scoped Classical in
noncomputable def embedInv (ι : State) (π' : M.Path') : (π : M.Path) → π.succs :=
  if π'[0] = ι then
    fun π ↦ if h : π ∈ π'.pref then ⟨π'.take (‖π‖ ), by
      simp [Path'.pref] at h
      obtain ⟨i, ⟨_⟩⟩ := h
      simp [Path.succs, Path'.take]⟩ else default
  else
    default

theorem embed_left_inverse : Function.LeftInverse (embed (M:=M) ι) (embedInv ι) := by
  intro π
  apply Path'.ext_tail
  intro n
  induction n with
  | zero => sorry
  | succ n ih => sorry

theorem ashjdasd (S : Set ((π : M.Path) → ↑π.succs)) : (embedInv ι ⁻¹' S) = embed ι (M:=M) '' S := by
  apply?
  ext
  simp_all
  sorry

theorem embedInv_measurable : @Measurable _ _ (Path'.Ω ι) _ (embedInv (M:=M) ι) := by
  intro S h
  induction h with
  | empty | compl | iUnion => measurability
  | basic T h =>
    simp_all only [Set.sSup_eq_sUnion, Set.sUnion_image, Set.mem_range, Set.iUnion_exists,
      Set.iUnion_iUnion_eq', Set.mem_iUnion, Set.mem_setOf_eq]
    obtain ⟨π, U, h, ⟨_⟩⟩ := h
    constructor
    simp_all
    use π


def embedInv_embed : @MeasurableEmbedding _ _ (Path'.Ω ι) _ (embedInv ι (M:=M)) := by
  letI := Path'.Ω (M:=M) ι
  apply MeasurableEmbedding.of_measurable_inverse _ _ _ embed_left_inverse
  ·
    sorry
  · constructor
    simp
    use ⟨[ι], by simp, by simp, by simp⟩
    constructor
    swap
    · exact Set.univ
    simp
    ext
    simp [embedInv]

    sorry
  · refine measurable_generateFrom ?_
    simp
    intro π h
    constructor
    simp
    use π
    constructor
    swap
    · exact Set.univ
    · simp
      ext f
      simp [embedInv, Path.Cyl]
      use ‖π‖ - 1
      ext
      · simp; grind
      · simp [embed]
        sorry


  -- {
  --   injective := by
  --     intro π₁ π₂ h
  --     apply Path'.ext_tail
  --     intro n
  --     simp [funext_iff] at h
  --     induction n with
  --     | zero =>
  --       have := h (π₁.take 0)
  --       have := h (π₂.take 0)
  --       have : π₁.take 1 = π₂.take 1 → π₁.take 0 = π₂.take 0 := by
  --         sorry
  --       simp_all [embedInv]
  --       split_ifs at *
  --       · simp_all
  --       · simp_all
  --       · simp_all
  --       · simp_all

  --         sorry
  --     | succ n ih =>
  --       have := h (π₁.take n)
  --       have := h (π₂.take n)
  --       simp_all [embedInv]
  --       split_ifs at *
  --       · simp_all
  --       · simp_all
  --       · simp_all
  --       · simp_all
  --         grind
  --   measurable := by
  --     -- refine measurable_pi_lambda embedInv ?_
  --     intro S hS
  --     induction hS with
  --     | basic S hS =>
  --       constructor
  --       simp_all
  --       obtain ⟨π, hS⟩ := hS
  --       obtain ⟨T, hT, _, _⟩ := hS
  --       use π
  --       split_ands
  --       · sorry
  --       · ext π'
  --         simp [Path.Cyl]
  --         constructor
  --         · simp
  --           rintro i ⟨_⟩
  --           simp [embedInv]
  --           sorry
  --         · simp [embedInv]


  --           sorry
  --     | empty => measurability
  --     | compl => measurability
  --     | iUnion => measurability
  --     simp [embedInv]
  --     intro S hS
  --     obtain ⟨T, hT, hS'⟩ := hS
  --     subst_eqs
  --     induction hT with
  --     | basic S _ =>
  --       constructor
  --       simp
  --       use π
  --       split_ands
  --       · sorry
  --       · ext π'
  --         simp [Path.Cyl]
  --         constructor
  --         · simp
  --           rintro i ⟨_⟩
  --           simp
  --           sorry
  --         · split_ifs
  --           · simp
  --           · simp

  --           sorry
  --     | empty => measurability
  --     | compl => measurability
  --     | iUnion => measurability

  --     refine measurable_comap_iff.mpr ?_
  --     apply (MeasurableEmbedding.measurable_comp_iff _).mpr
  --     · intro S hS
  --       induction hS with
  --       | intro T hT =>
  --         simp_all
  --     · refine MeasurableEmbedding.subtype_coe ?_
  --       measurability
  --   measurableSet_image' := by
  --     simp
  -- }

def Path.theSet (π : M.Path) : Set ((i : ↥π.pref) → i.val.succs) :=
  {f | ∀ (π' : ↥π.pref), π'.val ≠ π → (f π').val ∈ π.pref}

theorem Path.mem_theSet {π : M.Path} {f : (i : ↥π.pref) → i.val.succs} :
  f ∈ π.theSet ↔ ∀ (π' : ↥π.pref), π'.val ≠ π → (f π').val ∈ π.pref := by rfl

@[measurability]
theorem Path.theSet_measurable [Countable State] (π : M.Path) : MeasurableSet π.theSet :=
  DiscreteMeasurableSpace.forall_measurableSet _

theorem Path.theSet_eq_pi (π : M.Path) :
      π.theSet
    = Set.univ.pi fun (π' : ↥π.pref) ↦ {π'' : π'.val.succs | ¬π'.val = π → π''.val ∈ π.pref} := by
  ext f
  simp [theSet]

theorem embed_take : (embed s f).take i = (embed s f).take (i + 1) := by
  simp [embed, Path'.take]
theorem f_take_embed : f ((embed s f).take i) = (embed s f).take (i + 1) := by
  simp [embed_eq_iter, Path'.take]
  sorry
  simp [embed, Path'.take]
  ext j ha hb
  · simp
  · simp [embed.help_eq']
    simp_all [embed.help_eq']
    induction j with
    | zero => simp [embed.help_eq']
    | succ j ih =>
      simp only [Function.iterate_succ', Function.comp_apply]
      congr
      · ext
        simp
        congr!
        simp
        simp [embed.help_eq']
      · apply List.ext_getElem
        · simp
          sorry
        · simp [Stream'.take_get]
    -- simp at ha hb
    -- simp_all [embed.help_eq']
    -- conv =>
    --   enter [1, 1, 1, 1]
    --   rw [embed.help_eq']
    --   skip
    -- rw [embed.help_eq]
    -- simp_all only

variable [Countable State]

theorem Path.Cyl_subset_cylinder (π : M.Path) (hs : π[0]'(by grind) = s) : embed s ⁻¹' π.Cyl ⊆ cylinder π.pref π.theSet := by
  intro f
  simp [mem_theSet, Cyl]
  intro n h' ⟨i, hi⟩ h
  subst h'
  simp [Path.take] at hi
  have : i < n := by
    contrapose! h
    have : i = n := by omega
    subst_eqs
    simp_all
  use ⟨i + 1, by grind⟩
  ext j hj₁ hj₂
  · grind
  · simp at hj₁ hj₂
    -- conv => left; simp [Path.take, Path'.take]
    simp_all only [take_length]
    replace :
        (f (((embed s f).take n).take ⟨i, by omega⟩)).val = (f ((embed s f).take i)).val := by
      grind
    simp [this]
    -- NOTE: this would be a nice proof
    have : f ((embed s f).take i) = (embed s f).take (i + 1) := by

      sorry
    simp [this]; simp [Path'.take]
    by_cases h' : j < i + 1
    · have :
            (f ((embed s f).take i)).val.states[j]'(by simp; omega)
          = ((embed s f).take i).states[j]'(by simp; grind) := by
        simp [embed, Path'.take, Stream'.get]
        rw [Path.succs_states_getElem]
        · simp only [GetElem.getElem]
          simp
        · simp; grind
      simp [this]
      simp [Path'.take]
    · have : i + 1 = j := by omega
      subst_eqs
      simp [embed, embed.help]
      simp [Path'.take]
      simp only [GetElem.getElem]
      simp
      congr! 7
      · apply List.ext_getElem
        · simp
        · simp_all [Stream'.get]
      · simp_all [Path.succs]
        apply List.ext_getElem
        · simp
        · simp_all [Stream'.get]


theorem Path.Cyl_eq_cylinder (π : M.Path) (hs : π ∈ M.PathFrom ι) : embed ι ⁻¹' π.Cyl = cylinder π.pref π.theSet := by
  ext f
  constructor
  · intro hf
    apply π.Cyl_subset_cylinder
    · rfl
    · grind
  · simp [Path.Cyl, Path'.pref]
    intro h
    use ‖π‖ - 1
    simp [Path'.take]
    ext i ha hb
    · simp; grind
    · simp only [mem_theSet, ne_eq, Finset.restrict, mem_pref, Subtype.forall, forall_exists_index,
      forall_eq_apply_imp_iff] at h
      simp_all only [Stream'.take_get, Stream'.get]
      simp_all only [mk_length, Stream'.length_take, Order.lt_add_one_iff]
      suffices (embed ι f).take i = π.take ⟨i, by omega⟩ by
        simp_all [Path.eq_iff]
        have : ((embed ι f).take i).states[i] = (π.take ⟨i, hb⟩).states[i] := by grind
        simp [Path'.take, Stream'.get] at this
        simp [this, Path.take]
      induction i with
      | zero =>
        simp [Path'.take, Path.take]
        sorry
        -- cbv
        -- grind only [usr Set.mem_setOf_eq, = mk_getElem, = List.getElem_cons, = List.take_zero]
      | succ i ih =>
        simp_all
        specialize h ⟨i, by omega⟩ (by intro h; replace := Path.length_eq_of_eq h; grind)
        obtain ⟨⟨j, hj⟩, h⟩ := h
        have : j = i + 1 := by have := Path.length_eq_of_eq h; simp at this; omega
        subst_eqs
        rw [← h]; clear h
        rw [← ih _ (by omega)]; clear ih
        simp [embed, Path'.take]
        ext j h₁ h₂
        · simp
        · simp_all
          if j = i + 1 then
            subst_eqs
            simp_all [embed.help]
            simp only [GetElem.getElem]
            sorry
            -- congr! 7
            -- · apply List.ext_getElem
            --   · simp
            --   · simp_all [Stream'.get]
            -- · apply List.ext_getElem
            --   · simp
            --   · simp_all [Stream'.get]
          else
            rw [Path.succs_states_getElem _ _ (by simp_all; omega)]
            simp_all [Stream'.get]

@[measurability]
theorem embed.measurable : Measurable[inferInstance, Path'.Ω ι] (embed ι (M:=M)) := by
  intro S hS
  induction hS with try measurability
  | basic T hT =>
    obtain ⟨π, ⟨_⟩⟩ := hT
    subst_eqs
    simp_all [PathFrom]
    subst_eqs
    rw [Path.Cyl_eq_cylinder _ (by rfl)]
    apply MeasurableSet.cylinder π.pref π.theSet_measurable

noncomputable def Pr (ι) : Measure[Path'.Ω ι] M.Path' :=
  @Measure.map _ _ _ (Path'.Ω ι) (embed ι (M:=M)) (Path.lifted (M:=M))

instance : IsProbabilityMeasure (Pr ι (M:=M)) := by
  simp [Pr]
  letI := Path'.Ω (M:=M) ι
  refine Measure.isProbabilityMeasure_map ?_
  measurability

@[measurability]
theorem Path.Cyl_measurable (π : M.Path) (h : π ∈ M.PathFrom ι) : MeasurableSet[Path'.Ω ι] π.Cyl :=
  MeasurableSpace.measurableSet_generateFrom (Set.mem_image_of_mem Cyl h)

open scoped Classical in
open Path in
theorem Pr_cyl_help (π : M.Path) :
      (∏ x ∈ π.pref.attach, if h : ↑x = π then 1 else x.val.pmf' (π.take ⟨‖x.val‖, by
        obtain ⟨x, hx⟩ := x
        simp [Path.pref] at hx
        grind only [take, = take_length, = List.take_length]⟩))
    = ∏ i : Fin (‖π‖ - 1), (M.P π.states[i.val]) (π.states[↑i + 1]'(by grind only)) := by
  symm
  apply Finset.prod_bij_ne_one
          fun i h h' ↦ ⟨π.take ⟨i, by omega⟩,
                        by simp [Path.take, Path.pref]; use ⟨i, by omega⟩; simp; omega⟩
  · grind only [← Finset.mem_attach]
  · grind only [take, = List.length_take, = min_def]
  · simp +contextual only [Finset.mem_attach, ne_eq, dite_eq_left_iff, not_forall, exists_prop,
    Finset.mem_univ, forall_exists_index, forall_const, Subtype.forall, mem_pref, Subtype.mk.injEq,
    take_length]
    rintro _ ⟨i, hi⟩ ⟨_⟩ h h'
    use ⟨i, by grind⟩
    contrapose h'
    simp only [take_length, pmf'_apply]
    grind
  · intro ⟨i, hi⟩ h
    grind only [take, = List.length_take, = List.take_add, = min_def, = List.getElem_append,
      pmf'_apply, = take_length, = List.take_take, = List.getElem_take]

-- theorem Path.theSet_measurable

open scoped Classical in
open Path in
theorem Pr_cyl (π : M.Path) (h : π ∈ M.PathFrom ι) :
    Pr ι π.Cyl = ∏ i : Fin (‖π‖ - 1), M.P π.states[i] (π.states[i.val + 1]'(by grind)) := by
  simp [Pr]
  rw [Measure.map_apply (by measurability) (by measurability)]
  simp [lifted, Path.Cyl_eq_cylinder, h]
  rw [Measure.infinitePi_cylinder _ (by apply Path.theSet_measurable), Path.theSet_eq_pi, Measure.pi_pi]
  simp only [Finset.univ_eq_attach, Path.measure, pmf_toMeasure_apply, pmf'_toMeasure_apply,
    Set.mem_image, Set.mem_setOf_eq, Subtype.exists, exists_and_left, exists_prop,
    exists_eq_right_right]
  simp_all only [succs, Set.mem_setOf_eq, and_self, and_true, Nat.reduceSubDiff,
    add_tsub_cancel_right]
  rw [← Pr_cyl_help]
  simp [Path.pmf'_apply]
  congr! 1 with ⟨x, hx⟩ hx'
  simp_all only [Finset.mem_attach]
  split_ifs with hx''
  · subst_eqs
    simp_all only [not_true_eq_false, IsEmpty.forall_iff, ↓reduceIte]
    rw [← π.pmf.tsum_coe]
    apply tsum_eq_tsum_of_ne_zero_bij fun ⟨x, _⟩ ↦ x
    · intro; grind
    · intro
      simp only [Function.mem_support, succs, Set.mem_range, Subtype.exists]
      grind [pmf_apply, pmf'_apply]
    · grind [succs, pmf_apply, pmf'_apply]
  · have : ‖x‖ < ‖π‖ := by grind
    rw [tsum_eq_single (π.take ⟨‖x‖, by grind⟩)]
    · grind [succs]
    · simp only [ne_eq, dite_eq_right_iff, ite_eq_right_iff, forall_and_index]
      grind
  · simp only [ENNReal.tsum_eq_zero, dite_eq_right_iff, ite_eq_right_iff, forall_and_index]
    grind

end MarkovChain
