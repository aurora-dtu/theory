import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.Stream.Init
import Mathlib.Probability.ProbabilityMassFunction.Monad

open MeasureTheory

structure MarkovChain (State : Type*) [MeasurableSpace State] where
  ι : State
  P : State → PMF State

namespace MarkovChain

variable {State : Type*} [MeasurableSpace State] {M : MarkovChain State}

@[grind]
structure Path (M : MarkovChain State) where
  states : List State
  length_pos : states.length ≠ 0 := by grind
  nonempty : states ≠ [] := List.length_eq_zero_iff.not.mp length_pos
  initial : states[0] = M.ι := by grind
  property : ∀ i, (h : i + 1 < states.length) → M.P states[i] states[i + 1] ≠ 0 := by grind

attribute [grind ., simp] Path.nonempty
attribute [grind ., simp] Path.length_pos
attribute [grind ., simp] Path.initial
attribute [grind ., simp] Path.property

abbrev Path.length (π : M.Path) := List.length π.states

scoped notation "‖" a "‖" => Path.length a

@[grind =, simp]
theorem Path.states_length_eq_length {π : M.Path} : List.length π.states = ‖π‖ := by rfl

@[grind ., grind <=, simp]
theorem Path.mk_length {states : List State} {length_pos nonempty initial property} :
    ‖({states, length_pos, nonempty, initial, property} : M.Path)‖ = states.length := rfl

attribute [grind =] List.length_eq_zero_iff

@[grind]
structure Path' (M : MarkovChain State) where
  states : Stream' State
  initial : states 0 = M.ι
  property : ∀ i, M.P (states i) (states (i + 1)) ≠ 0

attribute [grind ., simp] Path'.property
attribute [grind ., simp] Path'.initial

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
theorem Path.mk_getElem {states : List State} {length_pos nonempty initial property}
    (i : ℕ) (hi : i < states.length) :
    ({states, length_pos, nonempty, initial, property} : M.Path)[i] = states[i] := rfl

theorem Path.length_eq_of_eq {a b : M.Path} (h : a = b) : ‖a‖ = ‖b‖ := by
  grind

noncomputable def measure (M : MarkovChain State) (s : State) : Measure State :=
  (M.P s).toMeasure
instance : IsProbabilityMeasure (M.measure s) := PMF.toMeasure.isProbabilityMeasure _

-- noncomputable def kernel (M : MarkovChain State) : ProbabilityTheory.Kernel State State :=
--   ⟨M.measure, by sorry⟩

def Path.take (π : M.Path) (i : Fin ‖π‖) : M.Path := { states := π.states.take (i + 1) }
def Path.take_inj (π : M.Path) : Function.Injective π.take := by intro i j hi; grind [take]

@[grind =, simp]
theorem Path.take_length {π : M.Path} (i : Fin ‖π‖) :
    ‖π.take i‖ = i + 1 := by grind [Path.take]

def Path'.take (π' : M.Path') (n : ℕ) : M.Path := {
  states := π'.states.take (n + 1)
  length_pos := by simp
  initial := by simp [Stream'.get]
  property := by simp [Stream'.get]
}
@[grind =, simp]
theorem Path'.take_length {π : M.Path'} (i : ℕ) :
    ‖π.take i‖ = i + 1 := by simp [Path'.take]

def Path'.pref (π' : M.Path') : Set M.Path := Set.range π'.take
def Path.Cyl (π : M.Path) : Set M.Path' := {π' | π ∈ π'.pref}

@[simp]
instance : MeasurableSpace M.Path' := MeasurableSpace.generateFrom (Set.range Path.Cyl)

noncomputable def Path.succs (π : M.Path) : Set M.Path :=
    {π' | ‖π'‖ = ‖π‖ + 1 ∧ π'.states.take ‖π‖ = π.states}

@[grind =, grind ., simp]
theorem Path.succs_length {π : M.Path} (π' : π.succs) : ‖π'.val‖ = ‖π‖ + 1 := by
  grind [succs]
@[grind =, simp]
theorem Path.succs_getElem {π : M.Path} (π' : π.succs) (i : ℕ) (h : i < ‖π‖) :
    π'.val[i]'(by simp; grind) = π[i] := by
  grind [succs]
@[grind =, simp]
theorem Path.succs_states_getElem {π : M.Path} (π' : π.succs) (i : ℕ) (h : i < ‖π‖) :
    π'.val.states[i]'(by simp; grind) = π[i] := by
  grind [succs]

def Path.pmf.lift : (State → ENNReal) → M.Path → ENNReal :=
  fun f π' ↦ f (π'.states[‖π'‖ - 1]'(by grind))

noncomputable def Path.pmf (π : M.Path) : PMF π.succs :=
  (M.P (π.states[‖π‖ - 1]'(by grind))).bindOnSupport
    (fun s hs ↦
      PMF.pure
        ⟨⟨π.states ++ [s],
            by simp, by simp, by grind, by grind [PMF.mem_support_iff]⟩, by simp [succs]⟩)
noncomputable def Path.pmf' (π : M.Path) : PMF M.Path :=
  (M.P (π.states[‖π‖ - 1]'(by grind))).bindOnSupport
    (fun s hs ↦
      PMF.pure
        ⟨π.states ++ [s], by simp, by simp, by grind, by grind [PMF.mem_support_iff]⟩)

theorem Path.pmf_apply {π : M.Path} {π' : π.succs} : π.pmf π' = π.pmf' π'.val := by
  simp [pmf, pmf']
  congr!
  grind

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
    · have : ‖π'‖ ≤ ‖π'‖ - 1 + 1 := by grind
      simp [this]
      grind
    · grind
  · simp_all
    intro s hs
    contrapose! h
    subst_eqs
    simp

def Path.ofLength_countable (n : ℕ) : Countable {π : M.Path | ‖π‖ = n} := by
  rcases n with _ | n
  · simp
  induction n with
  | zero =>
    have : { π : M.Path | ‖π‖ = 1 } = {({states := [M.ι]} : M.Path)} := by
      ext π; simp
      constructor
      · intro h; ext <;> grind
      · grind
    simp_all
  | succ n ih =>
    have : Countable {π : M.Path // ‖π‖ = n + 1} := by simp_all
    have :
          {π : M.Path | ‖π‖ = n + 1 + 1}
        = ⋃ π : {π : M.Path // ‖π‖ = n + 1}, π.val.succs := by
      ext π
      simp
      constructor
      · intro h
        use (π.take ⟨n, by omega⟩)
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
    · simp_all
      constructor
      · intro π'
        simp
        simp [Path.succs]
        grind
      · constructor
        · intro a ha b hb h
          simp_all [Path.succs, Path.eq_iff]
          -- simp only [instGetElemPathNatLtLengthStates] at h
          apply List.ext_getElem
          · grind
          · simp_all
            intro i hi
            if i = n + 1 then grind else
            have : List.take (n + 1) a.states = List.take (n + 1) b.states := by grind
            have :
                  (List.take (n + 1) a.states)[i]'(by simp; omega)
                = (List.take (n + 1) b.states)[i]'(by simp; omega) := by grind
            grind
        · intro s h'
          simp [Path.succs]
          simp at h'
          use {states:=π.states ++ [s]}
          simp

theorem Path.compelte : ⋃ n, {π : M.Path | ‖π‖ = n} = Set.univ := by
  ext
  simp

instance : Countable M.Path := by
  have : Countable (Set.univ : Set M.Path) := by
    rw [← Path.compelte]; simp
    exact Path.ofLength_countable
  exact Set.countable_univ_iff.mp this
@[simp]
instance : MeasurableSpace M.Path := MeasurableSpace.generateFrom Set.univ
instance : MeasurableSingletonClass M.Path := by
  constructor; exact fun _ ↦ MeasurableSpace.measurableSet_generateFrom trivial
instance : DiscreteMeasurableSpace M.Path := by
  constructor; exact fun s ↦ MeasurableSpace.measurableSet_generateFrom trivial

theorem Path.pmf_toMeasure_apply {π : M.Path} {S : Set π.succs} :
    π.pmf.toMeasure S = π.pmf'.toMeasure ((·.val) '' S) := by
  repeat rw [PMF.toMeasure_apply _ (by measurability)]
  simp [Set.indicator, Path.pmf_apply]
  symm
  apply tsum_eq_tsum_of_ne_zero_bij fun ⟨x, hx⟩ ↦ x.val
  · intro; grind
  · intro; simp
  · grind

@[grind =, simp]
theorem Path.pmf'_toMeasure_apply {π : M.Path} {S : Set M.Path} [∀ π' , Decidable (π' ∈ S)] :
    π.pmf'.toMeasure S = ∑' π', if π' ∈ S then π.pmf' π' else 0 := by
  repeat rw [PMF.toMeasure_apply _ (by measurability)]
  simp [Set.indicator]
  grind

noncomputable def Path.measure (π : M.Path) : Measure π.succs := π.pmf.toMeasure
instance {π : M.Path} : IsProbabilityMeasure π.measure := PMF.toMeasure.isProbabilityMeasure _

noncomputable def Path.lifted : Measure ((π : M.Path) → π.succs) :=
  Measure.infinitePi Path.measure

noncomputable instance {π : M.Path} : Inhabited π.succs :=
  let h := (M.P (π.states.getLast (by grind))).support_nonempty
  let s' := h.choose
  let hs' : s' ∈ (M.P (π.states.getLast (by exact π.nonempty))).support := h.choose_spec
  ⟨⟨{states := π.states ++ [s'], property := by simp at hs'; grind}, by simp [Path.succs]⟩⟩

@[grind]
noncomputable def embed_inv.help (f : (π : M.Path) → π.succs) : ℕ → M.Path
  | 0 => ⟨[M.ι], by grind, by simp, by grind, by grind⟩
  | n + 1 => f (help f n)
@[grind =, simp]
theorem embed_inv.help_length : ‖embed_inv.help (M:=M) f n‖ = n + 1 := by
  fun_induction help with grind
@[grind =, simp]
theorem embed_inv.help_getElem (i : ℕ) (h : i < n + 1) :
    (embed_inv.help (M:=M) f n)[i]'(by simp_all) = (embed_inv.help (M:=M) f i)[i] := by
  induction n with
  | zero => grind
  | succ n ih => grind
@[grind =, simp]
theorem embed_inv.help_states_getElem (i : ℕ) (h : i < n + 1) :
    (embed_inv.help (M:=M) f n).states[i]'(by simp_all) = (embed_inv.help (M:=M) f i).states[i]
  := embed_inv.help_getElem _ h
noncomputable def embed_inv (f : (π : M.Path) → π.succs) : M.Path' :=
  ⟨fun n ↦ (embed_inv.help f n)[n], by grind, by
    simp [embed_inv.help]
    intro i
    have : (f (embed_inv.help f i)).val[i] = (embed_inv.help f i)[i] := by
      grind
    rw [← this]
    exact (f (embed_inv.help f i)).val.property i (by simp)⟩

noncomputable def Pr : Measure M.Path' := (Path.lifted (M:=M)).map embed_inv

def Path.pref (π : M.Path) : Finset M.Path := Finset.univ.map ⟨π.take, π.take_inj⟩

@[grind ., simp]
theorem Path.take_mem_pref {π : M.Path} {i} (hi) : π.take ⟨i, hi⟩ ∈ π.pref := by
  simp [take, pref]
  use ⟨i, by grind⟩

theorem Path.Cyl_eq₁ (π : M.Path) :
    embed_inv ⁻¹' π.Cyl ⊆ cylinder π.pref {f | ∀ π', π'.val ≠ π → (f π').val ∈ π.pref} := by
  intro f
  simp [Path.Cyl, Path'.pref, Path.pref]
  rintro n ⟨_⟩ ⟨i, hi⟩ h
  simp at hi
  have : i < n := by
    contrapose! h
    have : i = n := by omega
    subst_eqs
    simp_all
    ext <;> grind [Path.take]
  use ⟨i + 1, by grind⟩
  ext j hj₁ hj₂
  · grind
  · simp at hj₁ hj₂
    simp_all only
    conv => left; simp [Path.take, Path'.take, Stream'.get]
    simp_all only [take_length]
    have : (((embed_inv f).take n).take ⟨i, by omega⟩) = (embed_inv f).take i := by
      ext
      · simp
      · simp [Path'.take, Path.take]
    simp_all
    replace :
        (f (((embed_inv f).take n).take ⟨i, by omega⟩)).val = (f ((embed_inv f).take i)).val := by
      grind
    simp [this]
    by_cases h' : j < i + 1
    · have :
            (f ((embed_inv f).take i)).val.states[j]'(by simp; omega)
          = ((embed_inv f).take i).states[j]'(by simp; grind) := by
        simp [embed_inv, Path'.take, Stream'.get]
        rw [Path.succs_states_getElem]
        · simp only [GetElem.getElem]
          simp [Stream'.get]
        · simp; grind
      simp [this]
      simp [Path'.take, Stream'.get]
    · have : i + 1 = j := by omega
      subst_eqs
      simp [embed_inv, embed_inv.help]
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
def Path.theSet (π : M.Path) : Set ((i : ↥π.pref) → i.val.succs) :=
  {f | ∀ π', π'.val ≠ π → (f π').val ∈ π.pref}

theorem Path.theSet_eq (π : M.Path) :
      π.theSet
    = Set.univ.pi fun (π' : ↥π.pref) ↦ {π'' : π'.val.succs | ¬π'.val = π → π''.val ∈ π.pref} := by
  ext f
  simp [theSet]

@[measurability]
theorem Path.theSet_measurable (π : M.Path) : MeasurableSet π.theSet :=
  DiscreteMeasurableSpace.forall_measurableSet π.theSet

theorem Path.Cyl_eq_cylinder (π : M.Path) : embed_inv ⁻¹' π.Cyl = cylinder π.pref π.theSet := by
  show embed_inv ⁻¹' π.Cyl = cylinder π.pref {f | ∀ π', π'.val ≠ π → (f π').val ∈ π.pref}
  ext f
  constructor
  · intro hf
    exact π.Cyl_eq₁ hf
  · simp [Path.Cyl, Path'.pref]
    intro h
    use ‖π‖ - 1
    simp [Path'.take]
    ext i ha hb
    · simp; grind
    · simp_all [Stream'.get]
      simp_all
      simp_all [Path.pref]
      suffices (embed_inv f).take i = π.take ⟨i, by omega⟩ by
        simp_all [Path.eq_iff]
        have : ((embed_inv f).take i).states[i] = (π.take ⟨i, hb⟩).states[i] := by grind
        simp [Path'.take, Stream'.get] at this
        simp [this, Path.take]
      induction i with
      | zero =>
        simp [Path'.take, Path.take]
        apply List.ext_getElem
        · simp; grind
        · simp [Stream'.get]
      | succ i ih =>
        simp_all
        specialize h ⟨i, by omega⟩ (by intro h; replace := Path.length_eq_of_eq h; grind)
        obtain ⟨⟨j, hj⟩, h⟩ := h
        have : j = i + 1 := by have := Path.length_eq_of_eq h; simp at this; omega
        subst_eqs
        rw [h]; clear h
        rw [← ih _ (by omega)]; clear ih
        simp [embed_inv, Path'.take]
        ext j h₁ h₂
        · simp
        · simp_all [Stream'.get]
          simp_all
          if j = i + 1 then
            subst_eqs
            simp_all
            simp [embed_inv.help]
            simp only [GetElem.getElem]
            simp
            congr! 7
            · apply List.ext_getElem
              · simp
              · simp_all [Stream'.get]
            · apply List.ext_getElem
              · simp
              · simp_all [Stream'.get]
          else
            rw [Path.succs_states_getElem _ _ (by simp_all; omega)]
            simp_all [Stream'.get]

@[measurability]
theorem embed_inv.measurable : Measurable (embed_inv (M:=M)) := by
  intro S hS
  induction hS with try measurability
  | basic T hT =>
    simp_all
    obtain ⟨π, ⟨_⟩⟩ := hT
    rw [Path.Cyl_eq_cylinder]
    measurability

instance : IsProbabilityMeasure (Path.lifted (M:=M)) :=
  Measure.instIsProbabilityMeasureForallInfinitePi _
instance : IsProbabilityMeasure (Pr (M:=M)) := by
  simp [Pr]
  refine Measure.isProbabilityMeasure_map ?_
  measurability

@[measurability]
theorem Path.Cyl_measurable (π : M.Path) : MeasurableSet π.Cyl :=
  MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self π)

set_option maxHeartbeats 500000 in
open scoped Classical in
open Path in
theorem Pr_cyl_help (π : M.Path) :
      (∏ x ∈ π.pref.attach, if h : ↑x = π then 1 else x.val.pmf' (π.take ⟨‖x.val‖, by
        obtain ⟨x, hx⟩ := x
        simp [Path.pref] at hx
        grind [Path.take]⟩))
    = ∏ i : Fin (‖π‖ - 1), (M.P π.states[i.val]) (π.states[↑i + 1]'(by grind)) := by
  symm
  apply Finset.prod_bij_ne_one
          fun i h h' ↦ ⟨π.take ⟨i, by omega⟩, by simp [Path.take, Path.pref]; use ⟨i, by omega⟩⟩
  · simp
  · simp
    intro i hi j hj h'
    have := π.take_inj h'
    grind
  · simp [pmf'_apply, Path.take, Path.pref, eq_iff]
    intro π' ⟨i, hi⟩ h h' h''
    have := congrArg List.length h
    simp at this
    have : π' = π.take ⟨i, by have : i = ‖π'‖ - 1 := (by grind); subst_eqs; omega⟩ := by
      have : i = ‖π'‖ - 1 := (by grind); subst_eqs
      ext <;> grind [Path.take]
    simp [this, Path.take]
    use ⟨i, by grind⟩
    simp
    simp [this, Path.take] at h''
    grind
  · simp
    intro ⟨i, hi⟩ h
    simp [Path.pmf'_apply]
    grind [Path.take]

attribute [grind =] Function.mem_support

set_option maxHeartbeats 500000 in
open scoped Classical in
open Path in
theorem Pr_cyl (π : M.Path) :
    Pr π.Cyl = ∏ i : Fin (‖π‖ - 1), M.P π.states[i] (π.states[i.val + 1]'(by grind)) := by
  simp [Pr]
  rw [Measure.map_apply (by measurability) (by measurability)]
  simp [lifted, Path.Cyl_eq_cylinder]
  rw [Measure.infinitePi_cylinder _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Path.theSet_eq]
  rw [Measure.pi_pi]
  simp
  simp [Path.measure, Path.pmf_toMeasure_apply]
  rw [← Pr_cyl_help]
  congr! 1 with ⟨x, hx⟩ hx'
  simp
  split_ifs with hx''
  · subst_eqs
    simp
    rw [← (M.P (π.states[‖π‖ - 1]'(by grind))).tsum_coe]
    apply tsum_eq_tsum_of_ne_zero_bij fun ⟨y, hy⟩ ↦ ({states:=π.states ++ [y]} : M.Path)
    · intro ⟨_, h₁⟩ ⟨_, h₂⟩ h; simp_all
    · intro π'; simp [succs]
      intro h h' h''
      use (π'.states[‖π'‖ - 1]'(by grind)), by
        have := π'.property (‖π'‖ - 2) (by grind)
        contrapose! this
        rw [← this]
        grind
      ext <;> grind
    · simp [succs, pmf']
      intro s hs
      rw [tsum_eq_single s] <;> grind
  simp [pmf'_apply]
  have : ‖x‖ < ‖π‖ := by clear hx'; simp_all [Path.pref, Path.take]; grind
  rw [tsum_eq_single (π.take ⟨‖x‖, by grind⟩)]
  · simp +contextual [hx'', Path.pref, succs]
  · simp +contextual [hx'', Path.pref, Path.succs]
    rintro π' _ ⟨i, hi⟩ ⟨_⟩
    grind

end MarkovChain
