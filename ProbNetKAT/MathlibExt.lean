import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!

# Mathlib extensions used by ProbNetKAT

These are general definitions and theorems unrelated but necessary for the ProbNetKAT formalization.

## Main definitions

- `Finset.nepowerset`: A variant of `Finset.powerset` which _excludes ∅_.
- `Finset.strongerInduction`: An induction principle on `Finset` where the induction hypothesis can
  be applied to any finset with a smaller cardinality.
- `Real.inclusion_exclusion`: Inclusion-exclusion principle for real valued functions.
- `MeasureTheory.real_inclusion_exclusion`: Inclusion-exclusion principle for real valued measures.
- `MeasureTheory.ennreal_inclusion_exclusion`: Inclusion-exclusion principle for measures by way of
  reals.
- `MeasureTheory.ennreal_inclusion_exclusion_even_odd`: Inclusion-exclusion principle for measures
  expressed as the difference between the odd and the even terms.

-/

namespace Finset

variable {α : Type} [DecidableEq α] (s : Finset α)

/-! ## `Finset.nepowerset` -/

def nepowerset : Finset (Finset α) :=
  s.powerset \ {∅}

theorem nepowerset_eq : s.nepowerset = s.powerset \ {∅} := rfl
theorem powerset_eq_empty_union_nepowerset : s.powerset = {∅} ∪ s.nepowerset := by
  simp [nepowerset_eq]

@[simp]
theorem nepowerset_empty : (∅ : Finset α).nepowerset = ∅ := rfl
@[simp]
theorem nepowerset_singleton : ({a} : Finset α).nepowerset = {{a}} := rfl
@[simp]
theorem mem_nepowerset_iff : x ∈ s.nepowerset ↔ x ⊆ s ∧ x ≠ ∅ := by
  simp [nepowerset]
theorem nepowerset_insert :
    (insert a s).nepowerset = s.nepowerset ∪ s.powerset.image (insert a ·) := by
  ext l
  simp_all only [nepowerset, ne_eq, powerset_insert, mem_filter, mem_union, mem_powerset, mem_image,
    union_assoc, mem_singleton]
  constructor
  · simp_all only [mem_sdiff, mem_union, mem_powerset, mem_image, mem_singleton, not_false_eq_true,
    and_true, implies_true]
  · rintro (h | ⟨q, h, _, _⟩) <;> simp_all
    right; use q

@[simp]
theorem nepowerset_pair : ({a, b} : Finset α).nepowerset = {{a}, {b}, {a,b}} := by
  ext; simp_all [nepowerset_insert]; aesop

lemma sum_nepowerset_insert [AddCommMonoid β] (ha : a ∉ s) (f : Finset α → β) :
    ∑ t ∈ (insert a s).nepowerset, f t =
      (∑ t ∈ s.nepowerset, f t) + ∑ t ∈ s.powerset, f (insert a t) := by
  rw [nepowerset_insert, sum_union, sum_image]
  · exact insert_erase_invOn.2.injOn.mono fun t ht ↦ not_mem_mono (mem_powerset.1 ht) ha
  · aesop (add simp [disjoint_left, insert_subset_iff])

/-! ## `Finset.strongerInduction` -/

def strongerInduction {α : Type u_1} {p : Finset α → Prop}
    (H : (s : Finset α) → ((t : Finset α) → t.card < s.card → p t) → p s) (s : Finset α) : p s := by
  generalize hn : s.card = n
  induction n using Nat.strongRec generalizing s H with
  | ind n ih =>
    simp_all
    rcases n with _ | n
    · simp_all
    · obtain ⟨s, x, hxs, _, _⟩ :=
        Nonempty.exists_cons_eq (card_pos.mp (by omega) : s.Nonempty)
      simp_all
      apply H
      intro t ht
      simp_all
      exact ih t.card ht t rfl

def caseStrongerInduction {p : Finset α → Prop}
    (h₀ : p ∅)
    (h₁ : ∀ a s, a ∉ s → (∀ t, t.card ≤ s.card → p t) → p (insert a s)) (s : Finset α) : p s := by
  induction s using strongerInduction with
  | H s ih =>
    if h : s = ∅ then simp_all else
    obtain ⟨s, a, haI, _, _⟩ := Nonempty.exists_cons_eq (nonempty_iff_ne_empty.mpr h)
    simp_all
    apply h₁ _ _ haI fun _ _ ↦ ih _ (by omega)

end Finset

/-! ## Inclusion-exclusion -/

variable [DecidableEq (Set (Set H))] in
theorem Real.inclusion_exclusion' (μ : Set (Set H) → ℝ) (I : Finset (Set (Set H)))
  (f : Set (Set H) → Set (Set H))
  (hf : ∀ a b, f (a ∩ b) = f a ∩ f b)
  (h₀ : μ ∅ = 0)
  (h₁ : ∀ a b, μ (a ∪ b) = μ a + μ b - μ (a ∩ b)) :
    μ (⋃ c ∈ I, f c) = ∑ c ∈ I.nepowerset, (-1 : ℝ)^(c.card + 1) * μ (f (⋂₀ c)) := by
  induction I using Finset.caseStrongerInduction generalizing f with
  | h₀ => simp [h₀]
  | h₁ x I hx ih =>
    simp only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left, le_refl, not_false_eq_true,
      Finset.sum_nepowerset_insert, Finset.coe_insert, Set.sInter_insert, ih, hx]
    have :
          ∑ c ∈ I.powerset, (-1) ^ ((insert x c).card + 1) * μ (f (x ∩ ⋂₀ ↑c))
        = ∑ c ∈ I.powerset, (-1) ^ c.card * μ (f (x ∩ ⋂₀ ↑c)) := by
      refine Finset.sum_bijective (·) (Function.Involutive.bijective (congrFun rfl)) (by simp) ?_
      intro c hc
      simp [Finset.not_mem_of_mem_powerset_of_not_mem hc hx]
      left
      ring_nf
    simp only [this]; clear this
    rw [Finset.powerset_eq_empty_union_nepowerset]
    rw [h₁]
    nth_rw 2 [add_comm]
    simp [Finset.sum_union]
    rw [add_assoc, add_sub_assoc]
    congr 1
    rw [add_comm, sub_eq_add_neg]
    rw [ih _ ((Finset.eq_iff_card_ge_of_superset fun ⦃a⦄ a ↦ a).mpr rfl) f hf]
    congr
    apply neg_eq_iff_eq_neg.mpr
    rw [← Finset.sum_neg_distrib]
    simp only [neg_mul_eq_neg_mul]
    simp only [(fun _ ↦ by ring : ∀ n : ℕ, -(-1 : ℝ) ^ n = (-1 : ℝ) ^ (n + 1))]
    simp [Set.inter_iUnion]
    rw [ih _ ((Finset.eq_iff_card_ge_of_superset fun ⦃a⦄ a ↦ a).mpr rfl)]
    · simp [hf]
    · simp [hf, Set.inter_inter_distrib_left (f x)]

variable [DecidableEq (Set (Set H))] in
theorem Real.inclusion_exclusion (μ : Set (Set H) → ℝ) (I : Finset (Set (Set H)))
  (h₀ : μ ∅ = 0)
  (h₁ : ∀ a b, μ (a ∪ b) = μ a + μ b - μ (a ∩ b)) :
    μ (⋃₀ I) = ∑ c ∈ I.nepowerset, (-1 : ℝ)^(c.card + 1) * μ (⋂₀ c) := by
  simp_all [Set.sUnion_eq_biUnion, Real.inclusion_exclusion']

namespace MeasureTheory

theorem inclusion_exclusion₂ (μ : Measure (Set H)) [IsFiniteMeasure μ]
    (h : MeasurableSet b) : μ (a ∪ b) = μ a + μ b - μ (a ∩ b) := by
  have := @measure_union_add_inter (μ:=μ) (t:=b) (s:=a) _ _ h
  rw [← this]
  refine ENNReal.eq_sub_of_add_eq ?_ rfl
  simp

theorem inclusion_exclusion₂_real (μ : Measure (Set H)) [IsFiniteMeasure μ]
    (h : MeasurableSet b) : μ.real (a ∪ b) = μ.real a + μ.real b - μ.real (a ∩ b) := by
  suffices ENNReal.toReal (μ (a ∪ b)) = ENNReal.toReal (μ a + μ b - μ (a ∩ b)) by
    simp_all only [Measure.real]
    rw [← ENNReal.toReal_add, ← ENNReal.toReal_sub_of_le] <;> try simp
    apply le_trans
      (measure_mono (s:=a ∩ b) (t:=a ∪ b) (μ:=μ) (Set.subset_union_of_subset_right (by simp) a))
      (measure_union_le a b)
  rw [inclusion_exclusion₂ _ h]

variable [DecidableEq (Set (Set H))]

theorem real_inclusion_exclusion' (μ : Measure (Set H)) [IsFiniteMeasure μ]
  (I : Finset (Set (Set H)))
  (hI : ∀ i ∈ I, MeasurableSet i)
  (f : Set (Set H) → Set (Set H))
  (hf : ∀ a b, f (a ∩ b) = f a ∩ f b)
  (hfm : ∀ x ∈ I, MeasurableSet (f x)) :
    μ.real (⋃ c ∈ I, f c) = ∑ c ∈ I.nepowerset, (-1 : ℝ)^(c.card + 1) * μ.real (f (⋂₀ c)) := by
  induction I using Finset.caseStrongerInduction generalizing f with
  | h₀ => simp
  | h₁ x I hx ih =>
    simp only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left, le_refl, not_false_eq_true,
      Finset.sum_nepowerset_insert, Finset.coe_insert, Set.sInter_insert, ih, hx]
    have :
          ∑ c ∈ I.powerset, (-1) ^ ((insert x c).card + 1) * μ.real (f (x ∩ ⋂₀ ↑c))
        = ∑ c ∈ I.powerset, (-1) ^ c.card * μ.real (f (x ∩ ⋂₀ ↑c)) := by
      refine Finset.sum_bijective (·) (Function.Involutive.bijective (congrFun rfl)) (by simp) ?_
      intro c hc
      simp [Finset.not_mem_of_mem_powerset_of_not_mem hc hx]
      left
      ring_nf
    simp only [this]; clear this
    rw [inclusion_exclusion₂_real _ (Finset.measurableSet_biUnion I (by simp_all))]
    nth_rw 2 [add_comm]
    simp only [Finset.powerset_eq_empty_union_nepowerset, Finset.disjoint_singleton_left,
      Finset.mem_nepowerset_iff, Finset.empty_subset, ne_eq, not_true_eq_false, and_false,
      not_false_eq_true, Finset.sum_union, Finset.sum_singleton, Finset.card_empty, pow_zero,
      Finset.coe_empty, Set.sInter_empty, Set.inter_univ, one_mul]
    rw [add_assoc]
    rw [add_sub_assoc]
    congr 1
    rw [ih _ (by rfl) (by simp_all) _ hf (by simp_all)]
    simp only [Set.inter_iUnion]
    rw [ih _ (by rfl) (by simp_all) _ _ (by simp_all)]
    · ring_nf; simp [hf, Finset.sum_neg_distrib]
    · simp [hf, Set.inter_inter_distrib_left (f x)]

theorem real_inclusion_exclusion (μ : Measure (Set H)) [IsFiniteMeasure μ]
  (I : Finset (Set (Set H)))
  (hI : ∀ i ∈ I, MeasurableSet i) :
    μ.real (⋃₀ I) = ∑ c ∈ I.nepowerset, (-1 : ℝ)^(c.card + 1) * μ.real (⋂₀ c) := by
  simp_all [Set.sUnion_eq_biUnion, real_inclusion_exclusion']

theorem real_inclusion_exclusion_even_odd (μ : Measure (Set H)) [IsFiniteMeasure μ]
  (I : Finset (Set (Set H))) :
      ∑ c ∈ I.nepowerset, (-1 : ℝ)^(c.card + 1) * μ.real (⋂₀ c)
    = (∑ c ∈ I.nepowerset with Odd c.card, μ.real (⋂₀ c))
      - ∑ c ∈ I.nepowerset with Even c.card, μ.real (⋂₀ c) := by
  have : I.nepowerset = I.nepowerset.filter (Odd ·.card) ∪ I.nepowerset.filter (Even ·.card) := by
    ext x; simp_all only [Finset.mem_nepowerset_iff, ne_eq, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro ⟨h₁, h₂⟩
      simp_all
      exact Nat.even_or_odd x.card |>.symm
    · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
      · exact h₁
      · exact h₁
  nth_rw 1 [this]; clear this
  rw [Finset.sum_union]
  · rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr! 2 with ⟨x, hx⟩ <;> simp_all
  · intro a he ho x hx
    replace he := he hx; replace ho := ho hx
    simp only [Finset.mem_filter, Finset.mem_nepowerset_iff, ne_eq] at he ho
    exact False.elim ((Nat.not_even_iff_odd.mpr he.right) ho.right)

theorem ennreal_inclusion_exclusion (μ : Measure (Set H)) [IsFiniteMeasure μ]
  (I : Finset (Set (Set H)))
  (hI : ∀ i ∈ I, MeasurableSet i) :
    μ (⋃₀ I) = ENNReal.ofReal (∑ c ∈ I.nepowerset, (-1 : ℝ)^(c.card + 1) * μ.real (⋂₀ c)) := by
  simp_all [Set.sUnion_eq_biUnion, ← real_inclusion_exclusion]

theorem probability_inclusion_exclusion (μ : ProbabilityMeasure (Set H))
    (I : Finset (Set (Set H))) (hI : ∀ x ∈ I, MeasurableSet x) :
    μ (⋃₀ I) = (∑ c ∈ I.nepowerset, (-1 : ℝ)^(c.card + 1) * μ (⋂₀ c)).toNNReal := by
  refine ENNReal.coe_inj.mp ?_
  simp [ennreal_inclusion_exclusion _ _ hI]
  rfl

theorem ennreal_inclusion_exclusion_even_odd (μ : Measure (Set H)) [IsFiniteMeasure μ]
  (I : Finset (Set (Set H)))
  (hI : ∀ i ∈ I, MeasurableSet i) :
      μ (⋃₀ I)
    = (∑ c ∈ I.nepowerset with Odd c.card, μ (⋂₀ c)) - ∑ c ∈ I.nepowerset with Even c.card, μ (⋂₀ c)
:= by
  rw [ennreal_inclusion_exclusion _ _ hI, real_inclusion_exclusion_even_odd]
  rw [ENNReal.ofReal_sub _ (Finset.sum_nonneg (by simp))]
  congr <;> (rw [ENNReal.ofReal_sum_of_nonneg (by simp)]; simp)

theorem probability_inclusion_exclusion_even_odd (μ : ProbabilityMeasure (Set H))
    (I : Finset (Set (Set H))) (hI : ∀ x ∈ I, MeasurableSet x) :
      μ (⋃₀ I)
    = (∑ c ∈ I.nepowerset with Odd c.card, μ (⋂₀ c)) - ∑ c ∈ I.nepowerset with Even c.card, μ (⋂₀ c)
:= by
  refine ENNReal.coe_inj.mp ?_
  simp [ennreal_inclusion_exclusion_even_odd _ _ hI]

end MeasureTheory
