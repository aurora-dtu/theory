import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Extensions to `ENNReal`

The intention is to upstream these to mathlib.
-/

namespace ENNReal

protected theorem tsum_biUnion'' {ι : Type*} {t : ι → Set α} {f : ↑(⋃ i, t i) → ENNReal}
    (h : Set.univ.PairwiseDisjoint t) :
    ∑' x : ⋃ i, t i, f x = ∑' (i) (x : t i), f ⟨x, by use t i; simp⟩ := by
  rw [← ENNReal.tsum_sigma]
  symm
  fapply Equiv.tsum_eq_tsum_of_support
  · exact Set.BijOn.equiv
      (fun ⟨x, ⟨y, _⟩⟩ ↦ ⟨y, ⟨t x, by simp_all⟩⟩)
      ⟨fun _ _ ↦ by simp_all, by
        constructor
        · intro ⟨x, x', hx⟩ _ ⟨y, y', hy⟩ _ _
          simp_all only [Subtype.mk.injEq]
          ext <;> try simp_all only [Function.mem_support, ne_eq, not_false_eq_true]
          by_contra q
          subst_eqs
          have h₁ : {x'} ⊆ t x := by simp_all
          have h₂ : {x'} ⊆ t y := by simp_all
          absurd h (by trivial : x ∈ Set.univ) (by trivial : y ∈ Set.univ)
          simp_all
          contrapose! q
          have := q (by simp_all : {x'} ⊆ t x) (by simp_all)
          simp_all
        · intro ⟨x, hx⟩ hxf
          simp_all
          exact Set.mem_iUnion.mp hx⟩
  · simp only [Subtype.forall, Function.mem_support, ne_eq]
    intro ⟨_, ⟨_, _⟩⟩ _
    simp_all
    rfl

end ENNReal

namespace NNRat

@[grind =, simp]
theorem ennreal_cast {n : ℕ} : (n : NNRat) = (n : ENNReal) := by
  simp [NNRat.cast]
  simp [NNRatCast.nnratCast]
@[grind =, simp]
theorem ennreal_cast_zero : (0 : NNRat) = (0 : ENNReal) := by
  simp [NNRat.cast]
  simp [NNRatCast.nnratCast]
@[grind =, simp]
theorem ennreal_cast_one : (1 : NNRat) = (1 : ENNReal) := by
  simp [NNRat.cast]
  simp [NNRatCast.nnratCast]

@[simp]
theorem toENNReal_sub (a b : ℚ≥0) : (((a - b) : ℚ≥0) : ENNReal) = (↑a : ENNReal) - ↑b := by
  if h : b ≤ a then
    have := Rat.cast_sub (α:=Real) a b
    simp only [Rat.cast_nnratCast] at this
    refine (ENNReal.toReal_eq_toReal_iff' ?_ ?_).mp ?_
    swap
    · exact Ne.symm (not_eq_of_beq_eq_false rfl)
    · exact Ne.symm (not_eq_of_beq_eq_false rfl)
    convert this <;> clear this
    · simp
      have hx : ∀ (x : ℚ≥0), (@NNRat.cast ENNReal ENNReal.instNNRatCast x).toReal = x := by
        intro x
        rfl
      simp only [hx]
      obtain ⟨a, ha⟩ := a
      obtain ⟨b, hb⟩ := b
      simp_all
      rw [sub_def]
      simp
      replace h : b ≤ a := h
      norm_cast
      simp_all [Rat.coe_toNNRat]
    · norm_cast
      obtain ⟨a, ha⟩ := a
      obtain ⟨b, hb⟩ := b
      replace h : b ≤ a := h
      have : @NNRat.cast ENNReal ENNReal.instNNRatCast ⟨a, ha⟩ = ENNReal.ofReal a := by
        refine (ENNReal.toReal_eq_toReal_iff' ?_ ?_).mp ?_
        · exact Ne.symm (not_eq_of_beq_eq_false rfl)
        · exact ENNReal.ofReal_ne_top
        · refine Eq.symm (ENNReal.toReal_ofReal ?_)
          exact Rat.cast_nonneg.mpr ha
      have : @NNRat.cast ENNReal ENNReal.instNNRatCast ⟨b, hb⟩ = ENNReal.ofReal b := by
        refine (ENNReal.toReal_eq_toReal_iff' ?_ ?_).mp ?_
        · exact Ne.symm (not_eq_of_beq_eq_false rfl)
        · exact ENNReal.ofReal_ne_top
        · refine Eq.symm (ENNReal.toReal_ofReal ?_)
          exact Rat.cast_nonneg.mpr hb
      simp_all
  else
    simp_all
    replace h := h.le
    have : a - b = 0 := by
      simp only [sub_def, Rat.toNNRat_eq_zero, tsub_le_iff_right, zero_add, cast_le, h]
    simp [this]
    symm
    refine tsub_eq_zero_of_le ?_
    suffices ∃ c, a + c = b by
      obtain ⟨c, ⟨_⟩⟩ := this
      apply le_trans _ _ (b:=(↑a : ENNReal) + (↑c : ENNReal))
      · exact le_self_add
      · apply le_of_eq
        refine (ENNReal.toReal_eq_toReal_iff' ?_ ?_).mp (Rat.cast_add _ _).symm
        · exact Ne.symm (not_eq_of_beq_eq_false rfl)
        · exact Ne.symm (not_eq_of_beq_eq_false rfl)
    use (b - a)
    exact add_tsub_cancel_of_le h

end NNRat
