import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Extensions to `ENNReal`

The intention is to upstream these to mathlib.
-/

namespace ENNReal

protected theorem tsum_biUnion' {ι : Type*} {S : Set ι} {f : α → ENNReal} {t : ι → Set α}
    (h : S.PairwiseDisjoint t) : ∑' x : ⋃ i ∈ S, t i, f x = ∑' (i : S), ∑' (x : t i), f x := by
  rw [← ENNReal.tsum_sigma]
  symm
  fapply Equiv.tsum_eq_tsum_of_support
  · exact Set.BijOn.equiv
      (fun ⟨⟨x, _⟩, ⟨y, _⟩⟩ ↦ ⟨y, ⟨t x, by simp_all; use x; simp_all⟩⟩)
      ⟨fun _ _ ↦ by simp_all, by
        constructor
        · intro ⟨x, x'⟩ _ ⟨y, y'⟩ _ _
          simp_all only [ne_eq, Subtype.mk.injEq, not_false_eq_true]
          ext <;> try assumption
          by_contra q
          have h₁ : {x'.val} ⊆ t x := by simp
          have h₂ : {x'.val} ⊆ t y := by simp_all
          absurd h x.coe_prop y.coe_prop q h₁ h₂
          simp
        · intro ⟨_, _⟩ _
          simp_all [Set.mem_iUnion.mp]⟩
  · simp only [Subtype.forall, Function.mem_support, ne_eq]
    intro ⟨_, ⟨_, _⟩⟩ _
    rfl

protected theorem tsum_biUnion {ι : Type*} {f : α → ENNReal} {t : ι → Set α}
    (h : Set.univ.PairwiseDisjoint t) : ∑' x : ⋃ i, t i, f x = ∑' (i) (x : t i), f x := by
  nth_rw 2 [← tsum_univ]
  rw [← ENNReal.tsum_biUnion' h, Set.biUnion_univ]

end ENNReal
