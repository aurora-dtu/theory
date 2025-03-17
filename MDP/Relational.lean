import MDP.Basic

namespace MDP

noncomputable def ofRelation (r : S → A → ENNReal → S → Prop)
  (h₀ : ∀ {c α p c'}, r c α p c' → ¬p = 0)
  (h₁ : ∀ {c α p₀ c'}, r c α p₀ c' → ∑' (b : S) (p : { p // r c α p b }), p.val = 1)
  (h₂ : ∀ (s : S), ∃ p a x, r s a p x) :
    MDP S A where
  P' := fun c α ↦
    have : Decidable (∃ p c', 0 < p ∧ r c α p c') := Classical.propDecidable _
    if h : ∃ p c', 0 < p ∧ r c α p c' then some ⟨fun c' ↦ ∑' x : {x // r c α x c'}, ↑x, by
      rw [Summable.hasSum_iff (by simp)]
      obtain ⟨p₀, c₀, h, h'⟩ := h
      exact h₁ h'
    ⟩ else none
  exists_P'_isSome := by
    intro s
    simp_all
    obtain ⟨p, α, c', h⟩ := h₂ s
    use α, p, pos_iff_ne_zero.mpr (h₀ h), c'

variable {r : S → A → ENNReal → S → Prop}

@[simp]
theorem ofRelation_P : (ofRelation r h₀ h₁ h₂).P = fun c α c' ↦ ∑' p : {p // r c α p c'}, ↑p := by
  unfold P
  ext c α c'
  simp [ofRelation]
  symm
  split_ifs with h'
  · obtain ⟨_, ⟨_⟩⟩ := h'; rfl
  · simp_all
    intro x
    by_cases 0 < x <;> simp_all only [IsEmpty.forall_iff, not_lt, nonpos_iff_eq_zero, implies_true]

@[simp]
theorem ofRelation_act : (ofRelation r h₀ h₁ h₂).act = fun c ↦ {α | ∃ p c', r c α p c'} := by
  ext c α
  simp [act]
  constructor
  · intro h
    obtain ⟨c', h⟩ := Function.ne_iff.mp h
    simp_all
    obtain ⟨p, h, hp⟩ := h
    use p, c'
  · refine fun ⟨p, c', h⟩ ↦ Function.ne_iff.mpr (Exists.intro c' ?_)
    simp_all
    use p, h, h₀ h

@[simp]
theorem ofRelation_succs : (ofRelation r h₀ h₁ h₂).succs = fun α c ↦ {c' | ∃ p, r c α p c'} := by
  ext α c c'
  simp [succs]
  constructor <;> aesop

@[simp]
theorem ofRelation_succs_univ :
    (ofRelation r h₀ h₁ h₂).succs_univ = fun c ↦ {c' | ∃ α p, r c α p c'} := by
  ext c c'
  simp [succs_univ]

end MDP
