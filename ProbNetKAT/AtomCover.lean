import ProbNetKAT.Cantor

namespace ProbNetKAT

variable {P : Type} [Countable P]
-- variable {H : Type}

theorem ℬ_b_exists_unique_cover.base (hb : b.Finite) (hs : s ∈ {x | ∃ h ∈ b, B[h] = x}) :
    ∃! q : Set (Set H[P]),
        ⋃ a ∈ q, A{a,b} = s
      ∧ (q.PairwiseDisjoint fun x ↦ A{x,b})
      ∧ q.Finite
      ∧ (s.Nonempty ↔ q.Nonempty)
      ∧ ∀ a ∈ q, a ⊆ b := by
  simp only [Set.mem_setOf_eq] at hs
  obtain ⟨w, hw, _, _⟩ := hs
  nth_rw 1 [B_h_eq_iUnion_A_ab hw]
  simp
  apply Exists.intro
  · split_ands
    · rfl
    · intro x hx y hy hxy a hax hay q hq
      simp_all
      replace hax := hax hq
      replace hqy := hay hq
      simp_all [A_ab]
    · show {a | w ∈ a ∧ a ⊆ b}.Finite
      suffices {a | a ⊆ b}.Finite by exact Set.Finite.subset this (by simp)
      exact Set.Finite.finite_subsets hb
    · constructor
      · intro _
        use {w}
        show w ∈ ({w} : Set H[P]) ∧ {w} ⊆ b
        simp [hw]
      · intro h
        replace h : {c | w ∈ c ∧ c ⊆ b}.Nonempty := h
        obtain ⟨c, h₁, h₂⟩ := h
        use {w}
        simp [B_h]
    · show ∀ a ∈ {c | w ∈ c ∧ c ⊆ b}, a ⊆ b
      simp
    · simp_all only [and_imp]
      intro y hy h_disjoint h_fin h_nonempty h
      show y = {c | w ∈ c ∧ c ⊆ b}
      simp [Set.ext_iff] at hy
      ext x
      simp_all only [Set.mem_setOf_eq]
      constructor
      · intro hxy
        replace hy := hy x |>.mp
        simp_all only [forall_exists_index, and_imp, and_true]
        have ⟨i, ⟨h₁, h₂⟩, h₃⟩ := hy x hxy (A_ab_a_mem (h x hxy)); clear hy
        simp only [A_ab, Set.mem_setOf_eq] at h₃
        subst_eqs
        simp_all only [Set.mem_inter_iff, and_true, Set.inter_subset_right]
      · intro ⟨h₁, h₂⟩
        replace hy := hy x |>.mpr
        simp_all only [A_ab, Set.mem_setOf_eq, exists_eq_right, Set.mem_inter_iff, and_self,
          Set.inter_subset_right, forall_const]
        induction y, h_fin using Set.Finite.induction_on with
        | empty => simp_all only [Set.pairwiseDisjoint_empty, Set.not_nonempty_empty, iff_false,
          Set.mem_empty_iff_false, IsEmpty.forall_iff, implies_true]
        | insert hsy ih h₃ =>
          rename_i s y
          simp_all only [Set.insert_nonempty, true_iff, Set.mem_insert_iff, or_true, implies_true,
            forall_const, iff_true, forall_eq_or_imp]
          rcases hy with hy | hy
          · subst_eqs
            simp_all only [IsEmpty.forall_iff, implies_true, Set.inter_subset_right, true_and,
              Set.left_eq_inter, true_or]
          · simp_all only [forall_const]
            right
            apply h₃ _ (Set.nonempty_of_mem hy)
            intro u huy v hvy huv
            exact h_disjoint (Set.mem_insert_of_mem s huy) (Set.mem_insert_of_mem s hvy) huv

theorem ℬ_b_exists_unique_cover.empty :
    ∃! q : Set (Set H[P]),
        ⋃ a ∈ q, A{a,b} = ∅
      ∧ (q.PairwiseDisjoint fun x ↦ A{x,b})
      ∧ q.Finite
      ∧ ((∅ : Set (Set H[P])).Nonempty ↔ q.Nonempty)
      ∧ ∀ a ∈ q, a ⊆ b := by
  use {}
  simp
  intro y h_empty h_disjoint h_fin h_nonempty h
  exact Set.not_nonempty_iff_eq_empty.mp h_nonempty

theorem A_ab_inj {b : Set H[P]} : Function.Injective (fun (a : {a | a ⊆ b}) ↦ A{a,b}) := by
  intro ⟨a₁, hab₁⟩ ⟨a₂, hab₂⟩ h
  simp_all [A_ab, Set.ext_iff]
  simp_all [A_ab, Set.ext_iff]
  intro x
  constructor
  · intro h'
    have h₁ := h a₁
    have h₂ := h a₂
    clear h
    simp_all [hab₁]
    replace h₁ := h₁.mp (fun x a ↦ hab₁ a)
    simp_all
  · intro h'
    have h₁ := h a₁
    clear h
    simp_all
    replace h₁ := h₁.mp (fun x a ↦ hab₁ a)
    simp_all

@[simp] theorem A_ab_mem_iff : x ∈ A{a,b} ↔ a = x ∩ b := by simp [A_ab]


/--
For any `B ∈ ℬ{b}` there exists **finite** set of **subsets of `b`**, call it `q`, who's **disjoint
union** satisfies `B = ⋃ a ∈ q, A{a,b}`.
-/
def ℬ_b_exists_cover (hsb : B ∈ ℬ{b}) (hb : b.Finite) :
    ∃ q : Set (Set H[P]),
        ⋃ a ∈ q, A{a,b} = B
      ∧ Set.PairwiseDisjoint q (A{·,b})
      ∧ q.Finite
      ∧ (B.Nonempty ↔ q.Nonempty)
      ∧ ∀ a ∈ q, a ⊆ b := by
  induction hsb with clear B
  | base s hs => exact (ℬ_b_exists_unique_cover.base hb hs).exists
  | empty => exact ℬ_b_exists_unique_cover.empty.exists
  | compl s hs ih =>
    replace hs : s ∈ ℬ{b} := hs
    obtain ⟨w, ⟨_, _, _⟩, hw⟩ := ih
    simp_all
    clear hs
    use {a ∈ wᶜ | a ⊆ b}
    split_ands
    · ext a
      simp_all only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_iUnion, A_ab_mem_iff, exists_prop,
        exists_eq_right, Set.inter_subset_right, and_true, Set.mem_iInter]
      constructor
      · intro h
        exact fun i ↦ (ne_of_mem_of_not_mem · h)
      · intro h q
        exact h (a ∩ b) q rfl
    · intro x hx y hy hxy a hax hay q hq
      simp_all
      replace hax := hax hq
      replace hqy := hay hq
      simp_all [A_ab]
    · suffices {a | a ⊆ b}.Finite by exact Set.Finite.subset this (by simp)
      exact Set.Finite.finite_subsets hb
    · simp
      constructor
      · simp
        intro x hx
        if hw : w.Nonempty then
          simp_all
          obtain ⟨c, hc⟩ := hw
          have : ∀ i, x ∈ A{i,b} → i ∉ w := fun i a a_1 ↦ hx i a_1 a
          simp [A_ab] at this
          use x ∩ b
          simp_all
        else
          simp_all
          have : w = ∅ := by exact Set.not_nonempty_iff_eq_empty.mp hw
          subst_eqs
          simp_all
          use b
          simp
      · rintro ⟨x, hx₁, hx₂⟩
        if hwN : w.Nonempty then
          simp_all
          have ⟨q, hq₁, hq₂⟩ := hw.right.right.left
          contrapose! hx₁
          obtain ⟨y, hy⟩ := hq₂
          simp [A_ab] at hy
          subst_eqs
          simp_all
          have := hx₁ x
          have : x ∩ b = x := by simp_all
          simp_all
        else
          have : w = ∅ := Set.not_nonempty_iff_eq_empty.mp hwN
          subst_eqs
          simp_all
    · simp
  | union s t hs ht ihs iht =>
    replace hs : s ∈ ℬ{b} := hs
    replace ht : t ∈ ℬ{b} := ht
    obtain ⟨s, ⟨_, _, _⟩, ihs⟩ := ihs
    obtain ⟨t, ⟨_, _, _⟩, iht⟩ := iht
    use s ∪ t
    split_ands
    · ext x
      simp_all
    · intro x hx y hy hxy a hax hay q hq
      simp_all only [Set.nonempty_iUnion, exists_prop, Set.mem_union, ne_eq, Set.le_eq_subset,
        Set.bot_eq_empty, Set.mem_empty_iff_false]
      replace hax := hax hq
      replace hqy := hay hq
      simp_all [A_ab]
    · refine Set.Finite.union ihs.right.left iht.right.left
    · simp_all only [Set.nonempty_iUnion, exists_prop, Set.union_nonempty]
    · simp_all
      rintro a (ha | ha)
      · exact ihs.right.right.right _ ha
      · exact iht.right.right.right _ ha

set_option maxHeartbeats 5000000 in
/--
For any `B ∈ ℬ{b}` there exists **finite** set of **subsets of `b`**, call it `q`, who's **disjoint
union** satisfies `B = ⋃ a ∈ q, A{a,b}`.
-/
def ℬ_b_exists_unique_cover (hsb : B ∈ ℬ{b}) (hb : b.Finite) :
    ∃! q : Set (Set H[P]),
        ⋃ a ∈ q, A{a,b} = B
      ∧ Set.PairwiseDisjoint q (A{·,b})
      ∧ q.Finite
      ∧ (B.Nonempty ↔ q.Nonempty)
      ∧ ∀ a ∈ q, a ⊆ b := by
  induction hsb with clear B
  | base s hs =>
    simp_all
    exact ℬ_b_exists_unique_cover.base hb hs
  | empty => exact ℬ_b_exists_unique_cover.empty
  | compl s hs ih => sorry
  | union s t hs ht ihs iht => sorry

/-- The unique atomic cover of `B` -/
def 𝒜 {b : Set H[P]} (B : ℬ{b}) (hb : b.Finite) : Set (Set H[P]) :=
  (ℬ_b_exists_cover B.prop hb).choose
def 𝒜_spec {b : Set H[P]} (B : ℬ{b}) (hb : b.Finite) :
      ⋃ a ∈ (𝒜 B hb), A{a,b} = B
    ∧ Set.PairwiseDisjoint (𝒜 B hb) (A{·,b})
    ∧ (𝒜 B hb).Finite
    ∧ (B.val.Nonempty ↔ (𝒜 B hb).Nonempty)
    ∧ ∀ a ∈ (𝒜 B hb), a ⊆ b :=
  (ℬ_b_exists_cover B.prop hb).choose_spec
def 𝒜_covers {b : Set H[P]} (B : ℬ{b}) (hb : b.Finite) :
    ⋃ a ∈ (𝒜 B hb), A{a,b} = B := by have := 𝒜_spec B hb; simp_all
def 𝒜_disjoint {b : Set H[P]} (B : ℬ{b}) (hb : b.Finite) :
    Set.PairwiseDisjoint (𝒜 B hb) (A{·,b}) := by have := 𝒜_spec B hb; simp_all
def 𝒜_finite {b : Set H[P]} (B : ℬ{b}) (hb : b.Finite) :
    (𝒜 B hb).Finite := by have := 𝒜_spec B hb; simp_all
def 𝒜_nonempty_iff {b : Set H[P]} (B : ℬ{b}) (hb : b.Finite) :
    (B.val.Nonempty ↔ (𝒜 B hb).Nonempty) := by have := 𝒜_spec B hb |>.right; simp_all
def 𝒜_empty_iff {b : Set H[P]} (B : ℬ{b}) (hb : b.Finite) :
    (B.val = ∅ ↔ 𝒜 B hb = ∅) := by
      constructor <;> (intro h; apply Set.not_nonempty_iff_eq_empty.mp)
      · exact (𝒜_nonempty_iff B hb).not.mp (Set.not_nonempty_iff_eq_empty.mpr h)
      · exact ((𝒜_nonempty_iff B hb).not).mpr (by exact Set.not_nonempty_iff_eq_empty.mpr h)
@[simp]
def 𝒜_empty {b : Set H[P]} (hb : b.Finite) :
    (𝒜 ⟨(∅ : Set (Set H[P])), by simp⟩ hb = ∅) := by
      have := 𝒜_empty_iff ⟨(∅ : Set (Set H[P])), by simp⟩ hb
      simp_all only [true_iff]
def 𝒜_subsets {b : Set H[P]} (B : ℬ{b}) (hb : b.Finite) :
    ∀ a ∈ 𝒜 B hb, a ⊆ b := by have := 𝒜_spec B hb; simp_all

-- theorem 𝒜_B_b : 𝒜 ⟨B[h], B_h_mem_ℬ_b rfl⟩ sorry = sorry := by
--   simp
-- theorem 𝒜_union : 𝒜 ⟨B[h], B_h_mem_ℬ_b rfl⟩ sorry = sorry := by
--   simp

end ProbNetKAT
