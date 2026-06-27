import Mathlib.Probability.ProductMeasure
import STDX.Subst
import MDP.Optimization
import Mathlib.Algebra.Order.IsBotOne
import Mathlib.Tactic.DeriveTraversable
import Mathlib.Topology.Order.ScottTopology
import Mathlib.Topology.Order.LawsonTopology
import Mathlib.Topology.Order.PartialSups
import Mathlib.Order.Ideal

class SubsetSum (α : Type*) [AddCommMonoid α] [TopologicalSpace α] [SupSet α] where
  tsum_eq_iSup_sum_range {f : ℕ → α} : ∑' i, f i = ⨆ n, ∑ i ≤ n, f i

section

variable {α : Type*} [CompleteLattice α]

class MuchLT (α : Type*) where
  mlt : α → α → Prop

infix:50 " ≪ " => MuchLT.mlt

instance {α : Type*} [CompleteLattice α] : MuchLT α where
  mlt x y := ∀ (D : Set α), D.Nonempty → DirectedOn (· ≤ ·) D → y ≤ sSup D → ∃ d ∈ D, x ≤ d

def muchUpperClosure {α : Type*} [CompleteLattice α] (s : Set α) := {x : α | ∃ a ∈ s, a ≪ x}
def muchLowerClosure {α : Type*} [CompleteLattice α] (s : Set α) := {x : α | ∃ a ∈ s, x ≪ a}

@[gcongr]
theorem monotone_mlt_apply {a : α} : Monotone (MuchLT.mlt a : α → Prop) := by
  intro x y hx
  simp_all [MuchLT.mlt]
  intro h D hD h'
  grw [hx] at h
  exact h D hD h'

-- https://proofwiki.org/wiki/Way_Below_implies_Preceding
theorem le_of_mlt {x y : α} (h : x ≪ y) : x ≤ y := by
  simp [MuchLT.mlt] at h
  specialize h {y}
  simpa [directedOn_singleton] using h

theorem inf_mlt {x y z : α} (hxz : x ≪ z) (hyz : y ≪ z) : x ⊓ y ≪ z := by
  simp_all [MuchLT.mlt]
  intro D hD hD' hzD
  specialize hxz D hD hD' hzD
  specialize hyz D hD hD' hzD
  obtain ⟨y', hy, hy'⟩ := hyz
  obtain ⟨x', hx, hx'⟩ := hxz
  specialize hD' y' hy x' hx
  obtain ⟨d, hd⟩ := hD'
  use d
  simp_all
  grw [← hd.right.left, hy']
  simp

-- https://proofwiki.org/wiki/Join_is_Way_Below_if_Operands_are_Way_Below
theorem sup_mlt {x y z : α} (hxz : x ≪ z) (hyz : y ≪ z) : x ⊔ y ≪ z := by
  simp_all [MuchLT.mlt]
  intro D hD hD' hzD
  specialize hxz D hD hD' hzD
  specialize hyz D hD hD' hzD
  obtain ⟨d₁, hy, hd₁⟩ := hyz
  obtain ⟨d₂, hx, hd₂⟩ := hxz
  obtain ⟨d, hdD, h₁, h₂⟩ := Set.inter_nonempty.mp (hD' d₁ hy d₂ hx)
  grind

@[simp]
theorem bot_mlt {x : α} : ⊥ ≪ x := by simp_all [MuchLT.mlt]; grind [Set.nonempty_def]

@[grind <=, grind .]
theorem mlt_of_le_mlt_le {x y z u : α} (hxy : x ≤ y) (hyz : y ≪ z) (hzu : z ≤ u) : x ≪ u := by
  simp_all [MuchLT.mlt]; grind
theorem mlt_of_mlt_le {x y z : α} (hxy : x ≪ y) (hyz : y ≤ z) : x ≪ z := by grind
theorem mlt_of_le_mlt {x y z : α} (hxy : x ≤ y) (hyz : y ≪ z) : x ≪ z := by grind

theorem mlt_trans {x y z : α} (hxy : x ≪ y) (hyz : y ≪ z) : x ≪ z :=
  mlt_of_le_mlt_le (le_of_mlt hxy) hyz (by rfl)
theorem mlt_antisymm {x y : α} (hxy : x ≪ y) (hyx : y ≪ x) : x = y :=
  (le_of_mlt hxy).antisymm (le_of_mlt hyx)

theorem mlt_iff_le_sSup {x y : α} :
    x ≪ y ↔ ∀ I, y ≤ sSup I ∧ Order.IsIdeal I → x ∈ I := by
  constructor
  · rintro h I ⟨hI, I_lower, I_nonempty, I_directed⟩
    specialize h I ‹_› ‹_› ‹_›
    obtain ⟨d, hd₁, hd₂⟩ := h
    exact Set.mem_of_eq_of_mem rfl (I_lower hd₂ hd₁)
  · simp_all
    intro h D h₁ h₂ h₃
    specialize h (lowerClosure D) (by simp_all [le_sSup_iff]) ?_
    · simp [Order.isIdeal_iff, ← Set.nonempty_iff_ne_empty, *]
      simp_all [DirectedOn]
      grind
    simp_all

class ContinuousLattice (α : Type*) [CompleteLattice α] where
  /-- axiom of approximation -/
  eq_sSup_of_mlt : ∀ (x : α), x = sSup {u | u ≪ x}
def ContinuousLattice.eq_sSup_muchLowerClosure [ContinuousLattice α] (x : α) :
    x = sSup (muchLowerClosure {x}) := by simp [muchLowerClosure]; exact eq_sSup_of_mlt x


end

variable {α : Type*} [CompleteLattice α] [ContinuousLattice α]

section

open Topology TopologicalSpace Set IsLawson Filter Function

-- ↑X = {y ∈ L : x ≤ y for some x ∈ X}
example {X : Set α} : (upperClosure X : Set α) = {y | ∃ x ∈ X, x ≤ y} := by ext; simp
example {x : α} : (upperClosure {x}).1 = Set.Ici x := by ext; simp

-- 1.16. LEMMA
theorem ContinuousLattice.exists_mlt_and_not_le {x z : α} (h₁ : x ≪ z) (h₂ : x ≠ z) :
    ∃ u, u ≪ z ∧ ¬u ≤ x := by
  replace := (ContinuousLattice.eq_sSup_of_mlt z).le
  simp [le_sSup_iff, upperBounds] at this
  conv at this => enter [b]; rw [← not_imp_not]
  simp at this
  specialize this x (by grind [le_of_mlt h₁])
  grind

-- 1.16. LEMMA
theorem asdasdasfasd' {x z : α} (h₁ : x ≪ z) (h₂ : x ≠ z) : ∃ y, x ≤ y ∧ y ≪ z ∧ x ≠ y := by
  obtain ⟨u, hu₁, hu₂⟩ : ∃ u, u ≪ z ∧ ¬u ≤ x := ContinuousLattice.exists_mlt_and_not_le h₁ h₂
  use x ⊔ u
  split_ands
  · exact le_sup_left
  · exact sup_mlt h₁ hu₁
  · contrapose hu₂
    rw [hu₂]
    simp

-- 1.17. LEMMA
theorem asdasdasfasd'' {x z : α} (h₁ : x ≪ z) (h₂ : x ≠ z) : ∃ y, x ≪ y ∧ y ≪ z ∧ x ≠ y := by
  let I := {u | ∃ y, u ≪ y ∧ y ≪ z}
  have I_lower : IsLowerSet I := by intro; grind
  have I_ideal : Order.IsIdeal I := by
    simp_all [Order.isIdeal_iff]
    constructor
    · simp [Set.nonempty_iff_empty_ne, I, Set.ext_iff]
      use ⊥, x; simp_all
    · intro a ha b hb
      obtain ⟨a', ha₁, ha₂⟩ := ha
      obtain ⟨b', hb₁, hb₂⟩ := hb
      use a ⊔ b
      simp_all
      use a' ⊔ b'
      grind [sup_mlt, le_sup_left, le_sup_right]
  have : sSup I = z := by
    set z' := sSup I
    by_contra q
    obtain ⟨y, hy₁, hy₂⟩ : ∃ y, y ≪ z ∧ ¬y ≤ z' := by
      have := (ContinuousLattice.eq_sSup_of_mlt z).le
      simp_all [le_sSup_iff, upperBounds]
      conv at this => enter [b]; rw [← not_imp_not]
      simp at this
      apply this
      simp [z', le_sSup_iff]
      simp_all [z']
      simp [le_antisymm_iff] at q
      specialize q ?_
      · simp [I]; intro a b hab hbz; apply le_trans (le_of_mlt hab) (le_of_mlt hbz)
      simp [le_sSup_iff] at q
      exact q
    obtain ⟨u, hu₁, hu₂⟩ : ∃ u, u ≪ y ∧ ¬u ≤ z' := by
      have := (ContinuousLattice.eq_sSup_of_mlt y).le
      simp_all [le_sSup_iff, upperBounds]
      conv at this => enter [b]; rw [← not_imp_not]
      simp at this
      exact this _ hy₂
    have : u ∈ I := by grind
    have : u ≤ sSup I := le_sSup_of_le this (by rfl)
    grind
  have : x ∈ I := by
    simp [I]
    rw [← this, mlt_iff_le_sSup] at h₁
    exact h₁ I ⟨by rfl, I_ideal⟩
  obtain ⟨y', hy'₁, hy'₂⟩ : ∃ y', x ≪ y' ∧ y' ≪ z := this
  obtain ⟨y'', hy''₁, hy''₂⟩ : ∃ y'', x < y'' ∧ y'' ≪ z := by
    if x = y' then
      subst_eqs
      obtain ⟨y', hy'₁, hy'₂, hy'₃⟩ := asdasdasfasd' hy'₂ h₂
      grind [lt_of_le_of_ne]
    else
      obtain ⟨y'', _, _, _⟩ := asdasdasfasd' hy'₁ ‹_›
      use y''
      grind [lt_of_le_of_ne, mlt_trans]
  use y' ⊔ y''
  split_ands
  · exact mlt_of_mlt_le hy'₁ le_sup_left
  · exact sup_mlt hy'₂ hy''₂
  · rintro ⟨_⟩
    simp_all
    contrapose hy''₁
    simp [Std.not_lt_of_ge]

-- Theorem 1.18
theorem exists_between_mlt {x y : α} (h : x ≪ y) : ∃ z, x ≪ z ∧ z ≪ y := by
  if x = y then subst_eqs; use x
  else
    obtain ⟨u, hu₁, hu₂, hu₃⟩ := asdasdasfasd'' h ‹_›
    use u

theorem asdasdasfasd {x y : α} :
    x ≪ y ↔ ∀ D, D.Nonempty → DirectedOn (· ≤ ·) D → y ≤ sSup D → ∃ d ∈ D, x ≪ d := by
  symm
  constructor
  · conv => right; simp [MuchLT.mlt]
    grind [le_of_mlt]
  intro h D h₁ h₂ h₃
  have ⟨z, hxz, hzy⟩ : ∃ z, x ≪ z ∧ z ≪ y := exists_between_mlt h
  have ⟨d, hdD, hzd⟩ : ∃ d ∈ D, z ≤ d := hzy D h₁ h₂ h₃
  grind

@[simp]
theorem isUpperSet_muchUpperClosure {α : Type*} [CompleteLattice α] {u : α} :
    IsUpperSet (muchUpperClosure {u}) := by
  simp [← Set.monotone_mem, muchUpperClosure, monotone_mlt_apply]
@[simp]
theorem dirSupInacc_muchUpperClosure {u : α} : DirSupInacc (muchUpperClosure {u}) := by
  simp [muchUpperClosure]
  intro D h₁ h₂ a hDa hax
  apply asdasdasfasd.mp at hax
  specialize hax D h₁ h₂ (by simp_all [IsLUB, IsLeast, upperBounds, lowerBounds, le_sSup_iff])
  obtain ⟨d, hd₁, hd₂⟩ := hax
  use d, hd₁, hd₂

@[simp]
theorem IsScott.isOpen_muchUpperClosure
    {α : Type*} [TopologicalSpace α] [CompleteLattice α] [ContinuousLattice α] [IsScott α Set.univ]
    {u : α} : IsOpen (muchUpperClosure {u}) := by
  simp [IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open (D := Set.univ)]
  simp [IsScottHausdorff.isOpen_iff_dirSupInacc (t := scottHausdorff α Set.univ)]

variable [L : TopologicalSpace α] [Topology.IsLawson α] [TopologicalLattice α]

#synth T1Space α

-- 1.10. THEOREM.
instance : T2Space α := by
  rw [t2Space_iff]
  intro x y hab
  wlog h : ¬x ≤ y
  · by_cases y ≤ x <;> grind
  obtain ⟨u, hu₁, hu₂⟩ : ∃ u, u ≪ x ∧ ¬u ≤ y := by
    have := ContinuousLattice.eq_sSup_of_mlt x
    grind [sSup_le_iff]
  have hu₁' := le_of_mlt hu₁
  use muchUpperClosure {u}, (upperClosure {u})ᶜ
  split_ands
  · letI S : TopologicalSpace α := Topology.scott α Set.univ
    letI : IsScott α Set.univ := ⟨rfl⟩
    simp [Topology.lawsonOpen_iff_scottOpen_of_isUpperSet' L S]
  · have : (↑(upperClosure {u}))ᶜ ∈ lawsonBasis α := by
      use {u}, ?_, Set.univ <;> simp [compl_eq_univ_diff]
    rw [IsTopologicalBasis.isOpen_iff (Topology.IsLawson.isTopologicalBasis α)]
    intro z hz
    use (↑(upperClosure {u}))ᶜ, this
  · simpa [muchUpperClosure]
  · simpa
  · intro A h₁ h₂ a ha
    specialize_all ha
    simp_all [muchUpperClosure]
    have : u ≤ a := le_of_mlt h₁
    contradiction

#print axioms instT2Space_wGCL

example {α : Type*} {A B : Set α} : A ⊆ B ↔ ∀ a, a ∈ A → a ∈ B := by
  grind only [= subset_def]


-- @[to_dual none]
theorem Lawson.nhds_eq [IsLawson α] (a : α) :
    𝓝 a = ⨅ b ∈ {b | b.Finite}, ⨅ S ∈ {S | IsOpen[scott α univ] S ∧ a ∈ S ∧ ∀ x ∈ b, ¬x ≤ a}, 𝓟 (S \ ↑(upperClosure b)) := by
  rw [(Topology.IsLawson.isTopologicalBasis α).eq_generateFrom, nhds_generateFrom]
  simp_rw [mem_setOf_eq, lawsonBasis, iInf_and]
  simp [iInf_comm (ι := Set α)]
  simp_rw [iInf_and]
  simp [iInf_comm (ι := Set α)]
  simp_rw [iInf_and]
  conv =>
    enter [1, 1, s]
    rw [iInf_comm]
    enter [1, _]
    rw [iInf_comm]
    enter [1, _]
    rw [iInf_comm]
    enter [1, _]
    rw [iInf_comm]
    enter [1, _]
    rw [iInf_comm]
    skip
  simp [iInf_comm (ι := Set α), iInf_and]

variable [AddCommMonoid α] [IsOrderedAddMonoid α]

/--
error: failed to synthesize
  IsBotZeroClass α

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in #synth IsBotZeroClass α

variable [IsBotZeroClass α]

example {α : Type*} [CompleteLinearOrder α] : ContinuousLattice α := by
  constructor
  ·
  -- eq_sSup_of_mlt := by
    -- have : ∀ (x y : α), x < y ↔ x ≪ y := by
    --   simp [MuchLT.mlt]
    --   intro x y
    --   constructor
    --   · intro h D hD hD'

    --   · intro h
    --     if x = ⊥ then
    --       subst_eqs
    --       simp_all
    --       if y = ⊥ then
    --         subst_eqs
    --         simp_all
    --         contrapose! h
    --         simp_all

    --         use {⊥}
    --         simp_all
    --         apply?
    --       else
    --         sorry
    --     if y = ⊥ then
    --       subst_eqs
    --       simp_all
    --       contrapose! h
    --       simp_all
    --       use {⊥}
    --       simp_all
    --       apply?
    --     specialize h (Iio y)
    --     simp_all

    intro x
    apply le_antisymm
    · simp [mlt_iff_le_sSup]

      simp_all [le_sSup_iff, upperBounds, le_of_mlt]
      intro y hy
      apply hy; clear hy
      rintro I h ⟨I_lower, I_nonempty, I_directed⟩
      specialize h (sSup I) ?_
      · intro a ha
        simp [le_sSup_iff]
        exact fun b a_1 ↦ le_of_eq_of_le rfl (a_1 ha)
      simp_all
      simp [le_sSup_iff] at h

      have {a b : α} : a = a ⊔ b ∨ b = a ⊔ b := by
        simp_all [left_eq_sup, right_eq_sup, le_total]

      have ⟨d, hd⟩ := I_nonempty
      have : d ≤ x := by apply h
      have := I_lower ?_ hd
      set z := sSup I
      have : z ∈ I := by
        simp [z]
        apply IsGreatest.csSup_mem
      apply I_lower _ this
      simp [z, le_sSup_iff, upperBounds]
      grind


      have hx : ∀ ⦃a : α⦄, a ≪ x → a ≤ x := by simp_all [le_of_mlt]
      simp_all

      -- conv at hx => enter [a]; rw [← not_imp_not]
      -- simp at hx
      -- simp [MuchLT.mlt] at hx

      obtain (h | h) := CompleteLinearOrder.le_total x y
      · simp_all
      convert_to x = y using 0
      · grind
      by_contra
      replace : y < x := by grind
      letI : DenselyOrdered α := sorry
      clear h
      contrapose! hy
      simp_all
      have ⟨q, hq₁, hq₂⟩ : ∃ q, y < q ∧ q < x := exists_between ‹_›
      use q
      simp_all
      simp [MuchLT.mlt]

      intro D hD h
      simp [le_sSup_iff] at h


      apply hy

      simp_all [MuchLT.mlt]
      apply hy
      simp_all [le_sSup_iff]
      intro D h₁ h₂
      sorry
    · simp_all [le_of_mlt]

-- omit [IsLawson α] [TopologicalLattice α] in
protected theorem Lawson.hasSum {f : ι → α} : HasSum f (⨆ S, ∑ i ∈ S, f i) := by
  simp [HasSum, Lawson.nhds_eq]
  intro I hI O hO h₁ h₂
  have ⟨hu, hu₁⟩ := (@Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (α := α) _ _ (scott α _) _ (@IsScott.mk _ _ _ (scott α _) rfl)).mp hO
  have : (⨆ s, ∑ b ∈ s, f b ∈ O) ↔ ∀ o, ⨆ s, ∑ b ∈ s, f b ≤ o → o ∈ O := by
    clear h₁ h₂
    simp_all
    constructor
    · simp_all [IsUpperSet]
      intro h₀
      intro o h'
      apply hu _ h₀
      simp_all
    · simp_all [IsUpperSet]
      intro h
      apply h
      simp_all [le_iSup_iff]
  simp_all
  simp [dirSupInacc_iff_forall_sSup] at hu₁

  let Q : Set ι := (fun x ↦ ⟨sorry, sorry⟩) ⁻¹' (Set.univ : Set I)

  simp [le_iSup_iff] at h₂

  induction I, hI using Set.Finite.induction_on with
  | empty =>
    simp_all
  | insert hiI hI ih =>
    rename_i i I
    simp_all
    obtain ⟨K, hK⟩ := ih
    have ⟨Q, hQ⟩ : ∃ Q, ¬i ≤ ∑ b ∈ Q, f b := sorry
    classical
    use K ∪ Q
    intro B hB
    have := hK (B ∪ Q) (by grind)
    split_ands
    · grind
    · contrapose hQ
      simp_all
      grw [hQ]
      gcongr
      · simp
      · sorry
    · grind
    simp_all

  have := (ContinuousLattice.eq_sSup_of_mlt (⨆ s, ∑ b ∈ s, f b)).le
  simp [le_sSup_iff, le_iSup_iff, iSup_le_iff, upperBounds] at this
  simp [MuchLT.mlt, le_sSup_iff, upperBounds] at this

  simp [dirSupInacc_iff_forall_sSup] at hu₁
  if I.Nonempty then
    specialize @hu₁ I ‹_›
  else
    have : I = ∅ := by grind [not_nonempty_iff_eq_empty]
    subst_eqs
    simp_all
    use {}
    simp
    intro B
    apply h₁
    simp


  obtain ⟨J, hJ₁, hJ₂⟩ : ∃ (J : Set α), J.Finite ∧ ∀ j ∈ J, (∀ (i : Finset ι), ∑ b ∈ i, f b ≤ j) ∧ ∃ i ∈ I, ¬i ≤ j := by
    use (fun ⟨i, hi⟩ ↦ (h₂ i hi).choose) '' (Set.univ : Set I)
    simp
    constructor
    · letI : Finite I := finite_coe_iff.mpr hI
      apply finite_range
    rintro j x hx ⟨_⟩
    have := (h₂ x hx).choose_spec
    simp_all
    grind

  sorry


  -- apply tendsto_atTop_iSup
  -- intro S T h
  -- simp
  -- gcongr
  -- · simp
  -- exact h

theorem Lawson.tsum_eq_iSup_sum_subset {f : ι → α} :
    ∑' i, f i = ⨆ (S : Finset ι), ∑ i ∈ S, f i := by
  rw [← Summable.hasSum_iff]
  · exact Lawson.hasSum
  · constructor; exact Lawson.hasSum

end
