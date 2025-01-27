import Mathlib.Data.Finset.Image
-- import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Defs

def DisjointOn {α β : Type*} [DecidableEq β] (f : α → Set β) := ∀ a b, a ≠ b → Disjoint (f a) (f b)
def DisjointOn₀ {α β : Type*} [DecidableEq β] (f : α → Finset β) := ∀ a b, a ≠ b → Disjoint (f a) (f b)

namespace Finset

variable {α ι : Type*}
variable [DecidableEq α] [DecidableEq ι]

theorem sum_singleton_attach {α : Type*} {β : Type*} [AddCommMonoid β] (y : α) (f : { x // x ∈ ({y} : Finset α) } → β) : ∑ x ∈ ({y} : Finset α).attach, f x = f ⟨y, by simp⟩ := by
  refine Finset.sum_unique_nonempty ({y} : Finset α).attach f ?h
  simp

theorem filterMap_insert (g : ι → Option α) (h : ∀ (a a' : ι), ∀ b ∈ g a, b ∈ g a' → a = a') (S : Finset ι) (x : ι) :
  (insert x S).filterMap g h = match g x with | some y => insert y (S.filterMap g h) | none => (S.filterMap g h)
:= by
  ext x
  split
  · simp_all
    constructor
    · simp_all
      intro h
      rcases h with h | ⟨y, h, h'⟩
      · subst_eqs
        simp
      · right
        use y
    · simp_all
      intro h
      rcases h with h | h
      · subst_eqs
        simp
      · simp_all
  · simp_all

theorem sum_filterMap {β : Type*} [AddCommMonoid β] (f : α → β) (g : ι → Option α) (h : ∀ (a a' : ι), ∀ b ∈ g a, b ∈ g a' → a = a') (S : Finset ι) :
  ∑ x ∈ S.filterMap g h, f x = ∑ x ∈ S,
    match g x with
    | some y => f y
    | none => 0
:= by
  induction S using Finset.induction with
  | empty => simp
  | insert hS' ih =>
    simp [filterMap_insert]
    split
    · simp_all
      rename_i i S' _ y h'
      by_cases hy : y ∈ filterMap g S' h
      · simp_all
        simp [←ih]
        obtain ⟨i', hi, hi'⟩ := hy
        have := h i i' y h' hi'
        simp_all
      · simp_all
    · simp_all

theorem sum_biUnion_attach {ι α β : Type*} [DecidableEq α] [AddCommMonoid β] {S : Finset ι} {f : S → Finset α} (hf' : DisjointOn₀ f) (g : { x : α // ∃ a : S, x ∈ f a } → β) : ∑ x ∈ (S.attach.biUnion f).attach, g ⟨x, by
  have := x.prop
  simp only [mem_biUnion, mem_attach, true_and, Subtype.exists] at this
  apply SetCoe.exists.mpr this
  ⟩ = ∑ x ∈ S.attach, ∑ y ∈ (f x).attach, g ⟨y, by
  use x, coe_mem y⟩
:= by
  have := sum_biUnion (s:=S.attach) (f:=g) (t:=fun x ↦
    (f x).attach.map ⟨fun y ↦ (⟨y.val, by use x, coe_mem y⟩ : { x // ∃ a : S, x ∈ f a }), by
      intro _ _ h
      simp at h
      exact SetCoe.ext h⟩)
  simp only [sum_map, Function.Embedding.coeFn_mk] at this
  rw [←this]
  · symm
    fapply sum_nbij (fun ⟨x, hx⟩ ↦ ⟨x, by simp ; exact Subtype.exists'.mpr hx⟩)
    · simp_all
    · simp_all only [coe_biUnion, mem_coe, mem_attach, coe_map,
      Function.Embedding.coeFn_mk, Set.iUnion_true]
      intro ⟨x, hx⟩ _
      simp_all
    · simp_all only [coe_biUnion, mem_coe, mem_attach, coe_map,
      Function.Embedding.coeFn_mk, Set.iUnion_true]
      intro ⟨x, hx⟩ _
      simp_all only [mem_coe, mem_attach, Set.mem_image, Set.mem_iUnion, true_and,
        Subtype.exists, Subtype.mk.injEq, exists_prop, exists_eq_right, exists_and_left,
        and_self_left]
      simp only [mem_biUnion, mem_attach, true_and, Subtype.exists] at hx
      exact hx
    · simp_all
  · intro x₁ _ x₂ _ h
    have f_disjoint := hf' x₁ x₂ h
    intro S hS₁ hS₂ y h'
    simp_all only [mem_coe, mem_attach, ne_eq, le_eq_subset, bot_eq_empty, not_mem_empty]
    have h'₁ := hS₁ h'
    have h'₂ := hS₂ h'
    simp at h'₁ h'₂
    obtain ⟨a₁, b₁, h'₁⟩ := h'₁
    obtain ⟨a₂, b₂, h'₂⟩ := h'₂
    absurd Disjoint.forall_ne_finset f_disjoint b₁ b₂
    rw [←h'₂] at h'₁
    simp at h'₁
    assumption

theorem filter_pair {α : Type u_1} [DecidableEq α] (p : α → Prop) [DecidablePred p] (a b : α) :
  filter p {a, b} = if p a ∧ p b then {a, b} else if p a then {a} else if p b then {b} else ∅
:= by
  simp only [filter_insert, filter_singleton]
  by_cases p a
  · simp_all only [ite_true, true_and, ite_false]
    by_cases p b
    · simp_all only [ite_true]
    · simp_all only [ite_false, insert_empty]
  · simp_all only [ite_false, false_and]

theorem filterMap_singleton {α β : Type*} {f : α → Option β} {hf : ∀ (a a' : α), ∀ b ∈ f a, b ∈ f a' → a = a'} (a : α) :
  ({a} : Finset α).filterMap f hf = match f a with | some b => {b} | none => {}
:= by
  ext B
  simp
  split
  · simp_all
    exact eq_comm
  · simp_all

theorem filterMap_pair {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → Option β} {hf : ∀ (a a' : α), ∀ b ∈ f a, b ∈ f a' → a = a'} (a a' : α) :
  ({a, a'} : Finset α).filterMap f hf =
    match (f a, f a') with
    | (some b, some b') => {b, b'}
    | (none, some b')   => {b'}
    | (some b, none)    => {b}
    | (none, none) => {}
:= by
  ext B
  simp only [mem_filterMap, mem_insert, mem_singleton, exists_eq_or_imp, exists_eq_left]
  split
  · simp_all
    apply or_congr eq_comm eq_comm
  · simp_all [eq_comm]
  · simp_all [eq_comm]
  · simp_all

theorem biUnion_ite_eq {α β : Type*} [DecidableEq α] [DecidableEq β] (s : Finset α) (a : α) (f : α → Finset β) : (s.biUnion fun i ↦ if i = a then f i else ∅) = if a ∈ s then f a else ∅ := by
  apply subset_antisymm <;> by_cases h : a ∈ s
  · simp_all
    intro x _
    by_cases h' : x = a
    · simp [h']
    · simp [h']
  · intro y
    simp_all
    intro x hx
    have : x ≠ a := by
      intro q
      simp_all only
    simp_all
  · simp_all
    intro x hx
    simp_all
    use a, h
    simp [hx]
  · simp_all

section argmin

variable {α β : Type*}
variable (S : Finset α) (hS : S.Nonempty) (f : α → β)
variable [LinearOrder β]

noncomputable def argmin : α := (S.exists_mem_eq_inf' hS f).choose
noncomputable def argmin_spec : S.argmin hS f ∈ S ∧ S.inf' hS f = f (S.argmin hS f) := (S.exists_mem_eq_inf' hS f).choose_spec

@[simp]
theorem argmin_le (a : α) (ha : a ∈ S) : f (S.argmin hS f) ≤ f a := by
  rw [←(S.argmin_spec hS f).right, inf'_le_iff]
  use a

@[simp]
theorem argmin_mem : S.argmin hS f ∈ S := (S.argmin_spec hS f).left
@[simp]
theorem toFinset_argmin_mem (S : Set α) [Fintype S] (hS : S.toFinset.Nonempty) : S.toFinset.argmin hS f ∈ S :=
  Set.mem_toFinset.mp (S.toFinset.argmin_spec hS f).left

end argmin
