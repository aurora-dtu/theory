import Mathlib.Data.Set.Pairwise.Basic

/-!
# Extensions to `Set`

The intention is to upstream these to mathlib or to find and use similar existing theorems in
mathlib.
-/

theorem Set.PairwiseDisjoint_iff {S : Set α} {f : α → Set β} :
    S.PairwiseDisjoint f ↔ (∀ {x} {a b}, a ∈ S → b ∈ S → x ∈ f a → x ∈ f b → a = b) := by
  constructor
  · intro h x a b ha hb ha' hb'
    refine not_imp_comm.mp (h ha hb) fun h' ↦ h' (x:={x}) ?_ ?_ rfl <;> simp_all
  · intro h a ha b hb a_ne_b _ hSa hSb x hx
    exact a_ne_b (h ha hb (hSa hx) (hSb hx))
