import MDP.Paths.Defs

namespace MDP.Path

variable {State : Type*} {Act: Type*} {M  : MDP State Act}
variable (π : M.Path)

instance : Membership State M.Path where
  mem π s := ∃ i : Fin ‖π‖, π[i] = s

@[simp] theorem mem_states_iff_mem : s ∈ π.states ↔ s ∈ π := by
  simp [instMembership, List.mem_iff_getElem, Fin.exists_iff]

theorem mem_iff_getElem : s ∈ π ↔ ∃ i : Fin _, π[i] = s := Eq.to_iff rfl

@[simp] theorem getElem_mem (i : Fin ‖π‖) :
    π[i] ∈ π := by simp [instMembership]
@[simp] theorem getElem_nat_mem (i : ℕ) (hi : i < ‖π‖) :
    π[i] ∈ π := by simp [instMembership]; use ⟨i, hi⟩
@[simp] theorem last_mem (π : M.Path) :
    π.last ∈ π := by simp_all

instance [DecidableEq State] (s : State) : Decidable (∀ s' ∈ π, s' = s) :=
  if h : π.states.all (· = s) then .isTrue (by simp_all [instMembership])
  else .isFalse (by simp_all)

instance [DecidableEq State] (s : State) : Decidable (s ∈ π) :=
  if h : s ∈ π.states then .isTrue (by simp_all) else .isFalse (by simp_all)

@[simp]
theorem mem_extend (s : M.succs_univ π.last) (s' : State) : s' ∈ π.extend s ↔ s' ∈ π ∨ s = s' := by
  obtain ⟨s, hs⟩ := s; rw [← mem_states_iff_mem]; simp [extend, eq_comm]

@[simp]
theorem mem_singleton (s s' : State) : s ∈ (instSingleton  (M:=M)).singleton s' ↔ s = s' := by
  simp [instMembership]
  constructor <;> simp_all
  exact fun _ ↦ Fin.isSome_find_iff.mp rfl

end MDP.Path
