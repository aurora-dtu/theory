import MDP.FinsetExt
import MDP.Scheduler
import MDP.SetExt

namespace MDP

variable {State : Type*} {Act : Type*}
variable (M : MDP State Act)

/-- Paths starting in `s` with length `n` -/
def Path_eq (n : ℕ) (s : State) := { π : M.Path | ‖π‖ = n ∧ π[0] = s }
/-- Paths starting in `s` with length at most `n` -/
def Path_le (n : ℕ) (s : State) := { π : M.Path | ‖π‖ ≤ n ∧ π[0] = s }

@[inherit_doc]
notation "Path[" M "," s "," "=" n "]" => MDP.Path_eq M n s
@[inherit_doc]
notation "Path[" M "," s "," "≤" n "]" => MDP.Path_le M n s

instance [DecidableEq State] : Decidable (π ∈ Path[M,s,=n]) := instDecidableAnd
instance [DecidableEq State] : Decidable (π ∈ Path[M,s,≤n]) := instDecidableAnd

namespace Path_eq

variable {M}
variable {n} {s}

section

variable (π : Path[M,s,=n])

@[simp] theorem length_pos : 0 < ‖π.val‖ := by have := π.val.length_ne_zero; omega
@[simp] theorem first_eq : π.val[0]'(by simp) = s := π.prop.right
@[simp] theorem length_eq : ‖π.val‖ = n := π.prop.left

@[simp] theorem iff (π) : π ∈ Path[M,s,=n] ↔ ‖π‖ = n ∧ π[0] = s := by simp [Path_eq]

end

instance : Subsingleton Path[M,s,=0] where
  allEq := fun ⟨a, _, _⟩ ⟨b, _, h⟩ ↦ by
    congr
    ext i
    · simp_all
    · have : i = 0 := by omega
      subst_eqs
      exact h.symm

@[simp]
theorem length_zero : Path[M,s,=0] = {} := by ext; simp
@[simp]
theorem length_one_singleton : Path[M,s,=1] = {{s}} := by
  ext
  simp
  constructor
  · intros; ext i
    · simp_all
    · simp_all [(by omega : i = 0)]
  · intro; subst_eqs; simp
@[simp]
theorem length_zero_tsum (f : Path[M,s,=0] → ENNReal) :
    ∑' π : Path[M,s,=0], f π = 0 := by simp
@[simp]
theorem length_zero_tsum_singleton (f : Path[M,s,=1] → ENNReal) :
    ∑' π : Path[M,s,=1], f π = f ⟨{s}, by simp⟩ := by
  rw [← tsum_singleton (f:=f)]
  apply tsum_eq_tsum_of_ne_zero_bij (fun ⟨π, _⟩ ↦ π)
  · intro _ _ _; simp_all; aesop
  · simp_all
  · simp

end Path_eq

namespace Path_le

variable {M}

theorem succs_univ_Finite [DecidableEq State] [M.FiniteBranching] (π : M.Path) :
    π.succs_univ.Finite := by
  simp [Path.succs_univ_eq_extend_range, Set.finite_range π.extend]
noncomputable instance [DecidableEq State] [M.FiniteBranching] (π : M.Path) : Fintype π.succs_univ
  := (succs_univ_Finite π).fintype

variable {n} {s}

@[simp] theorem length_pos (π : Path[M,s,≤n]) : 0 < ‖π.val‖ := by
  have := π.val.length_ne_zero
  omega
@[simp] theorem length_le (π : Path[M,s,≤n]) : ‖π.val‖ ≤ n := π.prop.left
@[simp] theorem first_le (π : Path[M,s,≤n]) : π.val[0] = s := π.prop.right

@[simp] theorem iff (π : M.Path) : π ∈ Path[M,s,≤n] ↔ ‖π‖ ≤ n ∧ π[0] = s := Set.mem_def

instance : Subsingleton Path[M,s,≤0] where
  allEq := fun ⟨a, _, _⟩ ⟨b, _, h⟩ ↦ by
    congr
    ext i
    · have : ‖a‖ = 1 := by have := a.length_pos; omega
      have : ‖b‖ = 1 := by have := b.length_pos; omega
      simp_all
    · have : i = 0 := by omega
      subst_eqs
      exact h.symm

theorem finite [DecidableEq State] [M.FiniteBranching] : Path[M,s,≤n].Finite :=
  match n with
  | 0 => Set.toFinite Path[M,s,≤0]
  | n + 1 => by
    induction n with
    | zero =>
      refine Set.Finite.ofFinset {{s}} fun π ↦ ?_
      constructor <;> simp_all
      rintro _ _
      have : ‖π‖ = 1 := by have := π.length_pos; omega
      ext <;> simp_all; simp_all
    | succ n ih =>
      apply Set.Finite.ofFinset (ih.toFinset ∪ ih.toFinset.biUnion (fun π ↦ π.succs_univ.toFinset))
      simp
      intro π
      constructor
      · intro h; rcases h with h | ⟨π', ⟨h, _, _⟩, h'⟩ <;> simp_all [Path.succs_univ]
        · omega
        · obtain ⟨⟨_, _⟩, _⟩ := h'; simp_all
      · simp_all
        intros
        subst_eqs
        if ‖π‖ ≤ n + 1 then omega else
        right
        use π.prev
        have : 1 < ‖π‖ := by omega
        simp_all [π.mem_prev_succs_univ (by omega)]

noncomputable instance [DecidableEq State] [M.FiniteBranching] : Fintype Path[M,s,≤n] :=
  finite.fintype

end Path_le

/-- The set of paths of the kind `s₀ s₁ ⋯ sₙ₊₁` -/
abbrev Path_eq_follows (s₀ : State) (n : ℕ) (s₁ : M.succs_univ s₀) : Set M.Path :=
  {π | ∃ h : π ∈ Path[M,s₀,=n+2], π[1]'(by simp_all) = s₁}

-- TODO: this notation is misleading because of the length
@[inherit_doc]
notation "Path[" M "," s₀ "─" s₁ "," "=" n "]" => Path_eq_follows M s₀ n s₁

theorem Path_eq_follows_disjoint : Set.univ.PairwiseDisjoint (Path[M,s₀─·,=n]) := by
  intro ⟨a, _⟩ _ ⟨b, _⟩ _ h S ha hb π h'
  have ⟨_, _⟩ := ha h'; have ⟨_, _⟩ := hb h'; simp_all

namespace Path_eq

theorem succs_univ_disjoint : Path[M,s,=n].PairwiseDisjoint Path.succs_univ := by
  simp [Set.PairwiseDisjoint_iff, iff, and_imp]
  intro x a b _ _ _ _ ha hb
  rw [←Path.mem_succs_univ_prev <| ha, ←Path.mem_succs_univ_prev <| hb]

theorem eq_biUnion_succs_univ : Path[M,s,=n+2] = ⋃ π : Path[M,s,=n+1], π.val.succs_univ := by
  ext π
  simp
  constructor
  · exact fun _ ↦ ⟨π.prev, by simp_all⟩
  · intro ⟨_, ⟨_, _⟩, h⟩
    simp [Path.succs_univ] at h
    obtain ⟨_, _⟩ := h
    subst_eqs
    have : ¬‖π‖ = 1 := by omega
    simp_all

theorem eq_succs_univ_biUnion : Path[M,s,=n+2] = ⋃ s', Path[M,s─s',=n] := by
  ext π
  simp
  constructor
  · simp_all; intro ⟨_, _⟩; subst_eqs; simp_all
  · simp_all

end MDP.Path_eq
