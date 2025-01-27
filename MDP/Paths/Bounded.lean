import MDP.Basic
import MDP.FinsetExt
import MDP.Paths.Prob
import MDP.Scheduler
import MDP.SetExt

namespace MDP

variable {State : Type*} {Act : Type*}
variable (M : MDP State Act)

def Path_eq (n : ℕ) (s : State) := { π : M.Path | π.length = n + 1 ∧ π[0] = s }
def Path_le (n : ℕ) (s : State) := { π : M.Path | π.length ≤ n + 1 ∧ π[0] = s }

notation "Path[" M "," s "," "=" n "]" => MDP.Path_eq M n s
notation "Path[" M "," s "," "≤" n "]" => MDP.Path_le M n s

instance [DecidableEq State] : Decidable (π ∈ Path[M,s,=n]) := instDecidableAnd
instance [DecidableEq State] : Decidable (π ∈ Path[M,s,≤n]) := instDecidableAnd

theorem length_ne_zero (π : M.Path) (h : π.length = 0) : False := by simp_all

namespace Path_eq

variable {M}
variable {n} {s}

section

variable (π : Path[M,s,=n])

@[simp] theorem length_pos : 0 < π.val.length := by
  have := π.val.length_ne_zero
  omega
@[simp] theorem first_eq : π.val[0]'(by simp) = s := π.prop.right
@[simp] theorem length_eq : π.val.length = n + 1 := π.prop.left

@[simp] theorem iff (π) : π ∈ Path[M,s,=n] ↔ π.length = n + 1 ∧ π[0] = s := by simp [Path_eq]

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
theorem length_zero_singleton : Path[M,s,=0] = {{s}} := by
  ext
  simp
  constructor
  · intros; ext i
    · simp_all
    · simp_all [(by omega : i = 0)]
  · intro; subst_eqs; simp
@[simp]
theorem length_zero_tsum_singleton (f : Path[M,s,=0] → ENNReal) :
    ∑' π : Path[M,s,=0], f π = f ⟨{s}, by simp⟩ := by
  rw [← tsum_singleton (f:=f)]
  apply tsum_eq_tsum_of_ne_zero_bij (fun ⟨π, _⟩ ↦ π)
  · intro _ _ _; simp_all; aesop
  · simp_all
  · simp

end Path_eq

namespace Path_le

variable {M}

instance [DecidableEq State] [M.FiniteBranching] (π : M.Path) : π.succs_univ.Finite := by
  simp [Path.succs_univ_eq_extend_succs_univ]
  refine Set.Finite.dependent_image ?hs fun x hx ↦ π.extend ⟨x, hx⟩
  exact M.instFiniteSuccs_univOfFiniteBranching
noncomputable instance [DecidableEq State] [M.FiniteBranching] (π : M.Path) : Fintype π.succs_univ
  := (instFinitePathSuccs_univOfDecidableEqOfFiniteBranching π).fintype

variable {n} {s}

@[simp] theorem length_pos (π : Path[M,s,≤n]) : 0 < π.val.length := by
  have := π.val.length_ne_zero
  omega
@[simp] theorem length_le (π : Path[M,s,≤n]) : π.val.length ≤ n + 1 := π.prop.left
@[simp] theorem first_le (π : Path[M,s,≤n]) : π.val[0] = s := π.prop.right

@[simp] theorem iff (π : M.Path) : π ∈ Path[M,s,≤n] ↔ π.length ≤ n + 1 ∧ π[0] = s := Set.mem_def

instance : Subsingleton Path[M,s,≤0] where
  allEq := fun ⟨a, _, _⟩ ⟨b, _, h⟩ ↦ by
    congr
    ext i
    · have : a.length = 1 := by have := a.length_pos; omega
      have : b.length = 1 := by have := b.length_pos; omega
      simp_all
    · have : i = 0 := by omega
      subst_eqs
      exact h.symm

instance instFinite [DecidableEq State] [M.FiniteBranching] : Path[M,s,≤n].Finite := by
  induction n with
  | zero => exact Set.toFinite Path[M,s,≤0]
  | succ n ih =>
    apply Set.Finite.ofFinset (ih.toFinset ∪ ih.toFinset.biUnion (fun π ↦ π.succs_univ.toFinset))
    simp
    intro π
    constructor
    · intro h; rcases h with h | ⟨π', ⟨h, h'⟩, h''⟩
      · simp_all
        omega
      · simp [Path.succs_univ] at h''
        obtain ⟨h'', h'''⟩ := h''
        subst_eqs
        simp_all
        split at h <;> simp_all
    · simp_all
      intros
      subst_eqs
      if π.length ≤ n + 1 then
        simp_all
      else
        right
        use π.prev
        have : ¬π.length = 1 := by omega
        simp_all [π.mem_prev_succs_univ (by omega)]

noncomputable instance [DecidableEq State] [M.FiniteBranching] : Fintype Path[M,s,≤n] :=
  instFinite.fintype

end Path_le

-- TODO: rename
abbrev wtf (s : State) (n : ℕ) (s' : M.succs_univ s) : Set M.Path :=
  -- {π' | ∃ h : π'.length = n + 2, π'[0] = s ∧ π'[1] = s'}
  {π | ∃ h : π ∈ Path[M,s,=n+1], π[1]'(by simp_all) = s'}

-- TODO: rename
theorem wtf_disjoint : Set.univ.PairwiseDisjoint (M.wtf s n) := by
  intro ⟨a, _⟩ _ ⟨b, _⟩ _ h S ha hb π h'
  have ⟨_, _⟩ := ha h'; have ⟨_, _⟩ := hb h'; simp_all

namespace Path_eq

theorem succs_univ_disjoint (s : State) (n : ℕ) : Path[M,s,=n].PairwiseDisjoint Path.succs_univ := by
  simp [Set.PairwiseDisjoin_iff, iff, and_imp]
  intro x a b _ _ _ _ ha hb
  rw [←Path.mem_succs_univ_prev <| ha, ←Path.mem_succs_univ_prev <| hb]

theorem eq_biUnion_succs_univ : Path[M,s,=n+1] = ⋃ π : Path[M,s,=n], π.val.succs_univ := by
  ext π
  simp
  constructor
  · exact fun _ ↦ ⟨π.prev, by simp_all⟩
  · intro ⟨_, ⟨_, _⟩, h⟩
    simp [Path.succs_univ] at h
    obtain ⟨_, _⟩ := h
    subst_eqs
    have : ¬π.length = 1 := by omega
    simp_all

theorem eq_succs_univ_biUnion :
    Path[M,s,=n+1] = ⋃ s' : M.succs_univ s, {π.val.prepend ⟨s, by simp⟩ | π : Path[M,s',=n]} := by
  ext π
  simp
  constructor
  · intro ⟨_, _⟩
    subst_eqs
    use π[1]
    simp_all
    use π.tail
    simp_all
  · simp_all
    intro s' hs' π' ⟨hπ', hπ''⟩ h'
    subst_eqs
    simp
    omega

theorem eq_succs_univ_biUnion' : Path[M,s,=n+1] = ⋃ s' : M.succs_univ s, M.wtf s n s' := by
  ext π
  simp
  constructor
  · simp_all; intro ⟨_, _⟩; subst_eqs; simp_all
  · simp_all

end Path_eq

variable {M}

namespace Scheduler'

@[mk_iff]
class IsBounded (𝒮 : M.Scheduler') (s : State) (n : ℕ) : Prop where
  isBounded : ∀ π, ¬π ∈ Path[M,s,≤n] → 𝒮 π = M.default_act π.last

end Scheduler'

def BScheduler' (M : MDP State Act) (s : State) (n : ℕ) := {𝒮 : M.Scheduler' // 𝒮.IsBounded s n}

namespace BScheduler'

noncomputable section

instance instDFunLike : DFunLike (M.BScheduler' s n) M.Path (fun _ ↦ Act) where
  coe ℬ π := ℬ.val π
  coe_injective' := by intro ⟨ℬ, _⟩ ⟨ℬ', _⟩ _; simp_all

@[simp] theorem mk_coe_apply (𝒮 : M.Scheduler') (h : 𝒮.IsBounded s n) (π : M.Path) :
  BScheduler'.instDFunLike.coe (⟨𝒮, h⟩) π = 𝒮 π := rfl

theorem default_on (ℬ : M.BScheduler' s n) {π : M.Path} (h : ¬π ∈ Path[M,s,≤n]) :
    ℬ π = M.default_act π.last := ℬ.prop.isBounded _ h

-- theorem asdf (𝒮 : M.Scheduler') (h : 𝒮.IsBounded s n) : (⟨𝒮, h⟩ : M.BScheduler' s n) π = 𝒮 π := sorry
@[simp] theorem coe_apply (ℬ : M.BScheduler' s n) : ℬ.val π = ℬ π := rfl

@[simp] theorem mem_act_if (ℬ : M.BScheduler' s n) : ℬ π ∈ M.act π.last := by
  cases ℬ; simp
@[simp] theorem tail_mem_act_if (ℬ : M.BScheduler' s n) {π : M.Path} : ℬ π.tail ∈ M.act π.last := by
  cases ℬ; simp

@[ext]
theorem ext {ℬ ℬ' : M.BScheduler' s n} (h : ∀ π ∈ Path[M,s,≤n], ℬ π = ℬ' π) : ℬ = ℬ' := by
  rcases ℬ with ⟨𝒮, h₁⟩; rcases ℬ' with ⟨𝒮', h₂⟩
  congr with π
  simp_all
  simp only [DFunLike.coe] at h
  simp only [Scheduler'.toFun_coe] at h
  if h' : π ∈ Path[M,s,≤n] then
    apply h <;> simp_all
  else
    rw [h₁.isBounded π h', h₂.isBounded π h']

variable [DecidableEq State]

def mk' (s) (n) (f : Path[M,s,≤n] → Act) (h : ∀π, f π ∈ M.act π.val.last) : M.BScheduler' s n :=
  ⟨⟨fun π ↦ if h : π ∈ Path[M,s,≤n] then f ⟨π, h⟩ else M.default_act π.last,
    fun π ↦ by simp; split <;> simp_all⟩, ⟨by simp_all⟩⟩

-- @[simp] theorem asdf : (¬π ∈ Path[M,s,≤n]) ↔ (¬π[0] = s) ∨ ¬π.length ≤ n + 1 := by
--   simp
--   constructor
--   · contrapose; simp_all
--   · intro h; cases h <;> simp_all

def specialize (ℬ : M.BScheduler' s (n + 1))  (_ : State) (s' : M.succs_univ s) : M.BScheduler' s' n
  := ⟨ℬ.val[s ↦ s'], ⟨fun π hπ ↦ by
    simp [Scheduler'.specialize]
    simp at hπ
    split_ifs
    · have := ℬ.default_on (π:=π.prepend ⟨s, by simp_all⟩) (by contrapose hπ; simp_all)
      simp_all
    · congr⟩⟩

@[simp]
theorem specialize_apply (ℬ : M.BScheduler' s (n + 1)) (s' : M.succs_univ s) (π : Path[M,s',≤n]) :
    ℬ[s ↦ s'] π = ℬ (π.val.prepend ⟨s, by simp_all⟩) := by
  simp [specialize, Scheduler'.specialize]

@[simp]
theorem specialize_apply' (ℬ : M.BScheduler' s (n + 1)) (π : M.Path) (s' : M.succs_univ s) :
    ℬ[s ↦ s'] π = if h : π ∈ Path[M,s',≤n] then ℬ (π.prepend ⟨s, by simp_all⟩) else M.default_act π.last := by
  split_ifs with h
  · apply ℬ.specialize_apply s' ⟨π, h⟩
  · apply default_on _ h

end end BScheduler'

variable [DecidableEq State]

noncomputable def Scheduler'.bound (𝒮 : M.Scheduler') {s : State} {n : ℕ} : M.BScheduler' s n :=
  ⟨⟨fun π ↦ if π ∈ Path[M,s,≤n] then 𝒮 π else M.default_act π.last,
    fun π ↦ by simp; split_ifs <;> simp⟩,
    by simp [Scheduler'.isBounded_iff]; intros; simp_all⟩

@[simp]
theorem Scheduler'.bound_coe_apply (𝒮 : M.Scheduler') (s : State) (n : ℕ) (π : M.Path) :
    (𝒮.bound (n:=n) (s:=s)) π = if π ∈ Path[M,s,≤n] then 𝒮 π else M.default_act π.last := rfl

omit [DecidableEq State] in
theorem Prob_eq_if (π : M.Path) (h : ∀ π' : Path[M,π[0],≤π.length], 𝒮 π' = 𝒮' π') :
    π.Prob 𝒮 = π.Prob 𝒮' := by simp_all [Path.Prob]

namespace BScheduler'

noncomputable section

def cast_arb (ℬ : M.BScheduler' s n) : M.BScheduler' s' m := ℬ.val.bound
def cast_arb_tail (ℬ : M.BScheduler' s n) : M.BScheduler' s' (n + 1) :=
  Scheduler'.mk' (fun π ↦ ⟨ℬ π.tail, by have := ℬ.val.property' π.tail; simp_all⟩) |>.bound

@[simp]
theorem cast_arb_tail_specialize (s' : M.succs_univ s) (ℬ : M.BScheduler' s' n) :
    ℬ.cast_arb_tail.specialize s s' = ℬ := by
  ext π hπ
  simp [cast_arb_tail]
  split_ifs <;> simp_all

instance : Coe M.Scheduler' (M.BScheduler' s n) where
  coe := (·.bound)

instance : Inhabited (M.BScheduler' s n) where
  default := ⟨default, ⟨fun π _ ↦ by congr⟩⟩

def FiniteScheduler [M.FiniteBranching] (s : State) (n : ℕ) := (π : Path[M,s,≤n]) → M.act₀ π.val.last

instance [DecidableEq State] [M.FiniteBranching] : Fintype (FiniteScheduler (M:=M) s n) := by
  unfold FiniteScheduler
  apply Pi.instFintype

instance [M.FiniteBranching] : Finite (M.BScheduler' s n) := by
  refine (Equiv.finite_iff (β:=BScheduler'.FiniteScheduler (M:=M) s n) ?_).mpr (Finite.of_fintype _)
  · apply Equiv.ofBijective fun 𝒮 ↦ fun π ↦ ⟨𝒮 π, by simp⟩
    constructor
    · intro a b h
      ext π hπ
      have := congrFun h ⟨π, hπ⟩
      simp_all
    · intro a
      simp_all
      use Scheduler'.mk' fun π ↦ if h : π ∈ Path[M,s,≤n] then ⟨a ⟨π, h⟩, by
        have := (a ⟨π, h⟩).prop
        simp_all [-Finset.coe_mem]⟩ else default
      simp
instance [M.FiniteBranching] : Fintype (M.BScheduler' s n) :=
  Fintype.ofFinite (M.BScheduler' s n)
instance [M.FiniteBranching] : Nonempty (M.BScheduler' s n) :=
  instNonemptyOfInhabited

def elems [M.FiniteBranching] : Finset (M.BScheduler' s n) :=
  (inferInstance : Fintype (M.BScheduler' s n)).elems

@[simp] theorem elems_mem [M.FiniteBranching] :
  ℬ ∈ elems (M:=M) (s:=s) (n:=n) := by simp [elems, Fintype.complete]
@[simp] theorem elems_nonempty [M.FiniteBranching] :
  (elems (M:=M) (s:=s) (n:=n)).Nonempty := by use default; simp

@[simp]
theorem mk'_specialize (f : Path[M,s,≤n+1] → Act) (h : ∀π, f π ∈ M.act π.val.last) :
    (mk' s _ f h)[s ↦ s']
  = mk' (M:=M) s' n (f ⟨·.val.prepend ⟨s, by simp⟩, by simp⟩)
      (by have := h ⟨·.val.prepend ⟨s, by simp⟩, by simp⟩; simp_all)
:= by ext π hπ; simp_all [mk']

variable [M.FiniteBranching] in
theorem mk'_argmin (s : State) (s' : M.succs_univ s) (f : M.BScheduler' s' n → ENNReal) :
  mk' (M:=M) s' (n:=n)
    (fun π ↦ elems.argmin (by simp) f π)
    (by simp)
  = elems.argmin (by simp) f
:= by ext π hπ; simp_all [mk']
