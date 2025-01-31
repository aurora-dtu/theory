import MDP.Paths.Bounded

variable {State : Type*} {Act : Type*}
variable {M : MDP State Act}

namespace MDP

namespace Scheduler

@[mk_iff]
class IsBounded (𝒮 : 𝔖[M]) (s : State) (n : ℕ) : Prop where
  isBounded : ∀ π, ¬π ∈ Path[M,s,≤n] → 𝒮 π = M.default_act π.last

end Scheduler

/-- A (potentially) history dependent scheduler, bounded to paths in `Path[M,s,≤n]`. -/
def BScheduler (M : MDP State Act) (s : State) (n : ℕ) := {𝒮 : 𝔖[M] // 𝒮.IsBounded s n}

@[inherit_doc]
notation "𝔖[" M "," s "," "≤" n "]" => BScheduler M s n

namespace BScheduler

noncomputable section

instance instDFunLike : DFunLike 𝔖[M,s,≤n] M.Path (fun _ ↦ Act) where
  coe ℬ π := ℬ.val π
  coe_injective' := by intro ⟨ℬ, _⟩ ⟨ℬ', _⟩ _; simp_all

@[simp] theorem mk_coe_apply (𝒮 : 𝔖[M]) (h : 𝒮.IsBounded s n) (π : M.Path) :
  BScheduler.instDFunLike.coe (⟨𝒮, h⟩) π = 𝒮 π := rfl

theorem default_on (ℬ : 𝔖[M,s,≤n]) {π : M.Path} (h : ¬π ∈ Path[M,s,≤n]) :
    ℬ π = M.default_act π.last := ℬ.prop.isBounded _ h

@[simp] theorem coe_apply (ℬ : 𝔖[M,s,≤n]) : ℬ.val π = ℬ π := rfl

@[simp] theorem mem_act_if (ℬ : 𝔖[M,s,≤n]) : ℬ π ∈ M.act π.last := by
  cases ℬ; simp
@[simp] theorem tail_mem_act_if (ℬ : 𝔖[M,s,≤n]) {π : M.Path} : ℬ π.tail ∈ M.act π.last := by
  cases ℬ; simp

@[ext]
theorem ext {ℬ ℬ' : 𝔖[M,s,≤n]} (h : ∀ π ∈ Path[M,s,≤n], ℬ π = ℬ' π) : ℬ = ℬ' := by
  rcases ℬ with ⟨𝒮, h₁⟩; rcases ℬ' with ⟨𝒮', h₂⟩
  congr with π
  simp_all
  simp only [DFunLike.coe] at h
  simp only [Scheduler.toFun_coe] at h
  if h' : π ∈ Path[M,s,≤n] then
    apply h <;> simp_all
  else
    rw [h₁.isBounded π h', h₂.isBounded π h']

variable [DecidableEq State]

def mk' (s) (n) (f : Path[M,s,≤n] → Act) (h : ∀π, f π ∈ M.act π.val.last) : 𝔖[M,s,≤n] :=
  ⟨⟨fun π ↦ if h : π ∈ Path[M,s,≤n] then f ⟨π, h⟩ else M.default_act π.last,
    fun π ↦ by simp; split <;> simp_all⟩, ⟨by simp_all⟩⟩

def specialize (ℬ : 𝔖[M,s,≤n+1])  (_ : State) (s' : M.succs_univ s) : 𝔖[M,s',≤n]
  := ⟨ℬ.val[s ↦ s'], ⟨fun π hπ ↦ by
    simp [Scheduler.specialize]
    simp at hπ
    split_ifs
    · have := ℬ.default_on (π:=π.prepend ⟨s, by simp_all⟩) (by contrapose hπ; simp_all)
      simp_all
    · congr⟩⟩

@[simp]
theorem specialize_apply (ℬ : 𝔖[M,s,≤n+1]) (s' : M.succs_univ s) (π : Path[M,s',≤n]) :
    ℬ[s ↦ s'] π = ℬ (π.val.prepend ⟨s, by simp_all⟩) := by
  simp [specialize, Scheduler.specialize]

@[simp]
theorem specialize_apply' (ℬ : 𝔖[M,s,≤n+1]) :
    ℬ[s ↦ s'] π = if h : π ∈ Path[M,s',≤n] then ℬ (π.prepend ⟨s, by simp_all⟩)
                                           else M.default_act π.last := by
  split_ifs with h
  · apply ℬ.specialize_apply s' ⟨π, h⟩
  · apply default_on _ h

end end BScheduler

variable [DecidableEq State]

noncomputable def Scheduler.bound (𝒮 : 𝔖[M]) {s : State} {n : ℕ} : 𝔖[M,s,≤n] :=
  ⟨⟨fun π ↦ if π ∈ Path[M,s,≤n] then 𝒮 π else M.default_act π.last,
    fun π ↦ by simp; split_ifs <;> simp⟩,
    by simp [Scheduler.isBounded_iff]; intros; simp_all⟩

@[simp]
theorem Scheduler.bound_coe_apply (𝒮 : 𝔖[M]) (s : State) (n : ℕ) (π : M.Path) :
    (𝒮.bound (n:=n) (s:=s)) π = if π ∈ Path[M,s,≤n] then 𝒮 π else M.default_act π.last := rfl

namespace BScheduler

noncomputable section

def cast_arb (ℬ : 𝔖[M,s,≤n]) : 𝔖[M,s',≤m] := ℬ.val.bound
def cast_arb_tail (ℬ : 𝔖[M,s,≤n]) : 𝔖[M,s',≤n+1] :=
  Scheduler.mk' (fun π ↦ ⟨ℬ π.tail, by have := ℬ.val.property π.tail; simp_all⟩) |>.bound

@[simp]
theorem cast_arb_tail_specialize (s' : M.succs_univ s) (ℬ : 𝔖[M,s',≤n]) :
    ℬ.cast_arb_tail.specialize s s' = ℬ := by
  ext π hπ
  simp [cast_arb_tail]
  split_ifs <;> simp_all

instance : Coe 𝔖[M] 𝔖[M,s,≤n] where
  coe := (·.bound)

instance : Inhabited 𝔖[M,s,≤n] where
  default := ⟨default, ⟨fun π _ ↦ by congr⟩⟩

def FiniteMScheduler [M.FiniteBranching] s n := (π : Path[M,s,≤n]) → M.act₀ π.val.last

instance [DecidableEq State] [M.FiniteBranching] : Fintype (FiniteMScheduler (M:=M) s n) := by
  unfold FiniteMScheduler
  apply Pi.instFintype

instance [M.FiniteBranching] : Finite 𝔖[M,s,≤n] := by
  refine (Equiv.finite_iff (β:=BScheduler.FiniteMScheduler (M:=M) s n) ?_).mpr (Finite.of_fintype _)
  refine Equiv.ofBijective (fun 𝒮 ↦ fun π ↦ ⟨𝒮 π, by simp⟩) ⟨fun a b h ↦ ?_, fun a ↦ ?_⟩
  · ext π hπ; have := congrFun h ⟨π, hπ⟩; simp_all
  · simp_all
    use Scheduler.mk' fun π ↦ if h : π ∈ Path[M,s,≤n] then ⟨a ⟨π, h⟩, by
      have := (a ⟨π, h⟩).prop
      simp_all [-Finset.coe_mem]⟩ else default
    simp
instance [M.FiniteBranching] : Fintype 𝔖[M,s,≤n] :=
  Fintype.ofFinite 𝔖[M,s,≤n]
instance [M.FiniteBranching] : Nonempty 𝔖[M,s,≤n] :=
  instNonemptyOfInhabited

def elems [M.FiniteBranching] : Finset 𝔖[M,s,≤n] :=
  (inferInstance : Fintype 𝔖[M,s,≤n]).elems

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
theorem mk'_argmin (s : State) (s' : M.succs_univ s) (f : 𝔖[M,s',≤n] → ENNReal) :
  mk' (M:=M) s' (n:=n) (fun π ↦ elems.argmin (by simp) f π) (by simp) = elems.argmin (by simp) f
:= by ext π hπ; simp_all [mk']

end

end MDP.BScheduler
