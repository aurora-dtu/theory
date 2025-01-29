import MDP.Paths.Defs

namespace MDP

variable {State : Type*} {Act : Type*}

structure Scheduler' (M : MDP State Act) where
  toFun : M.Path → Act
  property' : ∀ π : M.Path, toFun π ∈ M.act π.last

namespace Scheduler'

variable {M : MDP State Act}

def mk' (𝒮 : (π : M.Path) → M.act π.last) : M.Scheduler' := ⟨fun π ↦ 𝒮 π, by simp⟩

instance : DFunLike M.Scheduler' M.Path (fun _ ↦ Act) where
  coe 𝒮 := 𝒮.toFun
  coe_injective' := by
    intro a b
    cases a ; cases b
    simp_all only [implies_true]

@[simp]
theorem toFun_coe (𝒮 : M.Scheduler') (π : M.Path) : 𝒮.toFun π = 𝒮 π := by simp [DFunLike.coe]

@[simp]
theorem toFun_coe' (π : M.Path) : (⟨f, h⟩ : M.Scheduler') π = f π := by simp only [DFunLike.coe]

@[simp]
theorem mem_act_if (𝒮 : M.Scheduler') (h : π.last = s) : 𝒮 π ∈ M.act s := by
  simp only [𝒮.property' π, h.symm, DFunLike.coe]

@[simp]
theorem singleton_mem_act (𝒮 : M.Scheduler') : 𝒮 {s} ∈ M.act s := by
  simp

@[simp]
theorem mem_act (𝒮 : M.Scheduler') : 𝒮 π ∈ M.act π.last := by
  simp

theorem mem_prepend (𝒮 : M.Scheduler') (π : M.Path) (s₀ : M.prev_univ π[0]) :
    𝒮 (π.prepend s₀) ∈ M.act π.last := by simp

@[ext]
theorem ext {𝒮 𝒮' : M.Scheduler'} (h : ∀ π, 𝒮 π = 𝒮' π) : 𝒮 = 𝒮' := by
  cases 𝒮 ; cases 𝒮'
  simp_all [DFunLike.coe]
  apply (Set.eqOn_univ _ _).mp fun ⦃x⦄ _ ↦ h x

def IsMarkovian {M : MDP State Act} (𝒮 : M.Scheduler') : Prop := ∀ π, 𝒮 π = 𝒮 {π.last}

@[mk_iff]
class Markovian {M : MDP State Act} (𝒮 : M.Scheduler') : Prop where
  intro : (∀ π, 𝒮 π = 𝒮 {π.last})

theorem MarkovianOn (𝒮 : M.Scheduler') [inst : Markovian 𝒮] (π : M.Path) :
    𝒮 π = 𝒮 {π.last} := inst.intro π

@[simp]
theorem Markovian_path_take (𝒮 : M.Scheduler') [𝒮.Markovian] (π : M.Path) (i : Fin ∎|π|) :
    𝒮 (π.take i) = 𝒮 {π[i]} := by simp [MarkovianOn]

theorem singleton_last (s : State) : ({s} : M.Path).last = s := by simp

@[simp]
theorem Markovian_path_take' (𝒮 : M.Scheduler') [𝒮.Markovian] (π : M.Path) (i : ℕ) (hi : i < ∎|π|) :
    𝒮 (π.take i) = 𝒮 {π[i]} := by simp [MarkovianOn, hi]

@[simp]
theorem Markovian_path_take'' (𝒮 : M.Scheduler') [𝒮.Markovian] (π : M.Path) (i : Fin ∎|π|) :
    𝒮 (π.take i) = 𝒮 {π[i]} := by simp [𝒮.MarkovianOn (π.take i), Fin.getElem_fin]

@[simp]
theorem Markovian_path_take''' (𝒮 : M.Scheduler') [𝒮.Markovian] (π : M.Path) (i : Fin (∎|π| - 1)) :
    𝒮 (π.take i) = 𝒮 {π[i]} := by simp [𝒮.MarkovianOn (π.take i), Fin.getElem_fin]

end Scheduler'

def Scheduler (M : MDP State Act) := { 𝒮 : M.Scheduler' // 𝒮.Markovian }

namespace Scheduler

variable {M : MDP State Act}

noncomputable instance : Inhabited M.Scheduler' :=
  ⟨fun _ ↦ M.default_act _, fun _ ↦ M.default_act_spec _⟩

noncomputable instance : Inhabited M.Scheduler := ⟨default, ⟨fun _ ↦ rfl⟩⟩

@[coe]
def toScheduler' : M.Scheduler → M.Scheduler' := Subtype.val

instance : Coe M.Scheduler M.Scheduler' := ⟨toScheduler'⟩

instance (𝒮 : M.Scheduler) : Scheduler'.Markovian (𝒮 : M.Scheduler') := 𝒮.prop

@[simp, norm_cast] lemma coe_mk (μ : M.Scheduler') (hμ) : toScheduler' ⟨μ, hμ⟩ = μ := rfl

@[simp]
theorem val_eq_to_scheduler' (ν : M.Scheduler) : ν.val = (ν : M.Scheduler') := rfl

theorem toScheduler'_injective : Function.Injective ((↑) : M.Scheduler → M.Scheduler') :=
  Subtype.coe_injective

instance instFunLike : FunLike M.Scheduler M.Path Act where
  coe 𝒮 π := (𝒮 : M.Scheduler') π
  coe_injective' _ _ h := toScheduler'_injective (Scheduler'.ext <| congrFun h)

def mk' (f : (s : State) → Act) (hf : ∀s, f s ∈ M.act s) : M.Scheduler
  := ⟨⟨fun π ↦ f π.last, fun π ↦ hf π.last⟩, (Scheduler'.markovian_iff _).mpr fun _ ↦ rfl⟩

variable {𝒮 : M.Scheduler}

theorem markovian (π : M.Path) : 𝒮 π = 𝒮 {π.last} :=
  𝒮.prop.intro π

@[simp] theorem mem_act' (π : M.Path) :
    𝒮 π ∈ M.act π.last := by
  obtain ⟨𝒮, h𝒮⟩ := 𝒮
  simp only [DFunLike.coe]
  simp

@[simp]
theorem prepend {π : M.Path} (s : M.prev_univ π[0]) : 𝒮 (π.prepend s) = 𝒮 π := by
  have := 𝒮.markovian π |>.symm
  have := 𝒮.markovian (π.prepend ⟨s, by simp_all⟩)
  simp_all

@[simp]
theorem toScheduler'_apply : 𝒮.toScheduler' π = 𝒮 π := rfl

-- @[simp]
-- theorem toScheduler'_prepend : 𝒮.toScheduler' (({s} : M.Path).prepend s') = 𝒮 {s} :=
--   by simp

end Scheduler

variable {M : MDP State Act}

@[simp]
theorem P_tsum_one_iff_Scheduler (𝒮 : M.Scheduler') :
    ∑' (s' : (M.P s (𝒮 {s})).support), M.P s (𝒮 {s}) s' = 1 :=
  M.P_tsum_support_one_iff.mpr (Scheduler'.singleton_mem_act 𝒮)

@[simp]
theorem Path.P_tsum_one_iff_Scheduler (𝒮 : M.Scheduler') :
    ∑' (s' : (M.P π.last (𝒮 π)).support), M.P π.last (𝒮 π) s' = 1 :=
  M.P_tsum_support_one_iff.mpr (Scheduler'.mem_act 𝒮)

@[simp]
theorem Scheduler'.mk'_coe {𝒮 : (π : M.Path) → M.act π.last} (π : M.Path) :
    (Scheduler'.mk' 𝒮) π = (𝒮 π).val := by simp [mk']

/-- Specialize a scheduler such that all scheduled paths are considered with a given state as the
    immediately predecessor. -/
noncomputable def Scheduler'.specialize [DecidableEq State] (𝒮 : M.Scheduler')
    (s₀ : State) (s₀' : M.succs_univ s₀) : M.Scheduler' :=
  Scheduler'.mk' fun π ↦ if h : π[0] = s₀' then ⟨𝒮 (π.prepend ⟨s₀, by simp_all⟩), by simp⟩
                         else default

syntax:max term noWs "[" withoutPosition(term) " ↦ " withoutPosition(term) "]" : term
@[inherit_doc Scheduler'.specialize]
macro_rules | `($x[$i ↦ $j]) => `(($x).specialize $i $j)
syntax:max term noWs "[" withoutPosition(term) " ↦ " withoutPosition(term) "]'" term:max : term
macro_rules | `($x[$i ↦ $j]'$p) => `(($x).specialize $i ⟨$j, $p⟩)

variable [DecidableEq State] {𝒮 : M.Scheduler'}

@[simp]
theorem Scheduler'.specialize_apply :
    𝒮[s ↦ s'] π = if h : π[0] = s' then 𝒮 (π.prepend ⟨s, by simp_all⟩) else M.default_act π.last
:= by
  simp [specialize]; apply apply_dite

@[simp]
theorem Scheduler'.specialize_tail_take (π : M.Path)
  (h : 1 < ∎|π|) :
    𝒮[π[0] ↦ ⟨π[1], by simp⟩] (π.tail.take i) = 𝒮 (π.take (i + 1)) := by
  simp [Nat.ne_of_lt' h, Path.take_prepend, π.tail_prepend h]

@[simp]
theorem Scheduler'.specialize_default_on {π : M.Path}
    {s' : M.succs_univ s} (h : ¬π[0] = ↑s') : 𝒮[s ↦ s'] π = M.default_act π.last := by
  simp [h]

theorem Scheduler.toScheduler'_specialize (𝒮 : M.Scheduler) :
      (𝒮.toScheduler'.specialize s s')
    = ⟨fun π ↦ if π[0] = ↑s' then 𝒮 π else M.default_act π.last,
       fun π ↦ by simp; split_ifs <;> simp⟩ := by
  ext π; simp

end MDP
