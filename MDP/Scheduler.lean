import MDP.Paths.Defs

namespace MDP

variable {State : Type*} {Act : Type*}
variable {M : MDP State Act}

/-- A (potentially) history dependent scheduler. -/
structure Scheduler (M : MDP State Act) where
  toFun : M.Path → Act
  property : ∀ π : M.Path, toFun π ∈ M.act π.last

@[inherit_doc]
notation "𝔖[" M "]" => Scheduler M

namespace Scheduler

def mk' (𝒮 : (π : M.Path) → M.act π.last) : 𝔖[M] := ⟨fun π ↦ 𝒮 π, by simp⟩

instance : DFunLike 𝔖[M] M.Path (fun _ ↦ Act) where
  coe 𝒮 := 𝒮.toFun
  coe_injective' := by
    intro a b
    cases a ; cases b
    simp_all only [implies_true]

@[simp]
theorem toFun_coe (𝒮 : 𝔖[M]) (π : M.Path) : 𝒮.toFun π = 𝒮 π := by simp [DFunLike.coe]

@[simp]
theorem toFun_coe' (π : M.Path) : (⟨f, h⟩ : 𝔖[M]) π = f π := by simp only [DFunLike.coe]

@[simp]
theorem mem_act_if (𝒮 : 𝔖[M]) (h : π.last = s) : 𝒮 π ∈ M.act s := by
  simp only [𝒮.property π, h.symm, DFunLike.coe]

@[simp] theorem singleton_mem_act (𝒮 : 𝔖[M]) (s : State) : 𝒮 {s} ∈ M.act s := by simp

@[simp] theorem mem_act (𝒮 : 𝔖[M]) (π : M.Path) : 𝒮 π ∈ M.act π.last := by simp

theorem mem_prepend (𝒮 : 𝔖[M]) (π : M.Path) (s₀ : M.prev_univ π[0]) :
    𝒮 (π.prepend s₀) ∈ M.act π.last := by simp

@[ext]
theorem ext {𝒮 𝒮' : 𝔖[M]} (h : ∀ π, 𝒮 π = 𝒮' π) : 𝒮 = 𝒮' := by
  cases 𝒮 ; cases 𝒮'
  simp_all [DFunLike.coe]
  apply (Set.eqOn_univ _ _).mp fun ⦃x⦄ _ ↦ h x

def IsMarkovian (𝒮 : 𝔖[M]) : Prop := ∀ π, 𝒮 π = 𝒮 {π.last}

@[mk_iff]
class Markovian (𝒮 : 𝔖[M]) : Prop where
  intro : 𝒮.IsMarkovian

theorem MarkovianOn (𝒮 : 𝔖[M]) [inst : 𝒮.Markovian] (π : M.Path) :
    𝒮 π = 𝒮 {π.last} := inst.intro π

@[simp]
theorem Markovian_path_take (𝒮 : 𝔖[M]) [𝒮.Markovian] (π : M.Path) (i : Fin ‖π‖) :
    𝒮 (π.take i) = 𝒮 {π[i]} := by simp [MarkovianOn]

theorem singleton_last (s : State) : ({s} : M.Path).last = s := by simp

@[simp]
theorem Markovian_path_take' (𝒮 : 𝔖[M]) [𝒮.Markovian] (π : M.Path) (i : ℕ) (hi : i < ‖π‖) :
    𝒮 (π.take i) = 𝒮 {π[i]} := by simp [MarkovianOn, hi]

@[simp]
theorem Markovian_path_take'' (𝒮 : 𝔖[M]) [𝒮.Markovian] (π : M.Path) (i : Fin ‖π‖) :
    𝒮 (π.take i) = 𝒮 {π[i]} := by simp [𝒮.MarkovianOn (π.take i), Fin.getElem_fin]

@[simp]
theorem Markovian_path_take''' (𝒮 : 𝔖[M]) [𝒮.Markovian] (π : M.Path) (i : Fin (‖π‖ - 1)) :
    𝒮 (π.take i) = 𝒮 {π[i]} := by simp [𝒮.MarkovianOn (π.take i), Fin.getElem_fin]

end Scheduler

/-- A `Markovian` (historyless) scheduler. -/
def MScheduler (M : MDP State Act) := { 𝒮 : 𝔖[M] // 𝒮.Markovian }

@[inherit_doc]
notation "𝔏[" M "]" => MScheduler M

namespace MScheduler

variable {M : MDP State Act}

noncomputable instance : Inhabited 𝔖[M] :=
  ⟨fun _ ↦ M.default_act _, fun _ ↦ M.default_act_spec _⟩

noncomputable instance : Inhabited 𝔏[M] := ⟨default, ⟨fun _ ↦ rfl⟩⟩

@[coe]
def toScheduler : 𝔏[M] → 𝔖[M] := Subtype.val

instance : Coe 𝔏[M] 𝔖[M] := ⟨toScheduler⟩

instance (ℒ : 𝔏[M]) : Scheduler.Markovian (ℒ : 𝔖[M]) := ℒ.prop

@[simp, norm_cast] lemma coe_mk (𝒮 : 𝔖[M]) (h𝒮) : toScheduler ⟨𝒮, h𝒮⟩ = 𝒮 := rfl

@[simp]
theorem val_eq_toScheduler (ℒ : 𝔏[M]) : ℒ.val = (ℒ : 𝔖[M]) := rfl

theorem toScheduler_injective : Function.Injective ((↑) : 𝔏[M] → 𝔖[M]) := Subtype.coe_injective

instance instFunLike : FunLike 𝔏[M] M.Path Act where
  coe ℒ π := (ℒ : 𝔖[M]) π
  coe_injective' _ _ h := toScheduler_injective (Scheduler.ext <| congrFun h)

def mk' (f : (s : State) → Act) (hf : ∀s, f s ∈ M.act s) : 𝔏[M]
  := ⟨⟨fun π ↦ f π.last, fun π ↦ hf π.last⟩, (Scheduler.markovian_iff _).mpr fun _ ↦ rfl⟩

variable {ℒ : 𝔏[M]}

theorem markovian (π : M.Path) : ℒ π = ℒ {π.last} :=
  ℒ.prop.intro π

@[simp] theorem mem_act' (π : M.Path) :
    ℒ π ∈ M.act π.last := by
  obtain ⟨ℒ, h𝒮⟩ := ℒ
  simp only [DFunLike.coe]
  simp

@[simp]
theorem prepend {π : M.Path} (s : M.prev_univ π[0]) : ℒ (π.prepend s) = ℒ π := by
  have := ℒ.markovian π |>.symm
  have := ℒ.markovian (π.prepend ⟨s, by simp_all⟩)
  simp_all

@[simp]
theorem toScheduler_apply : ℒ.toScheduler π = ℒ π := rfl

end MScheduler

@[simp]
theorem Scheduler.mk'_coe {𝒮 : (π : M.Path) → M.act π.last} (π : M.Path) :
    (Scheduler.mk' 𝒮) π = (𝒮 π).val := by simp [mk']

/-- Specialize a scheduler such that all scheduled paths are considered with a given state as the
    immediately predecessor. -/
noncomputable def Scheduler.specialize [DecidableEq State] (𝒮 : 𝔖[M])
    (s : State) (s' : M.succs_univ s) : 𝔖[M] :=
  Scheduler.mk' fun π ↦ if h : π[0] = s' then ⟨𝒮 (π.prepend ⟨s, by simp_all⟩), by simp⟩ else default

syntax:max term noWs "[" withoutPosition(term) " ↦ " withoutPosition(term) "]" : term
@[inherit_doc Scheduler.specialize]
macro_rules | `($x[$i ↦ $j]) => `(($x).specialize $i $j)
syntax:max term noWs "[" withoutPosition(term) " ↦ " withoutPosition(term) "]'" term:max : term
@[inherit_doc Scheduler.specialize]
macro_rules | `($x[$i ↦ $j]'$p) => `(($x).specialize $i ⟨$j, $p⟩)

variable [DecidableEq State] {𝒮 : 𝔖[M]}

@[simp]
theorem Scheduler.specialize_apply :
    𝒮[s ↦ s'] π = if h : π[0] = s' then 𝒮 (π.prepend ⟨s, by simp_all⟩) else M.default_act π.last
:= by
  simp [specialize]; apply apply_dite

@[simp]
theorem Scheduler.specialize_tail_take (π : M.Path)
  (h : 1 < ‖π‖) :
    𝒮[π[0] ↦ ⟨π[1], by simp⟩] (π.tail.take i) = 𝒮 (π.take (i + 1)) := by
  simp [Nat.ne_of_lt' h, Path.take_prepend, π.tail_prepend h]

@[simp]
theorem Scheduler.specialize_default_on {π : M.Path}
    {s' : M.succs_univ s} (h : ¬π[0] = s') : 𝒮[s ↦ s'] π = M.default_act π.last := by
  simp [h]

theorem MScheduler.toScheduler_specialize (ℒ : 𝔏[M]) :
      ℒ.toScheduler[s ↦ s']
    = ⟨fun π ↦ if π[0] = s' then ℒ π else M.default_act π.last,
       fun π ↦ by simp; split_ifs <;> simp⟩ := by
  ext π; simp

end MDP
