import Mathlib.Data.Stream.Init
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Order.ScottContinuity.Complete
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic.Monotonicity.Basic
import MDP.Optimization

structure MDP (S A : Type*) where
  acts : S → Type*
  acts_inhabited : ∀ s, Inhabited (acts s)
  acts_nonempty : ∀ s, Nonempty (acts s)
  P : (s : S) → acts s → PMF S

namespace MDP

variable {S A : Type*} {M : MDP S A}

instance : Inhabited (M.acts s) := M.acts_inhabited s

def succ (M : MDP S A) (s : S) : Set S := {s' | ∃ α, 0 < M.P s α s'}

structure Path (M : MDP S A) where
  states : List S
  nonempty : states ≠ []
  property : ∀ i, (_ : i + 1 < states.length) → states[i + 1] ∈ M.succ states[i]

instance [Inhabited S] : Inhabited M.Path := ⟨⟨[default], by grind, by grind⟩⟩

attribute [grind .] List.take_eq_nil_iff
attribute [grind .] Path.nonempty
attribute [grind .] Path.property

def Path.length (π : M.Path) : ℕ := π.states.length

scoped notation "‖" π "‖" => Path.length π

@[simp, grind =]
theorem Path.states_length {π : M.Path} : π.states.length = ‖π‖ := rfl

@[grind ., simp]
theorem Path.length_pos {π : M.Path} : 0 < ‖π‖ := List.length_pos_iff.mpr π.nonempty
@[grind ., simp]
theorem Path.length_ne_zero {π : M.Path} : ‖π‖ ≠ 0 := Nat.ne_zero_of_lt π.length_pos

instance Path.instGetElem : GetElem M.Path ℕ S (fun π i ↦ i < ‖π‖) where
  getElem π i h := π.states[i]

@[simp, grind =]
theorem Path.states_getElem {π : M.Path} {i : ℕ} {h : i < ‖π‖} :
    π.states[i] = π[i] := rfl

@[simp, grind .]
theorem Path.property' (π : M.Path) (i : ℕ) (h : i + 1 < ‖π‖) : π[i + 1] ∈ M.succ π[i] :=
  π.property i h

@[grind]
def Path.last (π : M.Path) : S := π.states.getLast (by grind)

def Path.take (π : M.Path) (i : Fin ‖π‖) : M.Path :=
  ⟨π.states.take (i + 1), by grind, by grind⟩

@[simp, grind =]
theorem Path.take_last {π : M.Path} (i : Fin ‖π‖) : (π.take i).last = π[i] := by
  simp [take, last]
  rw [List.getLast_take]
  simp
@[simp, grind =]
theorem Path.take_length {π : M.Path} (i : Fin ‖π‖) : ‖π.take i‖ = i + 1 := by
  grind [take, length]

@[simp, grind =]
theorem Path.take_getElem {π : M.Path} (i : Fin ‖π‖) {j : ℕ} (hj : j ≤ i) :
    (π.take i)[j]'(by grind) = π[j] := by
  simp only [take, instGetElem, List.getElem_take]

@[ext]
theorem Path.ext {π₁ π₂ : M.Path}
    (h₁ : ‖π₁‖ = ‖π₂‖) (h₂ : ∀ i, (h₁ : i < ‖π₁‖) → (h₂ : i < ‖π₂‖) → π₁[i] = π₂[i]) : π₁ = π₂ := by
  cases π₁; cases π₂
  simp_all
  apply List.ext_getElem
  · exact h₁
  · exact fun i h₁' h₂' ↦ h₂ i h₂'

@[grind]
instance Path.instSingleton : Singleton S M.Path := ⟨(⟨[·], by grind, by grind⟩)⟩
@[simp, grind =] theorem Path.singleton_length : ‖({s} : M.Path)‖ = 1 := by rfl
@[simp, grind =] theorem Path.singleton_getElem {i : ℕ} {h} : ({s} : M.Path)[i]'h = s := by
  have : i = 0 := by grind
  subst_eqs
  simp [instSingleton]
  simp only [instGetElem]
  grind

structure Scheduler (M : MDP S A) where
  toFun : (π : M.Path) → M.acts π.last
deriving Nonempty, Inhabited

theorem Scheduler.ext_toFun {𝒮 𝒮' : M.Scheduler} (h : ∀ π, 𝒮.toFun π = 𝒮'.toFun π) : 𝒮 = 𝒮' := by
  rcases 𝒮 with ⟨f⟩; rcases 𝒮' with ⟨g⟩
  simp only [mk.injEq]
  ext
  grind

def Scheduler.toFun' (𝒮 : M.Scheduler) (π : M.Path) {s : S} (h : π.last = s := by grind) :
    M.acts s :=
  have h : M.acts π.last = M.acts s := by grind
  cast h (𝒮.toFun π)

instance Scheduler.instDFunLike :
    DFunLike M.Scheduler M.Path (fun π ↦ {s : S} → (h : π.last = s := by grind) → M.acts s) where
  coe 𝒮 π s h := 𝒮.toFun' π h
  coe_injective' := by
    intro 𝒮 𝒮' h
    apply ext_toFun fun π ↦ ?_
    replace h := congrFun₃ h π π.last
    grind [toFun']

@[ext]
theorem Scheduler.ext {𝒮₁ 𝒮₂ : M.Scheduler} (h : ∀ (π : M.Path), 𝒮₁ π rfl = 𝒮₂ π rfl) :
    𝒮₁ = 𝒮₂ := by
  cases 𝒮₁; cases 𝒮₂; simp; ext π; exact h π

@[grind =, simp]
theorem Scheduler.mk_apply (f : (π : M.Path) → M.acts π.last) : (⟨f⟩ : M.Scheduler) π = f π := rfl

noncomputable def Path.prob (π : M.Path) (𝒮 : M.Scheduler) : ENNReal :=
  ∏ i : Fin (‖π‖ - 1), M.P π[i] (𝒮 (π.take ⟨i, by grind⟩)) π[i.val + 1]
noncomputable def Path.rew (π : M.Path) (r : S → ENNReal) : ENNReal :=
  ∑ i : Fin ‖π‖, r π[i]

theorem Path.prob_eq {π : M.Path} :
      π.prob 𝒮
    = ∏ i ∈ Finset.range (‖π‖ - 1),
        if h : _ then M.P π[i] (𝒮 (π.take ⟨i, by grind⟩)) (π[i + 1]'h) else 1 := by
  simp only [prob, Fin.getElem_fin]
  apply Finset.prod_nbij (·.val) <;> intro <;> simp <;> grind
theorem Path.rew_eq {π : M.Path} :
      π.rew r
    = ∑ i ∈ Finset.range ‖π‖,
        if h : _ then r π[i] else 0 := by
  simp only [rew, Fin.getElem_fin]
  apply Finset.sum_nbij (·.val) <;> intro <;> simp; grind

@[simp, grind =] theorem Path.singleton_prob : ({s} : M.Path).prob 𝒮 = 1 := by simp [prob_eq]
@[simp, grind =] theorem Path.singleton_rew : ({s} : M.Path).rew r = r s := by simp [rew_eq]

noncomputable def Φ (M : MDP S A) (O : Optimization) :
    (S → ENNReal) →o (S → ENNReal) →o S → ENNReal :=
  ⟨fun r ↦ ⟨fun v s ↦ r s + O.opt fun α ↦ ∑' s', M.P s α s' * v s',
    by intro v₁ v₂ h s; simp only; gcongr; intro α; simp only; gcongr with s'; exact h s'⟩,
    by intro r₁ r₂ h v s; simp only; gcongr; exact h s⟩

class FiniteBranching (M : MDP S A) where
  acts_finite : ∀ s, Finite (M.acts s)
  succ_finite : ∀ s, Finite (M.succ s)

instance [i : M.FiniteBranching] : Finite (M.acts s) := i.acts_finite s

open scoped Optimization.Notation

theorem Φ_𝒜_iSup :
    ⨆ v, M.Φ 𝒜 r v = M.Φ 𝒜 r (fun s ↦ ⨆ v : S → ENNReal, v s) := by
  ext s
  simp only [Φ, Optimization.opt, OrderHom.coe_mk, iSup_apply, ← ENNReal.add_iSup, ENNReal.mul_iSup]
  rw [iSup_comm]
  congr with α
  simp [ENNReal.tsum_eq_iSup_sum]
  rw [iSup_comm]
  congr! with Z
  rw [ENNReal.finsetSum_iSup_of_monotone]
  intro s' v₁ v₂ h; simp only; gcongr; exact h s'

theorem Φ_𝒟_iSup [M.FiniteBranching] :
    ⨆ v, M.Φ 𝒟 r v = M.Φ 𝒟 r (fun s ↦ ⨆ v : S → ENNReal, v s) := by
  ext s
  simp only [Φ, Optimization.opt, OrderHom.coe_mk, iSup_apply, ← ENNReal.add_iSup, ENNReal.mul_iSup]
  rw [Set.iSup_iInf_of_monotone]
  · congr with α
    simp [ENNReal.tsum_eq_iSup_sum]
    rw [iSup_comm]
    congr! with Z
    rw [ENNReal.finsetSum_iSup_of_monotone]
    intro s' v₁ v₂ h; simp only; gcongr; exact h s'
  · intro α v₁ v₂ h; simp only; gcongr with s'; exact h s'

theorem Φ_𝒟_cont [M.FiniteBranching] : ScottContinuous (M.Φ 𝒟 r) := by
  refine ScottContinuous.of_map_sSup ?_
  intro Z hZ hZ'
  ext s
  suffices (M.Φ 𝒟 r) (sSup Z) s = ⨆ v : Z, (M.Φ 𝒟 r) v s by
    rw [this]
    apply Function.Surjective.iSup_congr (fun z ↦ ⟨M.Φ 𝒟 r z, by grind⟩)
    · intro ⟨f, hf⟩; simp only [Subtype.exists]; grind
    · grind
  simp [Φ]
  letI : Nonempty ↑Z := Set.Nonempty.to_subtype hZ
  letI : IsDirected ↑Z fun x1 x2 ↦ x1 ≤ x2 := by
    constructor; intro a b
    specialize hZ' a a.prop b b.prop
    simp_all only [Subtype.exists]
    obtain ⟨f, hf⟩ := hZ'
    use f, hf.left, hf.right.left, hf.right.right
  simp only [Optimization.opt, ENNReal.mul_iSup, OrderHom.coe_mk, ← ENNReal.add_iSup]
  rw [Set.iSup_iInf_of_monotone]
  · congr with α
    simp [ENNReal.tsum_eq_iSup_sum]
    rw [iSup_comm]
    congr! with Z
    rw [ENNReal.finsetSum_iSup_of_monotone]
    intro s' v₁ v₂ h; simp only; gcongr; exact h s'
  · intro α v₁ v₂ h; simp only; gcongr with s'; exact h s'

theorem Φ_𝒜_cont : ScottContinuous (M.Φ 𝒜 r) := by
  refine ScottContinuous.of_map_sSup ?_
  intro Z hZ hZ'
  ext s
  suffices (M.Φ 𝒜 r) (sSup Z) s = ⨆ v : Z, (M.Φ 𝒜 r) v s by
    rw [this]
    apply Function.Surjective.iSup_congr (fun z ↦ ⟨M.Φ 𝒜 r z, by grind⟩)
    · intro ⟨f, hf⟩; simp only [Subtype.exists]; grind
    · grind
  simp [Φ]
  letI : Nonempty ↑Z := Set.Nonempty.to_subtype hZ
  letI : IsDirected ↑Z fun x1 x2 ↦ x1 ≤ x2 := by
    constructor; intro a b
    specialize hZ' a a.prop b b.prop
    simp_all only [Subtype.exists]
    obtain ⟨f, hf⟩ := hZ'
    use f, hf.left, hf.right.left, hf.right.right
  simp only [Optimization.opt, ENNReal.mul_iSup, OrderHom.coe_mk, ← ENNReal.add_iSup]
  rw [iSup_comm]
  congr with α
  simp [ENNReal.tsum_eq_iSup_sum]
  rw [iSup_comm]
  congr! with Z
  rw [ENNReal.finsetSum_iSup_of_monotone]
  intro s' v₁ v₂ h; simp only; gcongr; exact h s'

open OrderHom

theorem lfp_Φ_𝒟_eq [M.FiniteBranching] : lfp (M.Φ 𝒟 r) = ⨆ i, (M.Φ 𝒟 r)^[i] ⊥ := by
  rw [fixedPoints.lfp_eq_sSup_iterate]
  apply ScottContinuous.ωScottContinuous Φ_𝒟_cont

theorem lfp_Φ_𝒜_eq : lfp (M.Φ 𝒜 r) = ⨆ i, (M.Φ 𝒜 r)^[i] ⊥ := by
  rw [fixedPoints.lfp_eq_sSup_iterate]
  apply ScottContinuous.ωScottContinuous Φ_𝒜_cont

class ΦContinuous (M : MDP S A) (O : Optimization) where
  Φ_cont : ∀ r, ScottContinuous (M.Φ O r)

def Φ_ωScottContinuous [i : M.ΦContinuous O] :
    OmegaCompletePartialOrder.ωScottContinuous (M.Φ O r) := by
  apply ScottContinuous.ωScottContinuous (i.Φ_cont r)

theorem lfp_Φ_eq [M.ΦContinuous O] : lfp (M.Φ O r) = ⨆ i, (M.Φ O r)^[i] ⊥ :=
  fixedPoints.lfp_eq_sSup_iterate _ Φ_ωScottContinuous

def Path.prepend (π : M.Path) (s : S) (h : π[0] ∈ M.succ s) : M.Path where
  states := s :: π.states
  nonempty := by simp
  property := by rintro (_ | i) <;> grind
@[simp, grind =]
theorem Path.prepend_length {π : M.Path} {s} {h} : ‖π.prepend s h‖ = ‖π‖ + 1 := by
  grind [length, prepend]
@[simp, grind =]
theorem Path.prepend_getElem {π : M.Path} {s} {h} {i : ℕ} (hi : i < ‖π‖ + 1) :
    (π.prepend s h)[i]'(by grind) = if h' : i = 0 then s else π[i - 1] := by
  simp only [length, instGetElem, prepend]
  grind
theorem Path.prepend_inj {π : M.Path} {s₁ s₂ h₁ h₂} (h : π.prepend s₁ h₁ = π.prepend s₂ h₂) :
    s₁ = s₂ := by
  grind [prepend]
theorem Path.prepend_inj' {π₁ π₂ : M.Path} {s h₁ h₂} (h : π₁.prepend s h₁ = π₂.prepend s h₂) :
    π₁ = π₂ := by
  ext i hi₁ hi₂
  · grind [prepend]
  · have : (π₁.prepend s h₁)[i + 1]'(by grind) = (π₂.prepend s h₂)[i + 1]'(by grind) := by grind
    grind

def Path.tail (π : M.Path) (h : 1 < ‖π‖) : M.Path where
  states := π.states.tail
  nonempty := by simp [List.ne_nil_of_length_pos, h]
  property := by rintro (_ | i) <;> grind
@[simp, grind =]
theorem Path.tail_length {π : M.Path} {h} : ‖π.tail h‖ = ‖π‖ - 1 := by
  grind [length, tail]
@[simp, grind =]
theorem Path.tail_getElem {π : M.Path} {h} {i : ℕ} {hi : i < ‖π‖ - 1} :
    (π.tail h)[i]'(by grind) = π[i + 1] := by
  simp only [length, instGetElem, tail]
  grind

@[simp, grind =]
theorem Path.prepend_tail {π : M.Path} {s h} : (π.prepend s h).tail (by grind) = π := by
  ext <;> grind

open scoped Classical in
noncomputable def Scheduler.prefix (𝒮 : M.Scheduler) (s : S) : M.Scheduler :=
  ⟨fun π ↦ if h : _ then 𝒮 (π.prepend s h) else default⟩
theorem Path.prepend_prob {π : M.Path} {s h} {𝒮 : M.Scheduler} :
      (π.prepend s h).prob 𝒮
    = M.P s (𝒮 {s}) π[0] * π.prob (𝒮.prefix s) := by
  simp [prob_eq]
  set n := ‖π‖ - 1
  have : ‖π‖ = n + 1 := by grind
  simp [this]
  simp [Finset.prod_range_succ']
  rw [mul_comm]
  congr! 2 with i hi
  simp_all [Scheduler.prefix]
  congr
  simp [DFunLike.coe, Scheduler.toFun']
  congr! 1 with h
  · grind
  · split_ifs with h'
    · simp_all
      simp at h h'
      congr
    · simp at h h'
      grind

theorem Path.prepend_rew {π : M.Path} {s h}  :
    (π.prepend s h).rew r = r s + π.rew r := by
  simp [rew_eq, Finset.sum_range_succ']
  rw [add_comm]
  congr

@[grind]
def PathEq (M : MDP S A) (s : S) (n : ℕ) : Set M.Path := {π : M.Path | ‖π‖ = n ∧ π[0] = s}
theorem PathEq_succ (M : MDP S A) (s : S) (n : ℕ) :
      M.PathEq s (n + 2)
    = ⋃ s' : M.succ s, (·.val.prepend s (by grind)) '' (Set.univ : Set (M.PathEq s' (n + 1))) := by
  ext π
  simp [PathEq, Path.ext_iff]
  simp_all only [Path.prepend_getElem, exists_prop]
  constructor
  · simp_all only [forall_and_index]
    intro hp hq
    use π[1]'(by grind)
    constructor
    · grind
    · use π.tail (by grind)
      grind
  · grind

@[grind =, simp]
theorem PathEq_first (π : ↑(M.PathEq s (n + 1))) : π.val[0] = s := by grind

theorem tsum_PathEq_succ {f : M.Path → ENNReal} :
      ∑' π : M.PathEq s (n + 2), f π.val
    = ∑' s' : M.succ s, ∑' π : M.PathEq s' (n + 1), f (π.val.prepend s (by grind)) := by
  rw [PathEq_succ]
  rw [ENNReal.tsum_biUnion]
  · congr! 2 with ⟨s', hs'⟩
    simp
    symm
    apply tsum_eq_tsum_of_ne_zero_bij fun ⟨⟨π, hπ⟩, h⟩ ↦ ⟨π.tail (by grind), by grind⟩
    · rintro ⟨⟨π₁, h₁⟩, h₁'⟩ ⟨⟨π₂, h₂⟩, h₂'⟩
      grind
    · intro ⟨π, hπ⟩ h
      simp_all only [Function.mem_support, ne_eq, Set.mem_range, Subtype.mk.injEq, Subtype.exists,
        Set.image_univ]
      use π.prepend s (by grind)
      simp only [Path.prepend_tail]
      grind
    · grind
  · simp
    intro ⟨s₁, h₁⟩ _ ⟨s₂, h₂⟩ _ h Z hZ₁ hZ₂ π hπ
    specialize hZ₁ hπ
    specialize hZ₂ hπ
    grind [Path.prepend_inj']

instance : IsEmpty (M.PathEq s 0) where
  false := by grind
instance : Subsingleton (M.PathEq s 1) where
  allEq := by intro ⟨_, h₁⟩ ⟨_, h₂⟩; ext <;> grind
@[simp, grind =]
theorem PathEq_zero : M.PathEq s 0 = ∅ := Set.eq_empty_of_isEmpty _
@[simp, grind =]
theorem PathEq_one : M.PathEq s 1 = {{s}} := by ext; simp [Path.ext_iff]; grind

instance : IsEmpty (Fin (‖({s} : M.Path)‖ - 1)) := Finset.univ_eq_empty_iff.mp rfl

@[simp]
theorem tsum_succ_P {𝒮 : M.Scheduler} : ∑' (s' : ↑(M.succ s)), (M.P s (𝒮 {s} rfl)) ↑s' = 1 := by
  rw [← (M.P s (𝒮 {s})).tsum_coe]
  symm
  apply tsum_eq_tsum_of_ne_zero_bij fun ⟨x, p⟩ ↦ x
  · intro; grind
  · intro s'; simp +contextual [succ]
    intro h₁
    use 𝒮 {s}
    exact (PMF.apply_pos_iff _ s').mpr h₁
  · grind

@[simp]
theorem tsum_PathEq_prob :
    ∑' π : M.PathEq s (n + 1), π.val.prob 𝒮 = 1 := by
  induction n generalizing s 𝒮 with
  | zero =>
    simp
    rw [tsum_eq_single ⟨{s}, by grind⟩]
    · simp [Path.prob]
    · simp
  | succ i ih =>
    rw [tsum_PathEq_succ (f:=fun π ↦ π.prob 𝒮)]
    simp [Path.prepend_prob, ENNReal.tsum_mul_left, ih]

noncomputable def EC (M : MDP S A) (r : S → ENNReal) (𝒮 : M.Scheduler) (n : ℕ) : S → ENNReal :=
  fun s ↦ ∑' π : M.PathEq s n, π.val.prob 𝒮 * π.val.rew r

theorem tsum_opt [Finite ι] [Nonempty ι] [DecidableEq γ] {O : Optimization} {f : ι → γ → ENNReal}
    (h₁ : ∀ (i j : ι), ∃ k, ∀ (a : γ), f i a ≤ f k a ∧ f j a ≤ f k a)
    (h₂ : ∀ (z) (Z) (i j : ι), z ∉ Z → ∃ k, f k z + ∑ s ∈ Z, f k s ≤ f i z + ∑ s ∈ Z, f j s) :
    (O.opt fun i ↦ ∑' s, f i s) = ∑' s, (O.opt fun i ↦ f i s) := by
  simp [ENNReal.tsum_eq_iSup_sum]
  cases O
  · simp; rw [iSup_comm]; congr with Z; symm; apply ENNReal.finsetSum_iSup; apply h₁
  · simp; rw [← Set.iSup_iInf_of_monotone]
    · congr with Z
      induction Z using Finset.induction with
      | empty => simp
      | insert z Z hzZ ih =>
        simp_all
        rw [← ENNReal.iInf_add_iInf, ih]; clear ih
        exact fun i j ↦ h₂ z Z i j hzZ
    · intro i a b hab; simp_all; gcongr

theorem EC_succ : (O.opt fun 𝒮 ↦ M.EC r 𝒮 (n + 1)) = ((M.Φ O) r) (O.opt fun 𝒮 ↦ M.EC r 𝒮 n) := by
  ext s
  simp [Φ, EC]
  rcases n with _ | n
  · simp [Path.prepend_prob, Path.prepend_rew, mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, mul_assoc, ENNReal.tsum_mul_left]
    conv => enter [1, 2]; ext 𝒮; rw [PathEq_one]
    simp
  · conv => left; arg 2; ext 𝒮; rw [M.tsum_PathEq_succ (f:=fun π ↦ π.prob 𝒮 * π.rew r)]
    simp [Path.prepend_prob, Path.prepend_rew, mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, mul_assoc, ENNReal.tsum_mul_left]
    have : ∀ α s', (M.P s α) s' ≠ ⊤ := by intro _ _; exact PMF.apply_ne_top _ _
    simp [Optimization.ENNReal_add_opt, Optimization.ENNReal_mul_opt, this]
    congr
    show (O.opt fun (𝒮 : M.Scheduler) ↦ ∑' (a : M.succ s), M.P s (𝒮 {s}) a * M.EC r (𝒮.prefix s) (n + 1) a) =
          O.opt fun α ↦ ∑' (s' : S), (M.P s α) s' * O.opt fun 𝒮 ↦ M.EC r 𝒮 (n + 1) s'
    have : ∀ s', (O.opt fun 𝒮 ↦ M.EC r 𝒮 (n + 1) s')
                  = O.opt fun (𝒮 : M.Scheduler) ↦ M.EC r (𝒮.prefix s) (n + 1) s' := by

      sorry
    simp [this]; clear this
    simp [← Optimization.ENNReal_mul_opt, this]
    letI : Finite M.Scheduler := sorry
    classical
    conv =>
      right
      arg 2
      ext α
      rw [← tsum_opt (by
        intro i j
        sorry
        ) (by
        intro s' Z i j hs'Z
        sorry)]
    sorry
  -- cases O
  -- · sorry
  -- · sorry

theorem EC_eq_lfp_Φ [M.ΦContinuous O] :
    (⨆ n, O.opt fun 𝒮 ↦ M.EC r 𝒮 n) = lfp (M.Φ O r) := by
  rw [lfp_Φ_eq]
  congr! with n
  induction n with
  | zero =>
    ext s
    cases O <;> simp [EC, Optimization.opt]
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    simp [← ih]; clear ih
    rw [EC_succ]

end MDP
