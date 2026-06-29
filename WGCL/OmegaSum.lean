module

public import Mathlib.Algebra.BigOperators.Group.Finset.Preimage
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.Countable.Basic
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Logic.Encodable.Basic
public import Mathlib.Data.Set.Countable
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.BourbakiWitt
public import WGCL.ScottRing

@[expose] public section

open OmegaCompletePartialOrder

attribute [local simp] Encodable.decode₂_eq_some
attribute [gcongr] OrderHom.mk_le_mk

namespace Finset

theorem sum_le_sum_of_inj {ι κ α : Type*} [AddCommMonoid α] [Preorder α] [AddLeftMono α] [IsBotZeroClass α] {I : Finset ι} {K : Finset κ} {f : ι → α} {g : κ → α}
    (e : ι → κ) (he : Function.Injective e) (h : ∀ i ∈ I, f i ≤ g (e i)) (h' : ∀ i ∈ I, e i ∈ K) :
    ∑ i ∈ I, f i ≤ ∑ k ∈ K, g k := by
  classical
  induction I using Finset.induction generalizing K with
  | empty => simp
  | insert i I hiI ih =>
    simp_all
    obtain ⟨h₁, h₂⟩ := h'
    obtain ⟨K, ⟨_⟩, _⟩ : ∃ K', K = insert (e i) K' ∧ e i ∉ K' := by exists K \ {e i}; simp_all
    simp_all
    gcongr <;> grind

def cosubtype {α : Type*} {β : α → Type*} [DecidableEq α] (S : Finset ((a : α) × β a)) (a : α) : Finset (β a) :=
  S.filterMap (fun ⟨a', b⟩ ↦ if h : a' = a then some (cast (congrArg β h) b) else none) (by simp; grind)
@[simp]
theorem mem_cosubtype_iff {α : Type*} {β : α → Type*} [DecidableEq α] (S : Finset ((a : α) × β a)) (a : α) (b : β a) :
    b ∈ S.cosubtype a ↔ ⟨a, b⟩ ∈ S := by
  simp_all [cosubtype]; grind

theorem sum_range_le_sup_of_le {𝒮 : Type*} [AddCommMonoid 𝒮] [PartialOrder 𝒮] [AddLeftMono 𝒮] [IsBotZeroClass 𝒮] {m n} {f g : ℕ → 𝒮} (h : f ≤ g) :
    ∑ i ∈ range n, f i ≤ ∑ i ∈ range (m ⊔ n), g i := by
  if h' : m < n then
    have : max m n = n := by omega
    simp_all; gcongr; apply h
  else
    simp_all
    grw [h']
    · gcongr; apply h
    · simp

def max₁ (S : Finset ℕ) : ℕ := if h : S.Nonempty then S.max' h + 1 else 0
@[simp]
theorem lt_max₁ {S : Finset ℕ} {i : ℕ} (h₁ : S.Nonempty) (h₂ : i ∈ S) : i < S.max₁ := by
  simp_all [max₁]; apply Finset.le_max' _ _ h₂
theorem insert_max₁ {S : Finset ℕ} {i : ℕ} : (insert i S).max₁ = (i + 1) ⊔ S.max₁ := by
  simp_all [max₁]
  split_ifs
  · simp_all
  · simp_all
@[simp]
theorem max₁_exists (S : Finset ℕ) : ∃ n, S.max₁ ≤ n := by
  simp [max₁]; split_ifs
  · simp_all
    use S.max' ‹_› + 1
    intro y hy
    simp
    apply Finset.le_max'
    assumption
  · simp
@[simp]
theorem subset_range_max₁ (S : Finset ℕ) : S ⊆ range S.max₁ := by
  simp [max₁]; split_ifs
  · intro; simp_all; apply Finset.le_max'
  · grind

def rangeCover (S : Finset ℕ) : Finset ℕ := range (S.max₁)
theorem rangeCover_exists (S : Finset ℕ) : ∃ n, S.rangeCover ⊆ Finset.range n := by
  simp [rangeCover]
@[grind ., simp]
theorem subset_rangeCover (S : Finset ℕ) : S ⊆ S.rangeCover := by simp [rangeCover]

variable {ι α : Type*} [e₁ : Encodable ι] [OmegaCompletePartialOrder α]

protected def ωSup (f : Finset ι →o α) : α :=
  ωSup ⟨fun i ↦ f ((range i).filterMap (Encodable.decode₂ _)
    (by grind [Option.mem_def, Encodable.decode₂_eq_some])),
    fun i j h ↦ by simp only; gcongr; refine filterMap_mono _ (by gcongr)⟩

protected theorem ωSup_le_copy (e₂ : Encodable ι) (f : Finset ι →o α) :
    @Finset.ωSup ι α e₁ inferInstance f ≤ @Finset.ωSup ι α e₂ inferInstance f := by
  simp [Finset.ωSup]
  intro i₁
  let S := (range i₁).filterMap (e₁.decode₂ _)
            (by grind [Option.mem_def, Encodable.decode₂_eq_some]) |>.map e₂.encode'
  if h : S.Nonempty then
    let m₁ := S.max' h
    apply le_ωSup_of_le (m₁ + 1)
    simp only [Chain.mk_apply]
    gcongr
    intro y h₁
    simp_all [Encodable.decode₂_eq_some, m₁, Encodable.encode', S]
    apply Finset.le_max'
    simp [h₁]
  else
    simp [S] at h; rw [h]; apply le_ωSup_of_le 0; rfl

protected theorem ωSup_copy (e₂ : Encodable ι) (f : Finset ι →o α) :
    @Finset.ωSup ι α e₁ inferInstance f = @Finset.ωSup ι α e₂ inferInstance f := by
  apply le_antisymm <;> exact Finset.ωSup_le_copy (e₁ := _) _ f

@[gcongr]
protected theorem ωSup_mono : Monotone (Finset.ωSup (ι := ι) (α := α)) :=
  fun _ _ h ↦ ωSup_le _ _ fun i ↦ le_ωSup_of_le i (h _)

protected theorem ωSup_le (f : Finset ι →o α) (x : α) (h : ∀ S, f S ≤ x) : Finset.ωSup f ≤ x := by
  simp [Finset.ωSup]; intro n; apply h

@[simp]
protected theorem ωSup_le_iff {f : Finset ι →o α} {x : α} : Finset.ωSup f ≤ x ↔ ∀ S, f S ≤ x := by
  constructor
  · simp [Finset.ωSup]
    intro h S
    if S = ∅ then
      specialize h 0
      simp_all
    else
      specialize h ((S.map (Encodable.encode' _) |>.max' (by simp_all [nonempty_iff_ne_empty])) + 1)
      grw [← h]
      gcongr
      simp
      intro i hi
      simp_all [Encodable.encode']
      apply Finset.le_max'
      simp_all
  · exact Finset.ωSup_le f x

protected theorem le_ωSup (f : Finset ι →o α) (S : Finset ι) : f S ≤ Finset.ωSup f := by
  simp [Finset.ωSup]
  if hS : S.Nonempty then
    apply le_ωSup_of_le ((S.map (Encodable.encode' _) |>.max' (by simp_all)) + 1)
    simp
    gcongr
    simp
    intro x hx
    simp_all [Encodable.encode']
    apply Finset.le_max'
    simp [hx]
  else
    simp_all; apply le_ωSup_of_le 0; simp

protected theorem le_ωSup_of_le {f : Finset ι →o α} {x : α} (S : Finset ι) (h : x ≤ f S) :
    x ≤ Finset.ωSup f := by
  apply h.trans (Finset.le_ωSup f S)

protected theorem ωSup_ωSup_comm {f : Chain (Finset ι →o α)} :
      ωSup ⟨fun i ↦ Finset.ωSup (f i), fun a b c ↦ by simp only; gcongr⟩
    = Finset.ωSup ⟨
        fun S ↦ ωSup ⟨fun i ↦ f i S, fun a b h ↦ by simp_all⟩,
        fun a b h ↦ by simp only; gcongr; refine Chain.le_of_apply fun _ ↦ ?_; simp; gcongr⟩ := by
  apply le_antisymm <;> simp
  · apply fun i S ↦ Finset.le_ωSup_of_le S (le_ωSup_of_le i (by rfl))
  · apply fun S i ↦ le_ωSup_of_le i (Finset.le_ωSup_of_le S (by rfl))

theorem ωSup_ωSup_eq_ωSup (f : Finset ι →o Finset ι →o α) :
      Finset.ωSup ⟨fun i ↦ Finset.ωSup ⟨fun j ↦ f i j, (f _).mono⟩, fun _ _ h ↦ by simp only; gcongr; simp; gcongr⟩
    = Finset.ωSup ⟨fun i ↦ f i i, fun i j h ↦ (f.mono h i).trans ((f j).mono h)⟩ := by
  classical
  apply le_antisymm
  · refine Finset.ωSup_le _ _ fun i ↦ Finset.ωSup_le _ _ fun j ↦ Finset.le_ωSup_of_le (i ∪ j) ?_
    simp only [OrderHom.coe_mk]
    (repeat apply OrderHom.apply_mono) <;> simp
  · apply ωSup_le _ _ fun i ↦ le_ωSup_of_le i (le_ωSup_of_le i (by rfl))

theorem ωSup_ωSup_eq_ωSup' (f : Finset ι → Finset ι → α) (hf : Monotone f) (hf' : ∀ i, Monotone (f i)) :
      Finset.ωSup ⟨fun i ↦ Finset.ωSup ⟨fun j ↦ f i j, hf' i⟩, fun _ _ hij ↦ by simp only; gcongr; simp [hf hij]⟩
    = Finset.ωSup ⟨fun i ↦ f i i, fun i j hij ↦ le_trans (hf hij i) (hf' j hij)⟩ :=
  Finset.ωSup_ωSup_eq_ωSup ⟨fun i ↦ ⟨fun j ↦ f i j, hf' i⟩, hf⟩

@[simp]
protected theorem ωSup_eq_zero_iff [Zero α] [IsBotZeroClass α] (c : Finset ι →o α) :
    Finset.ωSup c = 0 ↔ ∀ i, c i = 0 := by
  constructor
  · intro this
    replace this := ωSup_le_iff.mp this.le
    simp at this
    intro S
    replace := (this (S.map (Encodable.encode' _)).max₁).le
    apply le_antisymm
    · grw [← this]; clear this
      gcongr
      intro i hi
      simp [Encodable.encode']
      apply lt_max₁
      · simp; grind
      · simp_all
    · simp
  · simp_all [Finset.ωSup]

protected theorem map_ωSup {β : Type*} [OmegaCompletePartialOrder β] {f : α → β} (hf : ωScottContinuous f) (c : Finset ι →o α) :
    f (Finset.ωSup c) = Finset.ωSup (OrderHom.comp ⟨f, hf.monotone⟩ c) := by
  simp [Finset.ωSup]
  rw [hf.map_ωSup]
  rfl

section

variable {α β : Type*} [OmegaCompletePartialOrder α]

open SMulMono

protected theorem ωSup_add [Add α] [ωScottContinuousRightAdd α]
    (a : α) (c : Finset ι →o α) :
    Finset.ωSup c + a = Finset.ωSup ⟨(c · + a), fun _ _ _ ↦ add_le_add_left (c.mono ‹_›) a⟩ :=
  (ωScottContinuousRightAdd.add_left_ωScottContinuous a).map_ωSup _
protected theorem add_ωSup [Add α] [ωScottContinuousLeftAdd α]
    (a : α) (c : Finset ι →o α) :
    a + Finset.ωSup c = Finset.ωSup ⟨(a + c ·), fun _ _ _ ↦ add_le_add_right (c.mono ‹_›) a⟩ :=
  (ωScottContinuousLeftAdd.add_right_ωScottContinuous a).map_ωSup _
protected theorem ωSup_mul [Mul α] [ωScottContinuousRightMul α]
    (a : α) (c : Finset ι →o α) :
    Finset.ωSup c * a = Finset.ωSup ⟨(c · * a), fun _ _ _ ↦ mul_le_mul_left (c.mono ‹_›) a⟩ :=
  (ωScottContinuousRightMul.mul_left_ωScottContinuous a).map_ωSup _
protected theorem mul_ωSup [Mul α] [ωScottContinuousLeftMul α]
    (a : α) (c : Finset ι →o α) :
    a * Finset.ωSup c = Finset.ωSup ⟨(a * c ·), fun _ _ _ ↦ mul_le_mul_right (c.mono ‹_›) a⟩ :=
  (ωScottContinuousLeftMul.mul_right_ωScottContinuous a).map_ωSup _
protected theorem smul_ωSup [SMul β α] [ωScottContinuousSMul β α]
    (a : β) (c : Finset ι →o α) :
    a • Finset.ωSup c = Finset.ωSup ⟨(a • c ·), fun _ _ _ ↦ smul_le_smul_left (c.mono ‹_›)⟩ :=
  (ωScottContinuousSMul.smul_continuous a).map_ωSup _

end

section

variable {α ι : Type*} [CompleteLattice α] [Encodable ι]

@[simp]
theorem ωSup_eq_iSup {f : Finset ι →o α} : Finset.ωSup f = iSup f := by
  apply le_antisymm
  · simp [le_iSup]
  · simp [Finset.le_ωSup]

end

end Finset

section

variable {ι α : Type*} [PartialOrder α] [Zero α] [IsBotZeroClass α]
variable {f g : ι → α}

@[simp, grind ·, grind →]
theorem Function.support_subset_of_le (h : f ≤ g) :
    Function.support f ⊆ Function.support g := by
  simp; intro x; specialize h x; contrapose; intro h'; simp_all

@[grind .]
theorem Function.countable_support_of_le (h : f ≤ g) (hg : Countable g.support) :
    Countable f.support := Set.Countable.mono (by grind) (Countable.to_set hg)

end

namespace OmegaCompletePartialOrder

variable {ι κ α : Type*} [Countable ι] [Countable κ]
variable [OmegaCompletePartialOrder α] [AddCommMonoid α] [AddLeftMono α] [IsBotZeroClass α]

attribute [local simp] Finset.sum_le_sum_of_subset_of_nonneg

noncomputable local instance : Encodable ι := Encodable.ofCountable ι

open scoped Classical in
/-- `ω∑ i, f i` is the countable sum of `f` defined as the ω-supremum over sums finite subsets.

Note that `ωSum` is defined for `Countable ι : Prop` while `Finset.ωSup` is for `Encodable ι :
Type`. Since the sum is exhaustive, the instance of `Encodable` is irrelevant and thus use
`Encodable.ofCountable ι`.
-/
noncomputable def ωSum (f : ι → α) :=
  Finset.ωSup ⟨fun S ↦ ∑ s ∈ S, f s, fun S T h ↦ by simp_all⟩

@[inherit_doc ωSum]
notation3 "ω∑ "(...)", "r:67:(scoped f => ωSum f) => r

attribute [grind ·] Set.inclusion_injective

@[gcongr]
def ωSum_mono : Monotone (ωSum (ι := ι) (α := α)) := by
  intro f g h
  simp only [ωSum]
  gcongr
  exact fun _ ↦ Finset.sum_le_sum fun i _ ↦ h i

variable {f : ι → α} {g : κ → α} {a : α} (S : Finset ι)

theorem ωSum_le_iff : ω∑ i, f i ≤ a ↔ ∀ S, ∑ i ∈ S, f i ≤ a := Finset.ωSup_le_iff
theorem ωSum_le (h : ∀ S, ∑ i ∈ S, f i ≤ a) : ω∑ i, f i ≤ a := ωSum_le_iff.mpr h
@[simp]
theorem le_ωSum : ∑ i ∈ S, f i ≤ ω∑ i, f i := Finset.le_ωSup_of_le S (by rfl)
theorem le_ωSum_of_le (h : a ≤ ∑ i ∈ S, f i) : a ≤ ω∑ i, f i := h.trans (le_ωSum S)

theorem ωSum_eq_ωSum_of_ne_zero_bij
    (i : g.support → ι) (hi : Function.Injective i)
    (hf : f.support ⊆ Set.range i) (hfg : ∀ (x : g.support), f (i x) = g x) :
    ω∑ x, f x = ω∑ y, g y := by
  classical
  apply le_antisymm
    (ωSum_le fun S ↦ le_ωSum_of_le ((S.preimage i hi.injOn).map ⟨(·.val), (·.val_injective)⟩) ?_)
    (ωSum_le fun S ↦ le_ωSum_of_le ((S.subtype _).map ⟨i, hi⟩) ?_)
  · simp [← hfg]; grind [Finset.sum_preimage, Function.support_subset_iff]
  · simp [hfg, Finset.sum_filter_ne_zero]

@[simp]
theorem ωSum_substype_supp : ω∑ x : f.support, f x = ω∑ x, f x := by
  symm
  apply ωSum_eq_ωSum_of_ne_zero_bij (·.val.val)
  · intro ⟨_, _⟩; simp_all; grind
  · simp
  · simp

@[simp]
theorem ωSum_zero : ω∑ (_ : ι), (0 : α) = 0 := le_antisymm (by apply ωSum_le; simp) (by simp)
@[simp]
theorem ωSum_eq_zero_iff : ω∑ i, f i = 0 ↔ ∀ i, f i = 0 := by
  constructor
  · simp_all [ωSum]; intro h i; apply h {i}; simp
  · simp_all

@[simp]
theorem ωSum_finset (f : ι → α) : ω∑ x : S, f x = ∑ x ∈ S, f x := by
  apply le_antisymm (ωSum_le fun S' ↦ ?_) (le_ωSum_of_le Finset.univ (by simp [Finset.sum_attach]))
  trans ∑ x ∈ S'.map ⟨(·.val), (·.val_injective)⟩, f x
  · simp
  gcongr <;> intro <;> simp_all

@[simp]
theorem ωSum_fintype [Fintype ι] (f : ι → α) : ω∑ x, f x = ∑ x, f x := by
  rw [← ωSum_finset]
  apply ωSum_eq_ωSum_of_ne_zero_bij (·.val.val) (fun ⟨_, _⟩ ↦ by simp) (by simp) (by simp)

/--
error: failed to synthesize
  ∀ {μ : Type u_4}, AddLeftMono (μ → α)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in #synth ∀ {μ : Type*}, AddLeftMono (μ → α)
instance {μ : Type*} : AddLeftMono (μ → α) := ⟨fun a b c h i ↦ by simp; gcongr; apply h⟩
/--
error: failed to synthesize
  ∀ {μ : Type u_4}, IsBotZeroClass (μ → α)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in #synth ∀ {μ : Type*}, IsBotZeroClass (μ → α)
instance {μ : Type*} : IsBotZeroClass (μ → α) := ⟨fun a b ↦ by simp⟩

@[simp]
theorem ωSum_apply {μ : Type*} {f : ι → μ → α} (y : μ) : (ω∑ x, f x) y = ω∑ x, f x y := by
  simp [ωSum, Finset.ωSup, ωSup]; congr!; ext; simp

theorem ωSum_nat_eq_ωSup {f : ℕ → α} :
      ω∑ (x : ℕ), f x
    = ωSup ⟨fun n ↦ ∑ x ∈ Finset.range n, f x, fun i j h ↦ by simp; gcongr; simp⟩ :=
  (ωSum_le fun S ↦ le_ωSup_of_le S.max₁ (by simp)).antisymm (by simp)

def Chain.next {α : Type*} [Preorder α] (c : Chain α) : Chain α :=
  ⟨(c <| · + 1), fun i j h ↦ by simp; gcongr⟩
@[simp]
theorem Chain.next_apply {α : Type*} [Preorder α] (c : Chain α) (i : ℕ) : c.next i = c (i + 1) :=
  rfl
def Chain.drop {α : Type*} [Preorder α] (c : Chain α) (n : ℕ) : Chain α :=
  ⟨(c <| · + n), fun i j h ↦ by simp; gcongr⟩
@[simp]
theorem Chain.drop_zero {α : Type*} [Preorder α] (c : Chain α) :
    c.drop 0 = c := rfl
@[simp]
theorem Chain.drop_apply {α : Type*} [Preorder α] (c : Chain α) (d i : ℕ) :
    c.drop d i = c (i + d) := rfl

theorem ωSup_next_eq_ωSup {α : Type*} [OmegaCompletePartialOrder α] {c : Chain α} :
    ωSup c.next = ωSup c := by
  apply le_antisymm
  · apply ωSup_le _ _ (fun i ↦ le_ωSup_of_le (i + 1) ?_); rfl
  · refine ωSup_le_ωSup_of_le ?_; intro i; simp; use i; gcongr; omega

theorem ωSup_drop_eq_ωSup {α : Type*} [OmegaCompletePartialOrder α] {c : Chain α} (d : ℕ) :
    ωSup (c.drop d) = ωSup c := by
  apply le_antisymm
  · apply ωSup_le _ _ (fun i ↦ le_ωSup_of_le (i + d) ?_); rfl
  · refine ωSup_le_ωSup_of_le ?_; intro i; simp; use i; gcongr; omega

theorem ωSum_nat_succ [ωScottContinuousAdd α] {f : ℕ → α} :
    ω∑ (x : ℕ), f x = ω∑ (x : ℕ), f (x + 1) + f 0 := by
  simp [ωSum_nat_eq_ωSup]; rw [← ωSup_next_eq_ωSup]
  simp [Chain.next, Finset.sum_range_succ', ωSup_add]; rfl

theorem ωSum_nat_add [ωScottContinuousAdd α] {f : ℕ → α} (n : ℕ) :
    ω∑ (x : ℕ), f x = ω∑ (x : ℕ), f (x + n) + ∑ i ∈ Finset.range n, f i := by
  simp [ωSum_nat_eq_ωSup]; rw [← ωSup_drop_eq_ωSup n]
  simp [Chain.drop, ωSup_add]
  conv => enter [1, 1, 1, 1, x]; rw [add_comm]
  congr! with m
  simp [Finset.sum_range_add]
  grind

theorem ωSum_add [ωScottContinuousAdd α] {f' : ι → α} : ω∑ i, (f i + f' i) = ω∑ i, f i + ω∑ i, f' i := by
  simp [ωSum, Finset.ωSup_add, Finset.add_ωSup, Finset.sum_add_distrib]
  rw [Finset.ωSup_ωSup_eq_ωSup']
  intro i j h S
  simp_all
  grw [h]
  simp

theorem ωSum_sum {ω : Type*} [ωScottContinuousAdd α]
    {f : ι → ω → α} {K : Finset ω} :
    ω∑ (i : ι), ∑ k ∈ K, f i k = ∑ k ∈ K, ω∑ (i : ι), f i k := by
  classical induction K using Finset.induction with simp_all [ωSum_add]

theorem ωSum_prod [ωScottContinuousAdd α]
    {f : ι × κ → α} :
    ω∑ (p : ι × κ), f p = ω∑ (b : ι) (c : κ), f (b, c) := by
  classical
  apply le_antisymm
  · apply ωSum_le fun S ↦ le_ωSum_of_le (S.image (·.fst)) ?_
    simp [← ωSum_sum]
    apply le_ωSum_of_le (S.image (·.snd))
    rw [Finset.sum_comm]
    simp [← Finset.sum_product']
    gcongr <;> grind [zero_le]
  · simp [← ωSum_sum, ωSum_le_iff]
    intro S K
    rw [Finset.sum_comm]
    simp [← Finset.sum_product']

theorem ωSum_prod' [ωScottContinuousAdd α]
    {f : ι → κ → α} :
    ω∑ (p : ι × κ), f p.fst p.snd = ω∑ (b : ι) (c : κ), f b c := ωSum_prod

theorem ωSum_prod'' {ι' : ι → Type*} [∀ i, Countable (ι' i)] [ωScottContinuousAdd α]
    {f : (i : ι) → ι' i → α} :
    ω∑ (p : ((i : ι) × ι' i)), f p.fst p.snd = ω∑ (i : ι) (c : ι' i), f i c := by
  classical
  apply le_antisymm
  · apply ωSum_le fun S ↦ le_ωSum_of_le (S.image (·.fst)) ?_
    trans ∑ i ∈ Finset.image (fun x ↦ x.fst) S, ∑ c ∈ S, if h : c.fst = i then f i (by subst_eqs; exact c.snd) else 0
    · simp
      rw [← Finset.sum_product']
      apply Finset.sum_le_sum_of_inj fun ⟨i, j⟩ ↦ ⟨i, i, j⟩
      · intro ⟨_, _⟩; simp
      · simp
      · simp; grind
    · gcongr with i hi
      apply le_ωSum_of_le (S.cosubtype i)
      apply le_of_eq
      simp
      symm
      apply Finset.sum_bij_ne_zero fun j _ _ ↦ ⟨i, j⟩
      · simp_all
      · simp
      · intro ⟨i₁, j₁⟩ h
        simp_all
        rintro ⟨_⟩
        simp_all
      · simp
  · simp [ωSum_le_iff]
    intro S
    trans ω∑ (p : (i : S) × ι' i), f p.fst p.snd
    · induction S using Finset.induction with
      | empty => simp
      | insert s S hsS ih =>
        simp_all
        grw [ih]
        simp [ωSum, Finset.ωSup_add, Finset.add_ωSup]
        intro S₁ S₂
        let S₁' : Finset ((i : ↥(insert s S)) × ι' ↑i) := S₁.map ⟨fun ⟨⟨i, hi⟩, j⟩ ↦ ⟨⟨i, Finset.mem_insert_of_mem hi⟩, j⟩, by intro ⟨⟨_, _⟩, _⟩; simp_all; grind⟩
        let S₂' : Finset ((i : ↥(insert s S)) × ι' ↑i) := S₂.map ⟨fun i ↦ ⟨⟨s, Finset.mem_insert_self s S⟩, i⟩, by intro; simp_all⟩
        apply le_ωSum_of_le (S₂' ∪ S₁')
        rw [Finset.sum_union]
        · simp [S₁', S₂']
        simp [S₁', S₂']
        refine Finset.disjoint_iff_ne.mpr ?_
        simp
        rintro a ha b i hi x hx ⟨_⟩ h
        simp_all
    · simp [ωSum_le_iff]
      intro S'
      apply le_ωSum_of_le (S'.map ⟨fun ⟨i, j⟩ ↦ ⟨i, j⟩, by intro ⟨_, _⟩; simp; grind⟩)
      simp

omit [Countable ι] [IsBotZeroClass α] in
theorem sum_ωSup [ωScottContinuousAdd α] (C : Chain (ι → α)) (S : Finset ι) :
    ∑ n ∈ S, ωSup C n = ωSup ⟨(∑ n ∈ S, C · n), fun _ _ h ↦ by simp; gcongr⟩ := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert s S h ih =>
    simp_all [add_ωSup, Chain.map]
    unfold Function.comp
    have {C : Chain (ι → α)} : ωSup C s = ωSup (C.map ⟨_, Function.monotone_eval s⟩) := rfl
    simp_all [ωSup_add]
    rw [ωSup_ωSup_eq_ωSup'] <;> simp
    intro i j hij k
    simp only [Function.comp_apply, Function.eval]
    gcongr

omit [Countable ι] [IsBotZeroClass α] in
theorem sum_ωSup' [ωScottContinuousAdd α] (C : ι → Chain α) (S : Finset ι) :
    ∑ n ∈ S, ωSup (C n) = ωSup ⟨(∑ n ∈ S, C n ·), fun _ _ h ↦ by simp; gcongr⟩ := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert s S h ih =>
    simp_all [add_ωSup, Chain.map]
    unfold Function.comp
    have {C : Chain (ι → α)} : ωSup C s = ωSup (C.map ⟨_, Function.monotone_eval s⟩) := rfl
    simp_all [ωSup_add]
    rw [ωSup_ωSup_eq_ωSup'] <;> simp
    intro i j hij k
    simp only [Function.comp_apply]
    gcongr

omit [Countable ι] [IsBotZeroClass α] in
protected theorem _root_.Finset.sum_ωSup' [ωScottContinuousAdd α] (C : ι → (Finset κ →o α)) (S : Finset ι) :
    ∑ n ∈ S, Finset.ωSup (C n) = Finset.ωSup ⟨(∑ n ∈ S, C n ·), fun _ _ h ↦ by simp; gcongr⟩ := by
  apply OmegaCompletePartialOrder.sum_ωSup'

theorem ωSum_ωSup [ωScottContinuousAdd α] (C : Chain (ι → α)) :
    ω∑ n, ωSup C n = ωSup ⟨fun x ↦ ω∑ n, C x n, fun _ _ h ↦ ωSum_mono (C.mono h)⟩ := by
  apply le_antisymm
  · simp [ωSum, sum_ωSup]
    apply fun S i ↦ le_ωSup_of_le i (Finset.le_ωSup_of_le S (by simp))
  · simp [ωSum_le_iff]; apply fun n S ↦ le_ωSum_of_le S <| Finset.sum_le_sum fun _ _ ↦ le_ωSup_of_le n (by rfl)
theorem ωSum_ωSup' [ωScottContinuousAdd α] (C : ι → Chain α) :
    ω∑ n, ωSup (C n) = ωSup ⟨fun x ↦ ω∑ n, C n x, fun _ _ h ↦ by simp only; gcongr; intro n; apply (C _).mono h⟩ := by
  apply le_antisymm
  · simp [ωSum, sum_ωSup']
    apply fun S i ↦ le_ωSup_of_le i (Finset.le_ωSup_of_le S (by simp))
  · simp [ωSum_le_iff]; apply fun n S ↦ le_ωSum_of_le S <| Finset.sum_le_sum fun _ _ ↦ le_ωSup_of_le n (by rfl)

theorem ωSum_comm [ωScottContinuousAdd α] {f : ι → κ → α} :
    ω∑ (i) (j), f i j = ω∑ (j) (i), f i j := by
  simp [ωSum, Finset.sum_ωSup']
  apply le_antisymm
  all_goals
  simp
  apply fun S K ↦ Finset.le_ωSup_of_le K (Finset.le_ωSup_of_le S (by simp; rw [Finset.sum_comm]))

open scoped Classical in
theorem _root_.Function.Injective.ωSum_eq
    {g : κ → ι} (hg : Function.Injective g) {f : ι → α}
    (hf : f.support ⊆ Set.range g) : ω∑ c, f (g c) = ω∑ b, f b := by
  apply le_antisymm
  · apply ωSum_le fun S ↦ le_ωSum_of_le (S.map ⟨g, hg⟩) (by simp)
  · apply ωSum_le fun S ↦ le_ωSum_of_le (S.preimage g (Function.Injective.injOn hg)) ?_
    grind [Finset.sum_preimage, Function.support_subset_iff]

section

variable {α : Type*} [NonAssocSemiring α] [OmegaCompletePartialOrder α] [IsBotZeroClass α] [AddLeftMono α]
variable {β : Type*} [NonAssocSemiring β] [OmegaCompletePartialOrder β] [IsBotZeroClass β] [AddLeftMono β]

theorem map_ωSum {ι : Type*} [Countable ι] (g : α →+* β) (hg : ωScottContinuous g) (f : ι → α) :
    g (ω∑ i, f i) = ω∑ i, g (f i) := by
  simp only [ωSum]
  rw [Finset.map_ωSup hg]
  simp only [OrderHom.mk_comp_mk, Function.comp_def, map_sum]

end

section

variable {𝒮 : Type*} [NonUnitalNonAssocSemiring 𝒮] [OmegaCompletePartialOrder 𝒮] [IsBotZeroClass 𝒮] [AddLeftMono 𝒮]

theorem mul_ωSum [ωScottContinuousLeftMul 𝒮] {f : ι → 𝒮} {a : 𝒮} :
    a * ω∑ i, f i = ω∑ i, a * f i := by simp [ωSum, Finset.mul_ωSup, Finset.mul_sum]

theorem ωSum_mul [ωScottContinuousRightMul 𝒮] {f : ι → 𝒮} {a : 𝒮} :
    (ω∑ i, f i) * a = ω∑ i, f i * a := by simp [ωSum, Finset.ωSup_mul, Finset.sum_mul]

theorem ωSum_eq_single
    {f : ι → α} (x : ι) (hf : ∀ (x' : ι), x' ≠ x → f x' = 0) : ω∑ x, f x = f x := by
  apply le_antisymm
  · apply ωSum_le fun S ↦ ?_
    if x ∈ S then simp_all [Finset.sum_eq_single x] else rw [Finset.sum_eq_zero (by grind)]; simp
  · apply le_ωSum_of_le {x}; simp
theorem ωSum_eq_pair
    {f : ι → α} (x₁ x₂ : ι) (h : x₁ ≠ x₂) (hf : ∀ (x' : ι), x' ≠ x₁ → x' ≠ x₂ → f x' = 0) :
    ω∑ x, f x = f x₁ + f x₂  := by
  classical
  apply le_antisymm
  · apply ωSum_le fun S ↦ ?_
    induction S using Finset.induction with simp_all
    | insert x₃ S h₃ ih =>
      if x₁ = x₃ then
        subst_eqs
        induction S using Finset.induction with simp_all
        | empty => rw [add_comm]; refine le_add_of_nonneg_of_le ?_ ?_ <;> simp
        | insert x₄ S h₄ ih =>
          if x₂ = x₄ then
            subst_eqs; simp_all
            rw [Finset.sum_eq_zero]
            · simp_all
            · intro x hx; apply hf <;> grind
          else
            grind
      else if x₂ = x₃ then
        subst_eqs
        induction S using Finset.induction with simp_all
        | empty => refine le_add_of_nonneg_of_le ?_ ?_ <;> simp
        | insert x₄ S h₄ ih =>
          if x₁ = x₄ then
            subst_eqs
            rw [Finset.sum_eq_zero]
            · grind
            · intro x hx; apply hf <;> grind
          else
            grind
      else
        grind
  · apply le_ωSum_of_le {x₁, x₂}; simp_all

theorem ωSum_eq_ωSum_of_equiv
    {f : ι → α} {g : κ → α} (e : κ ≃ ι)
    (hfg : ∀ x, f (e x) = g x) : ω∑ x, f x = ω∑ y, g y := by
  simp [← hfg]; refine (Function.Injective.ωSum_eq e.injective ?_).symm; simp

end

section

variable {𝒜 𝒮 : Type*} [OmegaCompletePartialOrder 𝒮]
variable [AddCommMonoid 𝒮] [AddLeftMono 𝒮] [IsBotZeroClass 𝒮] [DistribSMul 𝒜 𝒮]

theorem smul_ωSum [ωScottContinuousSMul 𝒜 𝒮] {f : ι → 𝒮} {a : 𝒜} :
    a • ω∑ i, f i = ω∑ i, a • f i := by
  simp [ωSum, Finset.smul_ωSup, Finset.smul_sum]

end

section

variable {ι α : Type*} [Countable ι]
variable [CompleteLattice α] [AddCommMonoid α] [AddLeftMono α] [IsBotZeroClass α]

theorem ωSum_eq_iSup_sum {f : ι → α} : ω∑ a, f a = ⨆ S, ∑ a ∈ S, f a := by
  simp [ωSum]

end

end OmegaCompletePartialOrder
