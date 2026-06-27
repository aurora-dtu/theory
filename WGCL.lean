import Mathlib.Probability.ProductMeasure
import STDX.Subst
import MDP.Optimization
import Mathlib.Algebra.Order.IsBotOne
import Mathlib.Tactic.DeriveTraversable
import Mathlib.Topology.Order.ScottTopology
import WGCL.OmegaSum

class SubsetSum (α : Type*) [AddCommMonoid α] [TopologicalSpace α] [SupSet α] where
  tsum_eq_iSup_sum_range {f : ℕ → α} : ∑' i, f i = ⨆ n, ∑ i ≤ n, f i

namespace SubsetSum

variable {α : Type*} [AddCommMonoid α] [TopologicalSpace α] [CompleteLattice α] [SubsetSum α]
variable [AddLeftMono α] [IsBotZeroClass α]
variable {ι : Type*}

theorem tsum_eq_iSup_sum [Countable ι] {f : ι → α} : ∑' i, f i = ⨆ S, ∑ i ∈ S, f i := by
  letI e : Encodable ι := Encodable.ofCountable _
  convert tsum_eq_iSup_sum_range (f := fun (i : ℕ) ↦ ((e.decode₂ ι i).map f).getD 0)
  · symm
    apply tsum_eq_tsum_of_ne_zero_bij fun ⟨x, h⟩ ↦ e.encode x
    · intro ⟨x, _⟩ ⟨y, _⟩; simp
    · simp [Option.getD_eq_iff]
      grind [Encodable.decode₂_ne_none_iff, Encodable.decode₂_encode, Encodable.encode_inj]
    · simp
  · apply le_antisymm
    · refine iSup_mono' ?_
      intro S
      use (S.map e.encode' ∪ {0}).max' (by simp)
      trans ∑ i ∈ S.map e.encode', ((e.decode₂ _ i).map f).getD 0
      · simp
        gcongr with i hi
        simp [Encodable.encode', Encodable.decode₂_encode]
      · gcongr
        · simp
        · intro n
          simp_all [Encodable.encode']
          rintro x h ⟨_⟩
          apply Finset.le_max'
          simp [h]
    · refine iSup_mono' ?_
      intro n
      let S := (Finset.range (n + 1)).filterMap (Encodable.decode₂ ι)
          (by simp; grind [Encodable.decode₂_ne_none_iff, Encodable.decode₂_encode])
      use S
      simp [S]
      apply le_of_eq
      symm
      apply Finset.sum_bij_ne_zero fun a _ _ ↦ Encodable.encode a
      · simp
        grind [Encodable.decode₂_ne_none_iff, Encodable.decode₂_encode, Encodable.encode_inj]
      · simp
      · grind [Encodable.decode₂_ne_none_iff, Encodable.decode₂_encode, Encodable.encode_inj]
      · simp

theorem tsum_eq_iSup_sum_of_support {f : ι → α} (h : f.support.Countable) :
    ∑' i, f i = ⨆ S, ∑ i ∈ S, f i := by
  letI : Countable ↑(Function.support f) := Set.Countable.to_subtype h
  rw [← @tsum_subtype_support]
  rw [tsum_eq_iSup_sum]
  apply le_antisymm
  · refine iSup_mono' ?_
    intro s
    use s.map ⟨Subtype.val, Subtype.val_injective⟩
    simp
  · refine iSup_mono' ?_
    intro s
    classical
    use s.filterMap (fun i ↦ if h : _ then some ⟨i, h⟩ else none) (by simp; grind)
    simp
    apply le_of_eq
    symm
    apply Finset.sum_bij_ne_zero fun a _ _ ↦ a.val <;> simp <;> grind

end SubsetSum

namespace OmegaCompletePartialOrder

section lfp

variable {α : Type*} [OmegaCompletePartialOrder α]
variable {β : Type*} [OmegaCompletePartialOrder β]

@[gcongr]
theorem fixedPoints.iterateChain_mono {f g : α →o α} {a : α} {hf : a ≤ f a} {hg : a ≤ g a} (h : f ≤ g) :
    fixedPoints.iterateChain f a hf ≤ fixedPoints.iterateChain g a hg := by
  intro i; use i
  induction i with
  | zero => simp_all [iterateChain]
  | succ i ih =>
    simp_all [fixedPoints.iterateChain, -Function.iterate_succ, Function.iterate_succ']
    grw [ih]
    apply h

@[simp]
theorem Chain.map_const {c : Chain α} (b : β) :
    c.map ⟨fun _ ↦ b, monotone_const⟩ = ⟨fun _ ↦ b, monotone_const⟩ := rfl
@[simp]
theorem Chain.map_zero [Zero β] {c : Chain α} :
    c.map ⟨(0 : α → β), Pi.zero_mono⟩ = ⟨0, Pi.zero_mono⟩ := rfl

@[simp]
theorem ωSup_zero {α : Type*} [OmegaCompletePartialOrder α] [Zero α] :
    ωSup ⟨(@OfNat.ofNat (ℕ → α) 0 Zero.toOfNat0 : ℕ → α), Pi.zero_mono⟩ = 0 := by
  apply ωSup_const

variable [OrderBot α]

attribute [-simp] Function.iterate_succ
attribute [local simp] Function.iterate_succ'

def lfp : (α →𝒄 α) →𝒄 α := ⟨⟨fun f ↦ ωSup (fixedPoints.iterateChain f ⊥ bot_le),
  by intro f g h; simp only; gcongr; assumption⟩,
  by
    simp
    intro c
    have hc {i} := (c i).map_ωSup'
    simp at hc
    apply le_antisymm
    · apply fixedPoints.ωSup_iterate_le_prefixedPoint
      · simp [fixedPoints.iterateChain]
        intro i
        rw [hc]
        simp
        intro j
        rw [hc]
        simp
        intro k
        apply le_ωSup_of_le (i + j)
        apply le_ωSup_of_le (k + 1)
        simp
        gcongr
        · omega
        · induction k with simp_all | succ => gcongr; omega
      · simp
    · simp
      intro i j
      simp [fixedPoints.iterateChain]
      apply le_ωSup_of_le j
      simp
      induction j with simp_all | succ j ih => grw [ih]; apply le_ωSup_of_le i; simp⟩

variable (f : α →𝒄 α)

theorem lfp_le {a : α} (h : f a ≤ a) : lfp f ≤ a :=
  fixedPoints.ωSup_iterate_le_prefixedPoint f ⊥ bot_le h bot_le
theorem lfp_le_fixed {a : α} (h : f a = a) : lfp f ≤ a :=
  (lfp_le f h.le).trans (le_refl _)
theorem lfp_mem_fixedPoint : lfp f ∈ Function.fixedPoints f :=
  fixedPoints.ωSup_iterate_mem_fixedPoint _ _ _
@[simp]
theorem map_lfp : f (lfp f) = lfp f := lfp_mem_fixedPoint f
theorem isLeast_lfp : IsLeast {a | f a ≤ a} (lfp f) := by
  exact ⟨by simp, by apply lfp_le⟩

theorem lfp_ωSup {c : Chain (α →𝒄 α)} : lfp (ωSup c) = ωSup (c.map lfp.toOrderHom) :=
  lfp.map_ωSup' c

end lfp

section

class MulLeftContinuous (α : Type*) [OmegaCompletePartialOrder α] [Mul α] where
  mul_right_continuous (a : α) : ωScottContinuous fun x ↦ a * x
class MulRightContinuous (α : Type*) [OmegaCompletePartialOrder α] [Mul α] where
  mul_left_continuous (a : α) : ωScottContinuous fun x ↦ x * a
class AddLeftContinuous (α : Type*) [OmegaCompletePartialOrder α] [Add α] where
  add_right_continuous (a : α) : ωScottContinuous fun x ↦ a + x
class AddRightContinuous (α : Type*) [OmegaCompletePartialOrder α] [Add α] where
  add_left_continuous (a : α) : ωScottContinuous fun x ↦ x + a

class MulContinuous (α : Type*) [OmegaCompletePartialOrder α] [Mul α] extends
    MulLeftContinuous α, MulRightContinuous α
class AddContinuous (α : Type*) [OmegaCompletePartialOrder α] [Add α] extends
    AddLeftContinuous α, AddRightContinuous α

insert_to_additive_translation MulLeftContinuous AddLeftContinuous
insert_to_additive_translation MulLeftContinuous.mul_right_continuous AddLeftContinuous.add_right_continuous
insert_to_additive_translation MulRightContinuous AddRightContinuous
insert_to_additive_translation MulRightContinuous.mul_left_continuous AddRightContinuous.add_left_continuous
insert_to_additive_translation MulContinuous AddContinuous

variable {α : Type*} [OmegaCompletePartialOrder α]

instance [Mul α] [MulLeftContinuous α] : MulLeftMono α where
  elim a _ _ h := (MulLeftContinuous.mul_right_continuous a).monotone h
instance [Mul α] [MulRightContinuous α] : MulRightMono α where
  elim a _ _ h := (MulRightContinuous.mul_left_continuous a).monotone h
instance [Mul α] [MulLeftContinuous α] [MulRightContinuous α] : MulContinuous α where

instance [Add α] [AddLeftContinuous α] : AddLeftMono α where
  elim a _ _ h := (AddLeftContinuous.add_right_continuous a).monotone h
instance [Add α] [AddRightContinuous α] : AddRightMono α where
  elim a _ _ h := (AddRightContinuous.add_left_continuous a).monotone h
instance [Add α] [AddLeftContinuous α] [AddRightContinuous α] : AddContinuous α where

theorem add_ωSup [Add α] [AddLeftContinuous α] {c : Chain α} :
    a + ωSup c = ωSup (c.map ⟨(a + ·), fun _ _ _ ↦ by simp; gcongr⟩) :=
  (AddLeftContinuous.add_right_continuous a).map_ωSup _
theorem ωSup_add [Add α] [AddRightContinuous α] {c : Chain α} :
    ωSup c + a = ωSup (c.map ⟨(· + a), fun _ _ _ ↦ by simp; gcongr⟩) :=
  (AddRightContinuous.add_left_continuous a).map_ωSup _
theorem ωSup_add_ωSup [Add α] [AddContinuous α] {a b : Chain α} :
    ωSup a + ωSup b = ωSup ⟨fun i ↦ a i + b i, fun i j h ↦ by simp_all; gcongr⟩ := by
  simp [add_ωSup, ωSup_add]
  apply le_antisymm
  · simp
    intro i j
    apply le_ωSup_of_le (i + j)
    simp
    gcongr <;> omega
  · simp
    intro i
    refine le_ωSup_of_le i (le_ωSup_of_le i ?_)
    simp
theorem AddLeftContinuous.of_add_ωSup [Add α] [AddLeftMono α]
    (h : ∀ a (c : Chain α), a + ωSup c = ωSup (c.map ⟨(a + ·), fun _ _ _ ↦ by simp; gcongr⟩)) :
    AddLeftContinuous α where
  add_right_continuous _ := ωScottContinuous_iff_monotone_map_ωSup.mpr ⟨add_right_mono, h _⟩
theorem AddRightContinuous.of_ωSup_add [Add α] [AddRightMono α]
    (h : ∀ a (c : Chain α), ωSup c + a = ωSup (c.map ⟨(· + a), fun _ _ _ ↦ by simp; gcongr⟩)) :
    AddRightContinuous α where
  add_left_continuous _ := ωScottContinuous_iff_monotone_map_ωSup.mpr ⟨add_left_mono, h _⟩

theorem mul_ωSup [Mul α] [MulLeftContinuous α] {c : Chain α} :
    a * ωSup c = ωSup (c.map ⟨(a * ·), fun _ _ _ ↦ by simp; gcongr⟩) :=
  (MulLeftContinuous.mul_right_continuous a).map_ωSup _
theorem ωSup_mul [Mul α] [MulRightContinuous α] {c : Chain α} :
    ωSup c * a = ωSup (c.map ⟨(· * a), fun _ _ _ ↦ by simp; gcongr⟩) :=
  (MulRightContinuous.mul_left_continuous a).map_ωSup _
theorem ωSup_mul_ωSup [Mul α] [MulContinuous α] {a b : Chain α} :
    ωSup a * ωSup b = ωSup ⟨fun i ↦ a i * b i, fun i j h ↦ by simp_all; gcongr⟩ := by
  simp [mul_ωSup, ωSup_mul]
  apply le_antisymm
  · simp
    intro i j
    apply le_ωSup_of_le (i + j)
    simp
    gcongr <;> omega
  · simp
    intro i
    refine le_ωSup_of_le i (le_ωSup_of_le i ?_)
    simp
theorem MulLeftContinuous.of_mul_ωSup [Mul α] [MulLeftMono α]
    (h : ∀ a (c : Chain α), a * ωSup c = ωSup (c.map ⟨(a * ·), fun _ _ _ ↦ by simp; gcongr⟩)) :
    MulLeftContinuous α where
  mul_right_continuous _ := ωScottContinuous_iff_monotone_map_ωSup.mpr ⟨mul_right_mono, h _⟩
theorem MulRightContinuous.of_ωSup_mul [Mul α] [MulRightMono α]
    (h : ∀ a (c : Chain α), ωSup c * a = ωSup (c.map ⟨(· * a), fun _ _ _ ↦ by simp; gcongr⟩)) :
    MulRightContinuous α where
  mul_left_continuous _ := ωScottContinuous_iff_monotone_map_ωSup.mpr ⟨mul_left_mono, h _⟩

instance [Add α] [AddLeftMono α] : AddLeftMono (ι → α) :=
  ⟨fun a b c h i ↦ by simp; gcongr; apply h⟩
instance [Add α] [AddRightMono α] : AddRightMono (ι → α) :=
  ⟨fun a b c h i ↦ by simp [Function.swap]; gcongr; apply h⟩

instance [Add α] [AddLeftContinuous α] : AddLeftContinuous (ι → α) := AddLeftContinuous.of_add_ωSup <| by
  intro f c
  ext i
  show _ + ωSup (c.map ⟨(· i), _⟩) = _
  simp [add_ωSup]
  rfl
instance [Add α] [AddRightContinuous α] : AddRightContinuous (ι → α) := AddRightContinuous.of_ωSup_add <| by
  intro f c
  ext i
  show ωSup (c.map ⟨(· i), _⟩) + _ = _
  simp [ωSup_add]
  rfl

instance [Mul α] [MulLeftMono α] : MulLeftMono (ι → α) :=
  ⟨fun a b c h i ↦ by simp; gcongr; apply h⟩
instance [Mul α] [MulRightMono α] : MulRightMono (ι → α) :=
  ⟨fun a b c h i ↦ by simp [Function.swap]; gcongr; apply h⟩

instance [Mul α] [MulLeftContinuous α] : MulLeftContinuous (ι → α) := MulLeftContinuous.of_mul_ωSup <| by
  intro f c
  ext i
  show _ * ωSup (c.map ⟨(· i), _⟩) = _
  simp [mul_ωSup]
  rfl
instance [Mul α] [MulRightContinuous α] : MulRightContinuous (ι → α) := MulRightContinuous.of_ωSup_mul <| by
  intro f c
  ext i
  show ωSup (c.map ⟨(· i), _⟩) * _ = _
  simp [ωSup_mul]
  rfl

end

variable {α β : Type*} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β] in
def ContinuousHom.ofFun₂ (f : α → β) (h₁ : Monotone f)
    (h₂ : ∀ (c : Chain α), ωSup (c.map ⟨f, h₁⟩) = f (ωSup c)) :
    α →𝒄 β := ⟨⟨f, h₁⟩, fun c ↦ by simp [h₂]⟩


section

open ContinuousHom

variable {α β : Type*} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]

@[simps!]
instance [Zero β] :
    Zero (α →𝒄 β) where
  zero := ContinuousHom.const 0

@[simps!]
instance [Add β] [AddContinuous β] :
    Add (α →𝒄 β) where
  add a b := by
    refine ofFun₂ (a.toFun + b.toFun) ?_ ?_
    · intro x y h; simp; gcongr
    · intro c
      have := a.map_ωSup'
      have := b.map_ωSup'
      simp_all [ωSup_add_ωSup]
      rfl

instance [Add β] [AddContinuous β] : AddLeftMono (α →𝒄 β) where
  elim a b c h e := by simp_all; gcongr
instance [Add β] [AddContinuous β] : AddRightMono (α →𝒄 β) where
  elim a b c h e := by simp_all; gcongr

instance [AddSemigroup β] [AddContinuous β] :
    AddSemigroup (α →𝒄 β) where
  add_assoc a b c := by ext; simp [add_assoc]

instance [AddZeroClass β] [AddContinuous β] :
    AddZeroClass (α →𝒄 β) where
  zero_add a := by ext; simp
  add_zero a := by ext; simp

-- @[simps?]
instance [AddMonoid β] [AddContinuous β] :
    AddMonoid (α →𝒄 β) where
  nsmul n a := ofFun₂ (n • a.toFun) (by intro x y h; simp_all; gcongr) (by
    have := a.map_ωSup'
    simp_all
    intro c
    induction n with
    | zero => simp
    | succ n ih =>
      symm at ih
      simp_all [succ_nsmul, ωSup_add, add_ωSup]
      simp [Chain.map]
      simp [OrderHom.comp]
      unfold Function.comp
      simp
      apply le_antisymm
      · simp
        intro i
        refine le_ωSup_of_le i (le_ωSup_of_le i ?_)
        simp
      · simp
        intro i j
        apply le_ωSup_of_le (i + j)
        simp
        gcongr <;> omega)
  nsmul_zero x := by ext; simp [ofFun₂]
  nsmul_succ n x := by ext; simp [ofFun₂, succ_nsmul]

instance [AddMonoid β] [AddContinuous β] : AddLeftContinuous (α →𝒄 β) :=
  AddLeftContinuous.of_add_ωSup <| by
    intro f x; ext a; simp [Chain.map, OrderHom.comp, add_ωSup]; rfl
instance [AddMonoid β] [AddContinuous β] : AddRightContinuous (α →𝒄 β) :=
  AddRightContinuous.of_ωSup_add <| by
    intro f x; ext a; simp [Chain.map, OrderHom.comp, ωSup_add]; rfl

instance [AddMonoid β] [AddLeftContinuous β] : HAdd β (α →𝒄 β) (α →𝒄 β) where
  hAdd a b :=
    .ofFun₂ (fun x ↦ a + b x) (fun _ _ _ ↦ by simp; gcongr)
      (by intro; have := b.map_ωSup'; simp_all [add_ωSup]; rfl)

@[simps!]
instance {α 𝒲 ℳ : Type*} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder ℳ] [SMul 𝒲 ℳ] [SMulContinuous 𝒲 ℳ] :
    SMul 𝒲 (α →𝒄 ℳ) where
  smul w x := ofFun₂ (w • x.toFun)
        (by intro f g h; simp; gcongr) (by intro c; have := x.map_ωSup'; simp_all [smul_ωSup]; rfl)

instance {𝒲 ℳ : Type*} [Monoid 𝒲] [AddMonoid ℳ] [OmegaCompletePartialOrder ℳ] [AddContinuous ℳ] [DistribMulAction 𝒲 ℳ] [SMulContinuous 𝒲 ℳ] :
    DistribMulAction 𝒲 (α →𝒄 ℳ) where
  mul_smul n m x := by ext; simp [mul_smul]
  one_smul x := by ext i; simp
  smul_zero x := by ext; simp
  smul_add n m x := by ext; simp

end


end OmegaCompletePartialOrder

variable (Γ B I : Type*) (E : Γ → Type*) (W M : Type*) in
inductive WGCL where
  | assign (x : Γ) (e : E x)
  | seq (C₁ C₂ : WGCL)
  | ite (φ : B) (C₁ C₂ : WGCL)
  | nonDet (C₁ C₂ : WGCL)
  | weigh (a : W)
  | reward (a : M)
  | loop (φ : B) (inv : I) (C : WGCL)
deriving Functor, LawfulFunctor

namespace WGCL

section

variable {𝒲 ℳ : Type*} [Monoid 𝒲] [AddMonoid ℳ] [DistribMulAction 𝒲 ℳ]

variable {v w : 𝒲}
variable {a b : ℳ}

#check (0 : ℳ)
#check (1 : 𝒲)
#check (· + · : ℳ → ℳ → ℳ)
#check (· * · : 𝒲 → 𝒲 → 𝒲)
#check (· • · : 𝒲 → ℳ → ℳ)

example : (v * w) • a = v • (w • a) := mul_smul v w a
example : v • (a + b) = v • a + v • b := DistribSMul.smul_add v a b
example : 1 • a = a := one_nsmul a
example : v • (0 : ℳ) = 0 := DistribMulAction.smul_zero v

-- Weightings are also 𝒲-module's
#synth ∀ α, DistribMulAction 𝒲 (α → ℳ)

-- Semirings 𝒮 form 𝒮-module over 𝒮
#synth ∀ 𝒮 [Semiring 𝒮], DistribMulAction 𝒮 𝒮

end

instance {α β ℳ : Type*} {Γ : β → Type*} [i : Substitution α Γ] : Substitution (α → ℳ) Γ where
  subst a b c := a (i.subst c b)

variable {α : Type*}


@[notation_class]
class Iverson (α : Type*) (β : Type*) where
  /-- Iverson brackets `i[b]` -/
  iver : α → β → β

@[inherit_doc] notation "i[" b "]" => Iverson.iver b
@[inherit_doc Iverson.iver] notation "i[" b "]'" t:max => (Iverson.iver b : t)

instance {β : Type*} [Zero β] : Iverson Bool β where iver p := (if p then · else 0)
@[simps!]
instance {α β P : Type*} [i : Iverson P β] : Iverson (α → P) (α → β) where
  iver p f a := i.iver (p a) (f a)

open OmegaCompletePartialOrder

class IversonMono (α β : Type*) [Preorder β] [i : Iverson α β] where
  iver_mono (a : α) : Monotone (i.iver a)

attribute [gcongr] IversonMono.iver_mono

class IversonContinuous (α β : Type*) [OmegaCompletePartialOrder β] [i : Iverson α β] extends
    IversonMono α β where
  iver_continuous (a : α) : ωScottContinuous (i.iver a)

theorem iver_ωSup {α β : Type*} [OmegaCompletePartialOrder β] [i : Iverson α β] [IversonContinuous α β] {p : α} {c : Chain β} :
    i.iver p (ωSup c) = ωSup (c.map ⟨i[p], IversonMono.iver_mono p⟩) := by
  have := (IversonContinuous.iver_continuous p (β := β)).map_ωSup
  simp_all

instance {α β P : Type*} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β] [i : Iverson P β] [IversonContinuous P β] :
    Iverson P (α →𝒄 β) where
  iver p f :=
    ContinuousHom.ofFun₂ (fun a ↦ i.iver p (f a))
      (by intro a b h; simp; gcongr)
      (by
        intro c
        have := f.map_ωSup'
        have := (IversonContinuous.iver_continuous p (β := β)).map_ωSup
        simp_all
        rfl)

instance {α β P : Type*} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β] [i : Iverson P β] [IversonContinuous P β] :
    IversonMono P (α →𝒄 β) where
  iver_mono p f g h i := by
    simp
    simp [Iverson.iver, ContinuousHom.ofFun₂]
    gcongr

instance {α β P : Type*} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β] [i : Iverson P β] [IversonContinuous P β] :
    IversonContinuous P (α →𝒄 β) where
  iver_continuous p := by
    refine ωScottContinuous.of_monotone_map_ωSup ?_
    use IversonMono.iver_mono p
    intro c
    ext a
    simp [Iverson.iver, ContinuousHom.ofFun₂]
    simp [iver_ωSup]
    rfl

instance {α β P : Type*} [Iverson P β] [Preorder β] [IversonMono P β] : IversonMono (α → P) (α → β) where
  iver_mono p f g h a := by simp; gcongr; apply h
instance {α β P : Type*} [Iverson P β] [OmegaCompletePartialOrder β] [IversonContinuous P β] :
    IversonContinuous (α → P) (α → β) where
  iver_continuous p := by
    refine ωScottContinuous_iff_monotone_map_ωSup.mpr ?_
    use IversonMono.iver_mono p
    intro c
    ext a
    show i[p a] (ωSup (c.map ⟨(· a), _⟩)) = _
    simp [iver_ωSup]
    rfl

instance {ι : Type*} [Add α] [LE α] [AddLeftMono α] : AddLeftMono (ι → α) := ⟨fun a b c h σ ↦ by
  simp only [Pi.add_apply]; gcongr; apply h⟩
instance {ι : Type*} [Add α] [LE α] [AddRightMono α] : AddRightMono (ι → α) := ⟨fun a b c h σ ↦ by
  simp only [Pi.add_apply, Function.swap]; gcongr; apply h⟩

instance {α β γ : Type*} [SMul γ β] [Preorder β] [SMulMono γ β] : SMulMono γ (α → β) where
  smul_le_smul_left := by intro g b₁ b₂ h x; simp; gcongr; apply h

instance {α β : Type*} [LE β] [Zero β] [IsBotZeroClass β] : IsBotZeroClass (α → β) where
  isBot_zero := by intro _ _; simp
instance {α β : Type*} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β] [Zero β] [IsBotZeroClass β] :
    IsBotZeroClass (α →𝒄 β) where
  isBot_zero := by intro _ _; simp

instance {α β : Type*} [LE β] [Zero β] [IsBotZeroClass β] : OrderBot (α → β) :=
  IsBotZeroClass.toOrderBot _
instance {α β : Type*} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β] [Zero β] [IsBotZeroClass β] :
    OrderBot (α →𝒄 β) :=
  IsBotZeroClass.toOrderBot _

class SubstitutionMono (α : Type*) {ι : outParam (Type*)} (β : outParam (ι → Type*)) [Preorder α] [i : Substitution α β] where
  subst_mono {a b : α} : a ≤ b → i.subst a x ≤ i.subst b x

attribute [gcongr] SubstitutionMono.subst_mono

class SubstitutionContinuous (α : Type*) {ι : outParam (Type*)} (β : outParam (ι → Type*)) [OmegaCompletePartialOrder α] [i : Substitution α β] extends SubstitutionMono α β where
  subst_continuous (a) : ωScottContinuous (i.subst · a)

theorem subst_ωSup {α ι : Type*} {β : ι → Type*}   [OmegaCompletePartialOrder α] [i : Substitution α β] [SubstitutionContinuous α β] (c : Chain α) (b : Sigma β) :
    Substitution.subst (ωSup c) b = ωSup (c.map ⟨fun x ↦ Substitution.subst x b, fun _ _ _ ↦ by simp; gcongr⟩) := by
  apply (SubstitutionContinuous.subst_continuous b (α := α)).map_ωSup

instance {α β Γ : Type*} {E : Γ → Type*} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β] [Substitution α E] [SubstitutionContinuous α E] :
    Substitution (α →𝒄 β) E where
  subst a b :=
    ContinuousHom.ofFun₂ (fun x ↦ a (Substitution.subst x b))
      (by
        intro i j h
        simp
        gcongr)
      (by
        intro c
        have := (SubstitutionContinuous.subst_continuous b (α := α)).map_ωSup
        have := a.map_ωSup'
        simp_all
        rfl)

instance {α β Γ : Type*} {E : Γ → Type*} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β] [Substitution α E] [SubstitutionContinuous α E] :
    SubstitutionMono (α → β) E where
  subst_mono c i := c (Substitution.subst i _)
instance {α β Γ : Type*} {E : Γ → Type*} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β] [Substitution α E] [SubstitutionContinuous α E] :
    SubstitutionContinuous (α → β) E where
  subst_continuous s := by
    refine ωScottContinuous.of_monotone_map_ωSup ?_
    use by intro _ _ _; simp; gcongr
    intro c
    ext a
    simp [Substitution.subst, ContinuousHom.ofFun₂]
    rfl

instance {α β Γ : Type*} {E : Γ → Type*} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β] [Substitution α E] [SubstitutionContinuous α E] :
    SubstitutionMono (α →𝒄 β) E where
  subst_mono c i := c (Substitution.subst i _)
instance {α β Γ : Type*} {E : Γ → Type*} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β] [Substitution α E] [SubstitutionContinuous α E] :
    SubstitutionContinuous (α →𝒄 β) E where
  subst_continuous s := by
    refine ωScottContinuous.of_monotone_map_ωSup ?_
    use by intro _ _ _; simp; gcongr
    intro c
    ext a
    simp [Substitution.subst, ContinuousHom.ofFun₂]
    rfl

abbrev WT (α β : Type*) [OmegaCompletePartialOrder β] := (α → β) →𝒄 (α → β)

notation "i[" φ "]" => i[φ]'(WT _ _)

@[gcongr]
theorem _root_.ContinuousHom.const_mono {α β : Type*} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β] :
    Monotone (ContinuousHom.const (α := α) (β := β)) := fun _ _ h _ ↦ h

section

variable {𝒲 ℳ : Type*} [Monoid 𝒲] [AddMonoid ℳ] [DistribMulAction 𝒲 ℳ]
variable [OmegaCompletePartialOrder ℳ] [IsBotZeroClass ℳ]
variable [AddContinuous ℳ] [SMulContinuous 𝒲 ℳ]
variable [Compl B]
variable [Iverson B (α → ℳ)] [IversonContinuous B (α → ℳ)]

variable {Γ : Type*}
variable {E : Γ → Type*}
variable [Substitution α (ι := Γ) E]
variable [SubstitutionContinuous (α → ℳ) (ι := Γ) E]

-- open ContinuousHom in
-- def wp : WGCL Γ B I E 𝒲 → WT α ℳ
--   | .assign x e => id[x ↦ e]
--   | .seq C₁ C₂ => C₁.wp.comp C₂.wp
--   | .ite φ C₁ C₂ => i[φ] C₁.wp + i[φᶜ] C₂.wp
--   | .nonDet C₁ C₂ => C₁.wp + C₂.wp
--   | .weigh a => a • (id : WT _ _)
--   | .loop φ _ C =>
--     ofFun₂ (fun f ↦ lfp <| i[φ] (const f) + i[φᶜ] C.wp) (by intro f g h; simp; gcongr)
--       (fun c ↦ by
--         have : (const (ωSup c) : (α → ℳ) →𝒄 α → ℳ) =
--                 ωSup ⟨fun x ↦ const (c x), fun _ _ h ↦ by simp; gcongr⟩ := by rfl
--         simp only [this, iver_ωSup, ωSup_add, lfp_ωSup]
--         rfl)

end

section

variable {𝒲 ℳ : Type*} [Monoid 𝒲] [AddMonoid ℳ] [DistribMulAction 𝒲 ℳ]
variable [OmegaCompletePartialOrder ℳ] [IsBotZeroClass ℳ]
variable [AddContinuous ℳ] [SMulContinuous 𝒲 ℳ]
variable [Compl B]
variable [Iverson B ℳ] [IversonContinuous B ℳ]

variable {Γ : Type*} {E : Γ → Type*}
variable [Substitution ℳ E] [SubstitutionContinuous ℳ E]

instance : OrderBot ℳ := IsBotZeroClass.toOrderBot _

open ContinuousHom in
def wp : WGCL Γ B I E 𝒲 ℳ → (ℳ →𝒄 ℳ)
  | .assign x e => id[x ↦ e]
  | .seq C₁ C₂ => C₁.wp.comp C₂.wp
  | .ite φ C₁ C₂ => i[φ] C₁.wp + i[φᶜ] C₂.wp
  | .nonDet C₁ C₂ => C₁.wp + C₂.wp
  | .weigh a => a • (id : ℳ →𝒄 ℳ)
  | .reward a => a + (id : ℳ →𝒄 ℳ)
  | .loop φ _ C =>
    ofFun₂ (fun f ↦ lfp <| i[φ] (const f) + i[φᶜ] C.wp) (by intro f g h; simp; gcongr)
      (fun c ↦ by
        have : (const (ωSup c) : ℳ →𝒄 ℳ) =
                ωSup ⟨fun x ↦ const (c x), fun _ _ h ↦ by simp; gcongr⟩ := by rfl
        simp only [this, iver_ωSup, ωSup_add, lfp_ωSup]
        rfl)

end

section

universe u v

variable {Γ : Type*} (E : Γ → Type u) (D : Type u → Type*) (𝒲 ℳ : Type*) in
inductive HeyW where
  /-- `x :≈ μ` -/
  | Assign (x : Γ) (μ : D (E x))
  /-- `weigh μ` -/
  | Weigh (a : 𝒲)
  /-- `reward μ` -/
  | Reward (a : ℳ)
  /-- `S₁ ; S₂` -/
  | Seq (S₁ S₂ : HeyW)
  --
  /-- `if (⊓) { S₁ } else { S₂ }` -/
  | IfInf (S₁ S₂ : HeyW)
  /-- `assert φ` -/
  | Assert (φ : ℳ)
  /-- `assume φ` -/
  | Assume (φ : ℳ)
  /-- `havoc x` -/
  | Havoc (x : Γ)
  /-- `validate` -/
  | Validate
  --
  /-- `if (⊔) { S₁ } else { S₂ }` -/
  | IfSup (S₁ S₂ : HeyW)
  /-- `coassert φ` -/
  | Coassert (φ : ℳ)
  /-- `coassume φ` -/
  | Coassume (φ : ℳ)
  /-- `cohavoc x` -/
  | Cohavoc (x : Γ)
  /-- `covalidate` -/
  | Covalidate

variable {Γ : Type*} {E : Γ → Type u} {D : Type u → Type*} {𝒲 : Type*}

infixr:50 " ;; " => HeyW.Seq

def HeyW.Skip [Zero 𝒲] : HeyW E D 𝒲 ℳ := .Reward 0
def HeyW.If [Compl ℳ] (b : ℳ) (S₁ S₂ : HeyW E D 𝒲 ℳ) : HeyW E D 𝒲 ℳ :=
  .IfInf (.Assume b ;; S₁) (.Assume bᶜ ;; S₂)
def HeyW.Havocs [Zero 𝒲] (xs : List Γ) : HeyW E D 𝒲 ℳ :=
  match xs with
  | [] => .Skip
  | [x] => .Havoc x
  | x::xs => .Havoc x ;; .Havocs xs
def HeyW.Cohavocs [Zero 𝒲] (xs : List Γ) : HeyW E D 𝒲 ℳ :=
  match xs with
  | [] => .Skip
  | [x] => .Cohavoc x
  | x::xs => .Cohavoc x ;; .Cohavocs xs

end

section

variable {Γ B 𝒲 ℳ : Type*}
variable {E : Γ → Type u}
variable {D : Type u → Type*}
variable [SMul 𝒲 ℳ]
variable [Zero 𝒲] [Compl ℳ] [One ℳ]
variable [Iverson B ℳ]

-- def vc : WGCL Γ B I E 𝒲 → I → I
--   | .assign x e => id[x ↦ e]
--   | .seq C₁ C₂ => C₁.vc.comp C₂.vc
--   | .ite φ C₁ C₂ => i[φ] C₁.vc + Iverson.iver φᶜ C₁.vc
--   | .nonDet C₁ C₂ => C₁.vc + C₁.vc
--   | .weigh a => a • (id : I → I)
--   | .loop φ inv C =>
--     sorry

class Thingy (α β 𝒲 : Type*) where
  dirac : β → α
  read : α → 𝒲

def Thingy.idk {α β 𝒲 ℳ : Type*} [Thingy α β 𝒲] (μ : α) (f : β → ℳ) : ℳ := sorry

open scoped Optimization.Notation

def HeyW.mods : HeyW E D 𝒲 ℳ → List Γ := sorry

variable [∀ x, Thingy (D (E x)) (E x) 𝒲]

variable (O : Optimization) in
def encode : WGCL Γ B ℳ E 𝒲 ℳ → HeyW E D 𝒲 ℳ
  | .assign x e => .Assign x (Thingy.dirac 𝒲 e)
  | .seq C₁ C₂ => C₁.encode ;; C₂.encode
  | .ite φ C₁ C₂ =>
    .IfInf (.Assume (i[φ] 1) ;; C₁.encode) (.Assume (i[φ] 1)ᶜ ;; C₂.encode)
    -- .If (i[φ] 1) C₁.encode C₂.encode
  | .nonDet C₁ C₂ =>
    match O with
    | 𝒜 => .IfSup C₁.encode C₂.encode
    | 𝒟 => .IfInf C₁.encode C₂.encode
  | .weigh a => .Weigh a
  | .reward a => .Reward a
  | .loop φ I C =>
    let C := C.encode
    .Coassert I ;; .Cohavocs C.mods ;; .Covalidate ;; .Coassume I ;;
    .If (i[φ] 1) (C ;; .Coassert I) .Skip
    -- coassert(@I) ; cohavocs(@C.mods) ; covalidate ; coassume(@I) ;
    -- if (@b) { @C ; coassert(@I) ; coassume(⊤) }

variable [Min ℳ] [Max ℳ] [HImp ℳ] [HNot ℳ] [SDiff ℳ] [Add ℳ]

variable [Substitution ℳ E]

example {α : Type*} (P : Set α → ℝ) (h₀ : ∀ X, 0 < P X) (hP : ∀ X Y, P X * P Y ≤ P (X ∩ Y)) (hP₂ : ∀ X Y, Disjoint X Y → P (X ∪ Y) = P X + P Y) (A B C : Set α) (h : C ⊆ B) :
    P (A ∩ B) / P B ≤ P (A ∩ C) / P C := by
  let D := B \ C
  have : B = D ∪ C := by exact Eq.symm (Set.diff_union_of_subset h)
  simp_all [Set.inter_union_distrib_left]
  have : Disjoint C D := Set.disjoint_sdiff_right
  have : Disjoint (A ∩ D) (A ∩ C) := by simp_all [Disjoint]
  simp_all [div_le_div_iff₀, add_mul]
  have : Disjoint D C := Set.disjoint_sdiff_left
  simp_all [div_le_div_iff₀, mul_add]
  sorry

def HeyW.vp (C : HeyW E D 𝒲 ℳ) (φ : ℳ) : ℳ :=
  match C with
  -- | heyvl {@x :≈ @μ} => (μ.map (fun v ↦ φ[x ↦ v])).toExpr
  | .Assign x μ => Thingy.idk μ fun (v : E x) ↦ (φ[x ↦ v] : ℳ)
  -- | heyvl {reward(@a)} => φ + a
  | .Reward w => w + φ
  -- | heyvl {weigh(@a)} => φ + a
  | .Weigh w => w • φ
  -- | heyvl {@S₁ ; @S₂} => S₁.vp (S₂.vp φ)
  | .Seq S₁ S₂ => S₁.vp (S₂.vp φ)
  -- | heyvl {if (⊓) {@S₁} else {@S₂}} => S₁.vp φ ⊓ S₂.vp φ
  | .IfInf S₁ S₂ => S₁.vp φ + S₂.vp φ
  -- | heyvl {assert(@ψ)} => ψ ⊓ φ
  | .Assert ψ => ψ ⊓ φ
  -- | heyvl {assume(@ψ)} => ψ ⇨ φ -- HeyLo implication
  | .Assume ψ => ψ ⇨ φ
  -- | heyvl {havoc(@x)} => heylo {⨅ x, @φ}
  | .Havoc ψ => sorry
  -- | heyvl {validate} => ￢￢φ
  | .Validate => ￢￢φ
  -- | heyvl {if (⊔) {@S₁} else {@S₂}} => S₁.vp φ ⊔ S₂.vp φ
  | .IfSup S₁ S₂ => S₁.vp φ + S₂.vp φ
  -- | heyvl {coassert(@ψ)} => ψ ⊔ φ
  | .Coassert ψ => ψ ⊔ φ
  -- | heyvl {coassume(@ψ)} => ψ ↜ φ -- HeyLo coimplication
  | .Coassume ψ => ψ \ φ
  -- | heyvl {cohavoc(@x)} => heylo {⨆ x, @φ}
  | .Cohavoc ψ => sorry
  -- | heyvl {covalidate} => φᶜᶜ
  | .Covalidate => φᶜᶜ

end

section

variable {Γ B 𝒲 ℳ : Type*}
variable {E : Γ → Type*}
variable [Monoid 𝒲] [AddMonoid ℳ] [One ℳ]
variable [DistribMulAction 𝒲 ℳ]
variable [Zero 𝒲] [Compl ℳ]
variable [Min ℳ] [Max ℳ] [HImp ℳ] [HNot ℳ] [SDiff ℳ]
variable [Compl B]
variable [OmegaCompletePartialOrder ℳ]
variable [IsBotZeroClass ℳ]
variable [AddContinuous ℳ]
variable [SMulContinuous 𝒲 ℳ]
variable [Iverson B ℳ] [IversonContinuous B ℳ]
variable [Substitution ℳ (ι := Γ) E]
variable [SubstitutionContinuous ℳ (ι := Γ) E]

theorem wp_le_vp {O : Optimization} {C : WGCL Γ B ℳ E 𝒲} {φ : ℳ} : C.wp φ ≤ (C.encode O).vp φ := by
  induction C generalizing φ with
  | assign x e =>
    simp [WGCL.encode, wp, HeyW.vp]
    sorry
  | seq C₁ C₂ ih₁ ih₂ =>
    simp [WGCL.encode, wp, HeyW.vp, ih₁, ih₂]
    grw [ih₂, ih₁]
  | weigh w => simp [WGCL.encode, wp, HeyW.vp]
  | nonDet C₁ C₂ ih₁ ih₂ =>
    simp [WGCL.encode, wp, HeyW.vp, ih₁, ih₂]
    split
    · simp_all [WGCL.encode, wp, HeyW.vp, ih₁, ih₂]
      gcongr <;> grind
    · simp_all [WGCL.encode, wp, HeyW.vp, ih₁, ih₂]
      gcongr <;> grind
  | ite ψ C₁ C₂ ih₁ ih₂ =>
    simp [WGCL.encode, wp, HeyW.vp, ih₁, ih₂, HeyW.If, Iverson.iver, ContinuousHom.ofFun₂]
    grw [ih₁, ih₂]
    intro σ
    simp [Iverson.iver, ContinuousHom.ofFun₂]
    set b₁ := (encode O C₁).vp
    set b₂ := (encode O C₂).vp
    gcongr
    ·
      sorry
    · sorry
  | loop ψ I C ih =>
    simp_all [WGCL.encode, wp, HeyW.vp, ih, HeyW.Skip, HeyW.If, ContinuousHom.ofFun₂]
    apply lfp_le
    simp
    sorry

-- def vc : WGCL Γ B I E 𝒲 → HeyW E D 𝒲 ℳ → HeyW E D 𝒲 ℳ
--   | .assign x e => id[x ↦ e]
--   | .seq C₁ C₂ => C₁.vc.comp C₂.vc
--   | .ite φ C₁ C₂ => i[φ] C₁.vc + Iverson.iver φᶜ C₁.vc
--   | .nonDet C₁ C₂ => C₁.vc + C₁.vc
--   | .weigh a => a • (id : I → I)
--   | .loop φ inv C =>
--     sorry

end

def Mem {ι : Type*} (Γ : ι → Type*) := (i : ι) → Γ i

def Γ : String → Type := fun _ ↦ ℕ

def C : WGCL String (Mem Γ → Bool) (Mem Γ → ENNReal) (fun _ ↦ Mem Γ → ℕ) (Mem Γ → ENNReal) :=
  .assign "x" 12

instance : Substitution (Mem Γ) (fun (_ : String) ↦ Mem Γ → ℕ) where
  subst σ x := fun y ↦ if y = x.1 then x.2 σ else σ y

instance : IsBotZeroClass Unit where
  isBot_zero := by simp

instance : AddLeftMono Unit := ⟨fun a b c h ↦ by simp_all⟩
instance : AddLeftContinuous Unit := AddLeftContinuous.of_add_ωSup <| by simp
instance : AddRightContinuous Unit := AddRightContinuous.of_ωSup_add <| by simp
instance : SMulContinuous Unit Unit where
  smul_continuous i := by
    refine ωScottContinuous.of_monotone_map_ωSup ?_
    use Subsingleton.monotone _
    simp
@[simp]
theorem _root_.ENNReal.ωSup_eq_iSup {c : Chain ENNReal} : ωSup c = ⨆ i, c i := rfl
@[simp]
theorem _root_.ENNReal.pi_ωSup_eq_iSup {α : Type*} {c : Chain (α → ENNReal)} : ωSup c = ⨆ i, c i := by
  ext x
  show ωSup (c.map ⟨(· x), _⟩) = _
  simp

instance {α β : Type*} [SMul β β] [Preorder β] [SMulMono β β] :
    SMulMono (α → β) (α → β) := ⟨fun a b c h i ↦ by simp; gcongr; apply h⟩
instance {α β : Type*} [SMul β β] [OmegaCompletePartialOrder β] [SMulContinuous β β] :
    SMulContinuous (α → β) (α → β) := SMulContinuous.of_smul_continuous <| by
  intro f c; ext; simp; show _ • ωSup _ = _; simp [smul_ωSup]; rfl

instance : AddLeftContinuous ENNReal := AddLeftContinuous.of_add_ωSup <| by simp [ENNReal.add_iSup]
instance : AddRightContinuous ENNReal := AddRightContinuous.of_ωSup_add <| by simp [ENNReal.iSup_add]
instance : SMulMono ENNReal ENNReal := ⟨fun a b c h ↦ by simp; gcongr⟩
instance : SMulContinuous ENNReal ENNReal := SMulContinuous.of_smul_continuous <| by simp [ENNReal.mul_iSup]
instance : IversonMono Bool ENNReal where
  iver_mono i a b h := by simp [Iverson.iver]; grind
instance : IversonContinuous Bool ENNReal where
  iver_continuous i := by
    refine ωScottContinuous.of_monotone_map_ωSup ?_
    use IversonMono.iver_mono i
    simp [Iverson.iver]
    split_ifs <;> simp
instance : SubstitutionMono (Mem Γ → ENNReal) fun x ↦ Mem Γ → ℕ where
  subst_mono := by
    intro ⟨_, _⟩ a b h σ
    simp_all
    sorry
instance : SubstitutionContinuous (Mem Γ → ENNReal) fun x ↦ Mem Γ → ℕ where
  subst_continuous i := by
    refine ωScottContinuous.of_monotone_map_ωSup ?_
    use by apply SubstitutionMono.subst_mono
    simp
    intro c
    ext σ
    simp
    sorry

example : wp C (ℳ := Mem Γ → ENNReal) (fun σ ↦ OfNat.ofNat (σ "x")) ≤ (12 : ℕ) := by
  simp
  grw [wp_le_vp (O := .Angelic)]
  cbv
  simp

end WGCL

section

class SMulSupContinuous (α β : Type*) [SMul α β] [SupSet β] where
  smul_iSup {ι : Type} (f : ι → β) (c : α) : c • ⨆ i, f i = ⨆ i, c • f i
class SMulInfContinuous (α β : Type*) [SMul α β] [InfSet β] where
  smul_iInf {ι : Type} (f : ι → β) (c : α) : c • ⨅ i, f i = ⨅ i, c • f i
class SMulBicontinuous (α β : Type*) [SMul α β] [SupSet β] [InfSet β] extends
    SMulSupContinuous α β, SMulInfContinuous α β

class MulLeftSupContinuous (α : Type*) [Mul α] [SupSet α] where
  mul_iSup {ι : Type} (f : ι → α) (c : α) : c * ⨆ i, f i = ⨆ i, c * f i
class MulRightSupContinuous (α : Type*) [Mul α] [SupSet α] where
  iSup_mul {ι : Type} (f : ι → α) (c : α) : (⨆ i, f i) * c = ⨆ i, f i * c
class MulSupContinuous (α : Type*) [Mul α] [SupSet α] extends
    MulLeftSupContinuous α, MulRightSupContinuous α
class MulLeftInfContinuous (α : Type*) [Mul α] [InfSet α] where
  mul_iInf {ι : Type} [Nonempty ι] (f : ι → α) (c : α) : c * ⨅ i, f i = ⨅ i, c * f i
class MulRightInfContinuous (α : Type*) [Mul α] [InfSet α] where
  iInf_mul {ι : Type} [Nonempty ι] (f : ι → α) (c : α) : (⨅ i, f i) * c = ⨅ i, f i * c
class MulInfContinuous (α : Type*) [Mul α] [InfSet α] extends
    MulLeftInfContinuous α, MulRightInfContinuous α
class MulBicontinuous (α : Type*) [Mul α] [SupSet α] [InfSet α] extends
    MulSupContinuous α, MulInfContinuous α

class AddLeftSupContinuous (α : Type*) [Add α] [SupSet α] where
  add_iSup {ι : Type} [Nonempty ι] (f : ι → α) (c : α) : c + ⨆ i, f i = ⨆ i, c + f i
class AddRightSupContinuous (α : Type*) [Add α] [SupSet α] where
  iSup_add {ι : Type} [Nonempty ι] (f : ι → α) (c : α) : (⨆ i, f i) + c = ⨆ i, f i + c
class AddSupContinuous (α : Type*) [Add α] [SupSet α] extends
    AddLeftSupContinuous α, AddRightSupContinuous α
class AddLeftInfContinuous (α : Type*) [Add α] [InfSet α] where
  add_iInf {ι : Type} (f : ι → α) (c : α) : c + ⨅ i, f i = ⨅ i, c + f i
class AddRightInfContinuous (α : Type*) [Add α] [InfSet α] where
  iInf_add {ι : Type} (f : ι → α) (c : α) : (⨅ i, f i) + c = ⨅ i, f i + c
class AddInfContinuous (α : Type*) [Add α] [InfSet α] extends
    AddLeftInfContinuous α, AddRightInfContinuous α
class AddBicontinuous (α : Type*) [Add α] [SupSet α] [InfSet α] extends
    AddSupContinuous α, AddInfContinuous α

instance {α : Type*} [Add α] [CompleteLattice α] [AddLeftSupContinuous α] : AddLeftMono α where
  elim a := by
    simp
    intro b c h
    have := AddLeftSupContinuous.add_iSup (fun (x : Fin 2) ↦ if x = 0 then b else c) a
    simp_all only [Fin.isValue, ge_iff_le]
    have {f : Fin 2 → α} : iSup f = f 0 ⊔ f 1 := by
      apply le_antisymm
      · simp
      · simp
        split_ands
        · apply le_iSup_of_le 0; rfl
        · apply le_iSup_of_le 1; rfl
    simp_all
instance {α : Type*} [Add α] [CompleteLattice α] [AddRightSupContinuous α] : AddRightMono α where
  elim a := by
    simp
    intro b c h
    have := AddRightSupContinuous.iSup_add (fun (x : Fin 2) ↦ if x = 0 then b else c) a
    simp_all only [Fin.isValue, ge_iff_le]
    have {f : Fin 2 → α} : iSup f = f 0 ⊔ f 1 := by
      apply le_antisymm
      · simp
      · simp
        split_ands
        · apply le_iSup_of_le 0; rfl
        · apply le_iSup_of_le 1; rfl
    simp_all

open SMulSupContinuous
open SMulInfContinuous

instance : MulSupContinuous ENNReal where
  mul_iSup := by simp [ENNReal.mul_iSup]
  iSup_mul := by simp [ENNReal.iSup_mul]

instance : AddBicontinuous ENNReal where
  add_iInf := by simp [ENNReal.add_iInf]
  iInf_add := by simp [ENNReal.iInf_add]
  add_iSup := by simp_all [ENNReal.add_iSup]
  iSup_add := by simp_all [ENNReal.iSup_add]

theorem smul_tsum {ι : Type} {α β : Type*} [Monoid α] [AddCommMonoid β] [DistribMulAction α β]
    [TopologicalSpace β] [CompleteLattice β] [IsBotZeroClass β] [AddLeftMono β] [SubsetSum β]
    [SMulSupContinuous α β]
    {c : α} {f : ι → β} (hf : f.support.Countable) :
    c • ∑' i, f i = ∑' i, c • f i := by
  rw [SubsetSum.tsum_eq_iSup_sum_of_support hf]
  rw [SubsetSum.tsum_eq_iSup_sum_of_support]
  · simp [smul_iSup]
    congr with S
    rw [Finset.smul_sum (r := c) (s := S) (f := f)]
  apply Set.Countable.mono _ hf
  intro; simp; contrapose; simp +contextual

theorem iSup_add_iSup {ι : Type} {α : Type*} [Nonempty ι] [Add α] [CompleteLattice α] [AddSupContinuous α]
    {f g : ι → α}
    (h : ∀ (i j : ι), ∃ (k : ι), f i + g j ≤ f k + g k) :
    iSup f + iSup g = ⨆ i, f i + g i := by
  show (⨆ i, f i) + ⨆ i, g i = _
  simp [AddLeftSupContinuous.add_iSup, AddRightSupContinuous.iSup_add]
  apply le_antisymm
  · simp
    intro i j
    specialize h j i
    obtain ⟨k, h⟩ := h
    apply le_iSup_of_le k h
  · simp
    intro i
    apply le_iSup₂_of_le i i
    rfl

theorem sum_iSup {ι : Type} {γ α : Type*} [Nonempty ι] [AddCommMonoid α] [CompleteLattice α]
    [AddSupContinuous α]
    {f : γ → ι → α} {S : Finset γ}
    (h : ∀ (i j : ι), ∃ (k : ι), ∀ (a : γ), f a i ≤ f a k ∧ f a j ≤ f a k) :
    ∑ a ∈ S, ⨆ i, f a i = ⨆ i, ∑ a ∈ S, f a i := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert s S hs ih =>
    simp_all
    rw [iSup_add_iSup]
    intro i j
    obtain ⟨k, hk⟩ := h i j
    use k
    gcongr
    · grind
    · grind

theorem sum_iSup_mono {ι : Type} {γ α : Type*} [Nonempty ι] [AddCommMonoid α] [CompleteLattice α]
    [AddSupContinuous α] [SemilatticeSup ι]
    {f : γ → ι → α} {S : Finset γ}
    (h : ∀ i, Monotone (f i)) :
    ∑ a ∈ S, ⨆ i, f a i = ⨆ i, ∑ a ∈ S, f a i := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert s S hs ih =>
    simp_all
    rw [iSup_add_iSup]
    intro i j
    use i ⊔ j
    gcongr
    · apply h; simp
    · apply h; simp

theorem tsum_iSup {ι : Type} {γ α : Type*} [Nonempty ι] [AddCommMonoid α] [TopologicalSpace α]
    [CompleteLattice α]
    [IsBotZeroClass α]
    [AddSupContinuous α]
    [SubsetSum α]
    [Countable γ]
    [CompleteLattice ι]
    {f : γ → ι → α}
    (hf : ∀ i, Monotone (f i)) :
    ∑' a, ⨆ i, f a i = ⨆ i, ∑' a, f a i := by
  simp [SubsetSum.tsum_eq_iSup_sum]
  rw [iSup_comm]
  apply le_antisymm
  · gcongr with S
    classical
    induction S using Finset.induction with
    | empty => simp
    | insert s S hsS ih =>
      simp_all
      grw [ih]
      simp [AddLeftSupContinuous.add_iSup, AddRightSupContinuous.iSup_add]
      intro j i
      apply le_iSup_of_le (i ⊔ j)
      gcongr
      · apply hf; simp
      · apply hf; simp
  · simp
    intro S i
    apply le_iSup_of_le S
    gcongr
    apply le_iSup_of_le i
    rfl

theorem sum_iInf_le {ι : Type} {γ α : Type*} [Nonempty ι] [AddCommMonoid α] [CompleteLattice α]
    [AddLeftMono α] [AddInfContinuous α] {f : γ → ι → α} {S : Finset γ} :
    ∑ a ∈ S, ⨅ i, f a i ≤ ⨅ i, ∑ a ∈ S, f a i := by
  simp
  intro i
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert s S hsS ih =>
    simp_all
    grw [ih]
    rw [AddRightInfContinuous.iInf_add]
    apply iInf_le_of_le i
    rfl

theorem sum_iSup_le {ι : Type} {γ α : Type*} [Nonempty ι] [AddCommMonoid α] [CompleteLattice α]
    [AddLeftMono α] [AddBicontinuous α] {f : γ → ι → α} {S : Finset γ}
    (h : ∀ (i j : ι), ∃ (k : ι), ∀ (a : γ), f a i ≤ f a k ∧ f a j ≤ f a k) :
    ∑ a ∈ S, ⨆ i, f a i ≤ ⨆ i, ∑ a ∈ S, f a i := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert s S hsS ih =>
    simp_all
    grw [ih]
    simp [AddLeftSupContinuous.add_iSup, AddRightSupContinuous.iSup_add]
    intro j i
    obtain ⟨k, hk⟩ := h i j
    apply le_iSup_of_le k
    gcongr
    · grind
    · grind

end

-- section

-- variable {α : Type*} [CompleteLattice α] [Semiring α]

-- -- local instance : TopologicalSpace α := Preorder.topology α
-- local instance : TopologicalSpace α := Topology.scott α Set.univ
-- local instance : Topology.IsScott α Set.univ := ⟨rfl⟩
-- -- local instance : OrderTopology α := ⟨rfl⟩

-- instance : T0Space α := inferInstance
-- instance : R1Space α := by
--   refine r1Space_iff_inseparable_or_disjoint_nhds.mpr ?_
--   simp
--   intro x y
--   if h : x = y then simp_all else
--   simp_all
--   refine Filter.disjoint_iff.mpr ?_
--   use Set.Ici x
--   constructor
--   · refine IsOpen.mem_nhds ?_ ?_
--     · sorry
--     · simp
--   · use Set.Ici y
--     constructor
--     · sorry
--     · intro S h₁ h₂ a ha
--       simp_all
--       specialize h₁ ha
--       specialize h₂ ha
--       simp_all
--       contrapose h
--       simp_all


--   classical
--   refine Decidable.imp_iff_right_iff.mp ?_
--   simp
--   rintro ⟨_⟩
-- instance : T2Space α := inferInstance

-- #synth LinearOrder ENNReal
-- #synth SupConvergenceClass ENNReal

-- instance : SupConvergenceClass α where
--   tendsto_coe_atTop_isLUB := by
--     simp [tendsto_nhds]
--     intro a S h T h₁ h₂
--     simp_all [IsLUB, IsLeast, upperBounds, lowerBounds]
--     if S = ∅ then
--       subst_eqs
--       simp_all
--       specialize @h ⊥
--       simp_all
--       subst_eqs
--       have : T = Set.univ := by
--         ext x
--         simp_all [Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (D := Set.univ)]
--         simp_all [IsUpperSet]
--         obtain ⟨h₁, h₃⟩ := h₁
--         exact h₁ (by simp) h₂
--       subst_eqs
--       simp
--     else
--       have : Nonempty S := Set.nonempty_iff_ne_empty'.mpr ‹_›
--       letI : IsDirectedOrder { x // x ∈ S } := by
--         refine DirectedOn.isDirectedOrder ?_
--         intro x hx y hy
--         simp
--         use a
--         split_ands
--         · grind
--         · grind
--         · grind
--       refine Filter.mem_atTop_sets.mpr ?_
--       simp_all
--       obtain ⟨b, hb⟩ := this

--       sorry

-- variable [CanonicallyOrderedAdd α]

-- theorem hasSum' {f : ι → α} : HasSum f (⨆ s : Finset ι, ∑ a ∈ s, f a) :=
--   tendsto_atTop_iSup fun _ _ => Finset.sum_le_sum_of_subset

-- theorem asdasd {f : ι → α} : ∑' i, f i = ⨆ S, ∑ s ∈ S, f s := by
--   apply HasSum.tsum_eq

-- end
