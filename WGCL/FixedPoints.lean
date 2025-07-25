import Mathlib.Order.OmegaCompletePartialOrder
import WGCL.OmegaCompletePartialOrderBi

namespace OmegaCompletePartialOrder

section lfp

variable [instOrder : OmegaCompletePartialOrder α]
variable [OrderBot α]
variable (f : α →o α)

attribute [-simp] Function.iterate_succ
attribute [simp] Function.iterate_succ'

abbrev iterate_bot (f : α →o α) : ℕ →o α :=
  ⟨(f^[·] ⊥), fun _ _ h ↦ Monotone.monotone_iterate_of_le_map f.mono (OrderBot.bot_le _) h⟩

def lfp : (α →o α) →o α :=
  ⟨fun f ↦ ωSup (iterate_bot f),
  by
    intro X₁ X₂ h
    apply ωSup_le_iff.mpr fun i ↦ le_ωSup_of_le i ?_
    suffices X₁^[i] ≤ X₂^[i] by apply this
    apply Monotone.iterate_le_of_le X₁.mono h⟩

theorem lfp_le (h : f a ≤ a) : lfp f ≤ a := by
  apply ωSup_le_iff.mpr fun i ↦ ?_
  simp only [DFunLike.coe]; simp only [OrderHom.toFun_eq_coe]
  induction i generalizing a with
  | zero => simp
  | succ i ih =>
    simp only [OrderHomClass.coe_coe, Function.iterate_succ', Function.comp_apply]
    apply le_trans _ h
    gcongr
    apply ih h

theorem lfp_le_fixed (h : f a = a) : lfp f ≤ a := by
  apply ωSup_le_iff.mpr fun i ↦ ?_
  simp only [DFunLike.coe]; simp only [OrderHom.toFun_eq_coe]
  induction i generalizing a with
  | zero => simp
  | succ i ih =>
    simp only [OrderHomClass.coe_coe, Function.iterate_succ', Function.comp_apply]
    rw [← h]
    gcongr
    apply ih h

theorem lfp_le_map : lfp f ≤ f (lfp f) := by
  nth_rw 1 [lfp]
  apply ωSup_le_iff.mpr fun i ↦ ?_
  simp only [DFunLike.coe]; simp only [OrderHom.toFun_eq_coe, OrderHomClass.coe_coe,
    ContinuousHom.coe_toOrderHom]
  rcases i with _ | i
  · simp
  · simp only [Function.iterate_succ', Function.comp_apply]
    gcongr; apply le_ωSup_of_le i (by rfl)

theorem le_lfp (hf : ωScottContinuous f) (h : ∀ (b: α), f b ≤ b → a ≤ b) : a ≤ lfp f := by
  apply h; clear h
  simp [lfp, ωScottContinuous.map_ωSup hf]
  intro i
  apply le_ωSup_of_le (i + 1)
  simp only [DFunLike.coe]
  simp only [OrderHom.toFun_eq_coe, OrderHomClass.coe_coe, ContinuousHom.coe_toOrderHom,
    Function.iterate_succ', Function.comp_apply, le_refl]

theorem map_le_lfp (hf : ωScottContinuous f) (h : a ≤ lfp f) : f a ≤ lfp f :=
  le_lfp _ hf fun _ h' ↦ le_trans (f.mono <| le_trans h (lfp_le f h')) h'

theorem map_lfp (hf : ωScottContinuous f) : f (lfp f) = lfp f :=
  (map_le_lfp f hf (le_refl _)).antisymm (lfp_le_map f)

theorem isFixedPt_lfp (hf : ωScottContinuous f) : Function.IsFixedPt f (lfp f) := map_lfp f hf

theorem isLeast_lfp_le (hf : ωScottContinuous f) : IsLeast {a | f a ≤ a} (lfp f) :=
  ⟨map_le_lfp f hf (by rfl), mem_lowerBounds.mpr fun _ ↦ lfp_le f⟩

theorem isLeast_lfp (hf : ωScottContinuous f) : IsLeast (Function.fixedPoints f) (lfp f) :=
  ⟨isFixedPt_lfp f hf, mem_lowerBounds.mpr fun _ ↦ lfp_le_fixed f⟩

theorem lfp.ωScottContinuous : ωScottContinuous (lfp (α:=α)) := by
  sorry
  -- refine ωScottContinuous.of_map_ωSup_of_orderHom ?_
  -- rw [lfp]
  -- simp [iterate_bot]


end lfp

-- structure OrderDualHom (α : Type) (β : Type) [Preorder α] [Preorder β] where
--   toFun : α → β
--   antitone' : Antitone toFun

-- instance [Preorder α] [Preorder β] : DFunLike (OrderDualHom α β) α (fun _ ↦ β) where
--   coe := OrderDualHom.toFun
--   coe_injective' := fun ⟨f₁, _⟩ ⟨f₂, _⟩ ↦ by simp_all

-- instance [Preorder α] [Preorder β] : Preorder (OrderDualHom α β) := Preorder.lift OrderDualHom.toFun

-- def OrderDualHom.anti [Preorder α] [Preorder β]  (f : OrderDualHom α β) : Antitone f := f.antitone'

-- def Cochain (α : Type) [Preorder α] := OrderDualHom ℕ α

-- instance [Preorder α] : DFunLike (Cochain α) ℕ (fun _ ↦ α) where
--   coe := OrderDualHom.toFun
--   coe_injective' := fun ⟨f₁, _⟩ ⟨f₂, _⟩ ↦ by simp_all

-- class OmegaCompletePartialCoOrder (α : Type) extends OmegaCompletePartialOrder α where
--   ωInf : Cochain α → α
--   le_ωInf : ∀ (c : Cochain α) (x), (∀ i, x ≤ c i) → x ≤ ωInf c
--   ωInf_le : ∀ c : Cochain α, ∀ i, ωInf c ≤ c i

-- def Cochain.map [Preorder α] [Preorder β] (c : Cochain α) (f : α →o β) : Cochain β :=
--   ⟨f ∘ c, Monotone.comp_antitone f.mono c.anti⟩

-- instance OmegaCompletePartialCoOrder.instOmegaCompletePartialCoOrderForall
--   {α : Type} {β : α → Type} [(a : α) → OmegaCompletePartialCoOrder (β a)] :
--     OmegaCompletePartialCoOrder ((a : α) → β a) where
--   ωInf c a := ωInf (c.map (Pi.evalOrderHom a))
--   le_ωInf _ _ hf a := OmegaCompletePartialCoOrder.le_ωInf _ _ (hf · a)
--   ωInf_le _ _ _ := OmegaCompletePartialCoOrder.ωInf_le _ _

-- section ωInf

-- variable [instOrder : OmegaCompletePartialCoOrder α]
-- variable (f : α →o α)

-- attribute [-simp] Function.iterate_succ
-- attribute [simp] Function.iterate_succ'


section gfp

-- OmegaCompletePartialOrder α   extends Preorder
--                                          ≠
-- OmegaCompletePartialOrder αᵒᵈ extends Preorderᵒᵈ


-- variable (hPD : instD.le = fun a b ↦ instP.le b a)

-- @[simp] theorem no_le_od_DP (hPD : instD.le = fun a b ↦ instP.le b a) (a : α) (b : αᵒᵈ) :
--     instD.le b a ↔ instP.le a b := by simp_all
-- @[simp] theorem od_le_no_DP (hPD : instD.le = fun a b ↦ instP.le b a) (a : αᵒᵈ) (b : α) :
--     instD.le b a ↔ instP.le a b := by simp_all

-- def ωInf' (c : @Chain αᵒᵈ instD.toPreorder) : α :=
--   let a : αᵒᵈ := ωSup c
--   a

-- theorem le_ωInf' {hPD : instD.le = fun a b ↦ instP.le b a}
--     (c : @Chain αᵒᵈ instD.toPreorder) (x : α) (h : ∀ i, instP.le x (c i)) :
--     instP.le x (@ωInf' α instD c) := by
--   simp_all [ωInf']
--   have := @ωSup_le αᵒᵈ instD c x (fun i ↦ by simp_all only)
--   set y := ωSup c
--   simp_all

-- theorem ωInf'_le {hPD : instD.le = fun a b ↦ instP.le b a}
--     (c : @Chain αᵒᵈ instD.toPreorder) (i) : instP.le (ωInf' c) (c i) := by
--   simp_all [ωInf']
--   have := @le_ωSup αᵒᵈ instD c i
--   set y := ωSup c
--   simp_all

variable [OmegaCompletePartialOrder α]
variable [OrderTop α]
variable (f : α →o α)

abbrev iterate_top (f : α →o α) : OrderDualHom ℕ α :=
  ⟨(f^[·] ⊤), fun i j h ↦ by
    simp
    obtain ⟨j, _, _⟩ := Nat.exists_eq_add_of_le h
    induction j with
    | zero => simp
    | succ j ih =>
      have : i + (j + 1) = i + j + 1 := by omega
      rw [this]
      rw [Function.iterate_succ']
      simp_all
      have := f.mono ih
      apply le_trans (f.mono ih)
      clear! j
      induction i with
      | zero => simp
      | succ i ih =>
        simp [-Function.iterate_succ, Function.iterate_succ']
        gcongr⟩

theorem iterate_top.mono : Monotone (iterate_top (α:=α)) := by
  intro f₁ f₂ h i
  apply Monotone.iterate_le_of_le f₁.mono h i

open OmegaCompletePartialOrderBi

variable [OmegaCompletePartialOrder αᵒᵈ] [OmegaCompletePartialOrderBi α]

def gfp : (α →o α) →o α :=
  ⟨fun f ↦ ωInf (iterate_top f),
    fun f _ h ↦ le_ωInf _ _ fun i ↦ le_trans (ωInf_le (iterate_top f) i) (iterate_top.mono h i)⟩

theorem le_gfp (h : a ≤ f a) : a ≤ gfp f := by
  apply le_trans h
  simp [gfp]
  apply le_ωInf _ _ fun i ↦ ?_
  simp only [iterate_top, DFunLike.coe]
  simp
  induction i with
  | zero => simp
  | succ i ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    apply f.mono <| le_trans h ih

@[simp] theorem iterate_top_apply : iterate_top f i = f^[i] ⊤ := by rfl

-- le_gfp le_gfp_fixed map_le_gfp

-- theorem map_le_gfp (ha : a ≤ gfp f) : f a ≤ gfp f := by
--   apply le_gfp
--   gcongr

theorem gfp_le (h : ∀ b ≤ f b, b ≤ a) : gfp f ≤ a := by
  -- TODO: this is probably where i will need co-continuity
  sorry
  -- simp [gfp]
  -- have := ωInf_le (iterate_top f) 1
  -- nth_rw 2 [iterate_top] at this
  -- simp only [DFunLike.coe] at this
  -- simp at this
  -- apply le_trans this
  -- apply h (f ⊤) ?_
  -- gcongr
  -- simp

  -- intro i
  -- induction i with
  -- | zero =>
  --   rw [iterate_top_apply]; simp

theorem isFixedPt_gfp : Function.IsFixedPt f (gfp f) := sorry

theorem map_gfp : f (gfp f) = gfp f := isFixedPt_gfp f


theorem gfp_le_map (ha : gfp f ≤ a) : gfp f ≤ f a := sorry

theorem isGreatest_gfp_le : IsGreatest {a | a ≤ f a} (gfp f) := sorry

theorem isGreatest_gfp : IsGreatest (Function.fixedPoints f) (gfp f) := sorry

end gfp

end OmegaCompletePartialOrder
