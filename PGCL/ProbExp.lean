import PGCL.Exp

namespace pGCL

def ProbExp (ϖ : Γ[𝒱]) := {e : 𝔼[ϖ, ENNReal] // e ≤ 1}

namespace ProbExp

instance instFunLike : FunLike (ProbExp ϖ) (States ϖ) ENNReal where
  coe := Subtype.val
  coe_injective' := Subtype.val_injective

@[ext]
theorem ext {p q : ProbExp ϖ} (h : ∀ σ, p σ = q σ) : p = q := by
  cases p; cases q; congr; apply funext h

@[grind =, simp] theorem coe_apply {f : 𝔼[ϖ, ENNReal]} {h : f ≤ 1} :
    instFunLike.coe ⟨f, h⟩ σ = f σ := rfl
@[grind ., simp] theorem mk_val {f : 𝔼[ϖ, ENNReal]} {h : f ≤ 1} :
    (⟨f, h⟩ : ProbExp ϖ).val = f := rfl
@[grind =, simp] theorem mk_vcoe {f : 𝔼[ϖ, ENNReal]} {h : f ≤ 1} :
    @DFunLike.coe _ _ _ instFunLike (Subtype.mk f h : ProbExp ϖ) = f := by rfl

def ofExp (x : 𝔼[ϖ, ENNReal]) : ProbExp ϖ := ⟨x ⊓ 1, by simp⟩
@[grind =, simp] theorem ofExp_apply (x : 𝔼[ϖ, ENNReal]) : ofExp x σ = x σ ⊓ 1 := by simp [ofExp]
@[simp] def ofExp_coe (x : ProbExp ϖ) : ofExp x = x := by ext; simp [ofExp]; apply x.prop

end ProbExp

namespace ProbExp

variable {𝒱 : Type*} {ϖ : Γ[𝒱]}

variable (p : ProbExp ϖ) (σ : States ϖ)

instance instLE : LE (ProbExp ϖ) where
  le a b := ∀ x, a x ≤ b x

@[grind =, simp] theorem coe_le {f g : 𝔼[ϖ, ENNReal]} {hf : f ≤ 1} {hg : g ≤ 1} :
    instLE.le (⟨f, hf⟩) ⟨g, hg⟩ ↔ f ≤ g := by rfl

instance : PartialOrder (ProbExp ϖ) where
  le_refl a σ := by rfl
  le_trans a b c hab hbc σ := by exact (hab σ).trans (hbc σ)
  le_antisymm a b hab hba := by ext σ; exact (hab σ).antisymm (hba σ)

@[grind =, simp] theorem add_one_apply : p σ + (1 - p σ) = 1 := add_tsub_cancel_of_le (p.prop σ)

instance instOfNat0 : OfNat (ProbExp ϖ) 0 := ⟨⟨fun _ ↦ 0, by intro; simp⟩⟩
instance instOfNat1 : OfNat (ProbExp ϖ) 1 := ⟨⟨fun _ ↦ 1, by intro; simp⟩⟩

@[grind =, simp] theorem zero_apply : (ofNat(0) : ProbExp ϖ) σ = 0 := rfl
@[grind =, simp] theorem one_apply : (ofNat(1) : ProbExp ϖ) σ = 1 := rfl

@[grind ., simp] theorem le_one : p ≤ 1 := p.prop
@[grind ., simp] theorem zero_le : 0 ≤ p := by intro; simp
@[grind ., simp] theorem le_one_apply : p σ ≤ 1 := p.prop σ
@[grind ., simp] theorem val_le_one : p.val ≤ 1 := p.prop
@[grind ., simp] theorem zero_le_apply : 0 ≤ p σ := by simp
@[grind ., simp] theorem zero_val_le : 0 ≤ p.val := by apply zero_le
@[grind =, simp] theorem lt_one_iff : ¬p σ = 1 ↔ p σ < 1 := by simp
@[grind ., simp] theorem sub_one_le_one : 1 - p σ ≤ 1 := by simp
@[grind ., simp] theorem ne_top : p σ ≠ ⊤ := by intro h; have := p.le_one σ; simp_all
@[grind ., simp] theorem top_ne : ⊤ ≠ p σ := by intro h; symm at h; simp_all
@[grind =, simp] theorem not_zero_off : ¬p σ = 0 ↔ 0 < p σ := pos_iff_ne_zero.symm

@[grind =, simp]
theorem lt_one_iff' : 1 - p σ < 1 ↔ ¬p σ = 0 :=
  ⟨fun _ _ ↦ by simp_all,
    fun _ ↦ ENNReal.sub_lt_of_sub_lt (p.le_one σ) (.inl (by simp)) (by simp_all)⟩

@[grind ., simp]
theorem top_ne_one_sub : ¬⊤ = 1 - p σ :=
  by intro h; have := h.trans_le <| p.sub_one_le_one σ; simp at this

@[grind =, simp] theorem one_le_iff : 1 ≤ p σ ↔ p σ = 1 := LE.le.ge_iff_eq (p.le_one σ)

@[grind ., simp] theorem ite_eq_zero : (if 0 < p σ then p σ * x else 0) = p σ * x :=
  by split_ifs <;> simp_all
@[grind ., simp] theorem ite_eq_one : (if p σ < 1 then (1 - p σ) * x else 0) = (1 - p σ) * x :=
  by split_ifs <;> simp_all

@[grind ., simp] theorem ite_eq_zero' : (if 0 < p σ then p σ else 0) = p σ :=
  by split_ifs <;> simp_all
@[grind ., simp] theorem ite_eq_one' : (if p σ < 1 then (1 - p σ) else 0) = 1 - p σ :=
  by split_ifs <;> simp_all

instance [DecidableEq 𝒱] : Substitution (ProbExp ϖ) (𝔼[ϖ, ϖ ·]) where
  subst b := fun x ↦ ⟨fun σ ↦ b (σ[x.1 ↦ x.2 σ]), fun σ ↦ by simp⟩

@[grind =, simp] theorem subst_apply [DecidableEq 𝒱] {a : ProbExp ϖ} {x : 𝒱} {A : 𝔼[ϖ, ϖ x]} :
    a[x ↦ A] σ = a σ[x ↦ A σ] := rfl

@[coe] def exp_coe : ProbExp ϖ → 𝔼[ϖ, ENNReal] := Subtype.val
instance : Coe (ProbExp ϖ) (𝔼[ϖ, ENNReal]) := ⟨exp_coe⟩

@[grind =, simp] theorem exp_coe_apply : exp_coe p σ = p σ := by rfl

@[grind =, simp] theorem coe_exp_coe : ↑(exp_coe ⟨x, hx⟩) = x := by rfl

noncomputable instance : HMul (ProbExp ϖ) (𝔼[ϖ, ENNReal]) (𝔼[ϖ, ENNReal]) where
  hMul p x := p.val * x
noncomputable instance : HMul (𝔼[ϖ, ENNReal]) (ProbExp ϖ) (𝔼[ϖ, ENNReal]) where
  hMul x p := x * p.val
@[grind =, simp] theorem hMul_Exp_apply {p : ProbExp ϖ} {x : 𝔼[ϖ, ENNReal]} :
    (p * x) σ = p σ * x σ := rfl
@[grind =, simp] theorem Exp_hMul_apply {p : ProbExp ϖ} {x : 𝔼[ϖ, ENNReal]} :
    (x * p) σ = x σ * p σ := rfl

section

noncomputable instance : Mul (ProbExp ϖ) where
  mul a b := ⟨fun σ ↦ a σ * b σ, by intro σ; simp; refine Left.mul_le_one ?_ ?_ <;> simp⟩

noncomputable instance : Add (ProbExp ϖ) where
  add a b := ⟨fun σ ↦ (a σ + b σ) ⊓ 1, by intro σ; simp⟩

noncomputable instance : Sub (ProbExp ϖ) where
  sub a b := ⟨fun σ ↦ a σ - b σ, by intro σ; simp; exact le_add_right (by simp)⟩

variable {a b : ProbExp ϖ}

@[grind =, simp] theorem add_apply : (a + b) σ = (a σ + b σ) ⊓ 1 := by rfl
@[grind =, simp] theorem mul_apply : (a * b) σ = a σ * b σ := by rfl
@[grind =, simp] theorem sub_apply : (a - b) σ = a σ - b σ := by rfl

variable [DecidableEq 𝒱] {x : 𝒱} {A : 𝔼[ϖ, ϖ x]}

@[grind =, simp] theorem add_subst : (a + b)[x ↦ A] = a[x ↦ A] + b[x ↦ A] := by rfl
@[grind =, simp] theorem mul_subst : (a * b)[x ↦ A] = a[x ↦ A] * b[x ↦ A] := by rfl
@[grind =, simp] theorem sub_subst : (a - b)[x ↦ A] = a[x ↦ A] - b[x ↦ A] := by rfl

@[grind =, simp] theorem zero_subst : (0 : ProbExp ϖ)[x ↦ A] = 0 := by rfl
@[grind =, simp] theorem one_subst : (1 : ProbExp ϖ)[x ↦ A] = 1 := by rfl

end

noncomputable def pick' (x y : 𝔼[ϖ, ENNReal] →o 𝔼[ϖ, ENNReal]) : 𝔼[ϖ, ENNReal] →o 𝔼[ϖ, ENNReal] :=
  ⟨fun X ↦ p * x X + (1 - p) * y X, by intro a b hab; simp_all; gcongr⟩

@[grind =, simp] theorem pick'_apply : p.pick' x y X = p * x X + (1 - p) * y X := rfl
@[grind =, simp] theorem pick'_apply2 : p.pick' x y X σ = p σ * x X σ + (1 - p σ) * y X σ := rfl

-- @[grind =, simp]
-- theorem pick_true {x y : 𝔼[ϖ, ENNReal]} (h : b σ) : p[b].pick x y σ = x σ := by
--   simp [h, pick, BExpr.probOf]
-- @[grind =, simp]
-- theorem pick_false {x y : 𝔼[ϖ, ENNReal]} (h : ¬b σ) : p[b].pick x y σ = y σ := by
--   simp [h, pick, BExpr.probOf]

-- @[simp, gcongr]
-- theorem pick_le (h₁ : x ≤ z) (h₂ : y ≤ w) : p.pick x y ≤ p.pick z w := by
--   intro; simp [pick]; gcongr <;> apply_assumption
-- @[grind ., simp]
-- theorem pick_le' (h₁ : x ≤ z) (h₂ : y ≤ w) : p.pick x y σ ≤ p.pick z w σ := p.pick_le h₁ h₂ σ

-- @[grind =, simp]
-- theorem pickProb_coe : exp_coe (p.pickProb x y) = p.pick x y := by
--   ext σ; simp [pickProb, pick]
--   have := p.pick_le x.prop y.prop σ
--   simp [pick] at this
--   exact this

-- @[grind =, simp]
-- theorem pickProb_DFunLike_coe : DFunLike.coe (p.pickProb x y) = p.pick x y := by
--   rw [← pickProb_coe]; rfl

-- @[grind =, simp]
-- theorem pickProb_apply : (p.pickProb x y) σ = p.pick x y σ := by
--   simp [pickProb, pick]
--   have := p.pick_le x.prop y.prop σ
--   simp [pick] at this
--   exact this

-- @[grind =, simp] theorem pick_same : p.pick x x = x := by ext σ; simp [pick, ← add_mul]


open OmegaCompletePartialOrder in
def _root_.OmegaCompletePartialOrder.ωScottContinuous.apply_iSup
    {α ι : Type*} [CompleteLattice α] [CompleteLattice ι] {f : ι →o α}
    (hf : OmegaCompletePartialOrder.ωScottContinuous f) (c : Chain ι) :
    f (⨆ i, c i) = ⨆ i, f (c i) := hf.map_ωSup_of_orderHom (c:=c)


-- open OmegaCompletePartialOrder in
-- theorem pick_ωScottContinuous {ι : Type*} [CompleteLattice ι] {f g : ι →o 𝔼[ϖ, ENNReal]}
--     (hf : ωScottContinuous f) (hg : ωScottContinuous g) :
--     ωScottContinuous (fun X ↦ p.pick (f X) (g X)) := by
--   simp [pick]
--   refine ωScottContinuous.of_apply₂ fun σ ↦ ?_
--   simp
--   refine ωScottContinuous.of_monotone_map_ωSup ?_
--   simp [ωSup]
--   constructor
--   · intro _ _ _; simp; gcongr
--     · apply f.mono ‹_›
--     · apply g.mono ‹_›
--   · simp [hf.apply_iSup, hg.apply_iSup, ENNReal.mul_iSup, ENNReal.add_iSup, ENNReal.iSup_add]
--     intro c
--     refine iSup_iSup_eq_iSup (fun i j ↦ p σ * f (c j) σ + (1 - p σ) * g (c i) σ) ?_ ?_
--     · intro _ _ _; simp only; intro _; simp only; gcongr; apply g.mono (c.mono ‹_›)
--     · intro _ _ _ _; simp only; gcongr; apply f.mono (c.mono ‹_›)

/-- The expression `1/n` where is defined to be `1` if `n ≤ 1`. -/
noncomputable def inv (n : 𝔼[ϖ, ENNReal]) : ProbExp ϖ :=
  ⟨fun σ ↦ if h : n σ ≤ 1 then 1 else (n σ)⁻¹, fun _ ↦ by
    simp
    split_ifs with h
    · rfl
    · simp [le_of_not_ge h]⟩

@[grind =, simp] theorem inv_apply : inv n σ = if n σ ≤ 1 then (1 : ENNReal) else (n σ)⁻¹ := by rfl

instance : Bot (ProbExp ϖ) := ⟨0⟩
instance : Top (ProbExp ϖ) := ⟨1⟩

@[simp] theorem bot_eq_0 : (instBot (ϖ:=ϖ)).bot = 0 := by rfl
@[simp] theorem top_eq_1 : (instTop (ϖ:=ϖ)).top = 1 := by rfl

open scoped Classical in
noncomputable instance : CompleteLattice (ProbExp ϖ) where
  sup := fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ ⟨a ⊔ b, by simp; grind⟩
  le_sup_left a b σ := by split; split; simp
  le_sup_right a b σ := by split; split; simp
  sup_le := fun ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ _ _ ↦ by simp_all
  inf := fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ ⟨a ⊓ b, by intro σ; simp; left; exact ha σ⟩
  inf_le_left a b σ := by split; split; simp
  inf_le_right a b σ := by split; split; simp
  le_inf := fun ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ _ _ ↦ by simp_all
  sSup S := ⟨⨆ x ∈ S, x.val, by simp⟩
  le_sSup := by intro S ⟨a, ha⟩ ha'; simp; apply le_iSup₂_of_le ⟨a, ha⟩ ha'; rfl
  sSup_le := by intro S ⟨a, ha⟩ ha'; simp_all; apply ha'
  sInf S := ⟨if S = ∅ then 1 else ⨅ x ∈ S, x.val, by
    split_ifs with h
    · simp
    · apply iInf_le_iff.mpr
      simp
      intro b hb
      replace h : S.Nonempty := by exact Set.nonempty_iff_ne_empty.mpr h
      obtain ⟨⟨q, hq'⟩, hq⟩ := h
      specialize hb ⟨q, hq'⟩ hq
      simp_all
      apply hb.trans hq'⟩
  sInf_le S a ha := by
    have : S ≠ ∅ := ne_of_mem_of_not_mem' ha id
    simp [this]
    obtain ⟨a, ha'⟩ := a
    simp_all
    apply iInf₂_le_of_le ⟨a, ha'⟩ ha; rfl
  le_sInf S a ha := by
    obtain ⟨a, ha'⟩ := a
    split_ifs
    · simp_all
    · simp_all
      apply ha
  le_top := by simp
  bot_le := by simp

@[simp]
theorem sSup_apply (S : Set (ProbExp ϖ)) : sSup S x = ⨆ s ∈ S, s x := by
  rw [sSup]
  simp only [CompleteLattice.toConditionallyCompleteLattice, instCompleteLattice,
    CompleteLattice.toCompleteSemilatticeSup, coe_apply, iSup_apply]
  rfl
@[simp]
theorem sInf_apply (S : Set (ProbExp ϖ)) (hS : S.Nonempty) : sInf S x = ⨅ s ∈ S, s x := by
  rw [sInf]
  simp only [CompleteLattice.toConditionallyCompleteLattice, instCompleteLattice,
    CompleteLattice.toCompleteSemilatticeInf, coe_apply]
  have : ¬S = ∅ := Set.nonempty_iff_ne_empty.mp hS
  simp_all only [↓reduceIte, iInf_apply]
  rfl

@[simp]
theorem iSup_apply (f : ι → ProbExp ϖ) : (⨆ i, f i) x = ⨆ i, f i x := by
  rw [iSup]
  simp only [sSup_apply, Set.mem_range, iSup_exists]
  rw [iSup_comm]
  simp only [iSup_iSup_eq_right]
@[simp]
theorem iInf_apply [Nonempty ι] (f : ι → ProbExp ϖ) : (⨅ i, f i) x = ⨅ i, f i x := by
  rw [iInf, sInf_apply _ (Set.range_nonempty fun i ↦ f i)]
  simp only [Set.mem_range, iInf_exists]
  rw [iInf_comm]
  simp only [iInf_iInf_eq_right]
@[grind =, simp] theorem sup_apply {f g : ProbExp ϖ} : (f ⊔ g) σ = f σ ⊔ g σ := rfl
@[grind =, simp] theorem inf_apply {f g : ProbExp ϖ} : (f ⊓ g) σ = f σ ⊓ g σ := rfl
@[grind =, simp] theorem sup_coe_apply {f g : ProbExp ϖ} : (f ⊔ g).val σ = f σ ⊔ g σ := rfl
@[grind =, simp] theorem inf_coe_apply {f g : ProbExp ϖ} : (f ⊓ g).val σ = f σ ⊓ g σ := rfl
@[grind =, simp] theorem max_apply {f g : ProbExp ϖ} : (max f g) σ = max (f σ) (g σ) := rfl
@[grind =, simp] theorem min_apply {f g : ProbExp ϖ} : (min f g) σ = min (f σ) (g σ) := rfl
@[grind =, simp] theorem max_coe_apply {f g : ProbExp ϖ} : (max f g).val σ = max (f σ) (g σ) := rfl
@[grind =, simp] theorem min_coe_apply {f g : ProbExp ϖ} : (min f g).val σ = min (f σ) (g σ) := rfl

@[grind =, simp] theorem one_mul : (1 : ProbExp ϖ) * p = p := by ext; simp
@[grind =, simp] theorem zero_mul : (0 : ProbExp ϖ) * p = 0 := by ext; simp

@[grind =, simp] theorem mul_one : p * (1 : ProbExp ϖ) = p := by ext; simp
@[grind =, simp] theorem mul_zero : p * (0 : ProbExp ϖ) = 0 := by ext; simp

@[grind =, simp] theorem one_add : 1 + p = 1 := by ext; simp
@[grind =, simp] theorem add_one : p + 1 = 1 := by ext; simp
@[grind =, simp] theorem zero_add : 0 + p = p := by ext; simp
@[grind =, simp] theorem add_zero : p + 0 = p := by ext; simp
@[grind =, simp] theorem sub_one : p - 1 = 0 := by ext σ; exact tsub_eq_zero_of_le (le_one p σ)
@[grind =, simp] theorem zero_sub : 0 - p = 0 := by ext; simp
@[grind =, simp] theorem sub_zero : p - 0 = p := by ext; simp

@[grind =, simp] theorem coe_one : exp_coe (ϖ:=ϖ) 1 = 1 := by rfl
@[grind =, simp] theorem coe_zero : exp_coe (ϖ:=ϖ) 0 = 0 := by rfl

@[gcongr]
theorem mul_le_mul (a b c d : ProbExp ϖ) (hac : a ≤ c) (hbd : b ≤ d) : a * b ≤ c * d := by
  intro; simp; gcongr <;> apply_assumption

@[gcongr]
theorem add_le_add (a b c d : ProbExp ϖ) (hac : a ≤ c) (hbd : b ≤ d) : a + b ≤ c + d := by
  intro; simp only [add_apply]; gcongr <;> apply_assumption

@[gcongr]
theorem sub_le_sub (a b c d : ProbExp ϖ) (hac : a ≤ c) (hdb : d ≤ b) : a - b ≤ c - d := by
  intro; simp only [sub_apply]; gcongr <;> apply_assumption

@[simp]
theorem pick_le {p : ProbExp ϖ} (hl : l ≤ x) (hr : r ≤ x) :
    p σ * l + (1 - p σ) * r ≤ x := by
  grw [hl, hr]
  simp [← right_distrib]

@[grind =, simp] theorem coe_inv {X : 𝔼[ϖ, ENNReal]} :
    exp_coe (inv X) = X⁻¹ ⊓ 1 := by
      ext σ
      simp [inv]
      split_ifs with h
      · simp_all
      · simp_all
        exact h.le

variable [DecidableEq 𝒱]

@[grind =, simp] theorem exp_coe_subst {X : ProbExp ϖ} {x : 𝒱} {e : 𝔼[ϖ, ϖ x]} :
    (exp_coe X)[x ↦ e] = (exp_coe X[x ↦ e]) := by rfl
-- TODO
-- @[grind =, simp] theorem mk_subst {x : 𝒱} {e : 𝔼[ϖ, α]} :
--     (instSubstExpOfDecidableEq.subst ⟨q, hp⟩ x e) = ⟨q[x ↦ e], by
--       intro σ; simp; apply hp⟩ := by rfl
@[grind =, simp] theorem inv_subst {X : 𝔼[ϖ, ENNReal]} {x : 𝒱} {e : 𝔼[ϖ, ϖ x]} :
    (inv X)[x ↦ e] = inv X[x ↦ e] := by rfl

omit [DecidableEq 𝒱] in
@[simp]
theorem one_sub_one_sub_apply {X : ProbExp ϖ} : 1 - (1 - X σ) = X σ := by
  apply ENNReal.sub_sub_cancel <;> simp
omit [DecidableEq 𝒱] in
@[simp]
theorem one_sub_one_sub {X : ProbExp ϖ} : 1 - (1 - X) = X := by ext; simp
omit [DecidableEq 𝒱] in
@[simp]
theorem one_sub_le {X : ProbExp ϖ} : 1 - X.val ≤ 1 := by intro σ; simp

noncomputable instance : HImp (ProbExp ϖ) where
  himp a b := ⟨fun σ ↦ if a σ ≤ b σ then 1 else b σ, by intro; simp; split_ifs <;> simp_all⟩

omit [DecidableEq 𝒱] in
@[grind =, simp]
theorem one_le {p : ProbExp ϖ} : 1 ≤ p ↔ p = 1 := by
  constructor
  · intro h; ext σ; specialize h σ; simp_all
  · grind
omit [DecidableEq 𝒱] in
@[gcongr]
theorem himp_mono {l₁ l₂ r₁ r₂ : ProbExp ϖ} (hl : l₂ ≤ l₁) (hr : r₁ ≤ r₂) :
    l₁ ⇨ r₁ ≤ l₂ ⇨ r₂ := by
  intro σ
  specialize hl σ
  specialize hr σ
  simp [himp]
  split_ifs with h₁ h₂ <;> try grind
omit [DecidableEq 𝒱] in
@[grind =, simp]
theorem himp_apply {l r : ProbExp ϖ} : (l ⇨ r) σ = if l σ ≤ r σ then 1 else r σ := rfl

noncomputable instance : Compl (ProbExp ϖ) where
  compl x := 1 - x

noncomputable instance : DistribLattice (ProbExp ϖ) where
  le_sup_inf x y z := by intro σ; simp; grind

omit [DecidableEq 𝒱] in
@[gcongr]
theorem compl_mono {p r : ProbExp ϖ} (h : r ≤ p) : pᶜ ≤ rᶜ := by simp [compl]; gcongr
omit [DecidableEq 𝒱] in
@[grind =, simp]
theorem compl_compl {p : ProbExp ϖ} : pᶜᶜ = p := by simp [compl]

open OrderHom

omit [DecidableEq 𝒱] in
theorem gfp_eq_one_sub_lfp {f : ProbExp ϖ →o ProbExp ϖ} :
    gfp f = 1 - lfp ⟨fun x ↦ 1 - f (1 - x), fun _ _ _ ↦ by simp; gcongr⟩ := by
  apply le_antisymm
  · suffices 1 - gfp f ≥ 1 - (1 - lfp ⟨fun x ↦ 1 - f (1 - x), _⟩) by
      simp_all; grw [this]; simp
    simp
    apply lfp_le
    simp
  · apply le_gfp
    nth_rw 1 [← map_lfp]
    simp [-map_lfp]

noncomputable instance : Compl (ProbExp ϖ →o ProbExp ϖ) where
  compl f := ⟨fun x ↦ (f xᶜ)ᶜ, fun a b h ↦ by simp; gcongr⟩

omit [DecidableEq 𝒱] in
@[grind =, simp]
theorem orderHom_compl_compl {f : ProbExp ϖ →o ProbExp ϖ} : fᶜᶜ = f := by simp [compl]; rfl

omit [DecidableEq 𝒱] in
theorem gfp_eq_lfp_compl {f : ProbExp ϖ →o ProbExp ϖ} :
    gfp f = (lfp fᶜ)ᶜ := gfp_eq_one_sub_lfp

omit [DecidableEq 𝒱] in
theorem lfp_eq_gfp_compl {f : ProbExp ϖ →o ProbExp ϖ} :
    lfp f = (gfp fᶜ)ᶜ := by simp [ProbExp.gfp_eq_lfp_compl]

end ProbExp

namespace BExpr

noncomputable def probOf (b : BExpr ϖ) : ProbExp ϖ :=
  ⟨i[b], by intro; simp [Iverson.iver]; split <;> simp⟩
notation "p[" b "]" => BExpr.probOf b

@[grind =, simp] theorem probOf_apply (b : BExpr ϖ) : p[b] σ = i[b σ] := by simp [probOf]

end BExpr

end pGCL
