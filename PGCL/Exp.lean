import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Inv
import Mathlib.Order.OmegaCompletePartialOrder
import STDX.Subst

namespace pGCL

variable {ϖ : Type*}
def States (ϖ : Type*) := ϖ → ENNReal

instance : Nonempty (States ϖ) := ⟨fun _ ↦ Inhabited.default⟩

-- def NExp (ϖ : Type*) := States ϖ → ℕ
def Exp (ϖ : Type*) := States ϖ → ENNReal
-- alias NExp := Exp

instance States.instSubst [DecidableEq ϖ] : Subst (States ϖ) ϖ ENNReal where
  subst σ x v := fun α ↦ if x = α then v else σ α

@[ext] theorem States.ext {σ₁ σ₂ : States ϖ} (h : ∀ v, σ₁ v = σ₂ v) : σ₁ = σ₂ := _root_.funext h

@[simp] theorem States.subst_apply [DecidableEq ϖ] {σ : States ϖ} :
    σ[x ↦ v] y = if x = y then v else σ y := rfl

namespace Exp

noncomputable section

@[ext]
theorem ext {a b : Exp ϖ} (h : ∀ σ, a σ = b σ) : a = b := funext h

@[coe] def ennreal_coe : ENNReal → Exp ϖ := fun x _ ↦ x
instance : Coe ENNReal (Exp ϖ) := ⟨ennreal_coe⟩

instance : CommSemiring (Exp ϖ) := inferInstanceAs (CommSemiring (States ϖ → ENNReal))
instance : DivInvOneMonoid (Exp ϖ) := inferInstanceAs (DivInvOneMonoid (States ϖ → ENNReal))
instance : Sub (Exp ϖ) := inferInstanceAs (Sub (States ϖ → ENNReal))
instance : CompleteLattice (Exp ϖ) :=
  inferInstanceAs (CompleteLattice (States ϖ → ENNReal))

@[simp] theorem bot_eq_0 : (⊥ : Exp ϖ) = 0 := by rfl
@[simp] theorem top_apply : (⊤ : Exp ϖ) x = ⊤ := by rfl

@[simp] theorem zero_apply : (@OfNat.ofNat (Exp ϖ) 0 _) x = 0 := rfl
@[simp] theorem one_apply : (@OfNat.ofNat (Exp ϖ) 1 _) x = 1 := rfl
@[simp] theorem ofNat_apply {n : ℕ} : (n : Exp ϖ) x = n := rfl
@[simp] theorem ofNat_apply' [Nat.AtLeastTwo n] :
    @OfNat.ofNat (Exp ϖ) n instOfNatAtLeastTwo x = n := rfl

instance instSubst [DecidableEq ϖ] : Subst (Exp ϖ) ϖ (Exp ϖ) where
  subst X x A := fun σ ↦ X (σ[x ↦ A σ])
instance instSubst_ennreal [DecidableEq ϖ] : Subst (Exp ϖ) ϖ ENNReal where
  subst X x A := X[x ↦ (A : Exp ϖ)]
instance instSubst_nat [DecidableEq ϖ] : Subst (Exp ϖ) ϖ ℕ where
  subst X x A := X[x ↦ (A : Exp ϖ)]

@[simp] theorem subst_ennreal_eq [DecidableEq ϖ] {X : Exp ϖ} {x : ϖ} {A : ENNReal} :
    X[x ↦ A] = X[x ↦ (A : Exp ϖ)] := rfl
@[simp] theorem subst_nat_eq [DecidableEq ϖ] {X : Exp ϖ} {x : ϖ} {A : ℕ} :
    X[x ↦ A] = X[x ↦ (A : Exp ϖ)] := rfl

section

variable {a b : Exp ϖ}

@[simp] theorem add_apply : (a + b) x = a x + b x := rfl
@[simp] theorem sub_apply : (a - b) x = a x - b x := rfl
@[simp] theorem mul_apply : (a * b) x = a x * b x := rfl
@[simp] theorem div_apply : (a / b) x = a x / b x := rfl
@[simp] theorem max_apply : (a ⊔ b) x = a x ⊔ b x := rfl
@[simp] theorem min_apply : (a ⊓ b) x = a x ⊓ b x := rfl
@[simp] theorem iSup_apply (f : ι → Exp ϖ) : (⨆ i, f i) x = ⨆ i, f i x := _root_.iSup_apply
@[simp] theorem iInf_apply (f : ι → Exp ϖ) : (⨅ i, f i) x = ⨅ i, f i x := _root_.iInf_apply

instance : AddLeftMono (Exp ϖ) := ⟨fun a b c h σ ↦ by
  simp only [add_apply]; gcongr; apply h⟩
instance : AddRightMono (Exp ϖ) := ⟨fun a b c h σ ↦ by
  simp only [Function.swap, add_apply]; gcongr; apply h⟩

@[gcongr]
theorem div_le_div {a b c d : Exp ϖ} (hac : a ≤ c) (hdb : d ≤ b) :
    a / b ≤ c / d := by
  intro σ; simp; gcongr <;> apply_assumption

@[simp] theorem inv_apply {X : Exp ϖ} : X⁻¹ σ = (X σ)⁻¹ := by rfl
@[simp] theorem pow_apply {X : Exp ϖ} {n : ℕ} : (X^n) σ = (X σ)^n := by rfl

@[simp] theorem one_sub_one : (1 : Exp ϖ) - 1 = 0 := by ext; simp
@[simp] theorem sub_zero : (x : Exp ϖ) - 0 = x := by ext; simp

variable [DecidableEq ϖ] {v : ϖ} {e : Exp ϖ}

@[simp] theorem add_subst : (a + b)[v ↦ e] = a[v ↦ e] + b[v ↦ e] := rfl
@[simp] theorem sub_subst : (a - b)[v ↦ e] = a[v ↦ e] - b[v ↦ e] := rfl
@[simp] theorem mul_subst : (a * b)[v ↦ e] = a[v ↦ e] * b[v ↦ e] := rfl
@[simp] theorem div_subst : (a / b)[v ↦ e] = a[v ↦ e] / b[v ↦ e] := rfl
@[simp] theorem max_subst : (a ⊔ b)[v ↦ e] = a[v ↦ e] ⊔ b[v ↦ e] := rfl
@[simp] theorem min_subst : (a ⊓ b)[v ↦ e] = a[v ↦ e] ⊓ b[v ↦ e] := rfl

@[simp] theorem ennreal_coe_subst {Y : ENNReal} : (↑Y : Exp ϖ)[v ↦ e] = ↑Y := rfl

@[simp] theorem zero_subst : (@OfNat.ofNat (Exp ϖ) 0 _)[v ↦ e] = 0 := rfl
@[simp] theorem one_subst : (@OfNat.ofNat (Exp ϖ) 1 _)[v ↦ e] = 1 := rfl
@[simp] theorem ofNat_subst {n : ℕ} : (n : Exp ϖ)[v ↦ e] = n := rfl
@[simp] theorem ofNat_subst' [Nat.AtLeastTwo n] :
    (@OfNat.ofNat (Exp ϖ) n instOfNatAtLeastTwo)[v ↦ e] = n := rfl
@[simp] theorem pow_subst {X : Exp ϖ} {x : ϖ} {e : Exp ϖ} : (X^n)[x ↦ e] = X[x ↦ e]^n := by rfl
@[simp] theorem inv_subst {X : Exp ϖ} {x : ϖ} {e : Exp ϖ} : X⁻¹[x ↦ e] = X[x ↦ e]⁻¹ := by rfl

end

@[simp]
theorem subst_apply [DecidableEq ϖ] (e : Exp ϖ) (x : ϖ) (A : Exp ϖ) :
    e[x ↦ A] σ = e (σ[x ↦ A σ]) := rfl
-- @[simp]
-- theorem subst_apply_ennreal [DecidableEq ϖ] (e : Exp ϖ) (x : ϖ) (n : ENNReal) :
--     e[x ↦ n] σ = e (σ[x ↦ n]) := rfl
-- @[simp]
-- theorem subst_apply_nat [DecidableEq ϖ] (e : Exp ϖ) (x : ϖ) (n : ℕ) :
--     e[x ↦ n] σ = e (σ[x ↦ (n : ENNReal)]) := rfl

@[gcongr]
theorem add_le_add (a b c d : Exp ϖ) (hac : a ≤ c) (hbd : b ≤ d) : a + b ≤ c + d := by
  intro; simp; gcongr <;> apply_assumption
@[gcongr]
theorem mul_le_mul (a b c d : Exp ϖ) (hac : a ≤ c) (hbd : b ≤ d) : a * b ≤ c * d := by
  intro; simp; gcongr <;> apply_assumption

end

end Exp

structure BExpr (ϖ : Type*) where
  toFun : States ϖ → Prop
  decidable : DecidablePred toFun
def ProbExp (ϖ : Type*) := {e : Exp ϖ // e ≤ 1}

namespace ProbExp

instance instFunLike : FunLike (ProbExp ϖ) (States ϖ) ENNReal where
  coe := Subtype.val
  coe_injective' := Subtype.val_injective

@[simp] theorem coe_apply {f : Exp ϖ} {h : f ≤ 1} : instFunLike.coe ⟨f, h⟩ σ = f σ := by rfl
@[simp] theorem mk_val {f : Exp ϖ} {h : f ≤ 1} : (⟨f, h⟩ : ProbExp ϖ).val = f := by rfl
@[simp] theorem mk_vcoe {f : Exp ϖ} {h : f ≤ 1} :
    @DFunLike.coe _ _ _ instFunLike (Subtype.mk f h : ProbExp ϖ) = f := by rfl

end ProbExp

namespace BExpr

instance : FunLike (BExpr ϖ) (States ϖ) Prop where
  coe := BExpr.toFun
  coe_injective' := fun ⟨b, _⟩ ⟨b', _⟩ h ↦ by simp at h; subst_eqs; simp; ext; grind
instance {b : BExpr ϖ} : Decidable (b σ) := b.decidable σ

@[ext] theorem ext {a b : BExpr ϖ} (h : ∀ σ, a σ ↔ b σ) : a = b := by
  cases a; cases b;
  simp [DFunLike.coe] at h
  congr
  · ext; apply h
  · refine Function.hfunext rfl ?_; simp; grind

def not (b : BExpr ϖ) : BExpr ϖ :=
  ⟨(¬b ·), fun σ ↦ if h : b σ then .isFalse (by simp_all) else .isTrue (by simp_all)⟩
def iver (b : BExpr ϖ) : Exp ϖ := (if b · then 1 else 0)
notation "i[" b "]" => BExpr.iver b
def probOf (b : BExpr ϖ) : ProbExp ϖ :=
  ⟨i[b], by intro; simp [BExpr.iver]; split <;> simp⟩
notation "p[" b "]" => BExpr.probOf b

@[simp] theorem not_apply : (not b) σ = ¬b σ := by rfl

variable {b : BExpr ϖ}

@[coe] def coe_bool : Bool → BExpr ϖ := fun b ↦ ⟨fun _ ↦ b, fun _ ↦ inferInstance⟩
instance : Coe Bool (BExpr ϖ) := ⟨coe_bool⟩


@[simp] theorem iver_apply_le_one : i[b] σ ≤ 1 := by simp [iver]; split_ifs <;> simp
@[simp] theorem iver_le_one : i[b] ≤ 1 := by intro σ; simp
@[simp] theorem iver_mul_le_apply {X : Exp ϖ} : i[b] σ * X σ ≤ X σ := by calc
  _ ≤ 1 * X σ := by gcongr; simp
  _ = _ := by simp
@[simp] theorem iver_mul_le : i[b] * X ≤ X := by intro; simp
@[simp] theorem mul_iver_le_apply {X : Exp ϖ} : X σ * i[b] σ ≤ X σ := by calc
  _ ≤ X σ * 1 := by gcongr; simp
  _ = _ := by simp
@[simp] theorem mul_iver_le : i[b] * X ≤ X := by intro; simp

@[simp] theorem true_iver (h : b σ = true) : i[b] σ = 1 := by simp [iver, h]
@[simp] theorem false_iver (h : b σ = false) : i[b] σ = 0 := by simp [iver, h]
@[simp] theorem true_not_iver (h : b σ = true) : i[b.not] σ = 0 := by simp [iver, h]
@[simp] theorem false_not_iver (h : b σ = false) : i[b.not] σ = 1 := by simp [iver, h]

@[simp] theorem true_probOf (h : b σ = true) : p[b] σ = 1 := by simp [probOf, h]
@[simp] theorem false_probOf (h : b σ = false) : p[b] σ = 0 := by simp [probOf, h]
@[simp] theorem true_not_probOf (h : b σ = true) : p[b.not] σ = 0 := by simp [probOf, h]
@[simp] theorem false_not_probOf (h : b σ = false) : p[b.not] σ = 1 := by simp [probOf, h]

instance [DecidableEq ϖ] : Subst (BExpr ϖ) ϖ (Exp ϖ) where
  subst b x A := ⟨fun σ ↦ b (σ[x ↦ A σ]), fun σ ↦ by simp only; exact inferInstance⟩

noncomputable def lt (l r : Exp ϖ) : BExpr ϖ := ⟨fun σ ↦ l σ < r σ, by exact inferInstance⟩
noncomputable def le (l r : Exp ϖ) : BExpr ϖ := ⟨fun σ ↦ l σ ≤ r σ, by exact inferInstance⟩
noncomputable def eq (l r : Exp ϖ) : BExpr ϖ := ⟨fun σ ↦ l σ = r σ, by exact inferInstance⟩
def and (l r : BExpr ϖ) : BExpr ϖ := ⟨fun σ ↦ l σ ∧ r σ, by exact inferInstance⟩
def or (l r : BExpr ϖ) : BExpr ϖ := ⟨fun σ ↦ l σ ∨ r σ, by exact inferInstance⟩

@[simp] theorem lt_apply {l r : Exp ϖ} : lt l r σ ↔ l σ < r σ := by rfl
@[simp] theorem le_apply {l r : Exp ϖ} : le l r σ ↔ l σ ≤ r σ := by rfl
@[simp] theorem eq_apply {l r : Exp ϖ} : eq l r σ ↔ l σ = r σ := by rfl
@[simp] theorem and_apply {l r : BExpr ϖ} : and l r σ ↔ l σ ∧ r σ := by rfl
@[simp] theorem or_apply {l r : BExpr ϖ} : or l r σ ↔ l σ ∨ r σ := by rfl

end BExpr

namespace ProbExp

variable (p : ProbExp ϖ) (σ : States ϖ)

@[simp] theorem add_one_apply : p σ + (1 - p σ) = 1 := add_tsub_cancel_of_le (p.prop σ)

@[simp] theorem le_one : p σ ≤ 1 := p.prop σ
@[simp] theorem val_le_one : p.val ≤ 1 := p.prop
@[simp] theorem zero_le : 0 ≤ p σ := by simp
@[simp] theorem zero_val_le : 0 ≤ p.val := by apply zero_le
@[simp] theorem lt_one_iff : ¬p σ = 1 ↔ p σ < 1 := by simp
@[simp] theorem sub_one_le_one : 1 - p σ ≤ 1 := by simp
@[simp] theorem ne_top : p σ ≠ ⊤ := by intro h; have := p.le_one σ; simp_all
@[simp] theorem top_ne : ⊤ ≠ p σ := by intro h; symm at h; simp_all
@[simp] theorem not_zero_off : ¬p σ = 0 ↔ 0 < p σ := pos_iff_ne_zero.symm

@[simp]
theorem lt_one_iff' : 1 - p σ < 1 ↔ ¬p σ = 0 :=
  ⟨fun _ _ ↦ by simp_all,
    fun _ ↦ ENNReal.sub_lt_of_sub_lt (p.le_one σ) (.inl (by simp)) (by simp_all)⟩

@[simp]
theorem top_ne_one_sub : ¬⊤ = 1 - p σ :=
  by intro h; have := h.trans_le <| p.sub_one_le_one σ; simp at this

@[simp] theorem one_le_iff : 1 ≤ p σ ↔ p σ = 1 := LE.le.ge_iff_eq (p.le_one σ)

@[simp] theorem ite_eq_zero : (if 0 < p σ then p σ * x else 0) = p σ * x :=
  by split_ifs <;> simp_all
@[simp] theorem ite_eq_one : (if p σ < 1 then (1 - p σ) * x else 0) = (1 - p σ) * x :=
  by split_ifs <;> simp_all

@[simp] theorem ite_eq_zero' : (if 0 < p σ then p σ else 0) = p σ :=
  by split_ifs <;> simp_all
@[simp] theorem ite_eq_one' : (if p σ < 1 then (1 - p σ) else 0) = 1 - p σ :=
  by split_ifs <;> simp_all

instance [DecidableEq ϖ] : Subst (ProbExp ϖ) ϖ (Exp ϖ) where
  subst b x A := ⟨fun σ ↦ b (σ[x ↦ A σ]), fun σ ↦ by simp⟩

@[simp] theorem subst_apply [DecidableEq ϖ] {a : ProbExp ϖ} {x : ϖ} {A : Exp ϖ} :
    a[x ↦ A] σ = a σ[x ↦ A σ] := rfl

@[coe] def exp_coe : ProbExp ϖ → Exp ϖ := Subtype.val
instance : Coe (ProbExp ϖ) (Exp ϖ) := ⟨exp_coe⟩

@[simp] theorem exp_coe_apply : exp_coe p σ = p σ := by rfl

@[simp] theorem coe_exp_coe : ↑(exp_coe ⟨x, hx⟩) = x := by rfl

noncomputable instance : HMul (ProbExp ϖ) (Exp ϖ) (Exp ϖ) where
  hMul p x := p.val * x
noncomputable instance : HMul (Exp ϖ) (ProbExp ϖ) (Exp ϖ) where
  hMul x p := x * p.val
@[simp] theorem hMul_Exp_apply {p : ProbExp ϖ} {x : Exp ϖ} : (p * x) σ = p σ * x σ := by rfl
@[simp] theorem Exp_hMul_apply {p : ProbExp ϖ} {x : Exp ϖ} : (x * p) σ = x σ * p σ := by rfl

@[ext]
theorem ext {p q : ProbExp ϖ} (h : ∀ σ, p σ = q σ) : p = q := by
  cases p; cases q; congr; apply funext h

instance instOfNat0 : OfNat (ProbExp ϖ) 0 := ⟨⟨fun _ ↦ 0, by intro; simp⟩⟩
instance instOfNat1 : OfNat (ProbExp ϖ) 1 := ⟨⟨fun _ ↦ 1, by intro; simp⟩⟩

@[simp] theorem zero_apply : instOfNat0.ofNat σ = 0 := rfl
@[simp] theorem one_apply : instOfNat1.ofNat σ = 1 := rfl

section

noncomputable instance : Mul (ProbExp ϖ) where
  mul a b := ⟨fun σ ↦ a σ * b σ, by intro σ; simp; refine Left.mul_le_one ?_ ?_ <;> simp⟩

noncomputable instance : Add (ProbExp ϖ) where
  add a b := ⟨fun σ ↦ (a σ + b σ) ⊓ 1, by intro σ; simp⟩

noncomputable instance : Sub (ProbExp ϖ) where
  sub a b := ⟨fun σ ↦ a σ - b σ, by intro σ; simp; exact le_add_right (by simp)⟩

variable {a b : ProbExp ϖ}

@[simp] theorem add_apply : (a + b) σ = (a σ + b σ) ⊓ 1 := by rfl
@[simp] theorem mul_apply : (a * b) σ = a σ * b σ := by rfl
@[simp] theorem sub_apply : (a - b) σ = a σ - b σ := by rfl

variable [DecidableEq ϖ] {x : ϖ} {A : Exp ϖ}

@[simp] theorem add_subst : (a + b)[x ↦ A] = a[x ↦ A] + b[x ↦ A] := by rfl
@[simp] theorem mul_subst : (a * b)[x ↦ A] = a[x ↦ A] * b[x ↦ A] := by rfl
@[simp] theorem sub_subst : (a - b)[x ↦ A] = a[x ↦ A] - b[x ↦ A] := by rfl

@[simp] theorem zero_subst : (0 : ProbExp ϖ)[x ↦ A] = 0 := by rfl
@[simp] theorem one_subst : (1 : ProbExp ϖ)[x ↦ A] = 1 := by rfl

end

noncomputable def pick (x y : Exp ϖ) : Exp ϖ := p * x + (1 - p) * y
noncomputable def pickProb (x y : ProbExp ϖ) : ProbExp ϖ := p * x + (1 - p) * y

@[simp]
theorem pick_true {x y : Exp ϖ} (h : b σ) : p[b].pick x y σ = x σ := by
  simp [h, pick, BExpr.probOf]
@[simp]
theorem pick_false {x y : Exp ϖ} (h : ¬b σ) : p[b].pick x y σ = y σ := by
  simp [h, pick, BExpr.probOf]

@[simp, gcongr]
theorem pick_le (h₁ : x ≤ z) (h₂ : y ≤ w) : p.pick x y ≤ p.pick z w := by
  intro; simp [pick]; gcongr <;> apply_assumption
@[simp]
theorem pick_le' (h₁ : x ≤ z) (h₂ : y ≤ w) : p.pick x y σ ≤ p.pick z w σ := p.pick_le h₁ h₂ σ

@[simp]
theorem pickProb_coe : exp_coe (p.pickProb x y) = p.pick x y := by
  ext σ; simp [pickProb, pick]
  have := p.pick_le x.prop y.prop σ
  simp [pick] at this
  exact this

@[simp]
theorem pickProb_apply : (p.pickProb x y) σ = p.pick x y σ := by
  simp [pickProb, pick]
  have := p.pick_le x.prop y.prop σ
  simp [pick] at this
  exact this

@[simp] theorem pick_same : p.pick x x = x := by ext σ; simp [pick, ← add_mul]

instance instLE : LE (ProbExp ϖ) where
  le a b := ∀ x, a x ≤ b x

@[simp] theorem coe_le {f g : Exp ϖ} {hf : f ≤ 1} {hg : g ≤ 1} :
    instLE.le (⟨f, hf⟩) ⟨g, hg⟩ ↔ f ≤ g := by rfl

instance : PartialOrder (ProbExp ϖ) where
  le_refl a σ := by rfl
  le_trans a b c hab hbc σ := by exact (hab σ).trans (hbc σ)
  le_antisymm a b hab hba := by ext σ; exact (hab σ).antisymm (hba σ)

/-- The expression `1/n` where is defined to be `1` if `n ≤ 1`. -/
noncomputable def inv (n : Exp ϖ) : ProbExp ϖ :=
  ⟨fun σ ↦ if h : n σ ≤ 1 then 1 else (n σ)⁻¹, fun _ ↦ by
    simp
    split_ifs with h
    · rfl
    · simp [le_of_not_ge h]⟩

@[simp] theorem inv_apply : inv n σ = if n σ ≤ 1 then (1 : ENNReal) else (n σ)⁻¹ := by rfl

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
  le_top := by simp; intro; apply le_one
  bot_le := by simp; intro; apply zero_le

@[simp]
theorem iSup_apply (f : ι → ProbExp ϖ) : (⨆ i, f i) x = ⨆ i, f i x := by
  rw [iSup]
  simp [instCompleteLattice, CompleteLattice.toConditionallyCompleteLattice]
  apply le_antisymm
  · simp
    intro i
    apply le_iSup_of_le i
    rfl
  · simp
    intro i
    apply le_iSup₂_of_le (f i) i
    simp; rfl
@[simp]
theorem iInf_apply [Nonempty ι] (f : ι → ProbExp ϖ) : (⨅ i, f i) x = ⨅ i, f i x := by
  rw [iInf]
  simp [instCompleteLattice, CompleteLattice.toConditionallyCompleteLattice]
  apply le_antisymm
  · simp; intro i; apply iInf₂_le_of_le (f i) i; simp; rfl
  · simp_all; intro i; apply iInf_le_of_le i; rfl
@[simp]
theorem sSup_apply [Nonempty ι] (S : Set (ProbExp ϖ)) : sSup S x = ⨆ i : S, i.val x := by
  simp [instCompleteLattice, CompleteLattice.toConditionallyCompleteLattice]
  exact iSup_subtype'
@[simp]
theorem sInf_apply (S : Set (ProbExp ϖ)) [Nonempty S] : sInf S x = ⨅ i : S, i.val x := by
  simp [instCompleteLattice, CompleteLattice.toConditionallyCompleteLattice]
  split_ifs
  · simp_all
  · simp_all
    exact iInf_subtype'
@[simp] theorem sup_apply {f g : ProbExp ϖ} : (f ⊔ g) σ = f σ ⊔ g σ := by rfl
@[simp] theorem inf_apply {f g : ProbExp ϖ} : (f ⊓ g) σ = f σ ⊓ g σ := by rfl
@[simp] theorem sup_coe_apply {f g : ProbExp ϖ} : (f ⊔ g).val σ = f σ ⊔ g σ := by rfl
@[simp] theorem inf_coe_apply {f g : ProbExp ϖ} : (f ⊓ g).val σ = f σ ⊓ g σ := by rfl
@[simp] theorem max_apply {f g : ProbExp ϖ} : (max f g) σ = max (f σ) (g σ) := by rfl
@[simp] theorem min_apply {f g : ProbExp ϖ} : (min f g) σ = min (f σ) (g σ) := by rfl
@[simp] theorem max_coe_apply {f g : ProbExp ϖ} : (max f g).val σ = max (f σ) (g σ) := by rfl
@[simp] theorem min_coe_apply {f g : ProbExp ϖ} : (min f g).val σ = min (f σ) (g σ) := by rfl

@[simp] theorem one_mul : (1 : ProbExp ϖ) * p = p := by ext; simp
@[simp] theorem zero_mul : (0 : ProbExp ϖ) * p = 0 := by ext; simp

@[simp] theorem mul_one : p * (1 : ProbExp ϖ) = p := by ext; simp
@[simp] theorem mul_zero : p * (0 : ProbExp ϖ) = 0 := by ext; simp

@[simp] theorem one_add : 1 + p = 1 := by ext; simp
@[simp] theorem add_one : p + 1 = 1 := by ext; simp
@[simp] theorem zero_add : 0 + p = p := by ext; simp
@[simp] theorem add_zero : p + 0 = p := by ext; simp
@[simp] theorem sub_one : p - 1 = 0 := by ext σ; exact tsub_eq_zero_of_le (le_one p σ)
@[simp] theorem zero_sub : 0 - p = 0 := by ext; simp
@[simp] theorem sub_zero : p - 0 = p := by ext; simp

@[simp] theorem coe_one : exp_coe (ϖ:=ϖ) 1 = 1 := by rfl
@[simp] theorem coe_zero : exp_coe (ϖ:=ϖ) 0 = 0 := by rfl

@[gcongr]
theorem mul_le_mul (a b c d : ProbExp ϖ) (hac : a ≤ c) (hbd : b ≤ d) : a * b ≤ c * d := by
  intro; simp; gcongr <;> apply_assumption

@[gcongr]
theorem add_le_add (a b c d : ProbExp ϖ) (hac : a ≤ c) (hbd : b ≤ d) : a + b ≤ c + d := by
  intro; simp only [add_apply]; gcongr <;> apply_assumption

@[gcongr]
theorem sub_le_sub (a b c d : ProbExp ϖ) (hac : a ≤ c) (hdb : d ≤ b) : a - b ≤ c - d := by
  intro; simp only [sub_apply]; gcongr <;> apply_assumption

noncomputable instance : CommSemiring (ProbExp ϖ) where
  add_assoc a b c := by
    ext σ
    refine (ENNReal.toReal_eq_toReal_iff' ?_ ?_).mp ?_ <;> simp [ENNReal.toReal_min, ENNReal.toReal_add]
    apply le_antisymm <;> simp [min_add, add_min, add_assoc]
  zero_add := by simp
  add_zero := by simp
  nsmul := sorry
  nsmul_zero := sorry
  nsmul_succ := sorry
  add_comm a b := by ext σ; apply le_antisymm <;> simp [add_comm]
  left_distrib a b c := by
    ext σ
    sorry
  right_distrib := sorry
  zero_mul := sorry
  mul_zero := sorry
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry
  mul_comm := sorry

@[simp, gcongr]
theorem pickProb_le (h₁ : x ≤ z) (h₂ : y ≤ w) : p.pickProb x y ≤ p.pickProb z w := by
  intro; simp only [pickProb, add_apply, mul_apply, sub_apply, one_apply]
  gcongr <;> apply_assumption
@[simp]
theorem pickProb_le' (h₁ : x ≤ z) (h₂ : y ≤ w) : p.pickProb x y σ ≤ p.pickProb z w σ :=
  p.pickProb_le h₁ h₂ σ

@[simp]
theorem pick_of_prob_le_one {x y : ProbExp ϖ} : p.pick x y σ ≤ 1 := by
  have hx : x ≤ 1 := x.prop; have hy : y ≤ 1 := y.prop
  have := p.pickProb_le hx hy σ; simpa

@[simp] theorem coe_inv {X : Exp ϖ} :
    exp_coe (inv X) = X⁻¹ ⊓ 1 := by
      ext σ
      simp [inv]
      split_ifs with h
      · simp_all
      · simp_all
        exact h.le

variable [DecidableEq ϖ]

@[simp] theorem exp_coe_subst {X : ProbExp ϖ} {x : ϖ} {e : Exp ϖ} :
    (exp_coe X)[x ↦ e] = (exp_coe X[x ↦ e]) := by rfl
@[simp] theorem mk_subst {x : ϖ} {e : Exp ϖ} :
    (instSubstExpOfDecidableEq.subst ⟨q, hp⟩ x e) = ⟨q[x ↦ e], by
      intro σ; simp; apply hp⟩ := by rfl
@[simp] theorem inv_subst {X : Exp ϖ} {x : ϖ} {e : Exp ϖ} :
    (inv X)[x ↦ e] = inv X[x ↦ e] := by rfl

end ProbExp

end pGCL
