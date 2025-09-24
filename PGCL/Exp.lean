import Mathlib.Data.ENNReal.Operations

namespace pGCL

variable {ϖ : Type*}
def States (ϖ : Type*) := ϖ → Nat

instance : Nonempty (States ϖ) := ⟨fun _ ↦ Inhabited.default⟩

abbrev NExp (ϖ : Type*) := States ϖ → Nat
abbrev Exp (ϖ : Type*) := States ϖ → ENNReal
abbrev BExpr (ϖ : Type*) := States ϖ → Prop
def ProbExp (ϖ : Type*) := {e : Exp ϖ // e ≤ 1}

def States.subst [DecidableEq ϖ] (σ : States ϖ) (x : ϖ) (v : Nat) : States ϖ :=
  fun α ↦ if x = α then v else σ α

@[ext]
def States.ext {σ₁ σ₂ : States ϖ} (h : ∀ v, σ₁ v = σ₂ v) : σ₁ = σ₂ := _root_.funext h

notation σ "[" x " ↦ " v "]" => States.subst σ x v

def Exp.subst [DecidableEq ϖ] (e : Exp ϖ) (x : ϖ) (A : NExp ϖ) : Exp ϖ := fun σ ↦ e (σ[x ↦ A σ])

@[simp]
theorem Exp.subst_lift [DecidableEq ϖ] (e : Exp ϖ) : e.subst x A σ = e (σ[x ↦ A σ]) := rfl

@[gcongr]
theorem Exp.add_le_add (a b c d : Exp ϖ) (hac : a ≤ c) (hbd : b ≤ d) : a + b ≤ c + d := by
  intro; simp; gcongr <;> apply_assumption
@[gcongr]
theorem Exp.mul_le_mul (a b c d : Exp ϖ) (hac : a ≤ c) (hbd : b ≤ d) : a * b ≤ c * d := by
  intro; simp; gcongr <;> apply_assumption

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

def not (b : BExpr ϖ) : BExpr ϖ := (¬b ·)
def iver (b : BExpr ϖ) [DecidablePred b] : Exp ϖ := (if b · then 1 else 0)
def probOf (b : BExpr ϖ) [DecidablePred b] : ProbExp ϖ :=
  ⟨(if b · then 1 else 0), by intro; simp; split <;> simp⟩

notation "i[" b "]" => BExpr.iver b
notation "p[" b "]" => BExpr.probOf b

variable {b : BExpr ϖ} [DecidablePred b]

instance : DecidablePred b.not := fun σ ↦
  if h : b σ then .isFalse (by simp_all [BExpr.not]) else .isTrue (by simp_all [BExpr.not])

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
@[simp] theorem true_not_iver (h : b σ = true) : i[b.not] σ = 0 := by simp [iver, not, h]
@[simp] theorem false_not_iver (h : b σ = false) : i[b.not] σ = 1 := by simp [iver, not, h]

@[simp] theorem true_probOf (h : b σ = true) : p[b] σ = 1 := by simp [probOf, h]
@[simp] theorem false_probOf (h : b σ = false) : p[b] σ = 0 := by simp [probOf, h]
@[simp] theorem true_not_probOf (h : b σ = true) : p[b.not] σ = 0 := by simp [probOf, not, h]
@[simp] theorem false_not_probOf (h : b σ = false) : p[b.not] σ = 1 := by simp [probOf, not, h]

end BExpr

namespace ProbExp

variable (p : ProbExp ϖ) (σ : States ϖ)

@[simp] theorem add_one : p σ + (1 - p σ) = 1 := add_tsub_cancel_of_le (p.prop σ)

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

noncomputable def pick (x y : Exp ϖ) : Exp ϖ := p * x + (1 - p) * y
noncomputable def pickProb (x y : ProbExp ϖ) : ProbExp ϖ := ⟨p * x + (1 - p) * y, by
  intro σ; simp
  calc
    p σ * x σ + (1 - p σ) * y σ ≤ p σ * 1 + (1 - p σ) * 1 := by gcongr <;> simp
    _ ≤ 1 := by simp⟩

@[simp]
theorem pick_true {x y : Exp ϖ} [DecidablePred b] (h : b σ) : p[b].pick x y σ = x σ := by
  simp [h, pick]
@[simp]
theorem pick_false {x y : Exp ϖ} [DecidablePred b] (h : ¬b σ) : p[b].pick x y σ = y σ := by
  simp [h, pick]

@[simp, gcongr]
theorem pick_le (h₁ : x ≤ z) (h₂ : y ≤ w) : p.pick x y ≤ p.pick z w := by
  intro; simp [pick]; gcongr <;> apply_assumption
@[simp]
theorem pick_le' (h₁ : x ≤ z) (h₂ : y ≤ w) : p.pick x y σ ≤ p.pick z w σ := p.pick_le h₁ h₂ σ

@[simp] theorem pick_same : p.pick x x = x := by ext σ; simp [pick, ← add_mul]

@[simp] theorem pick_of : p σ * x σ + (1 - p σ) * y σ = p.pick x y σ := rfl

@[ext] theorem ext {p₁ p₂ : ProbExp ϖ} (h : ∀ σ, p₁ σ = p₂ σ) : p₁ = p₂ := by
  cases p₁; cases p₂; congr; simp at h; ext; apply_assumption

@[simp]
instance instLE : LE (ProbExp ϖ) where
  le a b := ∀ x, a x ≤ b x

@[simp] theorem coe_le {f g : Exp ϖ} {hf : f ≤ 1} {hg : g ≤ 1} :
    instLE.le (⟨f, hf⟩) ⟨g, hg⟩ ↔ f ≤ g := by rfl

instance : PartialOrder (ProbExp ϖ) where
  le_refl a σ := by rfl
  le_trans a b c hab hbc σ := by exact (hab σ).trans (hbc σ)
  le_antisymm a b hab hba := by ext σ; exact (hab σ).antisymm (hba σ)

instance instOfNat0 : OfNat (ProbExp ϖ) 0 := ⟨⟨fun _ ↦ 0, by intro; simp⟩⟩
instance instOfNat1 : OfNat (ProbExp ϖ) 1 := ⟨⟨fun _ ↦ 1, by intro; simp⟩⟩

@[simp] theorem zero_apply : instOfNat0.ofNat σ = 0 := rfl
@[simp] theorem one_apply : instOfNat1.ofNat σ = 1 := rfl

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

noncomputable instance : Mul (ProbExp ϖ) where
  mul a b := ⟨fun σ ↦ a σ * b σ, by intro σ; simp; refine Left.mul_le_one ?_ ?_ <;> simp⟩

@[simp] theorem mul_apply {a b : ProbExp ϖ} : (a * b) σ = a σ * b σ := by rfl

@[gcongr]
theorem mul_le_mul (a b c d : ProbExp ϖ) (hac : a ≤ c) (hbd : b ≤ d) : a * b ≤ c * d := by
  intro; simp; gcongr <;> apply_assumption

noncomputable instance : Add (ProbExp ϖ) where
  add a b := ⟨fun σ ↦ (a σ + b σ) ⊓ 1, by intro σ; simp⟩

@[simp] theorem add_apply {a b : ProbExp ϖ} : (a + b) σ = (a σ + b σ) ⊓ 1 := by rfl

@[gcongr]
theorem add_le_add (a b c d : ProbExp ϖ) (hac : a ≤ c) (hbd : b ≤ d) : a + b ≤ c + d := by
  intro; simp only [add_apply]; gcongr <;> apply_assumption

noncomputable instance : Sub (ProbExp ϖ) where
  sub a b := ⟨fun σ ↦ a σ - b σ, by intro σ; simp; exact le_add_right (by simp)⟩

@[simp] theorem sub_apply {a b : ProbExp ϖ} : (a - b) σ = a σ - b σ := by rfl

@[gcongr]
theorem sub_le_sub (a b c d : ProbExp ϖ) (hac : a ≤ c) (hdb : d ≤ b) : a - b ≤ c - d := by
  intro; simp only [sub_apply]; gcongr <;> apply_assumption

@[simp, gcongr]
theorem pickProb_le (h₁ : x ≤ z) (h₂ : y ≤ w) : p.pickProb x y ≤ p.pickProb z w := by
  intro; simp [pickProb, -pick_of]; gcongr <;> apply_assumption
@[simp]
theorem pickProb_le' (h₁ : x ≤ z) (h₂ : y ≤ w) : p.pickProb x y σ ≤ p.pickProb z w σ :=
  p.pickProb_le h₁ h₂ σ

end ProbExp

end pGCL
