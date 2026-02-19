import PGCL.WeakestLiberalPre
import PGCL.KInduction
import Mathlib.Logic.Function.DependsOn

open Optimization.Notation

theorem OrderHom.le_gfp_prob {x : 𝔼[Γ, ENNReal]} {f : pGCL.ProbExp Γ →o pGCL.ProbExp Γ}
    (h₁ : x ≤ 1)
    (h₂ : x ≤ f ⟨x, h₁⟩):
    x ≤ OrderHom.gfp f := by
  suffices ⟨x, h₁⟩ ≤ OrderHom.gfp f by exact this
  apply OrderHom.le_gfp _ h₂

theorem OrderHom.le_gfp_of_iter_prob {x : 𝔼[Γ, ENNReal]} {f : pGCL.ProbExp Γ →o pGCL.ProbExp Γ}
    (k : ℕ)
    (h₁ : x ≤ 1)
    (h₂ : x ≤ f ((f · ⊔ ⟨x, h₁⟩)^[k] ⟨x, h₁⟩)) :
    x ≤ OrderHom.gfp f := by
  suffices ⟨x, h₁⟩ ≤ OrderHom.gfp f by exact this
  apply OrderHom.le_gfp_of_iter k h₂

namespace pGCL

variable {𝒱 : Type*} {Γ : Γ[𝒱]}

@[gcongr]
def Exp.substs_mono [DecidableEq 𝒱] {X₁ X₂ : 𝔼[Γ, ENNReal]} {xs : List ((v : 𝒱) × 𝔼[Γ, Γ v])}
    (h : X₁ ≤ X₂) : X₁[..xs] ≤ X₂[..xs] := by
  induction xs generalizing X₁ X₂ with
  | nil => simp [h]
  | cons x xs ih => apply fun σ ↦ ih h _


@[gcongr]
theorem Exp.himp_mono {a₁ a₂ b₁ b₂ : 𝔼[Γ, ENNReal]} (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) :
    a₁ ⇨ b₁ ≤ a₂ ⇨ b₂ := by
  intro σ
  specialize ha σ
  specialize hb σ
  simp [himp]
  split_ifs <;> try grind
  · simp_all

@[gcongr]
theorem Exp.hnot_mono {a₁ a₂ : 𝔼[Γ, ENNReal]} (ha : a₂ ≤ a₁) :
    ￢ a₁ ≤ ￢ a₂ := by
  intro σ
  specialize ha σ
  simp [hnot]
  split_ifs <;> simp_all
@[gcongr]
theorem Exp.compl_mono {a₁ a₂ : 𝔼[Γ, ENNReal]} (ha : a₂ ≤ a₁) :
    a₁ᶜ ≤ a₂ᶜ := by
  apply compl_le_compl ha
@[gcongr]
theorem Exp.validate_mono {a₁ a₂ : 𝔼[Γ, ENNReal]} (ha : a₁ ≤ a₂) :
    ▵ a₁ ≤ ▵ a₂ := by
  show ￢￢ a₁ ≤ ￢￢ a₂
  gcongr
@[gcongr]
theorem Exp.covalidate_mono {a₁ a₂ : 𝔼[Γ, ENNReal]} (ha : a₁ ≤ a₂) :
    ▿ a₁ ≤ ▿ a₂ := by
  show ~~ a₁ ≤ ~~ a₂
  gcongr

@[gcongr]
theorem ENNReal.hnot_mono {a₁ a₂ : ENNReal} (ha : a₂ ≤ a₁) :
    ￢ a₁ ≤ ￢ a₂ := by
  simp [hnot]
  split_ifs <;> simp_all
@[gcongr]
theorem ENNReal.covalidate_mono {a₁ a₂ : ENNReal} (ha : a₁ ≤ a₂) :
    ▿ a₁ ≤ ▿ a₂ := by
  show ~~ a₁ ≤ ~~ a₂
  gcongr

@[grind =, simp]
theorem Exp.zero_himp {a : 𝔼[Γ, ENNReal]} :
    (0 ⇨ a) = ⊤ := by simp [himp]; rfl

@[grind =]
theorem State.subst_comm [DecidableEq 𝒱] {σ : State Γ} {x₁ x₂ : 𝒱} {v₁ v₂} (h : x₁ ≠ x₂) :
    σ[x₁ ↦ v₁][x₂ ↦ v₂] = σ[x₂ ↦ v₂][x₁ ↦ v₁] := by ext; grind

namespace Exp

variable {Γ : Γ[𝒱]} [DecidableEq 𝒱] {a b : 𝔼[Γ, ENNReal]} {b : BExpr Γ}
variable (xs : List ((v : 𝒱) × 𝔼[Γ, Γ v]))

@[simp] theorem top_subst :
    (⊤ : 𝔼[Γ, ENNReal])[..xs] = (⊤ : 𝔼[Γ, ENNReal]) := by
  induction xs with try simp
  | cons x xs ih =>
    simp [Substitution.substs_cons, Substitution.subst, ih]
    rfl

@[simp] theorem iver_subst :
    i[b][..xs] = i[(b)[..xs]] := by
  induction xs generalizing b with try simp
  | cons x xs ih =>
    simp only [Substitution.substs_cons, Substitution.subst, Substitution.substs_nil, ih]
    rfl
@[simp] theorem not_subst :
    (bᶜ)[..xs] = (b)[..xs]ᶜ := by
  induction xs generalizing b with try simp
  | cons x xs ih =>
    simp only [Substitution.substs_cons, Substitution.subst, Substitution.substs_nil]
    rw [ih]
    rfl
@[simp] theorem hnot_subst :
    (￢a)[..xs] = ￢a[..xs] := by
  induction xs generalizing a with try simp
  | cons x xs ih =>
    ext σ
    simp_all only [Substitution.substs_cons, Substitution.subst, Substitution.substs_nil,
      Pi.hnot_apply]
@[simp] theorem validate_subst :
    (▵ a)[..xs] = ▵ a[..xs] := by
  induction xs generalizing a with try simp
  | cons x xs ih =>
    ext σ
    simp_all only [Substitution.substs_cons, Substitution.subst, Substitution.substs_nil,
      validate_apply]
@[simp] theorem covalidate_subst :
    (▿ a)[..xs] = ▿ a[..xs] := by
  induction xs generalizing a with try simp
  | cons x xs ih =>
    ext σ
    simp_all only [Substitution.substs_cons, Substitution.subst, Substitution.substs_nil,
      covalidate_apply]

end Exp

@[simp] theorem BExpr.eq_self {a : 𝔼[Γ, ENNReal]} : BExpr.eq a a = true := by ext; simp
@[simp] theorem BExpr.eq_of_ne {a b : 𝔼[Γ, ENNReal]} (h : ∀ σ, a σ ≠ b σ) :
    BExpr.eq a b = false := by ext; simp_all [coe_prop]
@[simp] theorem BExpr.iver_coe_bool : i[BExpr.coe_prop (Γ:=Γ) a] = i[a] := by
  ext; simp [BExpr.coe_prop, Iverson.iver]
@[simp] theorem BExpr.not_coe_bool : (BExpr.coe_prop (Γ:=Γ) a)ᶜ = BExpr.coe_prop ¬a := by
  ext; simp only [Pi.compl_apply, coe_prop, compl_iff_not]

namespace State

open scoped Classical in
noncomputable
def cofix (σ₀ : State Γ) {S : Set 𝒱} (σ : State (Γ · : ↑Sᶜ → _)) : State Γ :=
  fun v ↦ if h : v ∈ S then σ₀ v else σ ⟨v, h⟩

@[grind =, simp]
theorem cofix_apply_mem {S : Set 𝒱} (h : v ∈ S) (σ₀ : State Γ) (σ' : State (Γ · : ↑Sᶜ → _)) :
    σ₀.cofix σ' v = σ₀ v := by simp [h, cofix]

end State

open scoped Classical in
noncomputable
def Exp.fix (X : 𝔼[Γ, α]) (S : Set 𝒱) (σ₀ : State Γ) : 𝔼[(Γ · : ↑Sᶜ → _), α] :=
  fun σ ↦ X (σ₀.cofix σ)

@[grind =, simp]
theorem Exp.fix_empty (φ : 𝔼[Γ, α]) : Exp.fix φ ∅ σ₀ σ = φ (σ ⟨·, id⟩) := by
  simp only [fix]; congr; ext; grind [State.cofix]
@[grind =, simp]
theorem Exp.fix_compl_empty (φ : 𝔼[Γ, α]) : Exp.fix φ ∅ᶜ σ₀ σ = φ σ₀ := by
  simp only [fix]; congr; ext; grind [State.cofix]
@[grind ., simp]
theorem Exp.fix_compl_empty_eq (φ ψ : 𝔼[Γ, α]) : Exp.fix φ ∅ᶜ = Exp.fix ψ ∅ᶜ ↔ φ = ψ := by
  constructor
  · intro h
    ext σ₀
    replace h := congrFun₂ h σ₀ (σ₀ ·)
    grind
  · grind

open scoped Classical in
noncomputable
def ProbExp.fix (X : ProbExp Γ) (S : Set 𝒱) (σ₀ : State Γ) : ProbExp (Γ · : ↑Sᶜ → _) :=
  ⟨Exp.fix X S σ₀, by intro σ; simp [Exp.fix]⟩

@[simp] theorem ProbExp.fix_apply {φ : ProbExp Γ} : φ.fix S σ₀ σ = φ (σ₀.cofix σ) := rfl

@[grind]
def mods : pGCL Γ → Set 𝒱
  | pgcl {skip} => ∅
  | pgcl {@x := @_} => {x}
  | pgcl {@C₁ ; @C₂} => C₁.mods ∪ C₂.mods
  | pgcl {{@C₁} [@_] {@C₂}} => C₁.mods ∪ C₂.mods
  | pgcl {{@C₁} [] {@C₂}} => C₁.mods ∪ C₂.mods
  | pgcl {while @_ {@C'}} => C'.mods
  | pgcl {tick(@ _)} => ∅
  | pgcl {observe(@ _)} => ∅

open scoped Classical in
noncomputable def fix (C : pGCL Γ) (S : Set 𝒱) (σ₀ : State Γ) : pGCL (Γ · : ↑Sᶜ → _) :=
  match C with
  | pgcl {skip} => pgcl {skip}
  | pgcl {@x := @A} =>
    let q : (State fun (x : ↑Sᶜ) ↦ Γ x) → Γ x := Exp.fix A S σ₀
    if hx : _ then pgcl {@⟨x, hx⟩ := @q} else pgcl {skip}
  | pgcl {@C₁ ; @C₂} => pgcl {@(C₁.fix S σ₀) ; @(C₂.fix S σ₀)}
  | pgcl {{@C₁} [@p] {@C₂}} =>
    pgcl {{@(C₁.fix S σ₀)} [@(p.fix S σ₀)] {@(C₂.fix S σ₀)}}
  | pgcl {{@C₁} [] {@C₂}} => pgcl {{@(C₁.fix S σ₀)} [] {@(C₂.fix S σ₀)}}
  | pgcl {while @b {@C'}} => pgcl {while @(Exp.fix b S σ₀) {@(C'.fix S σ₀)}}
  | pgcl {tick(@ r)} => pgcl {tick(@(Exp.fix r S σ₀))}
  | pgcl {observe(@ b)} => pgcl {observe(@(Exp.fix b S σ₀))}

@[simp] theorem Exp.fix_apply {φ : 𝔼[Γ, α]} : Exp.fix φ S σ₀ σ = φ (σ₀.cofix σ) := rfl

@[grind =, simp]
theorem Exp.zero_fix : Exp.fix (0 : 𝔼[Γ, ENNReal]) = 0 := rfl
@[grind =, simp]
theorem Exp.top_fix : Exp.fix (⊤ : 𝔼[Γ, ENNReal]) = ⊤ := rfl

@[simp]
theorem Exp.iSup_fix {X : α → 𝔼[Γ, ENNReal]} :
    Exp.fix (⨆ n, X n) S σ₀ σ = ⨆ n, Exp.fix (X n) S σ₀ σ := by simp [Exp.fix]
@[simp]
theorem Exp.iInf_fix {X : α → 𝔼[Γ, ENNReal]} :
    Exp.fix (⨅ n, X n) S σ₀ σ = ⨅ n, Exp.fix (X n) S σ₀ σ := by simp [Exp.fix]

variable [DecidableEq 𝒱]

open scoped Classical in
@[grind =, simp]
theorem Exp.subst_fix {φ : 𝔼[Γ, α]} {x : 𝒱} {e : 𝔼[Γ, Γ x]} {S : Set 𝒱}
    (hx : x ∉ S) :
    Exp.fix φ[x ↦ e] S σ = (Exp.fix φ S σ)[⟨x, hx⟩ ↦ Exp.fix e S σ] := by
  ext σ'
  simp only [fix_apply, subst_apply]
  congr! with v
  ext
  grind [State.cofix]

example {φ : 𝔼[Γ, ENNReal]} {x : 𝒱} {σ₀ : State Γ}
    {σ : State (𝒱:=↑({x} : Set 𝒱)ᶜᶜ) (Γ ·)} :
    Exp.fix φ ({x}ᶜ : Set 𝒱) σ₀ σ = φ σ₀[x ↦ σ ⟨x, by simp⟩] := by
  simp only [Exp.fix_apply]
  congr
  ext y
  grind [State.cofix]

theorem wp_le_of_fix (C : pGCL Γ) (φ : 𝔼[Γ, ENNReal]) (S : Set 𝒱) (X : 𝔼[Γ, ENNReal]) :
    Exp.fix (wp[O]⟦@C⟧ φ) S σ₀ ≤ Exp.fix X S σ₀ → wp[O]⟦@C⟧ φ σ₀ ≤ X σ₀ := by
  intro h
  replace h := h fun x ↦ σ₀ x
  simp_all
  convert h <;> ext <;> simp [State.cofix]

theorem le_wlp_of_fix (C : pGCL Γ) (φ : 𝔼[Γ, ENNReal]) (S : Set 𝒱) (X : 𝔼[Γ, ENNReal]) :
    Exp.fix X S σ₀ ≤ Exp.fix (wlp[O]⟦@C⟧ φ) S σ₀ → X σ₀ ≤ wlp[O]⟦@C⟧ φ σ₀ := by
  intro h
  replace h := h fun x ↦ σ₀ x
  simp_all
  convert h <;> ext <;> simp [State.cofix]

theorem le_wlp'_of_fix (C : pGCL Γ) (φ : ProbExp Γ) (S : Set 𝒱) (X : ProbExp Γ) :
    X.fix S σ₀ ≤ (wlp'[O]⟦@C⟧ φ).fix S σ₀ → X σ₀ ≤ wlp'[O]⟦@C⟧ φ σ₀ := by
  intro h
  replace h := h fun x ↦ σ₀ x
  simp_all
  convert h <;> ext <;> simp [State.cofix]

theorem wp_fix (C : pGCL Γ) (φ : 𝔼[Γ, ENNReal]) (S : Set 𝒱) (hS : C.mods ⊆ Sᶜ) :
    Exp.fix (wp[O]⟦@C⟧ φ) S σ₀ = wp[O]⟦@(C.fix S σ₀)⟧ (Exp.fix φ S σ₀) := by
  symm
  induction C generalizing φ with simp_all [fix, mods] <;> try rfl
  | nonDet => cases O <;> simp [Optimization.opt] <;> rfl
  | loop b C ih =>
    ext σ
    simp only [wp_loop_eq_iter, iSup_apply, Exp.fix_apply]
    congr with i
    induction i generalizing σ with
    | zero => simp only [Function.iterate_zero, id_eq, Pi.ofNat_apply]
    | succ i ih' =>
      simp only [Function.iterate_succ', Function.comp_apply]
      nth_rw 1 [Ψ]
      nth_rw 2 [Ψ]
      simp only [OrderHom.coe_mk, OrderHom.mk_apply, Pi.add_apply, Pi.mul_apply, Pi.iver_apply,
        Exp.fix_apply, Pi.compl_apply, compl_iff_not]
      congr! 2
      classical
      rw [← funext_iff] at ih'
      rw [ih']
      exact congrFun (ih ((Ψ[_] b φ)^[i] 0)) σ

theorem wlp_fix (C : pGCL Γ) (φ : 𝔼[Γ, ENNReal]) (S : Set 𝒱) (hS : C.mods ⊆ Sᶜ) :
    Exp.fix (wlp[O]⟦@C⟧ φ) S σ₀ = wlp[O]⟦@(C.fix S σ₀)⟧ (Exp.fix φ S σ₀) := by
  symm
  induction C generalizing φ with (simp_all [fix, mods]; try rfl)
  | assign x A =>
    ext σ
    simp_all only [Pi.inf_apply, Pi.substs_cons, Exp.fix_apply, Substitution.substs_nil,
      Pi.one_apply]
    congr
    ext v
    simp
    if hv : v ∈ S then
      simp [hv]
      grind
    else
      simp [State.cofix, hv]
  | seq C₁ C₂ ih₁ ih₂ =>
    ext
    simp
    specialize ih₁ (wlp[O]⟦@C₂⟧ φ ⊓ 1)
    have : (Exp.fix (wlp[O]⟦@C₂⟧ φ ⊓ 1) S σ₀) = (Exp.fix (wlp[O]⟦@C₂⟧ φ) S σ₀) ⊓ 1 := by
      ext; simp
    simp [this] at ih₁
    simp [ih₁]
  | nonDet => cases O <;> simp [Optimization.opt] <;> rfl
  | loop b C ih =>
    ext σ
    simp only [wlp_loop_eq_iter, iInf_apply, Exp.iInf_fix]
    simp
    congr with i
    induction i generalizing σ with
    | zero => simp only [Function.iterate_zero, id_eq, Pi.one_apply]
    | succ i ih' =>
      simp only [Function.iterate_succ', Function.comp_apply]
      nth_rw 1 [Ψ]
      nth_rw 2 [Ψ]
      simp only [OrderHom.coe_mk, OrderHom.mk_apply, Pi.add_apply, Pi.mul_apply, Pi.iver_apply,
        Exp.fix_apply, Pi.compl_apply, compl_iff_not, Pi.inf_apply, Pi.one_apply]
      congr! 2
      classical
      rw [← funext_iff] at ih'
      rw [ih']
      exact congrFun (ih ((Ψ[_] b (φ ⊓ 1))^[i] 1)) σ

theorem wlp'_fix_apply (C : pGCL Γ) (φ : ProbExp Γ) (S : Set 𝒱) (hS : C.mods ⊆ Sᶜ) (σ) :
    Exp.fix (wlp'[O]⟦@C⟧ φ) S σ₀ σ = wlp'[O]⟦@(C.fix S σ₀)⟧ ⟨Exp.fix φ S σ₀, by intro; simp⟩ σ := by
  simp
  have := congrFun (C.wlp_fix φ.val S hS (O:=O) (σ₀:=σ₀)) σ
  simp at this
  convert this
  · simp [wlp]; congr; ext σ; have := φ.prop σ; simp_all only [Pi.one_apply,
    ProbExp.ofExp_apply, inf_of_le_left]; rfl
  · simp [wlp]
    congr
    ext σ
    simp
    have := φ.prop (σ₀.cofix σ)
    simp_all
    rfl

theorem wlp'_fix_apply' (C : pGCL Γ) (φ : 𝔼[Γ, ENNReal]) (hφ : φ ≤ 1) (S) (hS : C.mods ⊆ Sᶜ) (σ) :
      Exp.fix (wlp'[O]⟦@C⟧ ⟨φ, hφ⟩) S σ₀ σ
    = wlp'[O]⟦@(C.fix S σ₀)⟧ ⟨Exp.fix φ S σ₀, by intro; simp; apply hφ⟩ σ :=
  wlp'_fix_apply _ _ _ hS _

theorem wlp'_fix (C : pGCL Γ) (φ : ProbExp Γ) (S : Set 𝒱) (hS : C.mods ⊆ Sᶜ) :
    (wlp'[O]⟦@C⟧ φ).fix S σ₀ = wlp'[O]⟦@(C.fix S σ₀)⟧ (φ.fix S σ₀) := by
  ext σ
  have := congrFun (C.wlp_fix φ S hS (σ₀:=σ₀) (O:=O)) σ
  simp [wlp] at this
  convert this
  · ext; simp [ProbExp.ofExp_apply, Exp.fix_apply, ProbExp.le_one_apply, inf_of_le_left]

end pGCL
