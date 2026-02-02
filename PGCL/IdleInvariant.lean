import PGCL.WeakestLiberalPre

open Optimization.Notation

namespace pGCL

variable {𝒱 : Type*} {ϖ : Γ[𝒱]}

@[gcongr]
def Exp.substs_mono [DecidableEq 𝒱] {X₁ X₂ : 𝔼[ϖ, ENNReal]} {xs : List ((v : 𝒱) × 𝔼[ϖ, ϖ v])}
    (h : X₁ ≤ X₂) : X₁[..xs] ≤ X₂[..xs] := by
  induction xs generalizing X₁ X₂ with
  | nil => simp [h]
  | cons x xs ih => apply fun σ ↦ ih h _

@[gcongr]
theorem Exp.hcoimp_mono {a₁ a₂ b₁ b₂ : 𝔼[ϖ, ENNReal]} (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) :
    a₁ ↜ b₁ ≤ a₂ ↜ b₂ := by
  intro σ
  specialize ha σ
  specialize hb σ
  simp [Exp.hcoimp_apply, instHCoImpENNReal]
  split_ifs <;> try grind
  simp_all

@[gcongr]
theorem Exp.himp_mono {a₁ a₂ b₁ b₂ : 𝔼[ϖ, ENNReal]} (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) :
    a₁ ⇨ b₁ ≤ a₂ ⇨ b₂ := by
  intro σ
  specialize ha σ
  specialize hb σ
  simp [himp]
  split_ifs <;> try grind
  · simp_all

@[gcongr]
theorem Exp.hnot_mono {a₁ a₂ : 𝔼[ϖ, ENNReal]} (ha : a₂ ≤ a₁) :
    ￢ a₁ ≤ ￢ a₂ := by
  intro σ
  specialize ha σ
  simp [hnot]
  split_ifs <;> simp_all
@[gcongr]
theorem Exp.hconot_mono {a₁ a₂ : 𝔼[ϖ, ENNReal]} (ha : a₂ ≤ a₁) :
    ~ a₁ ≤ ~ a₂ := by
  show a₁ ⇨ 0 ≤ a₂ ⇨ 0
  gcongr
@[gcongr]
theorem Exp.validate_mono {a₁ a₂ : 𝔼[ϖ, ENNReal]} (ha : a₁ ≤ a₂) :
    ▵ a₁ ≤ ▵ a₂ := by
  show ￢￢ a₁ ≤ ￢￢ a₂
  gcongr
@[gcongr]
theorem Exp.covalidate_mono {a₁ a₂ : 𝔼[ϖ, ENNReal]} (ha : a₁ ≤ a₂) :
    ▿ a₁ ≤ ▿ a₂ := by
  show ~~ a₁ ≤ ~~ a₂
  gcongr

@[gcongr]
theorem ENNReal.hcoimp_mono {a₁ a₂ b₁ b₂ : ENNReal} (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) :
    a₁ ↜ b₁ ≤ a₂ ↜ b₂ := by
  simp [instHCoImpENNReal]
  split_ifs <;> try grind
  simp_all
@[gcongr]
theorem ENNReal.hnot_mono {a₁ a₂ : ENNReal} (ha : a₂ ≤ a₁) :
    ￢ a₁ ≤ ￢ a₂ := by
  simp [hnot]
  split_ifs <;> simp_all
@[gcongr]
theorem ENNReal.covalidate_mono {a₁ a₂ : ENNReal} (ha : a₁ ≤ a₂) :
    ▿ a₁ ≤ ▿ a₂ := by
  show ~~ a₁ ≤ ~~ a₂
  simp [hconot, himp]
  split_ifs <;> try grind
  · simp
  · simp_all

@[grind =, simp]
theorem Exp.zero_himp {a : 𝔼[ϖ, ENNReal]} :
    (0 ⇨ a) = ⊤ := by simp [himp]; rfl

@[grind =, simp]
theorem BExpr.subst_single_apply [DecidableEq 𝒱] {b : BExpr ϖ} :
    b[x ↦ v] σ = b σ[x ↦ v σ] := by
  rfl
@[grind =]
theorem States.subst_comm [DecidableEq 𝒱] {σ : States ϖ} {x₁ x₂ : 𝒱} {v₁ v₂} (h : x₁ ≠ x₂) :
    σ[x₁ ↦ v₁][x₂ ↦ v₂] = σ[x₂ ↦ v₂][x₁ ↦ v₁] := by ext; grind

namespace Exp

variable {ϖ : Γ[𝒱]} [DecidableEq 𝒱] {a b : 𝔼[ϖ, ENNReal]} {b : BExpr ϖ}
variable (xs : List ((v : 𝒱) × 𝔼[ϖ, ϖ v]))

@[simp] theorem top_subst :
    (⊤ : 𝔼[ϖ, ENNReal])[..xs] = (⊤ : 𝔼[ϖ, ENNReal]) := by
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
    (b.not)[..xs] = (b)[..xs].not := by
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

@[simp] theorem BExpr.eq_self {a : 𝔼[ϖ, ENNReal]} : BExpr.eq a a = true := by ext; simp
@[simp] theorem BExpr.eq_of_ne {a b : 𝔼[ϖ, ENNReal]} (h : ∀ σ, a σ ≠ b σ) : BExpr.eq a b = false := by
  ext; simp_all [coe_prop]
@[simp] theorem BExpr.iver_coe_bool :
    i[BExpr.coe_prop (ϖ:=ϖ) a] = i[a] := by
  ext
  simp [BExpr.coe_prop, DFunLike.coe, Iverson.iver]
@[simp] theorem BExpr.not_coe_bool :
    BExpr.not (ϖ:=ϖ) (BExpr.coe_prop a) = BExpr.coe_prop ¬a := by
  ext
  simp [BExpr.not, BExpr.coe_prop, DFunLike.coe]

open scoped Classical in
noncomputable
def States.cofix (σ₀ : States ϖ) {S : Set 𝒱} (σ : States (𝒱:=↑Sᶜ) (ϖ ·)) : States ϖ :=
  fun v ↦ if h : v ∈ S then σ₀ v else σ ⟨v, h⟩

@[grind =, simp]
theorem States.cofix_apply_mem {S : Set 𝒱} (h : v ∈ S) (σ₀ : States ϖ) (σ' : States (ϖ · : ↑Sᶜ → Type)) :
    σ₀.cofix σ' v = σ₀ v := by simp [h, cofix]

open scoped Classical in
noncomputable
def Exp.fix (X : 𝔼[ϖ, α]) (S : Set 𝒱) (σ₀ : States ϖ) : 𝔼[(ϖ · : ↑Sᶜ → Type), α] :=
  fun σ ↦ X (σ₀.cofix σ)

@[grind =, simp]
theorem Exp.fix_empty (φ : 𝔼[ϖ, α]) : Exp.fix φ ∅ σ₀ σ = φ (σ ⟨·, id⟩) := by
  simp only [fix]; congr; ext; grind [States.cofix]
@[grind =, simp]
theorem Exp.fix_compl_empty (φ : 𝔼[ϖ, α]) : Exp.fix φ ∅ᶜ σ₀ σ = φ σ₀ := by
  simp only [fix]; congr; ext; grind [States.cofix]
@[grind ., simp]
theorem Exp.fix_compl_empty_eq (φ ψ : 𝔼[ϖ, α]) : Exp.fix φ ∅ᶜ = Exp.fix ψ ∅ᶜ ↔ φ = ψ := by
  constructor
  · intro h
    ext σ₀
    replace h := congrFun₂ h σ₀ (σ₀ ·)
    grind
  · grind

open scoped Classical in
noncomputable
def BExpr.fix (X : BExpr ϖ) (S : Set 𝒱) (σ₀ : States ϖ) : BExpr (ϖ · : ↑Sᶜ → Type) :=
  fun σ ↦ X (σ₀.cofix σ)

open scoped Classical in
@[grind =, simp]
theorem BExpr.fix_apply (X : BExpr ϖ) (S : Set 𝒱) (σ₀ : States ϖ) (σ : States (ϖ · : ↑Sᶜ → Type)) :
    (X.fix S σ₀) σ = X (σ₀.cofix σ) := rfl

open scoped Classical in
noncomputable
def ProbExp.fix (X : ProbExp ϖ) (S : Set 𝒱) (σ₀ : States ϖ) : ProbExp (ϖ · : ↑Sᶜ → Type) :=
  ⟨fun σ ↦ X fun v ↦ if h : v ∈ S then σ₀ v else σ ⟨v, h⟩, by intro σ; simp⟩

-- @[gcongr]
-- theorem Exp.ennreal_coe_le (h : a ≤ b) :
--     pGCL.Exp.ennreal_coe (ϖ:=ϖ) a ≤ pGCL.Exp.ennreal_coe b := by
--   intro; grind

@[grind]
def mods : pGCL ϖ → Set 𝒱
  | pgcl {skip} => ∅
  | pgcl {~x := ~_} => {x}
  | pgcl {~C₁ ; ~C₂} => C₁.mods ∪ C₂.mods
  | pgcl {{~C₁} [~_] {~C₂}} => C₁.mods ∪ C₂.mods
  | pgcl {{~C₁} [] {~C₂}} => C₁.mods ∪ C₂.mods
  | pgcl {while ~_ {~C'}} => C'.mods
  | pgcl {tick(~ _)} => ∅
  | pgcl {observe(~ _)} => ∅

open scoped Classical in
noncomputable def fix (C : pGCL ϖ) (S : Set 𝒱) (σ₀ : States ϖ) : pGCL (ϖ · : ↑Sᶜ → Type) :=
  match C with
  | pgcl {skip} => pgcl {skip}
  | pgcl {~x := ~A} =>
    let q : (States fun (x : ↑Sᶜ) ↦ ϖ x) → ϖ x := Exp.fix A S σ₀
    if hx : _ then pgcl {~⟨x, hx⟩ := ~q} else pgcl {skip}
  | pgcl {~C₁ ; ~C₂} => pgcl {~(C₁.fix S σ₀) ; ~(C₂.fix S σ₀)}
  | pgcl {{~C₁} [~p] {~C₂}} =>
    pgcl {{~(C₁.fix S σ₀)} [~(p.fix S σ₀)] {~(C₂.fix S σ₀)}}
  | pgcl {{~C₁} [] {~C₂}} => pgcl {{~(C₁.fix S σ₀)} [] {~(C₂.fix S σ₀)}}
  | pgcl {while ~b {~C'}} => pgcl {while ~(BExpr.fix b S σ₀) {~(C'.fix S σ₀)}}
  | pgcl {tick(~ r)} => pgcl {tick(~(Exp.fix r S σ₀))}
  | pgcl {observe(~ b)} => pgcl {observe(~(BExpr.fix b S σ₀))}

@[simp] theorem Exp.fix_apply {φ : 𝔼[ϖ, α]} : Exp.fix φ S σ₀ σ = φ (σ₀.cofix σ) := rfl

open scoped Classical in
@[grind =, simp]
theorem Exp.subst_fix [DecidableEq 𝒱] {φ : 𝔼[ϖ, α]} {x : 𝒱} {e : 𝔼[ϖ, ϖ x]} {S : Set 𝒱}
    (hx : x ∉ S) :
    Exp.fix φ[x ↦ e] S σ = (Exp.fix φ S σ)[⟨x, hx⟩ ↦ Exp.fix e S σ] := by
  ext σ'
  simp only [fix_apply, subst_apply]
  congr! with v
  ext
  grind [States.cofix]

example [DecidableEq 𝒱] {φ : 𝔼[ϖ, ENNReal]} {x : 𝒱} {σ₀ : States ϖ}
    {σ : States (𝒱:=↑({x} : Set 𝒱)ᶜᶜ) (ϖ ·)} :
    Exp.fix φ ({x}ᶜ : Set 𝒱) σ₀ σ = φ σ₀[x ↦ σ ⟨x, by simp⟩] := by
  simp only [Exp.fix_apply]
  congr
  ext y
  grind [States.cofix]

@[grind =, simp]
theorem Exp.zero_fix [DecidableEq 𝒱] : Exp.fix (0 : 𝔼[ϖ, ENNReal]) = 0 := rfl
@[grind =, simp]
theorem Exp.top_fix [DecidableEq 𝒱] : Exp.fix (⊤ : 𝔼[ϖ, ENNReal]) = ⊤ := rfl

@[simp]
theorem Exp.iSup_fix [DecidableEq 𝒱] {X : α → 𝔼[ϖ, ENNReal]} :
    Exp.fix (⨆ n, X n) S σ₀ σ = ⨆ n, Exp.fix (X n) S σ₀ σ := by simp [Exp.fix]
@[simp]
theorem Exp.iInf_fix [DecidableEq 𝒱] {X : α → 𝔼[ϖ, ENNReal]} :
    Exp.fix (⨅ n, X n) S σ₀ σ = ⨅ n, Exp.fix (X n) S σ₀ σ := by simp [Exp.fix]

theorem wp_le_of_fix [DecidableEq 𝒱] (C : pGCL ϖ) (φ : 𝔼[ϖ, ENNReal]) (S : Set 𝒱) (X : 𝔼[ϖ, ENNReal]) :
    Exp.fix (wp[O]⟦~C⟧ φ) S σ₀ ≤ Exp.fix X S σ₀ → wp[O]⟦~C⟧ φ σ₀ ≤ X σ₀ := by
  intro h
  replace h := h fun x ↦ σ₀ x
  simp_all
  convert h <;> ext <;> simp [States.cofix]

theorem le_wlp''_of_fix [DecidableEq 𝒱] (C : pGCL ϖ) (φ : 𝔼[ϖ, ENNReal]) (S : Set 𝒱) (X : 𝔼[ϖ, ENNReal]) :
    Exp.fix X S σ₀ ≤ Exp.fix (wlp''[O]⟦~C⟧ φ) S σ₀ → X σ₀ ≤ wlp''[O]⟦~C⟧ φ σ₀ := by
  intro h
  replace h := h fun x ↦ σ₀ x
  simp_all
  convert h <;> ext <;> simp [States.cofix]

theorem wp_fix [DecidableEq 𝒱] (C : pGCL ϖ) (φ : 𝔼[ϖ, ENNReal]) (S : Set 𝒱) (hS : C.mods ⊆ Sᶜ) :
    Exp.fix (wp[O]⟦~C⟧ φ) S σ₀ = wp[O]⟦~(C.fix S σ₀)⟧ (Exp.fix φ S σ₀) := by
  symm
  induction C generalizing φ with simp_all [fix, mods] <;> try rfl
  | nonDet => cases O <;> simp [Optimization.opt₂] <;> rfl
  | loop b C ih =>
    ext σ
    simp only [wp_loop_eq_iter, iSup_apply, Exp.fix_apply]
    congr with i
    induction i generalizing σ with
    | zero => simp only [Function.iterate_zero, id_eq, Pi.ofNat_apply]
    | succ i ih' =>
      simp only [Function.iterate_succ', Function.comp_apply]
      nth_rw 1 [Φ]
      nth_rw 2 [Φ]
      simp only [OrderHom.coe_mk, OrderHom.mk_apply, Pi.add_apply, Pi.mul_apply, BExpr.iver_apply,
        BExpr.not_apply]
      simp [Exp.fix] at ih' ⊢
      congr! 2
      classical
      rw [← Exp.ext_iff] at ih'
      rw [ih']
      exact congrFun (ih ((Φ[_] b φ)^[i] 0)) σ

theorem wlp''_fix [DecidableEq 𝒱] (C : pGCL ϖ) (φ : 𝔼[ϖ, ENNReal]) (S : Set 𝒱) (hS : C.mods ⊆ Sᶜ) :
    Exp.fix (wlp''[O]⟦~C⟧ φ) S σ₀ = wlp''[O]⟦~(C.fix S σ₀)⟧ (Exp.fix φ S σ₀) := by
  symm
  induction C generalizing φ with simp_all [fix, mods] <;> try rfl
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
      simp [States.cofix, hv]
  | seq C₁ C₂ ih₁ ih₂ =>
    ext
    simp [fix]
    specialize ih₁ (wlp''[O]⟦~C₂⟧ φ ⊓ 1)
    have : (Exp.fix (wlp''[O]⟦~C₂⟧ φ ⊓ 1) S σ₀) = (Exp.fix (wlp''[O]⟦~C₂⟧ φ) S σ₀) ⊓ 1 := by ext; simp
    simp [this] at ih₁
    simp [ih₁]
  | nonDet => cases O <;> simp [Optimization.opt₂] <;> rfl
  | loop b C ih =>
    ext σ
    simp only [wlp''_loop_eq_iter, iInf_apply, Exp.iInf_fix]
    simp
    congr with i
    induction i generalizing σ with
    | zero => simp only [Function.iterate_zero, id_eq, Pi.one_apply, Exp.fix_apply]
    | succ i ih' =>
      simp only [Function.iterate_succ', Function.comp_apply]
      nth_rw 1 [Φ]
      nth_rw 2 [Φ]
      simp only [OrderHom.coe_mk, OrderHom.mk_apply, Pi.add_apply, Pi.mul_apply, BExpr.iver_apply,
        BExpr.not_apply]
      simp [Exp.fix] at ih' ⊢
      congr! 2
      classical
      rw [← Exp.ext_iff] at ih'
      rw [ih']
      exact congrFun (ih ((Φ[_] b (φ ⊓ 1))^[i] 1)) σ

theorem wlp_fix_apply [DecidableEq 𝒱] (C : pGCL ϖ) (φ : ProbExp ϖ) (S : Set 𝒱) (hS : C.mods ⊆ Sᶜ) (σ) :
    Exp.fix (wlp[O]⟦~C⟧ φ) S σ₀ σ = wlp[O]⟦~(C.fix S σ₀)⟧ ⟨Exp.fix φ S σ₀, by intro; simp⟩ σ := by
  simp
  have := congrFun (C.wlp''_fix φ.val S hS (O:=O) (σ₀:=σ₀)) σ
  simp at this
  convert this
  · simp [wlp'']; congr; ext σ; have := φ.prop σ; simp_all only [Pi.one_apply,
    ProbExp.ofExp_apply, inf_of_le_left]; rfl
  · simp [wlp'']
    congr
    ext σ
    simp
    have := φ.prop (σ₀.cofix σ)
    simp_all
    rfl

/-- An _Idle invariant_ is _Park invariant_ that holds for states with a set of fixed variables. -/
def IdleInvariant [DecidableEq 𝒱] (g : 𝔼[ϖ, ENNReal] →o 𝔼[ϖ, ENNReal]) (b : BExpr ϖ) (φ : 𝔼[ϖ, ENNReal])
    (I : 𝔼[ϖ, ENNReal]) (S : Set 𝒱) (σ₀ : States ϖ) : Prop :=
  ∀ σ, (∀ v ∈ S, σ v = σ₀ v) → Φ[g] b φ I σ ≤ I σ

/-- _Idle induction_ is _Park induction_, but the engine is running (i.e. an initial state is
given), and as a consequence only states that vary over the modified variables need to be
considered for the inductive invariant. -/
theorem IdleInduction [DecidableEq 𝒱] {b : BExpr ϖ} {C : pGCL ϖ} {φ : 𝔼[ϖ, ENNReal]} {I : 𝔼[ϖ, ENNReal]}
    {σ₀ : States ϖ} (h : IdleInvariant wp[O]⟦~C⟧ b φ I C.modsᶜ σ₀) :
    wp[O]⟦while ~b { ~C }⟧ φ σ₀ ≤ I σ₀ := by
  apply wp_le_of_fix (S:=C.modsᶜ)
  rw [wp_fix _ _ _ (by simp; rfl)]
  apply OrderHom.lfp_le
  intro σ'
  simp only [Φ, OrderHom.coe_mk, OrderHom.mk_apply, Pi.add_apply, Pi.mul_apply, BExpr.iver_apply,
    BExpr.fix_apply, BExpr.not_apply, Exp.fix_apply]
  simp [IdleInvariant, Φ] at h
  rw [← wp_fix _ _ _ (by simp)]
  convert h (σ₀.cofix σ') ?_
  simp +contextual

/-- An _Idle coinvariant_ is _Park coinvariant_ that holds for states with a set of fixed variables.
-/
def IdleCoinvariant [DecidableEq 𝒱] (g : 𝔼[ϖ, ENNReal] →o 𝔼[ϖ, ENNReal]) (b : BExpr ϖ) (φ : 𝔼[ϖ, ENNReal])
    (I : 𝔼[ϖ, ENNReal]) (S : Set 𝒱) (σ₀ : States ϖ) : Prop :=
  ∀ σ, (∀ v ∈ S, σ v = σ₀ v) → I σ ≤ Φ[g] b φ I σ

theorem OrderHom.le_gfp_prob {x : 𝔼[ϖ, ENNReal]} {f : ProbExp ϖ →o ProbExp ϖ}
    (h₁ : x ≤ 1)
    (h₂ : x ≤ f ⟨x, h₁⟩):
    x ≤ OrderHom.gfp f := by
  suffices ⟨x, h₁⟩ ≤ OrderHom.gfp f by exact this
  apply OrderHom.le_gfp _ h₂

theorem wlp_apply_eq_wlp''_apply [DecidableEq 𝒱] {C : pGCL ϖ} :
    wlp[O]⟦~C⟧ X σ = wlp''[O]⟦~C⟧ X σ := by
  simp [wlp'']
  congr; ext; simp

/-- _Idle coinduction_ is _Park coinduction_, but the engine is running (i.e. an initial state is
given), and as a consequence only states that vary over the modified variables need to be
considered for the coinductive invariant. -/
theorem IdleCoinduction [DecidableEq 𝒱] {b : BExpr ϖ} {C : pGCL ϖ} {φ : 𝔼[ϖ, ENNReal]} {I : 𝔼[ϖ, ENNReal]}
    {σ₀ : States ϖ} (h : IdleCoinvariant wlp''[O]⟦~C⟧ b φ I C.modsᶜ σ₀) (hI : I ≤ 1) (hφ : φ ≤ 1) :
    I σ₀ ≤ wlp''[O]⟦while ~b { ~C }⟧ φ σ₀ := by
  apply le_wlp''_of_fix (S:=C.modsᶜ)
  rw [wlp''_fix _ _ _ (by simp; rfl)]
  simp [fix]
  rw [wlp''_loop_eq_gfp]
  fapply OrderHom.le_gfp_prob
  · exact fun i ↦ hI (σ₀.cofix i)
  intro σ'
  simp only [Exp.fix_apply, pΦ, OrderHom.coe_mk, ProbExp.pickProb_apply, ProbExp.pick,
    Pi.add_apply, Pi.mul_apply, BExpr.probOf_apply, BExpr.fix_apply, wlp_apply_eq_wlp''_apply,
    ProbExp.mk_vcoe, Pi.sub_apply, Pi.one_apply, ProbExp.ofExp_apply]
  simp [IdleCoinvariant, Φ] at h
  rw [← wlp''_fix _ _ _ (by simp)]
  convert h (σ₀.cofix σ') ?_
  · simp [Iverson.iver]; split <;> simp
  · simp; exact hφ _
  · simp +contextual

end pGCL
