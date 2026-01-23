import PGCL.WeakestLiberalPre

open Optimization.Notation

namespace pGCL

@[gcongr]
def Exp.substs_mono [DecidableEq ϖ] {X₁ X₂ : Exp ϖ} {xs : List ((_ : ϖ) × Exp ϖ)} (h : X₁ ≤ X₂) :
    X₁[..xs] ≤ X₂[..xs] := by
  induction xs generalizing X₁ X₂ with
  | nil => simp [h]
  | cons x xs ih => apply fun σ ↦ ih h _

@[gcongr]
theorem Exp.hcoimp_mono {a₁ a₂ b₁ b₂ : Exp ϖ} (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) :
    a₁ ↜ b₁ ≤ a₂ ↜ b₂ := by
  intro σ
  specialize ha σ
  specialize hb σ
  simp [Exp.hcoimp_apply, instHCoImpENNReal]
  split_ifs <;> try grind
  simp_all

@[gcongr]
theorem Exp.himp_mono {a₁ a₂ b₁ b₂ : Exp ϖ} (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) :
    a₁ ⇨ b₁ ≤ a₂ ⇨ b₂ := by
  intro σ
  specialize ha σ
  specialize hb σ
  simp [himp]
  split_ifs <;> try grind
  · simp_all

@[gcongr]
theorem Exp.hnot_mono {a₁ a₂ : Exp ϖ} (ha : a₂ ≤ a₁) :
    ￢ a₁ ≤ ￢ a₂ := by
  intro σ
  specialize ha σ
  simp [hnot]
  split_ifs <;> simp_all
@[gcongr]
theorem Exp.hconot_mono {a₁ a₂ : Exp ϖ} (ha : a₂ ≤ a₁) :
    ~ a₁ ≤ ~ a₂ := by
  show a₁ ⇨ 0 ≤ a₂ ⇨ 0
  gcongr
@[gcongr]
theorem Exp.validate_mono {a₁ a₂ : Exp ϖ} (ha : a₁ ≤ a₂) :
    ▵ a₁ ≤ ▵ a₂ := by
  show ￢￢ a₁ ≤ ￢￢ a₂
  gcongr
@[gcongr]
theorem Exp.covalidate_mono {a₁ a₂ : Exp ϖ} (ha : a₁ ≤ a₂) :
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
theorem Exp.zero_himp {a : Exp ϖ} :
    (0 ⇨ a) = ⊤ := by simp [himp]; rfl

@[grind =, simp]
theorem BExpr.subst_single_apply [DecidableEq ϖ] {b : BExpr ϖ} :
    b[x ↦ v] σ = b σ[x ↦ v σ] := by
  rfl
@[grind =]
theorem States.subst_comm [DecidableEq ϖ] {σ : States ϖ} {x₁ x₂ : ϖ} {v₁ v₂} (h : x₁ ≠ x₂) :
    σ[x₁ ↦ v₁][x₂ ↦ v₂] = σ[x₂ ↦ v₂][x₁ ↦ v₁] := by ext; grind

namespace Exp

variable {ϖ : Type*} [DecidableEq ϖ] {a b : Exp ϖ} {p : BExpr ϖ} (xs : List ((_ : ϖ) × Exp ϖ))

@[simp] theorem top_subst :
    (⊤ : Exp ϖ)[..xs] = (⊤ : Exp ϖ) := by
  induction xs with try simp
  | cons x xs ih =>
    simp [Substitution.substs_cons, Substitution.subst, ih]
    rfl

@[simp] theorem iver_subst :
    i[p][..xs] = i[(p)[..xs]] := by
  induction xs generalizing p with try simp
  | cons x xs ih =>
    simp only [Substitution.substs_cons, Substitution.subst, Substitution.substs_nil, ih, id_eq]
    rfl
@[simp] theorem not_subst :
    (p.not)[..xs] = (p)[..xs].not := by
  induction xs generalizing p with try simp
  | cons x xs ih =>
    simp only [Substitution.substs_cons, Substitution.subst, Substitution.substs_nil, id_eq]
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

@[simp] theorem BExpr.eq_self {a : Exp ϖ} : BExpr.eq a a = true := by ext; simp; rfl
@[simp] theorem BExpr.eq_of_ne {a b : Exp ϖ} (h : ∀ σ, a σ ≠ b σ) : BExpr.eq a b = false := by
  ext; simp_all; exact of_decide_eq_false rfl
@[simp] theorem BExpr.iver_coe_bool :
    i[BExpr.coe_bool (ϖ:=ϖ) a] = i[a] := by
  ext
  simp [BExpr.coe_bool, DFunLike.coe, Iverson.iver]
@[simp] theorem BExpr.not_coe_bool :
    BExpr.not (ϖ:=ϖ) (BExpr.coe_bool a) = BExpr.coe_bool ¬a := by
  ext
  simp [BExpr.not, BExpr.coe_bool, DFunLike.coe]

open scoped Classical in
noncomputable
def Exp.fix (X : Exp ϖ) (S : Set ϖ) (σ₀ : States ϖ) : Exp ↑Sᶜ :=
  fun σ ↦ X fun v ↦ if h : v ∈ S then σ₀ v else σ ⟨v, h⟩

@[grind =, simp]
theorem Exp.fix_empty (φ : Exp ϖ) : φ.fix ∅ σ₀ σ = φ (σ ⟨·, id⟩) := by
  simp [fix]
@[grind =, simp]
theorem Exp.fix_compl_empty (φ : Exp ϖ) : φ.fix ∅ᶜ σ₀ σ = φ σ₀ := by
  simp [fix]
@[grind ., simp]
theorem Exp.fix_compl_empty_eq (φ ψ : Exp ϖ) : φ.fix ∅ᶜ = ψ.fix ∅ᶜ ↔ φ = ψ := by
  constructor
  · intro h
    ext σ₀
    replace h := congrFun₂ h σ₀ (σ₀ ·)
    grind
  · grind

open scoped Classical in
noncomputable
def States.cofix (σ₀ : States ϖ) (S : Set ϖ) (σ : States ↑Sᶜ) : States ϖ :=
  fun v ↦ if h : v ∈ S then σ₀ v else σ ⟨v, h⟩

open scoped Classical in
noncomputable
def BExpr.fix (X : BExpr ϖ) (S : Set ϖ) (σ₀ : States ϖ) : BExpr ↑Sᶜ :=
  ⟨fun σ ↦ X fun v ↦ if h : v ∈ S then σ₀ v else σ ⟨v, h⟩, instDecidablePredComp⟩
  -- ⟨X ∘ States.cofix σ₀ S, instDecidablePredComp⟩

open scoped Classical in
theorem BExpr.fix_apply (X : BExpr ϖ) (S : Set ϖ) (σ₀ : States ϖ) (σ : States ↑Sᶜ) :
    (X.fix S σ₀) σ = X fun v ↦ if h : v ∈ S then σ₀ v else σ ⟨v, h⟩ := rfl

open scoped Classical in
noncomputable
def ProbExp.fix (X : ProbExp ϖ) (S : Set ϖ) (σ₀ : States ϖ) : ProbExp ↑Sᶜ :=
  ⟨fun σ ↦ X fun v ↦ if h : v ∈ S then σ₀ v else σ ⟨v, h⟩, by intro σ; simp⟩

@[gcongr]
theorem Exp.ennreal_coe_le (h : a ≤ b) :
    pGCL.Exp.ennreal_coe (ϖ:=ϖ) a ≤ pGCL.Exp.ennreal_coe b := by
  intro; grind

@[grind]
def mods : pGCL ϖ → Set ϖ
  | pgcl {skip} => ∅
  | pgcl {~x := ~_} => {x}
  | pgcl {~C₁ ; ~C₂} => C₁.mods ∪ C₂.mods
  | pgcl {{~C₁} [~_] {~C₂}} => C₁.mods ∪ C₂.mods
  | pgcl {{~C₁} [] {~C₂}} => C₁.mods ∪ C₂.mods
  | pgcl {while ~_ {~C'}} => C'.mods
  | pgcl {tick(~ _)} => ∅
  | pgcl {observe(~ _)} => ∅

open scoped Classical in
noncomputable def fix (C : pGCL ϖ) (S : Set ϖ) (σ₀ : States ϖ) : pGCL ↑Sᶜ :=
  match C with
  | pgcl {skip} => pgcl {skip}
  | pgcl {~x := ~A} =>
    if hx : _ then pgcl {~⟨x, hx⟩ := ~(Exp.fix A S σ₀)} else pgcl {skip}
  | pgcl {~C₁ ; ~C₂} => pgcl {~(C₁.fix S σ₀) ; ~(C₂.fix S σ₀)}
  | pgcl {{~C₁} [~p] {~C₂}} =>
    pgcl {{~(C₁.fix S σ₀)} [~(ProbExp.fix p S σ₀)] {~(C₂.fix S σ₀)}}
  | pgcl {{~C₁} [] {~C₂}} => pgcl {{~(C₁.fix S σ₀)} [] {~(C₂.fix S σ₀)}}
  | pgcl {while ~b {~C'}} => pgcl {while ~(BExpr.fix b S σ₀) {~(C'.fix S σ₀)}}
  | pgcl {tick(~ r)} => pgcl {tick(~(Exp.fix r S σ₀))}
  | pgcl {observe(~ b)} => pgcl {observe(~(BExpr.fix b S σ₀))}

theorem wp_le_of_fix [DecidableEq ϖ] (C : pGCL ϖ) (φ : Exp ϖ) (S : Set ϖ) :
    Exp.fix (wp[O]⟦~C⟧ φ) S σ₀ ≤ Exp.fix X S σ₀ → wp[O]⟦~C⟧ φ σ₀ ≤ X σ₀ := by
  intro h
  replace h := h fun x ↦ σ₀ x
  simp_all [Exp.fix]

theorem le_wlp''_of_fix [DecidableEq ϖ] (C : pGCL ϖ) (φ : Exp ϖ) (S : Set ϖ) :
    Exp.fix X S σ₀ ≤ Exp.fix (wlp''[O]⟦~C⟧ φ) S σ₀ → X σ₀ ≤ wlp''[O]⟦~C⟧ φ σ₀ := by
  intro h
  replace h := h fun x ↦ σ₀ x
  simp_all [Exp.fix]

theorem wp_fix [DecidableEq ϖ] (C : pGCL ϖ) (φ : Exp ϖ) (S : Set ϖ) (hS : C.mods ⊆ Sᶜ) :
    Exp.fix (wp[O]⟦~C⟧ φ) S σ₀ = wp[O]⟦~(C.fix S σ₀)⟧ (φ.fix S σ₀) := by
  symm
  induction C generalizing φ with simp_all [fix, mods] <;> try rfl
  | nonDet => cases O <;> simp [Optimization.opt₂] <;> rfl
  | assign x e =>
    ext σ'
    simp only [Exp.fix, Exp.subst_apply, States.subst_apply, Subtype.mk.injEq]
    congr! with y
    grind
  | loop b C ih =>
    ext σ
    simp only [wp_loop_eq_iter, iSup_apply, Exp.fix]
    congr with i
    induction i generalizing σ with
    | zero => simp only [Function.iterate_zero, id_eq, Pi.zero_apply]
    | succ i ih' =>
      simp only [Function.iterate_succ', Function.comp_apply]
      nth_rw 1 [Φ]
      nth_rw 2 [Φ]
      simp only [OrderHom.coe_mk, OrderHom.mk_apply, Pi.add_apply, Pi.mul_apply, BExpr.iver_apply,
        BExpr.not_apply]
      congr! 2
      classical
      rw [← Exp.ext_iff] at ih'
      rw [ih']
      exact congrFun (ih ((Φ[_] b φ)^[i] 0)) σ

theorem wlp''_fix [DecidableEq ϖ] (C : pGCL ϖ) (φ : Exp ϖ) (S : Set ϖ) (hS : C.mods ⊆ Sᶜ) :
    Exp.fix (wlp''[O]⟦~C⟧ φ) S σ₀ = wlp''[O]⟦~(C.fix S σ₀)⟧ (φ.fix S σ₀) := by
  symm
  induction C generalizing φ with simp_all [fix, mods] <;> try rfl
  | nonDet => cases O <;> simp [Optimization.opt₂] <;> rfl
  | assign x e =>
    ext σ'
    simp only [Exp.fix, Exp.subst_apply, States.subst_apply, Subtype.mk.injEq]
    congr! with y
    grind
  | loop b C ih =>
    ext σ
    simp only [wlp''_loop_eq_iter, iInf_apply, Exp.fix]
    congr with i
    induction i generalizing σ with
    | zero => simp only [Function.iterate_zero, id_eq, Pi.top_apply]
    | succ i ih' =>
      simp only [Function.iterate_succ', Function.comp_apply]
      nth_rw 1 [Φ_eq_pick]
      nth_rw 1 [Φ_eq_pick]
      simp [ProbExp.pick]
      congr! 2
      classical
      rw [← Exp.ext_iff] at ih'
      rw [ih']
      exact congrFun (ih ((Φ[_] b φ)^[i] ⊤)) σ

/-- An _Idle invariant_ is _Park invariant_ that holds for states with a set of fixed variables. -/
def IdleInvariant [DecidableEq ϖ] (g : Exp ϖ →o Exp ϖ) (b : BExpr ϖ) (φ : Exp ϖ)
    (I : Exp ϖ) (S : Set ϖ) (σ₀ : States ϖ) : Prop :=
  ∀ σ, (∀ v ∈ S, σ v = σ₀ v) → Φ[g] b φ I σ ≤ I σ

/-- _Idle induction_ is _Park induction_, but the engine is running (i.e. an initial state is
given), and as a consequence only states that vary over the modified variables need to be
considered for the inductive invariant. -/
theorem IdleInduction [DecidableEq ϖ] {b : BExpr ϖ} {C : pGCL ϖ} {φ : Exp ϖ} {I : Exp ϖ}
    {σ₀ : States ϖ} (h : IdleInvariant wp[O]⟦~C⟧ b φ I C.modsᶜ σ₀) :
    wp[O]⟦while ~b { ~C }⟧ φ σ₀ ≤ I σ₀ := by
  apply wp_le_of_fix (S:=C.modsᶜ)
  rw [wp_fix _ _ _ (by simp; rfl)]
  apply OrderHom.lfp_le
  simp [IdleInvariant, Φ] at h
  intro σ'
  simp only [OrderHom.mk_apply, Pi.add_apply, Pi.mul_apply]
  classical
  let σ₁' : States ϖ := States.cofix σ₀ _ σ'
  let σ₁ : States ϖ := fun v ↦ if h : v ∈ C.mods then σ' ⟨v, by grind⟩ else σ₀ v
  have : σ₁ = σ₁' := by ext; simp [σ₁, σ₁', States.cofix]
  have : (∀ v ∉ C.mods, σ₁ v = σ₀ v) := by simp +contextual [σ₁]
  convert h σ₁ this
  · simp [σ₁, BExpr.fix_apply]
  · rw [← wp_fix _ _ _ (by simp)]
    simp [Exp.fix, σ₁]
  · simp [σ₁, BExpr.fix_apply]
  · simp [Exp.fix, σ₁]
  · simp [Exp.fix, σ₁]

/-- An _Idle coinvariant_ is _Park coinvariant_ that holds for states with a set of fixed variables.
-/
def IdleCoinvariant [DecidableEq ϖ] (g : Exp ϖ →o Exp ϖ) (b : BExpr ϖ) (φ : Exp ϖ)
    (I : Exp ϖ) (S : Set ϖ) (σ₀ : States ϖ) : Prop :=
  ∀ σ, (∀ v ∈ S, σ v = σ₀ v) → I σ ≤ Φ[g] b φ I σ

/-- _Idle coinduction_ is _Park coinduction_, but the engine is running (i.e. an initial state is
given), and as a consequence only states that vary over the modified variables need to be
considered for the coinductive invariant. -/
theorem IdleCoinduction [DecidableEq ϖ] {b : BExpr ϖ} {C : pGCL ϖ} {φ : Exp ϖ} {I : Exp ϖ}
    {σ₀ : States ϖ} (h : IdleCoinvariant wlp''[O]⟦~C⟧  b φ I C.modsᶜ σ₀) :
    I σ₀ ≤ wlp''[O]⟦while ~b { ~C }⟧ φ σ₀ := by
  apply le_wlp''_of_fix (S:=C.modsᶜ)
  rw [wlp''_fix _ _ _ (by simp; rfl)]
  apply OrderHom.le_gfp
  simp [IdleCoinvariant, Φ] at h
  intro σ'
  classical
  let σ₁ : States ϖ := fun v ↦ if h : v ∈ C.mods then σ' ⟨v, by grind⟩ else σ₀ v
  have : (∀ v ∉ C.mods, σ₁ v = σ₀ v) := by simp +contextual [σ₁]
  convert h σ₁ this
  · simp [Exp.fix, σ₁]
  · simp only [Φ, OrderHom.coe_mk, OrderHom.mk_apply, Pi.add_apply, Pi.mul_apply, BExpr.iver_apply,
    BExpr.fix_apply, Set.mem_compl_iff, dite_not, BExpr.not_apply, σ₁]
    congr! 2
    · rw [← wlp''_fix _ _ _ (by simp)]
      simp [Exp.fix]
    · simp only [Exp.fix, Set.mem_compl_iff, dite_not]

end pGCL
