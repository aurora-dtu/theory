import HeyLo.Expr
import Mathlib.Data.Finset.Sort
import Mathlib.Data.NNRat.Lemmas
import PGCL.OperationalSemantics

attribute [grind =] Finset.empty_union

open pGCL
open Optimization.Notation

open HeyLo

def HeyLo.not (x : 𝔼b) : 𝔼b := .Unary .Not x
def HeyLo.iver (x : 𝔼b) : 𝔼r := .Unary .Iverson x
def HeyLo.embed (x : 𝔼b) : 𝔼r := .Unary .Embed x
def HeyLo.coembed (x : 𝔼b) : 𝔼r := .Unary .Embed x.not

section
variable {A B : 𝔼r}
variable {x : Ident} {P : 𝔼b}

@[grind =, simp]
theorem HeyLo.sem_zero : (0 : 𝔼r).sem = 0 := by
  simp [sem]
@[grind =, simp]
theorem HeyLo.sem_one : (1 : 𝔼r).sem = 1 := by
  simp [sem]
@[grind =, simp]
theorem HeyLo.sem_var : (HeyLo.Var x).sem σ = σ x := rfl
@[grind =, simp]
theorem HeyLo.sem_binop : (HeyLo.Binary op A B).sem = op.sem A.sem B.sem := rfl
@[grind =, simp]
theorem HeyLo.sem_unop : (HeyLo.Unary op A).sem = op.sem A.sem := rfl
@[grind =, simp]
theorem HeyLo.sem_add_apply : (A + B).sem = A.sem + B.sem := rfl
@[grind =, simp]
theorem HeyLo.sem_sub_apply : (A - B).sem = A.sem - B.sem := rfl
@[grind =, simp]
theorem HeyLo.sem_mul_apply : (A * B).sem = A.sem * B.sem := rfl
@[grind =, simp]
theorem HeyLo.sem_inf_apply : (A ⊓ B).sem = A.sem ⊓ B.sem := rfl
@[grind =, simp]
theorem HeyLo.sem_sup_apply : (A ⊔ B).sem = A.sem ⊔ B.sem := rfl
@[grind =, simp]
theorem HeyLo.sem_lit_apply : (HeyLo.Lit l).sem = l.sem := rfl
@[grind =, simp]
theorem HeyLo.sem_validate : (▵ A).sem = ▵ A.sem := rfl
@[grind =, simp]
theorem HeyLo.sem_covalidate : (▿ A).sem = ▿ A.sem := rfl
@[grind =, simp]
theorem HeyLo.sem_hnot_apply : (￢A).sem = ￢A.sem := rfl
@[grind =, simp]
theorem HeyLo.sem_hconot : (~A).sem = ~A.sem := rfl
@[grind =, simp]
theorem HeyLo.sem_himp_apply : (A ⇨ B).sem = A.sem ⇨ B.sem := rfl
@[grind =, simp]
theorem HeyLo.sem_hcoimp_apply : (A ↜ B).sem = A.sem ↜ B.sem := rfl

open Substitution in
@[grind =, simp]
theorem HeyLo.sem_subst_apply' : A[..xs].sem = A.sem[..xs.map (fun (a, b) ↦ (a, b.sem))] := by
  induction xs generalizing A with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨x, v⟩ := x
    simp_all
    calc
      (Substitution.subst (substs A xs) (x, v)).sem =
          Substitution.subst (substs A xs).sem (x, v.sem) :=
        by
          clear ih
          ext σ
          simp [Substitution.subst, subst, sem]
      _ =
          Substitution.subst (substs A.sem (List.map (fun x ↦ (x.1, x.2.sem)) xs)) (x, v.sem) :=
        by simp_all
@[grind =, simp]
theorem HeyLo.sem_subst_apply : P[x ↦ B].sem σ = P.sem σ[x ↦ B.sem σ] := rfl
@[grind =, simp]
theorem HeyLo.sem_iver : P.iver.sem = i[P.sem] := rfl
@[grind =, simp]
theorem HeyLo.sem_embed : P.embed.sem = i[P.sem] * ⊤ := rfl
@[grind =, simp]
theorem HeyLo.sem_not_apply : P.not.sem = P.sem.not := rfl
@[grind =, simp]
theorem HeyLo.sem_eq : (HeyLo.Binary .Eq A B).sem = BExpr.eq A.sem B.sem := rfl

@[grind =, simp]
theorem HeyLo.sem_subt_var : (HeyLo.Var x).sem[x ↦ v] = v := by
  simp [sem, Substitution.substs, Substitution.subst]

@[grind =, simp]
theorem HeyLo.substs_inf : (A ⊓ B).sem[..xs] = A.sem[..xs] ⊓ B.sem[..xs] :=
  Substitution.substs_of_binary fun _ _ ↦ congrFun rfl

end

inductive pGCL' where
  | skip : pGCL'
  | assign : Ident → 𝔼r → pGCL'
  | seq : pGCL' → pGCL' → pGCL'
  | prob : pGCL' → {p : NNRat // p ≤ 1} → pGCL' → pGCL'
  | nonDet : pGCL' → pGCL' → pGCL'
  | loop : 𝔼b → 𝔼r → pGCL' → pGCL'
  | tick : 𝔼r → pGCL'
  | observe : 𝔼b → pGCL'
deriving Inhabited

noncomputable def pGCL'.pGCL (C : pGCL') : pGCL Ident :=
  match C with
  | skip => .skip
  | assign x e => .assign x e.sem
  | seq C₁ C₂ => .seq C₁.pGCL C₂.pGCL
  | prob C₁ p C₂ =>
    .prob C₁.pGCL ⟨fun _ ↦ p, by
      intro; obtain ⟨p, hp⟩ := p
      simp_all [ENNReal.instNNRatCast, NNRat.cast]⟩ C₂.pGCL
  | nonDet C₁ C₂ => .nonDet C₁.pGCL C₂.pGCL
  | loop b I C => .loop b.sem C.pGCL
  | tick r => .tick r.sem
  | observe r => .observe r.sem

infixr:50 " ;; " => HeyVL.Seq

def HeyVL.Skip : HeyVL := .Reward 0
def HeyVL.If (b : 𝔼b) (S₁ S₂ : HeyVL) : HeyVL :=
  .IfInf (.Assume b.embed ;; S₁) (.Assume b.not.embed ;; S₂)
def HeyVL.Havocs (xs : List Ident) : HeyVL :=
  match xs with
  | [] => .Skip
  | [x] => .Havoc x
  | x::xs => .Havoc x ;; .Havocs xs
def HeyVL.Cohavocs (xs : List Ident) : HeyVL :=
  match xs with
  | [] => .Skip
  | [x] => .Cohavoc x
  | x::xs => .Cohavoc x ;; .Cohavocs xs

abbrev Globals := Finset Ident

def Globals.toList (G : Globals) : List Ident := (Finset.val G).sort
@[grind ., simp] theorem Globals.toList_Nodup (G : Globals) : G.toList.Nodup := by simp [toList]

instance : Union Globals := inferInstanceAs (Union (Finset Ident))
instance : Singleton Ident Globals := inferInstanceAs (Singleton Ident (Finset Ident))
instance : Membership Ident Globals := inferInstanceAs (Membership Ident (Finset Ident))
instance : HasSubset Globals := inferInstanceAs (HasSubset (Finset Ident))
instance : IsTrans Globals (· ⊆ ·) := inferInstanceAs (IsTrans (Finset Ident) (· ⊆ ·))
instance : IsRefl Globals (· ⊆ ·) := inferInstanceAs (IsRefl (Finset Ident) (· ⊆ ·))

@[grind ., simp] theorem Globals.mem_toList (G : Globals) : x ∈ G.toList ↔ x ∈ G := by simp [toList]

def Globals.fresh (G : Globals) : Globals × Ident :=
  let seen : Finset Ident := G
  if h : seen = ∅ then
    let new : Ident := Ident.mk "f₀"
    (({new} : Finset Ident), new)
  else
    let longest := seen.image (·.name.length) |>.max' (by simp [Finset.nonempty_iff_ne_empty, h])
    let new : Ident := Ident.mk ("f" ++ String.replicate longest '₀')
    (seen ∪ {new}, new)

@[grind ., simp]
theorem Globals.fresh_in {G : Globals} : G.fresh.2 ∈ G.fresh.1 := by
  simp [fresh]
  split_ifs
  · simp
  · simp_all
@[grind ., simp]
theorem Globals.fresh_not_in {G : Globals} : G.fresh.2 ∉ G := by
  simp [fresh]
  split_ifs
  · subst_eqs
    simp
  · simp
    have : ∀ (F : Finset Ident) (x : Ident), x ∉ F ↔ ∀ y ∈ F, x ≠ y :=
      fun F x ↦ Iff.symm Finset.forall_mem_not_eq
    apply (this _ _).mpr; clear this
    intro y hy
    have : ∀ {x y : Ident}, x ≠ y ↔ x.name ≠ y.name := by simp; grind
    apply this.mpr; clear this
    simp
    have : ∀ {x y : String}, x.length ≠ y.length → x ≠ y := by grind
    apply this; clear this
    have : "f".length = 1 := rfl
    simp_all
    simp [String.replicate]
    apply ne_of_gt
    apply Nat.lt_one_add_iff.mpr
    apply Finset.le_max'
    simp
    use y
@[grind ., simp]
theorem Globals.fresh_mono {G : Globals} : G ⊆ G.fresh.1 := by
  simp [fresh]
  split_ifs
  · subst_eqs; apply Finset.empty_subset
  · simp
@[grind =, simp]
theorem Globals.fresh_unique {G : Globals} {a} : a ∈ G.fresh.1 ∧ a ∉ G ↔ a = G.fresh.2 := by
  simp [fresh]
  split_ifs with h
  · subst_eqs
    simp
  · simp_all
    constructor
    · grind
    · rintro ⟨_⟩
      simp
      have := G.fresh_not_in
      simpa [fresh, h]

@[grind =, simp]
theorem Globals.toList_toFinset (G : Globals) : G.toList.toFinset = G := by ext; simp

@[grind]
def HeyLo.fv (C : HeyLo α) : Globals :=
  match C with
  | .Binary _ S₁ S₂ => S₁.fv ∪ S₂.fv
  | .Lit _ => ∅
  | .Subst v e m => {v} ∪ e.fv ∪ m.fv
  -- NOTE: we need to include `x` for complete-substitution purposes
  | .Quant _ x m => {x} ∪ m.fv
  | .Ite b l r => b.fv ∪ l.fv ∪ r.fv
  | .Var x => {x}
  | .Unary _ m => m.fv
def Distribution.fv (D : Distribution) : Globals :=
  D.values.toList.toFinset.biUnion (·.2.fv)
@[grind]
def pGCL'.fv (C : pGCL') : Globals :=
  match C with
  | .seq S₁ S₂ => S₁.fv ∪ S₂.fv
  | .skip => ∅
  | .observe o => o.fv
  | .tick r => r.fv
  | .loop b c I => b.fv ∪ c.fv ∪ I.fv
  | .nonDet S₁ S₂ => S₁.fv ∪ S₂.fv
  | .prob S₁ _ S₂ => S₁.fv ∪ S₂.fv
  | .assign x e => {x} ∪ e.fv
@[grind]
def HeyVL.fv (C : HeyVL) : Globals :=
  match C with
  | .Seq S₁ S₂ => S₁.fv ∪ S₂.fv
  | .Covalidate => ∅
  | .Cohavoc x => {x}
  | .Coassume x => x.fv
  | .Coassert x => x.fv
  | .IfSup l r => l.fv ∪ r.fv
  | .Validate => ∅
  | .Havoc x => {x}
  | .Assume x => x.fv
  | .Assert x => x.fv
  | .IfInf l r => l.fv ∪ r.fv
  | .Reward x => x.fv
  | .Assign x e => {x} ∪ e.fv

@[grind]
def pGCL'.mods (C : pGCL') : Globals :=
  match C with
  | .seq S₁ S₂ => S₁.mods ∪ S₂.mods
  | .skip => ∅
  | .observe _ => ∅
  | .tick _ => ∅
  | .loop _ _ c => c.mods
  | .nonDet S₁ S₂ => S₁.mods ∪ S₂.mods
  | .prob S₁ _ S₂ => S₁.mods ∪ S₂.mods
  | .assign x _ => {x}
@[grind]
def HeyVL.mods (C : HeyVL) : Globals :=
  match C with
  | .Seq S₁ S₂ => S₁.mods ∪ S₂.mods
  | .IfSup l r => l.mods ∪ r.mods
  | .IfInf l r => l.mods ∪ r.mods
  | .Assign x _ => {x}
  | .Covalidate
  | .Cohavoc _
  | .Coassume _
  | .Coassert _
  | .Validate
  | .Havoc _
  | .Assume _
  | .Assert _
  | .Reward _ => ∅

@[grind ., simp]
theorem HeyVL.mods_subset_fv (C : HeyVL) : C.mods ⊆ C.fv := by
  fun_induction mods <;> grind

@[grind =, simp]
theorem HeyVL.Skip_fv : HeyVL.Skip.fv = {} := rfl
@[grind =, simp]
theorem HeyVL.Havocs_fv : (HeyVL.Havocs xs).fv = xs.toFinset := by
  fun_induction Havocs with simp_all [fv]
@[grind =, simp]
theorem HeyVL.Cohavocs_fv : (HeyVL.Cohavocs xs).fv = xs.toFinset := by
  fun_induction Cohavocs with simp_all [fv]
@[grind =, simp]
theorem HeyLo.subst_fv (φ : HeyLo α) (y : 𝔼r) : φ[x ↦ y].fv = {x} ∪ φ.fv ∪ y.fv := by
  simp only [Substitution.subst_singleton, Substitution.subst, subst, HeyLo.fv,
    Finset.singleton_union, Finset.insert_union]
  grind

inductive Direction where
  /-- Corresponds to `gfp` -/
  | Upper
  /-- Corresponds to `lfp` -/
  | Lower

def pGCL'.HeyVL (C : pGCL') (O : Optimization) (D : Direction) (G : Globals) :
    Globals × HeyVL :=
  match C with
  | skip => (G, .Skip)
  | assign x e => (G, .Assign x (.pure e))
  | seq C₁ C₂ =>
    let (G, C₂) := C₂.HeyVL O D G
    let (G, C₁) := C₁.HeyVL O D G
    (G, C₁ ;; C₂)
  | prob C₁ p C₂ =>
    let (G, C₂) := C₂.HeyVL O D G
    let (G, C₁) := C₁.HeyVL O D G
    let (G, tmp) := G.fresh
    (G, .Assign tmp (.bin 0 p 1 p.prop) ;; .If (.Binary .Eq (.Var tmp) 0) C₁ C₂)
  | nonDet C₁ C₂ =>
    let (G, C₂) := C₂.HeyVL O D G
    let (G, C₁) := C₁.HeyVL O D G
    match O with
    | 𝒜 => (G, .IfSup C₁ C₂)
    | 𝒟 => (G, .IfInf C₁ C₂)
  | loop b I C =>
    let (G, C) := C.HeyVL O D G ;
    match D with
    -- NOTE: wp encoding
    | .Lower =>
      (G,
        .Coassert I ;;
        .Cohavocs C.mods.toList ;;
        .Covalidate ;;
        .Coassume I ;;
        .If b (
          C ;;
          .Coassert I ;;
          .Coassume ⊤
        ) (
          .Skip
        ))
    -- NOTE: wlp encoding
    | .Upper =>
      (G,
        .Assert I ;;
        .Havocs C.mods.toList ;;
        .Validate ;;
        .Assume I ;;
        .If b (
          C ;;
          .Assert I ;;
          .Assume 0
        ) (
          .Skip
        ))
  | tick r =>
    match D with
    -- NOTE: wp encoding
    | .Lower => (G, .Reward r)
    -- NOTE: wlp encoding
    | .Upper =>
      -- HACK: we include `r` as a subexpression such that `fv` is the same in both cases
      (G, .Reward (.Binary .Sub r r))
  | observe r => (G, .Assert r.embed)

#eval ((pGCL'.loop (.Lit (.Bool true)) (.Lit (.UInt 1)) pGCL'.skip).HeyVL 𝒜 .Upper ∅).2

@[grind =, simp]
theorem Distribution.toExpr_fv {μ : Distribution} : μ.toExpr.fv = μ.fv := by
  obtain ⟨⟨values⟩, h⟩ := μ
  simp [toExpr, fv]
  clear! h
  induction values with
  | nil => simp; rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, HeyLo.fv]
    grind [List.toFinset_cons, Finset.biUnion_insert]
-- @[grind =, simp]
-- theorem Distribution.map_fv {μ : Distribution} : (μ.map f).fv = μ.fv := by
--   obtain ⟨⟨values⟩, h⟩ := μ
--   simp [map, fv]
--   clear! h
--   induction values with
--   | nil => simp
--   | cons x xs ih =>
--     simp_all [List.map_cons, List.sum_cons, HeyLo.fv]
--     grind [List.toFinset_cons, Finset.biUnion_insert]

@[grind =, simp]
theorem pGCL'.fv_seq {C₁ C₂ : pGCL'} : (C₁.seq C₂).fv = C₁.fv ∪ C₂.fv := rfl
@[grind =, simp]
theorem pGCL'.fv_prob {C₁ C₂ : pGCL'} : (C₁.prob p C₂).fv = C₁.fv ∪ C₂.fv := by grind [fv]
@[grind =, simp]
theorem HeyVL.fv_vp {P : HeyVL} : (P.vp φ).fv = P.fv ∪ φ.fv := by
  induction P generalizing φ with (try simp_all [vp, fv, HeyLo.fv]) <;> try grind [fv, HeyLo.fv]
  | Assign x e =>
    simp only [Distribution.fv, Distribution.map, Array.toList_map]
    ext v
    simp
    constructor
    · grind
    · rintro (⟨⟨_⟩⟩ | ⟨q, p, h₁, h₂⟩)
      · simp_all only [true_or, and_true, Distribution.exists_in_values]
      · grind
      · simp_all only [true_or, or_true, and_true, Distribution.exists_in_values]
@[grind =, simp]
theorem HeyLo.fv_inf {X Y : 𝔼r} : (X ⊓ Y).fv = X.fv ∪ Y.fv := rfl
@[grind ., grind! ., simp]
theorem pGCL'.HeyVL_G_mono {C : pGCL'} : G ⊆ (C.HeyVL O D G).1 := by
  fun_induction HeyVL <;> try simp_all
  next => trans <;> assumption
  next ih₁ ih₂ =>
    apply trans ih₁
    apply trans ih₂
    grind [Globals.fresh_mono]
  next => trans <;> assumption
  next => trans <;> assumption
@[grind =, simp]
theorem pGCL'.fv_HeyVL_subset {C : pGCL'} :
    (C.HeyVL O D G).2.fv = C.fv ∪ ((C.HeyVL O D G).1 \ G) := by
  induction C generalizing G with simp_all [pGCL'.HeyVL, fv, embed, HeyVL.fv, HeyVL.Skip, HeyLo.fv]
  | assign => simp [Distribution.pure, Distribution.fv]
  | seq C₁ C₂ ih₁ ih₂ => grind
  | tick r => cases D <;> simp [HeyVL.fv]; grind
  | nonDet C₁ C₂ ih₁ ih₂ => grind
  | prob C₁ p C₂ ih₁ ih₂ =>
    simp only [Distribution.fv, Distribution.bin, List.toFinset_cons, List.toFinset_nil,
      insert_empty_eq, Finset.biUnion_insert, HeyLo.fv, Finset.singleton_biUnion,
      Finset.union_idempotent, HeyVL.If, embed, HeyLo.not, HeyVL.fv, Finset.union_empty,
      Finset.singleton_union, Finset.union_insert, Finset.insert_union, Finset.mem_insert,
      Finset.mem_union, true_or, Finset.insert_eq_of_mem, Finset.empty_union]
    simp_all
    ext a
    simp_all
    constructor
    · rintro (h | h | h | h | h) <;> try grind
      · right; right
        have : a ∉ G := by grind
        simp_all
        apply Globals.fresh_mono
        grind
      · simp_all
        right; right
        apply Globals.fresh_mono
        grind
    · grind
  | loop b I C ih =>
    have := (C.HeyVL O D G).2.mods_subset_fv
    simp only [HeyVL.If, embed, HeyLo.not]
    cases D
    · simp only [HeyVL.fv, HeyLo.fv, Finset.union_assoc, Finset.empty_union]
      grind
    · simp only [HeyVL.fv, HeyLo.fv, Finset.union_assoc, Finset.empty_union]
      grind

@[gcongr]
def Exp.substs_mono [DecidableEq ϖ] {X₁ X₂ : Exp ϖ} {xs : List (ϖ × Exp ϖ)} (h : X₁ ≤ X₂) :
    X₁[..xs] ≤ X₂[..xs] := by
  induction xs generalizing X₁ X₂ with
  | nil => simp [h]
  | cons x xs ih => apply fun σ ↦ ih h _

theorem HeyVL.havoc_alt :
    ((HeyVL.Havoc x).vp φ).sem = ⨅ (v : ENNReal), φ.sem[x ↦ ↑v] := by
  ext σ
  simp [vp]
theorem HeyVL.cohavoc_alt :
    ((HeyVL.Cohavoc x).vp φ).sem = ⨆ (v : ENNReal), φ.sem[x ↦ ↑v] := by
  ext σ
  simp [vp]

theorem HeyVL.havoc_comm :
    ((.Havoc x ;; .Havoc y).vp φ).sem = ((.Havoc y ;; .Havoc x).vp φ).sem := by
  wlog h : x ≠ y
  · grind
  rw [vp, vp]
  simp [HeyVL.havoc_alt]
  ext σ
  simp
  rw [iInf_comm]
  congr! 5 with vy vx
  ext z
  grind

structure HeyVL.Subs (Vars : List Ident) (hn : Vars.Nodup) (α : Type*) where
  values : List α
  prop : Vars.length = values.length

instance [Inhabited α] : Inhabited (HeyVL.Subs xs hn α) where
  default := ⟨xs.map (fun _ ↦ default), by simp⟩

def HeyVL.Subs.cons (S : Subs xs hn α) (x : Ident) (v : α) (hv : x ∉ xs) :
    Subs (x :: xs) (by grind) α :=
  ⟨v::S.values, by obtain ⟨S, hS⟩ := S; grind⟩
def HeyVL.Subs.tail (S : Subs (x :: xs) hn α) : α × Subs xs (List.Nodup.of_cons hn) α :=
  (S.values[0]'(by obtain ⟨S, hS⟩ := S; grind), ⟨S.values.tail, by obtain ⟨S, hS⟩ := S; grind⟩)

theorem HeyVL.Subs.tail_bij : Function.Bijective (Subs.tail (x:=x) (xs:=xs) (hn:=hn) (α:=α)) := by
  refine Function.bijective_iff_has_inverse.mpr ?_
  use fun (a, b) ↦ ⟨a :: b.values, by obtain ⟨b, hb⟩ := b; grind⟩
  simp
  constructor
  · intro ⟨S, hS⟩
    simp [tail]
    have : S ≠ [] := by grind
    ext
    grind
  · intro ⟨a, S, hS⟩
    simp_all [tail]

@[grind =, simp]
theorem HeyVL.Subs.values_length (S : Subs xs hn α) : S.values.length = xs.length := by
  obtain ⟨S, hS⟩ := S
  grind
def HeyVL.Subs.help (S : Subs xs hn ENNReal) : List (Ident × Exp Ident) :=
  xs.zip S.values
def HeyVL.Subs.help' (S : Subs xs hn α) : List (Ident × α) :=
  xs.zip S.values
@[grind =, simp]
theorem HeyVL.Subs.help_length (S : Subs xs hn ENNReal) : S.help.length = xs.length := by
  obtain ⟨S, hS⟩ := S
  simp [help]
  grind
@[grind =, simp]
theorem HeyVL.Subs.help_cons (S : Subs (x :: xs) hn ENNReal) :
    S.help = (x, ↑S.tail.1) :: S.tail.2.help := by
  simp [help, -List.pure_def, -List.bind_eq_flatMap, List.map_tail, Subs.tail]
  rw [← List.zip_cons_cons]
  congr
  ext
  grind
@[grind =, simp]
theorem HeyVL.Subs.help'_cons (S : Subs (x :: xs) hn α) :
    S.help' = (x, ↑S.tail.1) :: S.tail.2.help' := by
  simp only [help', tail]
  rw [← List.zip_cons_cons]
  congr
  ext
  grind

def HeyVL.Subs.get (S : Subs xs hn α) (x : Ident) (hx : x ∈ xs) : α :=
  S.values[xs.findIdx (· = x)]'(by grind)
@[grind =, simp]
theorem HeyVL.Subs.tail_get (S : Subs (x :: xs) hn α) (y : Ident) (hy : y ∈ xs) :
    S.tail.2.get y hy = S.get y (by grind) := by
  simp [tail, get]
  grind
@[grind =]
theorem HeyVL.Subs.tail_1_eq_get (S : Subs (x :: xs) hn α) :
    S.tail.1 = S.get x (by grind) := by
  simp [tail, get]
  grind

@[grind =, simp]
theorem HeyVL.Subs.subst_help'_apply (S : Subs xs hn ENNReal) (σ : States Ident) :
    σ[..S.help'] y = if h : y ∈ xs then S.get y h else σ y := by
  induction xs generalizing y with
  | nil => simp [HeyVL.Subs.help']
  | cons x xs ih =>
    simp
    rw [Substitution.substs_cons_substs]
    grind

@[simp]
theorem HeyVL.vp_havocs (h : xs.Nodup) :
    ((HeyVL.Havocs xs).vp φ).sem = ⨅ (vs : Subs xs hn ENNReal), φ.sem[..vs.help] := by
  rcases xs with _ | ⟨x, xs⟩
  · ext σ; simp [Havocs, Skip, vp, Subs.help]
  induction xs generalizing x φ with
  | nil =>
    ext σ
    simp [HeyVL.havoc_alt, Havocs]
    apply Function.Surjective.iInf_congr fun y ↦ ⟨[y], by simp⟩
    · intro ⟨e, h⟩
      simp
      use e[0]'(by grind)
      ext
      grind
    · intro g
      simp [Subs.help, Subs.tail]
  | cons y xs ih =>
    ext σ
    simp at ih
    simp_all [Havocs]
    rw [vp]
    have : y ∉ xs := by grind
    have : xs.Nodup := by grind
    simp_all [havoc_alt]
    rw [iInf_prod']
    symm
    apply Function.Surjective.iInf_congr Subs.tail Subs.tail_bij.surjective
    exact fun _ ↦ rfl

@[simp]
theorem HeyVL.vp_cohavocs (h : xs.Nodup) :
    ((HeyVL.Cohavocs xs).vp φ).sem = ⨆ (vs : Subs xs hn ENNReal), φ.sem[..vs.help] := by
  rcases xs with _ | ⟨x, xs⟩
  · ext σ; simp [Cohavocs, Skip, vp, Subs.help]
  induction xs generalizing x φ with
  | nil =>
    ext σ
    simp [HeyVL.cohavoc_alt, Cohavocs]
    apply Function.Surjective.iSup_congr fun y ↦ ⟨[y], by simp⟩
    · intro ⟨e, h⟩
      simp
      use e[0]'(by grind)
      ext
      grind
    · intro g
      simp [Subs.help, Subs.tail]
  | cons y xs ih =>
    ext σ
    simp at ih
    simp_all [Cohavocs]
    rw [vp]
    have : y ∉ xs := by grind
    have : xs.Nodup := by grind
    simp_all [cohavoc_alt]
    rw [iSup_prod']
    symm
    apply Function.Surjective.iSup_congr Subs.tail Subs.tail_bij.surjective
    exact fun _ ↦ rfl

@[gcongr]
theorem Exp.hcoimp_mono_left {a₁ a₂ b : Exp ϖ} (h : a₂ ≤ a₁) : a₁ ↜ b ≤ a₂ ↜ b := by
  intro σ
  specialize h σ
  simp [Exp.hcoimp_apply, instHCoImpENNReal]
  split_ifs <;> try grind
  simp_all

@[gcongr]
theorem Exp.hcoimp_mono_right {a b₁ b₂ : Exp ϖ} (h : b₁ ≤ b₂) : a ↜ b₁ ≤ a ↜ b₂ := by
  intro σ
  specialize h σ
  simp [Exp.hcoimp_apply, instHCoImpENNReal]
  split_ifs <;> try grind
  simp_all

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

namespace Exp

variable {ϖ : Type*} [DecidableEq ϖ] {a b : Exp ϖ} {p : BExpr ϖ} (xs : List (ϖ × Exp ϖ))

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

@[simp] theorem add_subst :
    (a + b)[..xs] = a[..xs] + b[..xs] := Substitution.substs_of_binary fun _ _ ↦ congrFun rfl
@[simp] theorem sub_subst :
    (a - b)[..xs] = a[..xs] - b[..xs] := Substitution.substs_of_binary fun _ _ ↦ congrFun rfl
@[simp] theorem mul_subst :
    (a * b)[..xs] = a[..xs] * b[..xs] := Substitution.substs_of_binary fun _ _ ↦ congrFun rfl
@[simp] theorem div_subst :
    (a / b)[..xs] = a[..xs] / b[..xs] := Substitution.substs_of_binary fun _ _ ↦ congrFun rfl
@[simp] theorem himp_subst :
    (a ⇨ b)[..xs] = a[..xs] ⇨ b[..xs] := Substitution.substs_of_binary fun _ _ ↦ congrFun rfl
@[simp] theorem hcoimp_subst :
    (a ↜ b)[..xs] = a[..xs] ↜ b[..xs] := Substitution.substs_of_binary fun _ _ ↦ congrFun rfl

@[simp] theorem eq_subst :
    (BExpr.eq a b)[..xs] = BExpr.eq a[..xs] b[..xs] :=
  Substitution.substs_of_binary fun _ _ ↦ congrFun rfl

end Exp

@[simp] theorem BExpr.eq_self {a : Exp ϖ} : BExpr.eq a a = true := by ext; simp; rfl
@[simp] theorem BExpr.eq_of_ne {a b : Exp ϖ} (h : ∀ σ, a σ ≠ b σ) : BExpr.eq a b = false := by
  ext; simp_all; exact of_decide_eq_false rfl
@[simp] theorem BExpr.iver_coe_bool :
    BExpr.iver (ϖ:=ϖ) (BExpr.coe_bool a) = if a then 1 else 0 := by
    ext
    simp [BExpr.iver, BExpr.coe_bool, DFunLike.coe]
    split_ifs <;> rfl
@[simp] theorem BExpr.not_coe_bool :
    BExpr.not (ϖ:=ϖ) (BExpr.coe_bool a) = BExpr.coe_bool ¬a := by
    ext
    simp [BExpr.not, BExpr.coe_bool, DFunLike.coe]

@[grind =, simp]
theorem HeyVL.if_vp_sem :
    ((HeyVL.If b S₁ S₂).vp φ).sem = i[b.sem] * (S₁.vp φ).sem + i[b.not.sem] * (S₂.vp φ).sem := by
  ext σ
  simp [If, vp]
  by_cases h : b.sem σ <;> simp [BExpr.iver, h]

noncomputable instance {α : Ty} : CompleteLattice α.lit :=
  match α with
  | .Bool => inferInstance
  | .ENNReal => inferInstance

def Substitution.applied [DecidableEq ϖ] (σ : States ϖ) (xs : List (ϖ × Exp ϖ)) : States ϖ :=
  match xs with
  | [] => σ
  | x::xs => Substitution.applied σ[x.1 ↦ x.2 σ] xs

theorem BExpr.subst_applied [DecidableEq ϖ] {b : BExpr ϖ} {xs : List (ϖ × Exp ϖ)} :
    b[..xs] = fun σ ↦ b (Substitution.applied σ xs) := by
  ext σ
  induction xs generalizing σ with
  | nil => simp [Substitution.applied]
  | cons x xs ih =>
    simp_all [Substitution.applied]
    simp [Substitution.substs_cons, BExpr.subst_apply]
    simp [ih]

@[grind =, simp]
theorem BExpr.subst_single_apply [DecidableEq ϖ] {b : BExpr ϖ} :
    b[x ↦ v] σ = b σ[x ↦ v σ] := by
  rfl
theorem BExpr.subst_apply [DecidableEq ϖ] {b : BExpr ϖ} {xs : List (ϖ × Exp ϖ)} :
    b[..xs] σ = b (Substitution.applied σ xs) := by
  rw [subst_applied]

theorem Exp.subst_applied [DecidableEq ϖ] {b : Exp ϖ} {xs : List (ϖ × Exp ϖ)} :
    b[..xs] = fun σ ↦ b (Substitution.applied σ xs) := by
  ext σ
  induction xs generalizing σ with
  | nil => simp [Substitution.applied]
  | cons x xs ih =>
    simp_all [Substitution.applied]
    simp [Substitution.substs_cons, Exp.subst₀_apply]
    simp [ih]

theorem Exp.subst_apply [DecidableEq ϖ] {b : Exp ϖ} {xs : List (ϖ × Exp ϖ)} :
    b[..xs] σ = b (Substitution.applied σ xs) := by
  rw [subst_applied]

@[grind =, simp]
theorem Exp.substs_help_apply (m : Exp Ident) (Ξ : HeyVL.Subs xs hxs ENNReal) :
    m[..Ξ.help] σ = m σ[..Ξ.help'] := by
  rw [Exp.subst_apply]
  congr
  induction xs generalizing σ with
  | nil => simp [HeyVL.Subs.help, HeyVL.Subs.help', Substitution.applied]
  | cons x xs ih =>
    simp [HeyVL.Subs.help_cons, Substitution.applied, Exp.ennreal_coe_apply, ih]
    clear ih
    simp only [Substitution.substs_cons_substs, Substitution.substs_nil]
    simp only [Substitution.substs_nil]
    ext y
    grind
@[grind =, simp]
theorem BExpr.substs_help_apply (m : BExpr Ident) (Ξ : HeyVL.Subs xs hxs ENNReal) :
    m[..Ξ.help] σ = m σ[..Ξ.help'] := by
  rw [BExpr.subst_apply]
  congr
  induction xs generalizing σ with
  | nil => simp [HeyVL.Subs.help, HeyVL.Subs.help', Substitution.applied]
  | cons x xs ih =>
    simp [HeyVL.Subs.help_cons, Substitution.applied, Exp.ennreal_coe_apply, ih]
    clear ih
    simp only [Substitution.substs_cons_substs, Substitution.substs_nil]
    simp only [Substitution.substs_nil]
    ext y
    grind

theorem HeyLo.sem_substs_apply (m : HeyLo α) :
    m.sem[..xs] σ = m.sem (Substitution.applied σ xs) := by
  cases α
  · simp [BExpr.subst_apply]
  · simp [Exp.subst_apply]
theorem HeyLo.sem_substs_apply' (m : HeyLo α) (Ξ : HeyVL.Subs xs hxs ENNReal) :
    m.sem[..Ξ.help] σ = m.sem σ[..Ξ.help'] := by
  cases α <;> simp
theorem Substitution.applied_subst [DecidableEq ϖ] (σ : States ϖ) (xs : List (ϖ × Exp ϖ)) :
      (Substitution.applied σ xs)[x ↦ v (Substitution.applied σ xs)]
    = Substitution.applied σ (xs ++ [(x, v)]) := by
  induction xs generalizing σ x v with
  | nil => simp [applied]
  | cons y xs ih =>
    simp_all [applied]

def HeyVL.Subs.of (xs : List Ident) (hn : xs.Nodup) (σ : States Ident) :
    HeyVL.Subs xs hn ENNReal := ⟨xs.map σ, by simp⟩
@[grind =, simp]
theorem HeyVL.Subs.of_get (xs : List Ident) (hn : xs.Nodup) (σ : States Ident) {y} {hy} :
    (Subs.of xs hn σ).get y hy = σ y := by simp [Subs.of, Subs.get]; grind
def HeyVL.Subs.of_surj : Function.Surjective (HeyVL.Subs.of xs hn) := by
  intro ⟨S, hS⟩
  simp_all [HeyVL.Subs.of]
  use fun i ↦ if h : i ∈ xs then S[xs.findIdx (· = i)]'(by grind) else 0
  apply List.ext_getElem
  · grind
  · simp
    intro n h₁ h₂
    congr
    refine (List.findIdx_eq h₁).mpr ?_
    grind [List.Nodup.getElem_inj_iff]

@[gcongr]
theorem pGCL.Exp.ennreal_coe_le (h : a ≤ b) :
    pGCL.Exp.ennreal_coe (ϖ:=ϖ) a ≤ pGCL.Exp.ennreal_coe b := by
  intro; grind

@[grind]
def HeyLo.mods : HeyLo α → Globals
  | .Binary _ S₁ S₂ => S₁.mods ∪ S₂.mods
  | .Lit _ => ∅
  | .Subst _ e m => e.mods ∪ m.mods
  | .Quant _ _ m => m.mods
  | .Ite b l r => b.mods ∪ l.mods ∪ r.mods
  | .Var _ => ∅
  | .Unary _ m => m.mods
def Distribution.mods (D : Distribution) : Globals :=
  D.values.toList.toFinset.biUnion (·.2.mods)

/-- Park induction -/
theorem pGCL.wp_le_of_le [DecidableEq ϖ] {C : pGCL ϖ} (I : Exp ϖ) (h : Φ O φ C f I ≤ I) :
    wp[O]⟦while (~φ) {~C}⟧ f ≤ I := by
  exact OrderHom.lfp_le _ h

@[grind =]
theorem States.subst_comm {σ : States Ident} {x₁ x₂ : Ident} {v₁ v₂ : ENNReal} (h : x₁ ≠ x₂) :
    σ[x₁ ↦ v₁][x₂ ↦ v₂] = σ[x₂ ↦ v₂][x₁ ↦ v₁] := by ext; grind
@[grind =, simp]
theorem HeyLo.sem_indep {α : Ty} {φ : HeyLo α} {x : Ident} (h : x ∉ φ.fv) :
    Substitution.IsIndepPair φ.sem x := by
  intro v
  induction φ generalizing v with
    (simp [fv] at h; simp_all only [not_false_eq_true, Ty.expr, forall_const])
  | Var y => grind [sem]
  | Lit l => simp [sem]; split <;> rfl
  | Ite b S₁ S₂ ihb ih₁ ih₂ =>
    simp [BExpr.ext_iff, *] at ihb
    cases ‹Ty›
    · ext σ
      simp [sem, BExpr.ite_apply]
      simp [BExpr.ext_iff, *] at ih₁
      simp [BExpr.ext_iff, *] at ih₂
      simp_all only
    · ext σ
      simp [sem, BExpr.iver]
      simp [Exp.ext_iff, *] at ih₁
      simp [Exp.ext_iff, *] at ih₂
      simp_all only
  | Subst y w m ih₁ ih₂ =>
    simp [sem]
    replace ih₁ : ∀ (v : ENNReal), w.sem[x ↦ ↑v] = w.sem := by grind
    replace ih₂ : ∀ (v : ENNReal), m.sem[x ↦ ↑v] = m.sem := by grind
    simp [Exp.ext_iff, *] at ih₁
    cases ‹Ty›
    · ext σ
      simp [BExpr.ext_iff, *] at ih₂
      grind
    · ext σ
      simp [Exp.ext_iff, *] at ih₂
      grind
  | Quant op y m ih =>
    cases op
    · ext σ
      simp only [sem_Inf, pGCL.Exp.subst_apply, iInf_apply]
      replace ih := (congrFun (ih (v σ)) σ[y ↦ ·])
      grind
    · ext σ
      simp only [sem_Sup, pGCL.Exp.subst_apply, iSup_apply]
      replace ih := (congrFun (ih (v σ)) σ[y ↦ ·])
      grind
    · ext σ
      replace ih := (BExpr.ext_iff.mp (ih (v σ)) σ[y ↦ ·])
      grind
    · ext σ
      replace ih := (BExpr.ext_iff.mp (ih (v σ)) σ[y ↦ ·])
      grind
  | Unary => grind [sem]
  | Binary => grind [sem]

@[grind]
def pGCL.mods : pGCL ϖ → Set ϖ
  | pgcl {skip} => ∅
  | pgcl {~x := ~_} => {x}
  | pgcl {~C₁ ; ~C₂} => C₁.mods ∪ C₂.mods
  | pgcl {{~C₁} [~_] {~C₂}} => C₁.mods ∪ C₂.mods
  | pgcl {{~C₁} [] {~C₂}} => C₁.mods ∪ C₂.mods
  | pgcl {while ~_ {~C'}} => C'.mods
  | pgcl {tick(~ _)} => ∅
  | pgcl {observe(~ _)} => ∅

open scoped Classical in
noncomputable
def Exp.fix (X : Exp ϖ) (S : Set ϖ) (σ₀ : States ϖ) : Exp ↑Sᶜ :=
  fun σ ↦ X fun v ↦ if h : v ∈ S then σ₀ v else σ ⟨v, h⟩

@[grind =, simp]
theorem Exp.fix_empty (φ : Exp ϖ) : Exp.fix φ ∅ σ₀ σ = φ (σ ⟨·, id⟩) := by
  simp [fix]
@[grind =, simp]
theorem Exp.fix_compl_empty (φ : Exp ϖ) : Exp.fix φ ∅ᶜ σ₀ σ = φ σ₀ := by
  simp [fix]
@[grind ., simp]
theorem Exp.fix_compl_empty_eq (φ ψ : Exp ϖ) : Exp.fix φ ∅ᶜ = Exp.fix ψ ∅ᶜ ↔ φ = ψ := by
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
    (BExpr.fix X S σ₀) σ = X fun v ↦ if h : v ∈ S then σ₀ v else σ ⟨v, h⟩ := rfl

open scoped Classical in
noncomputable
def ProbExp.fix (X : ProbExp ϖ) (S : Set ϖ) (σ₀ : States ϖ) : ProbExp ↑Sᶜ :=
  ⟨fun σ ↦ X fun v ↦ if h : v ∈ S then σ₀ v else σ ⟨v, h⟩, by intro σ; simp⟩

open scoped Classical in
noncomputable def pGCL.fix (C : pGCL ϖ) (S : Set ϖ) (σ₀ : States ϖ) : pGCL ↑Sᶜ :=
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

theorem pGCL.wp_le_of_fix [DecidableEq ϖ] (C : pGCL ϖ) (φ : Exp ϖ) (S : Set ϖ) :
    Exp.fix (wp[O]⟦~C⟧ φ) S σ₀ ≤ Exp.fix X S σ₀ → wp[O]⟦~C⟧ φ σ₀ ≤ X σ₀ := by
  intro h
  replace h := h fun x ↦ σ₀ x
  simp_all [Exp.fix]

theorem pGCL.le_wlp''_of_fix [DecidableEq ϖ] (C : pGCL ϖ) (φ : Exp ϖ) (S : Set ϖ) :
    Exp.fix X S σ₀ ≤ Exp.fix (wlp''[O]⟦~C⟧ φ) S σ₀ → X σ₀ ≤ wlp''[O]⟦~C⟧ φ σ₀ := by
  intro h
  replace h := h fun x ↦ σ₀ x
  simp_all [Exp.fix]

theorem pGCL.wp_fix [DecidableEq ϖ] (C : pGCL ϖ) (φ : Exp ϖ) (S : Set ϖ) (hS : C.mods ⊆ Sᶜ) :
    Exp.fix (wp[O]⟦~C⟧ φ) S σ₀ = wp[O]⟦~(C.fix S σ₀)⟧ (Exp.fix φ S σ₀) := by
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
      simp only [OrderHom.mk_apply, Pi.add_apply, Pi.mul_apply]
      congr! 2
      classical
      rw [← Exp.ext_iff] at ih'
      rw [ih']
      exact congrFun (ih ((Φ O b C φ)^[i] 0)) σ

theorem pGCL.wlp''_fix [DecidableEq ϖ] (C : pGCL ϖ) (φ : Exp ϖ) (S : Set ϖ) (hS : C.mods ⊆ Sᶜ) :
    Exp.fix (wlp''[O]⟦~C⟧ φ) S σ₀ = wlp''[O]⟦~(C.fix S σ₀)⟧ (Exp.fix φ S σ₀) := by
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
      nth_rw 1 [lΦ'']
      nth_rw 2 [lΦ'']
      simp [ProbExp.pick]
      congr! 2
      classical
      rw [← Exp.ext_iff] at ih'
      rw [ih']
      exact congrFun (ih ((lΦ'' O b C φ)^[i] ⊤)) σ

@[grind =, simp]
theorem HeyVL.Cohavocs_mods : (HeyVL.Cohavocs xs).mods = ∅ := by
  fun_induction Cohavocs with simp_all [mods, HeyVL.Skip]

@[grind ., simp]
theorem pGCL'.HeyVL_mods (C : pGCL') : C.mods ⊆ (C.HeyVL O D G).2.mods := by
  induction C generalizing G with simp_all [mods, HeyVL, HeyVL.mods, HeyVL.If] <;> try grind
  | loop => cases D <;> simp_all only [HeyVL.mods] <;> grind


/-- An _Idle invariant_ is _Park invariant_ that holds for states with a set of fixed variables. -/
def pGCL.IdleInvariant [DecidableEq ϖ] (O : Optimization) (b : BExpr ϖ) (C : pGCL ϖ) (φ : Exp ϖ)
    (I : Exp ϖ) (S : Set ϖ) (σ₀ : States ϖ) : Prop :=
  ∀ σ, (∀ v ∈ S, σ v = σ₀ v) → Φ O b C φ I σ ≤ I σ

/-- _Idle induction_ is _Park induction_, but the engine is running (i.e. an initial state is
given), and as a consequence only states that vary over the modified variables need to be
considered for the inductive invariant. -/
theorem pGCL.IdleInduction [DecidableEq ϖ] (b : BExpr ϖ) (C : pGCL ϖ) (φ : Exp ϖ) (I : Exp ϖ)
    (σ₀ : States ϖ) (h : C.IdleInvariant O b φ I C.modsᶜ σ₀) :
    wp[O]⟦while ~b { ~C }⟧ φ σ₀ ≤ I σ₀ := by
  apply pGCL.wp_le_of_fix (S:=C.modsᶜ)
  rw [pGCL.wp_fix _ _ _ (by simp; rfl)]
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
  · simp [BExpr.fix, BExpr.iver, σ₁]
    simp [DFunLike.coe]
  · rw [← pGCL.wp_fix _ _ _ (by simp)]
    simp [Exp.fix, σ₁]
  · simp [BExpr.fix, BExpr.iver, σ₁]
    simp [DFunLike.coe]
  · simp [Exp.fix, σ₁]
  · simp [Exp.fix, σ₁]

/-- An _Idle coinvariant_ is _Park coinvariant_ that holds for states with a set of fixed variables.
-/
def pGCL.IdleCoinvariant [DecidableEq ϖ] (O : Optimization) (b : BExpr ϖ) (C : pGCL ϖ) (φ : Exp ϖ)
    (I : Exp ϖ) (S : Set ϖ) (σ₀ : States ϖ) : Prop :=
  ∀ σ, (∀ v ∈ S, σ v = σ₀ v) → I σ ≤ lΦ'' O b C φ I σ

/-- _Idle coinduction_ is _Park coinduction_, but the engine is running (i.e. an initial state is
given), and as a consequence only states that vary over the modified variables need to be
considered for the coinductive invariant. -/
theorem pGCL.IdleCoinduction [DecidableEq ϖ] (b : BExpr ϖ) (C : pGCL ϖ) (φ : Exp ϖ) (I : Exp ϖ)
    (σ₀ : States ϖ) (h : C.IdleCoinvariant O b φ I C.modsᶜ σ₀) :
    I σ₀ ≤ wlp''[O]⟦while ~b { ~C }⟧ φ σ₀ := by
  apply pGCL.le_wlp''_of_fix (S:=C.modsᶜ)
  rw [pGCL.wlp''_fix _ _ _ (by simp; rfl)]
  apply OrderHom.le_gfp
  simp [IdleCoinvariant, lΦ''] at h
  intro σ'
  simp only [OrderHom.mk_apply]
  classical
  let σ₁ : States ϖ := fun v ↦ if h : v ∈ C.mods then σ' ⟨v, by grind⟩ else σ₀ v
  have : (∀ v ∉ C.mods, σ₁ v = σ₀ v) := by simp +contextual [σ₁]
  convert h σ₁ this
  · simp [Exp.fix, σ₁]
  · simp [ProbExp.pick, BExpr.probOf, BExpr.iver, BExpr.fix_apply, σ₁]
    congr! 2
    · rw [← pGCL.wlp''_fix _ _ _ (by simp)]
      simp [Exp.fix]
    · simp [Exp.fix]

@[grind =, simp]
theorem pGCL'.pGCL_mods (C : pGCL') : C.pGCL.mods = ↑C.mods := by
  induction C with simp_all [mods, pGCL, pGCL.mods]

theorem NNRat.toENNReal_sub (a b : ℚ≥0) (h : b ≤ a) :
    (((a - b) : ℚ≥0) : ENNReal) = (↑a : ENNReal) - ↑b := by
  have := Rat.cast_sub (α:=Real) a b
  simp only [Rat.cast_nnratCast] at this
  refine (ENNReal.toReal_eq_toReal_iff' ?_ ?_).mp ?_
  swap
  · exact Ne.symm (not_eq_of_beq_eq_false rfl)
  · exact Ne.symm (not_eq_of_beq_eq_false rfl)
  have hx : ∀ (x : ℚ≥0), (@NNRat.cast ENNReal ENNReal.instNNRatCast x).toReal = x := by
    intro x
    rfl
  convert this <;> clear this
  · simp
    simp only [hx]
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    simp_all
    rw [sub_def]
    simp
    replace h : b ≤ a := h
    norm_cast
    simp_all [Rat.coe_toNNRat]
  · norm_cast
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    replace h : b ≤ a := h
    have : @NNRat.cast ENNReal ENNReal.instNNRatCast ⟨a, ha⟩ = ENNReal.ofReal a := by
      refine (ENNReal.toReal_eq_toReal_iff' ?_ ?_).mp ?_
      · exact Ne.symm (not_eq_of_beq_eq_false rfl)
      · exact ENNReal.ofReal_ne_top
      · refine Eq.symm (ENNReal.toReal_ofReal ?_)
        exact Rat.cast_nonneg.mpr ha
    have : @NNRat.cast ENNReal ENNReal.instNNRatCast ⟨b, hb⟩ = ENNReal.ofReal b := by
      refine (ENNReal.toReal_eq_toReal_iff' ?_ ?_).mp ?_
      · exact Ne.symm (not_eq_of_beq_eq_false rfl)
      · exact ENNReal.ofReal_ne_top
      · refine Eq.symm (ENNReal.toReal_ofReal ?_)
        exact Rat.cast_nonneg.mpr hb
    simp_all

@[grind =, simp]
theorem NNRat.ennreal_cast : (1 : NNRat) = (1 : ENNReal) := by
  simp [NNRat.cast]
  simp [NNRatCast.nnratCast]

example (p : ℚ≥0) (hp : p ≤ 1) : 1 - (↑p : ENNReal) = (↑(1 - p) : ENNReal) := by
  simp only [hp, NNRat.toENNReal_sub, NNRat.ennreal_cast]

theorem pGCL'.wp_le_vp {C : pGCL'} {G : Globals} (hG : C.fv ∪ φ.fv ⊆ G) :
    wp[O]⟦~C.pGCL⟧ φ.sem ≤ ((C.HeyVL O .Lower G).2.vp φ).sem := by
  induction C generalizing G φ with
  | skip =>
    intro σ
    simp only [pGCL'.HeyVL, HeyVL.Skip, HeyVL.vp, sem_add_apply, sem_zero, Pi.add_apply,
      Pi.zero_apply, add_zero, pGCL'.pGCL, wp.skip_apply, le_refl]
  | assign x e =>
    simp [pGCL'.HeyVL, HeyVL.vp, pGCL'.pGCL, Literal.sem]
    intro σ
    simp
  | seq C₁ C₂ ih₁ ih₂ =>
    simp only [pGCL'.HeyVL, HeyVL.vp, pGCL'.pGCL, wp.seq_apply]
    simp_all
    grw [← ih₁, ← ih₂]
    · grind
    · simp
      grind
  | nonDet C₁ C₂ ih₁ ih₂ =>
    simp [pGCL'.fv] at hG
    simp only [pGCL, wp.nonDet_apply, Optimization.opt₂, HeyVL]
    cases O
    · simp only [HeyVL.vp, sem_sup_apply]
      grw [← ih₁, ← ih₂] <;> grind
    · simp only [HeyVL.vp, sem_inf_apply]
      grw [← ih₁, ← ih₂] <;> grind
  | prob C₁ p C₂ ih₁ ih₂ =>
    obtain ⟨p, hp⟩ := p
    simp_all [pGCL'.HeyVL, pGCL'.pGCL, HeyVL.If, HeyVL.vp, wp.prob_apply, ProbExp.pick]
    simp [BinOp.sem]
    rw [HeyLo.sem_subt_var]
    simp

    have : (C₁.HeyVL O .Lower (C₂.HeyVL O .Lower G).1).1.fresh.2 ∉ G := by grind
    rw [Substitution.indep_pair, Substitution.indep_pair]
    rotate_left
    · apply HeyLo.sem_indep
      grind
    · apply HeyLo.sem_indep
      grind

    grw [← ih₁, ← ih₂]
    · intro σ; simp [NNRat.toENNReal_sub, hp]
    · grind
    · calc
        C₁.fv ∪ φ.fv ⊆ C₁.fv ∪ (C₂.fv ∪ φ.fv) := by grind
        _ ⊆ G := by grind
        _ ⊆ (C₂.HeyVL O .Lower G).1 := by grind
  | loop b I C ih =>
    simp only [pGCL'.pGCL, pGCL'.HeyVL, HeyVL.vp, sem_sup_apply, Globals.toList_Nodup,
      HeyVL.vp_cohavocs]
    intro σ
    if inv : IdleInvariant O b.sem C.pGCL φ.sem I.sem C.modsᶜ σ then
      simp
      left
      apply IdleInduction
      grind
    else
      simp [IdleInvariant] at inv
      obtain ⟨σ', h₁, h₂⟩ := inv
      simp [Φ] at h₂
      let Ξ := HeyVL.Subs.of (C.HeyVL O .Lower G).2.mods.toList (by simp) σ'
      have : σ[..Ξ.help'] = σ' := by
        ext x
        simp +contextual [Ξ]
        intro h
        specialize h₁ x (by contrapose! h; exact C.HeyVL_mods h)
        simp_all
      simp_all
      right
      apply le_iSup_of_le Ξ
      simp [HeyVL.vp, HeyVL.Skip]
      have : ∀ {a b : ENNReal}, ▿ (a ↜ b) = if b ≤ a then 0 else ⊤ := by
        intro a b
        simp [covalidate, himp, hconot, hcoimp]
        grind [ne_zero_of_lt]
      simp [this]
      specialize ih (φ:=I ⊔ (⊤ ↜ φ)) (G:=G) (by simp [HeyLo.fv]; grind) σ[..Ξ.help']
      have :
            wp[O]⟦~C.pGCL⟧ I.sem σ[..Ξ.help']
          ≤ ((C.HeyVL O .Lower G).2.vp (I ⊔ (⊤ ↜ φ))).sem σ[..Ξ.help'] := by
        grw [← ih]
        have : (I.sem ⊔ ((⊤ : 𝔼r).sem ↜ φ.sem)) = I.sem := by ext; simp [sem, hcoimp]
        simp [this]
      simp only at this
      simp only [ge_iff_le]
      suffices
            ¬i[b.sem[..Ξ.help]] σ * ((C.HeyVL O .Lower G).2.vp (I ⊔ (⊤ ↜ φ))).sem σ[..Ξ.help'] +
              i[b.sem[..Ξ.help].not] σ * φ.sem σ[..Ξ.help']
          ≤ I.sem (σ[..Ξ.help']) by simp [this]
      grw [← this]; clear this; clear this; clear ih
      simp
      grind
  | tick r =>
    grind [pGCL'.HeyVL, HeyVL.vp, add_comm, pGCL'.pGCL, wp.tick_apply, le_refl]
  | observe r =>
    intro σ
    simp only [pGCL'.pGCL, wp.observe_apply, Pi.mul_apply, pGCL'.HeyVL, HeyVL.vp, sem_inf_apply,
      Ty.expr, sem_embed, Pi.inf_apply, Pi.top_apply, le_inf_iff, BExpr.iver_mul_le_apply, and_true]
    if r.sem σ then simp_all else simp_all

/-- info: 'pGCL'.wp_le_vp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pGCL'.wp_le_vp

theorem pGCL'.vp_le_wlp'' {C : pGCL'} {G : Globals} (hG : C.fv ∪ φ.fv ⊆ G) :
    ((C.HeyVL O .Upper G).2.vp φ).sem ≤ wlp'' O C.pGCL φ.sem := by
  induction C generalizing G φ with
  | skip =>
    intro σ
    simp only [HeyVL, HeyVL.Skip, HeyVL.vp, sem_add_apply, Ty.expr, sem_zero, Pi.add_apply,
      Pi.zero_apply, add_zero, pGCL, wlp''.skip_apply, le_refl]
  | assign x e =>
    simp only [Ty.expr, HeyVL, HeyVL.vp, Distribution.pure_map, Distribution.pure_toExpr,
      sem_add_apply, sem_mul_apply, sem_lit_apply, Literal.sem, NNRat.ennreal_cast, sem_subst,
      sem_zero, add_zero, pGCL, wlp''.assign_apply]
    intro σ
    simp
  | seq C₁ C₂ ih₁ ih₂ =>
    simp only [Ty.expr, HeyVL, HeyVL.vp, pGCL, wlp''.seq_apply]
    simp_all
    grw [ih₁, ih₂]
    · grind
    · simp
      grind
  | nonDet C₁ C₂ ih₁ ih₂ =>
    simp only [Ty.expr, HeyVL, pGCL, wlp''.nonDet_apply, Optimization.opt₂]
    simp [pGCL'.fv] at hG
    have : C₁.fv ∪ φ.fv ⊆ G := by grind
    cases O
    · simp only [HeyVL.vp, sem_sup_apply, Ty.expr]
      grw [ih₁, ih₂] <;> grind
    · simp only [HeyVL.vp, sem_inf_apply, Ty.expr]
      grw [ih₁, ih₂] <;> grind
  | prob C₁ p C₂ ih₁ ih₂ =>
    obtain ⟨p, hp⟩ := p
    simp_all only [Ty.expr, fv_prob, Finset.union_assoc, HeyVL, HeyVL.If, HeyVL.vp,
      Distribution.bin_map, Distribution.bin_toExpr, sem_add_apply, sem_mul_apply, sem_lit_apply,
      Literal.sem, sem_subst, sem_inf_apply, sem_himp_apply, sem_embed, sem_binop, sem_zero,
      sem_not_apply, Exp.min_subst, Exp.himp_subst, Exp.mul_subst, Exp.iver_subst, Exp.top_subst,
      Exp.not_subst, sem_one, add_zero, pGCL, wlp''.prob_apply, ProbExp.pick, ProbExp.mk_vcoe]
    simp [BinOp.sem]
    rw [HeyLo.sem_subt_var]
    simp

    have : (C₁.HeyVL O .Upper (C₂.HeyVL O .Upper G).1).1.fresh.2 ∉ G := by grind
    rw [Substitution.indep_pair, Substitution.indep_pair]
    rotate_left
    · apply HeyLo.sem_indep
      grind
    · apply HeyLo.sem_indep
      grind

    grw [ih₁, ih₂]
    · intro σ; simp [NNRat.toENNReal_sub, hp]
    · grind
    · calc
        C₁.fv ∪ φ.fv ⊆ C₁.fv ∪ (C₂.fv ∪ φ.fv) := by grind
        _ ⊆ G := by grind
        _ ⊆ (C₂.HeyVL O .Upper G).1 := by grind
  | loop b I C ih =>
    simp only [Ty.expr, HeyVL, HeyVL.vp, sem_inf_apply, Globals.toList_Nodup, HeyVL.vp_havocs,
      sem_validate, sem_himp_apply, HeyVL.if_vp_sem, sem_not_apply, Exp.validate_subst,
      Exp.himp_subst, Exp.add_subst, Exp.mul_subst, Exp.iver_subst, Exp.not_subst, pGCL]
    intro σ
    if inv : IdleCoinvariant O b.sem C.pGCL φ.sem I.sem C.modsᶜ σ then
      simp
      left
      apply IdleCoinduction
      grind
    else
      simp [IdleCoinvariant] at inv
      obtain ⟨σ', h₁, h₂⟩ := inv
      simp [lΦ''] at h₂
      let Ξ := HeyVL.Subs.of (C.HeyVL O .Upper G).2.mods.toList (by simp) σ'
      have : σ[..Ξ.help'] = σ' := by
        ext x
        simp +contextual [Ξ]
        intro h
        specialize h₁ x (by contrapose! h; exact C.HeyVL_mods h)
        simp_all
      simp_all
      right
      apply iInf_le_of_le Ξ
      simp [HeyVL.vp, HeyVL.Skip]
      have : ∀ {a b : ENNReal}, ▵ (a ⇨ b) = if a ≤ b then ⊤ else 0 := by
        intro a b
        simp [validate, himp, hnot, himp]
        grind [LT.lt.ne_top]
      simp [this]
      specialize ih (φ:=I ⊓ (0 ⇨ φ)) (G:=G) (by simp [HeyLo.fv]; grind) σ[..Ξ.help']
      have :
            ((C.HeyVL O .Upper G).2.vp (I ⊓ (0 ⇨ φ))).sem σ[..Ξ.help']
          ≤ wlp''[O]⟦~C.pGCL⟧ I.sem σ[..Ξ.help'] := by
        grw [ih]
        simp
      simp only at this
      simp only [ge_iff_le]
      suffices ¬I.sem (σ[..Ξ.help'])
          ≤ i[b.sem[..Ξ.help]] σ * ((C.HeyVL O .Upper G).2.vp (I ⊓ (0 ⇨ φ))).sem (σ[..Ξ.help'])
            + i[b.sem[..Ξ.help].not] σ * φ.sem (σ[..Ξ.help'])
        by simp [this]
      grw [this]; clear this; clear this; clear ih
      have : i[b.sem[..Ξ.help].not] σ = 1 - i[b.sem] σ' := by
        simp_all [BExpr.iver_apply]
        split_ifs <;> simp
      simp only [ProbExp.pick, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.one_apply] at h₂
      grind
  | tick r =>
    simp only [HeyVL, HeyVL.vp, sem_add_apply, sem_binop, BinOp.sem, pGCL, wlp''.tick_apply]
    intro σ
    grind [tsub_self, add_zero]
  | observe r =>
    intro σ
    simp only [HeyVL, HeyVL.vp, sem_inf_apply, Ty.expr, sem_embed, Pi.inf_apply, Pi.mul_apply,
      Pi.top_apply, pGCL]
    if r.sem σ then simp_all else simp_all

/-- info: 'pGCL'.vp_le_wlp''' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pGCL'.vp_le_wlp''
