import HeyLo.Expr
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Lattice
import PGCL.IdleInvariant

attribute [grind =] Finset.empty_union

open Optimization.Notation

open pGCL

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
theorem HeyLo.sem_subst_apply' : A[..xs].sem = A.sem[..xs.map (fun x ↦ ⟨x.1, x.2.sem⟩)] := by
  induction xs generalizing A with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨x, v⟩ := x
    simp_all
    calc
      (Substitution.subst (substs A xs) ⟨x, v⟩).sem =
          Substitution.subst (substs A xs).sem ⟨x, v.sem⟩ :=
        by
          clear ih
          ext σ
          simp [Substitution.subst, subst, sem]
      _ =
          Substitution.subst (substs A.sem (List.map (fun x ↦ ⟨x.1, x.2.sem⟩) xs)) ⟨x, v.sem⟩ :=
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
def HeyVL.Subs.help (S : Subs xs hn ENNReal) : List ((_ : Ident) × Exp Ident) :=
  (xs.zip S.values).map (fun a ↦ ⟨a.1, a.2⟩)
def HeyVL.Subs.help' (S : Subs xs hn α) : List ((_ : Ident) × α) :=
  (xs.zip S.values).map (fun a ↦ ⟨a.1, a.2⟩)
@[grind =, simp]
theorem HeyVL.Subs.help_length (S : Subs xs hn ENNReal) : S.help.length = xs.length := by
  obtain ⟨S, hS⟩ := S
  simp [help]
  grind
@[grind =, simp]
theorem HeyVL.Subs.help_cons (S : Subs (x :: xs) hn ENNReal) :
    S.help = ⟨x, ↑S.tail.1⟩ :: S.tail.2.help := by
  ext; grind [help, tail]
@[grind =, simp]
theorem HeyVL.Subs.help'_cons (S : Subs (x :: xs) hn α) :
    S.help' = ⟨x, ↑S.tail.1⟩ :: S.tail.2.help' := by
  ext; grind [help', tail]

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

@[grind =, simp]
theorem HeyVL.if_vp_sem :
    ((HeyVL.If b S₁ S₂).vp φ).sem = i[b.sem] * (S₁.vp φ).sem + i[b.not.sem] * (S₂.vp φ).sem := by
  ext σ
  simp [If, vp]
  by_cases h : b.sem σ <;> simp [h]

noncomputable instance {α : Ty} : CompleteLattice α.lit :=
  match α with
  | .Bool => inferInstance
  | .ENNReal => inferInstance

def Substitution.applied [DecidableEq ϖ] (σ : States ϖ) (xs : List ((_ : ϖ) × Exp ϖ)) : States ϖ :=
  match xs with
  | [] => σ
  | x::xs => Substitution.applied σ[x.1 ↦ x.2 σ] xs

theorem BExpr.subst_applied [DecidableEq ϖ] {b : BExpr ϖ} {xs : List ((_ : ϖ) × Exp ϖ)} :
    b[..xs] = fun σ ↦ b (Substitution.applied σ xs) := by
  ext σ
  induction xs generalizing σ with
  | nil => simp [Substitution.applied]
  | cons x xs ih =>
    simp_all [Substitution.applied]
    simp [Substitution.substs_cons, BExpr.subst_apply]
    simp [ih]

theorem BExpr.subst_apply [DecidableEq ϖ] {b : BExpr ϖ} {xs : List ((_ : ϖ) × Exp ϖ)} :
    b[..xs] σ = b (Substitution.applied σ xs) := by
  rw [subst_applied]

theorem Exp.subst_applied [DecidableEq ϖ] {b : Exp ϖ} {xs : List ((_ : ϖ) × Exp ϖ)} :
    b[..xs] = fun σ ↦ b (Substitution.applied σ xs) := by
  ext σ
  induction xs generalizing σ with
  | nil => simp [Substitution.applied]
  | cons x xs ih =>
    simp_all [Substitution.applied]
    simp [Substitution.substs_cons, Exp.subst₀_apply]
    simp [ih]

theorem Exp.subst_apply [DecidableEq ϖ] {b : Exp ϖ} {xs : List ((_ : ϖ) × Exp ϖ)} :
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
theorem Substitution.applied_subst [DecidableEq ϖ] (σ : States ϖ) (xs : List ((_ : ϖ) × Exp ϖ))
    (v : Exp ϖ) :
      (Substitution.applied σ xs)[x ↦ v (Substitution.applied σ xs)]
    = Substitution.applied σ (xs ++ [⟨x, v⟩]) := by
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
      simp [sem]
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

@[grind =, simp]
theorem HeyVL.Cohavocs_mods : (HeyVL.Cohavocs xs).mods = ∅ := by
  fun_induction Cohavocs with simp_all [mods, HeyVL.Skip]

@[grind ., simp]
theorem pGCL'.HeyVL_mods (C : pGCL') : C.mods ⊆ (C.HeyVL O D G).2.mods := by
  induction C generalizing G with simp_all [mods, HeyVL, HeyVL.mods, HeyVL.If] <;> try grind
  | loop => cases D <;> simp_all only [HeyVL.mods] <;> grind

@[grind =, simp]
theorem pGCL'.pGCL_mods (C : pGCL') : C.pGCL.mods = ↑C.mods := by
  induction C with simp_all [mods, pGCL, pGCL.mods]

@[grind =, simp]
theorem NNRat.ennreal_cast {n : ℕ} : (n : NNRat) = (n : ENNReal) := by
  simp [NNRat.cast]
  simp [NNRatCast.nnratCast]
@[grind =, simp]
theorem NNRat.ennreal_cast_zero : (0 : NNRat) = (0 : ENNReal) := by
  simp [NNRat.cast]
  simp [NNRatCast.nnratCast]
@[grind =, simp]
theorem NNRat.ennreal_cast_one : (1 : NNRat) = (1 : ENNReal) := by
  simp [NNRat.cast]
  simp [NNRatCast.nnratCast]

@[simp]
theorem NNRat.toENNReal_sub (a b : ℚ≥0) : (((a - b) : ℚ≥0) : ENNReal) = (↑a : ENNReal) - ↑b := by
  if h : b ≤ a then
    have := Rat.cast_sub (α:=Real) a b
    simp only [Rat.cast_nnratCast] at this
    refine (ENNReal.toReal_eq_toReal_iff' ?_ ?_).mp ?_
    swap
    · exact Ne.symm (not_eq_of_beq_eq_false rfl)
    · exact Ne.symm (not_eq_of_beq_eq_false rfl)
    convert this <;> clear this
    · simp
      have hx : ∀ (x : ℚ≥0), (@NNRat.cast ENNReal ENNReal.instNNRatCast x).toReal = x := by
        intro x
        rfl
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
  else
    simp_all
    replace h := h.le
    have : a - b = 0 := by
      simp only [sub_def, Rat.toNNRat_eq_zero, tsub_le_iff_right, zero_add, cast_le, h]
    simp [this]
    symm
    refine tsub_eq_zero_of_le ?_
    suffices ∃ c, a + c = b by
      obtain ⟨c, ⟨_⟩⟩ := this
      apply le_trans _ _ (b:=(↑a : ENNReal) + (↑c : ENNReal))
      · exact le_self_add
      · apply le_of_eq
        refine (ENNReal.toReal_eq_toReal_iff' ?_ ?_).mp (Rat.cast_add _ _).symm
        · exact Ne.symm (not_eq_of_beq_eq_false rfl)
        · exact Ne.symm (not_eq_of_beq_eq_false rfl)
    use (b - a)
    exact add_tsub_cancel_of_le h

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
    · intro σ; rfl
    · grind
    · calc
        C₁.fv ∪ φ.fv ⊆ C₁.fv ∪ (C₂.fv ∪ φ.fv) := by grind
        _ ⊆ G := by grind
        _ ⊆ (C₂.HeyVL O .Lower G).1 := by grind
  | loop b I C ih =>
    simp only [pGCL'.pGCL, pGCL'.HeyVL, HeyVL.vp, sem_sup_apply, Globals.toList_Nodup,
      HeyVL.vp_cohavocs]
    intro σ
    if inv : IdleInvariant wp[O]⟦~C.pGCL⟧ b.sem φ.sem I.sem C.modsᶜ σ then
      simp
      left
      apply IdleInduction
      grind
    else
      simp [IdleInvariant] at inv
      obtain ⟨σ', h₁, h₂⟩ := inv
      simp [Φ] at h₂
      let Ξ := HeyVL.Subs.of (C.HeyVL O .Lower G).2.mods.toList (by simp) σ'
      have σ_eq_σ' : σ[..Ξ.help'] = σ' := by
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
      specialize ih (φ:=I ⊔ (⊤ ↜ φ)) (G:=G) (by simp [HeyLo.fv]; grind) σ'
      simp [σ_eq_σ']
      have :
            wp[O]⟦~C.pGCL⟧ I.sem σ'
          ≤ ((C.HeyVL O .Lower G).2.vp (I ⊔ (⊤ ↜ φ))).sem σ' := by
        grw [← ih]
        have : (I.sem ⊔ ((⊤ : 𝔼r).sem ↜ φ.sem)) = I.sem := by ext; simp [sem, hcoimp]
        simp [this]
      simp only at this
      simp only [ge_iff_le]
      suffices
            ¬i[b.sem σ'] * ((C.HeyVL O .Lower G).2.vp (I ⊔ (⊤ ↜ φ))).sem σ' +
              i[¬b.sem σ'] * φ.sem σ'
          ≤ I.sem (σ') by simp [this]
      grw [← this]; clear this; clear this; clear ih
      simp
      grind
  | tick r =>
    grind [pGCL'.HeyVL, HeyVL.vp, add_comm, pGCL'.pGCL, wp.tick_apply, le_refl]
  | observe r =>
    intro σ
    simp only [pGCL, wp.observe_apply, Pi.mul_apply, HeyVL, HeyVL.vp, sem_inf_apply, Ty.expr,
      sem_embed, Pi.inf_apply, Pi.top_apply, le_inf_iff]
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
    intro σ
    simp only [HeyVL, HeyVL.vp, Distribution.pure_map, Distribution.pure_toExpr, sem_add_apply,
      Ty.expr, sem_mul_apply, sem_lit_apply, Literal.sem, NNRat.ennreal_cast_one, sem_subst,
      sem_zero, Pi.add_apply, Pi.mul_apply, Exp.ennreal_coe_apply, pGCL.Exp.subst_apply, one_mul,
      Pi.zero_apply, add_zero, pGCL, wlp''.assign_apply, le_refl]
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
    · rfl
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
    if inv : IdleCoinvariant wlp''[O]⟦~C.pGCL⟧ b.sem φ.sem I.sem C.modsᶜ σ then
      simp
      left
      apply IdleCoinduction
      grind
    else
      simp [IdleCoinvariant] at inv
      obtain ⟨σ', h₁, h₂⟩ := inv
      simp [Φ] at h₂
      let Ξ := HeyVL.Subs.of (C.HeyVL O .Upper G).2.mods.toList (by simp) σ'
      have σ_eq_σ' : σ[..Ξ.help'] = σ' := by
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
      simp [this, σ_eq_σ']
      specialize ih (φ:=I ⊓ (0 ⇨ φ)) (G:=G) (by simp [HeyLo.fv]; grind) σ'
      have :
            ((C.HeyVL O .Upper G).2.vp (I ⊓ (0 ⇨ φ))).sem σ'
          ≤ wlp''[O]⟦~C.pGCL⟧ I.sem σ' := by
        grw [ih]
        simp
      simp only at this
      simp only [ge_iff_le]
      suffices ¬I.sem (σ')
          ≤ i[b.sem σ'] * ((C.HeyVL O .Upper G).2.vp (I ⊓ (0 ⇨ φ))).sem (σ')
            + i[¬b.sem σ'] * φ.sem (σ')
        by simp [this]
      grw [this]; clear this; clear this; clear ih
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
