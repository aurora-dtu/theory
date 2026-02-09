import HeyLo.pGCL'
import HeyLo.Syntax
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Lattice
import PGCL.IdleInduction

attribute [grind =] Finset.empty_union

open Optimization.Notation

open pGCL

open HeyLo

section
variable {A B : HeyLo α}
variable {x : Ident} {P : 𝔼b} {X : HeyLo x.type}

@[grind =, simp]
theorem HeyLo.sem_zero : (0 : 𝔼r).sem = 0 := by
  simp [sem]
@[grind =, simp]
theorem HeyLo.sem_one : (1 : 𝔼r).sem = 1 := by
  simp [sem]
@[grind =, simp]
theorem HeyLo.sem_var : (HeyLo.Var a t).sem σ = σ ⟨a, t⟩ := rfl
@[grind =, simp]
theorem HeyLo.sem_binop : (HeyLo.Binary op A B).sem = op.sem A.sem B.sem := rfl
@[grind =, simp]
theorem HeyLo.sem_unop : (HeyLo.Unary op A).sem = op.sem A.sem := rfl
open scoped Classical in
@[grind =, simp]
theorem HeyLo.sem_eq : (HeyLo.Binary .Eq A B).sem = fun σ ↦ A.sem σ = B.sem σ := by
  ext σ
  simp [sem, BinOp.sem]

variable {A B : 𝔼r}

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
theorem HeyLo.sem_subst_apply : P[x ↦ X].sem σ = P.sem σ[x ↦ X.sem σ] := rfl
@[grind =, simp]
theorem HeyLo.sem_iver : P.iver.sem = i[P.sem] := rfl
@[grind =, simp]
theorem HeyLo.sem_embed : P.embed.sem = i[P.sem] * ⊤ := rfl
@[grind =, simp]
theorem HeyLo.sem_not_apply : P.not.sem = ￢P.sem := rfl

@[grind =, simp]
theorem HeyLo.sem_subt_var {v : Ty.expr x.type} : (HeyLo.Var x.name x.type).sem[x ↦ v] = v := by
  simp [sem, Substitution.substs, Substitution.subst]

@[grind =, simp]
theorem HeyLo.substs_inf {A B : 𝔼r} : (A ⊓ B).sem[..xs] = A.sem[..xs] ⊓ B.sem[..xs] :=
  Substitution.substs_of_binary (m:=A.sem) fun _ _ ↦ congrFun rfl

end

abbrev Globals := Finset Ident
def Globals.fresh (G : Globals) (α : Ty) : Globals × Ident :=
  let seen : Finset Ident := G
  if h : seen = ∅ then
    let new : Ident := Ident.mk "f₀" α
    (({new} : Finset Ident), new)
  else
    let longest := seen.image (·.name.length) |>.max' (by simp [Finset.nonempty_iff_ne_empty, h])
    let new : Ident := Ident.mk ("f" ++ String.replicate longest '₀') α
    (seen ∪ {new}, new)
theorem Globals.fresh_type (G : Globals) : (G.fresh ty).2.type = ty := by
  grind [fresh]
theorem Globals.fresh_update (G : Globals) : (fresh G ty).1 = insert (fresh G ty).2 G := by
  grind [fresh]
theorem Globals.fresh_not_in (G : Globals) : (fresh G ty).2 ∉ G := by
  simp [fresh]
  split_ifs
  · grind
  · simp
    have : ∀ (F : Finset Ident) (x : Ident), x ∉ F ↔ ∀ y ∈ F, x ≠ y :=
      fun F x ↦ Iff.symm Finset.forall_mem_not_eq
    apply (this _ _).mpr; clear this
    intro y hy
    have : ∀ {x y : Ident}, x ≠ y ↔ x.name ≠ y.name ∨ x.type ≠ y.type := by
      rintro ⟨_, _⟩ ⟨_, _⟩
      simp; grind
    apply this.mpr; clear this
    simp
    left
    apply (by grind : ∀ {x y : String}, x.length ≠ y.length → x ≠ y)
    simp_all [String.replicate]
    apply ne_of_gt (Nat.lt_one_add_iff.mpr (Finset.le_max' _ _ _))
    grind

attribute [grind =, simp] Globals.fresh_type
attribute [grind =, simp] Globals.fresh_update
attribute [grind ., simp] Globals.fresh_not_in

open Globals

@[grind, simp]
def HeyLo.fv (C : HeyLo α) : Globals :=
  match C with
  | .Binary _ S₁ S₂ => S₁.fv ∪ S₂.fv
  | .Lit _ => ∅
  | .Subst v e m => {v} ∪ e.fv ∪ m.fv
  | .Call _ m => m.fv
  -- NOTE: we need to include `x` for complete-substitution purposes
  | .Quant _ x m => {x} ∪ m.fv
  | .Ite b l r => b.fv ∪ l.fv ∪ r.fv
  | .Var x t => {⟨x, t⟩}
  | .Unary _ m => m.fv
def Distribution.fv (D : Distribution α) : Globals :=
  D.values.toList.map (fun (x, y) ↦ x.fv ∪ y.fv) |>.toFinset.biUnion (·)
@[grind]
def pGCL'.fv (C : pGCL') : Globals :=
  match C with
  | .seq S₁ S₂ => S₁.fv ∪ S₂.fv
  | .skip => ∅
  | .observe o => o.fv
  | .tick r => r.fv
  | .ite b S₁ S₂ => b.fv ∪ S₁.fv ∪ S₂.fv
  | .loop b c I => b.fv ∪ c.fv ∪ I.fv
  | .nonDet S₁ S₂ => S₁.fv ∪ S₂.fv
  | .prob S₁ p S₂ => S₁.fv ∪ p.fv ∪ S₂.fv
  | .assign x e => {x} ∪ e.fv
@[grind, simp]
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

@[grind, simp]
def pGCL'.mods (C : pGCL') : Globals :=
  match C with
  | .seq S₁ S₂ => S₁.mods ∪ S₂.mods
  | .skip => ∅
  | .observe _ => ∅
  | .tick _ => ∅
  | .loop _ _ c => c.mods
  | .ite _ S₁ S₂ => S₁.mods ∪ S₂.mods
  | .nonDet S₁ S₂ => S₁.mods ∪ S₂.mods
  | .prob S₁ _ S₂ => S₁.mods ∪ S₂.mods
  | .assign x _ => {x}
@[grind, simp]
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

@[grind, simp]
def pGCL'.invs (C : pGCL') : Finset 𝔼r :=
  match C with
  | .seq S₁ S₂ => S₁.invs ∪ S₂.invs
  | .skip => ∅
  | .observe _ => ∅
  | .tick _ => ∅
  | .loop _ I c => insert I c.invs
  | .ite _ S₁ S₂ => S₁.invs ∪ S₂.invs
  | .nonDet S₁ S₂ => S₁.invs ∪ S₂.invs
  | .prob S₁ _ S₂ => S₁.invs ∪ S₂.invs
  | .assign _ _ => ∅
@[grind, simp]
def pGCL'.invsList_aux (C : pGCL') : List 𝔼r :=
  match C with
  | .seq S₁ S₂ => S₁.invsList_aux ++ S₂.invsList_aux
  | .skip => ∅
  | .observe _ => ∅
  | .tick _ => ∅
  | .loop _ I c => I :: c.invsList_aux
  | .ite _ S₁ S₂ => S₁.invsList_aux ++ S₂.invsList_aux
  | .nonDet S₁ S₂ => S₁.invsList_aux ++ S₂.invsList_aux
  | .prob S₁ _ S₂ => S₁.invsList_aux ++ S₂.invsList_aux
  | .assign _ _ => ∅
@[grind, simp]
def pGCL'.invsList (C : pGCL') : List 𝔼r := C.invsList_aux.dedup

@[grind =, simp]
theorem pGCL'.mem_invsList_iff : I ∈ pGCL'.invsList C ↔ I ∈ C.invs := by
  fun_induction invs <;> simp_all

@[grind ., simp]
theorem HeyVL.mods_subset_fv (C : HeyVL) : C.mods ⊆ C.fv := by
  fun_induction mods <;> grind

@[grind =, simp]
theorem HeyVL.Skip_fv : HeyVL.Skip.fv = {} := rfl
@[grind =, simp]
theorem HeyVL.Havocs_fv {xs : List Ident} : (HeyVL.Havocs xs).fv = xs.toFinset := by
  fun_induction Havocs <;> simp [*]
@[grind =, simp]
theorem HeyVL.Cohavocs_fv {xs : List Ident} : (HeyVL.Cohavocs xs).fv = xs.toFinset := by
  fun_induction Cohavocs <;> simp [*]
@[grind =, simp]
theorem HeyLo.subst_fv (φ : HeyLo α) (y : HeyLo x.type) :
    φ[x ↦ y].fv = {x} ∪ φ.fv ∪ y.fv := by
  simp only [Substitution.subst_singleton, Substitution.subst, subst, HeyLo.fv,
    Finset.singleton_union, Finset.insert_union]
  grind

@[grind =, simp]
theorem Distribution.toExpr_fv {μ : Distribution .ENNReal} : μ.toExpr.fv = μ.fv := by
  obtain ⟨⟨values⟩, h⟩ := μ
  simp [toExpr, fv]
  clear! h
  induction values with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, HeyLo.fv]
    grind [List.toFinset_cons, Finset.biUnion_insert]

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

theorem HeyVL.havoc_alt {φ : 𝔼r} :
    ((HeyVL.Havoc x).vp φ).sem = ⨅ (v : x.type.lit), φ.sem[x ↦ fun _ ↦ v] := rfl
theorem HeyVL.cohavoc_alt {φ : 𝔼r} :
    ((HeyVL.Cohavoc x).vp φ).sem = ⨆ (v : x.type.lit), φ.sem[x ↦ fun _ ↦ v] := rfl

theorem HeyVL.havoc_comm {φ : 𝔼r} :
    (vp⟦havoc(~x) ; havoc(~y)⟧ φ).sem = (vp⟦havoc(~y) ; havoc(~x)⟧ φ).sem := by
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

structure HeyVL.Subs (Vars : List Ident) (hn : Vars.Nodup) where
  values : List ((x : Ident) × x.type.lit)
  prop : Vars.length = values.length
  prop' : ∀ (i : Fin Vars.length), values[i].1 = Vars[i]

instance : Inhabited (HeyVL.Subs xs hn) where
  default := ⟨xs.map (fun x ↦ ⟨x, default⟩), by simp, by simp⟩

attribute [grind .] HeyVL.Subs.prop
attribute [grind =] HeyVL.Subs.prop'

@[grind =, simp]
theorem HeyVL.Subs.values_nil (S : Subs [] hn) : S.values = [] := by
  grind [List.eq_nil_iff_length_eq_zero, cases Subs]

def HeyVL.Subs.cons (S : Subs xs hn) (x : Ident) (v : x.type.lit) (hv : x ∉ xs) :
    Subs (x :: xs) (by grind) :=
  ⟨⟨x, v⟩::S.values, by obtain ⟨S, hS, hS'⟩ := S; grind, by
    obtain ⟨S, hS, hS'⟩ := S; simp
    rintro ⟨(_ | n), hn⟩
    · simp_all
    · simp_all; apply hS' ⟨n, by omega⟩⟩
def HeyVL.Subs.tail (S : Subs (x :: xs) hn) : x.type.lit × Subs xs (List.Nodup.of_cons hn) :=
  let q : ((x : Ident) × x.type.lit) := S.values[0]'(by obtain ⟨S, hS, hS'⟩ := S; grind)
  let val := cast (by simp [q]; congr; have := S.prop' ⟨0, by simp⟩; grind) q.snd
  (val, ⟨S.values.tail, by obtain ⟨S, hS⟩ := S; grind, by
    simp_all only [Fin.getElem_fin, List.getElem_tail]
    intro i
    exact S.prop' ⟨(i + 1), by simp_all⟩⟩)

theorem HeyVL.Subs.tail_bij : Function.Bijective (Subs.tail (x:=x) (xs:=xs) (hn:=hn)) := by
  refine Function.bijective_iff_has_inverse.mpr ?_
  use fun (a, b) ↦ ⟨⟨x, a⟩ :: b.values, by obtain ⟨b, hb⟩ := b; grind, by
    simp
    rintro ⟨(_ | i), hi⟩
    · simp
    · simp; have := b.prop' ⟨i, by omega⟩; grind⟩
  simp
  constructor
  · intro ⟨S, hS, hS'⟩
    simp [tail]
    have : S ≠ [] := by grind
    convert List.cons_head_tail this
    · simp; rw [List.head_eq_getElem]
      specialize hS' ⟨0, by simp⟩
      exact hS'.symm
    · rw [List.head_eq_getElem]; simp
  · intro ⟨a, S, hS, hS'⟩
    simp_all [tail]

@[grind =, simp]
theorem HeyVL.Subs.values_length (S : Subs xs hn) : S.values.length = xs.length := by
  obtain ⟨S, hS⟩ := S
  grind
def HeyVL.Subs.help (S : Subs xs hn) : List ((v : Ident) × 𝔼'[v.type.lit]) :=
  S.values.map (fun a ↦ ⟨a.1, fun _ ↦ a.2⟩)
def HeyVL.Subs.help' (S : Subs xs hn) : List ((v : Ident) × v.type.lit) :=
  S.values
@[grind =, simp]
theorem HeyVL.Subs.help_length (S : Subs xs hn) : S.help.length = xs.length := by
  obtain ⟨S, hS⟩ := S
  simp [help]
  grind
@[grind =, simp]
theorem HeyVL.Subs.help_cons (S : Subs (x :: xs) hn) :
    S.help = ⟨x, fun _ ↦ S.tail.1⟩ :: S.tail.2.help := by
  simp [help, tail]
  apply List.ext_getElem
  · simp
  · simp_all only [List.length_map, values_length, List.length_cons, List.length_tail,
    add_tsub_cancel_right, List.getElem_map, forall_true_left]
    intro i hi
    have := S.prop' ⟨i, by simp [hi]⟩
    simp at this
    rcases i with _ | i
    · simp_all [Function.hfunext]
    · simp
@[grind =, simp]
theorem HeyVL.Subs.help'_cons (S : Subs (x :: xs) hn) :
    S.help' = ⟨x, ↑S.tail.1⟩ :: S.tail.2.help' := by
  simp [help', tail]
  apply List.ext_getElem
  · simp
  · simp_all only [Ty.lit, values_length, List.length_cons, List.length_tail,
    add_tsub_cancel_right, forall_true_left]
    intro i hi
    have := S.prop' ⟨i, by simp [hi]⟩
    simp at this
    rcases i with _ | i
    · simp_all
      congr!
      simp
    · simp

def HeyVL.Subs.get (S : Subs xs hn) (x : Ident) (hx : x ∈ xs) : x.type.lit :=
  cast
    (by congr; convert S.prop' ⟨List.findIdx (· = x) xs, by simp [hx]⟩; grind)
    (S.values[xs.findIdx (· = x)]'(by grind)).snd
@[grind =, simp]
theorem HeyVL.Subs.tail_get (S : Subs (x :: xs) hn) (y : Ident) (hy : y ∈ xs) :
    S.tail.2.get y hy = S.get y (by grind) := by
  simp [tail, get]
  grind
@[grind =]
theorem HeyVL.Subs.tail_1_eq_get (S : Subs (x :: xs) hn) :
    S.tail.1 = S.get x (by grind) := by
  simp [tail, get]
  grind

@[grind =, simp]
theorem HeyVL.Subs.subst_help'_apply (S : Subs xs hn) (σ : States fun (x : Ident) ↦ x.type.lit) :
    σ[..S.help'] y = if h : y ∈ xs then S.get y h else σ y := by
  induction xs generalizing y with
  | nil => simp [HeyVL.Subs.help']
  | cons x xs ih =>
    simp
    rw [Substitution.substs_cons_substs]
    grind

@[simp]
theorem HeyVL.vp_havocs (h : xs.Nodup) :
    (vp⟦havocs(~xs)⟧ φ).sem = ⨅ (vs : Subs xs hn), φ.sem[..vs.help] := by
  rcases xs with _ | ⟨x, xs⟩
  · ext σ; simp [Havocs, Skip, vp, Subs.help]
  induction xs generalizing x φ with
  | nil =>
    ext σ
    simp [HeyVL.havoc_alt, Havocs]
    apply Function.Surjective.iInf_congr fun y ↦ ⟨[⟨_, y⟩], by simp, by simp⟩
    · intro ⟨e, h, h'⟩
      simp at h h' ⊢
      rcases e with _ | y
      · simp at h
      simp only [List.length_cons, Nat.right_eq_add, List.length_eq_zero_iff] at h
      subst_eqs
      simp_all only [List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self,
        Ty.lit, List.getElem_cons_zero, List.cons.injEq, and_true]
      subst_eqs
      simp
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
    ((HeyVL.Cohavocs xs).vp φ).sem = ⨆ (vs : Subs xs hn), φ.sem[..vs.help] := by
  rcases xs with _ | ⟨x, xs⟩
  · ext σ; simp [Cohavocs, Skip, vp, Subs.help]
  induction xs generalizing x φ with
  | nil =>
    ext σ
    simp [HeyVL.cohavoc_alt, Cohavocs]
    apply Function.Surjective.iSup_congr fun y ↦ ⟨[⟨_, y⟩], by simp, by simp⟩
    · intro ⟨e, h, h'⟩
      simp at h h' ⊢
      rcases e with _ | y
      · simp at h
      simp only [List.length_cons, Nat.right_eq_add, List.length_eq_zero_iff] at h
      subst_eqs
      simp_all only [List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self,
        Ty.lit, List.getElem_cons_zero, List.cons.injEq, and_true]
      subst_eqs
      simp
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
theorem HeyVL.if_vp_sem {φ : 𝔼r} :
    ((HeyVL.If b S₁ S₂).vp φ).sem = i[b.sem] * (S₁.vp φ).sem + i[b.not.sem] * (S₂.vp φ).sem := by
  ext σ
  simp [If, vp]
  by_cases h : b.sem σ <;> simp [h, Iverson.iver]

def Substitution.applied (σ : States fun (x : Ident) ↦ x.type.lit) (xs : List ((v : Ident) × 𝔼'[v.type.lit])) :
    States fun (x : Ident) ↦ x.type.lit :=
  match xs with
  | [] => σ
  | x::xs => Substitution.applied σ[x.1 ↦ x.2 σ] xs

theorem BExpr.subst_applied {b : BExpr fun (x : Ident) ↦ x.type.lit} {xs : List ((v : Ident) × 𝔼'[v.type.lit])} :
    b[..xs] = fun σ ↦ b (Substitution.applied σ xs) := by
  ext σ
  induction xs generalizing σ with
  | nil => simp [Substitution.applied]
  | cons x xs ih => simp_all [Substitution.applied]

theorem BExpr.subst_apply {b : BExpr fun (x : Ident) ↦ x.type.lit} {xs : List ((v : Ident) × 𝔼'[v.type.lit])} :
    b[..xs] σ = b (Substitution.applied σ xs) := by
  rw [subst_applied]

theorem Exp.subst_applied {b : 𝔼'[α]} {xs : List ((v : Ident) × 𝔼'[v.type.lit])} :
    b[..xs] = fun σ ↦ b (Substitution.applied σ xs) := by
  ext σ
  induction xs generalizing σ with
  | nil => simp [Substitution.applied]
  | cons x xs ih => simp_all [Substitution.applied]

theorem Exp.subst_apply {b : 𝔼'[α]} {xs : List ((v : Ident) × 𝔼'[v.type.lit])} :
    b[..xs] σ = b (Substitution.applied σ xs) := by
  rw [subst_applied]

@[grind =, simp]
theorem Exp.substs_help_apply (m : 𝔼'[α]) (Ξ : HeyVL.Subs xs hxs) :
    m[..Ξ.help] σ = m σ[..Ξ.help'] := by
  rw [Exp.subst_apply]
  congr
  induction xs generalizing σ with
  | nil => simp [HeyVL.Subs.help, HeyVL.Subs.help', Substitution.applied]
  | cons x xs ih =>
    simp [HeyVL.Subs.help_cons, Substitution.applied, ih]
    clear ih
    simp only [Substitution.substs_cons_substs, Substitution.substs_nil]
    simp only [Substitution.substs_nil]
    ext y
    grind
@[grind =, simp]
theorem BExpr.substs_help_apply (m : BExpr fun (x : Ident) ↦ x.type.lit) (Ξ : HeyVL.Subs xs hxs) :
    m[..Ξ.help] σ = m σ[..Ξ.help'] := by
  rw [BExpr.subst_apply]
  congr
  induction xs generalizing σ with
  | nil => simp [HeyVL.Subs.help, HeyVL.Subs.help', Substitution.applied]
  | cons x xs ih =>
    simp [HeyVL.Subs.help_cons, Substitution.applied, ih]
    clear ih
    simp only [Substitution.substs_cons_substs, Substitution.substs_nil]
    simp only [Substitution.substs_nil]
    ext y
    grind

theorem HeyLo.sem_substs_apply (m : HeyLo α) :
    m.sem[..xs] σ = m.sem (Substitution.applied σ xs) := by
  cases α <;> simp [Exp.subst_apply]
theorem HeyLo.sem_substs_apply' (m : HeyLo α) (Ξ : HeyVL.Subs xs hxs) :
    m.sem[..Ξ.help] σ = m.sem σ[..Ξ.help'] := by
  cases α <;> simp
theorem Substitution.applied_subst (σ : States fun (x : Ident) ↦ x.type.lit) (xs : List ((v : Ident) × 𝔼'[v.type.lit]))
    (v : 𝔼'[_]) :
      (Substitution.applied σ xs)[x ↦ v (Substitution.applied σ xs)]
    = Substitution.applied σ (xs ++ [⟨x, v⟩]) := by
  induction xs generalizing σ x v with
  | nil => simp [applied]
  | cons y xs ih =>
    simp_all [applied]

def HeyVL.Subs.of (xs : List Ident) (hn : xs.Nodup) (σ : States fun (x : Ident) ↦ x.type.lit) :
    HeyVL.Subs xs hn := ⟨xs.map fun x ↦ ⟨x, σ x⟩, by simp, by simp⟩
@[grind =, simp]
theorem HeyVL.Subs.of_get (xs : List Ident) (hn : xs.Nodup) (σ : States fun (x : Ident) ↦ x.type.lit) {y} {hy} :
    (Subs.of xs hn σ).get y hy = σ y := by simp [Subs.of, Subs.get]; grind

@[grind =, simp]
theorem HeyLo.sem_indep {α : Ty} {φ : HeyLo α} {x : Ident} (h : x ∉ φ.fv) :
    Substitution.IsIndepPair φ.sem x := by
  intro v
  induction φ generalizing v with
    (simp [fv] at h; simp_all only [not_false_eq_true, Ty.expr, forall_const])
  | Var y => grind [sem]
  | Lit l =>
    simp [sem]; split <;> try rfl
    split <;> rfl
  | Ite b S₁ S₂ ihb ih₁ ih₂ =>
    simp [funext_iff, *] at ihb
    classical
    cases ‹Ty›
    · ext σ
      simp [sem]
      simp [funext_iff, *] at ih₁
      simp [funext_iff, *] at ih₂
      simp_all
    · ext σ
      simp [sem]
      simp [funext_iff, *] at ih₁
      simp [funext_iff, *] at ih₂
      simp_all only
    · ext σ
      simp [sem]
      simp [funext_iff, *] at ih₁
      simp [funext_iff, *] at ih₂
      simp_all
  | Subst y w m ih₁ ih₂ =>
    simp [sem]
    replace ih₁ : ∀ (v : x.type.lit), w.sem[x ↦ fun _ ↦ v] = w.sem := by grind
    replace ih₂ : ∀ (v : x.type.lit), m.sem[x ↦ fun _↦ v] = m.sem := by grind
    simp [funext_iff, *] at ih₁
    cases ‹Ty›
    · ext σ
      simp [funext_iff, *] at ih₂
      grind
    · ext σ
      simp [funext_iff, *] at ih₂
      grind
    · ext σ
      simp [funext_iff, *] at ih₂
      grind
  | Call op m ih =>
    cases op
    · ext σ
      replace ih := (congrFun (ih v) σ)
      simp_all only [Ty.lit, pGCL.Exp.subst_apply, sem, Fun.sem]
    · ext σ
      replace ih := (congrFun (ih v) σ)
      simp_all only [Ty.lit, pGCL.Exp.subst_apply, sem, Fun.sem]
    · ext σ
      replace ih := (congrFun (ih v) σ)
      simp_all only [Ty.lit, pGCL.Exp.subst_apply, sem, Fun.sem]
      simp_all
  | Quant op y m ih =>
    cases op
    · ext σ
      simp
      replace ih := (congrFun (ih (fun _ ↦ v σ)) σ[y ↦ ·])
      grind
    · ext σ
      simp
      replace ih := (congrFun (ih (fun _ ↦ v σ)) σ[y ↦ ·])
      grind
    · ext σ
      simp
      replace ih := (congrFun (ih (fun _ ↦ v σ)) σ[y ↦ ·])
      grind
    · ext σ
      simp
      replace ih := (congrFun (ih (fun _ ↦ v σ)) σ[y ↦ ·])
      grind
  | Unary => simp; grind
  | Binary => simp; grind

@[grind =, simp]
theorem HeyVL.Cohavocs_mods : (HeyVL.Cohavocs xs).mods = ∅ := by
  fun_induction Cohavocs with simp_all [mods, HeyVL.Skip]

@[grind =, simp]
theorem pGCL'.pGCL_mods (C : pGCL') : C.pGCL.mods = ↑C.mods := by
  induction C with simp_all [mods, pGCL, pGCL.mods, pGCL.ite]

inductive Direction where
  /-- Corresponds to `gfp` -/
  | Upper
  /-- Corresponds to `lfp` -/
  | Lower

def pGCL'.HeyVL (C : pGCL') (O : Optimization) (D : Direction) (G : Globals) :
    Globals × HeyVL :=
  match C with
  | skip => (G, .Skip)
  | assign x e => (G, heyvl {~x :≈ ~(.pure e)})
  | seq C₁ C₂ =>
    let (G, C₂) := C₂.HeyVL O D G
    let (G, C₁) := C₁.HeyVL O D G
    (G, heyvl{~C₁ ; ~C₂})
  | prob C₁ p C₂ =>
    let (G, C₂) := C₂.HeyVL O D G
    let (G, C₁) := C₁.HeyVL O D G
    let (G, choice) := fresh G .Nat
    -- (G,
    --   .Assign ⟨choice.name, .Nat⟩ (.bin 0 p 1) ;;
    --   .If (.Binary .Eq (.Var choice.name .Nat) 0) C₁ C₂)
    (G, heyvl {
      ~⟨choice.name, .Nat⟩ :≈ ~(.bin 0 p 1); if (~(.Var choice.name .Nat) = 0) {~C₁} else {~C₂}})
  | nonDet C₁ C₂ =>
    let (G, C₂) := C₂.HeyVL O D G
    let (G, C₁) := C₁.HeyVL O D G
    match O with
    | 𝒜 => (G, heyvl {if (⊔) {~C₁} else {~C₂}})
    | 𝒟 => (G, heyvl {if (⊓) {~C₁} else {~C₂}})
  | ite b C₁ C₂ =>
    let (G, C₂) := C₂.HeyVL O D G
    let (G, C₁) := C₁.HeyVL O D G
    (G, heyvl {if (~b) {~C₁} else {~C₂}})
  | loop b I C =>
    let (G, C) := C.HeyVL O D G ;
    match D with
    -- NOTE: wp encoding
    | .Lower => (G, heyvl {
        coassert(~I) ;
        cohavocs(~C.mods.sort) ;
        covalidate ;
        coassume(~I) ;
        if (~b) { ~C ; coassert(~I); coassume(~⊤) }
      })
    -- NOTE: wlp encoding
    | .Upper => (G, heyvl {
        assert(~I) ;
        havocs(~C.mods.sort) ;
        validate ;
        assume(~I) ;
        if (~b) { ~C ; assert(~I); assume(~0) }
      })
  | tick r =>
    match D with
    -- NOTE: wp encoding
    | .Lower => (G, heyvl { reward(~ r) })
    -- NOTE: wlp encoding
    -- HACK: we include `r` as a subexpression such that `fv` is the same in both cases
    | .Upper => (G, heyvl { reward(0 * ~ r) })
  | observe r => (G, heyvl { assert(~ r.embed) })

@[grind ., grind! ., simp]
theorem pGCL'.HeyVL_G_mono {C : pGCL'} : G ⊆ (C.HeyVL O D G).1 := by
  fun_induction HeyVL <;> try simp_all
  next => trans <;> assumption
  next ih₁ ih₂ =>
    apply trans ih₁
    apply trans ih₂
    grind
  next => trans <;> assumption
  next => trans <;> assumption
  next => trans <;> assumption
@[grind =, simp]
theorem pGCL'.fv_HeyVL_subset {C : pGCL'} :
    (C.HeyVL O D G).2.fv = C.fv ∪ ((C.HeyVL O D G).1 \ G) := by
  induction C generalizing G with
    simp_all [pGCL'.HeyVL, fv, embed, HeyLo.not, HeyVL.fv, HeyVL.Skip, HeyVL.If, HeyLo.fv]
  | assign => simp [Distribution.pure, Distribution.fv]
  | seq C₁ C₂ ih₁ ih₂ => grind
  | tick r => cases D <;> simp [HeyVL.fv]
  | nonDet C₁ C₂ ih₁ ih₂ => grind
  | ite b C₁ C₂ ih₁ ih₂ => grind
  | prob C₁ p C₂ ih₁ ih₂ =>
    simp only [Distribution.fv, Distribution.bin, List.map_cons, HeyLo.fv, Finset.union_empty,
      Finset.empty_union, List.map_nil, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_singleton, Finset.insert_eq_of_mem, Finset.singleton_biUnion]
    ext a
    simp_all only [Finset.mem_insert, Finset.mem_union, Finset.mem_sdiff]
    have :
        a = { name := ((C₁.HeyVL O D (C₂.HeyVL O D G).1).1.fresh Ty.Nat).2.name, type := Ty.Nat }
        ↔ a = ((C₁.HeyVL O D (C₂.HeyVL O D G).1).1.fresh Ty.Nat).2 := by
      refine Eq.congr_right ?_
      congr
      grind
    constructor
    · rintro (h | h | h | h | h) <;> try grind
    · grind
  | loop b I C ih =>
    have := (C.HeyVL O D G).2.mods_subset_fv
    cases D
    · simp only [HeyVL.fv, HeyVL.Havocs_fv, Finset.sort_toFinset, HeyLo.fv, Finset.union_empty,
      Finset.union_assoc, Finset.empty_union]
      grind
    · simp only [HeyVL.fv, HeyVL.Cohavocs_fv, Finset.sort_toFinset, HeyLo.fv, Finset.union_empty,
      Finset.union_assoc, Finset.empty_union]
      grind

@[grind ., simp]
theorem pGCL'.HeyVL_mods (C : pGCL') : C.mods ⊆ (C.HeyVL O D G).2.mods := by
  induction C generalizing G with simp_all [mods, HeyVL, HeyVL.mods, HeyVL.If] <;> try grind
  | loop => cases D <;> simp_all only [HeyVL.mods] <;> grind

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

@[grind =_, simp] theorem Iverson.iver_bool_eq_true {b : Bool} : i[b = true] = i[b] := by
  simp [Iverson.iver]
@[simp] theorem Iverson.iver_bool_eq_false {b : Bool} : i[b = false] = i[¬b] := by
  simp [Iverson.iver]

def pGCL'.vp (C : pGCL') (O : Optimization) (D : Direction) (φ : 𝔼r) :=
  (C.HeyVL O D (C.fv ∪ φ.fv)).2.vp φ

@[simp]
theorem HeyLo.ofNat_ident (n : String) :
      @OfNat.ofNat (HeyLo ({ name := n, type := Ty.Nat } : Ident).type) 0 instOfNatHeyLoNat
    = (0 : HeyLo .Nat) := by simp
@[grind =, simp]
theorem HeyLo.ofNat_sem (n : ℕ) : sem (@OfNat.ofNat (HeyLo .Nat) n instOfNatHeyLoNat) σ = n := by
  simp [sem]
@[grind =, simp]
theorem HeyLo.nat_zero_sem : sem (0 : HeyLo .Nat) = 0 := by simp [sem] @[grind =, simp]
theorem HeyLo.nat_one_sem : sem (1 : HeyLo .Nat) = 1 := by simp [sem]


theorem pGCL'.prob_vp {C₁ C₂ : pGCL'} {G : Globals} (hG : (C₁.prob p C₂).fv ∪ φ.fv ⊆ G) :
      (((C₁.prob p C₂).HeyVL O D G).2.vp φ).sem
    =   (p.sem ⊓ 1) * ((C₁.HeyVL O D (C₂.HeyVL O D G).1).2.vp φ).sem
      + (1 - p.sem ⊓ 1) * ((C₂.HeyVL O D G).2.vp φ).sem := by
  simp_all only [Ty.expr, Ty.lit, HeyVL, fresh_update, ofNat_ident, HeyVL.If, HeyVL.vp,
    Distribution.bin_map, Distribution.bin_toExpr, sem_add_apply, sem_mul_apply, sem_inf_apply,
    sem_one, sem_subst, sem_himp_apply, sem_embed, sem_binop, sem_not_apply, hnot_eq_compl,
    Exp.min_subst, Exp.himp_subst, Exp.mul_subst, Pi.iver_subst, BinOp.sem_subst, HeyLo.fv,
    Finset.notMem_empty, not_false_eq_true, sem_indep, Substitution.indep_pair, Exp.top_subst,
    Exp.not_subst, sem_sub_apply, sem_zero, add_zero]
  simp [BinOp.sem]
  have : i[fun (σ : States Ty.ϖ) ↦ True] = 1 := by ext; simp
  have : i[(fun (σ : States Ty.ϖ) ↦ True)ᶜ] = 0 := by ext; simp
  have : i[fun (σ : States Ty.ϖ) ↦ False] = 0 := by ext; simp
  have : i[(fun (σ : States Ty.ϖ) ↦ False)ᶜ] = 1 := by ext; simp
  simp [*]
  have :
      { name := ((C₁.HeyVL O D (C₂.HeyVL O D G).1).1.fresh Ty.Nat).2.name, type := Ty.Nat }
    = ((C₁.HeyVL O D (C₂.HeyVL O D G).1).1.fresh Ty.Nat).2 := by
    ext
    · rfl
    · simp
  rw [Substitution.indep_pair, Substitution.indep_pair]
  rotate_left
  · apply HeyLo.sem_indep
    grind
  · apply HeyLo.sem_indep
    grind

theorem ENNReal.covalidate_hcoimp {a b : ENNReal} : ▿ (a ↜ b) = if b ≤ a then 0 else ⊤ := by
  simp [covalidate, himp, hconot, hcoimp]
  grind [zero_ne_top, _root_.not_lt_zero]

set_option maxHeartbeats 500000 in
theorem pGCL'.wp_le_vp_aux {C : pGCL'} {G : Globals} (hG : C.fv ∪ φ.fv ⊆ G) :
    wp[O]⟦~C.pGCL⟧ φ.sem ≤ ((C.HeyVL O .Lower G).2.vp φ).sem := by
  induction C generalizing G φ with
  | skip =>
    intro σ
    simp only [Ty.lit, pGCL, wp.skip_apply, HeyVL, HeyVL.Skip, HeyVL.vp, sem_add_apply, Ty.expr,
      sem_zero, Pi.add_apply, Pi.ofNat_apply, add_zero, le_refl]
  | assign x e => simp [pGCL'.HeyVL, HeyVL.vp, pGCL'.pGCL]
  | seq C₁ C₂ ih₁ ih₂ =>
    simp only [pGCL'.HeyVL, HeyVL.vp, pGCL'.pGCL, wp.seq_apply]
    grw [← ih₁, ← ih₂]
    · grind
    · simp
      grind
  | ite b C₁ C₂ ih₁ ih₂ =>
    simp only [pGCL, pGCL.ite, wp.prob_apply, HeyVL, HeyVL.if_vp_sem, Ty.expr, sem_not_apply]
    simp only [fv, Finset.union_assoc] at hG
    grw [← ih₁, ← ih₂]
    · intro σ; simp only [Ty.lit, ProbExp.pick, Pi.add_apply, Pi.mul_apply, BExpr.probOf_apply,
      Pi.sub_apply, Pi.ofNat_apply, hnot_eq_compl, Pi.iver_apply, Pi.compl_apply, compl_iff_not,
      Iverson.iver_neg, ENNReal.natCast_sub, Nat.cast_one, le_refl]
    · grind
    · grind
  | nonDet C₁ C₂ ih₁ ih₂ =>
    simp [pGCL'.fv] at hG
    simp only [pGCL, wp.nonDet_apply, Optimization.opt₂, HeyVL]
    cases O
    · simp only [HeyVL.vp, sem_sup_apply]
      grw [← ih₁, ← ih₂] <;> grind
    · simp only [HeyVL.vp, sem_inf_apply]
      grw [← ih₁, ← ih₂] <;> grind
  | prob C₁ p C₂ ih₁ ih₂ =>
    simp only [Ty.lit, pGCL'.prob_vp hG, Ty.expr]
    grw [← ih₁, ← ih₂]
    · intro σ; rfl
    · grind
    · calc
        C₁.fv ∪ φ.fv ⊆ C₁.fv ∪ (C₂.fv ∪ φ.fv) := by grind
        _ ⊆ G := by grind
        _ ⊆ (C₂.HeyVL O .Lower G).1 := by grind
  | loop b I C ih =>
    simp only [Ty.lit, pGCL, HeyVL, HeyVL.vp, sem_sup_apply, Ty.expr, Finset.sort_nodup,
      HeyVL.vp_cohavocs, sem_covalidate, sem_hcoimp_apply, HeyVL.if_vp_sem, sem_not_apply,
      hnot_eq_compl, Exp.covalidate_subst, Exp.hcoimp_subst, Exp.add_subst, Exp.mul_subst]
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
      let Ξ := HeyVL.Subs.of (C.HeyVL O .Lower G).2.mods.sort (by simp) σ'
      have σ_eq_σ' : σ[..Ξ.help'] = σ' := by
        ext x
        simp +contextual [Ξ]
        intro h
        specialize h₁ x (by contrapose! h; exact C.HeyVL_mods h)
        simp_all only
      simp_all only [Ty.lit, Exp.iver_subst, Exp.not_subst, Pi.sup_apply, iSup_apply,
        Exp.covalidate_apply, Exp.hcoimp_apply, Exp.substs_help_apply, Pi.add_apply, Pi.mul_apply,
        Pi.iver_apply, Pi.compl_apply, compl_iff_not, le_sup_iff]
      right
      apply le_iSup_of_le Ξ
      simp [HeyVL.vp, HeyVL.Skip]
      simp [ENNReal.covalidate_hcoimp]
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
      grw [← this]; clear this; clear ih
      simp
      grind
  | tick r =>
    grind [pGCL'.HeyVL, HeyVL.vp, add_comm, pGCL'.pGCL, wp.tick_apply, le_refl]
  | observe r =>
    intro σ
    simp only [Ty.lit, pGCL, wp.observe_apply, Pi.mul_apply, Pi.iver_apply, HeyVL, HeyVL.vp,
      sem_inf_apply, Ty.expr, sem_embed, Pi.inf_apply, Pi.top_apply, le_inf_iff,
      BExpr.iver_mul_le_apply, and_true]
    if r.sem σ then simp_all [Iverson.iver] else simp_all

theorem pGCL'.wp_le_vp {C : pGCL'} :
    wp[O]⟦~C.pGCL⟧ φ.sem ≤ (C.vp O .Lower φ).sem := wp_le_vp_aux (by rfl)

/-- info: 'pGCL'.wp_le_vp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pGCL'.wp_le_vp

@[grind ., simp]
theorem pGCL.wlp''_le_one [DecidableEq 𝒱] {ϖ : Γ[𝒱]} {C : pGCL ϖ} {φ} : wlp''[O]⟦~C⟧ φ ≤ 1 := by
  intro; simp [wlp'']

theorem pGCL'.vp_le_wlp''_aux.loop
    (ih : ∀ {φ : 𝔼r} {G : Globals}, C.fv ∪ φ.fv ⊆ G →
      φ.sem ≤ 1 → ((C.HeyVL O Direction.Upper G).2.vp φ).sem ≤ wlp''[O]⟦~C.pGCL⟧ φ.sem)
    (hG : (loop b I C).fv ∪ φ.fv ⊆ G) (hφ : φ.sem ≤ 1) (hI : I.sem ≤ 1 ∧ ∀ a ∈ C.invs, a.sem ≤ 1) :
    (((loop b I C).HeyVL O Direction.Upper G).2.vp φ).sem ≤ wlp''[O]⟦~(loop b I C).pGCL⟧ φ.sem := by
  simp only [Ty.expr, HeyVL, HeyVL.vp, sem_inf_apply, Finset.sort_nodup, HeyVL.vp_havocs,
    sem_validate, sem_himp_apply, HeyVL.if_vp_sem, sem_not_apply, Exp.validate_subst,
    Exp.himp_subst, Exp.add_subst, Exp.mul_subst, Exp.iver_subst, pGCL]
  intro σ
  if inv : IdleCoinvariant wlp''[O]⟦~C.pGCL⟧ b.sem φ.sem I.sem C.modsᶜ σ then
    simp
    left
    apply IdleCoinduction <;> grind
  else
    simp [IdleCoinvariant] at inv
    obtain ⟨σ', h₁, h₂⟩ := inv
    simp [Φ] at h₂
    simp_all only [Pi.inf_apply, inf_le_iff]
    right
    simp_all only [Ty.expr, Ty.lit, hnot_eq_compl, Exp.not_subst, iInf_apply, Exp.validate_apply,
      Pi.himp_apply, Exp.substs_help_apply, Pi.add_apply, Pi.mul_apply, Pi.iver_apply,
      Pi.compl_apply, compl_iff_not]
    let Ξ := HeyVL.Subs.of (C.HeyVL O .Upper G).2.mods.sort (by simp) σ'
    have σ_eq_σ' : σ[..Ξ.help'] = σ' := by
      ext x
      simp +contextual [Ξ]
      intro h
      specialize h₁ x (by contrapose! h; exact C.HeyVL_mods h)
      simp_all
    apply iInf_le_of_le Ξ
    simp [HeyVL.vp, HeyVL.Skip]
    have : ∀ {a b : ENNReal}, ▵ (a ⇨ b) = if a ≤ b then ⊤ else 0 := by
      intro a b
      simp [validate, himp, hnot, himp]
      grind [LT.lt.ne_top]
    simp [this, σ_eq_σ']
    specialize ih (φ:=I ⊓ (0 ⇨ φ)) (G:=G) (by simp [HeyLo.fv]; grind) (by simp; grind) σ'
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

set_option maxHeartbeats 500000 in
theorem pGCL'.vp_le_wlp''_aux {C : pGCL'} {G : Globals} (hG : C.fv ∪ φ.fv ⊆ G) (hφ : φ.sem ≤ 1)
    (hI : ∀ I ∈ C.invs, I.sem ≤ 1) :
    ((C.HeyVL O .Upper G).2.vp φ).sem ≤ wlp'' O C.pGCL φ.sem := by
  induction C generalizing G φ with
  | skip =>
    intro σ
    have hφ' : ∀ σ, φ.sem σ ≤ 1 := (hφ ·)
    simp only [Ty.lit, HeyVL, HeyVL.Skip, HeyVL.vp, sem_add_apply, Ty.expr, sem_zero, Pi.add_apply,
      Pi.ofNat_apply, add_zero, pGCL, wlp''.skip_apply, Pi.inf_apply, hφ', inf_of_le_left, le_refl]
  | assign x e =>
    intro σ
    have hφ' : ∀ σ, φ.sem σ ≤ 1 := (hφ ·)
    simp only [Ty.lit, HeyVL, HeyVL.vp, Distribution.pure_map, Distribution.pure_toExpr,
      sem_add_apply, Ty.expr, sem_mul_apply, sem_one, sem_subst, one_mul, sem_zero, Pi.add_apply,
      Pi.substs_cons, Substitution.substs_nil, Pi.zero_apply, add_zero, pGCL, wlp''.assign_apply,
      Pi.inf_apply, Pi.one_apply, hφ', inf_of_le_left, le_refl]
  | seq C₁ C₂ ih₁ ih₂ =>
    simp only [Ty.expr, HeyVL, HeyVL.vp, pGCL, wlp''.seq_apply]
    simp_all
    specialize ih₂ (G:=G) (by grind) hφ
    grw [ih₁, ih₂]
    · grind
    · apply le_trans ih₂; simp
  | ite b C₁ C₂ ih₁ ih₂ =>
    simp only [Ty.expr, HeyVL, HeyVL.if_vp_sem, sem_not_apply, pGCL, pGCL.ite, wlp''.prob_apply]
    simp only [fv, Finset.union_assoc] at hG
    grw [ih₁ _ hφ, ih₂ _ hφ]
    · intro; simp only [Ty.lit, hnot_eq_compl, Pi.add_apply, Pi.mul_apply, Pi.iver_apply,
      Pi.compl_apply, compl_iff_not, Iverson.iver_neg, ENNReal.natCast_sub, Nat.cast_one,
      ProbExp.pick, BExpr.probOf_apply, Pi.sub_apply, Pi.ofNat_apply, le_refl]
    all_goals grind
  | nonDet C₁ C₂ ih₁ ih₂ =>
    simp only [Ty.expr, HeyVL, pGCL, wlp''.nonDet_apply, Optimization.opt₂]
    simp [pGCL'.fv] at hG
    have : C₁.fv ∪ φ.fv ⊆ G := by grind
    cases O
    · simp only [HeyVL.vp, sem_sup_apply, Ty.expr]
      grw [ih₁ _ hφ, ih₂ _ hφ] <;> grind
    · simp only [HeyVL.vp, sem_inf_apply, Ty.expr]
      grw [ih₁ _ hφ, ih₂ _ hφ] <;> grind
  | prob C₁ p C₂ ih₁ ih₂ =>
    simp only [Ty.lit, pGCL'.prob_vp hG, Ty.expr]
    grw [ih₁ _ hφ, ih₂ _ hφ]
    · conv => right; simp only [wlp'', pGCL, Ty.lit, wlp, OrderHom.coe_mk,
      ProbExp.pickProb_DFunLike_coe]
      rfl
    · grind
    · grind
    · grind
    · calc
        C₁.fv ∪ φ.fv ⊆ C₁.fv ∪ (C₂.fv ∪ φ.fv) := by grind
        _ ⊆ G := by grind
        _ ⊆ (C₂.HeyVL O .Upper G).1 := by grind
  | loop b I C ih =>
    simp_all only [Ty.expr, Ty.lit, invs, Finset.mem_insert, or_true, implies_true, forall_const,
      forall_eq_or_imp]
    exact vp_le_wlp''_aux.loop ih hG hφ hI
  | tick r =>
    simp only [Ty.expr, Ty.lit, HeyVL, HeyVL.vp, sem_add_apply, pGCL, wlp''.tick_apply]
    intro σ
    simp [Pi.add_apply, Ty.lit, add_zero, le_refl]
    apply hφ
  | observe r =>
    intro σ
    simp only [Ty.lit, HeyVL, HeyVL.vp, sem_inf_apply, Ty.expr, sem_embed, Pi.inf_apply,
      Pi.mul_apply, Pi.iver_apply, Pi.top_apply, pGCL, wlp''.observe_apply, inf_le_iff]
    if r.sem σ then
      simp_all only [Ty.expr, Ty.lit, invs, Finset.notMem_empty, IsEmpty.forall_iff, implies_true,
        Iverson.iver_True, Nat.cast_one, one_mul, inf_of_le_left, ProbExp.pick_true, top_le_iff,
        le_refl, or_true]
    else
      simp_all only [Ty.expr, Ty.lit, invs, Finset.notMem_empty, IsEmpty.forall_iff, implies_true,
        Iverson.iver_False, CharP.cast_eq_zero, zero_mul, inf_of_le_left, not_false_eq_true,
        ProbExp.pick_false, Pi.zero_apply, le_refl, nonpos_iff_eq_zero, true_or]

theorem pGCL'.vp_le_wlp'' {C : pGCL'} (hφ : φ.sem ≤ 1) (hI : ∀ I ∈ C.invs, I.sem ≤ 1) :
    (C.vp O .Upper φ).sem ≤ wlp''[O]⟦~C.pGCL⟧ φ.sem := vp_le_wlp''_aux (by rfl) hφ hI

/-- info: 'pGCL'.vp_le_wlp''' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pGCL'.vp_le_wlp''
