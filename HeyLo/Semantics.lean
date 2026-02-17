import HeyLo.vp
import PGCL.Fix

attribute [grind =] Finset.empty_union

open Optimization.Notation

open pGCL

open HeyLo

@[simp]
theorem HeyLo.ofNat_ident (n : String) :
      (ofNat(0) : HeyLo ({ name := n, type := Ty.Nat } : Ident).type)
    = (0 : HeyLo .Nat) := by simp
@[simp]
theorem HeyLo.ofNat_sem (n : ℕ) : sem (ofNat(n) : HeyLo .Nat) σ = n := by
  simp [sem]
@[grind =, simp]
theorem HeyLo.nat_zero_sem : sem (0 : HeyLo .Nat) = 0 := by simp [sem] @[grind =, simp]
theorem HeyLo.nat_one_sem : sem (1 : HeyLo .Nat) = 1 := by simp [sem]

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
theorem HeyLo.sem_compl : (Aᶜ).sem = A.semᶜ := rfl
@[grind =, simp]
theorem HeyLo.sem_himp_apply : (A ⇨ B).sem = A.sem ⇨ B.sem := rfl
@[grind =, simp]
theorem HeyLo.sem_sdiff_apply : (A \ B).sem = A.sem \ B.sem := rfl

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
theorem HeyLo.substs_inf {A B : 𝔼r} : (A ⊓ B).sem[..xs] = A.sem[..xs] ⊓ B.sem[..xs] :=
  Substitution.substs_of_binary (m:=A.sem) fun _ _ ↦ congrFun rfl

end

@[grind =, simp]
theorem HeyLo.Var_sem_subst :
      (HeyLo.Var n t).sem[x ↦ v]
    = if h : x = ⟨n, t⟩ then cast (by obtain ⟨x, t'⟩ := x; grind) v else (· ⟨n, t⟩) := by
  obtain ⟨x, t'⟩ := x
  split_ifs with h
  · simp only [Ident.mk.injEq] at h
    rcases h with ⟨⟨_⟩, ⟨_⟩⟩
    simp [sem, Substitution.subst_singleton, Substitution.subst]
  · simp at h
    ext σ
    simp [sem, Substitution.subst_singleton, Substitution.subst]
    grind

def Substitution.applied (σ : States fun (x : Ident) ↦ x.type.lit)
    (xs : List ((v : Ident) × 𝔼'[v.type.lit])) :
    States fun (x : Ident) ↦ x.type.lit :=
  match xs with
  | [] => σ
  | x::xs => Substitution.applied σ[x.1 ↦ x.2 σ] xs

theorem BExpr.subst_applied {b : BExpr fun (x : Ident) ↦ x.type.lit}
    {xs : List ((v : Ident) × 𝔼'[v.type.lit])} :
    b[..xs] = fun σ ↦ b (Substitution.applied σ xs) := by
  ext σ
  induction xs generalizing σ with
  | nil => simp [Substitution.applied]
  | cons x xs ih => simp_all [Substitution.applied]

theorem BExpr.subst_apply {b : BExpr fun (x : Ident) ↦ x.type.lit}
    {xs : List ((v : Ident) × 𝔼'[v.type.lit])} :
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
theorem Substitution.applied_subst (σ : States fun (x : Ident) ↦ x.type.lit)
    (xs : List ((v : Ident) × 𝔼'[v.type.lit])) (v : 𝔼'[_]) :
      (Substitution.applied σ xs)[x ↦ v (Substitution.applied σ xs)]
    = Substitution.applied σ (xs ++ [⟨x, v⟩]) := by
  induction xs generalizing σ x v with
  | nil => simp [applied]
  | cons y xs ih =>
    simp_all [applied]

def HeyVL.Subs.of (xs : List Ident) (hn : xs.Nodup) (σ : States fun (x : Ident) ↦ x.type.lit) :
    HeyVL.Subs xs hn := ⟨xs.map fun x ↦ ⟨x, σ x⟩, by simp, by simp⟩
@[grind =, simp]
theorem HeyVL.Subs.of_get (xs : List Ident) (hn : xs.Nodup)
    (σ : States fun (x : Ident) ↦ x.type.lit) {y} {hy} :
    (Subs.of xs hn σ).get y hy = σ y := by simp [Subs.of, Subs.get]; grind

set_option maxHeartbeats 700000 in
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

@[simp]
theorem HeyVL.vp_havocs (h : xs.Nodup) :
    (vp⟦@(Havocs @xs)⟧ φ).sem = ⨅ (vs : Subs xs hn), φ.sem[..vs.help] := by
  rcases xs with _ | ⟨x, xs⟩
  · ext σ; simp [Havocs, Skip, vp, Subs.help]
  induction xs generalizing x φ with
  | nil =>
    ext σ
    simp [Havocs, vp]
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
      simp [Subs.help', Subs.tail]
  | cons y xs ih =>
    ext σ
    simp at ih
    simp_all [Havocs]
    rw [vp]
    have : y ∉ xs := by grind
    have : xs.Nodup := by grind
    simp_all [vp]
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
    simp [Cohavocs, vp]
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
      simp [Subs.help', Subs.tail]
  | cons y xs ih =>
    ext σ
    simp at ih
    simp_all [Cohavocs]
    rw [vp]
    have : y ∉ xs := by grind
    have : xs.Nodup := by grind
    simp_all [vp]
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

@[grind =, simp]
theorem spGCL.pGCL_mods (C : spGCL) : C.pGCL.mods = ↑C.mods := by
  induction C with simp_all [mods, pGCL, pGCL.mods, pGCL.ite]
