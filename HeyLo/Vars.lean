import HeyLo.HeyVL
import HeyLo.spGCL

attribute [grind =] Finset.empty_union

open Optimization.Notation

open pGCL

open HeyLo

abbrev Globals := Finset Ident

namespace Globals

def fresh (G : Globals) (α : Ty) : Globals × Ident :=
  let new := if h : G = ∅ then
    ⟨"f₀", α⟩
  else
    let longest := G.image (·.name.length) |>.max' (by simp [Finset.nonempty_iff_ne_empty, h])
    ⟨("f" ++ String.replicate longest '₀'), α⟩
  (G ∪ {new}, new)
theorem fresh_type (G : Globals) : (G.fresh ty).2.type = ty := by
  grind [fresh]
theorem fresh_update (G : Globals) : (fresh G ty).1 = insert (fresh G ty).2 G := by
  grind [fresh]
theorem fresh_not_in (G : Globals) : (fresh G ty).2 ∉ G := by
  simp [fresh]
  split_ifs
  · grind
  · have : ∀ (F : Finset Ident) (x : Ident), x ∉ F ↔ ∀ y ∈ F, x ≠ y :=
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

attribute [grind =, simp] fresh_type
attribute [grind =, simp] fresh_update
attribute [grind ., simp] fresh_not_in

/-- Generate a fresh variables given some global.

This is a macro to ensure definitional equality of the generated idents type. -/
scoped syntax "let_fresh " ident " : " term " ← " term:max term : term

macro_rules
| `(let_fresh $n : $t ← $G $rest) =>
  `(term|let ($G, $n) := Globals.fresh $G $t ; let $n := ⟨Ident.name $n, $t⟩; $rest)

end Globals

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
def HeyLo.Distribution.fv (D : Distribution α) : Globals :=
  D.values.toList.map (fun (x, y) ↦ x.fv ∪ y.fv) |>.toFinset.biUnion (·)
@[grind]
def spGCL.fv (C : spGCL) : Globals :=
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
def spGCL.mods (C : spGCL) : Globals :=
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
def spGCL.invs (C : spGCL) : Finset 𝔼r :=
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
def spGCL.invsList_aux (C : spGCL) : List 𝔼r :=
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
def spGCL.invsList (C : spGCL) : List 𝔼r := C.invsList_aux.dedup

@[grind =, simp]
theorem spGCL.mem_invsList_iff : I ∈ spGCL.invsList C ↔ I ∈ C.invs := by
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
theorem HeyLo.Distribution.toExpr_fv {μ : Distribution .ENNReal} : μ.toExpr.fv = μ.fv := by
  obtain ⟨⟨values⟩, h⟩ := μ
  simp [toExpr, fv]
  clear! h
  induction values with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, HeyLo.fv]
    grind [List.toFinset_cons, Finset.biUnion_insert]

@[grind =, simp]
theorem HeyLo.fv_inf {X Y : 𝔼r} : (X ⊓ Y).fv = X.fv ∪ Y.fv := rfl
