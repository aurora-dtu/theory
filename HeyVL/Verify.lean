import HeyVL.Encoding
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Nat.Log

open Optimization.Notation
open HeyLo

/-- A HeyVL program C verifies if `vp⟦C⟧ ⊤ = ⊤` -/
def HeyVL.Verifies (C : HeyVL) : Prop := (vp⟦@C⟧ ⊤).sem = ⊤

structure Conditions (E : Encoding) where
  original : spGCL
  O : Optimization
  post : 𝔼r
  pre : 𝔼r

declare_syntax_cat pgclEncoding
syntax ident : pgclEncoding
syntax "pgclEncoding[" pgclEncoding "]" : term

syntax "vc[" term "," pgclEncoding "]" "{" cheylo "}" cspGCL "{" cheylo "}" : term

macro_rules
| `(pgclEncoding[wp]) => `(Encoding.wp)
| `(pgclEncoding[wlp]) => `(Encoding.wlp)
| `(vc[$O, $E] { $P } $C { $Q }) =>
  `(
    let P := heylo {$P}
    let C := spgcl {$C}
    let Q := heylo {$Q}
    ({
      original := C
      O := $O
      pre := P
      post := Q
    } : Conditions pgclEncoding[$E])
  )

theorem HeyVL.vp_sem_eq (S : HeyVL) (h : φ.sem = ψ.sem) : (vp⟦@S⟧ φ).sem = (vp⟦@S⟧ ψ).sem := by
  induction S generalizing φ ψ with (simp_all [vp]; try grind)
  | Assign => ext; simp [h]

theorem Conditions.wlp_valid (C : Conditions E)
    (h₁ : ⟦@C.post⟧' ≤ 1)
    (hI : ∀ I ∈ C.original.invs, ⟦@I⟧' ≤ 1)
    (h : heyvl {
        assume(@C.pre);
        @(C.original.enc C.O .wlp (C.original.fv ∪ C.post.fv)).2;
        assert(@C.post)
      }.Verifies) :
    C.pre.sem ≤ C.original.pGCL.wlp C.O C.post.sem := by
  simp only [HeyVL.Verifies, Ty.expr, Ty.lit, HeyVL.vp, sem_himp_apply, himp_eq_top_iff] at h
  apply le_trans _ (spGCL.vp_le_wlp _ _)
  · grw [h]
    simp [spGCL.vp]
    rw [HeyVL.vp_sem_eq]
    ext
    simp
    simp [sem]
  · apply h₁
  · apply hI

def Conditions.sound (C : Conditions E) : Prop :=
  match E with
  | .wp => wp[C.O]⟦@C.original.pGCL⟧ C.post.sem ≤ C.pre.sem
  | .wlp => C.pre.sem ≤ wlp[C.O]⟦@C.original.pGCL⟧ C.post.sem

@[simp]
theorem ENNReal.compl_compl_le : ∀ {a b : ENNReal}, (~~a ≤ b ↔ a = 0 ∨ b = ⊤) := by
  simp [compl]; grind [zero_le]

@[grind =, simp]
theorem Nat.log2_div_2 (n : ℕ) : Nat.log2 (n / 2) = Nat.log2 n - 1 := by
  nth_rw 2 [Nat.log2_def]
  split_ifs
  · omega
  · rcases n with _ | _ | n <;> (try omega) <;> simp
theorem Nat.log2_le_succ {n : ℕ} : Nat.log2 n ≤ Nat.log2 (n + 1) := by
  simp [Nat.log2_eq_log_two]
  gcongr
  omega
@[gcongr]
theorem Nat.log2_mono {n m : ℕ} (h : n ≤ m) : Nat.log2 n ≤ Nat.log2 m := by
  simp [Nat.log2_eq_log_two]
  gcongr

@[grind =, simp]
theorem ENNReal.two_inv_mul_two : (2 : ENNReal)⁻¹ * 2 = 1 := by
  apply ENNReal.inv_mul_cancel <;> simp
@[grind =, simp]
theorem ENNReal.two_mul_two_inv : (2 : ENNReal) * 2⁻¹ = 1 := by
  rw [mul_comm]; apply ENNReal.inv_mul_cancel <;> simp
@[grind =, simp]
theorem ENNReal.two_inv_mul_two_id (q : ENNReal) : 2⁻¹ * q * 2 = q := by
  rw [mul_comm, ← mul_assoc]
  simp

syntax "cbv_le" : tactic
macro_rules
| `(tactic|cbv_le) => `(tactic|apply le_of_eq_of_le (by cbv) (le_of_le_of_eq _ (by symm; cbv)))

syntax "vc_simp" : tactic

@[simp]
theorem Set.mem_fun_exists {α β : Type*} {a : α} {q : β → α} :
    Membership.mem (self:=Set.instMembership) (fun (x : α) ↦ ∃ y, q y = x) a ↔ (∃ y, q y = a) := by
  rw [Set.instMembership]
  simp [Set.Mem]

macro_rules
| `(tactic|vc_simp) =>
  let σ := Lean.mkIdent (Lean.Name.mkSimple "σ")
  `(tactic|
    simp [Conditions.sound];
    apply le_trans spGCL.wp_le_vp;
    cbv_le;
    intro $σ:ident;
    simp only [Ty.lit, CharP.cast_eq_zero, Nat.cast_add, Nat.cast_id, Nat.cast_ofNat,
      pGCL.State.subst_apply, ↓dreduceDIte, cast_eq, Ident.mk.injEq, String.reduceEq, and_true,
      UInt8.ofBitVec_ofNat, reduceCtorEq, and_false, sup_le_iff, Std.le_refl, iSup_le_iff,
      Subtype.forall, Set.mem_fun_exists, forall_exists_index, forall_apply_eq_imp_iff,
      Pi.substs_cons, Substitution.substs_nil, Nat.cast_one, one_div, ENNReal.inv_le_one,
      Nat.one_le_ofNat, inf_of_le_left, Iverson.iver_True, one_mul, Nat.div_pos_iff, Nat.ofNat_pos,
      true_and, Nat.log2_div_2, ENNReal.natCast_sub, sdiff_top, bot_eq_zero', zero_le,
      sup_of_le_left, add_zero, top_himp, compl_iff_not, not_true_eq_false, Iverson.iver_False,
      zero_mul, tsub_pos_iff_lt, ENNReal.zero_himp, le_top, ENNReal.one_sub_inv_two,
      Bool.false_eq_true, not_false_eq_true, inf_of_le_right, not_lt, nonpos_iff_eq_zero,
      ↓reduceDIte, ENNReal.compl_compl_le, ENNReal.sdiff_zero_eq_zero, ENNReal.add_eq_top,
      ENNReal.natCast_ne_top, ENNReal.mul_eq_top, ne_eq, Nat.cast_eq_zero, or_self, add_eq_zero,
      not_and, false_and, or_false, forall_const];
    )
