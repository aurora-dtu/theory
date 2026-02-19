import HeyVL.Encoding
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Eval

open Optimization.Notation
open HeyLo

/-- A HeyVL program C verifies if `vp⟦C⟧ ⊤ = ⊤` -/
def HeyVL.Verifies (C : HeyVL) : Prop := (vp⟦@C⟧ ⊤).sem = ⊤

structure Conditions (E : Encoding) where
  original : spGCL
  O : Optimization
  post : 𝔼r
  pre : 𝔼r
  encoding : 𝔼r
  prop : original.vp O E post = encoding
  fv : Globals
  fv_prop : fv = original.fv ∪ post.fv ∪ pre.fv
  invs : List 𝔼r
  invs_prop : invs = original.invsList

declare_syntax_cat pgclEncoding
syntax ident : pgclEncoding
syntax "pgclEncoding[" pgclEncoding "]" : term

syntax "vc[" term "," pgclEncoding "]" "{" cheylo "}" cspGCL "{" cheylo "}" : term

macro_rules
| `(pgclEncoding[wp]) => `(Encoding.wp)
| `(pgclEncoding[wlp]) => `(Encoding.wlp)
| `(vc[$O, $E] { $P } $C { $Q }) =>
  `(
    let C' :=
      eval% (spGCL.vp spgcl {$C} $O pgclEncoding[$E] heylo {$Q})
    let invs :=
      eval% (spGCL.invsList spgcl {$C})
    let P := heylo {$P}
    let C := spgcl {$C}
    let Q := heylo {$Q}
    ({
      original := C
      O := $O
      pre := P
      post := Q
      fv := C.fv ∪ P.fv ∪ Q.fv
      fv_prop := by decide
      invs := invs
      invs_prop := by decide +native
      encoding := C'
      prop := by decide +native
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

def Conditions.show_wp (C : Conditions .wp) (h : C.encoding.sem ≤ C.pre.sem) : C.sound := by
  simp [sound]
  apply le_trans spGCL.wp_le_vp
  simpa [C.prop]

def Conditions.show_wlp' (C : Conditions .wlp) (h : C.pre.sem ≤ C.encoding.sem)
    (hpost : C.post.sem ≤ 1) (hI : ∀ I ∈ C.invs, I.sem ≤ 1) : C.sound := by
  simp [sound]
  apply le_trans _ (spGCL.vp_le_wlp hpost _)
  · simpa [C.prop]
  · grind [cases Conditions]

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
