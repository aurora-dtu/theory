import HeyLo.Encoding
import Mathlib.Tactic.Eval

open Optimization.Notation
open HeyLo

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

abbrev y : Ident := ⟨"y", .Nat⟩
abbrev c : Ident := ⟨"c", .Nat⟩

def NatLog := vc[𝒟, wp]
  { ↑c + [0 < y] * ↑(y + nlog2 y) }
    while 0 < y inv(↑c + [0 < y] * ↑(y + nlog2 y)) {
      { y := y / 2 } [1/2] { y := y - 1 } ; c := c + 1
    }
  { ↑c }

theorem NatLog.soundess : NatLog.sound := by
  apply NatLog.show_wp fun σ ↦ ?_
  simp [NatLog]
  simp [BinOp.sem, UnOp.sem, sem, Fun.sem]
  set c : ℕ := σ c; set y : ℕ := σ y
  intro c' y'
  have : ∀ {a b : ENNReal}, (~~a ≤ b ↔ a = 0 ∨ b = ⊤) := by simp [compl]; grind [zero_le]
  simp [this]; left
  rcases y' with _ | y' <;> simp
  grw [Nat.log2_div_2, (by gcongr; omega : Nat.log2 y' ≤ Nat.log2 (y' + 1))]
  repeat rw [Nat.cast_add]
  if h₁ : 0 < y' then
    simp [h₁, (by omega : 0 < (y' + 1) / 2)]
    grw [(by omega : (y' + 1) / 2 ≤ (y' + 1))]
    simp [← ENNReal.toReal_le_toReal, ENNReal.mul_eq_top, ENNReal.toReal_add]
    rw [ENNReal.toReal_sub_of_le]
    · grind [ENNReal.toReal_natCast, ENNReal.toReal_one]
    · simp; apply (Nat.le_log2 ?_).mpr <;> grind
    · grind [ENNReal.natCast_ne_top]
  else
    have : y' = 0 := by omega
    subst_eqs
    ring_nf
    grind [ENNReal.two_inv_mul_two, add_comm, CharP.cast_eq_zero, zero_add]

/--
info: 'NatLog.soundess' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]
-/
#guard_msgs in
#print axioms NatLog.soundess

def NatLog' := vc[𝒜, wlp]
  { 1 }
    while 0 < y
      inv(1)
    {
      { y := y / 2 } [1/2] { y := y - 1 } ; c := c + 1
    }
  { 1 }

theorem NatLog'.soundess : NatLog'.sound := by
  apply NatLog'.show_wlp' fun σ ↦ ?_
  · intro σ; simp [NatLog']
  · simp [NatLog', sem]
  simp [NatLog', BinOp.sem, UnOp.sem, sem, ENNReal.inv_two_add_inv_two, hnot]

/--
info: 'NatLog'.soundess' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]
-/
#guard_msgs in
#print axioms NatLog'.soundess
