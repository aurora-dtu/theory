import HeyVL.Verify

open Optimization.Notation
open HeyLo

abbrev NatLog.y : Ident := ⟨"y", .Nat⟩
abbrev NatLog.c : Ident := ⟨"c", .Nat⟩

open NatLog

def NatLog := vc[𝒟, wp]
  { ↑c + [0 < y] * ↑(y + nlog2(y)) }
    while 0 < y inv(↑c + [0 < y] * ↑(y + nlog2(y))) {
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
#guard_msgs in #print axioms NatLog.soundess
