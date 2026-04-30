import HeyVL.Verify

open Optimization.Notation
open HeyLo

abbrev NatLog.y : Ident := ⟨"y", .Nat⟩

open NatLog

def NatLog := vc[𝒟, wp]
  { [0 < y] * ↑(y + nlog2(y)) }
    while 0 < y inv([0 < y] * ↑(y + nlog2(y))) {
      { y := y / 2 } [1/2] { y := y - 1 } ; tick(1)
    }
  { 0 }

theorem NatLog.soundess : NatLog.sound := by
  vc_simp
  rintro (_ | y) <;> simp
  grw [(by omega : 1 ≤ y ↔ 0 < y), (by omega : (y + 1) / 2 ≤ y + 1)]
  grw [(by gcongr; omega : y.log2 ≤ (y + 1).log2)]
  simp [← ENNReal.toReal_le_toReal, ENNReal.mul_eq_top, ENNReal.toReal_add]
  if h : y = 0 then subst_eqs; ring_nf; simp
  else
    rw [ENNReal.toReal_sub_of_le]
    · simp [Nat.zero_lt_of_ne_zero h]; grind
    · simp; apply (Nat.le_log2 ?_).mpr <;> grind
    · grind [ENNReal.natCast_ne_top]

/-- info: 'NatLog.soundess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NatLog.soundess
