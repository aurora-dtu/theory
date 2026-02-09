import PGCL.Exp

def PReal : Type := {p : ENNReal // p ≤ 1}

noncomputable instance : DecidableEq PReal := Subtype.instDecidableEq

namespace PReal

@[grind]
def ofENNReal (r : ENNReal) : PReal := ⟨r ⊓ 1, by simp⟩

@[grind, coe]
abbrev coe (r : PReal) : ENNReal := r.val
instance : Coe PReal ENNReal := ⟨coe⟩
@[ext]
theorem eq_of_coe {p r : PReal} (h : p.coe = r.coe) : p = r := by
  rcases p with ⟨p, hp⟩; rcases r with ⟨r, hr⟩
  congr
@[grind ., simp]
theorem coe_mk : coe ⟨p, hp⟩ = p := by rfl
abbrev lift₂ (f : ENNReal → ENNReal → ENNReal) : PReal → PReal → PReal :=
  fun p r ↦ ofENNReal (f p r)

noncomputable instance : Zero PReal := ⟨⟨0, by simp⟩⟩
noncomputable instance : One PReal := ⟨⟨1, by simp⟩⟩
noncomputable instance : Add PReal := ⟨lift₂ (· + ·)⟩
noncomputable instance : Sub PReal := ⟨fun a b ↦ ⟨coe a - b, by
  simp only [tsub_le_iff_right, le_add_right a.prop]⟩⟩
noncomputable instance : Mul PReal := ⟨fun a b ↦ ⟨coe a * b, Left.mul_le_one a.prop b.prop⟩⟩
noncomputable instance : Div PReal := ⟨lift₂ (· / ·)⟩

theorem add_def {p r : PReal} : p + r = ofENNReal (↑p + r) := by rfl
theorem coe_add {p r : PReal} :
    (p + r).coe = (p.coe + r.coe) ⊓ 1 := by
  rcases p with ⟨p, hp⟩; rcases r with ⟨r, hr⟩
  simp [coe, add_def, ofENNReal]
theorem sub_def {p r : PReal} :
    p - r = ⟨coe p - r, by simp only [tsub_le_iff_right, le_add_right p.prop]⟩ := by rfl
theorem coe_sub {p r : PReal} :
    (p - r).coe = (p.coe - r.coe) := by
  rcases p with ⟨p, hp⟩; rcases r with ⟨r, hr⟩
  simp [coe, sub_def]
theorem mul_def {p r : PReal} : p * r = ⟨coe p * r, Left.mul_le_one p.prop r.prop⟩ := by rfl
theorem coe_mul {p r : PReal} :
    (p * r).coe = p.coe * r.coe := by
  rcases p with ⟨p, hp⟩; rcases r with ⟨r, hr⟩
  simp [coe, mul_def]
theorem div_def {p r : PReal} : p / r = ofENNReal (↑p / r) := by rfl
theorem coe_div {p r : PReal} :
    (p / r).coe = (p.coe / r.coe) ⊓ 1 := by
  rcases p with ⟨p, hp⟩; rcases r with ⟨r, hr⟩
  simp [coe, div_def, ofENNReal]

noncomputable instance : LE PReal := ⟨(coe · ≤ ↑·)⟩
theorem le_def {p r : PReal} : p ≤ r ↔ coe p ≤ ↑r := by rfl
noncomputable instance : PartialOrder PReal where
  le_refl := by simp [le_def]
  le_trans := by simp [le_def]; intro a b c hab hbc; apply le_trans hab hbc
  le_antisymm := by
    simp [le_def]; intro a b hab hba;
    have := le_antisymm hab hba; exact PReal.eq_of_coe_iff.mpr (congrArg coe this)

@[grind =, simp]
theorem coe_zero : coe 0 = 0 := by rfl
@[grind =, simp]
theorem coe_one : coe 1 = 1 := by rfl
@[grind =, simp]
theorem mk_zero : (⟨0, by simp⟩ : PReal) = (0 : PReal) := by rfl
@[grind =, simp]
theorem mk_one : (⟨1, by simp⟩ : PReal) = (1 : PReal) := by rfl
@[simp]
theorem zero_le {p : PReal} : 0 ≤ p := by simp [le_def]
@[simp]
theorem le_one {p : PReal} : p ≤ 1 := by have := p.prop; simp_all [le_def]
@[simp]
theorem zero_le_coe {p : PReal} : 0 ≤ coe p := by simp
@[simp]
theorem coe_le_one {p : PReal} : coe p ≤ 1 := by have := p.prop; simp_all

@[grind =, simp]
theorem ofENNReal_min : ofENNReal (min (coe p) ↑r) = min (coe p) r := by
  simp [ofENNReal]
@[grind =, simp]
theorem ofENNReal_max {r : PReal} : ofENNReal (max (coe p) ↑r) = max (coe p) r := by
  simp [ofENNReal]

@[grind, simp]
noncomputable instance : Bot PReal := ⟨0⟩
@[grind, simp]
noncomputable instance : Top PReal := ⟨1⟩
noncomputable instance : CompleteLattice PReal where
  sup := lift₂ max
  inf := lift₂ min
  bot_le := by simp
  le_top := by simp
  le_inf := by
    intro a b c hab hac
    rw [lift₂, le_def]
    simp [hab, hac]
  inf_le_left := by simp [lift₂, ofENNReal, le_def]
  inf_le_right := by simp [lift₂, ofENNReal, le_def]
  le_sup_left := by simp [lift₂, ofENNReal, le_def]
  le_sup_right := by simp [lift₂, ofENNReal, le_def]
  sup_le := by
    intro a b c hab hac
    rw [lift₂, le_def]
    simp [hab, hac]
  sSup s := ⟨sSup (coe '' s), by simp⟩
  sInf s := ⟨sInf (coe '' s) ⊓ 1, by simp⟩
  le_sSup := by
    simp [le_def]
    intro s a h
    exact le_sSup (s:=coe '' s) (a:=coe a) (by grind)
  sSup_le := by intro s a h; simp [le_def]; exact h
  sInf_le := by
    simp [le_def]
    intro s a h
    left
    exact sInf_le (s:=coe '' s) (a:=coe a) (by grind)
  le_sInf := by intro s a h; simp [le_def]; exact h

@[simp]
theorem add_le_add_one {p r : PReal} : p ≤ r + 1 := by
  simp [add_def, ofENNReal]

theorem mul_le_left {p r : PReal} : p * r ≤ p := mul_le_of_le_one_right' r.prop
theorem mul_le_right {p r : PReal} : p * r ≤ r := mul_le_of_le_one_left' p.prop

noncomputable instance : MulZeroClass PReal where
  zero_mul a := by simp [mul_def]
  mul_zero a := by simp [mul_def]
noncomputable instance : AddCommMonoid PReal where
  add_assoc a b c := by
    simp [add_def, ofENNReal]
    ext
    simp [add_min, min_add, ← add_assoc]
    apply inf_congr_right <;> simp
  add_comm a b := by
    simp [add_def, ofENNReal]
    ext
    simp [add_comm]
  zero_add a := by simp [add_def, ofENNReal]
  add_zero a := by simp [add_def, ofENNReal]
  nsmul n a := ofENNReal (n * coe a)
  nsmul_zero := by simp [ofENNReal]
  nsmul_succ n a := by
    ext
    simp [ofENNReal, right_distrib, add_def, min_add]
    apply inf_congr_right <;> simp
noncomputable instance : SemigroupWithZero PReal where
  mul_assoc a := by simp [mul_def, mul_assoc]
noncomputable instance : MulZeroOneClass PReal where
  one_mul a := by simp [mul_def]
  mul_one a := by simp [mul_def]
noncomputable instance : MonoidWithZero PReal where

instance : ExistsAddOfLE PReal where
  exists_add_of_le := by
    intro a b h
    use b - a
    ext
    simp [add_def, sub_def, ofENNReal, add_tsub_cancel_of_le, h]

instance : AddLeftMono PReal where
  elim a b c h := by
    simp_all [le_def, add_def, ofENNReal]
    left
    exact add_le_add_right (le_def.mp h) _
instance : AddRightMono PReal where
  elim a b c h := by
    simp_all [le_def, add_def, ofENNReal]
    left
    exact add_le_add_left (le_def.mp h) _

instance : OrderedSub PReal where
  tsub_le_iff_right := by simp [sub_def, le_def, add_def, ofENNReal]

@[grind =, simp]
theorem coe_inf : ∀ {a b : PReal}, coe (a ⊓ b) = coe a ⊓ coe b := by
  rintro ⟨a, _⟩ ⟨b, _⟩
  conv => left; simp [min, SemilatticeInf.inf, lift₂, ofENNReal]
  rw [Lattice.inf]
  simp [CompleteLattice.toConditionallyCompleteLattice, instCompleteLattice]
@[grind =, simp]
theorem coe_sup : ∀ {a b : PReal}, coe (a ⊔ b) = coe a ⊔ coe b := by
  rintro ⟨a, _⟩ ⟨b, _⟩
  conv => left; simp [max]
  rw [SemilatticeSup.sup]
  simp [CompleteLattice.toConditionallyCompleteLattice, instCompleteLattice]
@[simp]
theorem coe_iInf {ι : Sort*} [Nonempty ι] (f : ι → PReal) : coe (⨅ i, f i) = ⨅ i, coe (f i) := by
  simp [CompleteLattice.toConditionallyCompleteLattice, instCompleteLattice]
  apply le_antisymm
  · simp only [le_iInf_iff, Subtype.coe_le_coe]
    intro i
    apply iInf_le_of_le (α:=PReal) i
    rfl
  · suffices ofENNReal (⨅ i, ↑(f i)) ≤ ⨅ i, f i by
      rw [le_def] at this
      convert this
      simp [ofENNReal]
      apply iInf_le_of_le Classical.ofNonempty
      simp
    simp [ofENNReal]
    intro i
    rw [le_def]
    simp only [coe_mk, inf_le_iff]
    left
    apply iInf_le_of_le i; rfl
@[simp]
theorem coe_iSup {ι : Sort*} (f : ι → PReal) : coe (⨆ i, f i) = ⨆ i, coe (f i) := by
  simp [CompleteLattice.toConditionallyCompleteLattice, instCompleteLattice]
  apply le_antisymm
  · suffices ⨆ i, f i ≤ ofENNReal (⨆ i, ↑(f i)) by
      rw [le_def] at this
      convert this
      simp [ofENNReal]
    simp [ofENNReal]
    intro i
    rw [le_def]
    simp
    apply le_iSup_of_le i; rfl
  · simp only [iSup_le_iff, Subtype.coe_le_coe]
    intro i
    apply le_iSup_of_le (α:=PReal) i
    rfl

noncomputable instance : CompletelyDistribLattice PReal where
  himp a b := if a ≤ b then 1 else b
  compl a := if a = 0 then 1 else 0
  hnot a := if a = 1 then 0 else 1
  sdiff a b := if a ≤ b then 0 else a
  le_himp_iff a b c := by
    split_ifs with h
    · constructor
      · simp
        exact inf_le_of_right_le h
      · simp
    · constructor
      · exact fun a_1 ↦ inf_le_of_left_le a_1
      · intro h'
        simp [le_def] at h'
        rcases h' with h' | h'
        · assumption
        · simp_all
  himp_bot a := by simp; simp [instCompleteLattice]
  top_sdiff a := by simp; simp [instCompleteLattice]
  sdiff_le_iff a b c := by
    split_ifs with h
    · simp; exact le_sup_of_le_left h
    · simp [le_def]
      exact fun a_1 ↦ Std.le_of_not_ge fun a ↦ h a_1
  iInf_iSup_eq := by
    intro ι κ f
    if Nonempty ι then
      ext
      simp
      apply iInf_iSup_eq
  else
    simp_all only [not_nonempty_iff]
    rw [iInf_of_empty]
    simp
    rw [iInf_of_empty]

variable {a b c d : PReal}

@[gcongr]
theorem add_le_add (hac : a ≤ c) (hbd : b ≤ d) : a + b ≤ c + d := by
  simp only [add_def, le_def, coe_mk, ofENNReal]
  gcongr
  · exact le_def.mp hac
  · exact le_def.mp hbd
@[gcongr]
theorem mul_le_mul (hac : a ≤ c) (hbd : b ≤ d) : a * b ≤ c * d := by
  simp only [mul_def, le_def, coe_mk]
  gcongr
  · exact le_def.mp hac
  · exact le_def.mp hbd
@[gcongr]
theorem sub_le_sub (hac : a ≤ c) (hdb : d ≤ b) : a - b ≤ c - d := by
  simp only [sub_def, le_def, coe_mk]
  gcongr
  · exact le_def.mp hac
  · exact le_def.mp hdb
@[gcongr]
theorem div_le_div (hac : a ≤ c) (hdb : d ≤ b) : a / b ≤ c / d := by
  simp only [div_def, le_def, coe_mk, ofENNReal]
  gcongr
  · exact le_def.mp hac
  · exact le_def.mp hdb

@[grind =, simp]
theorem one_sub_one_sub : 1 - (1 - a) = a := by ext; simp [sub_def, ENNReal.sub_sub_cancel]

end PReal
