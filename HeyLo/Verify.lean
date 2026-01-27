import HeyLo.Basic
import HeyLo.Syntax
import Mathlib.Tactic.Eval

open Optimization.Notation
open HeyLo

variable {ϖ : Type} [DecidableEq ϖ] [LE ϖ]
variable [DecidableRel (LE.le (α:=ϖ))] [IsTrans ϖ LE.le] [IsAntisymm ϖ LE.le] [IsTotal ϖ LE.le]
variable [Global ϖ]

def pGCL'.vp (C : pGCL' ϖ) (O : Optimization) (D : Direction) (φ : 𝔼r[ϖ]) :=
  (C.HeyVL O D (C.fv ∪ φ.fv)).2.vp φ

syntax (name := pgclVerify)
  "pgcl_verify " "wp["term"]⟦"cpgcl'"⟧" cheylo:max "≤" cheylo " := " term : command

open Lean in
def collectNames (e : Expr) : Array Name :=
  match e with
  | .app (.app _ (.app _ (.lit (.strVal n)))) r =>
    #[.mkSimple n] ++ collectNames r
  | _ => #[]

def HeyLo.opt : HeyLo ϖ α → HeyLo ϖ α
  | .Var x => .Var x
  | .Lit .Infinity => .Lit .Infinity
  | .Lit (.Frac q) => if q.den = 1 then .Lit (.UInt q.num) else .Lit (.Frac q)
  | .Lit (.UInt n) => .Lit (.UInt n)
  | .Lit (.Bool b) => .Lit (.Bool b)
  | .Subst a b c => .Subst a b.opt c.opt
  | .Ite b l r => .Ite b l.opt r.opt
  | .Binary .CoImpl l r => .Binary .CoImpl l.opt r.opt
  | .Binary .Impl l r => .Binary .Impl l.opt r.opt
  | .Binary .Sup l r => .Binary .Sup l.opt r.opt
  | .Binary .Inf l r => .Binary .Inf l.opt r.opt
  | .Binary .Div l r => .Binary .Div l.opt r.opt
  | .Binary .Mul l r => .Binary .Mul l.opt r.opt
  | .Binary .Sub l r => .Binary .Sub l.opt r.opt
  | .Binary .Add l r => .Binary .Add l.opt r.opt
  | .Binary .Gt l r => .Binary .Gt l.opt r.opt
  | .Binary .Ge l r => .Binary .Ge l.opt r.opt
  | .Binary .Ne l r => .Binary .Ne l.opt r.opt
  | .Binary .Le l r => .Binary .Le l.opt r.opt
  | .Binary .Lt l r => .Binary .Lt l.opt r.opt
  | .Binary .Eq l r => .Binary .Eq l.opt r.opt
  | .Binary .Or l r => .Binary .Or l.opt r.opt
  | .Binary .And l r => .Binary .And l.opt r.opt
  | .Unary (@UnOp.Not .ENNReal) x => .Unary (@UnOp.Not .ENNReal) x.opt
  | .Unary (@UnOp.Not .Bool) x => .Unary (@UnOp.Not .Bool) x.opt
  | .Unary .Non x => .Unary .Non x.opt
  | .Unary .Iverson x => .Unary .Iverson x.opt
  | .Unary .Embed x => .Unary .Embed x.opt
  | .Call op x => .Call op x
  | .Quant .Sup x e => .Quant .Sup x e.opt
  | .Quant .Inf x e => .Quant .Inf x e.opt
  | .Quant .Exists x e => .Quant .Exists x e.opt
  | .Quant .Forall x e => .Quant .Forall x e.opt

open Lean Elab Command Term Meta in
@[command_elab pgclVerify]
def pgclVerifyMacro : CommandElab := fun stx ↦ do
  let `(pgcl_verify wp[$O]⟦$C:cpgcl'⟧ $P:cheylo ≤ $Q := $proof) := stx | throwUnsupportedSyntax
  -- `(#check 12)
  -- dbg_trace "O := {O}"
  -- dbg_trace "P := {P}"
  -- dbg_trace "Q := {Q}"
  -- dbg_trace "proof := {proof}"
  let fv ← liftTermElabM <| do
    elabTermAndSynthesize (← `(eval% ((pgcl' {$C}).fv ∪ (heylo {$P} : 𝔼r[_]).fv ∪ (heylo {$Q} : 𝔼r[_]).fv).sort)) none
    -- elabTermAndSynthesize (← `(((pgcl' {$C}).fv ∪ (heylo {$P} : 𝔼r[_]).fv ∪ (heylo {$Q} : 𝔼r[_]).fv).sort)) none
  -- dbg_trace "fv := {fv}"
  let fv' := collectNames fv
  -- dbg_trace "fv' := {fv'}"

  let gens ← fv'.mapM fun (n : Lean.Name) ↦
    let str : TSyntax `term := Syntax.mkStrLit n.toString
    let ident : Lean.Ident := mkIdent n
    `(tactic|generalize σ $str = $ident)

  elabCommand (← `(example : ((eval% ((pgcl' {$C}).vp $O Direction.Lower heylo {$P}).opt) : 𝔼r[String]).sem ≤ (heylo {$Q} : 𝔼r[_]).sem := by
  -- elabCommand (← `(example : ((((pgcl' {$C}).vp $O Direction.Lower heylo {$P}).opt) : 𝔼r[String]).sem ≤ (heylo {$Q} : 𝔼r[_]).sem := by
  -- elabCommand (← `(example : (eval% (($C).vp $O Direction.Upper $P).opt) = sorry := by
    intro σ
    conv => left; simp [BinOp.sem, UnOp.sem, hnot, hconot, QuantOp.sem]; simp [sem, BinOp.sem, UnOp.sem, hnot, hconot, QuantOp.sem]
    conv => right; simp [BinOp.sem, UnOp.sem, hnot, hconot, QuantOp.sem]; simp [sem, BinOp.sem, UnOp.sem, hnot, hconot, QuantOp.sem]
    try (
      $[$gens]*
      try simp only
      -- clear! σ
      )
    exact $proof))

  -- pure ()

def C : pGCL' Ident :=
  (pGCL'.assign ⟨"n"⟩ 1).seq <|
  pGCL'.loop (.Binary .Lt (.Var ⟨"n"⟩) 10)
    ((HeyLo.Binary .Le (.Var ⟨"n"⟩) 10).iver * 10)
    (.assign ⟨"n"⟩ (.Var ⟨"n"⟩ + 1))

#check pgcl' {n := 1 ; while n < 10 inv ~heylo {n ≤ 10}.iver * 10 { n := n + 1 }}

@[grind =, simp]
theorem ENNReal.himp_zero_le (x y : ENNReal) : x ⇨ 0 ≤ y ↔ (x = 0 → y = ⊤) := by
  simp_all [himp]; split_ifs
  · grind
  · simp_all
@[grind =, simp]
theorem ENNReal.himp_zero_eq_zero (x : ENNReal) : x ⇨ 0 = 0 ↔ (¬x = 0) := by
  suffices x ⇨ 0 ≤ 0 ↔ (¬x = 0) by simpa
  rw [himp_zero_le]
  simp
@[grind =, simp]
theorem ENNReal.hcoimp_zero_eq_zero (x y : ENNReal) : x ↜ y = 0 ↔ y ≤ x := by
  simp [hcoimp]
  constructor
  · if x < y then simp_all else simp_all
  · simp_all

@[simp]
theorem ENNReal.hcoimp_zero_eq_zero' (x y z : ENNReal) (hz : z ≠ ⊤) :
    (i[x = 0] : ENNReal) * (⊤ : ENNReal) ⇨ y ≤ z ↔ x = 0 ∧ y ≤ z := by
  simp [himp]
  if x = 0 then
    simp_all
    split_ifs <;> simp_all
  else
    simp_all

@[grind =, simp]
theorem ENNReal.max_hcoimp (x y : ENNReal) : max x (⊤ ↜ y) = x := by simp [hcoimp]
@[grind =, simp]
theorem ENNReal.lt_himp (x y z : ENNReal) (hx : x < ⊤) : x < y ⇨ z ↔ (z < y → x < z) := by
  simp_all [himp]
  split_ifs
  · simp_all
  · simp_all
@[grind =, simp]
theorem ENNReal.zero_himp (x : ENNReal) : 0 ⇨ x = ⊤ := by
  simp_all [himp]

pgcl_verify wp[𝒟]⟦n := 2; while n = 2 inv 3 * [n = 2] + n * [¬n = 2] {n := 3}⟧(n) ≤ 11 := by
  norm_num
  intro i
  if i = 2 then
    simp_all
  else
    simp_all

theorem ENNReal.log_div {x y : ENNReal} : (x / y).log = x.log - y.log := by
  convert_to (x * y⁻¹).log = x.log - y.log
  rw [ENNReal.log_mul_add]
  rw [ENNReal.log_inv]
  rfl
@[grind =, simp]
theorem ENNReal.log₂_div_2 {x : ENNReal} : (x / 2).log₂ = x.log₂ - 1 := by
  simp [log₂, logb, ENNReal.log_div]
  convert_to (x.log + -log 2) * (log 2)⁻¹ = x.log₂ - 1
  rw [EReal.right_distrib_of_nonneg_of_ne_top]
  · simp
    have : (log 2 * (log 2)⁻¹) = 1 := by
      show (log 2 / log 2) = 1
      simp [EReal.div_self]
    simp [this]
    simp [log₂, logb]
    congr
  · refine EReal.inv_nonneg_of_nonneg ?_
    simp
  · refine lt_top_iff_ne_top.mp (EReal.inv_lt_top (log 2))



example {c y : ENNReal} : c + ↑i[0 < y] * (1 + ↑⌊y.log₂.toENNReal⌋ₑ) ≤ c + ↑i[0 < y] * 3 ∧
  ∀ (i y' : ENNReal),
    i + ↑i[0 < y'] * (1 + ↑⌊y'.log₂.toENNReal⌋ₑ) <
        ↑i[0 < y'] * (⊤ : ENNReal) ⇨
          ↑(1 / 2 : ENNReal) * (i + 1 + ↑i[¬y' = 0] * (1 + ↑⌊(y' / 2).log₂.toENNReal⌋ₑ)) + ↑(1 / 2 : ENNReal) * i →
      i + ↑i[0 < y'] * (1 + ↑⌊y'.log₂.toENNReal⌋ₑ) < ↑i[y' = 0] * (⊤ : ENNReal) ⇨ i → c = ⊤ ∨ ↑i[0 < y] * 3 = (⊤ : ENNReal) := by
  have : ¬(c = ⊤ ∨ ↑i[0 < y] * 3 = (⊤ : ENNReal)) := by sorry
  simp [this]
  constructor
  · sorry
  intro c y
  obtain ⟨c, ⟨_⟩⟩ : ∃ (n : ℕ), c = n := by sorry
  obtain ⟨y, ⟨_⟩⟩ : ∃ (n : ℕ), y = n := by sorry
  if hy : 0 < y then
    have : ¬(y : ENNReal).log₂ = ⊤ := by
      simp [ENNReal.log₂, ENNReal.logb]
      sorry
    simp [hy, (pos_iff_ne_zero.mp hy : y ≠ 0), this]
    ring_nf
    gcongr
    · exact ENNReal.inv_mul_le_one 2
    · rw [mul_comm, ← mul_assoc]
      apply le_of_eq
      convert one_mul (a:=(c:ENNReal))
      refine ENNReal.mul_inv_cancel ?_ ?_
      · exact Ne.symm (NeZero.ne' 2)
      · exact Ne.symm ENNReal.top_ne_ofNat
    · refine (ENNReal.toReal_le_toReal ?_ ?_).mp ?_
      · simp
        refine ENNReal.mul_ne_top ?_ ?_
        · simp
        · simp
          refine lt_top_iff_ne_top.mp ?_
          refine EReal.sub_lt_of_lt_add ?_
          have : (⊤ : EReal) + 1 = ⊤ := rfl
          simp [this]; clear this
          exact Ne.lt_top' (this ·.symm)
      · simp
      · simp
        rw [EReal.toENNReal_sub (by simp)]
        have : EReal.toENNReal 1 = 1 := by refine
          (ENNReal.toReal_eq_one_iff (EReal.toENNReal 1)).mp ?_; simp
        rw [this, ENat.floor_sub_one]
        simp
        grw [ENNReal.toReal_sub_of_le]
        · simp [mul_sub]
          field_simp
          ring_nf
          apply le_add_of_le_add_right (b:=0) _ (by simp)
          simp
          apply le_mul_of_le_mul_of_nonneg_left (c:=1) _ (by simp) (by simp)
          simp
          gcongr
          · simp
          · simp
            refine ENat.le_floor.mp ?_
            gcongr
            apply le_of_eq
            apply EReal.toENNReal_of_ne_top ‹_›
        · rcases y
          sorry
        · simp [*]
  else
    have : y = 0 := by exact Nat.eq_zero_of_not_pos hy
    subst_eqs
    simp

@[grind =, simp]
theorem EReal.floor_toNat (x : ℕ) : ⌊↑(x : ENNReal)⌋ₑ.toNat = x := by
  induction x with simp_all
  | succ x ih =>
    congr
    rcases x with _ | x
    · simp
    rw [← ENat.toNat_eq_iff]
    · exact ih
    · simp

theorem Idkaskdaskd (x b : ℕ) : (⌊((x : ENNReal).logb b).toENNReal⌋ₑ = ⌊x⌋ₑ.toNat.log b)  := by
  have : ⌊(1 : ENNReal).toReal⌋ = 1 := by simp
  simp [ENNReal.logb]
  simp [EReal.div_eq_inv_mul]
  rcases x with _ | x
  · simp
    rcases b with _ | _ | b
    · simp
    · simp
    simp only [Nat.cast_add, Nat.cast_one]
    rw [EReal.mul_bot_of_pos]
    · simp
    · refine EReal.inv_pos_of_pos_ne_top ?_ ?_
      · simp; norm_cast; omega
      · simp
  rw [EReal.toENNReal_mul']
  · simp
    refine (ENat.toNat_eq_iff ?_).mp ?_
    · simp
      sorry
    · sorry

example {c y : ENNReal} : ↑i[∃ (n : ℕ), y = ↑n] * ↑i[∃ (n : ℕ), c = ↑n] * (c + ↑i[0 < y] * (1 + ↑⌊y.toReal⌋.toNat.log2)) ≤
    ↑i[∃ (n : ℕ), y = ↑n] * ↑i[∃ (n : ℕ), c = ↑n] * (c + ↑i[0 < y] * 3) ∧
  ∀ (c' y' : ENNReal),
    ↑i[∃ (n : ℕ), y' = ↑n] * ↑i[∃ (n : ℕ), c' = ↑n] * (c' + ↑i[0 < y'] * (1 + ↑⌊y'.toReal⌋.toNat.log2)) <
        ↑i[0 < y'] * (⊤ : ENNReal) ⇨
          ↑(1 / 2 : ℚ).toNNRat *
              (↑i[∃ (n : ℕ), c' + 1 = ↑n] * (c' + 1 + ↑i[0 < ⌊y'.toReal / 2⌋] * (1 + ↑(max ⌊y'.toReal / 2⌋ 0).toNat.log2))) +
            ↑(1 / 2 : ℚ).toNNRat * (↑i[∃ (n : ℕ), 0 = ↑n] * ↑i[∃ (n : ℕ), c' = ↑n] * c') →
      ↑i[∃ (n : ℕ), y' = ↑n] * ↑i[∃ (n : ℕ), c' = ↑n] * (c' + ↑i[0 < y'] * (1 + ↑⌊y'.toReal⌋.toNat.log2)) <
          ↑i[y' = 0] * (⊤ : ENNReal) ⇨ ↑i[∃ (n : ℕ), y' = ↑n] * ↑i[∃ (n : ℕ), c' = ↑n] * c' →
        ↑i[∃ (n : ℕ), y = ↑n] * ↑i[∃ (n : ℕ), c = ↑n] * (c + ↑i[0 < y] * 3) = ⊤ := by
  classical
  have : ∀ (x : ENNReal), ▵ (i[∃ (n : ℕ), x = n] : ENNReal) = (if ∃ (n : ℕ), x = n then 1 else (⊤ : ENNReal)) := by
    intro x
    split_ifs with h
    · simp [h, hcoimp, validate, hnot, himp]
    · simp [h, covalidate, hconot, himp]
  simp only [one_div, ↓existsAndEq, Iverson.iver_True, Nat.cast_one, one_mul]
  -- have : ∀ x, @NNRat.cast ENNReal ENNReal.instNNRatCast ((@OfNat.ofNat ℚ x Rat.instOfNat)⁻¹ : ℚ).toNNRat = (x : ENNReal)⁻¹ := by
  --   sorry
  -- simp [this]
  -- have : ∀ (x : ℕ), (⌊(x : ENNReal).log₂.toENNReal⌋ₑ = ⌊x⌋ₑ.toNat.log2)  := by
  --   intro x
  --   have : ∀ x, ⌊(@Nat.cast ENNReal instAddCommMonoidWithOneENNReal.toNatCast x : ENNReal)⌋ₑ = x := by
  --     intro x
  --     induction x with
  --     | zero => simp
  --     | succ x ih => simp_all
  --   simp [this]
  --   rcases x with _ | _ | x
  --   · simp [ENNReal.log₂, ENNReal.logb]
  --     sorry
  --   · simp [ENNReal.log₂, ENNReal.logb]
  --   · simp [ENNReal.log₂, ENNReal.logb]
  --     refine (ENat.toNat_eq_iff ?_).mp ?_
  --     · simp
  --       rw [Nat.log2_def]
  --       simp
  --     · simp [EReal.toENNReal]
  --       simp_all [EReal.div_eq_iff, EReal.top_mul_of_pos]
  --       simp [EReal.div_eq_inv_mul, EReal.toReal_mul, ENNReal.ofReal_mul', EReal.toReal_nonneg]
  --       refine (ENat.toNat_eq_iff ?_).mpr ?_
  --       · simp_all
  --         exact
  --           Nat.add_one_ne_zero
  --             (Nat.rec (motive := fun x ↦ ℕ → ℕ) (fun x ↦ 0)
  --               (fun x ih n ↦ Bool.rec 0 (ih (n.div 2)).succ (Nat.ble 2 n)) (x + 1)
  --               ((x + 1 + 1).div 2))
  --       · apply le_antisymm
  --         · simp
  --           ring_nf
  --           sorry
  --         · simp
  --           ring_nf
  --           sorry
  --       sorry
  -- have : ∀ (x : ENNReal), (∃ (n : ℕ), ⌊x⌋ₑ = ↑n) ↔ x ≠ ⊤ := by simp [← ENat.exists_ne_top]
  -- simp [this, ENNReal.div_eq_top]
  have : ∀ (n : ℕ), ((OfNat.ofNat n : ℚ)⁻¹.toNNRat : ENNReal) = (n : ENNReal)⁻¹ := by
    intro n
    refine ENNReal.eq_inv_of_mul_eq_one_left ?_
    norm_num
    have : (n : ENNReal) = ((n : ℚ).toNNRat : ENNReal) := by simp
    rw [this]
    have := Rat.toNNRat_mul (p:=2⁻¹) (q:=2) (by simp) |>.symm
    simp at this
    have := congrArg (@NNRat.cast ENNReal ENNReal.instNNRatCast) this
    simp at this
    convert this
    norm_cast
    sorry
  simp [this]
  if hy : (∃ (n : ℕ), y = ↑n) ∧ ∃ (n : ℕ), c = ↑n then
    obtain ⟨⟨y, ⟨_⟩⟩, ⟨c, ⟨_⟩⟩⟩ := hy
    simp_all
    constructor
    · sorry
    · intro c' y'
      if h' : (∃ (n : ℕ), y' = ↑n) ∧ ∃ (n : ℕ), c' = ↑n then
        obtain ⟨⟨y', ⟨_⟩⟩, ⟨c', ⟨_⟩⟩⟩ := h'
        have : ∃ (n : ℕ), (↑c' : ENNReal) + 1 = ↑n := by use c' + 1; simp
        have : ⌊↑(y' : ℝ) / 2⌋ = y' / 2 := by
          sorry
        simp_all [Nat.cast_inj, exists_eq', Iverson.iver_True, Nat.cast_one, mul_one,
          Nat.cast_pos, ENNReal.toReal_natCast, Int.floor_natCast, Int.toNat_natCast, one_mul,
          Nat.cast_eq_zero]
        sorry
      else
        replace h' := Classical.not_and_iff_not_or_not.mp h'
        rcases h' with h' | h'
        · simp_all
          if hc : ∃ (n : ℕ), c' = ↑n then
            obtain ⟨c', ⟨_⟩⟩ := hc
            have : ∃ (n : ℕ), (↑c' : ENNReal) + 1 = ↑n := by use c' + 1; simp
            simp [this]
            have : 0 < ((2 : ℚ)⁻¹.toNNRat : ENNReal) := by
              refine (ENNReal.toNNReal_lt_toNNReal ?_ ?_).mp ?_
              · simp
              · simp
              · simp
                sorry
            simp [this, Iverson.iver]
          else
            sorry
        · simp_all
          sorry
  else

    have : ¬(∃ (n : ℕ), y = ↑n) ∨ ¬∃ (n : ℕ), c = ↑n := Classical.not_and_iff_not_or_not.mp hy
    rcases this with (h | h)
    · simp [h]
      intro c' y'
      if h' : (∃ (n : ℕ), y' = ↑n) ∧ ∃ (n : ℕ), c' = ↑n then
        obtain ⟨⟨y', ⟨_⟩⟩, ⟨c', ⟨_⟩⟩⟩ := h'
        simp
        rcases y' with _ | y'
        · simp
        · simp
          sorry
      else
        have : ¬(∃ (n : ℕ), y' = ↑n) ∨ ¬∃ (n : ℕ), c' = ↑n := Classical.not_and_iff_not_or_not.mp h'
        rcases this with (h | h)
        · simp [h]
          simp_all
          sorry
        · simp_all
          -- simp [h]
          have : ¬∃ (n : ℕ), c' + 1 = ↑n := by
            simp only [not_exists]
            intro x
            rcases x with (_ | x)
            · simp
            · simp
              specialize h x
              sorry
          simp [h, this]
          simp [Iverson.iver]
    · simp [h]
    -- simp [hy]
    -- intro c' y'
    -- if hy'_top : y' ≠ ⊤ then
    --   have : ∃ (n : ℕ), ⌊y' / 2⌋ₑ = ↑n := by
    --     refine ENat.exists_ne_top.mp ?_
    --     simp
    --     apply ENNReal.div_ne_top hy'_top (by simp)
    --   simp [this]
    --   have : (↑(2 : ℚ)⁻¹.toNNRat : ENNReal) = 1/2 := by
    --     sorry
    --   simp [this]
    --   if hy' : ∃ (n : ℕ), y' = ↑n then
    --     obtain ⟨y', ⟨_⟩⟩ := hy'
    --     simp
    --     ring_nf
    --     sorry
    --   else
    --     simp [hy']
    --     if y' = 0 then
    --       simp_all
    --     else
    --       simp_all
    -- else
    --   simp at hy'_top
    --   subst_eqs
    --   simp_all only [not_exists, ENNReal.top_ne_natCast, exists_const, Iverson.iver_False,
    --     CharP.cast_eq_zero, ENNReal.zero_lt_top, Iverson.iver_True, Nat.cast_one, ENNReal.log_top,
    --     EReal.toENNReal_top, ENat.floor_top, ENat.toENNReal_top, add_top, one_mul, zero_mul,
    --     top_himp, add_pos_iff, CanonicallyOrderedAdd.mul_pos, Nat.cast_pos, zero_lt_one, or_true,
    --     true_or, and_true, ENNReal.top_ne_zero, ENNReal.zero_himp, forall_const]
    --   sorry

structure Conditions (D : Direction) where
  original : pGCL' String
  O : Optimization
  post : 𝔼r[String]
  pre : 𝔼r[String]
  encoding : 𝔼r[String]
  prop : (original.HeyVL O D (original.fv ∪ post.fv)).2.vp post = encoding
  fv : Globals String
  fv_prop : fv = original.fv ∪ post.fv ∪ pre.fv


def C₀ := pgcl' {
    while 0 < y
      inv [isNat y] * [isNat c] * (c + [0 < y] * (y + nfloor (nlog₂ y)))
    {
      { y := nfloor (y / 2) } [1/2] { y := y - 1 } ; c := c + 1
    }
  }

def C' : Conditions .Lower where
  original := C₀
  O := 𝒟
  post := heylo { [isNat y] * [isNat c] * c }
  pre := heylo { [isNat y] * [isNat c] * (c + [0 < y] * 3) }
  encoding := eval% ((C₀.HeyVL 𝒟 .Lower {"c", "y"}).2.vp heylo { [isNat y] * [isNat c] * c }).opt
  prop := by decide +native
  fv := {"c", "y"}
  fv_prop := by decide

def Conditions.sound (C : Conditions D) : Prop :=
  match D with
  | .Lower => wp[C.O]⟦~C.original.pGCL⟧ C.post.sem ≤ C.post.sem
  | .Upper => C.post.sem ≤ wlp''[C.O]⟦~C.original.pGCL⟧ C.post.sem

def Conditions.show (C : Conditions .Lower) (h : C.encoding.sem ≤ C.post.sem) : C.sound := by
  simp [sound]
  apply le_trans pGCL'.wp_le_vp
  rw [C.prop]
  exact h

example : C'.sound := by
  apply C'.show
  simp [C']
  intro σ
  simp [BinOp.sem, UnOp.sem, sem, Fun.sem]
  simp only [DFunLike.coe]
  simp
  sorry

-- pgcl_verify wp[𝒟]⟦
-- while 0 < y
--   inv [isNat y] * [isNat c] * (c + [0 < y] * (y + nfloor (nlog₂ y)))
-- {
--   { y := nfloor (y / 2) } [1/2] { y := y - 1 } ; c := c + 1
-- }⟧([isNat y] * [isNat c] * c) ≤ [isNat y] * [isNat c] * (c + [0 < y] * 3) := by

--   simp [Fun.sem]
--   simp [DFunLike.coe]
--   rename_i σ
--   generalize σ "c" = c
--   generalize σ "y" = y
--   norm_num
--   if (∃ (n : ℕ), y = ↑n) ∧ (∃ (n : ℕ), c = ↑n) then
--     simp_all
--   else
--     simp_all
--   sorry
  -- norm_num
  -- have : ¬(c = ⊤ ∨ ↑i[0 < y] * 3 = (⊤ : ENNReal)) := by
  --   sorry
  -- simp [this]
  -- constructor
  -- · sorry
  -- intro c y
  -- obtain ⟨c, ⟨_⟩⟩ : ∃ (n : ℕ), c = n := by sorry
  -- obtain ⟨y, ⟨_⟩⟩ : ∃ (n : ℕ), y = n := by sorry
  -- if hy : 0 < y then
  --   simp [hy, (pos_iff_ne_zero.mp hy : y ≠ 0)]
  --   ring_nf
  --   sorry
  -- else
  --   have : y = 0 := by exact Nat.eq_zero_of_not_pos hy
  --   subst_eqs
  --   simp

-- pgcl_verify wp[𝒟]⟦~C⟧ (.Var ⟨"n"⟩) ≤ 11 := by
--   simp
--   norm_num
--   intro x
--   rename_i σ
--   generalize x (σ[{ name := "n" } ↦ 1]) = x
--   have : ∃ (y : ℕ), x = y := sorry
--   obtain ⟨x, _, _⟩ := this
--   set n := σ ⟨"n"⟩
--   have : ∀ (a : ENNReal), (⊤ ↜ a) = 0 := by simp [hcoimp]
--   have : ∀ (a b : ENNReal), b < ⊤ → ((a ⇨ 0) ≤ b ↔ a ≠ 0) := by
--     simp [himp]
--     intro a b hb
--     split_ifs
--     · grind
--     · simp_all
--   have : ∀ (a : ENNReal), ((a ⇨ 0) = 0 ↔ a ≠ 0) := by
--     have : (⊤ : ENNReal) ≠ 0 := ENNReal.top_ne_zero
--     simp [himp, this]
--   -- have : ∀ (a b : ENNReal), ((a * ⊤ ⇨ b) = if a = 0 then ⊤ else b) := by
--   --   simp [himp]
--   --   intro a b
--   --   split_ifs
--   --   · simp_all
--   --   · simp_all
--   --   · simp_all
--   --   · simp_all
--   have : ∀ (p : Prop) [Decidable p] (b : ENNReal), (((i[p] : ENNReal) * ⊤ ⇨ b) = if p then b else ⊤) := by
--     simp [himp]
--     intro a b
--     split_ifs
--     · simp_all
--     · simp_all
--   have : ∀ (p : Prop), i[p] = 0 ↔ ¬p := by simp [Iverson.iver]
--   simp_all
--   if x < 10 then
--     simp_all [le_of_lt, not_le_of_gt, hcoimp, Iverson.iver]
--     sorry
--   else
--     simp [*, le_of_lt, not_le_of_gt, Std.not_lt.mp, hcoimp]
--     have : 10 ≤ x := by (expose_names; exact Std.not_lt.mp h)
--     simp_all [le_of_lt, not_le_of_gt, hcoimp, Iverson.iver]
--     if x = 10 then
--       simp_all
--     else
--       split_ifs
--       · omega
--       · simp_all

--     simp_all
--     intro h
--     sorry
--     -- have : ¬10 ≤ x := by apply?
--   simp [this]
--   grind
--   if x (σ[{ name := "n" } ↦ 1]) ≤ 10 then
--     simp_all +arith
--     if x (σ[{ name := "n" } ↦ 1]) < 10 then
--       simp_all +arith
--     else
--       simp_all +arith
--   else
--     simp_all +arith
--   split_ifs
--   · simp_all

--   simp only [inf_le_iff, Nat.one_le_ofNat, -true_or]
--   sorry

-- example : (eval% C.vp 𝒜 .Upper ⊤).sem = fun _ ↦ sorry := by
--   clear! ϖ
--   ext σ
--   simp [BinOp.sem, UnOp.sem, hnot]
--   generalize σ ⟨"n"⟩ = n
--   clear σ
--   sorry
