import HeyLo.Basic
import HeyLo.Syntax
import Mathlib.Tactic.Eval

open Optimization.Notation
open HeyLo

def HeyLo.opt : HeyLo α → HeyLo α
  | .Var x t => .Var x t
  | .Lit .Infinity => .Lit .Infinity
  | .Lit (.Frac q) => .Lit (.Frac q)
  | .Lit (.UInt h n) => .Lit (.UInt h n)
  | .Lit (.Bool b) => .Lit (.Bool b)
  | .Subst a b c => .Subst a b.opt c.opt
  | .Ite b l r => .Ite b l.opt r.opt
  | .Binary .CoImpl l r => .Binary .CoImpl l.opt r.opt
  | .Binary .Impl l r => .Binary .Impl l.opt r.opt
  | .Binary .Sup l r => .Binary .Sup l.opt r.opt
  | .Binary .Inf l r => .Binary .Inf l.opt r.opt
  | .Binary (.Div h) l r => .Binary (.Div h) l.opt r.opt
  | .Binary (.Mul h) l r => .Binary (.Mul h) l.opt r.opt
  | .Binary (.Sub h) l r => .Binary (.Sub h) l.opt r.opt
  | .Binary (.Add h) l r => .Binary (.Add h) l.opt r.opt
  | .Binary (.Gt h) l r => .Binary (.Gt h) l.opt r.opt
  | .Binary (.Ge h) l r => .Binary (.Ge h) l.opt r.opt
  | .Binary (.Ne h) l r => .Binary (.Ne h) l.opt r.opt
  | .Binary (.Le h) l r => .Binary (.Le h) l.opt r.opt
  | .Binary (.Lt h) l r => .Binary (.Lt h) l.opt r.opt
  | .Binary .Eq l r => .Binary .Eq l.opt r.opt
  | .Binary .Or l r => .Binary .Or l.opt r.opt
  | .Binary .And l r => .Binary .And l.opt r.opt
  | .Unary (@UnOp.Not .ENNReal) x => .Unary (@UnOp.Not .ENNReal) x.opt
  | .Unary (@UnOp.Not .Nat) x => .Unary (@UnOp.Not .Nat) x.opt
  | .Unary (@UnOp.Not .Bool) x => .Unary (@UnOp.Not .Bool) x.opt
  | .Unary .Non x => .Unary .Non x.opt
  | .Unary .Iverson x => .Unary .Iverson x.opt
  | .Unary .Embed x => .Unary .Embed x.opt
  | .Unary .NatToENNReal x => .Unary .NatToENNReal x.opt
  | .Call op x => .Call op x
  | .Quant .Sup x e => .Quant .Sup x e.opt
  | .Quant .Inf x e => .Quant .Inf x e.opt
  | .Quant .Exists x e => .Quant .Exists x e.opt
  | .Quant .Forall x e => .Quant .Forall x e.opt

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

structure Conditions (D : Direction) where
  original : pGCL'
  O : Optimization
  post : 𝔼r
  pre : 𝔼r
  encoding : 𝔼r
  prop : original.vp O D post = encoding
  fv : Globals
  fv_prop : fv = original.fv ∪ post.fv ∪ pre.fv

abbrev y : Ident := ⟨"y", .Nat⟩
abbrev c : Ident := ⟨"c", .Nat⟩

syntax "vc[" term "," ident "]" "{" cheylo "}" cpgcl' "{" cheylo "}" : term

macro_rules
| `(vc[$O, wp] { $P } $C { $Q }) =>
  `(
    let C' :=
      eval% (pGCL'.vp pgcl' {$C} 𝒟 .Lower heylo {$Q})
    let P := heylo {$P}
    let C := pgcl' {$C}
    let Q := heylo {$Q}
    ({
      original := C
      O := $O
      pre := P
      post := Q
      fv := C.fv ∪ P.fv ∪ Q.fv
      fv_prop := by decide
      encoding := C'
      prop := by decide +native
    } : Conditions .Lower)
  )

def Conditions.sound (C : Conditions D) : Prop :=
  match D with
  | .Lower => wp[C.O]⟦~C.original.pGCL⟧ C.post.sem ≤ C.pre.sem
  | .Upper => C.pre.sem ≤ wlp''[C.O]⟦~C.original.pGCL⟧ C.post.sem

def Conditions.show (C : Conditions .Lower) (h : C.encoding.sem ≤ C.pre.sem) : C.sound := by
  simp [sound]
  apply le_trans pGCL'.wp_le_vp
  simpa [C.prop]

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
theorem ENNReal.two (q : ENNReal) : 2⁻¹ * q * 2 = q := by
  rw [mul_comm, ← mul_assoc]
  simp [*]

def C₀ :=
  vc[𝒟, wp]
    { ↑c + [0 < y] * ↑(y + nlog₂ y) }
      while 0 < y
        inv ↑c + [0 < y] * ↑(y + nlog₂ y)
      {
        { y := y / 2 } [1/2] { y := y - 1 } ; c := c + 1
      }
    { ↑c }

theorem C₀.soundess : C₀.sound := by
  apply C₀.show fun σ ↦ ?_
  simp [C₀]
  simp [BinOp.sem, UnOp.sem, sem, Fun.sem]
  set c : ℕ := σ c; set y : ℕ := σ y
  intro c' y'
  have : ∀ {a b : ENNReal}, (~~a ≤ b ↔ a = 0 ∨ b = ⊤) := by simp +contextual [hconot]; grind
  simp [this]; left
  rcases y' with _ | y' <;> simp
  grw [Nat.log2_div_2, (by gcongr; omega : Nat.log2 y' ≤ Nat.log2 (y' + 1))]
  repeat rw [Nat.cast_add]
  if h₁ : 0 < y' then
    simp [h₁, (by omega : 0 < (y' + 1) / 2)]
    grw [(by omega : (y' + 1) / 2 ≤ (y' + 1))]
    simp [← ENNReal.toReal_le_toReal, ENNReal.mul_eq_top, ENNReal.toReal_add]
    rw [ENNReal.toReal_sub_of_le]
    · simp; ring_nf; rfl
    · simp; apply (Nat.le_log2 ?_).mpr <;> omega
    · simp
  else
    have : y' = 0 := by omega
    subst_eqs
    ring_nf
    simp [add_comm]

/--
info: 'C₀.soundess' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]
-/
#guard_msgs in
#print axioms C₀.soundess

-- end
