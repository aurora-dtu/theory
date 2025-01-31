import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.List.OfFn

namespace List

variable {α : Type*}

@[simp]
theorem ofFn_head (f : Fin n → α) (h : 0 < n) :
    (List.ofFn f).head (by simp only [ne_eq, List.ofFn_eq_nil_iff] ; omega) = f ⟨0, by omega⟩ := by
  obtain ⟨k, _⟩ := Nat.exists_eq_succ_of_ne_zero h.ne.symm
  simp_all only [Nat.succ_eq_add_one, List.ofFn_succ, Fin.cast_zero, List.head_cons]
  rfl

@[simp]
theorem ofFn_tail (f : Fin n → α) :
    (List.ofFn f).tail = List.ofFn (fun (i : Fin (n - 1)) ↦ f ⟨i + 1, by omega⟩) := by
  by_cases h : n = 0
  · simp_all only [List.ofFn_zero, List.tail_nil, ge_iff_le, zero_le, tsub_eq_zero_of_le]
  · obtain ⟨k, ih⟩ := Nat.exists_eq_succ_of_ne_zero h
    simp only [ih, Nat.succ_eq_add_one, List.ofFn_succ, Fin.cast_zero, List.tail_cons,
      add_tsub_cancel_right, Fin.coe_cast, List.ofFn_inj]
    rfl

@[simp]
theorem ofFn_getLast (f : Fin n → α) (h : 0 < n) :
    (List.ofFn f).getLast (by simp only [ne_eq, List.ofFn_eq_nil_iff] ; omega) = f ⟨n - 1, by omega⟩
:= by
  induction n with
  | zero => absurd h ; omega
  | succ n ih =>
    simp only [List.ofFn_succ, add_tsub_cancel_right]
    by_cases pos : 0 < n
    · have ne_zero : ¬n = 0 := by omega
      rw [List.getLast_cons]
      · simp only [ih (f ·.succ) pos, Fin.succ_mk, Nat.succ_eq_add_one]
        congr
        omega
      · simp only [ne_eq, List.ofFn_eq_nil_iff, ne_zero, not_false_eq_true]
    · simp only [not_lt, nonpos_iff_eq_zero] at pos
      simp only [pos, List.ofFn_zero, List.getLast_singleton, Fin.zero_eta]

end List
