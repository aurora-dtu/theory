-- import Mathlib.Algebra.BigOperators.Group.List
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Indexes

namespace List

variable {α : Type*}

theorem eq_iff_head_and_tail_eq (l₁ l₂ : List α) {hh₁ : l₁ ≠ []} {hh₂ : l₂ ≠ []} (h_head : l₁.head hh₁ = l₂.head hh₂) (h_tail : l₁.tail = l₂.tail) : l₁ = l₂ := by
  induction l₁
  · exact False.elim (hh₁ rfl)
  · induction l₂
    · exact False.elim (hh₂ rfl)
    · simp_all only [ne_eq, head, not_false_eq_true, tail_cons]

theorem head_eq_get {L : List α} (h : L ≠ []) : L.head h = L.get ⟨0, length_pos.mpr h⟩ :=
  symm <| get_mk_zero (length_pos.mpr h)

theorem get_concat {L : List α} {x : α} (i : Fin L.length) : (L.concat x).get ⟨i, by
  simp only [List.concat_eq_append, List.length_append, List.length_singleton]
  exact Nat.lt_add_right 1 i.isLt
  ⟩ = L.get i := by
  simp only [get_eq_getElem, concat_eq_append, getElem_append, Fin.is_lt, ↓reduceDIte]

-- theorem get_tail {L : List α} (i : Fin (L.length - 1)) : L.tail.get ⟨i, by simp⟩ = L.get ⟨i + 1, by omega⟩ := by
--   induction L with
--   | nil => simp_all only [tail_nil, length_nil, Fin.eta, get_eq_get?, get?_nil]
--   | cons => simp_all only [get_eq_getElem, tail_cons, length_cons, Nat.add_succ_sub_one,
--     Nat.add_zero, Fin.eta, getElem_cons_succ]

theorem tail_getLast {L : List α} (h : L.tail ≠ []) : L.tail.getLast h = L.getLast (by simp_all ; exact ne_of_apply_ne tail h) := by
  unfold getLast
  split <;> (simp_all only [ne_eq, not_false_eq_true, heq_eq_eq] ; try split ; all_goals simp_all)

theorem take_succ_getLast {L : List α} (i : Fin L.length) (h : L ≠ []) : (L.take (i + 1)).getLast (by simp [h]) = L.get i := by
  rw [getLast_eq_getElem]
  have : ↑i + 1 ≤ L.length := by omega
  simp only [length_take, this, min_eq_left, add_tsub_cancel_right, getElem_take, get_eq_getElem]

theorem take_getLast {L : List α} (hL : L ≠ []) (i : Fin (L.length)) (h : 0 < i.val) : (L.take i).getLast (by
  simp [hL]
  exact Nat.not_eq_zero_of_lt h
  ) = L.get ⟨i - 1, by omega⟩ := by
  let ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h.ne.symm
  simp_all only [Nat.succ_eq_add_one, add_tsub_cancel_right, get_eq_getElem]
  rw [L.take_succ_getLast ⟨m, _⟩ hL]
  rfl

theorem take_head {L : List α} (h : L ≠ []) (i : ℕ) : (L.take (i + 1)).head (by simp [h]) = L.head h := by
  simp [head_eq_get, get_eq_getElem]

theorem mem_take_of_mem {L : List α} (i j : ℕ) (h₁ : i < L.length) (h₂ : j ≤ i) : L[j] ∈ L.take (i + 1) := by
  induction L using List.list_reverse_induction generalizing i j with
  | base => simp at h₁
  | ind l e =>
    simp only [length_append, length_singleton] at h₁
    apply mem_iff_get.mpr
    use ⟨j, by simp ; omega⟩
    simp only [get_eq_getElem, getElem_take]

theorem tail_getElem (L : List α) (i : Fin (L.length - 1)) : L.tail[i] = L[i.val + 1] := by
  simp only [tail, Fin.getElem_fin]
  split
  · absurd i.prop
    simp
  · simp

theorem tail_getElem? {L : List α} (i : ℕ) : L.tail[i]? = if h : i < L.length - 1 then some L[i + 1] else none := by
  split_ifs
  · simp_all
  · simp_all

theorem prod_step (L : List ENNReal) (h : L ≠ []) : L.prod = L.head h * L.tail.prod := by
  induction L
  · contradiction
  · simp only [List.prod_cons, List.head_cons, List.tail_cons]

theorem step_prod (L : List ENNReal) (h : L ≠ []) : L.prod = (L.take (L.length - 1)).prod * L.getLast h := by
  induction L using List.list_reverse_induction
  · contradiction
  · simp only [List.prod_append, List.prod_cons, List.prod_nil, mul_one, List.length_append,
    List.length_cons, List.length_nil, zero_add, add_tsub_cancel_right, List.take_left', ne_eq,
    List.cons_ne_self, not_false_eq_true, List.getLast_append_of_ne_nil, List.getLast_singleton]

@[simp]
theorem ofFn_head {n : ℕ} (f : Fin n → α) (h : 0 < n) : (List.ofFn f).head (by simp only [ne_eq, List.ofFn_eq_nil_iff] ; omega) = f ⟨0, by omega⟩ := by
  obtain ⟨k, _⟩ := Nat.exists_eq_succ_of_ne_zero h.ne.symm
  simp_all only [Nat.succ_eq_add_one, List.ofFn_succ, Fin.cast_zero, List.head_cons]
  rfl

@[simp]
theorem ofFn_tail {n : ℕ} (f : Fin n → α) : (List.ofFn f).tail = List.ofFn (fun (i : Fin (n - 1)) ↦ f ⟨i + 1, by omega⟩) := by
  by_cases h : n = 0
  · simp_all only [List.ofFn_zero, List.tail_nil, ge_iff_le, zero_le, tsub_eq_zero_of_le]
  · obtain ⟨k, ih⟩ := Nat.exists_eq_succ_of_ne_zero h
    simp only [ih, Nat.succ_eq_add_one, List.ofFn_succ, Fin.cast_zero, List.tail_cons,
      add_tsub_cancel_right, Fin.coe_cast, List.ofFn_inj]
    rfl

@[simp]
theorem ofFn_getLast {n : ℕ} (f : Fin n → α) (h : 0 < n) : (List.ofFn f).getLast (by simp only [ne_eq, List.ofFn_eq_nil_iff] ; omega) = f ⟨n - 1, by omega⟩ := by
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
  -- obtain ⟨k, _⟩ := Nat.exists_eq_succ_of_ne_zero h.ne.symm
  -- simp_all [Nat.succ_eq_add_one, List.ofFn_succ, Fin.cast_zero, List.head_cons]
  -- rfl

theorem mem_not_mem_dropLast (x : α) (l : List α) (h : x ∈ l) (h' : x ∉ l.dropLast) : x = l.getLast (l.ne_nil_of_mem h) := by
  by_contra q
  have ⟨n, hn, hn'⟩ := List.mem_iff_getElem.mp h
  absurd List.mem_iff_getElem.not.mp h'
  simp
  use n
  refine Exists.intro ?h.w hn'
  simp_all [List.getLast_eq_getElem]
  have : ¬n = l.length - 1 := fun q' ↦ by have := ne_of_eq_of_ne hn' q ; simp [q'] at this
  omega

-- @[simp]
-- theorem flatMap_singleton_subtype' {α : Type u_1} {p : α → Prop} (l : List {x : α // p x}) :
--   (l.flatMap fun x => [x.val]) = l.map fun x ↦ x.val
-- := by
--   exact List.map_eq_flatMap
--   cases l with
--   | nil =>
--     simp
--   | cons x xs =>
--     simp_all

def mk_Fintype' [Fintype α] [DecidableEq α] (n : ℕ) : Fintype (Fin n → α) := by
  exact Pi.instFintype

def mk_Fintype [Fintype α] [DecidableEq α] (n : ℕ) : Fintype { l : List α // l.length ≤ n } where
  elems := (Finset.range (n + 1)).attach.biUnion (fun i ↦ (@Pi.instFintype (Fin i) (fun _ ↦ α) _ _).elems.image (fun f ↦ ⟨List.ofFn f, by have := Finset.mem_range.mp i.prop ; simp ; omega⟩))
  complete := by
    intro ⟨l, h⟩
    simp [Fintype.complete]
    use l.length
    constructor
    · omega
    · use fun i ↦ l[i]
      simp

-- def mk_mem_finset [DecidableEq α] (n : ℕ) (S : Finset α) : Fintype { l : List α // l.length ≤ n ∧ l.all (· ∈ S) } where
--   elems := (Finset.range (n + 1)).attach.biUnion (fun i ↦ by
--     have : Finite (Fin i → S) := Pi.finite
--     let x : Fintype (Fin i → S) := mk_Fintype' i.val
--     simp_all
--     exact x.elems.image (fun (f : Fin i → S) ↦ ⟨@List.ofFn S i.val f, by have := Finset.mem_range.mp i.prop ; simp [Function.comp] ; omega⟩))
--   complete := by
--     intro ⟨l, h⟩
--     simp only [List.pure_def, List.bind_eq_bind, bind_singleton_subtype', List.map_ofFn,
--       Finset.mem_biUnion, Finset.mem_attach, Finset.mem_image, Fintype.complete, Subtype.mk.injEq,
--       true_and, Subtype.exists, Finset.mem_range, exists_prop', nonempty_prop]
--     use l.length
--     constructor
--     · omega
--     · use fun i ↦ ⟨l[i], by simp_all⟩
--       ext
--       simp only [Fin.getElem_fin, List.getElem?_ofFn, Option.mem_def]
--       exact Eq.congr_right rfl

-- def mk_nonempty_mem_finset [DecidableEq α] (n : ℕ) (S : Finset α) : Fintype { l : List α // l ≠ [] ∧ l.length ≤ n ∧ l.all (· ∈ S) } :=
--   let ttt : Fintype { l : List α // l.length ≤ n ∧ l.all (· ∈ S) } := List.mk_mem_finset n S
--   let tt : Finset { l : List α // l.length ≤ n ∧ l.all (· ∈ S) } := Finset.univ
--   let t := Finset.subtype _ (tt.image (·.val))
--   ⟨t, by simp_all [t, tt]⟩

def mk_nonempty_Fintype [Fintype α] [DecidableEq α] (n : ℕ) : Fintype { l : List α // l ≠ [] ∧ l.length ≤ n } :=
  let ttt : Fintype { l : List α // l.length ≤ n } := List.mk_Fintype n
  let tt : Finset { l : List α // l.length ≤ n } := Finset.univ
  let t := Finset.subtype _ (tt.image (·.val))
  ⟨t, by simp_all [t, tt]⟩

theorem find?_if_mem {p : α → Bool} {l : List α} (h : ∃ a ∈ l, p a) : (l.find? p).isSome := by
  induction l with
  | nil => simp_all
  | cons x xs ih =>
    simp_all only [forall_exists_index, and_imp, List.mem_cons, exists_eq_or_imp]
    rcases h with h | h
    · simp_all
    · obtain ⟨a, h, h'⟩ := h
      exact List.Sublist.find?_isSome (List.sublist_cons_self x xs) (ih a h h')
