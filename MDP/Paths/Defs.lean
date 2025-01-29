-- import Mathlib.Data.List.Indexes
import MDP.ListExt
import MDP.Basic

namespace MDP

structure Path (M : MDP State Act) where
  states : List State
  nonempty : states ≠ []
  property : ∀ i (h : i < states.length - 1),
    states[i + 1] ∈ M.succs_univ (states[i])

namespace Path

variable {State : Type*} {Act : Type*}
variable {M : MDP State Act} (π π' : M.Path)

instance [DecidableEq State] : DecidableEq M.Path := fun a b ↦
  if h : a.states = b.states then
    Decidable.isTrue (by cases a; cases b; simp_all)
  else
    Decidable.isFalse (by cases a; cases b; simp_all)

def length := π.states.length
notation "∎|" a "|" => Path.length a

instance instSingleton : Singleton State M.Path where
  singleton s := ⟨[s], by simp, by simp⟩

instance instGetElem : GetElem M.Path ℕ State (fun π i ↦ i < ∎|π|) where
  getElem π i _ := π.states[i]

@[simp] theorem states_getElem_eq_getElem (i : Fin ∎|π|) : π.states[i] = π[i] := rfl
@[simp] theorem states_getElem_eq_getElem_Nat (i : ℕ) (h : i < ∎|π|) : π.states[i] = π[i] := rfl

@[simp] theorem singleton_getElem_nat (h : i < 1) :
    (instSingleton.singleton (α:=State) (β:=M.Path) s)[i] = s := by
  simp only [instSingleton, instGetElem, List.getElem_singleton]
@[simp] theorem singleton_getElem (i : Fin 1) :
    (instSingleton.singleton (α:=State) (β:=M.Path) s)[i] = s := by simp [instSingleton]; rfl

@[simp] theorem states_length_eq_length : π.states.length = ∎|π| := rfl

@[simp] theorem states_nonempty : π.states ≠ [] := π.nonempty
@[simp] theorem length_pos : 0 < ∎|π| := List.length_pos.mpr π.nonempty
@[simp] theorem length_pos' : 1 ≤ ∎|π| := List.length_pos.mpr π.nonempty
@[simp] theorem length_ne_zero : ¬∎|π| = 0 := Nat.not_eq_zero_of_lt π.length_pos

@[simp] theorem length_pred_succ : ∎|π| - 1 + 1 = ∎|π| := by have := π.length_pos; omega

@[simp] theorem fin_succ_le_length (i : Fin (∎|π| - 1)) : ↑i + 1 < ∎|π| := by omega

abbrev last : State := π[∎|π| - 1]

@[simp] theorem succs_succs (i : Fin (∎|π| - 1)) : π[↑i + 1] ∈ M.succs_univ π[↑i] :=
  π.property i.val (by simp)
@[simp] theorem succs_succs_nat {i : ℕ} (h : i < ∎|π| - 1) : π[i + 1] ∈ M.succs_univ π[i] :=
  π.property i h

def take (n : ℕ) : M.Path := ⟨π.states.take (n + 1), by simp, fun i hi ↦ by
  simp
  apply π.succs_succs_nat
  simp at hi
  omega⟩

def prev : M.Path := ⟨if ∎|π| = 1 then π.states else π.states.dropLast, by
  split <;> simp
  have := π.length_pos
  apply List.ne_nil_of_length_pos ?isFalse.x
  simp
  omega, fun i hi ↦ by
  split_ifs with h <;> simp [h] at hi ⊢
  apply π.succs_succs_nat (by omega)⟩

def extend (s : M.succs_univ π.last) : M.Path := ⟨π.states ++ [s.val], by simp, by
  intro i hi
  simp at hi ⊢
  simp_rw [List.getElem_append]
  split_ifs with h₁ h₂ <;> simp_all <;> try omega
  · apply π.succs_succs_nat ; simp at * ; omega
  · have : i = ∎|π| - 1 := by simp_all ; omega
    simp_all
  · simp_all⟩

def succs_univ : Set M.Path := {π' : M.Path | π'.prev = π ∧ 1 < ∎|π'|}

@[simp] theorem mem_succs_univ_prev {π π' : M.Path} (h : π' ∈ π.succs_univ) : π'.prev = π := by
  simp [Path.succs_univ] at h; simp_all
@[simp] theorem succs_univ_prev (π' : π.succs_univ) : π'.val.prev = π := by
  obtain ⟨π', h⟩ := π'; simp_all [mem_succs_univ_prev h]
@[simp] theorem mem_prev_succs_univ (h : 1 < ∎|π|) : π ∈ π.prev.succs_univ := by
  simp [prev, succs_univ, h]

def act := M.act π.last

def tail : M.Path := ⟨if ∎|π| = 1 then π.states else π.states.tail,
  by
    split <;> simp
    have := π.length_pos
    refine List.ne_nil_of_length_pos ?isFalse.x
    simp
    omega,
  by
    intro i hi
    split_ifs with h <;> simp [h] at hi ⊢
    apply π.succs_succs_nat
    omega⟩

def prepend (s : M.prev_univ π[0]) : M.Path := ⟨s.val :: π.states, by simp, fun i hi ↦ by
  simp at hi ⊢
  rw [List.getElem_cons]
  split_ifs with h
  · simp_all [← prev_univ_iff_succs_univ]
  · simp_all
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero h
    simp_all
    apply π.succs_succs_nat
    omega⟩

@[ext]
theorem ext {π₁ π₂ : M.Path} (h₁ : ∎|π₁| = ∎|π₂|)
    (h₂ : ∀ i (_ : i < ∎|π₁|) (_ : i < ∎|π₂|), π₁[i] = π₂[i]) : π₁ = π₂ := by
  cases π₁ ; cases π₂
  simp_all
  apply List.ext_getElem h₁
  intro i hi _
  simp_all
  simp [length] at h₁ hi
  convert h₂ i (by simp [length] ; omega)

@[simp]
theorem mk_states (states : List State) (nonempty : states ≠ [])
  (succs : ∀ i (hi : i < states.length - 1), states[i + 1] ∈ M.succs_univ states[i]) :
    (⟨states, nonempty, fun i hi ↦ succs i hi⟩ : M.Path).states = states := by
      simp

@[simp]
theorem mk_length (states : List State) (nonempty : states ≠ [])
  (succs : ∀ i (hi : i < states.length - 1), states[i + 1] ∈ M.succs_univ states[i]) :
    (⟨states, nonempty, succs⟩ : M.Path).length = states.length := by
      simp [length]

@[simp]
theorem mk_last (states : List State) (nonempty : states ≠ [])
  (succs : ∀ i (hi : i < states.length - 1), states[i + 1] ∈ M.succs_univ states[i]) :
      (⟨states, nonempty, succs⟩ : M.Path).last
    = states[states.length - 1]'(by simp [List.length_pos.mpr nonempty]) := by
  simp only [last, length, instGetElem]

@[simp]
theorem mk_getElem (states : List State) (nonempty : states ≠ [])
  (succs : ∀ i (hi : i < states.length - 1), states[i + 1] ∈ M.succs_univ states[i])
  (i : ℕ) (hi : i < states.length) :
    (⟨states, nonempty, succs⟩ : M.Path)[i] = states[i] := by simp only [instGetElem]

@[simp] theorem extend_prev : (π.extend s).prev = π := by simp [extend, prev]

@[simp]
theorem tail_getElem_zero :
    π.tail[0] = if h : ∎|π| = 1 then π[0] else π[1]'(by have := π.length_pos ; omega) := by
  split_ifs <;> simp_all [tail]

@[simp]
theorem mem_succs_univ (h : 1 < ∎|π|) : π[1] ∈ M.succs_univ π[0] := π.succs_succs_nat (by omega)
@[simp]
theorem mem_prev_univ (h : 1 < ∎|π|) : π[0] ∈ M.prev_univ π[1] := by simp
@[simp]
theorem mem_succs_univ_of_prev_univ (π : M.Path) (s : M.prev_univ π[0]) : π[0] ∈ M.succs_univ s :=
  by obtain ⟨s, h⟩ := s; simp at h; exact h

@[simp]
theorem prepend_tail : (π.prepend s).tail = π := by simp [prepend, tail]
@[simp]
theorem tail_prepend (h : 1 < ∎|π|) : π.tail.prepend ⟨π[0], by simp [Nat.ne_of_lt' h]⟩ = π := by
  simp [prepend, tail, Nat.ne_of_lt' h]
  ext i _ hi
  · simp
  · simp
    rw [List.getElem_cons]
    split_ifs
    · subst_eqs ; rfl
    · simp ; congr ; omega
@[simp]
theorem tail_prepend' (h : 1 < ∎|π|) (h' : π[0] = s) :
    π.tail.prepend ⟨s, by simp [Nat.ne_of_lt' h, ← h']⟩ = π := by simp [← h', h]

@[simp]
theorem singleton_first : ({s} : M.Path)[0] = s := by simp only [instSingleton, instGetElem] ; simp
@[simp]
theorem extend_first : (π.extend s)[0] = π[0] := by simp [extend, List.getElem_append]
@[simp]
theorem prepend_first : (π.prepend s)[0] = s := by simp [prepend]
@[simp]
theorem tail_first :
    π.tail[0] = if h : ∎|π| = 1 then π[0] else π[1]'(by have := π.length_pos ; omega) := by
  simp [tail] ; split_ifs <;> simp
@[simp]
theorem prev_first : π.prev[0] = π[0] := by simp [prev] ; split_ifs <;> simp
@[simp]
theorem take_first : (π.take n)[0] = π[0] := by simp [take]
@[simp]
theorem succs_first (π' : π.succs_univ) : π'.val[0] = π[0] := by
  rcases π' with ⟨π', hπ, hπ'⟩
  subst_eqs
  simp

@[simp]
theorem singleton_last : ({s} : M.Path).last = s := by
  simp only [last, instSingleton, instGetElem, length] ; simp
@[simp]
theorem extend_last : (π.extend s).last = s := by simp [extend, List.getElem_append]
@[simp]
theorem prepend_last : (π.prepend s).last = π.last := by simp [prepend, List.getElem_cons, last]
@[simp]
theorem tail_last :
    π.tail.last = π.last := by
  have := π.length_pos
  simp [tail] ; split_ifs <;> simp
  congr ; omega
@[simp]
theorem prev_last : π.prev.last = π[∎|π| - 2] := by
  simp [prev] ; split_ifs <;> simp
  · simp_all
  · congr! 1

theorem take_last_nat : (π.take n).last = π[min n (∎|π| - 1)] := by simp [take]; congr; omega
@[simp]
theorem take_last_nat' (h : n < ∎|π|) : (π.take n).last = π[n] := by simp [take]; congr; omega
@[simp]
theorem take_last (n : Fin ∎|π|) : (π.take n).last = π[n] := by simp [take]; congr; omega
@[simp]
theorem take_last' (n : Fin (∎|π| - 1)) : (π.take n).last = π[n] := by simp [take]; congr; omega
@[simp]
theorem succs_last (π' : π.succs_univ) : π'.val.last ∈ M.succs_univ π.last := by
  rcases π' with ⟨π', hπ, hπ'⟩
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ¬∎|π'| = 0)
  obtain ⟨j', hj'⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ¬j = 0)
  subst_eqs
  simp
  simp_all [last]

@[simp]
theorem singleton_length : ({s} : M.Path).length = 1 := by simp [instSingleton]
@[simp]
theorem extend_length : ∎|π.extend s| = ∎|π| + 1 := by simp [extend]
@[simp]
theorem prepend_length : ∎|π.prepend s| = ∎|π| + 1 := by simp [prepend]
@[simp]
theorem tail_length :
    ∎|π.tail| = if ∎|π| = 1 then ∎|π| else ∎|π| - 1 := by
  simp [tail] ; split_ifs <;> simp
@[simp]
theorem prev_length : ∎|π.prev| = if ∎|π| = 1 then ∎|π| else ∎|π| - 1 := by
  simp [prev] ; split_ifs <;> simp
@[simp]
theorem take_length : ∎|π.take n| = min (n + 1) ∎|π| := by simp [take]
@[simp]
theorem succs_length (π' : π.succs_univ) : ∎|π'.val| = ∎|π| + 1 := by
  rcases π' with ⟨π', hπ, hπ'⟩
  subst_eqs
  simp
  split_ifs <;> omega

theorem take_prepend :
    (π.take i).prepend s = (π.prepend ⟨s, by let h := s.prop; simp at h; simpa⟩).take (i + 1) := by
  simp [prepend, take]
@[simp] theorem take_zero : π.take 0 = {π[0]} :=
  ext (by simp) (fun i _ _ ↦ by simp [(by simp_all : i = 0)])

@[simp]
theorem getElem_length_pred_eq_last : π[∎|π| - 1] = π.last := by rfl
@[simp]
theorem extend_getElem_length_pred_eq_last : (π.extend s)[∎|π| - 1] = π.last := by
  simp [extend, List.getElem_append]
@[simp]
theorem take_lenth_pred_eq_prev : π.take (∎|π| - 2) = π.prev := by
  simp [take, prev] ; split_ifs with h
  · simp_all
  · simp [List.dropLast_eq_take]
    omega
@[simp]
theorem extend_take_lenth_pred_eq_prev : (π.extend s).take (∎|π| - 1) = π := by
  have h : ∎|π| - 1 + 1 = ∎|π| := by have := π.length_pos; omega
  simp [take, prev, extend, h]
@[simp]
theorem extend_take (i : Fin ∎|π|) : (π.extend s).take i = π.take i := by
  simp [extend, take]
  omega
@[simp]
theorem extend_take' (i : Fin (∎|π| - 1)) : (π.extend s).take i = π.take i := by
  simp [extend, take]
  omega
@[simp]
theorem extend_getElem (i : Fin ∎|π|) : (π.extend s)[i] = π[i] := by
  simp only [extend, take, getElem]
  simp [List.getElem_append]
@[simp]
theorem extend_getElem' (i : Fin (∎|π| - 1)) : (π.extend s)[i] = π[i] := by
  simp only [extend, take, getElem]
  have : i < ∎|π| := by have := i.isLt; omega
  simp [List.getElem_append, this]
@[simp]
theorem extend_getElem_nat (h : i < ∎|π|) : (π.extend s)[i]'(by simp; omega) = π[i] := by
  have := π.extend_getElem ⟨i, h⟩ (s:=s)
  simp_all
@[simp]
theorem extend_getElem_nat' (h : i < ∎|π| - 1) : (π.extend s)[i]'(by simp; omega) = π[i] :=
  π.extend_getElem_nat (by omega) (s:=s)
@[simp]
theorem extend_getElem_length : (π.extend s)[∎|π|] = s := by simp [extend]
@[simp]
theorem extend_getElem_succ (i : Fin ∎|π|) :
    (π.extend s)[i.val + 1] = if h : ∎|π| - 1 = i then s.val else π[i.val + 1] := by
  simp [extend, List.getElem_append]
  split_ifs with h₁ h₂ h₂ <;> try simp_all
  all_goals simp at h₁ h₂; omega
@[simp]
theorem extend_getElem_succ' (i : Fin (∎|π| - 1)) :
    (π.extend s)[i.val + 1]'(by simp; omega) = π[i.val + 1] := by
  simp [extend, List.getElem_append]

@[simp]
theorem tail_getElem (i : Fin (∎|π| - 1)) :
    π.tail[i]'(by simp; split_ifs <;> omega) = π[i.val + 1] := by
  simp [tail]
  split_ifs <;> simp
  absurd i.isLt
  omega
@[simp]
theorem tail_getElem_nat (i : ℕ) (h : i < ∎|π| - 1) :
    π.tail[i]'(by simp; split_ifs <;> omega) = π[i + 1] := by
  simp [tail]
  split_ifs <;> simp
  omega
@[simp]
theorem tail_getElem_nat_succ (i : ℕ) (h : i < ∎|π| - 2) :
    π.tail[i]'(by simp; split_ifs <;> omega) = π[i + 1] := by
  simp [tail]
  split_ifs <;> simp
  omega
@[simp]
theorem tail_getElem_nat_succ' (i : ℕ) (h : i < ∎|π| - 2) :
    π.tail[i + 1]'(by simp; split_ifs <;> omega) = π[i + 2] := by
  simp [tail]
  split_ifs <;> simp
  omega

@[simp] theorem prepend_getElem_one (s : M.prev_univ π[0]) : (π.prepend s)[1] = π[0] := rfl
@[simp] theorem prepend_getElem_succ (s : M.prev_univ π[0]) (i : Fin ∎|π|) :
    (π.prepend s)[i.val + 1] = π[i] := by
  simp [prepend]
@[simp] theorem prepend_getElem_succ' (s : M.prev_univ π[0]) (i : Fin (∎|π| - 1)) :
    (π.prepend s)[i.val + 1]'(by simp; omega) = π[i] := by
  simp [prepend]
@[simp] theorem prepend_injective : Function.Injective π.prepend := by
  intro ⟨s, _⟩ ⟨s', _⟩ h
  simp_all [prepend]
@[simp] theorem prepend_inj_right (h : π[0] = π'[0]) :
    π.prepend s = π'.prepend ⟨s, by rw [← h]; simp⟩ ↔ π = π' := by
  cases π; cases π'; simp_all [prepend]

@[simp]
theorem last_mem_succs_univ_prev_last (h : 1 < ∎|π|) : π.last ∈ M.succs_univ π.prev.last := by
  have := π.succs_succs ⟨∎|π| - 2, by omega⟩
  have : ∎|π| - 2 + 1 = ∎|π| - 1 := by omega
  simp_all
@[simp]
theorem prev_extend (h : 1 < ∎|π|) :
    π.prev.extend ⟨π.last, π.last_mem_succs_univ_prev_last h⟩ = π := by
  have : ¬∎|π| = 1 := by omega
  simp [prev, extend, this]
  ext
  · simp
  · simp [List.getElem_append]
    split <;> try rfl
    simp only [last]
    congr
    omega

theorem succs_univ_eq_extend_succs_univ :
    π.succs_univ = {π.extend s' | s'} := by
  ext π'
  simp [succs_univ]
  constructor
  · intro ⟨_, h⟩
    subst_eqs
    exact Exists.intro _ (Exists.intro _ (π'.prev_extend h))
  · simp; intros; subst_eqs; simp

end MDP.Path
