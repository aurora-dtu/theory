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
notation "‖" a "‖" => Path.length a

instance instSingleton : Singleton State M.Path where
  singleton s := ⟨[s], by simp, by simp⟩

@[grind =, simp] theorem singleton_states :
    (instSingleton.singleton (α:=State) (β:=M.Path) s).states = [s] := by
  cbv

instance instGetElem : GetElem M.Path ℕ State (fun π i ↦ i < ‖π‖) where
  getElem π i _ := π.states[i]

@[grind =, simp] theorem states_getElem_eq_getElem (i : Fin ‖π‖) : π.states[i] = π[i] := rfl
@[grind =, simp] theorem states_getElem_eq_getElem_Nat (i : ℕ) (h : i < ‖π‖) : π.states[i] = π[i] :=
  rfl

@[grind =, simp] theorem singleton_getElem_nat (h : i < 1) :
    (instSingleton.singleton (α:=State) (β:=M.Path) s)[i] = s := by
  cbv; grind
@[grind =, simp] theorem singleton_getElem (i : Fin 1) :
    (instSingleton.singleton (α:=State) (β:=M.Path) s)[i] = s := by simp

@[grind =, simp] theorem states_length_eq_length : π.states.length = ‖π‖ := rfl

@[grind ., simp] theorem states_nonempty : π.states ≠ [] := π.nonempty
@[grind ., simp] theorem length_pos : 0 < ‖π‖ := List.length_pos_iff.mpr π.nonempty
@[grind ., simp] theorem length_ne_zero : ¬‖π‖ = 0 := π.length_pos.ne.symm

@[simp] theorem length_pred_succ : ‖π‖ - 1 + 1 = ‖π‖ := by have := π.length_pos; omega


abbrev last : State := π[‖π‖ - 1]

@[grind ., simp] theorem succs_succs (i : Fin (‖π‖ - 1)) : π[↑i + 1] ∈ M.succs_univ π[↑i] :=
  π.property i.val (by simp)
@[grind ., simp] theorem succs_succs_nat {i : ℕ} (h : i < ‖π‖ - 1) : π[i + 1] ∈ M.succs_univ π[i] :=
  π.property i h

def take (n : ℕ) : M.Path := ⟨π.states.take (n + 1), by simp, fun i hi ↦ by
  simp
  apply π.succs_succs_nat
  simp at hi
  omega⟩

def prev : M.Path := ⟨if ‖π‖ = 1 then π.states else π.states.dropLast,
  by split <;> simp; apply List.ne_nil_of_length_pos; have := π.length_pos; simp; omega,
  fun i hi ↦ by split_ifs with h <;> simp [h] at hi ⊢; apply π.succs_succs_nat; omega⟩

def extend (s : M.succs_univ π.last) : M.Path := ⟨π.states ++ [s.val], by simp, by grind⟩

def succs_univ : Set M.Path := {π' : M.Path | π'.prev = π ∧ 1 < ‖π'‖}

@[grind =, simp]
theorem last_if_singleton (h : ‖π‖ = 1) : π.last = π[0] := by simp [Path.last, h]

@[grind =, simp]
theorem length_ne_one_iff : ¬‖π‖ = 1 ↔ 1 < ‖π‖ := by have := π.length_pos; omega

@[grind =, simp]
theorem length_sub_add_eq (h : 1 < ‖π‖) : ‖π‖ - 2 + 1 = ‖π‖ - 1 := by have := π.length_pos; omega

@[grind ., simp]
theorem last_mem_succs (h : 1 < ‖π‖) : π.last ∈ M.succs_univ π[‖π‖ - 2] := by
  have := π.succs_succs_nat (i:=‖π‖ - 2) (by omega); simp_all

@[grind ., simp] theorem mem_succs_univ_prev {π π' : M.Path} (h : π' ∈ π.succs_univ) :
    π'.prev = π :=
  by simp [Path.succs_univ] at h; grind
@[grind =, simp] theorem succs_univ_prev (π' : π.succs_univ) : π'.val.prev = π := by
  obtain ⟨π', h⟩ := π'; simp_all [mem_succs_univ_prev h]
@[grind ., simp] theorem mem_prev_succs_univ (h : 1 < ‖π‖) : π ∈ π.prev.succs_univ := by
  simp [prev, succs_univ, h]

def act := M.act π.last

def tail : M.Path := ⟨if ‖π‖ = 1 then π.states else π.states.tail,
  by split <;> simp_all [List.ne_nil_of_length_pos],
  by
    intro i hi
    split_ifs with h <;> simp [h] at hi ⊢
    apply π.succs_succs_nat (by omega)⟩

def prepend (s : M.prev_univ π[0]) : M.Path := ⟨s.val :: π.states, by simp, fun i hi ↦ by
  simp at hi ⊢
  rw [List.getElem_cons]
  split_ifs with h
  · grind
  · obtain ⟨j, _, _⟩ := Nat.exists_eq_succ_of_ne_zero h; grind⟩

@[ext]
theorem ext {π₁ π₂ : M.Path} (h₁ : ‖π₁‖ = ‖π₂‖)
    (h₂ : ∀ i (_ : i < ‖π₁‖) (_ : i < ‖π₂‖), π₁[i] = π₂[i]) : π₁ = π₂ := by
  cases π₁; cases π₂
  simp_all
  apply List.ext_getElem h₁
  intro i hi _
  simp_all
  simp [length] at h₁ hi
  convert h₂ i (by simp [length]; omega)

theorem eq_iff {π₁ π₂ : M.Path} : π₁ = π₂ ↔ π₁.states = π₂.states := by
  obtain ⟨_, _, _⟩ := π₁
  obtain ⟨_, _, _⟩ := π₂
  grind

theorem ext_states {π₁ π₂ : M.Path} (h : π₁.states = π₂.states) : π₁ = π₂ := by
  simp [eq_iff, h]

@[simp]
theorem mk_states (states : List State) {h₁} {h₂} :
    (⟨states, h₁, h₂⟩ : M.Path).states = states := by simp

@[grind =, simp]
theorem mk_length (states : List State) {h₁} {h₂} :
    (⟨states, h₁, h₂⟩ : M.Path).length = states.length := by simp [length]

@[grind =, simp]
theorem mk_last (states : List State) {h₁} {h₂} :
      (⟨states, h₁, h₂⟩ : M.Path).last
    = states[states.length - 1]'(by simp [List.length_pos_iff.mpr h₁]) := by
  simp only [last, length, instGetElem]

@[grind =, simp]
theorem mk_getElem (states : List State) {h₁} {h₂} (hi : i < states.length) :
    (⟨states, h₁, h₂⟩ : M.Path)[i] = states[i] := by simp only [instGetElem]

@[grind =, simp]
theorem singleton_length : ({s} : M.Path).length = 1 := by rfl
@[grind =, simp]
theorem extend_length : ‖π.extend s‖ = ‖π‖ + 1 := by simp [extend]
@[grind =, simp]
theorem prepend_length : ‖π.prepend s‖ = ‖π‖ + 1 := by simp [prepend]
@[grind =, simp]
theorem tail_length :
    ‖π.tail‖ = max (‖π‖ - 1) 1 := by
  simp [tail]; grind
@[grind =, simp]
theorem prev_length : ‖π.prev‖ = max (‖π‖ - 1) 1 := by
  simp [prev]; grind
@[grind =, simp]
theorem take_length : ‖π.take n‖ = min (n + 1) ‖π‖ := by simp [take]
@[grind =, simp]
theorem succs_length (π' : π.succs_univ) : ‖π'.val‖ = ‖π‖ + 1 := by
  rcases π' with ⟨π', ⟨_⟩, hπ'⟩
  grind

@[grind =]
theorem prev_getElem {i} (hi : i < ‖π‖ - 1) : π.prev[i]'(by grind) = π[i] := by
  grind [prev]

@[grind =, simp] theorem extend_prev : (π.extend s).prev = π := by simp [extend, prev]

@[grind =, simp]
theorem tail_getElem_zero :
    π.tail[0]'(by grind) = if h : ‖π‖ = 1 then π[0] else π[1]'(by simp_all) := by
  split_ifs <;> simp_all [tail]; rfl

@[grind ., simp]
theorem mem_succs_univ (h : 1 < ‖π‖) : π[1] ∈ M.succs_univ π[0] := π.succs_succs_nat (by omega)
@[grind ., simp]
theorem mem_prev_univ (h : 1 < ‖π‖) : π[0] ∈ M.prev_univ π[1] := by simp
@[grind ., simp]
theorem mem_succs_univ_of_prev_univ (π : M.Path) (s : M.prev_univ π[0]) : π[0] ∈ M.succs_univ s :=
  by obtain ⟨s, h⟩ := s; simp at h; exact h

@[grind =, simp]
theorem prepend_tail : (π.prepend s).tail = π := by simp [prepend, tail]
@[grind =, simp]
theorem tail_prepend (h : 1 < ‖π‖) : π.tail.prepend ⟨π[0], by simp [Nat.ne_of_lt' h]⟩ = π := by
  ext <;> grind [prepend, tail]
@[grind =, simp]
theorem tail_prepend' (h : 1 < ‖π‖) (h' : π[0] = s) :
    π.tail.prepend ⟨s, by simp [Nat.ne_of_lt' h, ← h']⟩ = π := by simp [← h', h]

@[grind =, simp]
theorem singleton_first : ({s} : M.Path)[0] = s := by simp only [instGetElem]; simp
@[grind =, simp]
theorem extend_first : (π.extend s)[0] = π[0] := by simp [extend]
@[grind =, simp]
theorem prepend_first : (π.prepend s)[0] = s := by simp [prepend]
@[grind =, simp]
theorem tail_first :
    π.tail[0] = if h : ‖π‖ = 1 then π[0] else π[1]'(by simp_all) := by
  simp [tail]; split_ifs <;> simp <;> rfl
@[grind =, simp]
theorem prev_first : π.prev[0] = π[0] := by simp [prev]; split_ifs <;> simp <;> rfl
@[grind =, simp]
theorem take_first : (π.take n)[0] = π[0] := by simp [take]; rfl
@[grind =, simp]
theorem succs_first (π' : π.succs_univ) : π'.val[0] = π[0] := by
  rcases π' with ⟨π', ⟨_⟩, hπ'⟩; simp

@[grind =, simp]
theorem singleton_last : ({s} : M.Path).last = s := by
  simp only [last, instGetElem, length]; simp
@[grind =, simp]
theorem extend_last : (π.extend s).last = s := by simp [extend]
@[grind =, simp]
theorem prepend_last : (π.prepend s).last = π.last := by
  simp [prepend, List.getElem_cons, last]; rfl
@[grind =, simp]
theorem tail_last :
    π.tail.last = π.last := by
  simp [tail]; split_ifs <;> simp
  · rfl
  have := π.length_pos
  congr; omega
@[grind =, simp]
theorem prev_last : π.prev.last = π[‖π‖ - 2] := by
  simp [prev]; split_ifs <;> simp_all
  · rfl
  congr! 1

theorem take_last_nat : (π.take n).last = π[min n (‖π‖ - 1)] := by simp [take]; congr; omega
@[grind =, simp]
theorem take_last_nat' (h : n < ‖π‖) : (π.take n).last = π[n] := by simp [take]; congr; omega
@[grind =, simp]
theorem take_last (n : Fin ‖π‖) : (π.take n).last = π[n] := by simp [take]; rfl
@[grind =, simp]
theorem take_last' (n : Fin (‖π‖ - 1)) : (π.take n).last = π[n] := by simp [take]; congr; omega
@[grind ., simp]
theorem succs_last (π' : π.succs_univ) : π'.val.last ∈ M.succs_univ π.last := by
  rcases π' with ⟨π', hπ, hπ'⟩
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ¬‖π'‖ = 0)
  obtain ⟨j', hj'⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ¬j = 0)
  subst_eqs
  simp
  simp_all [last]

theorem take_prepend :
    (π.take i).prepend s = (π.prepend ⟨s, by let h := s.prop; simp at h; simpa⟩).take (i + 1) := by
  simp [prepend, take]
@[grind =, simp] theorem take_zero : π.take 0 = {π[0]} :=
  ext (by grind) (fun i _ _ ↦ by simp [(by simp_all : i = 0)])

@[grind =, simp]
theorem getElem_length_pred_eq_last : π[‖π‖ - 1] = π.last := by rfl
@[grind =, simp]
theorem extend_getElem_length_pred_eq_last : (π.extend s)[‖π‖ - 1] = π.last := by
  simp [extend]
@[grind =, simp]
theorem take_length_pred_eq_prev : π.take (‖π‖ - 2) = π.prev := by
  simp [take, prev]; split_ifs with h <;> simp_all [List.dropLast_eq_take]
@[grind =, simp]
theorem extend_take_length_pred_eq_prev : (π.extend s).take (‖π‖ - 1) = π := by
  simp [take, extend]
@[grind =, simp]
theorem extend_take (i : Fin ‖π‖) : (π.extend s).take i = π.take i := by
  grind [extend, take]
@[grind =, simp]
theorem extend_take' (i : Fin (‖π‖ - 1)) : (π.extend s).take i = π.take i := by
  grind [extend, take]
@[grind =, simp]
theorem extend_getElem_nat_if (h : i < ‖π‖ + 1) :
    (π.extend s)[i]'(by grind) = if h': i < ‖π‖ then π[i] else s := by
  grind [extend]
@[simp]
theorem extend_getElem (i : Fin ‖π‖) : (π.extend s)[i] = π[i] := by
  grind
@[simp] theorem extend_getElem_length : (π.extend s)[‖π‖] = s := by grind
@[grind =, simp]
theorem extend_getElem_succ (i : Fin ‖π‖) :
    (π.extend s)[i.val + 1] = if h : ‖π‖ = i + 1 then s.val else π[i.val + 1] := by
  simp [extend, List.getElem_append]
  split_ifs with h₁ h₂ h₂ <;> try simp_all
  · omega
  · rfl
  · omega

@[grind =, simp]
theorem tail_getElem (i : Fin (‖π‖ - 1)) :
    π.tail[i] = π[i.val + 1] := by
  simp [tail]
  split_ifs <;> simp
  · absurd i.isLt; omega
  · rfl
@[grind =, simp]
theorem tail_getElem_nat (i : ℕ) (h : i < ‖π‖ - 1) :
    π.tail[i]'(by grind) = π[i + 1] := by
  simp [tail]
  split_ifs <;> simp
  · omega
  · rfl
@[grind =, simp]
theorem tail_getElem_nat_succ (i : ℕ) (h : i < ‖π‖ - 2) :
    π.tail[i]'(by grind) = π[i + 1] := by
  simp [tail]
  split_ifs <;> simp
  · omega
  · rfl
@[grind =, simp]
theorem tail_getElem_nat_succ' (i : ℕ) (h : i < ‖π‖ - 2) :
    π.tail[i + 1]'(by grind) = π[i + 2] := by
  simp [tail]
  split_ifs <;> simp
  · omega
  · rfl

@[grind =, simp] theorem prepend_getElem (s : M.prev_univ π[0]) (i : ℕ) (hi : i < ‖π‖ + 1) :
    (π.prepend s)[i]'(by grind) = if _ : i = 0 then s.val else π[i - 1] := by
  grind [prepend]

-- @[grind =, simp] theorem prepend_getElem_one (s : M.prev_univ π[0]) : (π.prepend s)[1] = π[0] := rfl
@[grind =, simp] theorem prepend_getElem_succ (s : M.prev_univ π[0]) (i : Fin ‖π‖) :
    (π.prepend s)[i.val + 1] = π[i] := by simp
-- @[grind =, simp] theorem prepend_getElem_succ' (s : M.prev_univ π[0]) (i : Fin (‖π‖ - 1)) :
--     (π.prepend s)[i.val + 1]'(by grind) = π[i] := by simp [prepend]; rfl
@[grind ., simp] theorem prepend_injective : Function.Injective π.prepend := by
  intro ⟨s, _⟩ ⟨s', _⟩ h
  simp_all [prepend]
@[grind =, simp] theorem prepend_inj_right (h : π[0] = π'[0]) :
    π.prepend s = π'.prepend ⟨s, by rw [← h]; simp⟩ ↔ π = π' := by
  cases π; cases π'; simp_all [prepend]

theorem last_mem_succs_univ_prev_last (h : 1 < ‖π‖) : π.last ∈ M.succs_univ π.prev.last := by
  grind
@[grind =, simp]
theorem prev_extend (h : 1 < ‖π‖) :
    π.prev.extend ⟨π.last, π.last_mem_succs_univ_prev_last h⟩ = π := by
  ext <;> grind

theorem succs_univ_eq_extend_range : π.succs_univ = Set.range π.extend := by
  ext π'
  simp [succs_univ]
  constructor <;> simp_all
  · rintro ⟨_⟩; grind [Path.prev_extend]
  · grind

theorem induction_on
  {P : M.Path → Prop} (π : M.Path)
  (single : P {π[0]}) (extend : ∀ π (s' : M.succs_univ π.last), P π → P (π.extend s')) :
    P π := by
  obtain ⟨π, nonempty, progress⟩ := π
  induction π using List.reverseRecOn with
  | nil => contradiction
  | append_singleton l s' ih =>
    if nonempty' : l = [] then
      subst_eqs
      exact single
    else
      simp_all
      apply extend ⟨l, nonempty', by
          intro i hi
          have := progress i (by grind)
          grind⟩ s'
      · have := progress (l.length - 1) (by simp_all [List.length_pos_iff])
        grind
      · apply ih; grind

end MDP.Path
