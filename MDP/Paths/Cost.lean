import MDP.Paths.Bounded
import MDP.Paths.Prob

namespace MDP

variable {State : Type*} {Act : Type*}
variable {M : MDP State Act}

abbrev Costs (_ : MDP State Act) := State → ENNReal

noncomputable def Path.Cost (c : M.Costs) (π : M.Path) := (π.states.map c).sum
noncomputable def Path.ECost (c : M.Costs) (𝒮 : 𝔖[M]) (π : M.Path) := π.Cost c * π.Prob 𝒮

noncomputable def EC (c : M.Costs) (𝒮 : 𝔖[M]) s n :=
  ∑' π : Path[M,s,=n], π.val.ECost c 𝒮

namespace Path

variable (π : M.Path)

theorem prepend_Cost (c : M.Costs) (s : M.prev_univ π[0]) :
    (π.prepend s).Cost c = c s + π.Cost c := by
  simp [Cost, Fin.getElem_fin, Nat.succ_eq_add_one, Fin.val_succ, prepend]

theorem Cost_tail (h : 1 < ∎|π|) (c : M.Costs) :
    π.Cost c = c π[0] + π.tail.Cost c := by
  nth_rw 1 [←π.tail_prepend h, prepend_Cost]

theorem ECost_tail [DecidableEq State] (𝒮 : 𝔖[M]) (c : M.Costs) (h : 1 < ∎|π|) :
    π.ECost c 𝒮 = M.P π[0] (𝒮 {π[0]}) π[1] *
      (c π[0] * π.tail.Prob (𝒮.specialize π[0] ⟨π[1], by simp⟩)
        + π.tail.ECost c (𝒮.specialize π[0] ⟨π[1], by simp⟩)) := by
  simp [ECost, π.Prob_tail h, π.Cost_tail h]
  ring

theorem prepend_ECost [DecidableEq State] (𝒮 : 𝔖[M]) (c : M.Costs) :
    (π.prepend s).ECost c 𝒮 = M.P s (𝒮 {s.val}) π[0] *
      (c s * π.Prob (𝒮.specialize s ⟨π[0], by simp⟩)
        + π.ECost c (𝒮.specialize s ⟨π[0], by simp⟩)) := by
  simp [ECost, π.prepend_Prob, π.prepend_Cost]
  ring

end MDP.Path
