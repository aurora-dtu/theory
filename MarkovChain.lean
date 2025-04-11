import MDP

def MarkovChain (State : Type*) := MDP State Unit

namespace MDP

variable {State : Type*} {Act : Type*}
variable (M : MDP State Act)

def inducedMarkovChain (ℒ : 𝔏[M]) : MarkovChain State where
  P' s _ := M.P' s (ℒ {s}) |>.get (by
    by_contra
    absurd ℒ.val.property {s}
    simp_all [P, funext_iff])
  exists_P'_isSome s := ⟨(), rfl⟩

namespace inducedMarkovChain

@[simp]
def P_eq : (M.inducedMarkovChain ℒ).P s () = M.P s (ℒ {s}) := by
  ext s'
  simp [inducedMarkovChain, P]

noncomputable def Paths_eq_bij : Path[M.inducedMarkovChain ℒ,s,=n] ≃ Path[M,s,=n] := by
  apply Equiv.ofBijective (fun π ↦ ⟨⟨π.val.states, sorry, sorry⟩, by simp⟩)
  sorry
  -- apply Set.BijOn.equiv (fun π ↦ ⟨π.states, sorry, sorry⟩)
  -- constructor
  -- · simp
  -- sorry

def EC_eq : (M.inducedMarkovChain ℒ).EC c default = M.EC c ℒ := by
  ext n s
  simp [EC]


end inducedMarkovChain

end MDP

namespace MDP.Unique

variable {State : Type*} {Act : Type*}
variable (M : MDP State Act)

variable [instUnique : Unique Act]

theorem 𝒮_eq_default (𝒮 : 𝔖[M]) : 𝒮 = default := by ext; simp [instUnique.uniq]

@[simp] theorem Scheduler_specialize [DecidableEq State] (𝒮 : 𝔖[M]) : 𝒮[s ↦ s'] = 𝒮 := by
  simp [𝒮_eq_default]
@[simp] theorem Scheduler_apply_eq_unit [DecidableEq State] (𝒮 : 𝔖[M]) : 𝒮 π = default :=
  (Unique.default_eq _).symm

@[simp] theorem act_eq : M.act s = {default} := (Set.eq_of_nonempty_of_subsingleton _ _).symm

@[simp] theorem iInf_act (f : Act → ENNReal) : ⨅ α, f α = f default := by simp
@[simp] theorem iInf_act' (f : M.act s → ENNReal) : ⨅ α : M.act s, f α = f ⟨default, by simp⟩ :=
  ciInf_subsingleton _ _

@[simp] theorem iSup_act (f : Act → ENNReal) : ⨆ α, f α = f default := by simp
@[simp] theorem iSup_act' (f : M.act s → ENNReal) : ⨆ α : M.act s, f α = f ⟨default, by simp⟩ :=
  ciSup_subsingleton _ _

theorem iInf_iSup_eq_iSup :
    ⨅ 𝒮, ⨆ n, M.EC c 𝒮 n = ⨆ n, M.EC c default n := by simp [𝒮_eq_default]
theorem iSup_iInf_eq_iSup :
    ⨆ n, ⨅ 𝒮, M.EC c 𝒮 n = ⨆ n, M.EC c default n := by simp [𝒮_eq_default]
theorem iSup_iSup_eq_iSup :
    ⨆ 𝒮, ⨆ n, M.EC c 𝒮 n = ⨆ n, M.EC c default n := by simp [𝒮_eq_default]
theorem iSup_iSup_eq_iSup' :
    ⨆ n, ⨆ 𝒮, M.EC c 𝒮 n = ⨆ n, M.EC c default n := by simp [𝒮_eq_default]

theorem iSup_EC_eq_lfp_Ψ [DecidableEq State] :
    ⨆ n, M.EC c default n = OrderHom.lfp (M.Ψ c) := by simp [← iSup_iSup_EC_eq_lfp_Ψ, 𝒮_eq_default]

open OrderHom in
theorem iSup_EC_eq_lfp_Φ [DecidableEq State] :
    ⨆ n, M.EC c default n = M.lfp_Φ c := by
  convert iSup_EC_eq_lfp_Ψ M
  apply le_antisymm
  · apply lfp_le; nth_rw 2 [← map_lfp]
    simp only [Φ, Φf, coe_mk, iInf_act', Ψ, iSup_act', le_refl]
  · apply lfp_le; nth_rw 2 [← map_lfp_Φ]
    simp only [Ψ, Φf, coe_mk, iSup_act', Φ, iInf_act', le_refl]

end MDP.Unique

namespace MarkovChain

variable {State : Type*}
variable (M : MarkovChain State)

@[simp] theorem Scheduler_specialize [DecidableEq State] (𝒮 : 𝔖[M]) : 𝒮[s ↦ s'] = 𝒮 := rfl
@[simp] theorem Scheduler_apply_eq_unit [DecidableEq State] (𝒮 : 𝔖[M]) : 𝒮 π = () := rfl

@[simp] theorem act_eq : M.act s = {()} := (Set.eq_of_nonempty_of_subsingleton _ _).symm

@[simp] theorem iInf_act (f : Unit → ENNReal) : ⨅ α : M.act s, f α = f () := by rw [act_eq]; simp
@[simp] theorem iInf_act' (f : M.act s → ENNReal) : ⨅ α : M.act s, f α = f ⟨(), by simp⟩ :=
  M.iInf_act (fun () ↦ f ⟨(), by simp⟩)

theorem iSup_EC_eq_lfp_Φ [DecidableEq State] (𝒮 : 𝔖[M]) : ⨆ n, M.EC c 𝒮 n = M.lfp_Φ c :=
  MDP.Unique.iSup_EC_eq_lfp_Φ M

end MarkovChain
