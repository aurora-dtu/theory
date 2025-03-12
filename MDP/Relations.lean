import MDP.Counterexample
import MDP.Relations.Syntax
import MDP.SupSup

namespace MDP.Relations

example : relations
    [⨆ n, ⨅ 𝒮 : 𝔖[M], M.EC c 𝒮 n] =ᶠ [⨆ n, ⨅ ℒ : 𝔏[M], M.EC c ℒ n]
            =ᶠ                                 =ᶠ
    [⨅ 𝒮 : 𝔖[M], ⨆ n, M.EC c 𝒮 n] =ᶠ [⨅ ℒ : 𝔏[M], ⨆ n, M.EC c ℒ n]
:= by
  split_ands <;> intros <;>
  simp_all [iInf_iSup_EC_eq_iInf_iSup_ECℒ, implies_true, iSup_iInf_EC_eq_iInf_iSup_EC,
    iSup_iInf_ECℒ_eq_iInf_iSup_ECℒ, and_self]

example : relations
    [⨆ n, ⨅ 𝒮 : 𝔖[M], EC c 𝒮 n] ≤ [⨆ n, ⨅ ℒ : 𝔏[M], EC c ℒ n]
            ∃<                                 ≤
    [⨅ 𝒮 : 𝔖[M], ⨆ n, EC c 𝒮 n] ∃< [⨅ ℒ : 𝔏[M], ⨆ n, EC c ℒ n]
:= by
  simp_all only [iInf_apply, iSup_apply, exists_iInf_iSup_EC_lt_iInf_iSup_ECℒ,
    exists_iSup_iInf_EC_lt_iInf_iSup_EC, iSup_iInf_le_iInf_iSup, implies_true,
    iSup_iInf_EC_le_iSup_iInf_ECℒ, true_and]

example : relations
    [⨆ n, ⨆ 𝒮 : 𝔖[M], EC c 𝒮 n] ≥ [⨆ n, ⨆ ℒ : 𝔏[M], EC c ℒ n]
            =                                 =
    [⨆ 𝒮 : 𝔖[M], ⨆ n, EC c 𝒮 n] ≥ [⨆ ℒ : 𝔏[M], ⨆ n, EC c ℒ n]
:= by
  split_ands
  · simp; intros _ _ _ _ n ℒ; apply le_iSup₂_of_le n ℒ.toScheduler; rfl
  · intros; rw [iSup_comm]
  · intros; rw [iSup_comm]
  · simp; intros _ _ _ _ ℒ n; apply le_iSup₂_of_le ℒ.toScheduler n; rfl

end MDP.Relations
