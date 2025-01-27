import MDP.Basic

namespace MDP

variable {State : Type*} {Act : Type*}

variable [DecidableEq State]

noncomputable def mk_from_succs₀
  (succs : State → Act → Finset (State × PReal))
  (h : ∀ (s : State) (a : Act), is₀₁ (succs s a |>.sum (·.2.val)))
  (progress : ∀ (s : State), ∃ (a : Act) (s' : State) (p : PReal), (s', p) ∈ succs s a)
  : MDP State Act
:=
  let P' s a : Option (PMF State) :=
    if h_nonempty : (succs s a).Nonempty then
      some ⟨(fun s' ↦ (succs s a).filter (·.1 = s') |>.sum (·.2.val)), by
        simp [Summable.hasSum_iff, Finset.sum_filter, tsum_sum, eq_comm]
        rcases h s a with h' | h'
        · simp at h'
          have ⟨⟨s', ⟨p, hp⟩⟩, h_succs⟩ := h_nonempty
          absurd hp.left
          exact (h' s' p hp h_succs).not_gt
        · exact h'.symm⟩
    else
      none
  let progress := by
    intro s
    have ⟨a, s', ⟨p, hp⟩, h_succs⟩ := progress s
    use a
    simp [P']
    use (s', ⟨p, hp⟩)
  ⟨P', progress⟩

noncomputable def mk_from_succs
  (succs : State → Act → Set (State × PReal))
  (x : ∀ (s : State) (a : Act), Decidable (succs s a).Nonempty)
  (h : ∀ (s : State) (a : Act), is₀₁ (∑' (x : succs s a), x.val.2.val))
  (progress : ∀ (s : State), ∃ (a : Act) (s' : State) (p : PReal), (s', p) ∈ succs s a)
  : MDP State Act
:=
  let P' s a : Option (PMF State) :=
    if h_nonempty : (succs s a).Nonempty then
      some ⟨(fun s' ↦ ∑' (x : succs s a), if x.val.1 = s' then x.val.2.val else 0), by
        simp [Summable.hasSum_iff, Finset.sum_filter, tsum_sum, eq_comm, ENNReal.tsum_comm]
        rcases h s a with h' | h'
        · simp at h'
          have ⟨⟨s', ⟨p, hp⟩⟩, h_succs⟩ := h_nonempty
          absurd hp.left
          exact (h' s' p hp h_succs).not_gt
        · exact h'.symm⟩
    else
      none
  let progress := by
    intro s
    have ⟨a, s', ⟨p, hp⟩, h_succs⟩ := progress s
    use a
    simp [P']
    use (s', ⟨p, hp⟩)
  ⟨P', progress⟩

noncomputable def mk_from_op
  [DecidableEq Act]
  (op : State → Finset (Act × State × PReal))
  (h : ∀ (s : State) (a : Act), is₀₁ (op s |>.filter (·.1 = a) |>.sum (·.2.2.val)))
  (progress : ∀ (s : State), ∃ (a : Act) (s' : State) (p : PReal), (a, s', p) ∈ op s)
  : MDP State Act
:= mk_from_succs₀ (fun s a ↦ op s |>.filter (·.1 = a) |>.image (·.2))
  (by
    intro s a
    simp_all only [Finset.sum_filter, Finset.mem_filter, and_imp, Prod.forall, Subtype.forall,
      implies_true, Finset.sum_image])
  (by
    intro s
    obtain ⟨a, s', p, h⟩ := progress s
    use a, s', p
    simp only [Finset.mem_image, Finset.mem_filter, Prod.exists, exists_eq_right]
    exact h)

variable (succs : State → Act → Finset (State × PReal))
variable {h_succs₁ : ∀ (s : State) (a : Act), is₀₁ (succs s a |>.sum (·.2.val))}
variable {h_succs₂ : ∀ (s : State), ∃ (a : Act) (s' : State) (p : PReal), (s', p) ∈ succs s a}

theorem succs_eq_mk_succs (s : State) (α : Act) :
  (mk_from_succs₀ succs h_succs₁ h_succs₂).succs α s = (succs s α).image (·.1)
:= by
  ext s'
  simp [mk_from_succs₀, MDP.succs, P]
  split
  · simp_all
    rename_i pmf h
    obtain ⟨⟨s'', hs''⟩, h⟩ := h
    -- simp at hs''
    subst_eqs
    simp [DFunLike.coe]
    constructor
    · simp_all
      intro s'' p hp h' _ _
      subst_eqs
      use p, hp
    · intro ⟨p, hp⟩
      use s', p, hp
      simp_all
      obtain ⟨⟨hp, _⟩, _⟩ := hp
      exact pos_iff_ne_zero.mp hp
  · simp_all

theorem succs_mem_iff_P_pos (s s' : State) (α : Act) :
  (∃p, (s', p) ∈ succs s α) ↔ 0 < (mk_from_succs₀ succs h_succs₁ h_succs₂).P s α s'
:= by
  simp [mk_from_succs₀]
  constructor <;> intro h
  · refine zero_lt_iff.mpr ?mp.a
    simp
    obtain ⟨p, hp, h⟩ := h
    simp [P]
    split
    · simp_all
      rename_i pmf h'
      obtain ⟨h', h''⟩ := h'
      subst_eqs
      simp [DFunLike.coe]
      use s', p
      simp [pos_iff_ne_zero.mp hp.left]
      apply Exists.intro hp h
    · rename_i h'
      absurd h'
      simp
      exact Finset.ne_empty_of_mem h
  · simp [P, zero_lt_iff] at h
    split at h
    · simp_all
      rename_i pmf h'
      obtain ⟨⟨s'', hs''⟩, h''⟩ := h'
      subst_eqs
      simp [DFunLike.coe] at h
      obtain ⟨s''', p, hp, hs'', _⟩ := h
      subst_eqs
      exact Exists.intro p hp
    · simp_all

theorem P_eq_succs_filter_sum (s s' : State) (α : Act) :
  (mk_from_succs₀ succs h_succs₁ h_succs₂).P s α s' = ((succs s α).filter (·.1=s')).sum (·.2.val)
:= by
  simp [P, mk_from_succs₀]
  split
  · simp_all [DFunLike.coe]
    rename_i pmf h
    obtain ⟨_, _⟩ := h
    subst_eqs
    simp_all
  · simp_all

instance [Fintype Act] : (mk_from_succs₀ succs h_succs₁ h_succs₂).FiniteBranching where
  act_fin s := Set.toFinite ((mk_from_succs₀ succs h_succs₁ h_succs₂).act s)
  succs_fin s a := by
    simp [mk_from_succs₀]
    unfold P
    simp
    split
    · simp_all only [Subtype.exists, Option.dite_none_right_eq_some, Option.some.injEq,
      DFunLike.coe]
      rename_i pmf h
      obtain ⟨h_nonempty, h⟩ := h
      subst_eqs
      simp [Finset.sum_filter]
      apply Set.Finite.ofFinset ((succs s a).image (·.1))
      simp
      intro s'
      constructor <;> intro h
      · obtain ⟨p, hp, h⟩ := h
        use s', p
        simp_all only [Subtype.exists, implies_true, and_self, exists_const, true_and]
        exact pos_iff_ne_zero.mp hp.left
      · obtain ⟨_, p, ⟨hp, h⟩, _, _⟩ := h
        subst_eqs
        use p, hp
    · simp_all

theorem mk_from_op_act_Finite
  [DecidableEq Act]
  (op : State → Finset (Act × State × PReal))
  (h : ∀ (s : State) (a : Act), is₀₁ (op s |>.filter (·.1 = a) |>.sum (·.2.2.val)))
  (progress : ∀ (s : State), ∃ (a : Act) (s' : State) (p : PReal), (a, s', p) ∈ op s)
  (s : State)
: ((mk_from_op op h progress).act s).Finite := by
  simp only [act, mk_from_op, mk_from_succs₀, Finset.image_nonempty]
  unfold P
  simp only
  apply Set.Finite.ofFinset ((op s).image (·.1))
  intro a
  simp only [Finset.mem_image, Prod.exists, exists_and_right, Subtype.exists, exists_eq_right,
    DFunLike.coe, Function.mem_support, ne_eq]
  split
  · simp_all only [Subtype.exists, Option.dite_none_right_eq_some, Option.some.injEq]
    rename_i pmf h
    obtain ⟨h_nonempty, h⟩ := h
    subst_eqs
    simp_all only [Finset.sum_filter, Finset.mem_filter, and_imp, Prod.forall, Subtype.forall,
      implies_true, Finset.sum_image]
    simp [iff_not_comm]
    constructor
    · intro q s' p hp h'
      have := congrFun q s'
      simp at this
      absurd this a s' p hp h' rfl rfl
      exact pos_iff_ne_zero.mp hp.left
    · intro h
      funext s'
      simp
      intro a _ p hp h' _ _
      subst_eqs
      absurd h s' p hp h'
      simp
  · simp_all only [Subtype.exists, dite_eq_right_iff]
    rename_i h
    simp [Finset.filter_eq_empty_iff] at h
    constructor <;> intro h'
    · absurd h'
      simp
      intro s' p hp q
      exact h a s' p hp q rfl
    · absurd h'
      rfl

instance
  [DecidableEq Act]
  (op : State → Finset (Act × State × PReal))
  (h : ∀ (s : State) (a : Act), is₀₁ (op s |>.filter (·.1 = a) |>.sum (·.2.2.val)))
  (progress : ∀ (s : State), ∃ (a : Act) (s' : State) (p : PReal), (a, s', p) ∈ op s)
: (mk_from_op op h progress).FiniteBranching where
  act_fin s := mk_from_op_act_Finite op h progress s
  succs_fin s a := by
    simp only [mk_from_op, mk_from_succs₀, Finset.image_nonempty]
    unfold P
    simp
    split
    · simp_all only [Subtype.exists, Option.dite_none_right_eq_some, Option.some.injEq]
      rename_i pmf h
      obtain ⟨h_nonempty, h⟩ := h
      subst_eqs
      apply Set.Finite.ofFinset ((op s).filter (·.1=a) |>.image (·.2.1))
      -- simp
      simp only [Finset.mem_image, Finset.mem_filter, Prod.exists, exists_and_right, Subtype.exists,
        exists_eq_right, DFunLike.coe, Finset.sum_filter, Function.mem_support, ne_eq,
        Finset.sum_eq_zero_iff, ite_eq_right_iff, Prod.forall, Subtype.forall, not_forall,
        Classical.not_imp]
      intro s'
      constructor <;> simp
      · intro p hp h
        use p
        constructor
        · use hp
        · exact pos_iff_ne_zero.mp hp.left
      · intro p hp h _
        use p, hp
    · simp_all only [Subtype.exists, dite_eq_right_iff, Function.support_zero, Set.finite_empty]

theorem succs₀_eq_mk_succs [Fintype Act] (s : State) (α : Act) :
  (mk_from_succs₀ succs h_succs₁ h_succs₂).succs₀ α s = (succs s α).image (·.1)
:= by
  have := succs_eq_mk_succs (h_succs₁:=h_succs₁) (h_succs₂:=h_succs₂) succs s α
  ext s
  simp_all


theorem act₀_eq_succs_filter_nonempty [i : Fintype Act] (s : State) :
  (mk_from_succs₀ succs h_succs₁ h_succs₂).act₀ s = i.elems.filter (succs s · |>.Nonempty)
:= by
  ext α
  simp [P, mk_from_succs₀, act₀, act, Fintype.complete]
  unfold P
  simp
  split
  · simp_all [DFunLike.coe]
    rename_i pmf h
    obtain ⟨h, _⟩ := h
    subst_eqs
    simp_all [Finset.sum_filter]
    obtain ⟨⟨s', ⟨p, hp⟩⟩, h⟩ := h
    intro q
    have := congrFun q s'
    simp at this
    absurd this s' p hp h rfl
    exact pos_iff_ne_zero.mp hp.left
  · simp_all
    rfl
