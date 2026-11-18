module

/-
General leafy-core forcing and every-minimum-support time classification.
The static criterion is prior mathematics. Priority of the time-support
classification remains unconfirmed. This does not prove the full tree
classification. Compilation records identify verified source versions.
-/
public import «formalization-foundations»
public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace FaultObservationResearch

universe u

variable {I : Type u} [Fintype I] [DecidableEq I]

def coronaLeaf (amount : I → ℕ) (i : I) (j : Fin (amount i)) : CoronaVertex I amount :=
  Sum.inr ⟨i, j⟩

def LeafSparse (amount : I → ℕ) (blue : Finset (CoronaVertex I amount)) : Prop :=
  ∀ (i : I) (j k : Fin (amount i)),
    coronaLeaf amount i j ∉ blue → coronaLeaf amount i k ∉ blue → j = k

omit [Fintype I] [DecidableEq I] in
theorem coronaLeaf_injective (amount : I → ℕ) (i : I) :
    Function.Injective (coronaLeaf amount i) := by
  intro j k h
  exact eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj h)).2

omit [Fintype I] [DecidableEq I] in
theorem leafSparse_mono (amount : I → ℕ) {A B : Finset (CoronaVertex I amount)}
    (hA : LeafSparse amount A) (hAB : A ⊆ B) : LeafSparse amount B := by
  intro i j k hj hk
  exact hA i j k (fun h => hj (hAB h)) (fun h => hk (hAB h))

theorem leaf_not_step_of_two_white (core : SimpleGraph I) (amount : I → ℕ)
    (blue : Finset (CoronaVertex I amount)) (i : I) (j k : Fin (amount i))
    (hjk : j ≠ k) (hj : coronaLeaf amount i j ∉ blue)
    (hk : coronaLeaf amount i k ∉ blue) :
    coronaLeaf amount i j ∉ synchronousStep (coronaAdj core amount) blue := by
  intro h
  rcases (mem_synchronousStep _ _ _).mp h with hold | ⟨source, hs, ha, hu⟩
  · exact hj hold
  · cases source with
    | inl v =>
      change v = i at ha
      subst v
      have heq := hu (coronaLeaf amount i k) rfl hk
      exact hjk (coronaLeaf_injective amount i heq).symm
    | inr leaf => exact False.elim ha

theorem two_white_leaves_stay_white (core : SimpleGraph I) (amount : I → ℕ)
    (blue : Finset (CoronaVertex I amount)) (i : I) (j k : Fin (amount i))
    (hjk : j ≠ k) (hj : coronaLeaf amount i j ∉ blue)
    (hk : coronaLeaf amount i k ∉ blue) (t : ℕ) :
    coronaLeaf amount i j ∉ colorAfter (coronaAdj core amount) blue t ∧
      coronaLeaf amount i k ∉ colorAfter (coronaAdj core amount) blue t := by
  induction t with
  | zero => exact ⟨hj, hk⟩
  | succ t ih =>
    exact ⟨leaf_not_step_of_two_white core amount _ i j k hjk ih.1 ih.2,
      leaf_not_step_of_two_white core amount _ i k j hjk.symm ih.2 ih.1⟩

theorem leafy_forcing_implies_sparse (core : SimpleGraph I) (amount : I → ℕ)
    (blue : Finset (CoronaVertex I amount))
    (hforcing : IsForcing (coronaAdj core amount) blue) : LeafSparse amount blue := by
  intro i j k hj hk
  by_contra hne
  obtain ⟨t, ht⟩ := hforcing
  have hwhite := (two_white_leaves_stay_white core amount blue i j k hne hj hk t).1
  change colorAfter (coronaAdj core amount) blue t = Finset.univ at ht
  exact hwhite (by rw [ht]; exact Finset.mem_univ _)

omit [Fintype I] [DecidableEq I] in
theorem sparse_exists_blue_leaf (amount : I → ℕ)
    (hmin : ∀ i : I, 2 ≤ amount i) (blue : Finset (CoronaVertex I amount))
    (hsparse : LeafSparse amount blue) (i : I) :
    ∃ j : Fin (amount i), coronaLeaf amount i j ∈ blue := by
  classical
  by_contra hnone
  have hwhite : ∀ j : Fin (amount i), coronaLeaf amount i j ∉ blue := by
    intro j hj
    exact hnone ⟨j, hj⟩
  let j : Fin (amount i) := ⟨0, by have := hmin i; omega⟩
  let k : Fin (amount i) := ⟨1, by have := hmin i; omega⟩
  have heq := hsparse i j k (hwhite j) (hwhite k)
  have hval := congrArg Fin.val heq
  change (0 : ℕ) = 1 at hval
  exact Nat.zero_ne_one hval

theorem core_mem_step_of_blue_leaf (core : SimpleGraph I) (amount : I → ℕ)
    (blue : Finset (CoronaVertex I amount)) (i : I) (j : Fin (amount i))
    (hj : coronaLeaf amount i j ∈ blue) :
    Sum.inl i ∈ synchronousStep (coronaAdj core amount) blue := by
  apply (mem_synchronousStep _ _ _).mpr
  refine Or.inr ⟨coronaLeaf amount i j, hj, rfl, ?_⟩
  intro other ha _
  cases other with
  | inl v => exact congrArg Sum.inl ha.symm
  | inr leaf => exact False.elim ha

theorem leaf_mem_step_of_cores_blue (core : SimpleGraph I) (amount : I → ℕ)
    (blue : Finset (CoronaVertex I amount)) (hsparse : LeafSparse amount blue)
    (hcores : ∀ i : I, Sum.inl i ∈ blue) (i : I) (j : Fin (amount i)) :
    coronaLeaf amount i j ∈ synchronousStep (coronaAdj core amount) blue := by
  classical
  apply (mem_synchronousStep _ _ _).mpr
  by_cases hj : coronaLeaf amount i j ∈ blue
  · exact Or.inl hj
  · refine Or.inr ⟨Sum.inl i, hcores i, rfl, ?_⟩
    intro other ha hwhite
    cases other with
    | inl v => exact False.elim (hwhite (hcores v))
    | inr leaf =>
      rcases leaf with ⟨v, k⟩
      change i = v at ha
      subst v
      exact congrArg (coronaLeaf amount i) (hsparse i k j hwhite hj)

theorem leafy_finishes_two_of_sparse (core : SimpleGraph I) (amount : I → ℕ)
    (hmin : ∀ i : I, 2 ≤ amount i) (blue : Finset (CoronaVertex I amount))
    (hsparse : LeafSparse amount blue) : FinishesBy (coronaAdj core amount) blue 2 := by
  classical
  have hcores : ∀ i : I, Sum.inl i ∈ synchronousStep (coronaAdj core amount) blue := by
    intro i
    obtain ⟨j, hj⟩ := sparse_exists_blue_leaf amount hmin blue hsparse i
    exact core_mem_step_of_blue_leaf core amount blue i j hj
  have hnext := leafSparse_mono amount hsparse (subset_synchronousStep (coronaAdj core amount) blue)
  change synchronousStep (coronaAdj core amount)
    (synchronousStep (coronaAdj core amount) blue) = Finset.univ
  apply Finset.eq_univ_of_forall
  intro v
  cases v with
  | inl i => exact subset_synchronousStep _ _ (hcores i)
  | inr leaf =>
    rcases leaf with ⟨i, j⟩
    exact leaf_mem_step_of_cores_blue core amount _ hnext hcores i j

theorem leafy_forcing_iff_sparse (core : SimpleGraph I) (amount : I → ℕ)
    (hmin : ∀ i : I, 2 ≤ amount i) (blue : Finset (CoronaVertex I amount)) :
    IsForcing (coronaAdj core amount) blue ↔ LeafSparse amount blue :=
  ⟨leafy_forcing_implies_sparse core amount blue,
    fun h => ⟨2, leafy_finishes_two_of_sparse core amount hmin blue h⟩⟩

theorem leafy_forcing_iff_two_rounds (core : SimpleGraph I) (amount : I → ℕ)
    (hmin : ∀ i : I, 2 ≤ amount i) (blue : Finset (CoronaVertex I amount)) :
    IsForcing (coronaAdj core amount) blue ↔ FinishesBy (coronaAdj core amount) blue 2 :=
  ⟨fun h => leafy_finishes_two_of_sparse core amount hmin blue
    (leafy_forcing_implies_sparse core amount blue h), fun h => ⟨2, h⟩⟩

def AllLeavesBlue (amount : I → ℕ) (blue : Finset (CoronaVertex I amount)) : Prop :=
  ∀ (i : I) (j : Fin (amount i)), coronaLeaf amount i j ∈ blue

theorem leafy_single_loss_forcing (core : SimpleGraph I) (amount : I → ℕ)
    (hmin : ∀ i : I, 2 ≤ amount i) (blue loss : Finset (CoronaVertex I amount))
    (hall : AllLeavesBlue amount blue) (hcard : loss.card ≤ 1) :
    IsForcing (coronaAdj core amount) (blue \ loss) := by
  classical
  apply (leafy_forcing_iff_sparse core amount hmin _).mpr
  intro i j k hj hk
  have hjloss : coronaLeaf amount i j ∈ loss := by
    by_contra h
    exact hj (Finset.mem_sdiff.mpr ⟨hall i j, h⟩)
  have hkloss : coronaLeaf amount i k ∈ loss := by
    by_contra h
    exact hk (Finset.mem_sdiff.mpr ⟨hall i k, h⟩)
  exact coronaLeaf_injective amount i
    (Finset.card_le_one.mp hcard _ hjloss _ hkloss)

theorem leafy_pair_trace_kills (core : SimpleGraph I) (amount : I → ℕ)
    (blue : Finset (CoronaVertex I amount)) (i : I) (j k : Fin (amount i))
    (hjk : j ≠ k) :
    ¬ IsForcing (coronaAdj core amount)
      (blue \ ({coronaLeaf amount i j, coronaLeaf amount i k} ∩ blue)) := by
  classical
  intro h
  have hs := leafy_forcing_implies_sparse core amount _ h
  exact hjk (hs i j k (by simp) (by simp))

theorem leafy_minimum_support_is_trace (core : SimpleGraph I) (amount : I → ℕ)
    (hmin : ∀ i : I, 2 ≤ amount i) (blue support : Finset (CoronaVertex I amount))
    (hsupport : IsMinimumKilling (coronaAdj core amount) blue support) :
    ∃ (i : I) (j k : Fin (amount i)), j ≠ k ∧
      support = {coronaLeaf amount i j, coronaLeaf amount i k} ∩ blue := by
  classical
  have hex : ∃ (i : I) (j k : Fin (amount i)), j ≠ k ∧
      coronaLeaf amount i j ∉ blue \ support ∧
      coronaLeaf amount i k ∉ blue \ support := by
    by_contra hnone
    apply hsupport.2.1
    apply (leafy_forcing_iff_sparse core amount hmin _).mpr
    intro i j k hj hk
    by_contra hjk
    exact hnone ⟨i, j, k, hjk, hj, hk⟩
  obtain ⟨i, j, k, hjk, hj, hk⟩ := hex
  let trace : Finset (CoronaVertex I amount) :=
    {coronaLeaf amount i j, coronaLeaf amount i k} ∩ blue
  have hsub : trace ⊆ support := by
    intro x hx
    have hx' : (x = coronaLeaf amount i j ∨ x = coronaLeaf amount i k) ∧ x ∈ blue := by
      simpa [trace] using hx
    rcases hx'.1 with rfl | rfl
    · by_contra hn
      exact hj (Finset.mem_sdiff.mpr ⟨hx'.2, hn⟩)
    · by_contra hn
      exact hk (Finset.mem_sdiff.mpr ⟨hx'.2, hn⟩)
  have hkill : ¬ IsForcing (coronaAdj core amount) (blue \ trace) :=
    leafy_pair_trace_kills core amount blue i j k hjk
  have hcard : support.card ≤ trace.card :=
    le_of_not_gt (fun hlt => hkill
      (hsupport.2.2 trace (fun _ hx => hsupport.1 (hsub hx)) hlt))
  have heq : trace = support := Finset.eq_of_subset_of_card_le hsub hcard
  exact ⟨i, j, k, hjk, heq.symm⟩

theorem leafy_minimum_support_card_le_two (core : SimpleGraph I) (amount : I → ℕ)
    (hmin : ∀ i : I, 2 ≤ amount i) (blue support : Finset (CoronaVertex I amount))
    (hsupport : IsMinimumKilling (coronaAdj core amount) blue support) :
    support.card ≤ 2 := by
  classical
  obtain ⟨i, j, k, _, heq⟩ := leafy_minimum_support_is_trace core amount hmin blue support hsupport
  rw [heq]
  calc
    ({coronaLeaf amount i j, coronaLeaf amount i k} ∩ blue).card ≤
        ({coronaLeaf amount i j, coronaLeaf amount i k} : Finset _).card :=
      Finset.card_le_card Finset.inter_subset_left
    _ ≤ 2 := by
      simpa only [Finset.card_singleton] using
        (Finset.card_insert_le (coronaLeaf amount i j) {coronaLeaf amount i k})

theorem leafy_minimum_two_all_leaves_blue (core : SimpleGraph I) (amount : I → ℕ)
    (hmin : ∀ i : I, 2 ≤ amount i) (blue support : Finset (CoronaVertex I amount))
    (hforcing : IsForcing (coronaAdj core amount) blue)
    (hsupport : IsMinimumKilling (coronaAdj core amount) blue support)
    (hcard : support.card = 2) : AllLeavesBlue amount blue := by
  classical
  intro i j
  by_contra hj
  obtain ⟨k, hk⟩ := sparse_exists_blue_leaf amount hmin blue
    (leafy_forcing_implies_sparse core amount blue hforcing) i
  let loss : Finset (CoronaVertex I amount) := {coronaLeaf amount i k}
  have hsub : loss ⊆ blue := by simpa [loss] using hk
  have hsmall : loss.card < support.card := by simp [loss, hcard]
  have hf := hsupport.2.2 loss hsub hsmall
  have hs := leafy_forcing_implies_sparse core amount (blue \ loss) hf
  have hjwhite : coronaLeaf amount i j ∉ blue \ loss :=
    fun h => hj (Finset.mem_sdiff.mp h).1
  have hkwhite : coronaLeaf amount i k ∉ blue \ loss := by simp [loss]
  have heq := hs i j k hjwhite hkwhite
  apply hj
  simpa only [heq] using hk

theorem robustBy_zero_iff {V : Type u} [Fintype V] [DecidableEq V] (adj : V → V → Prop)
    (blue allowed : Finset V) (deadline : ℕ) :
    RobustBy adj blue allowed 0 deadline ↔ FinishesBy adj blue deadline := by
  classical
  constructor
  · intro h
    simpa using h ∅ (Finset.empty_subset _) (by simp)
  · intro h loss _ hcard
    have hempty : loss = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)
    simpa only [hempty, Finset.sdiff_empty] using h

theorem leafy_erased_leaf_not_one_complete (core : SimpleGraph I) (amount : I → ℕ)
    (hcomplete : CoreComplete core) (blue : Finset (CoronaVertex I amount))
    (whiteCore : I) (hwhite : Sum.inl whiteCore ∉ blue) (i : I) (j : Fin (amount i)) :
    ¬ FinishesBy (coronaAdj core amount) (blue \ {coronaLeaf amount i j}) 1 := by
  classical
  intro hfinish
  change synchronousStep (coronaAdj core amount) (blue \ {coronaLeaf amount i j}) =
    Finset.univ at hfinish
  have hm : coronaLeaf amount i j ∈
      synchronousStep (coronaAdj core amount) (blue \ {coronaLeaf amount i j}) := by
    rw [hfinish]
    exact Finset.mem_univ _
  rcases (mem_synchronousStep _ _ _).mp hm with hold | ⟨source, hs, ha, hu⟩
  · exact (Finset.mem_sdiff.mp hold).2 (by simp)
  · cases source with
    | inl v =>
      change v = i at ha
      subst v
      have hcore : Sum.inl i ∈ blue := (Finset.mem_sdiff.mp hs).1
      have hne : i ≠ whiteCore := by
        intro heq
        exact hwhite (by simpa only [heq] using hcore)
      have hadj := hcomplete i whiteCore hne
      have hw : Sum.inl whiteCore ∉ blue \ {coronaLeaf amount i j} :=
        fun h => hwhite (Finset.mem_sdiff.mp h).1
      have hbad := hu (Sum.inl whiteCore) hadj hw
      cases hbad
    | inr leaf => exact False.elim ha

theorem leafy_full_single_loss_finishes_one (core : SimpleGraph I) (amount : I → ℕ)
    (hmin : ∀ i : I, 2 ≤ amount i) (loss : Finset (CoronaVertex I amount))
    (hcard : loss.card ≤ 1) :
    FinishesBy (coronaAdj core amount) (Finset.univ \ loss) 1 := by
  classical
  change synchronousStep (coronaAdj core amount) (Finset.univ \ loss) = Finset.univ
  apply Finset.eq_univ_of_forall
  intro target
  apply (mem_synchronousStep _ _ _).mpr
  by_cases ht : target ∈ Finset.univ \ loss
  · exact Or.inl ht
  · have htL : target ∈ loss := by simpa using ht
    have hex : ∃ source : CoronaVertex I amount,
        source ≠ target ∧ coronaAdj core amount source target := by
      cases target with
      | inl i =>
        let j : Fin (amount i) := ⟨0, by have := hmin i; omega⟩
        refine ⟨coronaLeaf amount i j, ?_, rfl⟩
        intro heq
        cases heq
      | inr leaf =>
        rcases leaf with ⟨i, j⟩
        refine ⟨Sum.inl i, ?_, rfl⟩
        intro heq
        cases heq
    obtain ⟨source, hne, hadj⟩ := hex
    have hsL : source ∉ loss :=
      fun h => hne (Finset.card_le_one.mp hcard source h target htL)
    refine Or.inr ⟨source, by simp [hsL], hadj, ?_⟩
    intro other _ hwhite
    have hoL : other ∈ loss := by simpa using hwhite
    exact Finset.card_le_one.mp hcard other hoL target htL

theorem leafy_complete_every_minimum_support (core : SimpleGraph I) (amount : I → ℕ)
    (hmin : ∀ i : I, 2 ≤ amount i) (hcomplete : CoreComplete core) :
    EveryMinimumSupport (coronaAdj core amount) := by
  classical
  intro blue hforcing support hsupport budget deadline
  constructor
  · intro h loss hsub hcard
    exact h loss (fun _ hx => hsupport.1 (hsub hx)) hcard
  · intro hrestricted
    by_cases hlarge : support.card ≤ budget
    · exact False.elim (hsupport.2.1
        ⟨deadline, hrestricted support (fun _ hx => hx) hlarge⟩)
    by_cases hzero : budget = 0
    · subst budget
      exact (robustBy_zero_iff _ blue blue deadline).mpr
        ((robustBy_zero_iff _ blue support deadline).mp hrestricted)
    have hbound := leafy_minimum_support_card_le_two core amount hmin blue support hsupport
    have htwo : support.card = 2 := by omega
    have hbudget : budget = 1 := by omega
    subst budget
    have hall := leafy_minimum_two_all_leaves_blue core amount hmin blue support
      hforcing hsupport htwo
    obtain ⟨i, j, k, _, htrace⟩ :=
      leafy_minimum_support_is_trace core amount hmin blue support hsupport
    have hjH : coronaLeaf amount i j ∈ support := by rw [htrace]; simp [hall i j]
    have hsingle : {coronaLeaf amount i j} ⊆ support := by simpa using hjH
    have hdone := hrestricted {coronaLeaf amount i j} hsingle (by simp)
    by_cases hcores : ∀ i : I, Sum.inl i ∈ blue
    · have hfull : blue = Finset.univ := by
        apply Finset.eq_univ_of_forall
        intro v
        cases v with
        | inl v => exact hcores v
        | inr leaf => exact hall leaf.1 leaf.2
      have hd : 1 ≤ deadline := by
        by_contra hn
        have hz : deadline = 0 := by omega
        subst deadline
        change blue \ {coronaLeaf amount i j} = Finset.univ at hdone
        have hm : coronaLeaf amount i j ∈ blue \ {coronaLeaf amount i j} := by
          rw [hdone]
          exact Finset.mem_univ _
        simp at hm
      intro loss _ hcard
      rw [hfull]
      exact FinishesBy_mono_time _ _
        (leafy_full_single_loss_finishes_one core amount hmin loss hcard) hd
    · have hex : ∃ w : I, Sum.inl w ∉ blue := by
        by_contra hn
        apply hcores
        intro w
        by_contra hw
        exact hn ⟨w, hw⟩
      obtain ⟨w, hw⟩ := hex
      have hnot := leafy_erased_leaf_not_one_complete core amount hcomplete blue w hw i j
      have hd : 2 ≤ deadline := by
        by_contra hn
        have hle : deadline ≤ 1 := by omega
        exact hnot (FinishesBy_mono_time _ _ hdone hle)
      intro loss hsub hcard
      have hf := hsupport.2.2 loss hsub (by omega)
      have htwoRound := (leafy_forcing_iff_two_rounds core amount hmin _).mp hf
      exact FinishesBy_mono_time _ _ htwoRound hd

theorem leafy_erased_leaf_not_one_white_center (core : SimpleGraph I) (amount : I → ℕ)
    (blue : Finset (CoronaVertex I amount)) (i : I) (j : Fin (amount i))
    (hwhite : Sum.inl i ∉ blue) :
    ¬ FinishesBy (coronaAdj core amount) (blue \ {coronaLeaf amount i j}) 1 := by
  classical
  intro hfinish
  change synchronousStep (coronaAdj core amount) (blue \ {coronaLeaf amount i j}) =
    Finset.univ at hfinish
  have hm : coronaLeaf amount i j ∈
      synchronousStep (coronaAdj core amount) (blue \ {coronaLeaf amount i j}) := by
    rw [hfinish]
    exact Finset.mem_univ _
  rcases (mem_synchronousStep _ _ _).mp hm with hold | ⟨source, hs, ha, _⟩
  · exact (Finset.mem_sdiff.mp hold).2 (by simp)
  · cases source with
    | inl v =>
      change v = i at ha
      subst v
      exact hwhite (Finset.mem_sdiff.mp hs).1
    | inr leaf => exact False.elim ha

theorem leafy_nonadjacent_restricted_one_round (core : SimpleGraph I) (amount : I → ℕ)
    (hmin : ∀ i : I, 2 ≤ amount i) (v w : I) (hne : v ≠ w)
    (hnadj : ¬ core.Adj v w) (loss : Finset (CoronaVertex I amount))
    (hleaves : ∀ x ∈ loss, ∃ j : Fin (amount v), x = coronaLeaf amount v j)
    (hcard : loss.card ≤ 1) :
    FinishesBy (coronaAdj core amount) ((Finset.univ \ {Sum.inl w}) \ loss) 1 := by
  classical
  let initial : Finset (CoronaVertex I amount) := Finset.univ \ {Sum.inl w}
  let blue := initial \ loss
  have hall : AllLeavesBlue amount initial := by
    intro i j
    simp [initial, coronaLeaf]
  have hsparse : LeafSparse amount blue :=
    leafy_forcing_implies_sparse core amount blue
      (leafy_single_loss_forcing core amount hmin initial loss hall hcard)
  have hcoreStep : ∀ i : I, Sum.inl i ∈ synchronousStep (coronaAdj core amount) blue := by
    intro i
    obtain ⟨j, hj⟩ := sparse_exists_blue_leaf amount hmin blue hsparse i
    exact core_mem_step_of_blue_leaf core amount blue i j hj
  have hshape : ∀ x : CoronaVertex I amount, x ∉ blue → x = Sum.inl w ∨ x ∈ loss := by
    intro x hx
    by_cases hxl : x ∈ loss
    · exact Or.inr hxl
    · left
      by_contra hne'
      exact hx (Finset.mem_sdiff.mpr ⟨by simp [initial, hne'], hxl⟩)
  have hvNot : Sum.inl v ∉ loss := by
    intro hv
    obtain ⟨j, heq⟩ := hleaves _ hv
    cases heq
  have hvBlue : Sum.inl v ∈ blue := by simp [blue, initial, hne, hvNot]
  change synchronousStep (coronaAdj core amount) blue = Finset.univ
  apply Finset.eq_univ_of_forall
  intro target
  cases target with
  | inl i => exact hcoreStep i
  | inr leaf =>
    by_cases hblue : Sum.inr leaf ∈ blue
    · exact subset_synchronousStep _ _ hblue
    · have hL : Sum.inr leaf ∈ loss := by
        rcases hshape _ hblue with heq | hl
        · cases heq
        · exact hl
      obtain ⟨j, heq⟩ := hleaves _ hL
      rw [heq]
      apply (mem_synchronousStep _ _ _).mpr
      refine Or.inr ⟨Sum.inl v, hvBlue, rfl, ?_⟩
      intro other ha hwhite
      rcases hshape other hwhite with hw | hoL
      · subst other
        exact False.elim (hnadj ha)
      · have hjL : coronaLeaf amount v j ∈ loss := by simpa only [heq] using hL
        exact Finset.card_le_one.mp hcard other hoL _ hjL

theorem leafy_not_support_of_nonadjacent (core : SimpleGraph I) (amount : I → ℕ)
    (hmin : ∀ i : I, 2 ≤ amount i) (v w : I) (hne : v ≠ w)
    (hnadj : ¬ core.Adj v w) : ¬ EveryMinimumSupport (coronaAdj core amount) := by
  classical
  intro hU
  let blue : Finset (CoronaVertex I amount) := Finset.univ \ {Sum.inl w}
  let j : Fin (amount v) := ⟨0, by have := hmin v; omega⟩
  let k : Fin (amount v) := ⟨1, by have := hmin v; omega⟩
  have hjk : j ≠ k := by
    intro heq
    have hval := congrArg Fin.val heq
    change (0 : ℕ) = 1 at hval
    exact Nat.zero_ne_one hval
  let support : Finset (CoronaVertex I amount) :=
    {coronaLeaf amount v j, coronaLeaf amount v k}
  have hleafNe : coronaLeaf amount v j ≠ coronaLeaf amount v k :=
    fun h => hjk (coronaLeaf_injective amount v h)
  have hHcard : support.card = 2 := by simp [support, hleafNe]
  have hall : AllLeavesBlue amount blue := by intro i l; simp [blue, coronaLeaf]
  have hforcing : IsForcing (coronaAdj core amount) blue := by
    apply (leafy_forcing_iff_sparse core amount hmin blue).mpr
    intro i l m hl _
    exact False.elim (hl (hall i l))
  have hHsub : support ⊆ blue := by
    intro x hx
    have hpair : x = coronaLeaf amount v j ∨ x = coronaLeaf amount v k := by
      simpa [support] using hx
    rcases hpair with rfl | rfl
    · exact hall v j
    · exact hall v k
  have hkill : ¬ IsForcing (coronaAdj core amount) (blue \ support) := by
    intro hf
    have hs := leafy_forcing_implies_sparse core amount _ hf
    exact hjk (hs v j k (by simp [support]) (by simp [support]))
  have hminimum : IsMinimumKilling (coronaAdj core amount) blue support := by
    refine ⟨hHsub, hkill, ?_⟩
    intro loss _ hsmall
    exact leafy_single_loss_forcing core amount hmin blue loss hall (by omega)
  have hrestricted : RobustBy (coronaAdj core amount) blue support 1 1 := by
    intro loss hsub hcard
    have hleaves : ∀ x ∈ loss, ∃ l : Fin (amount v), x = coronaLeaf amount v l := by
      intro x hx
      have hpair : x = coronaLeaf amount v j ∨ x = coronaLeaf amount v k := by
        simpa [support] using hsub hx
      rcases hpair with h | h
      · exact ⟨j, h⟩
      · exact ⟨k, h⟩
    exact leafy_nonadjacent_restricted_one_round core amount hmin v w hne hnadj
      loss hleaves hcard
  have hglobal : ¬ RobustBy (coronaAdj core amount) blue blue 1 1 := by
    intro hg
    let l : Fin (amount w) := ⟨0, by have := hmin w; omega⟩
    have hsub : {coronaLeaf amount w l} ⊆ blue := by simpa using hall w l
    have hdone := hg {coronaLeaf amount w l} hsub (by simp)
    have hw : Sum.inl w ∉ blue := by simp [blue]
    exact leafy_erased_leaf_not_one_white_center core amount blue w l hw hdone
  exact hglobal ((hU blue hforcing support hminimum 1 1).mpr hrestricted)

theorem leafy_every_minimum_support_iff_complete (core : SimpleGraph I) (amount : I → ℕ)
    (hmin : ∀ i : I, 2 ≤ amount i) :
    EveryMinimumSupport (coronaAdj core amount) ↔ CoreComplete core := by
  constructor
  · intro hU v w hne
    by_contra hnadj
    exact leafy_not_support_of_nonadjacent core amount hmin v w hne hnadj hU
  · exact leafy_complete_every_minimum_support core amount hmin

theorem leafyCoreTarget_proved [Nonempty I] (core : SimpleGraph I) (amount : I → ℕ) :
    LeafyCoreTarget I core amount := by
  intro hmin
  exact leafy_every_minimum_support_iff_complete core amount hmin

end FaultObservationResearch
