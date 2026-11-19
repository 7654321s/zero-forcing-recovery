module

public import «formalization-foundations»

@[expose] public section

set_option autoImplicit false

namespace FaultObservationResearch

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

private def CanForce (adj : V → V → Prop) (blue : Finset V) (source target : V) : Prop :=
  source ∈ blue ∧ adj source target ∧
    ∀ other, adj source other → other ∉ blue → other = target

private theorem source_of_finishes_one (adj : V → V → Prop) (blue : Finset V)
    (intact : FinishesBy adj blue 1) (target : V) (white : target ∉ blue) :
    ∃ source, CanForce adj blue source target := by
  have colored : target ∈ colorAfter adj blue 1 := by
    unfold FinishesBy at intact
    rw [intact]
    exact Finset.mem_univ target
  rcases (mem_synchronousStep adj blue target).mp colored with early | ⟨v, hv⟩
  · exact False.elim (white early)
  · exact ⟨v, hv⟩

private theorem retained_initial_blue (adj : V → V → Prop) (blue : Finset V)
    (lost : V) (rounds : ℕ) : blue \ {lost} ⊆ colorAfter adj (blue \ {lost}) rounds :=
  colorAfter_mono_time adj _ (Nat.zero_le rounds)

private theorem recovered_target_enables_loss (adj : V → V → Prop) (blue : Finset V)
    (lost source target : V) (retained : source ≠ lost)
    (oldForce : CanForce adj blue source target)
    (missedFirst : target ∉ colorAfter adj (blue \ {lost}) 1)
    {rounds : ℕ} (recovered : target ∈ colorAfter adj (blue \ {lost}) rounds) :
    lost ∈ colorAfter adj (blue \ {lost}) (rounds + 1) := by
  classical
  obtain ⟨sourceBlue, targetEdge, unique⟩ := oldForce
  have sourceRetained : source ∈ blue \ {lost} :=
    Finset.mem_sdiff.mpr ⟨sourceBlue, by simpa using retained⟩
  have lostEdge : adj source lost := by
    by_contra noEdge
    apply missedFirst
    apply (mem_synchronousStep adj (blue \ {lost}) target).mpr
    refine Or.inr ⟨source, sourceRetained, targetEdge, ?_⟩
    intro w edge white
    apply unique w edge
    intro wasBlue
    have ne : w ≠ lost := fun eq => noEdge (eq ▸ edge)
    exact white (Finset.mem_sdiff.mpr ⟨wasBlue, by simpa using ne⟩)
  have retainedBlue := retained_initial_blue adj blue lost rounds
  apply (mem_synchronousStep adj _ lost).mpr
  refine Or.inr ⟨source, retainedBlue sourceRetained, lostEdge, ?_⟩
  intro w edge white
  by_contra ne
  have wasWhite : w ∉ blue := fun wasBlue =>
    white (retainedBlue (Finset.mem_sdiff.mpr ⟨wasBlue, by simpa using ne⟩))
  exact white ((unique w edge wasWhite).symm ▸ recovered)

private theorem fresh_original_white (adj : V → V → Prop) (blue : Finset V)
    (lost : V) (recovers : IsForcing adj (blue \ {lost})) (t : ℕ)
    (lostMissing : lost ∉ colorAfter adj (blue \ {lost}) (t + 1)) :
    ∃ w, w ∉ blue ∧ w ∈ colorAfter adj (blue \ {lost}) (t + 1) ∧
      w ∉ colorAfter adj (blue \ {lost}) t := by
  have unfinished : ¬ FinishesBy adj (blue \ {lost}) t := by
    intro finished
    unfold FinishesBy at finished
    have present : lost ∈ colorAfter adj (blue \ {lost}) t := by
      rw [finished]
      exact Finset.mem_univ lost
    exact lostMissing (colorAfter_subset_succ adj _ t present)
  obtain ⟨w, nowBlue, earlierWhite⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (card_colorAfter_strict_of_unfinished adj _ recovers t unfinished)
  have ne : w ≠ lost := fun eq => lostMissing (eq ▸ nowBlue)
  refine ⟨w, ?_, nowBlue, earlierWhite⟩
  intro wasBlue
  exact earlierWhite (retained_initial_blue adj blue lost t
    (Finset.mem_sdiff.mpr ⟨wasBlue, by simpa using ne⟩))

private theorem finishes_one_after_loss_returns (adj : V → V → Prop) (blue : Finset V)
    (lost : V) (intact : FinishesBy adj blue 1) {rounds : ℕ}
    (returned : lost ∈ colorAfter adj (blue \ {lost}) rounds) :
    FinishesBy adj (blue \ {lost}) (rounds + 1) := by
  classical
  have contains : blue ⊆ colorAfter adj (blue \ {lost}) rounds := by
    intro v hv
    by_cases eq : v = lost
    · exact eq.symm ▸ returned
    · exact retained_initial_blue adj blue lost rounds
        (Finset.mem_sdiff.mpr ⟨hv, by simpa using eq⟩)
  have next := FinishesBy_mono_blue adj contains intact
  unfold FinishesBy at next ⊢
  rwa [← colorAfter_add] at next

theorem single_loss_finishes_by_five_of_intact_one (adj : V → V → Prop) (blue : Finset V)
    (lost : V) (intact : FinishesBy adj blue 1) (recovers : IsForcing adj (blue \ {lost})) :
    FinishesBy adj (blue \ {lost}) 5 := by
  classical
  apply finishes_one_after_loss_returns adj blue lost intact (rounds := 4)
  by_contra missing
  have absent (t : ℕ) (le : t ≤ 4) : lost ∉ colorAfter adj (blue \ {lost}) t :=
    fun h => missing (colorAfter_mono_time adj _ le h)
  obtain ⟨u, uWhite, uTwo, uNotOne⟩ := fresh_original_white adj blue lost recovers 1 (absent 2 (by decide))
  obtain ⟨v, vWhite, vThree, vNotTwo⟩ := fresh_original_white adj blue lost recovers 2 (absent 3 (by decide))
  have vNotOne : v ∉ colorAfter adj (blue \ {lost}) 1 :=
    fun h => vNotTwo (colorAfter_subset_succ adj _ 1 h)
  obtain ⟨sourceU, forceU⟩ := source_of_finishes_one adj blue intact u uWhite
  obtain ⟨sourceV, forceV⟩ := source_of_finishes_one adj blue intact v vWhite
  have sourceUEq : sourceU = lost := by
    by_contra ne
    exact absent 3 (by decide) (recovered_target_enables_loss adj blue lost sourceU u ne forceU uNotOne uTwo)
  have sourceVEq : sourceV = lost := by
    by_contra ne
    exact missing (recovered_target_enables_loss adj blue lost sourceV v ne forceV vNotOne vThree)
  rw [sourceUEq] at forceU
  rw [sourceVEq] at forceV
  have same : v = u := forceU.2.2 v forceV.2.1 vWhite
  exact vNotTwo (same.symm ▸ uTwo)

theorem single_loss_finishes_by_four_with_blue_representative (adj : V → V → Prop)
    (blue : Finset V) (lost mate : V) (different : mate ≠ lost) (mateBlue : mate ∈ blue)
    (agreement : ∀ w ∉ blue, adj lost w ↔ adj mate w)
    (intact : FinishesBy adj blue 1) (recovers : IsForcing adj (blue \ {lost})) :
    FinishesBy adj (blue \ {lost}) 4 := by
  classical
  apply finishes_one_after_loss_returns adj blue lost intact (rounds := 3)
  by_contra missing
  have lostNotTwo : lost ∉ colorAfter adj (blue \ {lost}) 2 :=
    fun h => missing (colorAfter_subset_succ adj _ 2 h)
  obtain ⟨w, wWhite, wTwo, wNotOne⟩ := fresh_original_white adj blue lost recovers 1 lostNotTwo
  obtain ⟨source, oldForce⟩ := source_of_finishes_one adj blue intact w wWhite
  by_cases eq : source = lost
  · subst source
    have mateForce : CanForce adj blue mate w := by
      refine ⟨mateBlue, (agreement w wWhite).mp oldForce.2.1, ?_⟩
      intro v edge white
      exact oldForce.2.2 v ((agreement v white).mpr edge) white
    exact missing (recovered_target_enables_loss adj blue lost mate w different mateForce wNotOne wTwo)
  · exact missing (recovered_target_enables_loss adj blue lost source w eq oldForce wNotOne wTwo)

end FaultObservationResearch

#print axioms FaultObservationResearch.single_loss_finishes_by_five_of_intact_one
#print axioms FaultObservationResearch.single_loss_finishes_by_four_with_blue_representative
