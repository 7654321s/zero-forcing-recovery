module

public import «formalization-foundations»

@[expose] public section

set_option autoImplicit false

namespace FaultObservationResearch

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A finite time gap witnessed by one loss outside a two-element killing support. -/
structure BudgetOnePairWitness (adj : V → V → Prop) (blue support : Finset V)
    (slow : V) (deadline : ℕ) : Prop where
  pair : support.card = 2
  supportBlue : support ⊆ blue
  doubleFails : ¬ IsForcing adj (blue \ support)
  singletonFinishes : ∀ x ∈ blue, IsForcing adj (blue \ {x})
  restrictedFinishes : RobustBy adj blue support 1 deadline
  slowBlue : slow ∈ blue
  slowMisses : ¬ FinishesBy adj (blue \ {slow}) deadline

theorem robustBy_one_iff (adj : V → V → Prop) (blue allowed : Finset V) (deadline : ℕ) :
    RobustBy adj blue allowed 1 deadline ↔ FinishesBy adj blue deadline ∧
      ∀ x ∈ allowed, FinishesBy adj (blue \ {x}) deadline := by
  constructor
  · intro h
    refine ⟨?_, fun x hx => h {x} (Finset.singleton_subset_iff.mpr hx) (by simp)⟩
    simpa using h ∅ (Finset.empty_subset _) (by simp)
  · rintro ⟨hIntact, hSingleton⟩ loss hAllowed hCard
    by_cases hEmpty : loss = ∅
    · simpa [hEmpty] using hIntact
    · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
      have hEq : loss = {x} := by
        ext y
        rw [Finset.mem_singleton]
        exact ⟨fun hy => (Finset.card_le_one_iff.mp hCard) hy hx, fun hy => hy ▸ hx⟩
      rw [hEq]
      exact hSingleton x (hAllowed hx)

theorem BudgetOnePairWitness.minimumKilling {adj : V → V → Prop}
    {blue support : Finset V} {slow : V} {deadline : ℕ}
    (h : BudgetOnePairWitness adj blue support slow deadline) :
    IsMinimumKilling adj blue support := by
  refine ⟨h.supportBlue, h.doubleFails, ?_⟩
  intro loss hLoss hSize
  have hAtMostOne : loss.card ≤ 1 := by rw [h.pair] at hSize; omega
  by_cases hEmpty : loss = ∅
  · have hZero : FinishesBy adj (blue \ ∅) deadline :=
      h.restrictedFinishes ∅ (Finset.empty_subset _) (by simp)
    simpa only [hEmpty] using (show IsForcing adj (blue \ ∅) from ⟨deadline, hZero⟩)
  · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
    have hEq : loss = {x} := by
      ext y
      rw [Finset.mem_singleton]
      exact ⟨fun hy => (Finset.card_le_one_iff.mp hAtMostOne) hy hx,
        fun hy => hy ▸ hx⟩
    rw [hEq]
    exact h.singletonFinishes x (hLoss hx)

theorem BudgetOnePairWitness.not_everyMinimumSupport {adj : V → V → Prop}
    {blue support : Finset V} {slow : V} {deadline : ℕ}
    (h : BudgetOnePairWitness adj blue support slow deadline) :
    ¬ EveryMinimumSupport adj := by
  intro hEvery
  have hBlue : IsForcing adj blue :=
    h.minimumKilling.2.2 ∅ (Finset.empty_subset _) (by simp [h.pair])
    |> fun ⟨t, ht⟩ => ⟨t, by simpa using ht⟩
  have hAll := (hEvery blue hBlue support h.minimumKilling 1 deadline).mpr
    h.restrictedFinishes
  exact h.slowMisses (hAll {slow} (Finset.singleton_subset_iff.mpr h.slowBlue) (by simp))

/-- A white tail's restricted term is dominated by its own slow term or by a
longest increment whose slow arrival beats the restricted arrival. -/
theorem tail_term_lt_slow (r s delta deltaMax sMax : ℕ)
    (h : r < s ∨ (r < sMax ∧ delta ≤ deltaMax)) :
    r + delta < max (s + delta) (sMax + deltaMax) := by
  rcases h with hOwn | ⟨hArrival, hLength⟩
  · exact lt_of_lt_of_le (by omega : r + delta < s + delta) (le_max_left _ _)
  · exact lt_of_lt_of_le (by omega : r + delta < sMax + deltaMax) (le_max_right _ _)

/-- Alternating side paths with length at most half the final long arm
contribute at most one plus the long arm's extension. -/
theorem side_path_budget (base increment length : ℕ) (hBase : base ≤ 4)
    (hLength : length ≤ (base + increment) / 2) :
    (length + 1) / 2 ≤ 1 + increment := by
  omega

theorem combined_deadline_le_iff (base bound : ℕ) (terms : List ℕ) :
    terms.foldr max base ≤ bound ↔ base ≤ bound ∧ ∀ t ∈ terms, t ≤ bound := by
  induction terms with
  | nil => simp
  | cons term terms ih =>
    simp only [List.foldr_cons, max_le_iff, ih, List.mem_cons]
    constructor
    · rintro ⟨hTerm, hBase, hTerms⟩
      exact ⟨hBase, fun t ht => ht.elim (fun e => e ▸ hTerm) (hTerms t)⟩
    · rintro ⟨hBase, hTerms⟩
      exact ⟨hTerms term (Or.inl rfl), hBase, fun t ht => hTerms t (Or.inr ht)⟩

/-- Dominate every restricted term by the same slow bound to obtain a
strict gap for any finite collection of extensions. -/
theorem combined_deadline_lt (base slow : ℕ) (terms : List ℕ)
    (hBase : base < slow) (hTerms : ∀ t ∈ terms, t < slow) :
    terms.foldr max base < slow := by
  have hBound : terms.foldr max base ≤ slow - 1 := by
    apply (combined_deadline_le_iff base (slow - 1) terms).mpr
    exact ⟨by omega, fun t ht => by have := hTerms t ht; omega⟩
  omega

end FaultObservationResearch

#print axioms FaultObservationResearch.BudgetOnePairWitness.minimumKilling
#print axioms FaultObservationResearch.BudgetOnePairWitness.not_everyMinimumSupport
#print axioms FaultObservationResearch.robustBy_one_iff
#print axioms FaultObservationResearch.tail_term_lt_slow
#print axioms FaultObservationResearch.side_path_budget
#print axioms FaultObservationResearch.combined_deadline_lt
