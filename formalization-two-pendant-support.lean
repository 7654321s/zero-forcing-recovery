module

/-
The two arm heads form a cardinality-minimum killing set for the specified
initial coloring. This is a static construction, not the time separation
needed for the remaining tree-classification direction.
-/
public import «formalization-two-pendant-model»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

def twoPendantInitial (root : V) (a b : ℕ) (coreBlue : Finset V) :
    Finset (TwoPendantVertex V a b) := by
  classical
  exact Finset.univ.filter (fun z => match z with
    | Sum.inl x => x ∈ coreBlue ∨ x = root
    | Sum.inr (Sum.inl i) => i = 0
    | Sum.inr (Sum.inr j) => j = 0)

def twoPendantHeads (V : Type u) (a b : ℕ) : Finset (TwoPendantVertex V a b) := by
  classical
  exact {twoPendantA V a b 0, twoPendantB V a b 0}

omit [DecidableEq V] in
@[simp] theorem twoPendant_mem_initial_core (root x : V) (a b : ℕ) (coreBlue : Finset V) :
    twoPendantCore V a b x ∈ twoPendantInitial root a b coreBlue ↔
      x ∈ coreBlue ∨ x = root := by
  classical
  simp [twoPendantInitial, twoPendantCore]

omit [DecidableEq V] in
@[simp] theorem twoPendant_mem_initial_A (root : V) (a b : ℕ) (coreBlue : Finset V)
    (i : Fin (a + 1)) :
    twoPendantA V a b i ∈ twoPendantInitial root a b coreBlue ↔ i = 0 := by
  classical
  change Sum.inr (Sum.inl i) ∈ twoPendantInitial root a b coreBlue ↔ i = 0
  simp [twoPendantInitial]

omit [DecidableEq V] in
@[simp] theorem twoPendant_mem_initial_B (root : V) (a b : ℕ) (coreBlue : Finset V)
    (j : Fin (b + 1)) :
    twoPendantB V a b j ∈ twoPendantInitial root a b coreBlue ↔ j = 0 := by
  classical
  change Sum.inr (Sum.inr j) ∈ twoPendantInitial root a b coreBlue ↔ j = 0
  simp [twoPendantInitial]

omit [Fintype V] [DecidableEq V] in
theorem twoPendant_heads_card (a b : ℕ) : (twoPendantHeads V a b).card = 2 := by
  classical
  change ({Sum.inr (Sum.inl (0 : Fin (a + 1))),
    Sum.inr (Sum.inr (0 : Fin (b + 1)))} : Finset (TwoPendantVertex V a b)).card = 2
  simp

omit [DecidableEq V] in
theorem twoPendant_heads_subset (root : V) (a b : ℕ) (coreBlue : Finset V) :
    twoPendantHeads V a b ⊆ twoPendantInitial root a b coreBlue := by
  classical
  intro z hz
  rcases (by simpa [twoPendantHeads] using hz :
    z = twoPendantA V a b 0 ∨ z = twoPendantB V a b 0) with rfl | rfl
  · exact (twoPendant_mem_initial_A root a b coreBlue 0).mpr rfl
  · exact (twoPendant_mem_initial_B root a b coreBlue 0).mpr rfl

theorem twoPendant_singleton_loss_forcing [Nontrivial V]
    (R : SimpleGraph V) (htree : R.IsTree) (root : V) (a b : ℕ) (coreBlue : Finset V)
    (hleaves : ∀ x, TreeLeaf R x → x ≠ root → x ∈ coreBlue)
    (lost : TwoPendantVertex V a b) :
    IsForcing (twoPendantGraph R root a b).Adj
      (twoPendantInitial root a b coreBlue \ {lost}) := by
  classical
  let G := twoPendantGraph R root a b
  let B := twoPendantInitial root a b coreBlue
  let C := B \ {lost}
  have hA : twoPendantA V a b 0 ∈ B := by simp [B]
  have hB : twoPendantB V a b 0 ∈ B := by simp [B]
  rcases lost with y | (i | j)
  · have hcA : twoPendantA V a b 0 ∈ C := by
      apply Finset.mem_sdiff.mpr
      refine ⟨hA, ?_⟩
      change Sum.inr (Sum.inl (0 : Fin (a + 1))) ∉ {Sum.inl y}
      simp
    have hcB : twoPendantB V a b 0 ∈ C := by
      apply Finset.mem_sdiff.mpr
      refine ⟨hB, ?_⟩
      change Sum.inr (Sum.inr (0 : Fin (b + 1))) ∉ {Sum.inl y}
      simp
    have hc := twoPendant_core_colors_active R htree root y a b C hcA hcB (by
      intro x hx hxy
      apply Finset.mem_sdiff.mpr
      constructor
      · apply (twoPendant_mem_initial_core root x a b coreBlue).mpr
        by_cases hxr : x = root
        · exact Or.inr hxr
        · exact Or.inl (hleaves x hx hxr)
      · simpa [twoPendantCore] using hxy)
    apply IsForcing_of_forcing_colorAfter G.Adj C (Fintype.card V)
    apply twoPendant_forcing_of_core_and_head R root a b _ hc
    exact Or.inl (colorAfter_mono_time G.Adj C (Nat.zero_le _) hcA)
  · have hcB : twoPendantB V a b 0 ∈ C := by
      apply Finset.mem_sdiff.mpr
      refine ⟨hB, ?_⟩
      change Sum.inr (Sum.inr (0 : Fin (b + 1))) ∉ {Sum.inr (Sum.inl i)}
      simp
    have hc := twoPendant_core_colors_inactive R htree root a b C (by
      intro x hx hxr
      apply Finset.mem_sdiff.mpr
      constructor
      · exact (twoPendant_mem_initial_core root x a b coreBlue).mpr
          (Or.inl (hleaves x hx hxr))
      · simp [twoPendantCore])
    apply IsForcing_of_forcing_colorAfter G.Adj C (Fintype.card V)
    apply twoPendant_forcing_of_core_and_head R root a b _ hc
    exact Or.inr (colorAfter_mono_time G.Adj C (Nat.zero_le _) hcB)
  · have hcA : twoPendantA V a b 0 ∈ C := by
      apply Finset.mem_sdiff.mpr
      refine ⟨hA, ?_⟩
      change Sum.inr (Sum.inl (0 : Fin (a + 1))) ∉ {Sum.inr (Sum.inr j)}
      simp
    have hc := twoPendant_core_colors_inactive R htree root a b C (by
      intro x hx hxr
      apply Finset.mem_sdiff.mpr
      constructor
      · exact (twoPendant_mem_initial_core root x a b coreBlue).mpr
          (Or.inl (hleaves x hx hxr))
      · simp [twoPendantCore])
    apply IsForcing_of_forcing_colorAfter G.Adj C (Fintype.card V)
    apply twoPendant_forcing_of_core_and_head R root a b _ hc
    exact Or.inl (colorAfter_mono_time G.Adj C (Nat.zero_le _) hcA)

theorem twoPendant_initial_forcing [Nontrivial V]
    (R : SimpleGraph V) (htree : R.IsTree) (root : V) (a b : ℕ) (coreBlue : Finset V)
    (hleaves : ∀ x, TreeLeaf R x → x ≠ root → x ∈ coreBlue) :
    IsForcing (twoPendantGraph R root a b).Adj (twoPendantInitial root a b coreBlue) := by
  apply IsForcing_mono _ (Finset.sdiff_subset :
    twoPendantInitial root a b coreBlue \ {twoPendantCore V a b root} ⊆ _)
  exact twoPendant_singleton_loss_forcing R htree root a b coreBlue hleaves _

theorem twoPendant_only_core_step (R : SimpleGraph V) (root : V) (a b : ℕ)
    (C : Finset (TwoPendantVertex V a b))
    (hcore : ∀ z ∈ C, ∃ x, z = twoPendantCore V a b x) :
    ∀ z ∈ synchronousStep (twoPendantGraph R root a b).Adj C,
      ∃ x, z = twoPendantCore V a b x := by
  classical
  have hA : twoPendantA V a b 0 ∉ C := by
    intro h
    obtain ⟨x, hx⟩ := hcore _ h
    cases hx
  have hB : twoPendantB V a b 0 ∉ C := by
    intro h
    obtain ⟨x, hx⟩ := hcore _ h
    cases hx
  intro z hz
  rcases (mem_synchronousStep _ _ _).mp hz with hold | ⟨s, hs, ha, hu⟩
  · exact hcore z hold
  · obtain ⟨x, rfl⟩ := hcore s hs
    rcases z with y | (i | j)
    · exact ⟨y, rfl⟩
    · change x = root ∧ i = 0 at ha
      rcases ha with ⟨hroot, _⟩
      subst x
      have heq := hu (twoPendantB V a b 0) ⟨rfl, rfl⟩ hB
      cases heq
    · change x = root ∧ j = 0 at ha
      rcases ha with ⟨hroot, _⟩
      subst x
      have heq := hu (twoPendantA V a b 0) ⟨rfl, rfl⟩ hA
      cases heq

theorem twoPendant_heads_kill (R : SimpleGraph V) (root : V) (a b : ℕ)
    (coreBlue : Finset V) :
    ¬ IsForcing (twoPendantGraph R root a b).Adj
      (twoPendantInitial root a b coreBlue \ twoPendantHeads V a b) := by
  classical
  let G := twoPendantGraph R root a b
  let C := twoPendantInitial root a b coreBlue \ twoPendantHeads V a b
  have honly : ∀ t, ∀ z ∈ colorAfter G.Adj C t,
      ∃ x, z = twoPendantCore V a b x := by
    intro t
    induction t with
    | zero =>
      intro z hz
      have hm := Finset.mem_sdiff.mp hz
      rcases z with x | (i | j)
      · exact ⟨x, rfl⟩
      · have hi : i = 0 := (twoPendant_mem_initial_A root a b coreBlue i).mp hm.1
        subst i
        exact False.elim (hm.2 (by
          simp only [twoPendantHeads, Finset.mem_insert, Finset.mem_singleton]
          exact Or.inl rfl))
      · have hj : j = 0 := (twoPendant_mem_initial_B root a b coreBlue j).mp hm.1
        subst j
        exact False.elim (hm.2 (by
          simp only [twoPendantHeads, Finset.mem_insert, Finset.mem_singleton]
          exact Or.inr rfl))
    | succ t ih => exact twoPendant_only_core_step R root a b _ ih
  rintro ⟨t, ht⟩
  have hm : twoPendantA V a b 0 ∈ colorAfter G.Adj C t := by
    rw [ht]
    exact Finset.mem_univ _
  obtain ⟨x, hx⟩ := honly t _ hm
  cases hx

theorem twoPendant_heads_minimum_killing [Nontrivial V]
    (R : SimpleGraph V) (htree : R.IsTree) (root : V) (a b : ℕ) (coreBlue : Finset V)
    (hleaves : ∀ x, TreeLeaf R x → x ≠ root → x ∈ coreBlue) :
    IsMinimumKilling (twoPendantGraph R root a b).Adj
      (twoPendantInitial root a b coreBlue) (twoPendantHeads V a b) := by
  classical
  refine ⟨twoPendant_heads_subset root a b coreBlue,
    twoPendant_heads_kill R root a b coreBlue, ?_⟩
  intro loss _ hsmall
  rw [twoPendant_heads_card] at hsmall
  by_cases he : loss = ∅
  · simpa [he] using twoPendant_initial_forcing R htree root a b coreBlue hleaves
  · have hone : loss.card = 1 := by
      have hp := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
      omega
    obtain ⟨lost, rfl⟩ := Finset.card_eq_one.mp hone
    exact twoPendant_singleton_loss_forcing R htree root a b coreBlue hleaves lost

end FaultObservationResearch
