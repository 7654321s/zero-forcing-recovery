module

public import «formalization-foundations»

@[expose] public section

set_option autoImplicit false

namespace FaultObservationResearch

universe u

variable {V : Type u}

/-- Agreement at every vertex outside the two indicated vertices. -/
def TwinOutsidePair (adj : V → V → Prop) (x y : V) : Prop :=
  ∀ v, v ≠ x → v ≠ y → (adj x v ↔ adj y v)

variable [Fintype V] [DecidableEq V]

/-- Retain the induced graph on `keep`, with discarded vertices isolated in
the ambient type so both colorings can be compared as finsets of `V`. -/
def twinKeptAdj (adj : V → V → Prop) (keep : Finset V) (x y : V) : Prop :=
  x ∈ keep ∧ y ∈ keep ∧ adj x y

omit [Fintype V] [DecidableEq V] in
theorem TwinOutsidePair.agrees_on_white {adj : V → V → Prop} {x y : V}
    (twins : TwinOutsidePair adj x y) {blue : Finset V}
    (hx : x ∈ blue) (hy : y ∈ blue) {v : V} (hv : v ∉ blue) :
    adj x v ↔ adj y v :=
  twins v (fun h => hv (h.symm ▸ hx)) (fun h => hv (h.symm ▸ hy))

theorem twin_truncation_step (adj : V → V → Prop) (keep blue : Finset V)
    (extraBlue : ∀ v ∉ keep, v ∈ blue)
    (representative : ∀ v ∉ keep, ∃ u ∈ keep, u ∈ blue ∧ TwinOutsidePair adj u v) :
    synchronousStep adj blue = synchronousStep (twinKeptAdj adj keep) blue := by
  classical
  have keepWhite (v : V) (h : v ∉ blue) : v ∈ keep := by
    by_contra outside
    exact h (extraBlue v outside)
  ext target
  rw [mem_synchronousStep, mem_synchronousStep]
  by_cases targetBlue : target ∈ blue
  · simp only [targetBlue, true_or]
  simp only [targetBlue, false_or]
  have targetKept := keepWhite target targetBlue
  constructor
  · rintro ⟨v, vBlue, edge, unique⟩
    by_cases vKept : v ∈ keep
    · refine ⟨v, vBlue, ⟨vKept, targetKept, edge⟩, ?_⟩
      intro w edge' wWhite
      exact unique w edge'.2.2 wWhite
    · obtain ⟨u, uKept, uBlue, agreement⟩ := representative v vKept
      have targetEdge := (agreement.agrees_on_white uBlue vBlue targetBlue).mpr edge
      refine ⟨u, uBlue, ⟨uKept, targetKept, targetEdge⟩, ?_⟩
      intro w edge' wWhite
      exact unique w ((agreement.agrees_on_white uBlue vBlue wWhite).mp edge'.2.2) wWhite
  · rintro ⟨u, uBlue, edge, unique⟩
    refine ⟨u, uBlue, edge.2.2, ?_⟩
    intro w edge' wWhite
    exact unique w ⟨edge.1, keepWhite w wWhite, edge'⟩ wWhite

theorem twin_truncation_colorAfter (adj : V → V → Prop) (keep blue : Finset V)
    (extraBlue : ∀ v ∉ keep, v ∈ blue)
    (representative : ∀ v ∉ keep, ∃ u ∈ keep, u ∈ blue ∧ TwinOutsidePair adj u v)
    (rounds : ℕ) : colorAfter adj blue rounds = colorAfter (twinKeptAdj adj keep) blue rounds := by
  induction rounds with
  | zero => rfl
  | succ t ih =>
    change synchronousStep adj (colorAfter adj blue t) =
      synchronousStep (twinKeptAdj adj keep) (colorAfter (twinKeptAdj adj keep) blue t)
    rw [← ih]
    have earlier : blue ⊆ colorAfter adj blue t := colorAfter_mono_time adj blue (Nat.zero_le t)
    apply twin_truncation_step
    · exact fun v hv => earlier (extraBlue v hv)
    · intro v hv
      obtain ⟨u, uKept, uBlue, hTwin⟩ := representative v hv
      exact ⟨u, uKept, earlier uBlue, hTwin⟩

theorem twin_truncation_finishesBy (adj : V → V → Prop) (keep blue : Finset V)
    (extraBlue : ∀ v ∉ keep, v ∈ blue)
    (representative : ∀ v ∉ keep, ∃ u ∈ keep, u ∈ blue ∧ TwinOutsidePair adj u v)
    (deadline : ℕ) : FinishesBy adj blue deadline ↔
      FinishesBy (twinKeptAdj adj keep) blue deadline := by
  unfold FinishesBy
  rw [twin_truncation_colorAfter adj keep blue extraBlue representative]

theorem twin_pair_stays_white (adj : V → V → Prop) (symm : ∀ ⦃u v : V⦄, adj u v → adj v u)
    {x y : V} (distinct : x ≠ y) (twins : TwinOutsidePair adj x y)
    (blue : Finset V) (xWhite : x ∉ blue) (yWhite : y ∉ blue) (rounds : ℕ) :
    x ∉ colorAfter adj blue rounds ∧ y ∉ colorAfter adj blue rounds := by
  induction rounds with
  | zero => exact ⟨xWhite, yWhite⟩
  | succ t ih =>
    let current := colorAfter adj blue t
    have blocked (a b : V) (ab : a ≠ b) (pair : TwinOutsidePair adj a b)
        (ha : a ∉ current) (hb : b ∉ current) : a ∉ synchronousStep adj current := by
      intro h
      rcases (mem_synchronousStep adj current a).mp h with inBlue | ⟨v, hv, edge, unique⟩
      · exact ha inBlue
      · have va : v ≠ a := fun e => ha (e ▸ hv)
        have vb : v ≠ b := fun e => hb (e ▸ hv)
        have otherEdge : adj v b := symm ((pair v va vb).mp (symm edge))
        exact ab (unique b otherEdge hb).symm
    refine ⟨blocked x y distinct twins ih.1 ih.2, blocked y x distinct.symm ?_ ih.2 ih.1⟩
    intro v vy vx
    exact (twins v vx vy).symm

end FaultObservationResearch

#print axioms FaultObservationResearch.twin_truncation_colorAfter
#print axioms FaultObservationResearch.twin_truncation_finishesBy
#print axioms FaultObservationResearch.twin_pair_stays_white
