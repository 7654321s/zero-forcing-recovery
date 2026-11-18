module

public import SubdivisionProjection
public import CertificateDeadline

@[expose] public section

set_option autoImplicit false

namespace FaultObservationResearch

universe u v

variable {V : Type u} {W : Type v}
variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

def coreEmbedding : V ↪ V ⊕ W :=
  ⟨Sum.inl, fun _ _ h => Sum.inl.inj h⟩

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
@[simp] theorem coreEmbedding_apply (x : V) :
    coreEmbedding (W := W) x = Sum.inl x := rfl

omit [Fintype V] in
private theorem remove_core_colors (blue loss : Finset V) :
    (blue.disjSum (Finset.univ : Finset W)) \ loss.map coreEmbedding =
      (blue \ loss).disjSum Finset.univ := by
  ext z
  cases z with
  | inl z => simp [Finset.mem_sdiff]
  | inr z => simp

/-- Subdivision transports a full budget-one witness, with exactly the
same deadline. The endpoint exclusions protect every compared coloring.
The last hypothesis concerns only losses of inserted vertices. -/
theorem subdivision_preserves_budgetOnePairWitness
    (old : V → V → Prop) (new : W → W → Prop) (x y : V) (first last : W)
    (blue support : Finset V) (slow : V) (deadline : ℕ)
    (witness : BudgetOnePairWitness old blue support slow deadline)
    (hx : x ∈ blue) (hy : y ∈ blue)
    (xOutside : x ∉ support) (yOutside : y ∉ support) (xs : x ≠ slow) (ys : y ≠ slow)
    (repairNew : ∀ q : W, Sum.inr q ∈ synchronousStep
      (subdivideAdj old new x y first last) (blue.disjSum Finset.univ \ {Sum.inr q})) :
    BudgetOnePairWitness (subdivideAdj old new x y first last)
      (blue.disjSum Finset.univ) (support.map coreEmbedding) (.inl slow) deadline := by
  let adj := subdivideAdj old new x y first last
  let large := blue.disjSum (Finset.univ : Finset W)
  have hExact (start : Finset V) (xBlue : x ∈ start) (yBlue : y ∈ start) (t : ℕ) :
      FinishesBy adj (start.disjSum Finset.univ) t ↔ FinishesBy old start t :=
    subdivide_finishesBy_iff old new x y first last start _
      (fun _ => Finset.inl_mem_disjSum) xBlue yBlue (fun _ => by simp) t
  have hForcing (start : Finset V) (xBlue : x ∈ start) (yBlue : y ∈ start) :
      IsForcing adj (start.disjSum Finset.univ) ↔ IsForcing old start := by
    unfold IsForcing
    exact exists_congr (hExact start xBlue yBlue)
  have hIntactAndSingles := (robustBy_one_iff old blue support deadline).mp
    witness.restrictedFinishes
  have hIntact : IsForcing adj large :=
    ⟨deadline, (hExact blue hx hy deadline).mpr hIntactAndSingles.1⟩
  have hLoss (z : V) : large \ {Sum.inl z} = (blue \ {z}).disjSum Finset.univ := by
    simpa using (remove_core_colors (W := W) blue {z})
  have hRepair (missing : V ⊕ W) (back : missing ∈ synchronousStep adj (large \ {missing})) :
      IsForcing adj (large \ {missing}) := by
    have hIncluded : large ⊆ colorAfter adj (large \ {missing}) 1 := by
      intro q hq
      by_cases same : q = missing
      · exact same.symm ▸ back
      · exact subset_synchronousStep adj _ (Finset.mem_sdiff.mpr ⟨hq, by simpa using same⟩)
    obtain ⟨t, ht⟩ := IsForcing_mono adj hIncluded hIntact
    exact ⟨1 + t, by simpa only [FinishesBy, colorAfter_add] using ht⟩
  refine ⟨by simpa using witness.pair, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hq
    exact Finset.inl_mem_disjSum.mpr (witness.supportBlue ha)
  · rw [remove_core_colors]
    exact fun h => witness.doubleFails
      ((hForcing (blue \ support) (Finset.mem_sdiff.mpr ⟨hx, xOutside⟩)
        (Finset.mem_sdiff.mpr ⟨hy, yOutside⟩)).mp h)
  · intro q hq
    cases q with
    | inr q => exact hRepair _ (repairNew q)
    | inl b =>
      have hOld : b ∈ blue := Finset.inl_mem_disjSum.mp hq
      by_cases hEnd : b = x ∨ b = y
      · apply hRepair
        refine subdivide_restore_endpoint old new x y first last _ b hEnd ?_ ?_
        · intro a ha hNe
          apply Finset.mem_sdiff.mpr
          exact ⟨Finset.inl_mem_disjSum.mpr (ha.elim (fun h => h.symm ▸ hx)
            (fun h => h.symm ▸ hy)), by simpa using hNe⟩
        · intro a
          simp [large]
      · rw [hLoss]
        exact (hForcing (blue \ {b}) (Finset.mem_sdiff.mpr ⟨hx, by simpa using
            (fun he : x = b => hEnd (Or.inl he.symm))⟩)
          (Finset.mem_sdiff.mpr ⟨hy, by simpa using
            (fun he : y = b => hEnd (Or.inr he.symm))⟩)).mpr (witness.singletonFinishes b hOld)
  · apply (robustBy_one_iff adj large (support.map coreEmbedding) deadline).mpr
    refine ⟨(hExact blue hx hy deadline).mpr hIntactAndSingles.1, ?_⟩
    intro q hq
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hq
    change FinishesBy adj (large \ {Sum.inl b}) deadline
    rw [hLoss]
    have hNotX : x ≠ b := fun h => xOutside (h.symm ▸ hb)
    have hNotY : y ≠ b := fun h => yOutside (h.symm ▸ hb)
    exact (hExact (blue \ {b}) (Finset.mem_sdiff.mpr ⟨hx, by simpa using hNotX⟩)
      (Finset.mem_sdiff.mpr ⟨hy, by simpa using hNotY⟩) deadline).mpr
      (hIntactAndSingles.2 b hb)
  · exact Finset.inl_mem_disjSum.mpr witness.slowBlue
  · change ¬ FinishesBy adj (large \ {Sum.inl slow}) deadline
    rw [hLoss]
    exact fun h => witness.slowMisses
      ((hExact (blue \ {slow}) (Finset.mem_sdiff.mpr ⟨hx, by simpa using xs⟩)
        (Finset.mem_sdiff.mpr ⟨hy, by simpa using ys⟩) deadline).mp h)

end FaultObservationResearch

#print axioms FaultObservationResearch.subdivision_preserves_budgetOnePairWitness
