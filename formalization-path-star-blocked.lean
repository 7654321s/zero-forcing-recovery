module

/-
Static blocking by one blue head on each arm, when every arm has length at least two.
This is an ingredient of the pending minimum-killing witness, not its full proof.
-/
public import «formalization-single-branch-realization»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

def pathStarHeads (lengths : I → ℕ) : Finset (PathStarVertex I lengths) := by
  classical
  exact Finset.univ.filter (fun z => match z with
    | none => False
    | some ⟨_, k⟩ => k.val = 0)

theorem pathStar_heads_fixed (lengths : I → ℕ) (hlong : ∀ i, 2 ≤ lengths i) :
    synchronousStep (pathStarGraph lengths).Adj (pathStarHeads lengths) =
      pathStarHeads lengths := by
  classical
  apply le_antisymm ?_ (subset_synchronousStep _ _)
  intro target ht
  rcases (mem_synchronousStep _ _ _).mp ht with hold | ⟨source, hs, _, hu⟩
  · exact hold
  · cases source with
    | none => simp [pathStarHeads] at hs
    | some source =>
      obtain ⟨i, k⟩ := source
      have hk : k.val = 0 := by simpa [pathStarHeads] using hs
      let second : Fin (lengths i) := ⟨1, by have h := hlong i; omega⟩
      have hcenter : (none : PathStarVertex I lengths) ∉ pathStarHeads lengths := by
        simp [pathStarHeads]
      have hsecond : some ⟨i, second⟩ ∉ pathStarHeads lengths := by
        simp [pathStarHeads, second]
      have hcenteradj : (pathStarGraph lengths).Adj (some ⟨i, k⟩) none := hk
      have hsecondadj : (pathStarGraph lengths).Adj (some ⟨i, k⟩) (some ⟨i, second⟩) := by
        change i = i ∧ (k.val + 1 = second.val ∨ second.val + 1 = k.val)
        exact ⟨rfl, Or.inl (by change k.val + 1 = 1; omega)⟩
      have hbad : (none : PathStarVertex I lengths) = some ⟨i, second⟩ :=
        (hu none hcenteradj hcenter).trans (hu (some ⟨i, second⟩) hsecondadj hsecond).symm
      cases hbad

theorem pathStar_heads_not_forcing (lengths : I → ℕ) (hlong : ∀ i, 2 ≤ lengths i) :
    ¬ IsForcing (pathStarGraph lengths).Adj (pathStarHeads lengths) := by
  classical
  rintro ⟨t, ht⟩
  have hc : (none : PathStarVertex I lengths) ∈
      colorAfter (pathStarGraph lengths).Adj (pathStarHeads lengths) t := by
    rw [ht]
    exact Finset.mem_univ _
  rw [colorAfter_of_fixed _ _ (pathStar_heads_fixed lengths hlong) t] at hc
  simp [pathStarHeads] at hc

end FaultObservationResearch
