module

/-
Propagation upper bounds after the center and arm heads have become blue.
These local process lemmas are ingredients, not the full all-long-arm obstruction.
-/
public import «formalization-single-branch-realization»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

theorem pathStar_arm_prefix_blue (lengths : I → ℕ) (i : I)
    (C : Finset (PathStarVertex I lengths)) (hcenter : none ∈ C)
    (hhead : ∀ k : Fin (lengths i), k.val = 0 → some ⟨i, k⟩ ∈ C)
    (t : ℕ) : ∀ k : Fin (lengths i), k.val ≤ t →
      some ⟨i, k⟩ ∈ colorAfter (pathStarGraph lengths).Adj C t := by
  classical
  let G := pathStarGraph lengths
  induction t with
  | zero =>
    intro k hk
    exact hhead k (by omega)
  | succ t ih =>
    intro k hk
    by_cases hold : k.val ≤ t
    · exact colorAfter_subset_succ G.Adj C t (ih k hold)
    · have hkval : k.val = t + 1 := by omega
      let previous : Fin (lengths i) := ⟨t, by have h := k.isLt; omega⟩
      apply (mem_synchronousStep G.Adj (colorAfter G.Adj C t) _).mpr
      refine Or.inr ⟨some ⟨i, previous⟩, ih previous le_rfl, ?_, ?_⟩
      · change i = i ∧ (previous.val + 1 = k.val ∨ k.val + 1 = previous.val)
        exact ⟨rfl, Or.inl hkval.symm⟩
      · intro other hadj hwhite
        cases other with
        | none =>
          exact False.elim (hwhite (colorAfter_mono_time G.Adj C (Nat.zero_le t) hcenter))
        | some other =>
          obtain ⟨j, l⟩ := other
          change i = j ∧ (previous.val + 1 = l.val ∨ l.val + 1 = previous.val) at hadj
          obtain ⟨rfl, hleft | hright⟩ := hadj
          · have hl : l = k := Fin.ext (by change t + 1 = l.val at hleft; omega)
            exact congrArg (fun z : Fin (lengths i) =>
              (some ⟨i, z⟩ : PathStarVertex I lengths)) hl
          · have hl : l.val ≤ t := by change l.val + 1 = t at hright; omega
            exact False.elim (hwhite (ih l hl))

theorem pathStar_arm_after_center_head (lengths : I → ℕ) (i : I)
    (C : Finset (PathStarVertex I lengths)) (s t : ℕ)
    (hcenter : none ∈ colorAfter (pathStarGraph lengths).Adj C s)
    (hhead : ∀ k : Fin (lengths i), k.val = 0 →
      some ⟨i, k⟩ ∈ colorAfter (pathStarGraph lengths).Adj C s)
    (k : Fin (lengths i)) (hdeadline : s + k.val ≤ t) :
    some ⟨i, k⟩ ∈ colorAfter (pathStarGraph lengths).Adj C t := by
  have h := pathStar_arm_prefix_blue lengths i
    (colorAfter (pathStarGraph lengths).Adj C s) hcenter hhead k.val k le_rfl
  rw [← colorAfter_add] at h
  exact colorAfter_mono_time _ C hdeadline h

theorem pathStar_finishes_after_center_heads (lengths : I → ℕ)
    (C : Finset (PathStarVertex I lengths)) (s t : ℕ) (hst : s ≤ t)
    (hcenter : none ∈ colorAfter (pathStarGraph lengths).Adj C s)
    (hheads : ∀ (i : I) (k : Fin (lengths i)), k.val = 0 →
      some ⟨i, k⟩ ∈ colorAfter (pathStarGraph lengths).Adj C s)
    (hdeadline : ∀ i, s + lengths i ≤ t + 1) :
    FinishesBy (pathStarGraph lengths).Adj C t := by
  classical
  apply Finset.eq_univ_of_forall
  intro vertex
  cases vertex with
  | none => exact colorAfter_mono_time _ C hst hcenter
  | some vertex =>
    obtain ⟨i, k⟩ := vertex
    apply pathStar_arm_after_center_head lengths i C s t hcenter (hheads i) k
    have h := hdeadline i
    have hk := k.isLt
    omega

end FaultObservationResearch
