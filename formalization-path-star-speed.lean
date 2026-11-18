module

/-
An initially empty arm cannot propagate before its initially white center.
This is a standard speed invariant for the pending all-long-arm obstruction.
It does not by itself establish the obstruction or the full tree classification.
-/
public import «formalization-single-branch-realization»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

theorem pathStar_empty_arm_white_center_speed (lengths : I → ℕ) (i : I)
    (C : Finset (PathStarVertex I lengths)) (hcenter : none ∉ C)
    (harm : ∀ k : Fin (lengths i), some ⟨i, k⟩ ∉ C) (t : ℕ) :
    ∀ k : Fin (lengths i),
      some ⟨i, k⟩ ∈ colorAfter (pathStarGraph lengths).Adj C t → k.val + 2 ≤ t := by
  classical
  let G := pathStarGraph lengths
  induction t with
  | zero =>
    intro k hk
    exact False.elim (harm k hk)
  | succ t ih =>
    intro k hk
    rcases (mem_synchronousStep G.Adj (colorAfter G.Adj C t) _).mp hk with
      hold | ⟨source, hs, ha, _⟩
    · have hb := ih k hold
      omega
    · cases source with
      | none =>
        change k.val = 0 at ha
        have ht : 1 ≤ t := by
          by_contra h
          have ht0 : t = 0 := by omega
          subst t
          exact hcenter hs
        omega
      | some source =>
        obtain ⟨j, l⟩ := source
        change j = i ∧ (l.val + 1 = k.val ∨ k.val + 1 = l.val) at ha
        obtain ⟨rfl, hadj⟩ := ha
        have hb := ih l hs
        rcases hadj with hleft | hright <;> omega

theorem pathStar_empty_arm_white_center_completion_lower (lengths : I → ℕ) (i : I)
    (hpos : 1 ≤ lengths i) (C : Finset (PathStarVertex I lengths))
    (hcenter : none ∉ C) (harm : ∀ k : Fin (lengths i), some ⟨i, k⟩ ∉ C)
    (t : ℕ) (hfinish : FinishesBy (pathStarGraph lengths).Adj C t) :
    lengths i + 1 ≤ t := by
  let last : Fin (lengths i) := ⟨lengths i - 1, by omega⟩
  have hm : some ⟨i, last⟩ ∈ colorAfter (pathStarGraph lengths).Adj C t := by
    rw [hfinish]
    exact Finset.mem_univ _
  have hb := pathStar_empty_arm_white_center_speed lengths i C hcenter harm t last hm
  change lengths i - 1 + 2 ≤ t at hb
  omega

end FaultObservationResearch
