module

/-
A terminal-only arm delays the start of a different initially empty arm.
These speed bounds are ingredients for the remaining one-short-arm witness.
-/
public import «formalization-path-star-two-empty»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

theorem pathStar_coupled_arm_speed (L : I → ℕ) (a j : I) (haj : a ≠ j)
    (hapos : 0 < L a) (hjpos : 0 < L j) (C : Finset (PathStarVertex I L))
    (ha : ∀ k : Fin (L a), (some ⟨a, k⟩ : PathStarVertex I L) ∈ C → L a ≤ k.val + 1)
    (hj : ∀ k : Fin (L j), (some ⟨j, k⟩ : PathStarVertex I L) ∉ C) (t : ℕ) :
    (∀ k : Fin (L a), some ⟨a, k⟩ ∈ colorAfter (pathStarGraph L).Adj C t →
      L a ≤ k.val + t + 1) ∧
    (∀ k : Fin (L j), some ⟨j, k⟩ ∈ colorAfter (pathStarGraph L).Adj C t →
      L a + k.val ≤ t) := by
  classical
  let G := pathStarGraph L
  induction t with
  | zero =>
    constructor
    · intro k hk
      exact ha k hk
    · intro k hk
      exact False.elim (hj k hk)
  | succ t ih =>
    constructor
    · intro k hk
      rcases (mem_synchronousStep G.Adj (colorAfter G.Adj C t) _).mp hk with
        hold | ⟨source, hs, hadj, hu⟩
      · have h := ih.1 k hold
        omega
      · cases source with
        | none =>
          by_contra hbound
          let other : Fin (L j) := ⟨0, hjpos⟩
          have hwhite : (some ⟨j, other⟩ : PathStarVertex I L) ∉ colorAfter G.Adj C t := by
            intro hblue
            have h := ih.2 other hblue
            change L a + 0 ≤ t at h
            omega
          have hn : G.Adj none (some ⟨j, other⟩) := by
            change other.val = 0
            rfl
          have heq := hu (some ⟨j, other⟩) hn hwhite
          exact haj (pathStar_nodes_eq_arm L j a other k heq).symm
        | some source =>
          obtain ⟨m, l⟩ := source
          change m = a ∧ (l.val + 1 = k.val ∨ k.val + 1 = l.val) at hadj
          obtain ⟨rfl, hleft | hright⟩ := hadj
          · have h := ih.1 l hs
            omega
          · have h := ih.1 l hs
            omega
    · intro k hk
      rcases (mem_synchronousStep G.Adj (colorAfter G.Adj C t) _).mp hk with
        hold | ⟨source, hs, hadj, hu⟩
      · have h := ih.2 k hold
        omega
      · cases source with
        | none =>
          change k.val = 0 at hadj
          let other : Fin (L a) := ⟨0, hapos⟩
          have hn : G.Adj none (some ⟨a, other⟩) := by
            change other.val = 0
            rfl
          have hblue : some ⟨a, other⟩ ∈ colorAfter G.Adj C t := by
            by_contra hwhite
            have heq := hu (some ⟨a, other⟩) hn hwhite
            exact haj (pathStar_nodes_eq_arm L a j other k heq)
          have h := ih.1 other hblue
          change L a ≤ 0 + t + 1 at h
          omega
        | some source =>
          obtain ⟨m, l⟩ := source
          change m = j ∧ (l.val + 1 = k.val ∨ k.val + 1 = l.val) at hadj
          obtain ⟨rfl, hleft | hright⟩ := hadj
          · have h := ih.2 l hs
            omega
          · have h := ih.2 l hs
            omega

theorem pathStar_terminal_empty_completion_lower (L : I → ℕ) (a j : I) (haj : a ≠ j)
    (hapos : 0 < L a) (hjpos : 0 < L j) (C : Finset (PathStarVertex I L))
    (ha : ∀ k : Fin (L a), (some ⟨a, k⟩ : PathStarVertex I L) ∈ C → L a ≤ k.val + 1)
    (hj : ∀ k : Fin (L j), (some ⟨j, k⟩ : PathStarVertex I L) ∉ C)
    (t : ℕ) (hfinish : FinishesBy (pathStarGraph L).Adj C t) : L a + L j ≤ t + 1 := by
  let last : Fin (L j) := ⟨L j - 1, by omega⟩
  have hblue : some ⟨j, last⟩ ∈ colorAfter (pathStarGraph L).Adj C t := by
    rw [hfinish]
    exact Finset.mem_univ _
  have h := (pathStar_coupled_arm_speed L a j haj hapos hjpos C ha hj t).2 last hblue
  change L a + (L j - 1) ≤ t at h
  omega

theorem pathStar_terminal_empty_not_finishes_at_arm_length
    (L : I → ℕ) (a j : I) (haj : a ≠ j) (hapos : 0 < L a) (hjlong : 2 ≤ L j)
    (C : Finset (PathStarVertex I L))
    (ha : ∀ k : Fin (L a), (some ⟨a, k⟩ : PathStarVertex I L) ∈ C → L a ≤ k.val + 1)
    (hj : ∀ k : Fin (L j), (some ⟨j, k⟩ : PathStarVertex I L) ∉ C) :
    ¬ FinishesBy (pathStarGraph L).Adj C (L a) := by
  intro hfinish
  have h := pathStar_terminal_empty_completion_lower L a j haj hapos (by omega) C ha hj (L a) hfinish
  omega

end FaultObservationResearch
