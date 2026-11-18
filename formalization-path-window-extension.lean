module

/-
Finite ordered interval extension and a white-count comparison.
These are components for the pending arbitrary-blue-set path time theorem.
-/
public import «formalization-path-interval-upper»
public import «formalization-path-gap-one-sided»
public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace FaultObservationResearch

def PathRangeHits (n : ℕ) (support : Finset (Fin (n + 1))) (low high : ℕ) :
    Finset (Fin (n + 1)) := support.filter (fun x => low ≤ x.val ∧ x.val ≤ high)

theorem path_range_extend_to_budget (n : ℕ) (support : Finset (Fin (n + 1)))
    (budget low high : ℕ) (hlh : low ≤ high) (hhn : high ≤ n)
    (hsmall : (PathRangeHits n support low high).card ≤ budget)
    (hbudget : budget < support.card) :
    ∃ a b : ℕ, a ≤ low ∧ high ≤ b ∧ b ≤ n ∧
      (PathRangeHits n support a b).card = budget ∧ (0 < a ∨ b < n) := by
  classical
  have general : ∀ m : ℕ, ∀ l h : ℕ, l + (n - h) = m → l ≤ h → h ≤ n →
      (PathRangeHits n support l h).card ≤ budget →
      ∃ a b : ℕ, a ≤ l ∧ h ≤ b ∧ b ≤ n ∧
        (PathRangeHits n support a b).card = budget ∧ (0 < a ∨ b < n) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro l h hmeasure hlh hhn hcount
      by_cases heq : (PathRangeHits n support l h).card = budget
      · refine ⟨l, h, le_rfl, le_rfl, hhn, heq, ?_⟩
        by_cases hl : 0 < l
        · exact Or.inl hl
        · right
          by_contra hh
          have hl0 : l = 0 := by omega
          have hhnEq : h = n := by omega
          have hfull : PathRangeHits n support l h = support := by
            ext x
            simp only [PathRangeHits, Finset.mem_filter]
            have hx := x.isLt
            constructor
            · exact fun h => h.1
            · exact fun h => ⟨h, by omega, by omega⟩
          rw [hfull] at heq
          omega
      · have hlt : (PathRangeHits n support l h).card < budget := by omega
        by_cases hl : 0 < l
        · let p : Fin (n + 1) := ⟨l - 1, by omega⟩
          have hsub : PathRangeHits n support (l - 1) h ⊆
              insert p (PathRangeHits n support l h) := by
            intro x hx
            have hi := Finset.mem_filter.mp hx
            by_cases hp : x.val = l - 1
            · exact Finset.mem_insert.mpr (Or.inl (Fin.ext hp))
            · exact Finset.mem_insert.mpr (Or.inr
                (Finset.mem_filter.mpr ⟨hi.1, by omega, hi.2.2⟩))
          have hle := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
          have hnew : (PathRangeHits n support (l - 1) h).card ≤ budget := by omega
          obtain ⟨a, b, ha, hb, hbn, hc, hedge⟩ :=
            ih ((l - 1) + (n - h)) (by omega) (l - 1) h rfl (by omega) hhn hnew
          exact ⟨a, b, by omega, hb, hbn, hc, hedge⟩
        · have hl0 : l = 0 := by omega
          have hh : h < n := by
            by_contra hh
            have hhnEq : h = n := by omega
            have hfull : PathRangeHits n support l h = support := by
              ext x
              simp only [PathRangeHits, Finset.mem_filter]
              have hx := x.isLt
              constructor
              · exact fun h => h.1
              · exact fun h => ⟨h, by omega, by omega⟩
            rw [hfull] at hcount
            omega
          let p : Fin (n + 1) := ⟨h + 1, by omega⟩
          have hsub : PathRangeHits n support l (h + 1) ⊆
              insert p (PathRangeHits n support l h) := by
            intro x hx
            have hi := Finset.mem_filter.mp hx
            by_cases hp : x.val = h + 1
            · exact Finset.mem_insert.mpr (Or.inl (Fin.ext hp))
            · exact Finset.mem_insert.mpr (Or.inr
                (Finset.mem_filter.mpr ⟨hi.1, hi.2.1, by omega⟩))
          have hle := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
          have hnew : (PathRangeHits n support l (h + 1)).card ≤ budget := by omega
          obtain ⟨a, b, ha, hb, hbn, hc, hedge⟩ :=
            ih (l + (n - (h + 1))) (by omega) l (h + 1) rfl (by omega) (by omega) hnew
          exact ⟨a, b, ha, by omega, hbn, hc, hedge⟩
  exact general _ low high rfl hlh hhn hsmall

theorem path_white_interval_card (n : ℕ) (blue support : Finset (Fin (n + 1)))
    (hsub : support ⊆ blue) (low high : ℕ) :
    (PathWhiteInterval n blue support low high).card =
      (Finset.univ.filter (fun x : Fin (n + 1) => low ≤ x.val ∧ x.val ≤ high ∧ x ∉ blue)).card +
        (PathRangeHits n support low high).card := by
  classical
  let W := Finset.univ.filter (fun x : Fin (n + 1) => low ≤ x.val ∧ x.val ≤ high ∧ x ∉ blue)
  have heq : PathWhiteInterval n blue support low high = W ∪ PathRangeHits n support low high := by
    ext x
    simp only [PathWhiteInterval, PathRangeHits, W, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_union]
    aesop
  have hdis : Disjoint W (PathRangeHits n support low high) := by
    apply Finset.disjoint_left.mpr
    intro x hxW hxS
    exact (Finset.mem_filter.mp hxW).2.2.2 (hsub (Finset.mem_filter.mp hxS).1)
  exact heq ▸ Finset.card_union_of_disjoint hdis

theorem path_loss_interval_card_le_support_window (n : ℕ)
    (blue support loss : Finset (Fin (n + 1))) (hsub : support ⊆ blue)
    (left right : Fin (n + 1)) (low high budget : ℕ)
    (hleft : low ≤ left.val) (hright : right.val ≤ high)
    (hloss : loss.card ≤ budget)
    (hcard : (PathRangeHits n support low high).card = budget) :
    (PathIntervalWhites n (blue \ loss) left right).card ≤
      (PathWhiteInterval n blue support low high).card := by
  classical
  let W := Finset.univ.filter (fun x : Fin (n + 1) => low ≤ x.val ∧ x.val ≤ high ∧ x ∉ blue)
  have hinc : PathIntervalWhites n (blue \ loss) left right ⊆ W ∪ loss := by
    intro x hx
    have hi := (Finset.mem_filter.mp hx).2
    by_cases hxB : x ∈ blue
    · have hxD : x ∈ loss := by
        by_contra hnot
        exact hi.2.2 (Finset.mem_sdiff.mpr ⟨hxB, hnot⟩)
      exact Finset.mem_union_right _ hxD
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, by omega, by omega, hxB⟩)
  have hle := (Finset.card_le_card hinc).trans (Finset.card_union_le W loss)
  rw [path_white_interval_card n blue support hsub low high, hcard]
  change _ ≤ W.card + budget
  omega

end FaultObservationResearch
