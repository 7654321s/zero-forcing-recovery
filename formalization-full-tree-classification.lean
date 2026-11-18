module

/- Full finite-tree classification, assembled from the original-graph obstructions. -/
public import «formalization-tree-adjacent-core»
public import «formalization-single-branch-one-short»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
open SimpleGraph SimpleGraph.Walk
universe u
variable {V : Type u}

theorem sorted_cherry_free_support_impossible [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsTree) (hU : EveryMinimumSupport G.Adj)
    (hnocherry : ∀ c, ¬ TreeLeafPairCenter G c) (a b : V) (hab : a ≠ b)
    (A : SortedTerminalArms G a b hab) (B : SortedTerminalArms G b a hab.symm) : False := by
  obtain ⟨ha, hb, haone, hbone, heq, hpos⟩ :=
    sorted_terminal_cherry_free_shape G hG hU hnocherry a b hab A B
  have hadj := sorted_cherry_free_support_centers_adjacent G hG hU hnocherry a b hab A B
  obtain ⟨hAl, hAs⟩ := sorted_longest_two_lengths G a b hab A ha
  obtain ⟨hBl, hBs⟩ := sorted_longest_two_lengths G b a hab.symm B hb
  obtain ⟨m, n, k, l, ⟨e⟩, hm, hn, hk, hl⟩ :=
    sorted_adjacent_canonical_realization G hG a b hab A B ha hb hadj
  have hnzero : n = 0 := by omega
  have hlzero : l = 0 := by omega
  have hkm : k = m := by omega
  have hmpos : 1 ≤ m := by omega
  subst n
  subst l
  subst k
  let r := m - 1
  have hmshape : m = r + 1 := by omega
  have hmodel := (EveryMinimumSupport_iso_iff _ G e).mpr hU
  rw [hmshape] at hmodel
  exact adjacentEqual_not_support r hmodel

theorem finite_cherry_free_multi_branch_not_support [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsTree) (hnocherry : ∀ c, ¬ TreeLeafPairCenter G c)
    (hexists : ∃ a b, TreeBranchVertex G a ∧ TreeBranchVertex G b ∧ a ≠ b) :
    ¬ EveryMinimumSupport G.Adj := by
  intro hU
  obtain ⟨a, b, hab, A, B, _⟩ :=
    finite_cherry_free_support_terminal_reduction G hG hU hnocherry hexists
  exact sorted_cherry_free_support_impossible G hG hU hnocherry a b hab A B

theorem finite_tree_everyMinimumSupport_classification [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsTree) : EveryMinimumSupport G.Adj ↔ InTreeCandidateClass G := by
  classical
  constructor
  · intro hU
    by_cases hatmost : ∀ x y, TreeBranchVertex G x → TreeBranchVertex G y → x = y
    · exact (finite_at_most_one_branch_tree_classification G hG hatmost).mp hU
    · have hexists : ∃ a b, TreeBranchVertex G a ∧ TreeBranchVertex G b ∧ a ≠ b := by
        by_contra hno
        apply hatmost
        intro a b ha hb
        by_contra hab
        exact hno ⟨a, b, ha, hb, hab⟩
      by_cases hcherry : ∃ c, TreeLeafPairCenter G c
      · exact Or.inr ((tree_cherry_support_iff_star_or_double_star G hG hcherry).mp hU)
      · exact False.elim (finite_cherry_free_multi_branch_not_support G hG
          (fun c hc => hcherry ⟨c, hc⟩) hexists hU)
  · exact candidateClass_every_minimum_support G

theorem full_tree_classification_statement : FullTreeClassificationStatement.{u} := by
  intro V instF instD instN G hG
  exact finite_tree_everyMinimumSupport_classification G hG

end FaultObservationResearch
