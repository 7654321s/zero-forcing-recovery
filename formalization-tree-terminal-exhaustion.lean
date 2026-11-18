module

/- Transfer the sorted arithmetic split to original-tree terminal structures. -/
public import «formalization-tree-terminal-sort»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
open SimpleGraph SimpleGraph.Walk
universe u
variable {V : Type u}

theorem sorted_terminal_strict_not_support [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsTree) (a b : V) (hab : a ≠ b)
    (A : SortedTerminalArms G a b hab) (B : SortedTerminalArms G b a hab.symm)
    (hstrict : terminalArmSecond B.extra (sortedArmLengths G b a hab.symm B) <
      terminalArmSum A.extra (sortedArmLengths G a b hab A)) : ¬ EveryMinimumSupport G.Adj := by
  apply terminal_pairs_strict_not_support G hG b a hab.symm
    (sortedShortestPair G b a hab.symm B) (sortedLongestPair G a b hab A)
  rw [sorted_shortest_pair_max]
  change terminalArmSecond B.extra (sortedArmLengths G b a hab.symm B) + 1 <
    sortedArmLengths G a b hab A (Fin.last (A.extra + 1)) +
      sortedArmLengths G a b hab A (armPenultimateIndex A.extra)
  dsimp [terminalArmSum] at hstrict
  omega

theorem sorted_terminal_cherry_free_shape [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsTree) (hU : EveryMinimumSupport G.Adj)
    (hnocherry : ∀ c, ¬ TreeLeafPairCenter G c) (a b : V) (hab : a ≠ b)
    (A : SortedTerminalArms G a b hab) (B : SortedTerminalArms G b a hab.symm) :
    A.extra = 0 ∧ B.extra = 0 ∧
      sortedArmLengths G a b hab A (armFirstIndex A.extra) = 1 ∧
      sortedArmLengths G b a hab.symm B (armFirstIndex B.extra) = 1 ∧
      terminalArmSecond A.extra (sortedArmLengths G a b hab A) =
        terminalArmSecond B.extra (sortedArmLengths G b a hab.symm B) ∧
      2 ≤ terminalArmSecond A.extra (sortedArmLengths G a b hab A) := by
  rcases terminal_arm_all_positive_cases A.extra B.extra
    (sortedArmLengths G a b hab A) (sortedArmLengths G b a hab.symm B)
    A.monotone B.monotone A.positive B.positive with hleft | hright | hones | hmatching
  · exact False.elim (sorted_terminal_strict_not_support G hG a b hab A B hleft hU)
  · exact False.elim (sorted_terminal_strict_not_support G hG b a hab.symm B A hright hU)
  · apply False.elim
    apply hnocherry a
    apply terminal_pair_unit_lengths_cherry G hG a b hab (sortedShortestPair G a b hab A)
    · exact hones.1 (armFirstIndex A.extra)
    · exact hones.1 (armSecondIndex A.extra)
  · exact hmatching

theorem sorted_longest_two_lengths (G : SimpleGraph V) (a b : V) (hab : a ≠ b)
    (A : SortedTerminalArms G a b hab) (hextra : A.extra = 0) :
    Nat.card (sortedLongestPair G a b hab A).first =
        terminalArmSecond A.extra (sortedArmLengths G a b hab A) ∧
      Nat.card (sortedLongestPair G a b hab A).second =
        sortedArmLengths G a b hab A (armFirstIndex A.extra) := by
  constructor
  · change sortedArmLengths G a b hab A (Fin.last (A.extra + 1)) =
      sortedArmLengths G a b hab A (armSecondIndex A.extra)
    congr 1
    apply Fin.ext
    change A.extra + 1 = (1 : ℕ)
    omega
  · change sortedArmLengths G a b hab A (armPenultimateIndex A.extra) =
      sortedArmLengths G a b hab A (armFirstIndex A.extra)
    congr 1
    apply Fin.ext
    exact hextra

theorem sorted_cherry_free_support_centers_adjacent [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsTree) (hU : EveryMinimumSupport G.Adj)
    (hnocherry : ∀ c, ¬ TreeLeafPairCenter G c) (a b : V) (hab : a ≠ b)
    (A : SortedTerminalArms G a b hab) (B : SortedTerminalArms G b a hab.symm) : G.Adj a b := by
  obtain ⟨ha, hb, haone, hbone, heq, hpos⟩ :=
    sorted_terminal_cherry_free_shape G hG hU hnocherry a b hab A B
  obtain ⟨hAl, hAs⟩ := sorted_longest_two_lengths G a b hab A ha
  obtain ⟨hBl, hBs⟩ := sorted_longest_two_lengths G b a hab.symm B hb
  let n := terminalArmSecond A.extra (sortedArmLengths G a b hab A) - 1
  have hAn : Nat.card (sortedLongestPair G a b hab A).first = n + 1 := by omega
  have hBn : Nat.card (sortedLongestPair G b a hab.symm B).first = n + 1 := by omega
  have hAone : Nat.card (sortedLongestPair G a b hab A).second = 1 := hAs.trans haone
  have hBone : Nat.card (sortedLongestPair G b a hab.symm B).second = 1 := hBs.trans hbone
  by_contra hnadj
  exact terminal_pairs_equal_nonadjacent_not_support G hG a b hab
    (sortedLongestPair G a b hab A) (sortedLongestPair G b a hab.symm B) n
    hBn hBone hAn hAone hnadj hU

theorem sorted_terminal_off_components_exhausted (G : SimpleGraph V) (a b : V) (hab : a ≠ b)
    (A : SortedTerminalArms G a b hab) (hextra : A.extra = 0)
    (C : (treeCutGraph G a).ConnectedComponent)
    (hoff : (⟨b, hab.symm⟩ : TreeCutVertex a) ∉ C.supp) :
    C = (sortedLongestPair G a b hab A).first ∨ C = (sortedLongestPair G a b hab A).second := by
  obtain ⟨i, hi⟩ := A.index.surjective ⟨C, hoff⟩
  have hival := i.isLt
  have hchoice : i = Fin.last (A.extra + 1) ∨ i = armPenultimateIndex A.extra := by
    by_cases hz : i.val = 0
    · right
      apply Fin.ext
      change i.val = A.extra
      omega
    · left
      apply Fin.ext
      change i.val = A.extra + 1
      omega
  rcases hchoice with rfl | rfl
  · exact Or.inl (congrArg Subtype.val hi).symm
  · exact Or.inr (congrArg Subtype.val hi).symm

theorem sorted_terminal_adjacent_core_root_neighbor [Fintype V]
    (G : SimpleGraph V) (hG : G.IsTree) (a b : V) (hab : a ≠ b)
    (A : SortedTerminalArms G a b hab) (hextra : A.extra = 0) (hadj : G.Adj a b)
    (z : treeComponentRemainderSet G a
      ({(sortedLongestPair G a b hab A).first, (sortedLongestPair G a b hab A).second} : Set _))
    (hz : G.Adj a z.val) : z.val = b := by
  classical
  by_contra hzb
  let zcut : TreeCutVertex a := ⟨z.val, hz.ne'⟩
  let C := (treeCutGraph G a).connectedComponentMk zcut
  have hzC : zcut ∈ C.supp := (C.mem_supp_iff zcut).mpr rfl
  have hoff : (⟨b, hab.symm⟩ : TreeCutVertex a) ∉ C.supp := by
    intro hbC
    have heq := acyclic_cut_neighbors_unique G hG.isAcyclic a zcut ⟨b, hab.symm⟩
      hz hadj (C.reachable_of_mem_supp hzC hbC)
    exact hzb (congrArg Subtype.val heq)
  have hchoice := sorted_terminal_off_components_exhausted G a b hab A hextra C hoff
  apply z.property hz.ne'
  change C ∈ ({(sortedLongestPair G a b hab A).first,
    (sortedLongestPair G a b hab A).second} : Set _)
  rcases hchoice with h | h <;> simp [h]

theorem finite_cherry_free_support_terminal_reduction [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsTree) (hU : EveryMinimumSupport G.Adj)
    (hnocherry : ∀ c, ¬ TreeLeafPairCenter G c)
    (hexists : ∃ a b, TreeBranchVertex G a ∧ TreeBranchVertex G b ∧ a ≠ b) :
    ∃ (a b : V) (hab : a ≠ b) (A : SortedTerminalArms G a b hab)
      (B : SortedTerminalArms G b a hab.symm), G.Adj a b ∧ A.extra = 0 ∧ B.extra = 0 ∧
      sortedArmLengths G a b hab A (armFirstIndex A.extra) = 1 ∧
      sortedArmLengths G b a hab.symm B (armFirstIndex B.extra) = 1 ∧
      terminalArmSecond A.extra (sortedArmLengths G a b hab A) =
        terminalArmSecond B.extra (sortedArmLengths G b a hab.symm B) ∧
      2 ≤ terminalArmSecond A.extra (sortedArmLengths G a b hab A) := by
  classical
  obtain ⟨a, b, hab, _, ha, hb, _, _, hleft, hright⟩ :=
    finite_terminal_branch_path_components G hG hexists
  obtain ⟨A⟩ := finite_sorted_terminal_arms G hG a b hab ha
    (fun C hC => rooted_cut_path_of_positive_length G a C (hleft C hC))
  obtain ⟨B⟩ := finite_sorted_terminal_arms G hG b a hab.symm hb
    (fun C hC => rooted_cut_path_of_positive_length G b C (hright C hC))
  exact ⟨a, b, hab, A, B, sorted_cherry_free_support_centers_adjacent G hG hU hnocherry a b hab A B,
    sorted_terminal_cherry_free_shape G hG hU hnocherry a b hab A B⟩

end FaultObservationResearch
