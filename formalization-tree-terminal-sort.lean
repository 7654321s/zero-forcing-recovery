module

/- Enumerate terminal cut components in increasing path length. -/
public import «formalization-tree-two-center-obstruction»
public import «formalization-terminal-arm-general-split»
public import Mathlib.Data.Fin.Tuple.Sort

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
open SimpleGraph SimpleGraph.Walk
universe u
variable {V : Type u}

abbrev TerminalOffComponent (G : SimpleGraph V) (root other : V) (hne : root ≠ other) :=
  {C : (treeCutGraph G root).ConnectedComponent |
    (⟨other, hne.symm⟩ : TreeCutVertex root) ∉ C.supp}

structure SortedTerminalArms (G : SimpleGraph V) (root other : V) (hne : root ≠ other) where
  extra : ℕ
  index : Fin (extra + 2) ≃ TerminalOffComponent G root other hne
  monotone : Monotone (fun i => Nat.card (index i).val)
  positive : ∀ i, 1 ≤ Nat.card (index i).val
  paths : ∀ i, RootedTreeCutPath G root (index i).val

def sortedArmLengths (G : SimpleGraph V) (root other : V) (hne : root ≠ other)
    (A : SortedTerminalArms G root other hne) (i : Fin (A.extra + 2)) : ℕ :=
  Nat.card (A.index i).val

theorem finite_sorted_terminal_arms [Fintype V] (G : SimpleGraph V) (hG : G.IsTree)
    (root other : V) (hne : root ≠ other) (hbranch : TreeBranchVertex G root)
    (hpaths : ∀ C : (treeCutGraph G root).ConnectedComponent,
      (⟨other, hne.symm⟩ : TreeCutVertex root) ∉ C.supp → RootedTreeCutPath G root C) :
    Nonempty (SortedTerminalArms G root other hne) := by
  classical
  let O := TerminalOffComponent G root other hne
  let : Fintype O := Fintype.ofFinite O
  obtain ⟨C, D, hCD, hC, hD⟩ := branch_vertex_two_off_components G hG root other hne hbranch
  let c : O := ⟨C, hC⟩
  let d : O := ⟨D, hD⟩
  have hcd : c ≠ d := fun h => hCD (congrArg Subtype.val h)
  have hcard : 2 ≤ Fintype.card O := by
    have hp := Finset.card_pair_eq_two_iff.mpr hcd
    have hb := Finset.card_le_univ ({c, d} : Finset O)
    omega
  let k := Fintype.card O - 2
  have hk : Fintype.card O = k + 2 := by omega
  let e : Fin (k + 2) ≃ O := (Fintype.equivFinOfCardEq hk).symm
  let f : Fin (k + 2) → ℕ := fun i => Nat.card (e i).val
  let e' := (Tuple.sort f).trans e
  refine ⟨⟨k, e', Tuple.monotone_sort f, ?_, ?_⟩⟩
  · intro i
    let E := (e' i).val
    obtain ⟨x, hx⟩ := E.nonempty_supp
    have : Nonempty E := ⟨⟨x, hx⟩⟩
    exact Nat.card_pos
  · intro i
    exact hpaths (e' i).val (e' i).property

def sortedArmsPair (G : SimpleGraph V) (root other : V) (hne : root ≠ other)
    (A : SortedTerminalArms G root other hne) (i j : Fin (A.extra + 2)) (hij : i ≠ j) :
    TerminalTreeCutPair G root other hne where
  first := (A.index i).val
  second := (A.index j).val
  distinct := fun h => hij (A.index.injective (Subtype.ext h))
  first_off := (A.index i).property
  second_off := (A.index j).property
  first_path := A.paths i
  second_path := A.paths j

def sortedLongestPair (G : SimpleGraph V) (root other : V) (hne : root ≠ other)
    (A : SortedTerminalArms G root other hne) : TerminalTreeCutPair G root other hne :=
  sortedArmsPair G root other hne A (Fin.last (A.extra + 1)) (armPenultimateIndex A.extra)
    (by intro h; have := congrArg Fin.val h; dsimp [armPenultimateIndex] at this; omega)

def sortedShortestPair (G : SimpleGraph V) (root other : V) (hne : root ≠ other)
    (A : SortedTerminalArms G root other hne) : TerminalTreeCutPair G root other hne :=
  sortedArmsPair G root other hne A (armFirstIndex A.extra) (armSecondIndex A.extra)
    (by intro h; have hval := congrArg Fin.val h; change (0 : ℕ) = 1 at hval; omega)

theorem sorted_shortest_pair_max (G : SimpleGraph V) (root other : V) (hne : root ≠ other)
    (A : SortedTerminalArms G root other hne) :
    max (Nat.card (sortedShortestPair G root other hne A).first)
      (Nat.card (sortedShortestPair G root other hne A).second) =
      terminalArmSecond A.extra (sortedArmLengths G root other hne A) := by
  apply max_eq_right
  exact A.monotone (by change (0 : ℕ) ≤ 1; omega)

theorem singleton_cut_component_leaf (G : SimpleGraph V) (root : V)
    (C : (treeCutGraph G root).ConnectedComponent) (hcard : Nat.card C = 1)
    (a : C) (ha : G.Adj root a.val.val) : TreeLeaf G a.val.val := by
  have hsub := (Nat.card_eq_one_iff_unique.mp hcard).1
  refine ⟨root, ha.symm, ?_⟩
  intro y hy
  by_contra hne
  have hyC := tree_cut_component_adj_mem G root C a ⟨y, hne⟩ hy
  have heq : (⟨⟨y, hne⟩, hyC⟩ : C) = a := hsub.elim _ _
  have hya : y = a.val.val := congrArg (fun z : C => z.val.val) heq
  exact G.loopless.irrefl _ (hya ▸ hy)

theorem terminal_pair_unit_lengths_cherry (G : SimpleGraph V) (hG : G.IsTree)
    (root other : V) (hne : root ≠ other) (P : TerminalTreeCutPair G root other hne)
    (hfirst : Nat.card P.first = 1) (hsecond : Nat.card P.second = 1) :
    TreeLeafPairCenter G root := by
  obtain ⟨a, ha⟩ := connected_cut_component_has_neighbor G hG.connected root P.first
  obtain ⟨b, hb⟩ := connected_cut_component_has_neighbor G hG.connected root P.second
  refine ⟨a.val.val, b.val.val, ?_, ha.symm,
    singleton_cut_component_leaf G root P.first hfirst a ha, hb.symm,
    singleton_cut_component_leaf G root P.second hsecond b hb⟩
  intro heq
  exact P.distinct (cut_component_point_eq_component G root P.first P.second a b heq)

end FaultObservationResearch
