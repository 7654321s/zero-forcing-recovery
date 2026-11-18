module

/-
Original-graph realization of a finite tree with at most one branch vertex
as a star of paths. Standard graph structure, not a new research claim.
Unverified draft until compiler and axiom records are available.
-/
public import «formalization-tree-cut-components»
public import Mathlib.Logic.Equiv.Option
public import Mathlib.Logic.Equiv.Sum

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
open SimpleGraph SimpleGraph.Walk
universe u v
variable {V : Type u} {I : Type v}

abbrev PathStarVertex (I : Type v) (lengths : I → ℕ) := Option (Σ i : I, Fin (lengths i))

def pathStarAdj (lengths : I → ℕ) : PathStarVertex I lengths → PathStarVertex I lengths → Prop
  | none, none => False
  | none, some ⟨_, j⟩ => j.val = 0
  | some ⟨_, j⟩, none => j.val = 0
  | some ⟨i, j⟩, some ⟨k, l⟩ => i = k ∧ (j.val + 1 = l.val ∨ l.val + 1 = j.val)

def pathStarGraph (lengths : I → ℕ) : SimpleGraph (PathStarVertex I lengths) where
  Adj := pathStarAdj lengths
  symm := ⟨by
    rintro (_ | ⟨i, j⟩) (_ | ⟨k, l⟩) <;>
      simp only [pathStarAdj, eq_comm, or_comm] <;> exact id⟩
  loopless := ⟨by
    rintro (_ | ⟨i, j⟩) <;> simp [pathStarAdj]⟩

theorem cut_component_edge_same (G : SimpleGraph V) (root : V)
    (C D : (treeCutGraph G root).ConnectedComponent) (x : C) (y : D)
    (hxy : G.Adj x.val.val y.val.val) : C = D := by
  calc
    C = (treeCutGraph G root).connectedComponentMk x.val :=
      ((C.mem_supp_iff x.val).mp x.property).symm
    _ = (treeCutGraph G root).connectedComponentMk y.val :=
      SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy
    _ = D := (D.mem_supp_iff y.val).mp y.property

theorem tree_cut_root_adj_iff_index_zero (G : SimpleGraph V) (hG : G.IsTree)
    (root : V) (C : (treeCutGraph G root).ConnectedComponent)
    (a : C) (ha : G.Adj root a.val.val) (n : ℕ)
    (e : C.toSimpleGraph ≃g SimpleGraph.pathGraph n) (he : (e a).val = 0) (y : C) :
    G.Adj root y.val.val ↔ (e y).val = 0 := by
  constructor
  · intro hy
    have hya : y = a := Subtype.ext (acyclic_cut_neighbors_unique G hG.isAcyclic root
      y.val a.val hy ha (C.reachable_of_mem_supp y.property a.property))
    simpa only [hya] using he
  · intro hy
    have hya : y = a := e.injective (Fin.ext (hy.trans he.symm))
    simpa only [hya] using ha

def pathStarRealizationEquiv (G : SimpleGraph V) (root : V)
    (lengths : (treeCutGraph G root).ConnectedComponent → ℕ)
    (e : ∀ C : (treeCutGraph G root).ConnectedComponent,
      C.toSimpleGraph ≃g SimpleGraph.pathGraph (lengths C)) :
    PathStarVertex (treeCutGraph G root).ConnectedComponent lengths ≃ V := by
  classical
  let fiber : (Σ C : (treeCutGraph G root).ConnectedComponent, C) ≃ TreeCutVertex root :=
    Equiv.sigmaFiberEquiv (treeCutGraph G root).connectedComponentMk
  let paths : (Σ C : (treeCutGraph G root).ConnectedComponent, Fin (lengths C)) ≃
      (Σ C : (treeCutGraph G root).ConnectedComponent, C) :=
    Equiv.sigmaCongrRight (fun C => (e C).toEquiv.symm)
  exact (Equiv.optionCongr (paths.trans fiber)).trans (Equiv.optionSubtypeNe root)

theorem pathStarRealizationEquiv_adj_iff (G : SimpleGraph V) (hG : G.IsTree) (root : V)
    (a : ∀ C : (treeCutGraph G root).ConnectedComponent, C)
    (ha : ∀ C, G.Adj root (a C).val.val)
    (lengths : (treeCutGraph G root).ConnectedComponent → ℕ)
    (e : ∀ C : (treeCutGraph G root).ConnectedComponent,
      C.toSimpleGraph ≃g SimpleGraph.pathGraph (lengths C))
    (he : ∀ C, (e C (a C)).val = 0)
    (x y : PathStarVertex (treeCutGraph G root).ConnectedComponent lengths) :
    G.Adj (pathStarRealizationEquiv G root lengths e x)
        (pathStarRealizationEquiv G root lengths e y) ↔ pathStarAdj lengths x y := by
  cases x with
  | none =>
    cases y with
    | none =>
      change G.Adj root root ↔ False
      simp
    | some y =>
      obtain ⟨C, j⟩ := y
      change G.Adj root ((e C).symm j).val.val ↔ j.val = 0
      simpa using tree_cut_root_adj_iff_index_zero G hG root C (a C) (ha C)
        (lengths C) (e C) (he C) ((e C).symm j)
  | some x =>
    obtain ⟨C, j⟩ := x
    cases y with
    | none =>
      change G.Adj ((e C).symm j).val.val root ↔ j.val = 0
      rw [G.adj_comm]
      simpa using tree_cut_root_adj_iff_index_zero G hG root C (a C) (ha C)
        (lengths C) (e C) (he C) ((e C).symm j)
    | some y =>
      obtain ⟨D, l⟩ := y
      change G.Adj ((e C).symm j).val.val ((e D).symm l).val.val ↔
        C = D ∧ (j.val + 1 = l.val ∨ l.val + 1 = j.val)
      by_cases hCD : C = D
      · subst D
        change C.toSimpleGraph.Adj ((e C).symm j) ((e C).symm l) ↔
          C = C ∧ (j.val + 1 = l.val ∨ l.val + 1 = j.val)
        simp only [true_and]
        exact (e C).symm.map_adj_iff.trans SimpleGraph.pathGraph_adj
      · constructor
        · intro h
          exact False.elim (hCD (cut_component_edge_same G root C D _ _ h))
        · intro h
          exact False.elim (hCD h.1)

def pathStarRealizationIso (G : SimpleGraph V) (hG : G.IsTree) (root : V)
    (a : ∀ C : (treeCutGraph G root).ConnectedComponent, C)
    (ha : ∀ C, G.Adj root (a C).val.val)
    (lengths : (treeCutGraph G root).ConnectedComponent → ℕ)
    (e : ∀ C : (treeCutGraph G root).ConnectedComponent,
      C.toSimpleGraph ≃g SimpleGraph.pathGraph (lengths C))
    (he : ∀ C, (e C (a C)).val = 0) : pathStarGraph lengths ≃g G where
  toEquiv := pathStarRealizationEquiv G root lengths e
  map_rel_iff' := by
    intro x y
    exact pathStarRealizationEquiv_adj_iff G hG root a ha lengths e he x y

theorem finite_single_branch_path_star_iso [Fintype V]
    (G : SimpleGraph V) (hG : G.IsTree) (root : V)
    (hbranch : ∀ x, x ≠ root → ¬ TreeBranchVertex G x) :
    ∃ lengths : (treeCutGraph G root).ConnectedComponent → ℕ,
      (∀ C, 1 ≤ lengths C) ∧ Nonempty (G ≃g pathStarGraph lengths) := by
  classical
  have hpaths := finite_single_branch_cut_components_paths G hG root hbranch
  choose a ha lengths hpos e he using hpaths
  exact ⟨lengths, hpos, ⟨(pathStarRealizationIso G hG root a ha lengths e he).symm⟩⟩

end FaultObservationResearch
