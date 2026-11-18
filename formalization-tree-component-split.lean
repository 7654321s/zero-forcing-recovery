module

/-
Removing whole components attached at one root preserves a connected core.
Standard decomposition tools for extracting the two-center model from a tree.
This file does not itself establish the remaining time-support classification.
-/
public import «formalization-single-branch-realization»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
open SimpleGraph SimpleGraph.Walk
universe u
variable {V : Type u}

def treeComponentRemainderSet (G : SimpleGraph V) (root : V)
    (removed : Set (treeCutGraph G root).ConnectedComponent) : Set V :=
  {x | ∀ hx : x ≠ root, (treeCutGraph G root).connectedComponentMk ⟨x, hx⟩ ∉ removed}

def treeComponentRemainderGraph (G : SimpleGraph V) (root : V)
    (removed : Set (treeCutGraph G root).ConnectedComponent) :
    SimpleGraph (treeComponentRemainderSet G root removed) :=
  G.induce (treeComponentRemainderSet G root removed)

theorem tree_component_remainder_root_mem (G : SimpleGraph V) (root : V)
    (removed : Set (treeCutGraph G root).ConnectedComponent) :
    root ∈ treeComponentRemainderSet G root removed := by
  intro h
  exact False.elim (h rfl)

theorem tree_component_remainder_of_component (G : SimpleGraph V) (root : V)
    (removed : Set (treeCutGraph G root).ConnectedComponent)
    (C : (treeCutGraph G root).ConnectedComponent) (hC : C ∉ removed) (x : C) :
    x.val.val ∈ treeComponentRemainderSet G root removed := by
  intro hx
  change (treeCutGraph G root).connectedComponentMk x.val ∉ removed
  rw [(C.mem_supp_iff x.val).mp x.property]
  exact hC

theorem tree_cut_component_adj_mem (G : SimpleGraph V) (root : V)
    (C : (treeCutGraph G root).ConnectedComponent) (x : C) (y : TreeCutVertex root)
    (hxy : G.Adj x.val.val y.val) : y ∈ C.supp := by
  have hcut : (treeCutGraph G root).Adj x.val y := hxy
  exact (C.mem_supp_iff y).mpr
    ((ConnectedComponent.sound hcut.reachable).symm.trans ((C.mem_supp_iff x.val).mp x.property))

theorem tree_component_remainder_connected (G : SimpleGraph V) (hG : G.Connected)
    (root : V) (removed : Set (treeCutGraph G root).ConnectedComponent) :
    (treeComponentRemainderGraph G root removed).Connected := by
  classical
  let r : treeComponentRemainderSet G root removed :=
    ⟨root, tree_component_remainder_root_mem G root removed⟩
  apply (treeComponentRemainderGraph G root removed).connected_iff_exists_forall_reachable.mpr
  refine ⟨r, ?_⟩
  intro x
  by_cases hx : x.val = root
  · have heq : x = r := Subtype.ext hx
    rw [heq]
  · let xcut : TreeCutVertex root := ⟨x.val, hx⟩
    let C := (treeCutGraph G root).connectedComponentMk xcut
    have hC : C ∉ removed := x.property hx
    have hxC : xcut ∈ C.supp := (C.mem_supp_iff xcut).mpr rfl
    obtain ⟨a, ha⟩ := connected_cut_component_has_neighbor G hG root C
    let q : (treeCutGraph G root).Walk a.val xcut :=
      (C.reachable_of_mem_supp a.property hxC).some
    let f : treeCutGraph G root ↪g G := SimpleGraph.Embedding.induce {z | z ≠ root}
    let p : G.Walk root x.val := (q.map f.toHom).cons ha
    have hinside : ∀ z ∈ p.support, z ∈ treeComponentRemainderSet G root removed := by
      intro z hz
      change z ∈ root :: (q.map f.toHom).support at hz
      rcases List.mem_cons.mp hz with hroot | hz
      · subst z
        exact tree_component_remainder_root_mem G root removed
      · rw [SimpleGraph.Walk.support_map] at hz
        obtain ⟨y, hy, hyz⟩ := List.mem_map.mp hz
        have hyC : y ∈ C.supp := (C.mem_supp_iff y).mpr
          ((ConnectedComponent.sound (q.takeUntil y hy).reachable).symm.trans
            ((C.mem_supp_iff a.val).mp a.property))
        rw [← hyz]
        exact tree_component_remainder_of_component G root removed C hC ⟨y, hyC⟩
    exact (p.induce (treeComponentRemainderSet G root removed) hinside).reachable

theorem tree_component_remainder_isTree (G : SimpleGraph V) (hG : G.IsTree)
    (root : V) (removed : Set (treeCutGraph G root).ConnectedComponent) :
    (treeComponentRemainderGraph G root removed).IsTree := by
  exact ⟨tree_component_remainder_connected G hG.connected root removed,
    hG.isAcyclic.induce (treeComponentRemainderSet G root removed)⟩

theorem removed_component_core_adj_root (G : SimpleGraph V) (root : V)
    (removed : Set (treeCutGraph G root).ConnectedComponent)
    (C : (treeCutGraph G root).ConnectedComponent) (hC : C ∈ removed)
    (x : C) (y : treeComponentRemainderSet G root removed)
    (hxy : G.Adj x.val.val y.val) : y.val = root := by
  by_contra hy
  have hyC := tree_cut_component_adj_mem G root C x ⟨y.val, hy⟩ hxy
  apply y.property hy
  rw [(C.mem_supp_iff _).mp hyC]
  exact hC

theorem tree_off_components_keep_other_vertex (G : SimpleGraph V) (root other : V)
    (hne : other ≠ root) (removed : Set (treeCutGraph G root).ConnectedComponent)
    (hoff : ∀ C ∈ removed, (⟨other, hne⟩ : TreeCutVertex root) ∉ C.supp) :
    other ∈ treeComponentRemainderSet G root removed := by
  intro hx hremoved
  apply hoff ((treeCutGraph G root).connectedComponentMk ⟨other, hx⟩) hremoved
  exact (ConnectedComponent.mem_supp_iff _ _).mpr rfl

end FaultObservationResearch
