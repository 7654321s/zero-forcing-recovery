module

/-
Two rooted cut-component paths can be extracted as a two-pendant model.
The remaining induced graph is kept as the original-vertex core.
This is a structural transport tool, not the full tree classification.
-/
public import «formalization-tree-component-split»
public import «formalization-two-pendant-model»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
open SimpleGraph SimpleGraph.Walk
universe u
variable {V : Type u}

theorem removed_component_not_in_core (G : SimpleGraph V) (root : V)
    (removed : Set (treeCutGraph G root).ConnectedComponent)
    (C : (treeCutGraph G root).ConnectedComponent) (hC : C ∈ removed) (x : C) :
    x.val.val ∉ treeComponentRemainderSet G root removed := by
  intro hmem
  apply hmem x.val.property
  change (treeCutGraph G root).connectedComponentMk x.val ∈ removed
  rw [(C.mem_supp_iff x.val).mp x.property]
  exact hC

theorem cut_component_point_eq_component (G : SimpleGraph V) (root : V)
    (C D : (treeCutGraph G root).ConnectedComponent) (x : C) (y : D)
    (hxy : x.val.val = y.val.val) : C = D := by
  calc
    C = (treeCutGraph G root).connectedComponentMk x.val :=
      ((C.mem_supp_iff x.val).mp x.property).symm
    _ = (treeCutGraph G root).connectedComponentMk y.val :=
      congrArg (treeCutGraph G root).connectedComponentMk (Subtype.ext hxy)
    _ = D := (D.mem_supp_iff y.val).mp y.property

theorem tree_component_remainder_or_removed (G : SimpleGraph V) (root : V)
    (removed : Set (treeCutGraph G root).ConnectedComponent) (x : V) :
    x ∈ treeComponentRemainderSet G root removed ∨
      ∃ C ∈ removed, ∃ y : C, y.val.val = x := by
  classical
  by_cases hcore : x ∈ treeComponentRemainderSet G root removed
  · exact Or.inl hcore
  · have hxroot : x ≠ root := by
      intro heq
      apply hcore
      rw [heq]
      exact tree_component_remainder_root_mem G root removed
    let xcut : TreeCutVertex root := ⟨x, hxroot⟩
    let C := (treeCutGraph G root).connectedComponentMk xcut
    have hC : C ∈ removed := by
      by_contra hnot
      apply hcore
      intro hx
      change C ∉ removed
      exact hnot
    exact Or.inr ⟨C, hC, ⟨xcut, (C.mem_supp_iff xcut).mpr rfl⟩, rfl⟩

def twoComponentPartitionMap (G : SimpleGraph V) (root : V)
    (C D : (treeCutGraph G root).ConnectedComponent) :
    (treeComponentRemainderSet G root ({C, D} : Set _)) ⊕ (C ⊕ D) → V
  | Sum.inl x => x.val
  | Sum.inr (Sum.inl x) => x.val.val
  | Sum.inr (Sum.inr x) => x.val.val

theorem twoComponentPartitionMap_bijective (G : SimpleGraph V) (root : V)
    (C D : (treeCutGraph G root).ConnectedComponent) (hCD : C ≠ D) :
    Function.Bijective (twoComponentPartitionMap G root C D) := by
  classical
  constructor
  · rintro (x | (x | x)) (y | (y | y)) heq
    · change x.val = y.val at heq
      congr 1
      exact Subtype.ext heq
    · change x.val = y.val.val at heq
      exact False.elim (removed_component_not_in_core G root {C, D} C (by simp) y (heq ▸ x.property))
    · change x.val = y.val.val at heq
      exact False.elim (removed_component_not_in_core G root {C, D} D (by simp) y (heq ▸ x.property))
    · change x.val.val = y.val at heq
      exact False.elim (removed_component_not_in_core G root {C, D} C (by simp) x (heq.symm ▸ y.property))
    · change x.val.val = y.val.val at heq
      congr 2
      exact Subtype.ext (Subtype.ext heq)
    · change x.val.val = y.val.val at heq
      exact False.elim (hCD (cut_component_point_eq_component G root C D x y heq))
    · change x.val.val = y.val at heq
      exact False.elim (removed_component_not_in_core G root {C, D} D (by simp) x (heq.symm ▸ y.property))
    · change x.val.val = y.val.val at heq
      exact False.elim (hCD (cut_component_point_eq_component G root D C x y heq).symm)
    · change x.val.val = y.val.val at heq
      congr 2
      exact Subtype.ext (Subtype.ext heq)
  · intro z
    rcases tree_component_remainder_or_removed G root ({C, D} : Set _) z with hcore | ⟨E, hE, x, hx⟩
    · exact ⟨Sum.inl ⟨z, hcore⟩, rfl⟩
    · have hchoice : E = C ∨ E = D := by simpa using hE
      rcases hchoice with rfl | rfl
      · exact ⟨Sum.inr (Sum.inl x), hx⟩
      · exact ⟨Sum.inr (Sum.inr x), hx⟩

def twoComponentPartitionEquiv (G : SimpleGraph V) (root : V)
    (C D : (treeCutGraph G root).ConnectedComponent) (hCD : C ≠ D) :
    (treeComponentRemainderSet G root ({C, D} : Set _)) ⊕ (C ⊕ D) ≃ V :=
  Equiv.ofBijective (twoComponentPartitionMap G root C D)
    (twoComponentPartitionMap_bijective G root C D hCD)

def twoCutPathsRealizationEquiv (G : SimpleGraph V) (root : V)
    (C D : (treeCutGraph G root).ConnectedComponent) (hCD : C ≠ D) (a b : ℕ)
    (eC : C.toSimpleGraph ≃g SimpleGraph.pathGraph (a + 1))
    (eD : D.toSimpleGraph ≃g SimpleGraph.pathGraph (b + 1)) :
    TwoPendantVertex (treeComponentRemainderSet G root ({C, D} : Set _)) a b ≃ V :=
  (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr eC.toEquiv.symm eD.toEquiv.symm)).trans
    (twoComponentPartitionEquiv G root C D hCD)

def twoComponentCoreRoot (G : SimpleGraph V) (root : V)
    (C D : (treeCutGraph G root).ConnectedComponent) :
    treeComponentRemainderSet G root ({C, D} : Set _) :=
  ⟨root, tree_component_remainder_root_mem G root {C, D}⟩

theorem removed_path_core_adj_iff (G : SimpleGraph V) (hG : G.IsTree) (root : V)
    (removed : Set (treeCutGraph G root).ConnectedComponent)
    (C : (treeCutGraph G root).ConnectedComponent) (hC : C ∈ removed)
    (attach : C) (hattach : G.Adj root attach.val.val) (n : ℕ)
    (e : C.toSimpleGraph ≃g SimpleGraph.pathGraph n) (he : (e attach).val = 0)
    (x : treeComponentRemainderSet G root removed) (i : Fin n) :
    G.Adj x.val ((e.symm i).val.val) ↔ x.val = root ∧ i.val = 0 := by
  constructor
  · intro h
    have hx := removed_component_core_adj_root G root removed C hC (e.symm i) x h.symm
    have hroot : G.Adj root ((e.symm i).val.val) := by rwa [hx] at h
    have hi := (tree_cut_root_adj_iff_index_zero G hG root C attach hattach n e he (e.symm i)).mp hroot
    exact ⟨hx, by simpa using hi⟩
  · rintro ⟨hx, hi⟩
    rw [hx]
    apply (tree_cut_root_adj_iff_index_zero G hG root C attach hattach n e he (e.symm i)).mpr
    simpa using hi

theorem twoCutPathsRealizationEquiv_adj_iff (G : SimpleGraph V) (hG : G.IsTree) (root : V)
    (C D : (treeCutGraph G root).ConnectedComponent) (hCD : C ≠ D) (a b : ℕ)
    (attachC : C) (hC : G.Adj root attachC.val.val)
    (attachD : D) (hD : G.Adj root attachD.val.val)
    (eC : C.toSimpleGraph ≃g SimpleGraph.pathGraph (a + 1))
    (eD : D.toSimpleGraph ≃g SimpleGraph.pathGraph (b + 1))
    (heC : (eC attachC).val = 0) (heD : (eD attachD).val = 0)
    (x y : TwoPendantVertex (treeComponentRemainderSet G root ({C, D} : Set _)) a b) :
    G.Adj (twoCutPathsRealizationEquiv G root C D hCD a b eC eD x)
      (twoCutPathsRealizationEquiv G root C D hCD a b eC eD y) ↔
      (twoPendantGraph (treeComponentRemainderGraph G root {C, D})
        (twoComponentCoreRoot G root C D) a b).Adj x y := by
  classical
  have hcoreC : ∀ (z : treeComponentRemainderSet G root ({C, D} : Set _)) (i : Fin (a + 1)),
      G.Adj z.val ((eC.symm i).val.val) ↔ z = twoComponentCoreRoot G root C D ∧ i = 0 := by
    intro z i
    rw [removed_path_core_adj_iff G hG root {C, D} C (by simp) attachC hC (a + 1) eC heC z i]
    constructor
    · rintro ⟨hz, hi⟩
      exact ⟨Subtype.ext hz, Fin.ext hi⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
  have hcoreD : ∀ (z : treeComponentRemainderSet G root ({C, D} : Set _)) (i : Fin (b + 1)),
      G.Adj z.val ((eD.symm i).val.val) ↔ z = twoComponentCoreRoot G root C D ∧ i = 0 := by
    intro z i
    rw [removed_path_core_adj_iff G hG root {C, D} D (by simp) attachD hD (b + 1) eD heD z i]
    constructor
    · rintro ⟨hz, hi⟩
      exact ⟨Subtype.ext hz, Fin.ext hi⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
  rcases x with x | (i | j) <;> rcases y with y | (k | l)
  · rfl
  · exact hcoreC x k
  · exact hcoreD x l
  · change G.Adj ((eC.symm i).val.val) y.val ↔ y = twoComponentCoreRoot G root C D ∧ i = 0
    rw [G.adj_comm]
    exact hcoreC y i
  · exact eC.symm.map_adj_iff
  · change G.Adj ((eC.symm i).val.val) ((eD.symm l).val.val) ↔ False
    constructor
    · intro h
      exact hCD (cut_component_edge_same G root C D (eC.symm i) (eD.symm l) h)
    · exact False.elim
  · change G.Adj ((eD.symm j).val.val) y.val ↔ y = twoComponentCoreRoot G root C D ∧ j = 0
    rw [G.adj_comm]
    exact hcoreD y j
  · change G.Adj ((eD.symm j).val.val) ((eC.symm k).val.val) ↔ False
    constructor
    · intro h
      exact hCD (cut_component_edge_same G root D C (eD.symm j) (eC.symm k) h).symm
    · exact False.elim
  · exact eD.symm.map_adj_iff

def twoCutPathsRealizationIso (G : SimpleGraph V) (hG : G.IsTree) (root : V)
    (C D : (treeCutGraph G root).ConnectedComponent) (hCD : C ≠ D) (a b : ℕ)
    (attachC : C) (hC : G.Adj root attachC.val.val)
    (attachD : D) (hD : G.Adj root attachD.val.val)
    (eC : C.toSimpleGraph ≃g SimpleGraph.pathGraph (a + 1))
    (eD : D.toSimpleGraph ≃g SimpleGraph.pathGraph (b + 1))
    (heC : (eC attachC).val = 0) (heD : (eD attachD).val = 0) :
    twoPendantGraph (treeComponentRemainderGraph G root {C, D})
      (twoComponentCoreRoot G root C D) a b ≃g G where
  toEquiv := twoCutPathsRealizationEquiv G root C D hCD a b eC eD
  map_rel_iff' := by
    intro x y
    exact twoCutPathsRealizationEquiv_adj_iff G hG root C D hCD a b
      attachC hC attachD hD eC eD heC heD x y

theorem tree_two_cut_paths_realization (G : SimpleGraph V) (hG : G.IsTree) (root : V)
    (C D : (treeCutGraph G root).ConnectedComponent) (hCD : C ≠ D) (a b : ℕ)
    (attachC : C) (hC : G.Adj root attachC.val.val)
    (attachD : D) (hD : G.Adj root attachD.val.val)
    (eC : C.toSimpleGraph ≃g SimpleGraph.pathGraph (a + 1))
    (eD : D.toSimpleGraph ≃g SimpleGraph.pathGraph (b + 1))
    (heC : (eC attachC).val = 0) (heD : (eD attachD).val = 0) :
    (treeComponentRemainderGraph G root {C, D}).IsTree ∧
    Nonempty (twoPendantGraph (treeComponentRemainderGraph G root {C, D})
      (twoComponentCoreRoot G root C D) a b ≃g G) := by
  exact ⟨tree_component_remainder_isTree G hG root {C, D},
    ⟨twoCutPathsRealizationIso G hG root C D hCD a b attachC hC attachD hD eC eD heC heD⟩⟩

end FaultObservationResearch
