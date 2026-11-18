module

/-
Transport of the one-short-arm obstruction back to original finite trees.
The multiple-branch structural exhaustion remains a separate obligation.
-/
public import «formalization-single-branch-all-long»
public import «formalization-path-star-short-witness»
public import «formalization-tree-cherry-canonical»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
universe u v

theorem pathStar_head_leaf_length_one {I : Type u} (L : I → ℕ) (i : I)
    (hpos : 1 ≤ L i) (k : Fin (L i)) (hk : k.val = 0)
    (hleaf : TreeLeaf (pathStarGraph L) (some ⟨i, k⟩)) : L i = 1 := by
  by_contra hne
  have hlong : 2 ≤ L i := by omega
  let second : Fin (L i) := ⟨1, by omega⟩
  obtain ⟨neighbor, _, huniq⟩ := hleaf
  have hnone : (none : PathStarVertex I L) = neighbor := huniq none hk
  have hsecond : (some ⟨i, second⟩ : PathStarVertex I L) = neighbor := by
    apply huniq
    change i = i ∧ (k.val + 1 = second.val ∨ second.val + 1 = k.val)
    exact ⟨rfl, Or.inl (by change k.val + 1 = 1; omega)⟩
  have heq := hsecond.trans hnone.symm
  cases heq

theorem finite_single_branch_unique_leaf_neighbor_not_support {V : Type v}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : G.IsTree) (root : V)
    (hrootbranch : TreeBranchVertex G root)
    (hbranch : ∀ x, x ≠ root → ¬ TreeBranchVertex G x)
    (hunique : ∃! x, G.Adj root x ∧ TreeLeaf G x) : ¬ EveryMinimumSupport G.Adj := by
  classical
  let : Fintype (treeCutGraph G root).ConnectedComponent := Fintype.ofFinite _
  have hpaths := finite_single_branch_cut_components_paths G hG root hbranch
  choose a ha L hpos e he using hpaths
  let f := pathStarRealizationIso G hG root a ha L e he
  have hroot : f none = root := rfl
  have hsym : f.symm root = none := by
    apply f.injective
    rw [f.apply_symm_apply, hroot]
  have hmodelbranch : TreeBranchVertex (pathStarGraph L) none := by
    have h := branch_vertex_of_embedding G (pathStarGraph L) f.symm.toEmbedding root hrootbranch
    change TreeBranchVertex (pathStarGraph L) (f.symm root) at h
    simpa only [hsym] using h
  have hcard := pathStar_branch_center_card L hmodelbranch
  obtain ⟨leaf, ⟨hadj, hleaf⟩, huniq⟩ := hunique
  have hmodeladj : (pathStarGraph L).Adj none (f.symm leaf) := by
    have h := f.symm.map_adj_iff.mpr hadj
    simpa only [hsym] using h
  have hmodelleaf := treeLeaf_of_graph_iso G (pathStarGraph L) f.symm leaf hleaf
  cases hpre : f.symm leaf with
  | none =>
    rw [hpre] at hmodeladj
    exact False.elim hmodeladj
  | some vertex =>
    obtain ⟨s, k⟩ := vertex
    rw [hpre] at hmodeladj hmodelleaf
    have hk : k.val = 0 := hmodeladj
    have hs : L s = 1 := pathStar_head_leaf_length_one L s (hpos s) k hk hmodelleaf
    have hleafimage : f (some ⟨s, k⟩) = leaf := by
      rw [← hpre]
      exact f.apply_symm_apply leaf
    have hlong : ∀ i, i ≠ s → 2 ≤ L i := by
      intro i his
      by_contra h
      have hLi : L i = 1 := by have hp := hpos i; omega
      let q : Fin (L i) := ⟨0, by omega⟩
      have hleafi := treeLeaf_of_graph_iso (pathStarGraph L) G f (some ⟨i, q⟩)
        (pathStar_length_one_is_leaf L i hLi q)
      have hadji : G.Adj root (f (some ⟨i, q⟩)) := by
        have hm : (pathStarGraph L).Adj none (some ⟨i, q⟩) := rfl
        simpa only [hroot] using f.map_adj_iff.mpr hm
      have himage : f (some ⟨i, q⟩) = leaf := huniq _ ⟨hadji, hleafi⟩
      have heq := f.injective (himage.trans hleafimage.symm)
      exact his (pathStar_nodes_eq_arm L i s q k heq)
    exact graph_iso_one_short_pathStar_not_support G L hpos s hs hlong hcard f.symm

theorem finite_single_branch_at_most_one_leaf_neighbor_not_support {V : Type v}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : G.IsTree) (root : V)
    (hrootbranch : TreeBranchVertex G root)
    (hbranch : ∀ x, x ≠ root → ¬ TreeBranchVertex G x)
    (hatmost : ∀ x y, G.Adj root x → TreeLeaf G x → G.Adj root y → TreeLeaf G y → x = y) :
    ¬ EveryMinimumSupport G.Adj := by
  classical
  by_cases hexists : ∃ x, G.Adj root x ∧ TreeLeaf G x
  · obtain ⟨x, hx⟩ := hexists
    apply finite_single_branch_unique_leaf_neighbor_not_support G hG root hrootbranch hbranch
    refine ⟨x, hx, ?_⟩
    intro y hy
    exact hatmost y x hy.1 hy.2 hx.1 hx.2
  · apply finite_single_branch_no_leaf_neighbors_not_support G hG root hrootbranch hbranch
    intro x hadj hleaf
    exact hexists ⟨x, hadj, hleaf⟩

theorem finite_at_most_one_branch_tree_classification {V : Type v}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : G.IsTree)
    (hatmostbranch : ∀ x y, TreeBranchVertex G x → TreeBranchVertex G y → x = y) :
    EveryMinimumSupport G.Adj ↔ InTreeCandidateClass G := by
  classical
  constructor
  · intro htarget
    by_cases hcherry : ∃ c, TreeLeafPairCenter G c
    · exact Or.inr ((tree_cherry_support_iff_star_or_double_star G hG hcherry).mp htarget)
    · by_cases hhasbranch : ∃ root, TreeBranchVertex G root
      · obtain ⟨root, hroot⟩ := hhasbranch
        have hbranch : ∀ x, x ≠ root → ¬ TreeBranchVertex G x := by
          intro x hx hxb
          exact hx (hatmostbranch x root hxb hroot)
        have hatmostleaf : ∀ x y, G.Adj root x → TreeLeaf G x →
            G.Adj root y → TreeLeaf G y → x = y := by
          intro x y hax hx hay hy
          by_contra hne
          exact hcherry ⟨root, x, y, hne, hax.symm, hx, hay.symm, hy⟩
        exact False.elim (finite_single_branch_at_most_one_leaf_neighbor_not_support
          G hG root hroot hbranch hatmostleaf htarget)
      · exact Or.inl (finite_nonbranch_tree_path G hG (by
          intro x hx
          exact hhasbranch ⟨x, hx⟩))
  · exact candidateClass_every_minimum_support G

end FaultObservationResearch
