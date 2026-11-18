module

/-
Standard structural tools for the zero-branch case of finite-tree exhaustion.
Draft until a successful scoped compiler and axiom audit is recorded.
No graph vertices or edges are discarded by the resulting isomorphism.
-/
public import «formalization-tree-leaf-path-cover»
public import «formalization-path-support»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
open SimpleGraph SimpleGraph.Walk
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

def TreeBranchVertex (G : SimpleGraph V) (x : V) : Prop :=
  ∃ a b c, G.Adj x a ∧ G.Adj x b ∧ G.Adj x c ∧
    a ≠ b ∧ a ≠ c ∧ b ≠ c

omit [Fintype V] [DecidableEq V] in
theorem nonbranch_maximal_path_neighbor_closed (G : SimpleGraph V)
    (hnobranch : ∀ x, ¬ TreeBranchVertex G x)
    (z a b : V) (p : G.Walk a b) (hp : p.IsPath) (hz : z ∈ p.support)
    (hmax : ∀ (a' b' : V) (q : G.Walk a' b'), q.IsPath →
      z ∈ q.support → q.length ≤ p.length) :
    ∀ x ∈ p.support, ∀ y, G.Adj x y → y ∈ p.support := by
  classical
  intro x hx y hxy
  by_contra hy
  by_cases hxa : x = a
  · subst x
    have hnew : (p.cons hxy.symm).IsPath := hp.cons hy
    have h := hmax y b (p.cons hxy.symm) hnew
      (p.support_subset_support_cons hxy.symm hz)
    simp only [length_cons] at h
    omega
  by_cases hxb : x = b
  · subst x
    have hnew : (p.concat hxy).IsPath := hp.concat hy hxy
    have h := hmax a y (p.concat hxy) hnew
      (p.support_subset_support_concat hxy hz)
    simp only [length_concat] at h
    omega
  obtain ⟨i, hix, hi⟩ := mem_support_iff_exists_getVert.mp hx
  have hi0 : 0 < i := by
    by_contra h
    have hiZero : i = 0 := by omega
    exact hxa (hix.symm.trans (by simp [hiZero]))
  have hiLast : i < p.length := by
    by_contra h
    have hiEnd : i = p.length := by omega
    exact hxb (hix.symm.trans (by simp [hiEnd]))
  have hleft : G.Adj x (p.getVert (i - 1)) := by
    have h := (p.adj_getVert_succ (i := i - 1) (by omega)).symm
    have heq : i - 1 + 1 = i := by omega
    simpa only [heq, hix] using h
  have hright : G.Adj x (p.getVert (i + 1)) := by
    simpa only [hix] using p.adj_getVert_succ hiLast
  have hne : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
    intro heq
    have h := hp.getVert_injOn (by rw [Set.mem_ofPred_eq]; omega)
      (by rw [Set.mem_ofPred_eq]; omega) heq
    omega
  have hleftNe : p.getVert (i - 1) ≠ y := by
    intro heq
    exact hy (heq ▸ p.getVert_mem_support (i - 1))
  have hrightNe : p.getVert (i + 1) ≠ y := by
    intro heq
    exact hy (heq ▸ p.getVert_mem_support (i + 1))
  exact hnobranch x ⟨p.getVert (i - 1), p.getVert (i + 1), y,
    hleft, hright, hxy, hne, hleftNe, hrightNe⟩

omit [Fintype V] [DecidableEq V] in
theorem tree_spanning_path_iso (G : SimpleGraph V) (hG : G.IsTree)
    (a b : V) (p : G.Walk a b) (hp : p.IsPath)
    (hcover : ∀ x, x ∈ p.support) :
    Nonempty (G ≃g SimpleGraph.pathGraph (p.length + 1)) := by
  classical
  have hspan : p.toSubgraph.IsSpanning := by
    intro x
    exact p.mem_verts_toSubgraph.mpr (hcover x)
  let e := p.toSubgraph.spanningCoeEquivCoeOfSpanning hspan
  have hconn : p.toSubgraph.spanningCoe.Connected :=
    e.connected_iff.mpr p.toSubgraph_connected.coe
  have hle : G ≤ p.toSubgraph.spanningCoe :=
    (SimpleGraph.isTree_iff_minimal_connected.mp hG).2 hconn p.toSubgraph.spanningCoe_le
  have heq : p.toSubgraph.spanningCoe = G :=
    le_antisymm p.toSubgraph.spanningCoe_le hle
  have hIso : SimpleGraph.pathGraph (p.length + 1) ≃g G := by
    simpa only [heq] using hp.pathGraphIsoToSubgraph.trans e.symm
  exact ⟨hIso.symm⟩

omit [DecidableEq V] in
theorem finite_nonbranch_tree_path (G : SimpleGraph V) (hG : G.IsTree)
    (hnobranch : ∀ x, ¬ TreeBranchVertex G x) :
    ∃ n, 1 ≤ n ∧ Nonempty (G ≃g SimpleGraph.pathGraph n) := by
  classical
  obtain ⟨z⟩ := hG.connected.nonempty
  obtain ⟨a, b, p, hp, hz, hmax⟩ := finite_maximal_path_through_vertex G z
  have hclosed := nonbranch_maximal_path_neighbor_closed G hnobranch z a b p hp hz hmax
  have hset : {x | x ∈ p.support} = Set.univ :=
    connected_neighbor_closed_eq_univ G hG.connected {x | x ∈ p.support} z hz hclosed
  have hcover : ∀ x, x ∈ p.support := by
    intro x
    change x ∈ {x | x ∈ p.support}
    rw [hset]
    exact Set.mem_univ x
  exact ⟨p.length + 1, by omega, tree_spanning_path_iso G hG a b p hp hcover⟩

theorem finite_nonbranch_tree_support (G : SimpleGraph V) (hG : G.IsTree)
    (hnobranch : ∀ x, ¬ TreeBranchVertex G x) : EveryMinimumSupport G.Adj := by
  obtain ⟨n, hn, ⟨e⟩⟩ := finite_nonbranch_tree_path G hG hnobranch
  exact support_of_path_iso G n hn e

end FaultObservationResearch
