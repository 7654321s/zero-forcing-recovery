module

/-
Standard tree structure: components after removing a vertex, their unique
attachment, and rooted path models when there is no other branch vertex.
Draft until a successful scoped compiler/axiom record is available.
These structural facts are prior graph theory, not originality claims.
-/
public import «formalization-tree-rooted-path»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
open SimpleGraph SimpleGraph.Walk
universe u v
variable {V : Type u} {W : Type v}

abbrev TreeCutVertex (root : V) := {x : V // x ≠ root}

def treeCutGraph (G : SimpleGraph V) (root : V) : SimpleGraph (TreeCutVertex root) :=
  G.induce {x | x ≠ root}

theorem branch_vertex_of_embedding (H : SimpleGraph W) (G : SimpleGraph V)
    (e : H ↪g G) (x : W) (hx : TreeBranchVertex H x) : TreeBranchVertex G (e x) := by
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := hx
  exact ⟨e a, e b, e c, e.map_adj_iff.mpr ha, e.map_adj_iff.mpr hb,
    e.map_adj_iff.mpr hc, fun h => hab (e.injective h),
    fun h => hac (e.injective h), fun h => hbc (e.injective h)⟩

theorem acyclic_cut_neighbors_unique (G : SimpleGraph V) (hG : G.IsAcyclic)
    (root : V) (x y : TreeCutVertex root)
    (hx : G.Adj root x.val) (hy : G.Adj root y.val)
    (hreach : (treeCutGraph G root).Reachable x y) : x = y := by
  classical
  obtain ⟨p, hp⟩ := hreach.exists_isPath
  let f : treeCutGraph G root ↪g G := SimpleGraph.Embedding.induce {z | z ≠ root}
  have hpmap : (p.map f.toHom).IsPath := hp.map f.injective
  have hnot : root ∉ (p.map f.toHom).support := by
    rw [SimpleGraph.Walk.support_map]
    intro h
    obtain ⟨z, _, hz⟩ := List.mem_map.mp h
    exact z.property hz
  have hnew : ((p.map f.toHom).cons hx).IsPath := hpmap.cons hnot
  have h := hG.eq_snd_of_adj_start hnew hy ((p.map f.toHom).cons hx).end_mem_support
  apply Subtype.ext
  exact (h.trans ((p.map f.toHom).snd_cons hx)).symm

theorem connected_cut_component_has_neighbor (G : SimpleGraph V) (hG : G.Connected)
    (root : V) (C : (treeCutGraph G root).ConnectedComponent) :
    ∃ a : C, G.Adj root a.val.val := by
  classical
  obtain ⟨x, hx⟩ := C.nonempty_supp
  obtain ⟨p, hp⟩ := hG.exists_isPath root x.val
  have hnil : ¬ p.Nil := not_nil_of_ne x.property.symm
  have hnot : root ∉ p.tail.support := by
    have hnodup := hp.support_nodup
    rw [← p.cons_support_tail hnil] at hnodup
    exact (List.nodup_cons.mp hnodup).1
  have hinside : ∀ z ∈ p.tail.support, z ∈ {z | z ≠ root} := by
    intro z hz heq
    exact hnot (heq ▸ hz)
  let a : TreeCutVertex root := ⟨p.snd, (p.adj_snd hnil).ne'⟩
  have hreach : (treeCutGraph G root).Reachable a x :=
    (p.tail.induce {z | z ≠ root} hinside).reachable
  have ha : a ∈ C.supp := (C.mem_supp_iff a).mpr
    ((ConnectedComponent.sound hreach).trans ((C.mem_supp_iff x).mp hx))
  exact ⟨⟨a, ha⟩, p.adj_snd hnil⟩

theorem tree_cut_component_unique_neighbor (G : SimpleGraph V) (hG : G.IsTree)
    (root : V) (C : (treeCutGraph G root).ConnectedComponent) :
    ∃! a : C, G.Adj root a.val.val := by
  obtain ⟨a, ha⟩ := connected_cut_component_has_neighbor G hG.connected root C
  refine ⟨a, ha, ?_⟩
  intro b hb
  exact Subtype.ext (acyclic_cut_neighbors_unique G hG.isAcyclic root b.val a.val hb ha
    (C.reachable_of_mem_supp b.property a.property))

theorem tree_cut_component_isTree (G : SimpleGraph V) (hG : G.IsTree)
    (root : V) (C : (treeCutGraph G root).ConnectedComponent) : C.toSimpleGraph.IsTree := by
  exact ⟨C.connected_toSimpleGraph,
    (hG.isAcyclic.induce {z | z ≠ root}).induce C.supp⟩

theorem single_branch_cut_component_nonbranch (G : SimpleGraph V) (root : V)
    (hbranch : ∀ x, x ≠ root → ¬ TreeBranchVertex G x)
    (C : (treeCutGraph G root).ConnectedComponent) :
    ∀ x : C, ¬ TreeBranchVertex C.toSimpleGraph x := by
  intro x hx
  let e : C.toSimpleGraph ↪g G :=
    (SimpleGraph.Embedding.induce {z | z ≠ root}).comp
      (SimpleGraph.Embedding.induce C.supp)
  exact hbranch x.val.val x.val.property
    (branch_vertex_of_embedding C.toSimpleGraph G e x hx)

theorem single_branch_cut_attachment_at_most_one_neighbor (G : SimpleGraph V) (root : V)
    (hbranch : ∀ x, x ≠ root → ¬ TreeBranchVertex G x)
    (C : (treeCutGraph G root).ConnectedComponent) (a : C) (ha : G.Adj root a.val.val) :
    ∀ x y : C, C.toSimpleGraph.Adj a x → C.toSimpleGraph.Adj a y → x = y := by
  intro x y hx hy
  by_contra hne
  have hxy : x.val.val ≠ y.val.val := by
    intro h
    exact hne (Subtype.ext (Subtype.ext h))
  exact hbranch a.val.val a.val.property
    ⟨root, x.val.val, y.val.val, ha.symm, hx, hy,
      x.val.property.symm, y.val.property.symm, hxy⟩

theorem finite_single_branch_cut_components_paths [Fintype V]
    (G : SimpleGraph V) (hG : G.IsTree) (root : V)
    (hbranch : ∀ x, x ≠ root → ¬ TreeBranchVertex G x)
    (C : (treeCutGraph G root).ConnectedComponent) :
    ∃ a : C, G.Adj root a.val.val ∧
      ∃ n, 1 ≤ n ∧ ∃ e : C.toSimpleGraph ≃g SimpleGraph.pathGraph n, (e a).val = 0 := by
  classical
  let : Fintype C := Fintype.ofFinite C
  obtain ⟨a, ha⟩ := connected_cut_component_has_neighbor G hG.connected root C
  refine ⟨a, ha, ?_⟩
  exact finite_rooted_nonbranch_tree_path C.toSimpleGraph
    (tree_cut_component_isTree G hG root C) a
    (single_branch_cut_component_nonbranch G root hbranch C)
    (single_branch_cut_attachment_at_most_one_neighbor G root hbranch C a ha)

end FaultObservationResearch
