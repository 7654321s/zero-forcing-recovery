module

/-
Off components at distinct roots do not overlap. Removing one side preserves
every vertex of the opposite off components. No classification claim here.
-/
public import «formalization-tree-component-split»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
open SimpleGraph SimpleGraph.Walk
universe u
variable {V : Type u}

theorem off_cut_component_point_ne (G : SimpleGraph V) (root other : V)
    (hne : other ≠ root) (C : (treeCutGraph G root).ConnectedComponent)
    (hoff : (⟨other, hne⟩ : TreeCutVertex root) ∉ C.supp) (x : C) :
    x.val.val ≠ other := by
  intro heq
  apply hoff
  have hsub : x.val = (⟨other, hne⟩ : TreeCutVertex root) := Subtype.ext heq
  rw [← hsub]
  exact x.property

theorem off_cut_component_root_reachable (G : SimpleGraph V) (hG : G.Connected)
    (root other : V) (hne : root ≠ other)
    (C : (treeCutGraph G root).ConnectedComponent)
    (hoff : (⟨other, hne.symm⟩ : TreeCutVertex root) ∉ C.supp) (x : C) :
    (treeCutGraph G other).Reachable ⟨root, hne⟩
      ⟨x.val.val, off_cut_component_point_ne G root other hne.symm C hoff x⟩ := by
  classical
  obtain ⟨a, ha⟩ := connected_cut_component_has_neighbor G hG root C
  let q : (treeCutGraph G root).Walk a.val x.val :=
    (C.reachable_of_mem_supp a.property x.property).some
  let f : treeCutGraph G root ↪g G := SimpleGraph.Embedding.induce {z | z ≠ root}
  let p : G.Walk root x.val.val := (q.map f.toHom).cons ha
  have hinside : ∀ z ∈ p.support, z ≠ other := by
    intro z hz
    change z ∈ root :: (q.map f.toHom).support at hz
    rcases List.mem_cons.mp hz with hroot | hz
    · exact hroot ▸ hne
    · rw [SimpleGraph.Walk.support_map] at hz
      obtain ⟨y, hy, hyz⟩ := List.mem_map.mp hz
      have hyC : y ∈ C.supp := (C.mem_supp_iff y).mpr
        ((ConnectedComponent.sound (q.takeUntil y hy).reachable).symm.trans
          ((C.mem_supp_iff a.val).mp a.property))
      rw [← hyz]
      exact off_cut_component_point_ne G root other hne.symm C hoff ⟨y, hyC⟩
  exact (p.induce {z | z ≠ other} hinside).reachable

theorem opposite_off_components_disjoint (G : SimpleGraph V) (hG : G.Connected)
    (root other : V) (hne : root ≠ other)
    (C : (treeCutGraph G root).ConnectedComponent)
    (D : (treeCutGraph G other).ConnectedComponent)
    (hC : (⟨other, hne.symm⟩ : TreeCutVertex root) ∉ C.supp)
    (hD : (⟨root, hne⟩ : TreeCutVertex other) ∉ D.supp)
    (x : C) (y : D) : x.val.val ≠ y.val.val := by
  intro heq
  let xcut : TreeCutVertex other :=
    ⟨x.val.val, off_cut_component_point_ne G root other hne.symm C hC x⟩
  have hxD : xcut ∈ D.supp := by
    have hsub : xcut = y.val := Subtype.ext heq
    rw [hsub]
    exact y.property
  apply hD
  exact (D.mem_supp_iff _).mpr
    ((ConnectedComponent.sound (off_cut_component_root_reachable G hG root other hne C hC x)).trans
      ((D.mem_supp_iff xcut).mp hxD))

theorem opposite_off_component_kept (G : SimpleGraph V) (hG : G.Connected)
    (root other : V) (hne : root ≠ other)
    (removed : Set (treeCutGraph G root).ConnectedComponent)
    (hoff : ∀ C ∈ removed, (⟨other, hne.symm⟩ : TreeCutVertex root) ∉ C.supp)
    (D : (treeCutGraph G other).ConnectedComponent)
    (hD : (⟨root, hne⟩ : TreeCutVertex other) ∉ D.supp) (y : D) :
    y.val.val ∈ treeComponentRemainderSet G root removed := by
  intro hy hremoved
  let C := (treeCutGraph G root).connectedComponentMk ⟨y.val.val, hy⟩
  let x : C := ⟨⟨y.val.val, hy⟩, (C.mem_supp_iff _).mpr rfl⟩
  exact opposite_off_components_disjoint G hG root other hne C D
    (hoff C hremoved) hD x y rfl

end FaultObservationResearch
