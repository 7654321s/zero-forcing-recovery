module

/- A whole connected component contained in an induced set remains a component. -/
public import «formalization-tree-component-split»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
open SimpleGraph SimpleGraph.Walk
universe u v
variable {V : Type u}

def componentIntoInduced (G : SimpleGraph V) (S : Set V)
    (C : G.ConnectedComponent) (hC : C.supp ⊆ S) : C.toSimpleGraph →g G.induce S where
  toFun x := ⟨x.val, hC x.property⟩
  map_rel' h := h

def retainedComponent (G : SimpleGraph V) (S : Set V)
    (C : G.ConnectedComponent) (hC : C.supp ⊆ S) (a : C) :
    (G.induce S).ConnectedComponent :=
  (G.induce S).connectedComponentMk (componentIntoInduced G S C hC a)

theorem retained_component_point_mem (G : SimpleGraph V) (S : Set V)
    (C : G.ConnectedComponent) (hC : C.supp ⊆ S) (a : C)
    (z : retainedComponent G S C hC a) : z.val.val ∈ C.supp := by
  have hr : (G.induce S).Reachable (componentIntoInduced G S C hC a) z.val :=
    ConnectedComponent.exact ((retainedComponent G S C hC a).mem_supp_iff z.val |>.mp z.property).symm
  have hmap := hr.map (SimpleGraph.Embedding.induce S).toHom
  exact (C.mem_supp_iff z.val.val).mpr
    ((ConnectedComponent.sound hmap).symm.trans ((C.mem_supp_iff a.val).mp a.property))

def componentToRetained (G : SimpleGraph V) (S : Set V)
    (C : G.ConnectedComponent) (hC : C.supp ⊆ S) (a : C) (x : C) :
    retainedComponent G S C hC a := by
  refine ⟨componentIntoInduced G S C hC x, ?_⟩
  apply ((retainedComponent G S C hC a).mem_supp_iff _).mpr
  exact (ConnectedComponent.sound ((C.connected_toSimpleGraph a x).map
    (componentIntoInduced G S C hC))).symm

theorem componentToRetained_bijective (G : SimpleGraph V) (S : Set V)
    (C : G.ConnectedComponent) (hC : C.supp ⊆ S) (a : C) :
    Function.Bijective (componentToRetained G S C hC a) := by
  constructor
  · intro x y hxy
    exact Subtype.ext (congrArg (fun z : retainedComponent G S C hC a => z.val.val) hxy)
  · intro z
    refine ⟨⟨z.val.val, retained_component_point_mem G S C hC a z⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl

def retainedComponentIso (G : SimpleGraph V) (S : Set V)
    (C : G.ConnectedComponent) (hC : C.supp ⊆ S) (a : C) :
    C.toSimpleGraph ≃g (retainedComponent G S C hC a).toSimpleGraph where
  toEquiv := Equiv.ofBijective (componentToRetained G S C hC a)
    (componentToRetained_bijective G S C hC a)
  map_rel_iff' := by intro x y; rfl

theorem retained_component_realization (G : SimpleGraph V) (S : Set V)
    (C : G.ConnectedComponent) (hC : C.supp ⊆ S) :
    ∃ D : (G.induce S).ConnectedComponent, Nonempty (C.toSimpleGraph ≃g D.toSimpleGraph) := by
  obtain ⟨a, ha⟩ := C.nonempty_supp
  exact ⟨retainedComponent G S C hC ⟨a, ha⟩, ⟨retainedComponentIso G S C hC ⟨a, ha⟩⟩⟩

def componentTransportIso {W : Type v} (G : SimpleGraph V) (H : SimpleGraph W)
    (e : G ≃g H) (C : G.ConnectedComponent) :
    C.toSimpleGraph ≃g (e.connectedComponentEquiv C).toSimpleGraph where
  toEquiv := ConnectedComponent.isoEquivSupp e C
  map_rel_iff' := by
    intro x y
    change H.Adj (e x.val) (e y.val) ↔ G.Adj x.val y.val
    exact e.map_adj_iff

def cutInduceCommIso (G : SimpleGraph V) (S : Set V) (root : V) (hroot : root ∈ S) :
    treeCutGraph (G.induce S) (⟨root, hroot⟩ : S) ≃g
      (treeCutGraph G root).induce {x : TreeCutVertex root | x.val ∈ S} where
  toEquiv := {
    toFun := fun x => ⟨⟨x.val.val, fun h => x.property (Subtype.ext h)⟩, x.val.property⟩
    invFun := fun x => ⟨⟨x.val.val, x.property⟩, fun h => x.val.property (congrArg Subtype.val h)⟩
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl }
  map_rel_iff' := by intro x y; rfl

theorem retained_cut_component_realization (G : SimpleGraph V) (S : Set V)
    (root : V) (hroot : root ∈ S) (C : (treeCutGraph G root).ConnectedComponent)
    (hC : ∀ x : C, x.val.val ∈ S) :
    ∃ D : (treeCutGraph (G.induce S) (⟨root, hroot⟩ : S)).ConnectedComponent,
      Nonempty (C.toSimpleGraph ≃g D.toSimpleGraph) := by
  let T : Set (TreeCutVertex root) := {x | x.val ∈ S}
  have hCT : C.supp ⊆ T := by
    intro x hx
    exact hC ⟨x, hx⟩
  obtain ⟨D, ⟨e⟩⟩ := retained_component_realization (treeCutGraph G root) T C hCT
  let f := (cutInduceCommIso G S root hroot).symm
  exact ⟨f.connectedComponentEquiv D, ⟨e.trans (componentTransportIso _ _ f D)⟩⟩

def cutInducedForgetHom (G : SimpleGraph V) (S : Set V) (root : V) (hroot : root ∈ S) :
    treeCutGraph (G.induce S) (⟨root, hroot⟩ : S) →g treeCutGraph G root where
  toFun x := ⟨x.val.val, fun h => x.property (Subtype.ext h)⟩
  map_rel' h := h

def retainedCutComponent (G : SimpleGraph V) (S : Set V) (root : V) (hroot : root ∈ S)
    (C : (treeCutGraph G root).ConnectedComponent) (hC : ∀ x : C, x.val.val ∈ S) (a : C) :
    (treeCutGraph (G.induce S) (⟨root, hroot⟩ : S)).ConnectedComponent :=
  (cutInduceCommIso G S root hroot).symm.connectedComponentEquiv
    (retainedComponent (treeCutGraph G root) {x : TreeCutVertex root | x.val ∈ S}
      C (fun x hx => hC ⟨x, hx⟩) a)

def retainedCutComponentIso (G : SimpleGraph V) (S : Set V) (root : V) (hroot : root ∈ S)
    (C : (treeCutGraph G root).ConnectedComponent) (hC : ∀ x : C, x.val.val ∈ S) (a : C) :
    C.toSimpleGraph ≃g (retainedCutComponent G S root hroot C hC a).toSimpleGraph :=
  (retainedComponentIso (treeCutGraph G root) {x : TreeCutVertex root | x.val ∈ S}
    C (fun x hx => hC ⟨x, hx⟩) a).trans
      (componentTransportIso _ _ (cutInduceCommIso G S root hroot).symm _)

theorem retainedCutComponentIso_apply_val (G : SimpleGraph V) (S : Set V)
    (root : V) (hroot : root ∈ S) (C : (treeCutGraph G root).ConnectedComponent)
    (hC : ∀ x : C, x.val.val ∈ S) (a x : C) :
    (retainedCutComponentIso G S root hroot C hC a x).val.val.val = x.val.val := rfl

theorem retainedCutComponent_map (G : SimpleGraph V) (S : Set V)
    (root : V) (hroot : root ∈ S) (C : (treeCutGraph G root).ConnectedComponent)
    (hC : ∀ x : C, x.val.val ∈ S) (a : C) :
    (retainedCutComponent G S root hroot C hC a).map (cutInducedForgetHom G S root hroot) = C := by
  change (treeCutGraph G root).connectedComponentMk a.val = C
  exact (C.mem_supp_iff a.val).mp a.property

theorem retained_cut_components_distinct (G : SimpleGraph V) (S : Set V)
    (root : V) (hroot : root ∈ S) (C D : (treeCutGraph G root).ConnectedComponent)
    (hCD : C ≠ D) (hC : ∀ x : C, x.val.val ∈ S) (hD : ∀ x : D, x.val.val ∈ S)
    (a : C) (b : D) :
    retainedCutComponent G S root hroot C hC a ≠ retainedCutComponent G S root hroot D hD b := by
  intro heq
  apply hCD
  have h := congrArg (fun E => E.map (cutInducedForgetHom G S root hroot)) heq
  simpa only [retainedCutComponent_map] using h

theorem retained_cut_component_avoids (G : SimpleGraph V) (S : Set V)
    (root other : V) (hroot : root ∈ S) (hother : other ∈ S) (hne : other ≠ root)
    (C : (treeCutGraph G root).ConnectedComponent) (hC : ∀ x : C, x.val.val ∈ S) (a : C)
    (hoff : (⟨other, hne⟩ : TreeCutVertex root) ∉ C.supp) :
    (⟨(⟨other, hother⟩ : S), fun h => hne (congrArg Subtype.val h)⟩ :
      TreeCutVertex (⟨root, hroot⟩ : S)) ∉ (retainedCutComponent G S root hroot C hC a).supp := by
  intro hmem
  have h := congrArg (fun E => E.map (cutInducedForgetHom G S root hroot))
    (((retainedCutComponent G S root hroot C hC a).mem_supp_iff _).mp hmem)
  rw [retainedCutComponent_map] at h
  change (treeCutGraph G root).connectedComponentMk ⟨other, hne⟩ = C at h
  exact hoff ((C.mem_supp_iff _).mpr h)

theorem retained_cut_component_mem_iff (G : SimpleGraph V) (S : Set V)
    (root : V) (hroot : root ∈ S) (C : (treeCutGraph G root).ConnectedComponent)
    (hC : ∀ x : C, x.val.val ∈ S) (a : C)
    (z : TreeCutVertex (⟨root, hroot⟩ : S)) :
    z ∈ (retainedCutComponent G S root hroot C hC a).supp ↔
      cutInducedForgetHom G S root hroot z ∈ C.supp := by
  constructor
  · intro hz
    have h := congrArg (fun E => E.map (cutInducedForgetHom G S root hroot))
      (((retainedCutComponent G S root hroot C hC a).mem_supp_iff z).mp hz)
    rw [retainedCutComponent_map] at h
    exact (C.mem_supp_iff _).mpr h
  · intro hz
    let x : C := ⟨cutInducedForgetHom G S root hroot z, hz⟩
    let e := retainedCutComponentIso G S root hroot C hC a
    have heq : (e x).val = z := by
      apply Subtype.ext
      apply Subtype.ext
      rfl
    rw [← heq]
    exact (e x).property

end FaultObservationResearch
