module

/-
Unverified draft: exact original-graph realization from leaf-parent fibers.
No vertices are deleted. This is a transport tool and a tree-cherry criterion,
not the full tree classification and not an originality claim.
-/
public import «formalization-tree-leaf-path-cover»
public import «formalization-tree-target»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

abbrev LeafParentVertex (G : SimpleGraph V) := {r : V // TreeLeafParent G r}
abbrev LeafParentFiber (G : SimpleGraph V) (r : LeafParentVertex G) :=
  {x : V // TreeLeaf G x ∧ G.Adj x r.val}

def leafParentAmount (G : SimpleGraph V) (r : LeafParentVertex G) : ℕ := by
  classical
  exact Fintype.card (LeafParentFiber G r)

def leafParentEnumeration (G : SimpleGraph V) (r : LeafParentVertex G) :
    Fin (leafParentAmount G r) ≃ LeafParentFiber G r := by
  classical
  exact (Fintype.equivFin (LeafParentFiber G r)).symm

def leafParentCore (G : SimpleGraph V) : SimpleGraph (LeafParentVertex G) :=
  G.induce {r | TreeLeafParent G r}

def leafParentRealizationMap (G : SimpleGraph V) :
    CoronaVertex (LeafParentVertex G) (leafParentAmount G) → V
  | Sum.inl r => r.val
  | Sum.inr ⟨r, j⟩ => (leafParentEnumeration G r j).val

omit [Fintype V] [DecidableEq V] in
theorem tree_leaf_neighbor_unique (G : SimpleGraph V) (x r c : V)
    (hx : TreeLeaf G x) (hxr : G.Adj x r) (hxc : G.Adj x c) : r = c := by
  obtain ⟨q, _, hq⟩ := hx
  exact (hq r hxr).trans (hq c hxc).symm

omit [DecidableEq V] in
theorem leafParentAmount_at_least_two (G : SimpleGraph V)
    (hpair : ∀ r, TreeLeafParent G r → TreeLeafPairCenter G r)
    (r : LeafParentVertex G) : 2 ≤ leafParentAmount G r := by
  classical
  obtain ⟨a, b, hab, har, ha, hbr, hb⟩ := hpair r.val r.property
  let aa : LeafParentFiber G r := ⟨a, ha, har⟩
  let bb : LeafParentFiber G r := ⟨b, hb, hbr⟩
  have hne : aa ≠ bb := by
    intro h
    exact hab (congrArg Subtype.val h)
  have : Nontrivial (LeafParentFiber G r) := ⟨⟨aa, bb, hne⟩⟩
  have h := Fintype.one_lt_card (α := LeafParentFiber G r)
  change 2 ≤ Fintype.card (LeafParentFiber G r)
  omega

omit [DecidableEq V] in
theorem leafParentRealizationMap_injective (G : SimpleGraph V)
    (hpair : ∀ r, TreeLeafParent G r → TreeLeafPairCenter G r) :
    Function.Injective (leafParentRealizationMap G) := by
  classical
  intro x y hxy
  cases x with
  | inl r =>
    cases y with
    | inl c =>
      exact congrArg Sum.inl (Subtype.ext hxy)
    | inr leaf =>
      obtain ⟨c, j⟩ := leaf
      change r.val = (leafParentEnumeration G c j).val at hxy
      have hleaf := (leafParentEnumeration G c j).property.1
      have hnot := leaf_pair_center_not_leaf G r.val (hpair r.val r.property)
      exact False.elim (hnot (hxy.symm ▸ hleaf))
  | inr leaf =>
    obtain ⟨r, i⟩ := leaf
    cases y with
    | inl c =>
      change (leafParentEnumeration G r i).val = c.val at hxy
      have hleaf := (leafParentEnumeration G r i).property.1
      have hnot := leaf_pair_center_not_leaf G c.val (hpair c.val c.property)
      exact False.elim (hnot (hxy ▸ hleaf))
    | inr other =>
      obtain ⟨c, j⟩ := other
      change (leafParentEnumeration G r i).val = (leafParentEnumeration G c j).val at hxy
      have haa := (leafParentEnumeration G r i).property.2
      have hbb := (leafParentEnumeration G c j).property.2
      have hleaf := (leafParentEnumeration G r i).property.1
      have hto : G.Adj (leafParentEnumeration G r i).val c.val := hxy.symm ▸ hbb
      have hrc : r = c := Subtype.ext (tree_leaf_neighbor_unique G _ _ _ hleaf haa hto)
      subst c
      have hij : i = j := (leafParentEnumeration G r).injective (Subtype.ext hxy)
      subst j
      rfl

omit [DecidableEq V] in
theorem leafParentRealizationMap_surjective (G : SimpleGraph V)
    (hcover : ∀ x, TreeLeaf G x ∨ TreeLeafParent G x) :
    Function.Surjective (leafParentRealizationMap G) := by
  classical
  intro x
  by_cases hx : TreeLeaf G x
  · have hxCopy := hx
    obtain ⟨r, hxr, _⟩ := hxCopy
    let rr : LeafParentVertex G := ⟨r, x, hxr, hx⟩
    let xx : LeafParentFiber G rr := ⟨x, hx, hxr⟩
    refine ⟨Sum.inr ⟨rr, (leafParentEnumeration G rr).symm xx⟩, ?_⟩
    change (leafParentEnumeration G rr ((leafParentEnumeration G rr).symm xx)).val = x
    simp [xx]
  · have hr : TreeLeafParent G x := (hcover x).resolve_left hx
    exact ⟨Sum.inl ⟨x, hr⟩, rfl⟩

omit [DecidableEq V] in
theorem leafParentRealizationMap_adj_iff (G : SimpleGraph V)
    (hpair : ∀ r, TreeLeafParent G r → TreeLeafPairCenter G r)
    (x y : CoronaVertex (LeafParentVertex G) (leafParentAmount G)) :
    G.Adj (leafParentRealizationMap G x) (leafParentRealizationMap G y) ↔
      coronaAdj (leafParentCore G) (leafParentAmount G) x y := by
  classical
  cases x with
  | inl r =>
    cases y with
    | inl c => exact Iff.rfl
    | inr leaf =>
      obtain ⟨c, j⟩ := leaf
      change G.Adj r.val (leafParentEnumeration G c j).val ↔ r = c
      constructor
      · intro h
        exact Subtype.ext (tree_leaf_neighbor_unique G _ _ _
          (leafParentEnumeration G c j).property.1 h.symm
          (leafParentEnumeration G c j).property.2)
      · intro hrc
        subst c
        exact (leafParentEnumeration G r j).property.2.symm
  | inr leaf =>
    obtain ⟨r, i⟩ := leaf
    cases y with
    | inl c =>
      change G.Adj (leafParentEnumeration G r i).val c.val ↔ r = c
      constructor
      · intro h
        exact Subtype.ext (tree_leaf_neighbor_unique G _ _ _
          (leafParentEnumeration G r i).property.1
          (leafParentEnumeration G r i).property.2 h)
      · rintro rfl
        exact (leafParentEnumeration G r i).property.2
    | inr other =>
      obtain ⟨c, j⟩ := other
      change G.Adj (leafParentEnumeration G r i).val (leafParentEnumeration G c j).val ↔ False
      constructor
      · intro h
        have heq := tree_leaf_neighbor_unique G _ _ _
          (leafParentEnumeration G r i).property.1
          (leafParentEnumeration G r i).property.2 h
        have hleaf : TreeLeaf G r.val := heq.symm ▸ (leafParentEnumeration G c j).property.1
        exact (leaf_pair_center_not_leaf G r.val (hpair r.val r.property)) hleaf
      · intro h
        exact False.elim h

def leafParentRealizationIso (G : SimpleGraph V)
    (hpair : ∀ r, TreeLeafParent G r → TreeLeafPairCenter G r)
    (hcover : ∀ x, TreeLeaf G x ∨ TreeLeafParent G x) :
    coronaGraph (leafParentCore G) (leafParentAmount G) ≃g G where
  toEquiv := Equiv.ofBijective (leafParentRealizationMap G)
    ⟨leafParentRealizationMap_injective G hpair, leafParentRealizationMap_surjective G hcover⟩
  map_rel_iff' := by
    intro x y
    exact leafParentRealizationMap_adj_iff G hpair x y

theorem support_of_leaf_parent_complete_cover (G : SimpleGraph V)
    (hpair : ∀ r, TreeLeafParent G r → TreeLeafPairCenter G r)
    (hcover : ∀ x, TreeLeaf G x ∨ TreeLeafParent G x)
    (hclique : ∀ r c, TreeLeafParent G r → TreeLeafParent G c → r ≠ c → G.Adj r c) :
    EveryMinimumSupport G.Adj := by
  classical
  have hcore : CoreComplete (leafParentCore G) := by
    intro r c hne
    exact hclique r.val c.val r.property c.property
      (fun heq => hne (Subtype.ext heq))
  have hmodel : EveryMinimumSupport
      (coronaGraph (leafParentCore G) (leafParentAmount G)).Adj :=
    leafy_complete_every_minimum_support (leafParentCore G) (leafParentAmount G)
      (leafParentAmount_at_least_two G hpair) hcore
  exact (EveryMinimumSupport_iso_iff _ _ (leafParentRealizationIso G hpair hcover)).mp hmodel

theorem tree_cherry_support_iff_leaf_parent_structure (G : SimpleGraph V) (hG : G.IsTree)
    (hcherry : ∃ c, TreeLeafPairCenter G c) :
    EveryMinimumSupport G.Adj ↔
      (∀ r, TreeLeafParent G r → TreeLeafPairCenter G r) ∧
      (∀ x, TreeLeaf G x ∨ TreeLeafParent G x) ∧
      (∀ r c, TreeLeafParent G r → TreeLeafParent G c → r ≠ c → G.Adj r c) := by
  constructor
  · intro hU
    exact ⟨support_cherry_leaf_parent_has_pair G hG.connected hU hcherry,
      support_cherry_leaf_parent_cover G hG hU hcherry,
      support_cherry_leaf_parents_clique G hG.connected hU hcherry⟩
  · rintro ⟨hpair, hcover, hclique⟩
    exact support_of_leaf_parent_complete_cover G hpair hcover hclique

end FaultObservationResearch
