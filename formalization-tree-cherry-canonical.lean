module

/- Unverified draft: identify the checked leaf-parent structure with canonical
stars/double stars. The no-sibling-leaf cases of the full tree target remain open. -/
public import «formalization-leafy-original-realization»
public import «formalization-corona-isomorphisms»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

local instance leafParentVertexFintype (G : SimpleGraph V) : Fintype (LeafParentVertex G) := by
  classical
  exact Fintype.ofFinite (LeafParentVertex G)

omit [DecidableEq V] in
theorem leaf_parent_clique_tree_card_le_two (G : SimpleGraph V) (hG : G.IsTree)
    (hclique : ∀ r c, TreeLeafParent G r → TreeLeafParent G c → r ≠ c → G.Adj r c) :
    Fintype.card (LeafParentVertex G) ≤ 2 := by
  classical
  by_contra h
  have hlarge : 2 < Fintype.card (LeafParentVertex G) := by omega
  obtain ⟨r, c, d, hrc, hrd, hcd⟩ := Fintype.two_lt_card_iff.mp hlarge
  have hrcAdj := hclique r.val c.val r.property c.property (fun heq => hrc (Subtype.ext heq))
  have hrdAdj := hclique r.val d.val r.property d.property (fun heq => hrd (Subtype.ext heq))
  have hcdAdj := hclique c.val d.val c.property d.property (fun heq => hcd (Subtype.ext heq))
  exact hG.isAcyclic.cliqueFree_three {r.val, c.val, d.val}
    (SimpleGraph.is3Clique_triple_iff.mpr ⟨hrcAdj, hrdAdj, hcdAdj⟩)

def leafParentCoreOneIso (G : SimpleGraph V) (hcard : Fintype.card (LeafParentVertex G) = 1) :
    leafParentCore G ≃g (⊥ : SimpleGraph (Fin 1)) := by
  classical
  let e : LeafParentVertex G ≃ Fin 1 := Fintype.equivFinOfCardEq hcard
  exact {
    toEquiv := e
    map_rel_iff' := by
      intro r c
      have hrc : r = c := e.injective (Subsingleton.elim _ _)
      subst c
      simp [leafParentCore] }

def leafParentCoreTwoIso (G : SimpleGraph V) (hcard : Fintype.card (LeafParentVertex G) = 2)
    (hclique : ∀ r c, TreeLeafParent G r → TreeLeafParent G c → r ≠ c → G.Adj r c) :
    leafParentCore G ≃g (⊤ : SimpleGraph (Fin 2)) := by
  classical
  let e : LeafParentVertex G ≃ Fin 2 := Fintype.equivFinOfCardEq hcard
  exact {
    toEquiv := e
    map_rel_iff' := by
      intro r c
      change e r ≠ e c ↔ G.Adj r.val c.val
      constructor
      · intro hne
        exact hclique r.val c.val r.property c.property
          (fun heq => hne (congrArg e (Subtype.ext heq)))
      · intro hAdj heq
        exact hAdj.ne (congrArg Subtype.val (e.injective heq)) }

omit [DecidableEq V] in
theorem original_graph_star_of_one_leaf_parent (G : SimpleGraph V)
    (hpair : ∀ r, TreeLeafParent G r → TreeLeafPairCenter G r)
    (hcover : ∀ x, TreeLeaf G x ∨ TreeLeafParent G x)
    (hcard : Fintype.card (LeafParentVertex G) = 1) :
    ∃ a, 2 ≤ a ∧ Nonempty (G ≃g starModel a) := by
  classical
  let e := leafParentCoreOneIso G hcard
  let a := leafParentAmount G (e.symm 0)
  have hlen : ∀ r, leafParentAmount G r = a := by
    intro r
    have hr : e r = 0 := Subsingleton.elim _ _
    have heq : r = e.symm 0 := by
      apply e.injective
      simpa using hr
    rw [heq]
  have hIso := (leafParentRealizationIso G hpair hcover).symm.trans
    (coronaGraphIso (leafParentCore G) (⊥ : SimpleGraph (Fin 1)) e
      (leafParentAmount G) (fun _ => a) hlen)
  exact ⟨a, leafParentAmount_at_least_two G hpair (e.symm 0), ⟨hIso⟩⟩

omit [DecidableEq V] in
theorem original_graph_double_star_of_two_leaf_parents (G : SimpleGraph V)
    (hpair : ∀ r, TreeLeafParent G r → TreeLeafPairCenter G r)
    (hcover : ∀ x, TreeLeaf G x ∨ TreeLeafParent G x)
    (hclique : ∀ r c, TreeLeafParent G r → TreeLeafParent G c → r ≠ c → G.Adj r c)
    (hcard : Fintype.card (LeafParentVertex G) = 2) :
    ∃ a b, 2 ≤ a ∧ 2 ≤ b ∧ Nonempty (G ≃g doubleStarModel a b) := by
  classical
  let e := leafParentCoreTwoIso G hcard hclique
  let a := leafParentAmount G (e.symm 0)
  let b := leafParentAmount G (e.symm 1)
  have hlen' : ∀ j : Fin 2,
      leafParentAmount G (e.symm j) = if j = 0 then a else b := by
    rw [Fin.forall_fin_two]
    constructor <;> simp [a, b]
  have hlen : ∀ r, leafParentAmount G r = if e r = 0 then a else b := by
    intro r
    simpa using hlen' (e r)
  have hIso := (leafParentRealizationIso G hpair hcover).symm.trans
    (coronaGraphIso (leafParentCore G) (⊤ : SimpleGraph (Fin 2)) e
      (leafParentAmount G) (fun j => if j = 0 then a else b) hlen)
  exact ⟨a, b, leafParentAmount_at_least_two G hpair (e.symm 0),
    leafParentAmount_at_least_two G hpair (e.symm 1), ⟨hIso⟩⟩

theorem tree_cherry_support_iff_star_or_double_star (G : SimpleGraph V) (hG : G.IsTree)
    (hcherry : ∃ c, TreeLeafPairCenter G c) :
    EveryMinimumSupport G.Adj ↔
      (∃ a, 2 ≤ a ∧ Nonempty (G ≃g starModel a)) ∨
      (∃ a b, 2 ≤ a ∧ 2 ≤ b ∧ Nonempty (G ≃g doubleStarModel a b)) := by
  classical
  constructor
  · intro hU
    have hpair := support_cherry_leaf_parent_has_pair G hG.connected hU hcherry
    have hcover := support_cherry_leaf_parent_cover G hG hU hcherry
    have hclique := support_cherry_leaf_parents_clique G hG.connected hU hcherry
    have hcardle := leaf_parent_clique_tree_card_le_two G hG hclique
    have hcherryCopy := hcherry
    obtain ⟨c, a, _, _, hac, ha, _, _⟩ := hcherryCopy
    have : Nonempty (LeafParentVertex G) := ⟨⟨c, a, hac, ha⟩⟩
    have hpos := Fintype.card_pos (α := LeafParentVertex G)
    have hcard : Fintype.card (LeafParentVertex G) = 1 ∨
        Fintype.card (LeafParentVertex G) = 2 := by omega
    rcases hcard with hcard | hcard
    · exact Or.inl (original_graph_star_of_one_leaf_parent G hpair hcover hcard)
    · exact Or.inr (original_graph_double_star_of_two_leaf_parents G hpair hcover hclique hcard)
  · rintro (⟨a, ha, ⟨e⟩⟩ | ⟨a, b, ha, hb, ⟨e⟩⟩)
    · exact support_of_star_iso G a ha e
    · exact support_of_doubleStar_iso G a b ha hb e

end FaultObservationResearch
