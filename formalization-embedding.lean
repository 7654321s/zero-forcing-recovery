module

/-
Simulation of root-inactive forcing inside a larger graph.
The root is the only vertex allowed to have additional external neighbors.
Only the embedded image is asserted to become blue. These are structural
proof tools, not a claim of novelty or of equality of pruned completion times.
-/
public import «formalization-rooted-leaves»

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace FaultObservationResearch

universe u v

variable {V : Type u} {W : Type v}
variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem rooted_colorAfter_embeds (H : SimpleGraph V) (root : V)
    (G : SimpleGraph W) (e : V ↪ W)
    (hmap : ∀ {x y : V}, H.Adj x y → G.Adj (e x) (e y))
    (hneighbors : ∀ x : V, x ≠ root → ∀ z : W,
      G.Adj (e x) z → ∃ y : V, z = e y ∧ H.Adj x y)
    (blue : Finset V) (bigBlue : Finset W)
    (hinitial : ∀ x ∈ blue, e x ∈ bigBlue) (t : ℕ) :
    ∀ x ∈ colorAfter (rootInactiveAdj H root) blue t,
      e x ∈ colorAfter G.Adj bigBlue t := by
  induction t with
  | zero => exact hinitial
  | succ t ih =>
    intro x hx
    apply (mem_synchronousStep G.Adj (colorAfter G.Adj bigBlue t) (e x)).mpr
    rcases (mem_synchronousStep (rootInactiveAdj H root)
      (colorAfter (rootInactiveAdj H root) blue t) x).mp hx with
      hx | ⟨source, hs, ha, hu⟩
    · exact Or.inl (ih x hx)
    · refine Or.inr ⟨e source, ih source hs, hmap ha.2, ?_⟩
      intro other hother hwhite
      obtain ⟨y, rfl, hy⟩ := hneighbors source ha.1 other hother
      have hyWhite : y ∉ colorAfter (rootInactiveAdj H root) blue t :=
        fun h => hwhite (ih y h)
      exact congrArg e (hu y ⟨ha.1, hy⟩ hyWhite)

theorem rooted_leaf_embedding_colors_image [Nontrivial V]
    (H : SimpleGraph V) (htree : H.IsTree) (root : V)
    (G : SimpleGraph W) (e : V ↪ W)
    (hmap : ∀ {x y : V}, H.Adj x y → G.Adj (e x) (e y))
    (hneighbors : ∀ x : V, x ≠ root → ∀ z : W,
      G.Adj (e x) z → ∃ y : V, z = e y ∧ H.Adj x y)
    (blue : Finset V) (bigBlue : Finset W)
    (hleaves : ∀ x : V, TreeLeaf H x → x ≠ root → x ∈ blue)
    (hinitial : ∀ x ∈ blue, e x ∈ bigBlue) :
    ∀ x : V, e x ∈ colorAfter G.Adj bigBlue (Fintype.card V) := by
  intro x
  apply rooted_colorAfter_embeds H root G e hmap hneighbors blue bigBlue hinitial
  have hfull := rooted_leaves_finish_card H htree root blue hleaves
  change colorAfter (rootInactiveAdj H root) blue (Fintype.card V) = Finset.univ at hfull
  rw [hfull]
  exact Finset.mem_univ x

theorem rootInactive_colorAfter_subset (G : SimpleGraph V) (root : V)
    (blue : Finset V) (t : ℕ) :
    colorAfter (rootInactiveAdj G root) blue t ⊆ colorAfter G.Adj blue t := by
  exact rooted_colorAfter_embeds G root G (Function.Embedding.refl V)
    (fun h => h) (fun _ _ z h => ⟨z, rfl, h⟩) blue blue (fun _ h => h) t

theorem rooted_leaves_finish_card_ordinary [Nontrivial V]
    (G : SimpleGraph V) (htree : G.IsTree) (root : V) (blue : Finset V)
    (hleaves : ∀ x : V, TreeLeaf G x → x ≠ root → x ∈ blue) :
    FinishesBy G.Adj blue (Fintype.card V) := by
  have hfull := rooted_leaves_finish_card G htree root blue hleaves
  apply Finset.eq_univ_of_forall
  intro x
  apply rootInactive_colorAfter_subset G root blue (Fintype.card V)
  change colorAfter (rootInactiveAdj G root) blue (Fintype.card V) = Finset.univ at hfull
  rw [hfull]
  exact Finset.mem_univ x

theorem rooted_leaves_forcing_ordinary [Nontrivial V]
    (G : SimpleGraph V) (htree : G.IsTree) (root : V) (blue : Finset V)
    (hleaves : ∀ x : V, TreeLeaf G x → x ≠ root → x ∈ blue) :
    IsForcing G.Adj blue :=
  ⟨Fintype.card V, rooted_leaves_finish_card_ordinary G htree root blue hleaves⟩

end FaultObservationResearch
