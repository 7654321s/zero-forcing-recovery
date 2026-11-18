module

/-
Ordinary forcing can be embedded when every additional neighbor is already blue.
This is a standard monotone simulation tool, not a claim of novelty. It is kept
separate from root-inactive embedding and from equality of completion times.
-/
public import «formalization-embedding»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch

universe u v
variable {V : Type u} {W : Type v}
variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem colorAfter_embeds_with_blue_exterior (H : SimpleGraph V) (G : SimpleGraph W)
    (e : V ↪ W) (hmap : ∀ {x y : V}, H.Adj x y → G.Adj (e x) (e y))
    (blue : Finset V) (bigBlue : Finset W)
    (hneighbors : ∀ x : V, ∀ z : W, G.Adj (e x) z →
      (∃ y : V, z = e y ∧ H.Adj x y) ∨ z ∈ bigBlue)
    (hinitial : ∀ x ∈ blue, e x ∈ bigBlue) (t : ℕ) :
    ∀ x ∈ colorAfter H.Adj blue t, e x ∈ colorAfter G.Adj bigBlue t := by
  induction t with
  | zero => exact hinitial
  | succ t ih =>
    intro x hx
    apply (mem_synchronousStep G.Adj (colorAfter G.Adj bigBlue t) (e x)).mpr
    rcases (mem_synchronousStep H.Adj (colorAfter H.Adj blue t) x).mp hx with
      hx | ⟨source, hs, ha, hu⟩
    · exact Or.inl (ih x hx)
    · refine Or.inr ⟨e source, ih source hs, hmap ha, ?_⟩
      intro other hother hwhite
      rcases hneighbors source other hother with ⟨y, rfl, hy⟩ | hblue
      · have hyWhite : y ∉ colorAfter H.Adj blue t := fun h => hwhite (ih y h)
        exact congrArg e (hu y hy hyWhite)
      · exact False.elim (hwhite (colorAfter_mono_time G.Adj bigBlue (Nat.zero_le t) hblue))

theorem forcing_embedding_with_blue_exterior_colors_image (H : SimpleGraph V)
    (G : SimpleGraph W) (e : V ↪ W)
    (hmap : ∀ {x y : V}, H.Adj x y → G.Adj (e x) (e y))
    (blue : Finset V) (bigBlue : Finset W)
    (hneighbors : ∀ x : V, ∀ z : W, G.Adj (e x) z →
      (∃ y : V, z = e y ∧ H.Adj x y) ∨ z ∈ bigBlue)
    (hinitial : ∀ x ∈ blue, e x ∈ bigBlue) (hforcing : IsForcing H.Adj blue) :
    ∀ x : V, e x ∈ colorAfter G.Adj bigBlue (Fintype.card V) := by
  intro x
  apply colorAfter_embeds_with_blue_exterior H G e hmap blue bigBlue hneighbors hinitial
  have hfull := IsForcing_finishes_card H.Adj blue hforcing
  change colorAfter H.Adj blue (Fintype.card V) = Finset.univ at hfull
  rw [hfull]
  exact Finset.mem_univ x

theorem forcing_of_embedding_and_blue_complement (H : SimpleGraph V)
    (G : SimpleGraph W) (e : V ↪ W)
    (hmap : ∀ {x y : V}, H.Adj x y → G.Adj (e x) (e y))
    (blue : Finset V) (bigBlue : Finset W)
    (hneighbors : ∀ x : V, ∀ z : W, G.Adj (e x) z →
      (∃ y : V, z = e y ∧ H.Adj x y) ∨ z ∈ bigBlue)
    (hinitial : ∀ x ∈ blue, e x ∈ bigBlue) (hforcing : IsForcing H.Adj blue)
    (hcover : ∀ z : W, (∃ x : V, z = e x) ∨ z ∈ bigBlue) : IsForcing G.Adj bigBlue := by
  refine ⟨Fintype.card V, Finset.eq_univ_of_forall ?_⟩
  intro z
  rcases hcover z with ⟨x, rfl⟩ | hz
  · exact forcing_embedding_with_blue_exterior_colors_image H G e hmap blue bigBlue
      hneighbors hinitial hforcing x
  · exact colorAfter_mono_time G.Adj bigBlue (Nat.zero_le _) hz

theorem IsForcing_of_forcing_colorAfter (adj : V → V → Prop) (blue : Finset V) (t : ℕ)
    (hforcing : IsForcing adj (colorAfter adj blue t)) : IsForcing adj blue := by
  obtain ⟨s, hs⟩ := hforcing
  refine ⟨t + s, ?_⟩
  change colorAfter adj blue (t + s) = Finset.univ
  rw [colorAfter_add]
  exact hs

end FaultObservationResearch
