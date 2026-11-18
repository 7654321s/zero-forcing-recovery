module

/-
Standard finite packing/hitting tools for preserving EVERY minimum killing set.
This file does not construct the path decomposition or prove path time support.
-/
public import «formalization-path-forcing»
public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace FaultObservationResearch

universe u v

variable {I : Type u} {V : Type v}
variable [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]

def DisjointForcingCells (cells : I → Finset V) : Prop :=
  ∀ i j : I, i ≠ j → Disjoint (cells i) (cells j)

def ExactCellSelection (cells : I → Finset V) (support : Finset V) (pick : I → V) : Prop :=
  Function.Injective pick ∧ (∀ i, pick i ∈ cells i) ∧
    support = Finset.univ.image pick ∧ ∀ i, support ∩ cells i = {pick i}

theorem minimumKilling_hits_forcing_subset (adj : V → V → Prop)
    (blue support cell : Finset V) (hminimum : IsMinimumKilling adj blue support)
    (hsub : cell ⊆ blue) (hforcing : IsForcing adj cell) :
    ∃ x ∈ cell, x ∈ support := by
  classical
  by_contra hnot
  have hremain : cell ⊆ blue \ support := by
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨hsub hx, fun hs => hnot ⟨x, hx, hs⟩⟩
  exact hminimum.2.1 (IsForcing_mono adj hremain hforcing)

omit [Fintype I] [Fintype V] [DecidableEq V] in
theorem disjoint_cells_selection_injective (cells : I → Finset V)
    (hdis : DisjointForcingCells cells) (pick : I → V) (hp : ∀ i, pick i ∈ cells i) :
    Function.Injective pick := by
  intro i j heq
  by_contra hne
  have hj : pick i ∈ cells j := by rw [heq]; exact hp j
  exact (Finset.disjoint_left.mp (hdis i j hne)) (hp i) hj

omit [Fintype I] [Fintype V] [DecidableEq V] in
theorem exists_injective_cell_pick (cells : I → Finset V) (hdis : DisjointForcingCells cells)
    (support : Finset V) (hhit : ∀ i, ∃ x ∈ cells i, x ∈ support) :
    ∃ pick : I → V, Function.Injective pick ∧ ∀ i, pick i ∈ cells i ∧ pick i ∈ support := by
  classical
  let pick : I → V := fun i => Classical.choose (hhit i)
  have hp : ∀ i, pick i ∈ cells i ∧ pick i ∈ support :=
    fun i => Classical.choose_spec (hhit i)
  exact ⟨pick, disjoint_cells_selection_injective cells hdis pick (fun i => (hp i).1), hp⟩

omit [Fintype V] in
theorem disjoint_cells_hitting_card_le (cells : I → Finset V) (hdis : DisjointForcingCells cells)
    (support : Finset V) (hhit : ∀ i, ∃ x ∈ cells i, x ∈ support) :
    Fintype.card I ≤ support.card := by
  classical
  obtain ⟨pick, hinj, hp⟩ := exists_injective_cell_pick cells hdis support hhit
  have hsub : Finset.univ.image pick ⊆ support := by
    intro x hx
    obtain ⟨i, _, heq⟩ := Finset.mem_image.mp hx
    rw [← heq]
    exact (hp i).2
  have hcard : (Finset.univ.image pick).card = Fintype.card I := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  rw [← hcard]
  exact Finset.card_le_card hsub

omit [Fintype V] in
theorem exists_exact_cell_selector (cells : I → Finset V) (hdis : DisjointForcingCells cells)
    (support : Finset V) (hhit : ∀ i, ∃ x ∈ cells i, x ∈ support)
    (hcard : support.card = Fintype.card I) :
    ∃ pick : I → V, ExactCellSelection cells support pick := by
  classical
  obtain ⟨pick, hinj, hp⟩ := exists_injective_cell_pick cells hdis support hhit
  have hsub : Finset.univ.image pick ⊆ support := by
    intro x hx
    obtain ⟨i, _, heq⟩ := Finset.mem_image.mp hx
    rw [← heq]
    exact (hp i).2
  have himageCard : (Finset.univ.image pick).card = Fintype.card I := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  have himage : Finset.univ.image pick = support :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard, himageCard])
  refine ⟨pick, hinj, (fun i => (hp i).1), himage.symm, ?_⟩
  intro i
  ext x
  constructor
  · intro hx
    have hxH := (Finset.mem_inter.mp hx).1
    have hxC := (Finset.mem_inter.mp hx).2
    have hxImage : x ∈ Finset.univ.image pick := by rw [himage]; exact hxH
    obtain ⟨j, _, heq⟩ := Finset.mem_image.mp hxImage
    have hji : j = i := by
      by_contra hne
      have hIn : pick j ∈ cells i := by rw [heq]; exact hxC
      exact (Finset.disjoint_left.mp (hdis j i hne)) (hp j).1 hIn
    subst j
    exact Finset.mem_singleton.mpr heq.symm
  · intro hx
    have heq := Finset.mem_singleton.mp hx
    subst x
    exact Finset.mem_inter.mpr ⟨(hp i).2, (hp i).1⟩

theorem minimumKilling_card_eq_disjoint_forcing_cells (adj : V → V → Prop)
    (blue support witness : Finset V) (cells : I → Finset V)
    (hdis : DisjointForcingCells cells) (hcell : ∀ i, cells i ⊆ blue)
    (hforce : ∀ i, IsForcing adj (cells i)) (hminimum : IsMinimumKilling adj blue support)
    (hwitness : witness ⊆ blue) (hfail : ¬ IsForcing adj (blue \ witness))
    (hwcard : witness.card = Fintype.card I) : support.card = Fintype.card I := by
  have hhit : ∀ i, ∃ x ∈ cells i, x ∈ support :=
    fun i => minimumKilling_hits_forcing_subset adj blue support (cells i) hminimum (hcell i) (hforce i)
  have hlower := disjoint_cells_hitting_card_le cells hdis support hhit
  have hupper := ((IsMinimumKilling_iff_card_minimum adj blue support).mp hminimum).2.2
    witness hwitness hfail
  omega

theorem minimumKilling_exact_cell_selector (adj : V → V → Prop)
    (blue support witness : Finset V) (cells : I → Finset V)
    (hdis : DisjointForcingCells cells) (hcell : ∀ i, cells i ⊆ blue)
    (hforce : ∀ i, IsForcing adj (cells i)) (hminimum : IsMinimumKilling adj blue support)
    (hwitness : witness ⊆ blue) (hfail : ¬ IsForcing adj (blue \ witness))
    (hwcard : witness.card = Fintype.card I) :
    ∃ pick : I → V, ExactCellSelection cells support pick := by
  apply exists_exact_cell_selector cells hdis support
  · exact fun i => minimumKilling_hits_forcing_subset adj blue support (cells i)
      hminimum (hcell i) (hforce i)
  · exact minimumKilling_card_eq_disjoint_forcing_cells adj blue support witness cells
      hdis hcell hforce hminimum hwitness hfail hwcard

omit [DecidableEq I] [Fintype V] in
theorem exact_cell_selection_subfamily_card (cells : I → Finset V) (support : Finset V)
    (pick : I → V) (hselection : ExactCellSelection cells support pick) (subfamily : Finset I) :
    subfamily.image pick ⊆ support ∧ (subfamily.image pick).card = subfamily.card := by
  classical
  constructor
  · rw [hselection.2.2.1]
    intro x hx
    obtain ⟨i, _, heq⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, heq⟩
  · exact Finset.card_image_of_injective subfamily hselection.1

omit [Fintype V] in
theorem damaged_disjoint_cells_card_le_loss (cells : I → Finset V)
    (hdis : DisjointForcingCells cells) (loss : Finset V) :
    (Finset.univ.filter (fun i => ∃ x ∈ cells i, x ∈ loss)).card ≤ loss.card := by
  classical
  let damaged := Finset.univ.filter (fun i => ∃ x ∈ cells i, x ∈ loss)
  have hdis' : DisjointForcingCells (fun i : {i : I // i ∈ damaged} => cells i.val) := by
    intro i j hne
    exact hdis i.val j.val (fun h => hne (Subtype.ext h))
  have hhit : ∀ i : {i : I // i ∈ damaged}, ∃ x ∈ cells i.val, x ∈ loss :=
    fun i => (Finset.mem_filter.mp i.property).2
  have hcard := disjoint_cells_hitting_card_le
    (fun i : {i : I // i ∈ damaged} => cells i.val) hdis' loss hhit
  change damaged.card ≤ loss.card
  simpa only [Fintype.card_coe] using hcard

end FaultObservationResearch
