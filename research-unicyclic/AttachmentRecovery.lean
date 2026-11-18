module

public import AttachmentTiming

@[expose] public section

set_option autoImplicit false

namespace FaultObservationResearch

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- After recovery of the old graph, a pendant path always finishes,
even if its initial head was lost. -/
theorem attached_path_forces_after_core (core : V → V → Prop) (root : V) (n : ℕ)
    (large : Finset (V ⊕ Fin (n + 1))) (r : ℕ)
    (recovered : ∀ x, Sum.inl x ∈
      colorAfter (attachAtAdj core (SimpleGraph.pathGraph (n + 1)).Adj root 0) large r) :
    IsForcing (attachAtAdj core (SimpleGraph.pathGraph (n + 1)).Adj root 0) large := by
  classical
  let tail := (SimpleGraph.pathGraph (n + 1)).Adj
  let joined := attachAtAdj core tail root 0
  let active := colorAfter joined large (r + 1)
  have hHead : Sum.inr (0 : Fin (n + 1)) ∈ active := by
    change Sum.inr (0 : Fin (n + 1)) ∈ synchronousStep joined (colorAfter joined large r)
    refine (mem_synchronousStep _ _ _).mpr (Or.inr ⟨.inl root, recovered root, ⟨rfl, rfl⟩, ?_⟩)
    intro a ha haWhite
    cases a with
    | inl x => exact False.elim (haWhite (recovered x))
    | inr j =>
      change root = root ∧ j = 0 at ha
      exact congrArg Sum.inr ha.2
  let side := Finset.univ.filter (fun i : Fin (n + 1) => Sum.inr i ∈ active)
  have hSide : ∀ i, Sum.inr i ∈ active ↔ i ∈ side := by
    intro i
    simp [side]
  have hRoot : Sum.inl root ∈ active := colorAfter_subset_succ joined large r (recovered root)
  have hShift := attachAt_tail_colorAfter_of_blue_bridge core tail root 0 active side
    hSide hRoot ((hSide 0).mp hHead) n
  refine ⟨r + 1 + n, Finset.eq_univ_of_forall ?_⟩
  intro a
  cases a with
  | inl x => exact colorAfter_mono_time joined large (by omega) (recovered x)
  | inr i =>
    change Sum.inr i ∈ colorAfter joined large (r + 1 + n)
    rw [colorAfter_add]
    apply (hShift i).mpr
    apply colorAfter_mono_blue tail (A := {0}) (B := side) _ n
      ((path_colorAfter_single_first n n i).mpr (by have := i.isLt; omega))
    exact Finset.singleton_subset_iff.mpr ((hSide 0).mp hHead)

theorem attached_path_forces_with_blue_head (core : V → V → Prop) (root : V) (n : ℕ)
    (old : Finset V) (large : Finset (V ⊕ Fin (n + 1)))
    (initial : ∀ x ∈ old, Sum.inl x ∈ large) (head : Sum.inr (0 : Fin (n + 1)) ∈ large)
    (forcing : IsForcing core old) :
    IsForcing (attachAtAdj core (SimpleGraph.pathGraph (n + 1)).Adj root 0) large := by
  obtain ⟨r, hr⟩ := forcing
  apply attached_path_forces_after_core core root n large r
  intro x
  apply attachAt_contains_core core _ root 0 old large True (fun _ => head) initial r x
  simp only [or_true, and_true]
  rw [show colorAfter core old r = Finset.univ from hr]
  exact Finset.mem_univ _

theorem attached_path_forces_with_root_suppressed (core : V → V → Prop) (root : V) (n : ℕ)
    (old : Finset V) (large : Finset (V ⊕ Fin (n + 1)))
    (initial : ∀ x ∈ old, Sum.inl x ∈ large)
    (forcing : IsForcing (fun x y => core x y ∧ x ≠ root) old) :
    IsForcing (attachAtAdj core (SimpleGraph.pathGraph (n + 1)).Adj root 0) large := by
  obtain ⟨r, hr⟩ := forcing
  apply attached_path_forces_after_core core root n large r
  intro x
  apply attachAt_contains_core core _ root 0 old large False False.elim initial r x
  simp only [or_false]
  rw [show colorAfter (fun x y => core x y ∧ x ≠ root) old r = Finset.univ from hr]
  exact Finset.mem_univ _

/-- For an all-blue path of length at least two, the second vertex repairs
a lost head in round one, irrespective of the coloring of the core. -/
theorem blue_path_head_repaired_in_one (core : V → V → Prop) (root : V)
    (n : ℕ) (hLength : 0 < n) (large : Finset (V ⊕ Fin (n + 1)))
    (survive : ∀ i : Fin (n + 1), i ≠ 0 → Sum.inr i ∈ large) :
    Sum.inr (0 : Fin (n + 1)) ∈ synchronousStep
      (attachAtAdj core (SimpleGraph.pathGraph (n + 1)).Adj root 0) large := by
  let second : Fin (n + 1) := ⟨1, by omega⟩
  have hVal : second.val = 1 := rfl
  have hSecond : second ≠ 0 := by
    intro h
    have heq := congrArg Fin.val h
    change 1 = 0 at heq
    omega
  apply (mem_synchronousStep _ _ _).mpr
  refine Or.inr ⟨.inr second, survive second hSecond,
    SimpleGraph.pathGraph_adj.mpr (Or.inr rfl), ?_⟩
  intro a ha haWhite
  cases a with
  | inl x =>
    change second = 0 ∧ x = root at ha
    exact False.elim (hSecond ha.1)
  | inr j =>
    by_contra hJ
    exact haWhite (survive j (fun h => hJ (congrArg Sum.inr h)))

end FaultObservationResearch

#print axioms FaultObservationResearch.attached_path_forces_with_blue_head
#print axioms FaultObservationResearch.attached_path_forces_with_root_suppressed
#print axioms FaultObservationResearch.blue_path_head_repaired_in_one
