module

/-
Geometry needed to place two pendant constructions in the same graph. These
are static bridge tools. No time-separation or full classification is claimed.
-/
public import «formalization-two-pendant-support»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem twoPendant_core_neighbors_from_core_blue (R : SimpleGraph V) (u v : V) (a b : ℕ)
    (C : Finset (TwoPendantVertex V a b)) (hvu : v ≠ u)
    (hc : ∀ x, twoPendantCore V a b x ∈ C) :
    ∀ z, (twoPendantGraph R u a b).Adj (twoPendantCore V a b v) z → z ∈ C := by
  rintro (x | (i | j)) hz
  · exact hc x
  · exact False.elim (hvu hz.1)
  · exact False.elim (hvu hz.1)

theorem twoPendant_heads_step_of_blue_neighbors (R : SimpleGraph V) (root : V) (a b : ℕ)
    (C : Finset (TwoPendantVertex V a b))
    (hr : twoPendantCore V a b root ∈ C)
    (hn : ∀ x, R.Adj root x → twoPendantCore V a b x ∈ C)
    (hh : twoPendantA V a b 0 ∈ C ∨ twoPendantB V a b 0 ∈ C) :
    twoPendantA V a b 0 ∈ synchronousStep (twoPendantGraph R root a b).Adj C ∧
      twoPendantB V a b 0 ∈ synchronousStep (twoPendantGraph R root a b).Adj C := by
  classical
  constructor
  · rcases hh with hA | hB
    · exact subset_synchronousStep _ _ hA
    · apply (mem_synchronousStep _ _ _).mpr
      refine Or.inr ⟨twoPendantCore V a b root, hr, ⟨rfl, rfl⟩, ?_⟩
      intro other ho hw
      rcases other with x | (i | j)
      · exact False.elim (hw (hn x ho))
      · change root = root ∧ i = 0 at ho
        exact congrArg (twoPendantA V a b) ho.2
      · change root = root ∧ j = 0 at ho
        exact False.elim (hw (ho.2 ▸ hB))
  · rcases hh with hA | hB
    · apply (mem_synchronousStep _ _ _).mpr
      refine Or.inr ⟨twoPendantCore V a b root, hr, ⟨rfl, rfl⟩, ?_⟩
      intro other ho hw
      rcases other with x | (i | j)
      · exact False.elim (hw (hn x ho))
      · change root = root ∧ i = 0 at ho
        exact False.elim (hw (ho.2 ▸ hA))
      · change root = root ∧ j = 0 at ho
        exact congrArg (twoPendantB V a b) ho.2
    · exact subset_synchronousStep _ _ hB

omit [Fintype V] [DecidableEq V] in
theorem twoPendant_leaf_A_is_last (R : SimpleGraph V) (root : V) (a b : ℕ)
    (i : Fin (a + 1)) (hleaf : TreeLeaf (twoPendantGraph R root a b) (twoPendantA V a b i)) :
    i = Fin.last a := by
  by_contra hlast
  have hpos : 0 < a := by
    by_contra hn
    apply hlast
    apply Fin.ext
    have := i.isLt
    change i.val = a
    omega
  obtain ⟨neighbor, _, hu⟩ := hleaf
  by_cases hi0 : i = 0
  · subst i
    let next : Fin (a + 1) := ⟨1, by omega⟩
    have hroot : (twoPendantGraph R root a b).Adj
        (twoPendantA V a b 0) (twoPendantCore V a b root) := ⟨rfl, rfl⟩
    have hnext : (twoPendantGraph R root a b).Adj
        (twoPendantA V a b 0) (twoPendantA V a b next) := by
      exact SimpleGraph.pathGraph_adj.mpr (Or.inl rfl)
    have heq := (hu _ hroot).trans (hu _ hnext).symm
    cases heq
  · have hiPos : 0 < i.val := by
      have hn : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
      omega
    have hiLast : i.val ≠ a := fun h => hlast (Fin.ext h)
    have hiLt : i.val < a := by have := i.isLt; omega
    let left : Fin (a + 1) := ⟨i.val - 1, by have := i.isLt; omega⟩
    let right : Fin (a + 1) := ⟨i.val + 1, by omega⟩
    have hleft : (twoPendantGraph R root a b).Adj
        (twoPendantA V a b i) (twoPendantA V a b left) := by
      apply SimpleGraph.pathGraph_adj.mpr
      right
      dsimp [left]
      omega
    have hright : (twoPendantGraph R root a b).Adj
        (twoPendantA V a b i) (twoPendantA V a b right) :=
      SimpleGraph.pathGraph_adj.mpr (Or.inl rfl)
    have heq := (twoPendantA V a b).injective ((hu _ hleft).trans (hu _ hright).symm)
    have hv := congrArg Fin.val heq
    dsimp [left, right] at hv
    omega

omit [Fintype V] [DecidableEq V] in
theorem twoPendant_leaf_B_is_last (R : SimpleGraph V) (root : V) (a b : ℕ)
    (i : Fin (b + 1)) (hleaf : TreeLeaf (twoPendantGraph R root a b) (twoPendantB V a b i)) :
    i = Fin.last b := by
  by_contra hlast
  have hpos : 0 < b := by
    by_contra hn
    apply hlast
    apply Fin.ext
    have := i.isLt
    change i.val = b
    omega
  obtain ⟨neighbor, _, hu⟩ := hleaf
  by_cases hi0 : i = 0
  · subst i
    let next : Fin (b + 1) := ⟨1, by omega⟩
    have hroot : (twoPendantGraph R root a b).Adj
        (twoPendantB V a b 0) (twoPendantCore V a b root) := ⟨rfl, rfl⟩
    have hnext : (twoPendantGraph R root a b).Adj
        (twoPendantB V a b 0) (twoPendantB V a b next) := by
      exact SimpleGraph.pathGraph_adj.mpr (Or.inl rfl)
    have heq := (hu _ hroot).trans (hu _ hnext).symm
    cases heq
  · have hiPos : 0 < i.val := by
      have hn : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
      omega
    have hiLast : i.val ≠ b := fun h => hlast (Fin.ext h)
    have hiLt : i.val < b := by have := i.isLt; omega
    let left : Fin (b + 1) := ⟨i.val - 1, by have := i.isLt; omega⟩
    let right : Fin (b + 1) := ⟨i.val + 1, by omega⟩
    have hleft : (twoPendantGraph R root a b).Adj
        (twoPendantB V a b i) (twoPendantB V a b left) := by
      apply SimpleGraph.pathGraph_adj.mpr
      right
      dsimp [left]
      omega
    have hright : (twoPendantGraph R root a b).Adj
        (twoPendantB V a b i) (twoPendantB V a b right) :=
      SimpleGraph.pathGraph_adj.mpr (Or.inl rfl)
    have heq := (twoPendantB V a b).injective ((hu _ hleft).trans (hu _ hright).symm)
    have hv := congrArg Fin.val heq
    dsimp [left, right] at hv
    omega

def twoPendantCoreAndEnds (V : Type u) [Fintype V] (a b : ℕ) :
    Finset (TwoPendantVertex V a b) := by
  classical
  exact Finset.univ.filter (fun z => match z with
    | Sum.inl _ => True
    | Sum.inr (Sum.inl i) => i = Fin.last a
    | Sum.inr (Sum.inr j) => j = Fin.last b)

omit [DecidableEq V] in
theorem twoPendant_leaves_in_core_and_ends (R : SimpleGraph V) (root : V) (a b : ℕ) :
    ∀ z, TreeLeaf (twoPendantGraph R root a b) z → z ∈ twoPendantCoreAndEnds V a b := by
  classical
  rintro (x | (i | j)) hz
  · simp [twoPendantCoreAndEnds]
  · have hi := twoPendant_leaf_A_is_last R root a b i hz
    simpa [twoPendantCoreAndEnds] using hi
  · have hj := twoPendant_leaf_B_is_last R root a b j hz
    simpa [twoPendantCoreAndEnds] using hj

theorem twoPendant_nested_heads_minimum (R : SimpleGraph V) (u v : V) (a b c d : ℕ)
    (hinner : (twoPendantGraph R u a b).IsTree) :
    IsMinimumKilling
      (twoPendantGraph (twoPendantGraph R u a b) (twoPendantCore V a b v) c d).Adj
      (twoPendantInitial (twoPendantCore V a b v) c d (twoPendantCoreAndEnds V a b))
      (twoPendantHeads (TwoPendantVertex V a b) c d) := by
  classical
  have : Nontrivial (TwoPendantVertex V a b) :=
    ⟨⟨twoPendantA V a b 0, twoPendantB V a b 0, by intro h; cases h⟩⟩
  apply twoPendant_heads_minimum_killing (twoPendantGraph R u a b) hinner
    (twoPendantCore V a b v) c d (twoPendantCoreAndEnds V a b)
  intro x hx _
  exact twoPendant_leaves_in_core_and_ends R u a b x hx

def twoPendantCommuteEquiv (V : Type u) (a b c d : ℕ) :
    TwoPendantVertex (TwoPendantVertex V a b) c d ≃
      TwoPendantVertex (TwoPendantVertex V c d) a b where
  toFun
    | Sum.inl (Sum.inl x) => Sum.inl (Sum.inl x)
    | Sum.inl (Sum.inr p) => Sum.inr p
    | Sum.inr q => Sum.inl (Sum.inr q)
  invFun
    | Sum.inl (Sum.inl x) => Sum.inl (Sum.inl x)
    | Sum.inl (Sum.inr p) => Sum.inr p
    | Sum.inr q => Sum.inl (Sum.inr q)
  left_inv := by rintro ((x | p) | q) <;> rfl
  right_inv := by rintro ((x | p) | q) <;> rfl

def twoPendantCommuteIso (R : SimpleGraph V) (u v : V) (a b c d : ℕ) :
    twoPendantGraph (twoPendantGraph R u a b) (twoPendantCore V a b v) c d ≃g
      twoPendantGraph (twoPendantGraph R v c d) (twoPendantCore V c d u) a b where
  toEquiv := twoPendantCommuteEquiv V a b c d
  map_rel_iff' := by
    rintro ((x | (i | j)) | (k | l)) ((y | (m | n)) | (p | q)) <;>
      simp [twoPendantCommuteEquiv, twoPendantGraph, twoPendantAdj, twoPendantCore]

theorem twoPendant_colorAfter_commute (R : SimpleGraph V) (u v : V) (a b c d : ℕ)
    (blue : Finset (TwoPendantVertex (TwoPendantVertex V a b) c d)) (t : ℕ) :
    relabelColors (twoPendantCommuteEquiv V a b c d)
      (colorAfter
        (twoPendantGraph (twoPendantGraph R u a b) (twoPendantCore V a b v) c d).Adj blue t) =
    colorAfter
      (twoPendantGraph (twoPendantGraph R v c d) (twoPendantCore V c d u) a b).Adj
      (relabelColors (twoPendantCommuteEquiv V a b c d) blue) t := by
  apply colorAfter_relabel
  intro x y
  exact (twoPendantCommuteIso R u v a b c d).map_rel_iff

theorem twoPendant_finishesBy_commute (R : SimpleGraph V) (u v : V) (a b c d : ℕ)
    (blue : Finset (TwoPendantVertex (TwoPendantVertex V a b) c d)) (t : ℕ) :
    FinishesBy
      (twoPendantGraph (twoPendantGraph R v c d) (twoPendantCore V c d u) a b).Adj
      (relabelColors (twoPendantCommuteEquiv V a b c d) blue) t ↔
    FinishesBy
      (twoPendantGraph (twoPendantGraph R u a b) (twoPendantCore V a b v) c d).Adj blue t := by
  apply FinishesBy_relabel_iff
  intro x y
  exact (twoPendantCommuteIso R u v a b c d).map_rel_iff

end FaultObservationResearch
