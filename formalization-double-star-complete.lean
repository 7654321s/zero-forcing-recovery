module

/-
The exact original DoubleStarTarget, including the four-vertex path boundary.
The four-vertex calculation is bridged to the unbounded budget/deadline
statement by the proved finite-check equivalence. The full tree target is
not asserted by this component.
-/
public import «formalization-finite-check»
public import «formalization-corona-isomorphisms»

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace FaultObservationResearch

def doubleStar11ToFourPath (x : BroomVertex 1) : Fin 4 :=
  match x with
  | Sum.inl i => if i = 0 then 1 else 2
  | Sum.inr leaf => if leaf.1 = 0 then 0 else 3

def fourPathToDoubleStar11 (j : Fin 4) : BroomVertex 1 :=
  if j = 0 then broomShortLeaf 1
  else if j = 1 then Sum.inl 0
  else if j = 2 then Sum.inl 1
  else broomLongLeaf 1 (0 : Fin 1)

theorem fin_four_vertex_cases (j : Fin 4) : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by
  have hv : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by
    have := j.isLt
    omega
  rcases hv with h | h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))

def doubleStar11VertexEquiv : BroomVertex 1 ≃ Fin 4 where
  toFun := doubleStar11ToFourPath
  invFun := fourPathToDoubleStar11
  left_inv := by
    intro x
    cases x with
    | inl i =>
      rcases fin_two_vertex_cases i with rfl | rfl <;> rfl
    | inr leaf =>
      rcases leaf with ⟨i, j⟩
      rcases fin_two_vertex_cases i with rfl | rfl
      · have hj : j = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
        subst j
        rfl
      · have hj : j = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
        subst j
        rfl
  right_inv := by
    intro j
    rcases fin_four_vertex_cases j with rfl | rfl | rfl | rfl <;> rfl

def doubleStar11PathIso : doubleStarModel 1 1 ≃g SimpleGraph.pathGraph 4 where
  toEquiv := doubleStar11VertexEquiv
  map_rel_iff' := by
    intro x y
    change (SimpleGraph.pathGraph 4).Adj (doubleStar11ToFourPath x)
      (doubleStar11ToFourPath y) ↔ (doubleStarModel 1 1).Adj x y
    rw [SimpleGraph.pathGraph_adj]
    rcases x with i | ⟨i, j⟩ <;> rcases y with k | ⟨k, l⟩
    all_goals rcases fin_two_vertex_cases i with rfl | rfl
    all_goals rcases fin_two_vertex_cases k with rfl | rfl
    all_goals simp [doubleStar11ToFourPath,
      doubleStarModel, coronaGraph, coronaAdj]

theorem pathGraph_four_support : EveryMinimumSupport (SimpleGraph.pathGraph 4).Adj := by
  have heq : (SimpleGraph.pathGraph 4).Adj = fourPathAdj := by
    funext x y
    exact propext SimpleGraph.pathGraph_adj
  rw [heq]
  exact fourPath_every_minimum_support

theorem doubleStar_one_one_support : EveryMinimumSupport (doubleStarModel 1 1).Adj :=
  (EveryMinimumSupport_iso_iff _ _ doubleStar11PathIso).mpr pathGraph_four_support

theorem doubleStarTarget_proved : DoubleStarTarget := by
  intro a b ha hb
  change EveryMinimumSupport (doubleStarModel a b).Adj ↔
    ((a = 1 ∧ b = 1) ∨ (2 ≤ a ∧ 2 ≤ b))
  constructor
  · intro h
    by_cases ha1 : a = 1
    · by_cases hb1 : b = 1
      · exact Or.inl ⟨ha1, hb1⟩
      · have hb2 : 2 ≤ b := by omega
        subst a
        exact False.elim (doubleStar_one_leaf_not_support b hb2 h)
    · by_cases hb1 : b = 1
      · have ha2 : 2 ≤ a := by omega
        subst b
        exact False.elim (doubleStar_other_one_leaf_not_support a ha2 h)
      · exact Or.inr ⟨by omega, by omega⟩
  · rintro (⟨rfl, rfl⟩ | ⟨ha2, hb2⟩)
    · exact doubleStar_one_one_support
    · exact canonical_doubleStar_support a b ha2 hb2

universe u

theorem doubleStar_support_iff_of_iso {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (e : G ≃g doubleStarModel a b) :
    EveryMinimumSupport G.Adj ↔ ((a = 1 ∧ b = 1) ∨ (2 ≤ a ∧ 2 ≤ b)) :=
  (EveryMinimumSupport_iso_iff G (doubleStarModel a b) e).trans
    (doubleStarTarget_proved a b ha hb)

end FaultObservationResearch
