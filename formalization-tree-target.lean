module

/-
Exact statement of the candidate full tree classification and proved transports
of the already verified positive families. The full classification is a target
proposition, not a theorem in this file.
-/
public import «formalization-leafy-core»
public import «formalization-transport»
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Hasse

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace FaultObservationResearch

universe u v

def coronaGraph {I : Type u} (core : SimpleGraph I) (amount : I → ℕ) :
    SimpleGraph (CoronaVertex I amount) where
  Adj := coronaAdj core amount
  symm := ⟨coronaAdj_symmetric core amount⟩
  loopless := ⟨coronaAdj_irreflexive core amount⟩

def starModel (a : ℕ) : SimpleGraph (CoronaVertex (Fin 1) (fun _ => a)) :=
  coronaGraph (⊥ : SimpleGraph (Fin 1)) (fun _ => a)

def doubleStarModel (a b : ℕ) :
    SimpleGraph (CoronaVertex (Fin 2) (fun i => if i = 0 then a else b)) :=
  coronaGraph (⊤ : SimpleGraph (Fin 2)) (fun i => if i = 0 then a else b)

/-- The path branch includes one- and two-vertex stars. All graph labels are allowed. -/
def InTreeCandidateClass {V : Type u} (G : SimpleGraph V) : Prop :=
  (∃ n : ℕ, 1 ≤ n ∧ Nonempty (G ≃g SimpleGraph.pathGraph n)) ∨
  (∃ a : ℕ, 2 ≤ a ∧ Nonempty (G ≃g starModel a)) ∨
  (∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ Nonempty (G ≃g doubleStarModel a b))

/-- An unproved target: every finite nonempty tree, with every B/H/budget quantifier. -/
def FullTreeClassificationTarget (V : Type u) [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) : Prop :=
  G.IsTree → (EveryMinimumSupport G.Adj ↔ InTreeCandidateClass G)

/-- The complete candidate statement. Defining it does not prove it. -/
def FullTreeClassificationStatement : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V),
    FullTreeClassificationTarget V G

theorem canonical_star_support (a : ℕ) (ha : 2 ≤ a) :
    EveryMinimumSupport (starModel a).Adj := by
  change EveryMinimumSupport (coronaAdj (⊥ : SimpleGraph (Fin 1)) (fun _ => a))
  apply leafy_complete_every_minimum_support
  · intro i
    exact ha
  · intro i j hne
    exact False.elim (hne (Subsingleton.elim i j))

theorem canonical_doubleStar_support (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    EveryMinimumSupport (doubleStarModel a b).Adj := by
  change EveryMinimumSupport
    (coronaAdj (⊤ : SimpleGraph (Fin 2)) (fun i => if i = 0 then a else b))
  apply leafy_complete_every_minimum_support
  · intro i
    by_cases hi : i = 0
    · simpa only [hi, ite_true] using ha
    · simpa only [hi, ite_false] using hb
  · intro i j hne
    exact hne

variable {V : Type u} {W : Type v}

theorem InTreeCandidateClass_iso_iff (G : SimpleGraph V) (H : SimpleGraph W)
    (e : G ≃g H) : InTreeCandidateClass G ↔ InTreeCandidateClass H := by
  constructor
  · intro h
    rcases h with ⟨n, hn, ⟨f⟩⟩ | ⟨a, ha, ⟨f⟩⟩ | ⟨a, b, ha, hb, ⟨f⟩⟩
    · exact Or.inl ⟨n, hn, ⟨e.symm.trans f⟩⟩
    · exact Or.inr (Or.inl ⟨a, ha, ⟨e.symm.trans f⟩⟩)
    · exact Or.inr (Or.inr ⟨a, b, ha, hb, ⟨e.symm.trans f⟩⟩)
  · intro h
    rcases h with ⟨n, hn, ⟨f⟩⟩ | ⟨a, ha, ⟨f⟩⟩ | ⟨a, b, ha, hb, ⟨f⟩⟩
    · exact Or.inl ⟨n, hn, ⟨e.trans f⟩⟩
    · exact Or.inr (Or.inl ⟨a, ha, ⟨e.trans f⟩⟩)
    · exact Or.inr (Or.inr ⟨a, b, ha, hb, ⟨e.trans f⟩⟩)

variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem support_of_star_iso (G : SimpleGraph V) (a : ℕ) (ha : 2 ≤ a)
    (e : G ≃g starModel a) : EveryMinimumSupport G.Adj :=
  (EveryMinimumSupport_iso_iff G (starModel a) e).mpr (canonical_star_support a ha)

theorem support_of_doubleStar_iso (G : SimpleGraph V) (a b : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (e : G ≃g doubleStarModel a b) :
    EveryMinimumSupport G.Adj :=
  (EveryMinimumSupport_iso_iff G (doubleStarModel a b) e).mpr
    (canonical_doubleStar_support a b ha hb)

theorem FullTreeClassificationTarget_iso_iff [Nonempty V] [Nonempty W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : G ≃g H) :
    FullTreeClassificationTarget V G ↔ FullTreeClassificationTarget W H := by
  unfold FullTreeClassificationTarget
  rw [e.isTree_iff, EveryMinimumSupport_iso_iff G H e, InTreeCandidateClass_iso_iff G H e]

end FaultObservationResearch
