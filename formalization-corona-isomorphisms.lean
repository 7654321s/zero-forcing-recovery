module

/-
Graph isomorphisms for the attached-leaf models, including center exchange.
These are transport tools; this development source has no novelty claim.
-/
public import «formalization-double-star-boundary»

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace FaultObservationResearch

universe u v

def coronaRelabelEquiv {I : Type u} {J : Type v} (e : I ≃ J)
    (amountI : I → ℕ) (amountJ : J → ℕ)
    (hlen : ∀ i : I, amountI i = amountJ (e i)) :
    CoronaVertex I amountI ≃ CoronaVertex J amountJ :=
  Equiv.sumCongr e (Equiv.sigmaCongr e (fun i => finCongr (hlen i)))

theorem coronaAdj_relabel_iff {I : Type u} {J : Type v}
    (coreI : SimpleGraph I) (coreJ : SimpleGraph J) (e : I ≃ J)
    (amountI : I → ℕ) (amountJ : J → ℕ)
    (hlen : ∀ i : I, amountI i = amountJ (e i))
    (hcore : ∀ i j : I, coreJ.Adj (e i) (e j) ↔ coreI.Adj i j)
    (x y : CoronaVertex I amountI) :
    coronaAdj coreJ amountJ (coronaRelabelEquiv e amountI amountJ hlen x)
      (coronaRelabelEquiv e amountI amountJ hlen y) ↔ coronaAdj coreI amountI x y := by
  cases x with
  | inl i =>
    cases y with
    | inl j => exact hcore i j
    | inr leaf =>
      change e i = e leaf.1 ↔ i = leaf.1
      exact e.injective.eq_iff
  | inr leaf =>
    cases y with
    | inl j =>
      change e leaf.1 = e j ↔ leaf.1 = j
      exact e.injective.eq_iff
    | inr other => exact Iff.rfl

def coronaGraphIso {I : Type u} {J : Type v}
    (coreI : SimpleGraph I) (coreJ : SimpleGraph J) (e : coreI ≃g coreJ)
    (amountI : I → ℕ) (amountJ : J → ℕ)
    (hlen : ∀ i : I, amountI i = amountJ (e i)) :
    coronaGraph coreI amountI ≃g coronaGraph coreJ amountJ where
  toEquiv := coronaRelabelEquiv e.toEquiv amountI amountJ hlen
  map_rel_iff' := by
    intro x y
    exact coronaAdj_relabel_iff coreI coreJ e.toEquiv amountI amountJ hlen
      (fun _ _ => e.map_rel_iff) x y

def twoCoreSwapIso : (⊤ : SimpleGraph (Fin 2)) ≃g (⊤ : SimpleGraph (Fin 2)) where
  toEquiv := Equiv.swap 0 1
  map_rel_iff' := by
    intro i j
    change (Equiv.swap (0 : Fin 2) 1 i ≠ Equiv.swap (0 : Fin 2) 1 j) ↔ i ≠ j
    exact not_congr (Equiv.swap (0 : Fin 2) 1).injective.eq_iff

def doubleStarSwapIso (a b : ℕ) : doubleStarModel a b ≃g doubleStarModel b a := by
  apply coronaGraphIso (⊤ : SimpleGraph (Fin 2)) (⊤ : SimpleGraph (Fin 2)) twoCoreSwapIso
    (fun i => if i = 0 then a else b) (fun i => if i = 0 then b else a)
  rw [Fin.forall_fin_two]
  constructor <;> simp [twoCoreSwapIso]

theorem doubleStar_support_swap_iff (a b : ℕ) :
    EveryMinimumSupport (doubleStarModel a b).Adj ↔
      EveryMinimumSupport (doubleStarModel b a).Adj :=
  EveryMinimumSupport_iso_iff _ _ (doubleStarSwapIso a b)

theorem doubleStar_other_one_leaf_not_support (a : ℕ) (ha : 2 ≤ a) :
    ¬ EveryMinimumSupport (doubleStarModel a 1).Adj := by
  intro h
  exact doubleStar_one_leaf_not_support a ha ((doubleStar_support_swap_iff a 1).mp h)

end FaultObservationResearch
