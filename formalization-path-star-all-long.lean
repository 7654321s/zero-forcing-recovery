module

/-
Every finite path star with at least three arms of lengths at least two
fails EveryMinimumSupport. The proof selects a longest arm and two others.
-/
public import «formalization-path-star-witness»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
universe u v
variable {I : Type u} [Fintype I] [DecidableEq I]

theorem finite_two_distinct_away_from (hcard : 3 ≤ Fintype.card I) (j : I) :
    ∃ a b : I, a ≠ b ∧ j ≠ a ∧ j ≠ b := by
  classical
  have hfirst : ({j} : Finset I).card < (Finset.univ : Finset I).card := by
    simp only [Finset.card_singleton, Finset.card_univ]
    omega
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hfirst
  have haj : a ≠ j := by simpa only [Finset.mem_singleton] using ha
  have hpair : ({j, a} : Finset I).card = 2 :=
    Finset.card_pair_eq_two_iff.mpr haj.symm
  have hsecond : ({j, a} : Finset I).card < (Finset.univ : Finset I).card := by
    rw [hpair, Finset.card_univ]
    omega
  obtain ⟨b, _, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card hsecond
  have hba : b ≠ j ∧ b ≠ a := by simpa using hb
  exact ⟨a, b, hba.2.symm, haj.symm, hba.1.symm⟩

theorem pathStar_all_long_not_everyMinimumSupport (L : I → ℕ)
    (hlong : ∀ i, 2 ≤ L i) (hcard : 3 ≤ Fintype.card I) :
    ¬ EveryMinimumSupport (pathStarGraph L).Adj := by
  classical
  have hnonempty : (Finset.univ : Finset I).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_univ]
    omega
  obtain ⟨j, _, hmax⟩ := Finset.exists_max_image Finset.univ L hnonempty
  obtain ⟨a, b, hab, hja, hjb⟩ := finite_two_distinct_away_from hcard j
  exact pathStar_all_long_designated_obstruction L hlong a b j hab hja hjb
    (fun i => hmax i (Finset.mem_univ i))

theorem graph_iso_all_long_pathStar_not_support {V : Type v} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (L : I → ℕ) (hlong : ∀ i, 2 ≤ L i)
    (hcard : 3 ≤ Fintype.card I) (e : G ≃g pathStarGraph L) :
    ¬ EveryMinimumSupport G.Adj := by
  intro hs
  exact pathStar_all_long_not_everyMinimumSupport L hlong hcard
    ((EveryMinimumSupport_iso_iff G (pathStarGraph L) e).mp hs)

end FaultObservationResearch
