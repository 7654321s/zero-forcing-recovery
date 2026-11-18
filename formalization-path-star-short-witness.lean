module

/-
One-short-arm counterexample. All nonshort arms have length at least two.
The proof uses a longest terminal-seeded arm and another empty long arm.
-/
public import «formalization-path-star-short-upper»
public import «formalization-path-star-coupled-speed»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
universe u v
variable {I : Type u} [Fintype I] [DecidableEq I]

theorem pathStar_short_support_minimum_killing (L : I → ℕ) (hpos : ∀ i, 1 ≤ L i)
    (s a : I) (hsa : s ≠ a) (hs : L s = 1) (halong : 2 ≤ L a)
    (hbound : ∀ i, L i ≤ L a) :
    IsMinimumKilling (pathStarGraph L).Adj (pathStarTerminalInitial L a)
      (pathStarShortSupport L hpos s a) := by
  classical
  refine ⟨pathStar_short_support_subset L hpos s a hsa,
    pathStar_short_support_kills L hpos s a hsa, ?_⟩
  intro D _ hsmall
  have hD : D.card ≤ 1 := by
    rw [pathStar_short_support_card L hpos s a hsa] at hsmall
    omega
  exact ⟨2 * L a + 1, pathStar_terminal_single_loss_finishes L hpos s a hsa hs halong hbound D hD⟩

theorem pathStar_terminal_other_head_loss_completion_lower
    (L : I → ℕ) (hpos : ∀ i, 1 ≤ L i) (a j : I) (hja : j ≠ a)
    (t : ℕ) (hfinish : FinishesBy (pathStarGraph L).Adj
      (pathStarTerminalInitial L a \ {pathStarFirst L hpos j}) t) : L a + L j ≤ t + 1 := by
  classical
  apply pathStar_terminal_empty_completion_lower L a j hja.symm
    (by have h := hpos a; omega) (by have h := hpos j; omega)
    (pathStarTerminalInitial L a \ {pathStarFirst L hpos j})
  · intro k hk
    have h := (pathStar_terminal_arm_mem_iff L a k).mp (Finset.mem_sdiff.mp hk).1
    omega
  · intro k hk
    obtain ⟨hinitial, hnot⟩ := Finset.mem_sdiff.mp hk
    have hzero := (pathStar_terminal_other_mem_iff L a j hja k).mp hinitial
    apply hnot
    rw [pathStar_eq_first L hpos j k hzero]
    exact Finset.mem_singleton_self _
  · exact hfinish

theorem pathStar_terminal_other_head_loss_not_finishes (L : I → ℕ) (hpos : ∀ i, 1 ≤ L i)
    (a j : I) (hja : j ≠ a) (hjlong : 2 ≤ L j) :
    ¬ FinishesBy (pathStarGraph L).Adj
      (pathStarTerminalInitial L a \ {pathStarFirst L hpos j}) (L a) := by
  intro hfinish
  have h := pathStar_terminal_other_head_loss_completion_lower L hpos a j hja (L a) hfinish
  omega

theorem pathStar_one_short_deadline_gap (L : I → ℕ) (hpos : ∀ i, 1 ≤ L i)
    (s a j : I) (hsa : s ≠ a) (hs : L s = 1) (halong : 2 ≤ L a)
    (hja : j ≠ a) (hjlong : 2 ≤ L j) (hbound : ∀ i, L i ≤ L a) :
    IsForcing (pathStarGraph L).Adj (pathStarTerminalInitial L a) ∧
    IsMinimumKilling (pathStarGraph L).Adj (pathStarTerminalInitial L a)
      (pathStarShortSupport L hpos s a) ∧
    RobustBy (pathStarGraph L).Adj (pathStarTerminalInitial L a)
      (pathStarShortSupport L hpos s a) 1 (L a) ∧
    ¬ RobustBy (pathStarGraph L).Adj (pathStarTerminalInitial L a)
      (pathStarTerminalInitial L a) 1 (L a + L j - 2) := by
  classical
  refine ⟨?_, pathStar_short_support_minimum_killing L hpos s a hsa hs halong hbound, ?_, ?_⟩
  · refine ⟨2 * L a + 1, ?_⟩
    simpa using pathStar_terminal_single_loss_finishes L hpos s a hsa hs halong hbound ∅ (by simp)
  · intro D hsubset hcard
    exact pathStar_terminal_support_loss_finishes L hpos s a hs halong hbound D hsubset hcard
  · intro hglobal
    have hhead : pathStarFirst L hpos j ∈ pathStarTerminalInitial L a :=
      pathStar_terminal_head_mem L a j hja _ rfl
    have hfinish := hglobal {pathStarFirst L hpos j}
      (Finset.singleton_subset_iff.mpr hhead) (by simp)
    have h := pathStar_terminal_other_head_loss_completion_lower L hpos a j hja
      (L a + L j - 2) hfinish
    omega

theorem pathStar_one_short_designated_obstruction (L : I → ℕ) (hpos : ∀ i, 1 ≤ L i)
    (s a j : I) (hsa : s ≠ a) (hs : L s = 1) (halong : 2 ≤ L a)
    (hja : j ≠ a) (hjlong : 2 ≤ L j) (hbound : ∀ i, L i ≤ L a) :
    ¬ EveryMinimumSupport (pathStarGraph L).Adj := by
  classical
  intro htarget
  have hforcing : IsForcing (pathStarGraph L).Adj (pathStarTerminalInitial L a) := by
    refine ⟨2 * L a + 1, ?_⟩
    simpa using pathStar_terminal_single_loss_finishes L hpos s a hsa hs halong hbound ∅ (by simp)
  have hminimum := pathStar_short_support_minimum_killing L hpos s a hsa hs halong hbound
  have hrestricted : RobustBy (pathStarGraph L).Adj (pathStarTerminalInitial L a)
      (pathStarShortSupport L hpos s a) 1 (L a) := by
    intro D hsubset hcard
    exact pathStar_terminal_support_loss_finishes L hpos s a hs halong hbound D hsubset hcard
  have hglobal := (htarget _ hforcing _ hminimum 1 (L a)).mpr hrestricted
  have hhead : pathStarFirst L hpos j ∈ pathStarTerminalInitial L a :=
    pathStar_terminal_head_mem L a j hja _ rfl
  have hfinish := hglobal {pathStarFirst L hpos j}
    (Finset.singleton_subset_iff.mpr hhead) (by simp)
  exact pathStar_terminal_other_head_loss_not_finishes L hpos a j hja hjlong hfinish

theorem pathStar_one_short_not_everyMinimumSupport (L : I → ℕ) (hpos : ∀ i, 1 ≤ L i)
    (s : I) (hs : L s = 1) (hlong : ∀ i, i ≠ s → 2 ≤ L i)
    (hcard : 3 ≤ Fintype.card I) : ¬ EveryMinimumSupport (pathStarGraph L).Adj := by
  classical
  have hnonempty : (Finset.univ : Finset I).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_univ]
    omega
  obtain ⟨a, _, hmax⟩ := Finset.exists_max_image Finset.univ L hnonempty
  have hbound : ∀ i, L i ≤ L a := fun i => hmax i (Finset.mem_univ i)
  have hfirst : ({s} : Finset I).card < (Finset.univ : Finset I).card := by
    simp only [Finset.card_singleton, Finset.card_univ]
    omega
  obtain ⟨q, _, hq⟩ := Finset.exists_mem_notMem_of_card_lt_card hfirst
  have hqs : q ≠ s := by simpa only [Finset.mem_singleton] using hq
  have halong : 2 ≤ L a := le_trans (hlong q hqs) (hbound q)
  have hsa : s ≠ a := by
    intro heq
    rw [← heq, hs] at halong
    omega
  have hpair : ({s, a} : Finset I).card = 2 := Finset.card_pair_eq_two_iff.mpr hsa
  have hthird : ({s, a} : Finset I).card < (Finset.univ : Finset I).card := by
    rw [hpair, Finset.card_univ]
    omega
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card hthird
  have hne : j ≠ s ∧ j ≠ a := by simpa using hj
  exact pathStar_one_short_designated_obstruction L hpos s a j hsa hs halong
    hne.2 (hlong j hne.1) hbound

theorem graph_iso_one_short_pathStar_not_support {V : Type v} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (L : I → ℕ) (hpos : ∀ i, 1 ≤ L i) (s : I) (hs : L s = 1)
    (hlong : ∀ i, i ≠ s → 2 ≤ L i) (hcard : 3 ≤ Fintype.card I)
    (e : G ≃g pathStarGraph L) : ¬ EveryMinimumSupport G.Adj := by
  intro htarget
  exact pathStar_one_short_not_everyMinimumSupport L hpos s hs hlong hcard
    ((EveryMinimumSupport_iso_iff G (pathStarGraph L) e).mp htarget)

end FaultObservationResearch
