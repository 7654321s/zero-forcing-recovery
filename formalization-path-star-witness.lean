module

/-
All-long-arm counterexample with two designated second vertices as killing support.
Draft until the source and all named statements pass compilation and axiom audit.
-/
public import «formalization-path-star-initial»
public import «formalization-path-star-upper»
public import «formalization-path-star-recovery»
public import «formalization-path-star-speed»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

theorem pathStar_initial_head (L : I → ℕ) (hlong : ∀ i, 2 ≤ L i)
    (a b i : I) (k : Fin (L i)) (hk : k.val = 0) :
    some ⟨i, k⟩ ∈ pathStarPairInitial L hlong a b := by
  apply Finset.mem_union_left
  simp [pathStarHeads, hk]

theorem pathStar_initial_selected_second (L : I → ℕ) (hlong : ∀ i, 2 ≤ L i)
    (a b i : I) (hi : i = a ∨ i = b) :
    pathStarSecond L hlong i ∈ pathStarPairInitial L hlong a b := by
  apply Finset.mem_union_right
  rcases hi with rfl | rfl <;> simp [pathStarPairSupport]

theorem pathStar_single_loss_center_one (L : I → ℕ) (hlong : ∀ i, 2 ≤ L i)
    (a b : I) (hab : a ≠ b) (D : Finset (PathStarVertex I L)) (hD : D.card ≤ 1) :
    none ∈ colorAfter (pathStarGraph L).Adj (pathStarPairInitial L hlong a b \ D) 1 := by
  classical
  by_cases ha : ∃ k : Fin (L a), some ⟨a, k⟩ ∈ D
  · obtain ⟨k, hk⟩ := ha
    have hbclear : ∀ l : Fin (L b), (some ⟨b, l⟩ : PathStarVertex I L) ∉ D := by
      intro l hl
      exact pathStar_arm_index_ne L hab k l ((Finset.card_le_one.mp hD) _ hk _ hl)
    apply pathStar_center_from_intact_pair L b
      ⟨0, by have h := hlong b; omega⟩ ⟨1, by have h := hlong b; omega⟩ rfl rfl
    · exact Finset.mem_sdiff.mpr ⟨pathStar_initial_head L hlong a b b _ rfl, hbclear _⟩
    · exact Finset.mem_sdiff.mpr
        ⟨pathStar_initial_selected_second L hlong a b b (Or.inr rfl), hbclear _⟩
  · have haclear : ∀ k : Fin (L a), (some ⟨a, k⟩ : PathStarVertex I L) ∉ D := by
      intro k hk
      exact ha ⟨k, hk⟩
    apply pathStar_center_from_intact_pair L a
      ⟨0, by have h := hlong a; omega⟩ ⟨1, by have h := hlong a; omega⟩ rfl rfl
    · exact Finset.mem_sdiff.mpr ⟨pathStar_initial_head L hlong a b a _ rfl, haclear _⟩
    · exact Finset.mem_sdiff.mpr
        ⟨pathStar_initial_selected_second L hlong a b a (Or.inl rfl), haclear _⟩

theorem pathStar_single_loss_heads_two (L : I → ℕ) (hlong : ∀ i, 2 ≤ L i)
    (a b : I) (hab : a ≠ b) (D : Finset (PathStarVertex I L)) (hD : D.card ≤ 1)
    (i : I) (k : Fin (L i)) (hk : k.val = 0) :
    some ⟨i, k⟩ ∈ colorAfter (pathStarGraph L).Adj (pathStarPairInitial L hlong a b \ D) 2 := by
  classical
  by_cases hlost : (some ⟨i, k⟩ : PathStarVertex I L) ∈ D
  · apply pathStar_missing_head_recovers L i k hk _ 1
      (pathStar_single_loss_center_one L hlong a b hab D hD)
    intro j hji l hl
    have hnot : (some ⟨j, l⟩ : PathStarVertex I L) ∉ D := by
      intro hjlost
      exact pathStar_arm_index_ne L hji l k ((Finset.card_le_one.mp hD) _ hjlost _ hlost)
    exact colorAfter_mono_time _ _ (Nat.zero_le 1)
      (Finset.mem_sdiff.mpr ⟨pathStar_initial_head L hlong a b j l hl, hnot⟩)
  · exact colorAfter_mono_time _ _ (Nat.zero_le 2)
      (Finset.mem_sdiff.mpr ⟨pathStar_initial_head L hlong a b i k hk, hlost⟩)

theorem pathStar_single_loss_finishes (L : I → ℕ) (hlong : ∀ i, 2 ≤ L i)
    (a b : I) (hab : a ≠ b) (M : ℕ) (hbound : ∀ i, L i ≤ M)
    (D : Finset (PathStarVertex I L)) (hD : D.card ≤ 1) :
    FinishesBy (pathStarGraph L).Adj (pathStarPairInitial L hlong a b \ D) (M + 1) := by
  have hM : 2 ≤ M := le_trans (hlong a) (hbound a)
  apply pathStar_finishes_after_center_heads L _ 2 (M + 1) (by omega)
  · exact colorAfter_mono_time _ _ (by omega : 1 ≤ 2)
      (pathStar_single_loss_center_one L hlong a b hab D hD)
  · exact pathStar_single_loss_heads_two L hlong a b hab D hD
  · intro i
    have h := hbound i
    omega

theorem pathStar_support_loss_finishes (L : I → ℕ) (hlong : ∀ i, 2 ≤ L i)
    (a b : I) (hab : a ≠ b) (M : ℕ) (hbound : ∀ i, L i ≤ M)
    (D : Finset (PathStarVertex I L)) (hsubset : D ⊆ pathStarPairSupport L hlong a b)
    (hD : D.card ≤ 1) :
    FinishesBy (pathStarGraph L).Adj (pathStarPairInitial L hlong a b \ D) M := by
  have hM : 2 ≤ M := le_trans (hlong a) (hbound a)
  apply pathStar_finishes_after_center_heads L _ 1 M (by omega)
  · exact pathStar_single_loss_center_one L hlong a b hab D hD
  · intro i k hk
    have hnot : (some ⟨i, k⟩ : PathStarVertex I L) ∉ D := by
      intro h
      exact pathStar_head_not_support L hlong a b i k hk (hsubset h)
    exact colorAfter_mono_time _ _ (Nat.zero_le 1)
      (Finset.mem_sdiff.mpr ⟨pathStar_initial_head L hlong a b i k hk, hnot⟩)
  · intro i
    have h := hbound i
    omega

theorem pathStar_pair_minimum_killing (L : I → ℕ) (hlong : ∀ i, 2 ≤ L i)
    (a b : I) (hab : a ≠ b) (M : ℕ) (hbound : ∀ i, L i ≤ M) :
    IsMinimumKilling (pathStarGraph L).Adj (pathStarPairInitial L hlong a b)
      (pathStarPairSupport L hlong a b) := by
  refine ⟨pathStar_support_subset_initial L hlong a b, ?_, ?_⟩
  · rw [pathStar_initial_sdiff_support]
    exact pathStar_heads_not_forcing L hlong
  · intro D _ hD
    have hcard : D.card ≤ 1 := by
      rw [pathStar_pair_support_card L hlong a b hab] at hD
      omega
    exact ⟨M + 1, pathStar_single_loss_finishes L hlong a b hab M hbound D hcard⟩

theorem pathStar_unselected_head_loss_not_finishes (L : I → ℕ) (hlong : ∀ i, 2 ≤ L i)
    (a b j : I) (hja : j ≠ a) (hjb : j ≠ b) :
    ¬ FinishesBy (pathStarGraph L).Adj
      (pathStarPairInitial L hlong a b \ {pathStarHead L hlong j}) (L j) := by
  classical
  intro hfinish
  have hcenter : (none : PathStarVertex I L) ∉
      pathStarPairInitial L hlong a b \ {pathStarHead L hlong j} := by
    intro h
    exact pathStar_center_not_initial L hlong a b (Finset.mem_sdiff.mp h).1
  have harm : ∀ k : Fin (L j), (some ⟨j, k⟩ : PathStarVertex I L) ∉
      pathStarPairInitial L hlong a b \ {pathStarHead L hlong j} := by
    intro k h
    obtain ⟨hinitial, hnot⟩ := Finset.mem_sdiff.mp h
    rcases Finset.mem_union.mp hinitial with hhead | hsupport
    · have hk : k.val = 0 := by simpa [pathStarHeads] using hhead
      have heq : (some ⟨j, k⟩ : PathStarVertex I L) = pathStarHead L hlong j := by
        unfold pathStarHead
        congr 2
        exact Fin.ext hk
      exact hnot (Finset.mem_singleton.mpr heq)
    · rcases Finset.mem_insert.mp hsupport with ha | hb
      · exact pathStar_arm_index_ne L hja k _ ha
      · exact pathStar_arm_index_ne L hjb k _ (Finset.mem_singleton.mp hb)
  have h := pathStar_empty_arm_white_center_completion_lower L j
    (by have h := hlong j; omega) _ hcenter harm (L j) hfinish
  omega

theorem pathStar_all_long_designated_obstruction (L : I → ℕ) (hlong : ∀ i, 2 ≤ L i)
    (a b j : I) (hab : a ≠ b) (hja : j ≠ a) (hjb : j ≠ b)
    (hbound : ∀ i, L i ≤ L j) : ¬ EveryMinimumSupport (pathStarGraph L).Adj := by
  classical
  intro htarget
  have hforcing : IsForcing (pathStarGraph L).Adj (pathStarPairInitial L hlong a b) := by
    refine ⟨L j + 1, ?_⟩
    simpa using pathStar_single_loss_finishes L hlong a b hab (L j) hbound ∅ (by simp)
  have hminimum := pathStar_pair_minimum_killing L hlong a b hab (L j) hbound
  have hrestricted : RobustBy (pathStarGraph L).Adj (pathStarPairInitial L hlong a b)
      (pathStarPairSupport L hlong a b) 1 (L j) := by
    intro D hD hcard
    exact pathStar_support_loss_finishes L hlong a b hab (L j) hbound D hD hcard
  have hglobal := (htarget _ hforcing _ hminimum 1 (L j)).mpr hrestricted
  have hhead : pathStarHead L hlong j ∈ pathStarPairInitial L hlong a b :=
    pathStar_initial_head L hlong a b j _ rfl
  have hfinish := hglobal {pathStarHead L hlong j}
    (Finset.singleton_subset_iff.mpr hhead) (by simp)
  exact pathStar_unselected_head_loss_not_finishes L hlong a b j hja hjb hfinish

end FaultObservationResearch
