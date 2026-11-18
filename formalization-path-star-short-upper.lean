module

/-
Recovery bounds for a terminal seed on one long arm and a short leaf.
The sharp restricted deadline is the longest arm length; the general
single-loss deadline is deliberately coarse and proves finite recovery.
-/
public import «formalization-path-star-short-initial»
public import «formalization-path-star-endpoint»
public import «formalization-path-star-upper»
public import «formalization-path-star-recovery»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

theorem pathStar_center_from_short_leaf (L : I → ℕ) (s : I) (hs : L s = 1)
    (k : Fin (L s)) (C : Finset (PathStarVertex I L)) (hk : some ⟨s, k⟩ ∈ C) :
    none ∈ colorAfter (pathStarGraph L).Adj C 1 := by
  classical
  have hkzero : k.val = 0 := by have h := k.isLt; omega
  apply (mem_synchronousStep _ C none).mpr
  refine Or.inr ⟨some ⟨s, k⟩, hk, hkzero, ?_⟩
  intro other hadj _
  cases other with
  | none => rfl
  | some other =>
    obtain ⟨i, l⟩ := other
    change s = i ∧ (k.val + 1 = l.val ∨ l.val + 1 = k.val) at hadj
    obtain ⟨rfl, hleft | hright⟩ := hadj
    · have h := l.isLt
      omega
    · omega

theorem pathStar_terminal_single_loss_center_one (L : I → ℕ) (hpos : ∀ i, 1 ≤ L i)
    (s a : I) (hsa : s ≠ a) (hs : L s = 1)
    (D : Finset (PathStarVertex I L)) (hD : D.card ≤ 1) :
    none ∈ colorAfter (pathStarGraph L).Adj (pathStarTerminalInitial L a \ D) 1 := by
  classical
  by_cases hnone : (none : PathStarVertex I L) ∈ D
  · have hkeep : pathStarFirst L hpos s ∉ D := by
      intro h
      have heq := (Finset.card_le_one.mp hD) _ h _ hnone
      cases heq
    apply pathStar_center_from_short_leaf L s hs _ _
    exact Finset.mem_sdiff.mpr ⟨pathStar_terminal_head_mem L a s hsa _ rfl, hkeep⟩
  · exact colorAfter_mono_time _ _ (Nat.zero_le 1)
      (Finset.mem_sdiff.mpr ⟨pathStar_terminal_center_mem L a, hnone⟩)

theorem pathStar_terminal_lost_end_finishes (L : I → ℕ) (hpos : ∀ i, 1 ≤ L i)
    (a : I) (hbound : ∀ i, L i ≤ L a)
    (D : Finset (PathStarVertex I L)) (hD : D.card ≤ 1)
    (hlost : pathStarLast L hpos a ∈ D) :
    FinishesBy (pathStarGraph L).Adj (pathStarTerminalInitial L a \ D) (L a) := by
  classical
  let C := pathStarTerminalInitial L a \ D
  have hroot : (none : PathStarVertex I L) ∈ C := by
    apply Finset.mem_sdiff.mpr
    refine ⟨pathStar_terminal_center_mem L a, ?_⟩
    intro h
    have heq := (Finset.card_le_one.mp hD) _ h _ hlost
    cases heq
  have hothers : ∀ i, i ≠ a → ∀ k : Fin (L i), k.val = 0 → some ⟨i, k⟩ ∈ C := by
    intro i hia k hk
    apply Finset.mem_sdiff.mpr
    refine ⟨pathStar_terminal_head_mem L a i hia k hk, ?_⟩
    intro h
    have heq := (Finset.card_le_one.mp hD) _ h _ hlost
    exact hia (pathStar_nodes_eq_arm L i a k _ heq)
  have hapos := hpos a
  apply pathStar_finishes_after_center_heads L C 1 (L a) (by omega)
  · exact colorAfter_mono_time _ C (Nat.zero_le 1) hroot
  · intro i k hk
    by_cases hia : i = a
    · subst i
      exact pathStar_missing_head_recovers L a k hk C 0 hroot hothers
    · exact colorAfter_mono_time _ C (Nat.zero_le 1) (hothers i hia k hk)
  · intro i
    have h := hbound i
    omega

theorem pathStar_terminal_kept_end_colors (L : I → ℕ) (hpos : ∀ i, 1 ≤ L i)
    (a : I) (D : Finset (PathStarVertex I L)) (hkeep : pathStarLast L hpos a ∉ D) :
    ∀ k : Fin (L a), some ⟨a, k⟩ ∈ colorAfter (pathStarGraph L).Adj
      (pathStarTerminalInitial L a \ D) (L a - 1) := by
  apply pathStar_arm_endpoint_finishes
  intro k hk
  apply Finset.mem_sdiff.mpr
  refine ⟨pathStar_terminal_end_mem L a k hk, ?_⟩
  rw [pathStar_eq_last L hpos a k hk]
  exact hkeep

theorem pathStar_terminal_single_loss_finishes (L : I → ℕ) (hpos : ∀ i, 1 ≤ L i)
    (s a : I) (hsa : s ≠ a) (hs : L s = 1) (halong : 2 ≤ L a)
    (hbound : ∀ i, L i ≤ L a) (D : Finset (PathStarVertex I L)) (hD : D.card ≤ 1) :
    FinishesBy (pathStarGraph L).Adj (pathStarTerminalInitial L a \ D) (2 * L a + 1) := by
  classical
  by_cases hlost : pathStarLast L hpos a ∈ D
  · exact FinishesBy_mono_time _ _
      (pathStar_terminal_lost_end_finishes L hpos a hbound D hD hlost) (by omega)
  · let C := pathStarTerminalInitial L a \ D
    have hcenter := pathStar_terminal_single_loss_center_one L hpos s a hsa hs D hD
    have ha : ∀ k : Fin (L a), some ⟨a, k⟩ ∈ colorAfter (pathStarGraph L).Adj C (L a) := by
      intro k
      exact colorAfter_mono_time _ C (by omega : L a - 1 ≤ L a)
        (pathStar_terminal_kept_end_colors L hpos a D hlost k)
    have hheads : ∀ i, ∀ k : Fin (L i), k.val = 0 →
        some ⟨i, k⟩ ∈ colorAfter (pathStarGraph L).Adj C (L a + 1) := by
      intro i k hk
      by_cases hia : i = a
      · subst i
        exact colorAfter_subset_succ _ C (L a) (ha k)
      · by_cases hki : (some ⟨i, k⟩ : PathStarVertex I L) ∈ D
        · apply pathStar_missing_head_recovers L i k hk C (L a)
          · exact colorAfter_mono_time _ C (by omega : 1 ≤ L a) hcenter
          · intro j hji l hl
            by_cases hja : j = a
            · subst j
              exact ha l
            · have hnot : (some ⟨j, l⟩ : PathStarVertex I L) ∉ D := by
                intro h
                have heq := (Finset.card_le_one.mp hD) _ h _ hki
                exact hji (pathStar_nodes_eq_arm L j i l k heq)
              exact colorAfter_mono_time _ C (Nat.zero_le _)
                (Finset.mem_sdiff.mpr ⟨pathStar_terminal_head_mem L a j hja l hl, hnot⟩)
        · exact colorAfter_mono_time _ C (Nat.zero_le _)
            (Finset.mem_sdiff.mpr ⟨pathStar_terminal_head_mem L a i hia k hk, hki⟩)
    apply pathStar_finishes_after_center_heads L C (L a + 1) (2 * L a + 1) (by omega)
    · exact colorAfter_mono_time _ C (by omega : 1 ≤ L a + 1) hcenter
    · exact hheads
    · intro i
      have h := hbound i
      omega

theorem pathStar_terminal_support_loss_finishes (L : I → ℕ) (hpos : ∀ i, 1 ≤ L i)
    (s a : I) (hs : L s = 1) (halong : 2 ≤ L a)
    (hbound : ∀ i, L i ≤ L a) (D : Finset (PathStarVertex I L))
    (hsubset : D ⊆ pathStarShortSupport L hpos s a) (hD : D.card ≤ 1) :
    FinishesBy (pathStarGraph L).Adj (pathStarTerminalInitial L a \ D) (L a) := by
  classical
  by_cases hlost : pathStarLast L hpos a ∈ D
  · exact pathStar_terminal_lost_end_finishes L hpos a hbound D hD hlost
  · let C := pathStarTerminalInitial L a \ D
    have hroot : (none : PathStarVertex I L) ∈ C := by
      apply Finset.mem_sdiff.mpr
      refine ⟨pathStar_terminal_center_mem L a, ?_⟩
      intro h
      have hmem := hsubset h
      simp [pathStarShortSupport, pathStarFirst, pathStarLast] at hmem
    have hsafe : ∀ i, i ≠ s → i ≠ a → ∀ k : Fin (L i),
        (some ⟨i, k⟩ : PathStarVertex I L) ∉ D := by
      intro i his hia k hk
      have hmem := hsubset hk
      rcases (by simpa [pathStarShortSupport] using hmem :
        (some ⟨i, k⟩ : PathStarVertex I L) = pathStarFirst L hpos s ∨
        (some ⟨i, k⟩ : PathStarVertex I L) = pathStarLast L hpos a) with heq | heq
      · exact his (pathStar_nodes_eq_arm L i s k _ heq)
      · exact hia (pathStar_nodes_eq_arm L i a k _ heq)
    have ha := pathStar_terminal_kept_end_colors L hpos a D hlost
    have hheads : ∀ i, i ≠ s → ∀ k : Fin (L i), k.val = 0 →
        some ⟨i, k⟩ ∈ colorAfter (pathStarGraph L).Adj C (L a - 1) := by
      intro i his k hk
      by_cases hia : i = a
      · subst i
        exact ha k
      · exact colorAfter_mono_time _ C (Nat.zero_le _)
          (Finset.mem_sdiff.mpr ⟨pathStar_terminal_head_mem L a i hia k hk, hsafe i his hia k⟩)
    apply Finset.eq_univ_of_forall
    intro vertex
    cases vertex with
    | none => exact colorAfter_mono_time _ C (Nat.zero_le _) hroot
    | some vertex =>
      obtain ⟨i, k⟩ := vertex
      by_cases his : i = s
      · subst i
        have hkzero : k.val = 0 := by have h := k.isLt; omega
        have h := pathStar_missing_head_recovers L s k hkzero C (L a - 1)
          (colorAfter_mono_time _ C (Nat.zero_le _) hroot) hheads
        have htime : L a - 1 + 1 = L a := by omega
        simpa only [htime] using h
      · by_cases hia : i = a
        · subst i
          exact colorAfter_mono_time _ C (by omega : L a - 1 ≤ L a) (ha k)
        · apply pathStar_arm_prefix_blue L i C hroot
            (fun l hl => Finset.mem_sdiff.mpr
              ⟨pathStar_terminal_head_mem L a i hia l hl, hsafe i his hia l⟩) (L a) k
          have h := hbound i
          have hk := k.isLt
          omega

end FaultObservationResearch
