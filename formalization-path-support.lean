module

/-
The arbitrary-blue-set, every-minimum-support path theorem.
All budgets and deadlines are natural numbers; no bound on path order.
The graph and edges are retained after initial color losses.
-/
public import «formalization-path-guards»
public import «formalization-path-reversal-tools»
public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch

theorem path_guard_whites_inside (n : ℕ) (blue : Finset (Fin (n + 1)))
    (white : Fin (n + 1)) (low high : ℕ) (left right : Fin (n + 1))
    (hL : PathLeftGuard n blue white low left) (hR : PathRightGuard n blue white high right) :
    ∀ x ∈ PathIntervalWhites n blue left right, low ≤ x.val ∧ x.val ≤ high := by
  classical
  intro x hx
  have hi := (Finset.mem_filter.mp hx).2
  constructor
  · rcases hL.kind with ⟨hlo, _⟩ | ⟨hr, hlo⟩
    · rw [hlo]
      exact Nat.zero_le _
    · have hne : x.val ≠ left.val := fun h => hi.2.2 (by rw [Fin.ext h]; exact hr.1)
      omega
  · rcases hR.kind with ⟨hhi, _⟩ | ⟨hr, hhi⟩
    · rw [hhi]
      have hxBound := x.isLt
      omega
    · have hne : x.val ≠ right.val := fun h => hi.2.2 (by rw [Fin.ext h]; exact hr.1)
      omega

theorem path_guards_have_ready_side (n : ℕ) (blue : Finset (Fin (n + 1)))
    (hforcing : IsForcing (SimpleGraph.pathGraph (n + 1)).Adj blue)
    (white : Fin (n + 1)) (hw : white ∉ blue) (low high : ℕ) (left right : Fin (n + 1))
    (hL : PathLeftGuard n blue white low left) (hR : PathRightGuard n blue white high right) :
    PathLeftReady n blue left ∨ PathRightReady n blue right := by
  classical
  have hcell : ∃ cell : Finset (Fin (n + 1)), cell ⊆ blue ∧ PathForcingUnit n cell := by
    rcases (path_forcing_iff_seed n blue).mp hforcing with hz | hl | ⟨u, v, hu, hv, huv⟩
    · exact ⟨{0}, by simpa using hz, Or.inl rfl⟩
    · exact ⟨{Fin.last n}, by simpa using hl, Or.inr (Or.inl rfl)⟩
    · refine ⟨{u, v}, ?_, Or.inr (Or.inr ⟨u, v, huv, rfl⟩)⟩
      intro x hx
      rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hx) with hx | hx
      · rwa [hx]
      · rwa [hx]
  rcases hL.kind with ⟨hlo, _⟩ | ⟨hr, _⟩
  · rcases hR.kind with ⟨hhi, _⟩ | ⟨hr, _⟩
    · obtain ⟨cell, hsub, hk⟩ := hcell
      rcases pathForcingUnit_ready_around_white n blue cell hk hsub white hw with
        ⟨p, _, hp, hready, _⟩ | ⟨p, _, hp, hready, _⟩
      · have h := hL.sources_before p hp hready
        omega
      · have h := hR.sources_after p hp hready
        have hpBound := p.isLt
        omega
    · exact Or.inr hr
  · exact Or.inl hr

theorem path_support_window_deadline_bounds (n : ℕ) (blue support : Finset (Fin (n + 1)))
    (hcover : HitsPathSeeds n blue support) (budget deadline low high : ℕ)
    (hrobust : RobustBy (SimpleGraph.pathGraph (n + 1)).Adj blue support budget deadline)
    (hlh : low ≤ high) (hhn : high ≤ n) (hedge : 0 < low ∨ high < n)
    (hcard : (PathRangeHits n support low high).card ≤ budget) :
    (PathWhiteInterval n blue support low high).card ≤ 2 * deadline ∧
      (low = 0 → (PathWhiteInterval n blue support low high).card ≤ deadline) ∧
      (high = n → (PathWhiteInterval n blue support low high).card ≤ deadline) := by
  classical
  have hsub : PathRangeHits n support low high ⊆ support := fun _ hx => (Finset.mem_filter.mp hx).1
  have hf := hrobust (PathRangeHits n support low high) hsub hcard
  by_cases hz : low = 0
  · have hhi : high < n := by omega
    have hle := path_interval_end_deadline_lower_bound n blue support hcover high hhi deadline (by
      simpa only [PathRangeHits, hz] using hf)
    rw [hz]
    refine ⟨by omega, fun _ => hle, ?_⟩
    intro heq
    omega
  · have hlo : 0 < low := by omega
    by_cases hn : high = n
    · have hle := path_interval_suffix_deadline_lower_bound n blue support hcover low hlo
        (by omega) deadline (by simpa only [PathRangeHits, hn] using hf)
      rw [hn]
      exact ⟨by omega, fun heq => False.elim (hz heq), fun _ => hle⟩
    · have hhi : high < n := by omega
      have hle := path_interval_deadline_lower_bound n blue support hcover low high hlo hhi deadline hf
      exact ⟨hle, fun heq => False.elim (hz heq), fun heq => False.elim (hn heq)⟩

theorem path_loss_white_inclusion_card_le (n : ℕ)
    (blue support loss : Finset (Fin (n + 1))) (hsub : support ⊆ blue)
    (left right : Fin (n + 1)) (low high budget : ℕ)
    (hinside : ∀ x ∈ PathIntervalWhites n (blue \ loss) left right, low ≤ x.val ∧ x.val ≤ high)
    (hloss : loss.card ≤ budget) (hcard : (PathRangeHits n support low high).card = budget) :
    (PathIntervalWhites n (blue \ loss) left right).card ≤
      (PathWhiteInterval n blue support low high).card := by
  classical
  let W := Finset.univ.filter (fun x : Fin (n + 1) => low ≤ x.val ∧ x.val ≤ high ∧ x ∉ blue)
  have hinc : PathIntervalWhites n (blue \ loss) left right ⊆ W ∪ loss := by
    intro x hx
    have hi := (Finset.mem_filter.mp hx).2
    have hr := hinside x hx
    by_cases hxB : x ∈ blue
    · have hxD : x ∈ loss := by
        by_contra hnot
        exact hi.2.2 (Finset.mem_sdiff.mpr ⟨hxB, hnot⟩)
      exact Finset.mem_union_right _ hxD
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr.1, hr.2, hxB⟩)
  have hle := (Finset.card_le_card hinc).trans (Finset.card_union_le W loss)
  rw [path_white_interval_card n blue support hsub low high, hcard]
  change _ ≤ W.card + budget
  omega

theorem path_support_from_seed_packing (n : ℕ) (blue support : Finset (Fin (n + 1)))
    (units : List (Finset (Fin (n + 1)))) (witness : Finset (Fin (n + 1)))
    (hpack : PathSeedPacking n blue units witness)
    (hminimum : IsMinimumKilling (SimpleGraph.pathGraph (n + 1)).Adj blue support)
    (budget deadline : ℕ) :
    RobustBy (SimpleGraph.pathGraph (n + 1)).Adj blue blue budget deadline ↔
      RobustBy (SimpleGraph.pathGraph (n + 1)).Adj blue support budget deadline := by
  classical
  constructor
  · intro h loss hs hc
    exact h loss (fun _ hx => hminimum.1 (hs hx)) hc
  · intro hrestricted
    by_cases hlarge : support.card ≤ budget
    · exact False.elim (hminimum.2.1 ⟨deadline, hrestricted support (fun _ hx => hx) hlarge⟩)
    · have hbudget : budget < support.card := by omega
      obtain ⟨pick, hsel⟩ := pathSeedPacking_every_minimum_selector n blue support units witness hpack hminimum
      have hcover := (path_nonforcing_sdiff_iff_hits_seeds n blue support).mp hminimum.2.1
      intro loss hD hDcard
      have hforcing : IsForcing (SimpleGraph.pathGraph (n + 1)).Adj (blue \ loss) :=
        hminimum.2.2 loss hD (by omega)
      change colorAfter (SimpleGraph.pathGraph (n + 1)).Adj (blue \ loss) deadline = Finset.univ
      apply Finset.eq_univ_of_forall
      intro white
      by_cases hw : white ∈ blue \ loss
      · exact colorAfter_mono_time _ (blue \ loss) (Nat.zero_le deadline) hw
      · obtain ⟨low, left, hL⟩ := exists_path_left_guard n (blue \ loss) white
        obtain ⟨high, right, hR⟩ := exists_path_right_guard n (blue \ loss) white
        have hsmall := path_guard_interval_support_card_le_loss n blue support loss units witness
          hpack pick hsel white hw low high left right hL hR
        have hlh : low ≤ high := hL.low_le.trans hR.high_ge
        obtain ⟨a, b, hal, hhb, hbn, hc, hedge⟩ := path_range_extend_to_budget n support
          budget low high hlh hR.high_le (hsmall.trans hDcard) hbudget
        have hab : a ≤ b := by omega
        have hbounds := path_support_window_deadline_bounds n blue support hcover budget deadline a b
          hrestricted hab hbn hedge (by omega)
        have hinside := path_guard_whites_inside n (blue \ loss) white low high left right hL hR
        have hcompare := path_loss_white_inclusion_card_le n blue support loss hminimum.1 left right a b
          budget (fun x hx => ⟨hal.trans (hinside x hx).1, ((hinside x hx).2).trans hhb⟩) hDcard hc
        have htwo : (PathIntervalWhites n (blue \ loss) left right).card ≤ 2 * deadline :=
          hcompare.trans hbounds.1
        have hprefix : low = 0 → (PathIntervalWhites n (blue \ loss) left right).card ≤ deadline := by
          intro hlo
          have ha : a = 0 := by omega
          exact hcompare.trans (hbounds.2.1 ha)
        have hsuffix : high = n → (PathIntervalWhites n (blue \ loss) left right).card ≤ deadline := by
          intro hhi
          have hb : b = n := by omega
          exact hcompare.trans (hbounds.2.2 hb)
        have hready := path_guards_have_ready_side n (blue \ loss) hforcing white hw low high left right hL hR
        by_cases hleft : PathLeftReady n (blue \ loss) left
        · by_cases hright : PathRightReady n (blue \ loss) right
          · exact path_interval_two_sided_upper n (blue \ loss) left right hleft hright deadline htwo
              white hL.left_le hR.right_ge
          · have hhi : high = n := hR.kind.elim (fun h => h.1) (fun h => False.elim (hright h.1))
            exact path_interval_left_sided_upper n (blue \ loss) left right hleft deadline (hsuffix hhi)
              white hL.left_le hR.right_ge
        · have hright : PathRightReady n (blue \ loss) right := hready.resolve_left hleft
          have hlo : low = 0 := hL.kind.elim (fun h => h.1) (fun h => False.elim (hleft h.1))
          exact path_interval_one_sided_upper n (blue \ loss) left right hright deadline (hprefix hlo)
            white hL.left_le hR.right_ge

theorem path_every_minimum_support (n : ℕ) :
    EveryMinimumSupport (SimpleGraph.pathGraph (n + 1)).Adj := by
  classical
  by_cases hn : 0 < n
  · intro blue _ support hminimum budget deadline
    obtain ⟨units, witness, hpack⟩ := exists_path_seed_packing n hn blue
    exact path_support_from_seed_packing n blue support units witness hpack hminimum budget deadline
  · have heq : n = 0 := by omega
    subst n
    exact path_small_support 1 (by omega)

theorem path_every_minimum_support_time (n : ℕ) :
    EveryMinimumSupportTime (SimpleGraph.pathGraph (n + 1)).Adj :=
  (everyMinimumSupport_iff_worstTime _).mp (path_every_minimum_support n)

theorem canonical_path_support (n : ℕ) (hn : 1 ≤ n) :
    EveryMinimumSupport (SimpleGraph.pathGraph n).Adj := by
  cases n with
  | zero => omega
  | succ n => exact path_every_minimum_support n

theorem support_of_path_iso {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (n : ℕ) (hn : 1 ≤ n) (e : G ≃g SimpleGraph.pathGraph n) :
    EveryMinimumSupport G.Adj :=
  (EveryMinimumSupport_iso_iff G _ e).mpr (canonical_path_support n hn)

theorem candidateClass_every_minimum_support {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hclass : InTreeCandidateClass G) : EveryMinimumSupport G.Adj := by
  rcases hclass with ⟨n, hn, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩ | ⟨a, b, ha, hb, ⟨e⟩⟩
  · exact support_of_path_iso G n hn e
  · exact support_of_star_iso G a ha e
  · exact support_of_doubleStar_iso G a b ha hb e

end FaultObservationResearch
