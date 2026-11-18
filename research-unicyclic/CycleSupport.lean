module

public import CyclePacking

@[expose] public section

set_option autoImplicit false

namespace FaultObservationResearch

/-- Each full packed pair in the prefix contributes exactly one support point. -/
theorem cycle_support_arc_card (n : ℕ) (blue support starts : Finset (Fin (n + 3)))
    (hpack : CyclePairPacking n blue starts) (h0 : 0 ∈ starts)
    (hcard : starts.card = support.card)
    (hminimum : IsMinimumKilling (SimpleGraph.cycleGraph (n + 3)).Adj blue support)
    (hi : ℕ) (hend : hi < n + 3 → ∃ b ∈ starts.erase 0, b.val = hi) :
    (support ∩ cycleArc n 2 hi).card = (cyclePrefix n starts hi).card := by
  classical
  obtain ⟨pick, hpick⟩ := cycle_pair_packing_exact_selector n blue support starts
    hpack hcard hminimum
  let idx := (Finset.univ : Finset starts).filter
    (fun a => a.val ∈ cyclePrefix n starts hi)
  have hidx (a : starts) : a ∈ idx ↔ a.val ∈ cyclePrefix n starts hi := by simp [idx]
  have hval : idx.image (fun a : starts => a.val) = cyclePrefix n starts hi := by
    ext v
    constructor
    · intro hv
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
      exact (hidx a).mp ha
    · intro hv
      let a : starts := ⟨v, ((mem_cyclePrefix n starts hi v).mp hv).1⟩
      exact Finset.mem_image.mpr ⟨a, (hidx a).mpr hv, rfl⟩
  have hpicked : idx.image pick = support ∩ cycleArc n 2 hi := by
    ext v
    constructor
    · intro hv
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
      apply Finset.mem_inter.mpr
      constructor
      · rw [hpick.2.2.1]
        exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
      · exact cycle_pair_subset_arc_of_prefix n blue starts hpack h0 hi hend a.val
          ((hidx a).mp ha) (hpick.2.1 a)
    · intro hv
      obtain ⟨hSupport, hArc⟩ := Finset.mem_inter.mp hv
      rw [hpick.2.2.1] at hSupport
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hSupport
      exact Finset.mem_image.mpr ⟨a, (hidx a).mpr
        (cycle_pair_meets_arc_implies_prefix n blue starts hpack h0 hi a.val
          (pick a) a.property (hpick.2.1 a) hArc), rfl⟩
  rw [← hpicked, ← hval, Finset.card_image_of_injective _ hpick.1,
    Finset.card_image_of_injective _ Subtype.val_injective]

theorem cycle_restricted_prefix_white_bound (n : ℕ)
    (blue support starts : Finset (Fin (n + 3)))
    (hpack : CyclePairPacking n blue starts) (h0 : 0 ∈ starts)
    (hcard : starts.card = support.card)
    (hminimum : IsMinimumKilling (SimpleGraph.cycleGraph (n + 3)).Adj blue support)
    (hi budget deadline : ℕ) (hend : hi < n + 3 → ∃ b ∈ starts.erase 0, b.val = hi)
    (hsize : (cyclePrefix n starts hi).card = budget)
    (hrobust : RobustBy (SimpleGraph.cycleGraph (n + 3)).Adj blue support budget deadline) :
    (cycleArc n 2 hi \ blue).card + budget ≤ 2 * deadline := by
  classical
  let region := cycleArc n 2 hi
  let loss := support ∩ region
  have hLoss : loss ⊆ support := Finset.inter_subset_left
  have hLossSize : loss.card = budget :=
    (cycle_support_arc_card n blue support starts hpack h0 hcard hminimum hi hend).trans hsize
  have hfin := hrobust loss hLoss hLossSize.le
  have hNoPair : ∀ u ∈ region, ∀ v ∈ region,
      (SimpleGraph.cycleGraph (n + 3)).Adj u v → u ∉ blue \ loss ∨ v ∉ blue \ loss := by
    intro u hu v hv hadj
    by_contra h
    have huB : u ∈ blue \ loss := by by_contra hn; exact h (Or.inl hn)
    have hvB : v ∈ blue \ loss := by by_contra hn; exact h (Or.inr hn)
    have hhit := (cycle_nonforcing_sdiff_iff_hits_edges n blue support).mp hminimum.2.1
      u (Finset.mem_sdiff.mp huB).1 v (Finset.mem_sdiff.mp hvB).1 hadj
    rcases hhit with hs | hs
    · exact (Finset.mem_sdiff.mp huB).2 (Finset.mem_inter.mpr ⟨hs, hu⟩)
    · exact (Finset.mem_sdiff.mp hvB).2 (Finset.mem_inter.mpr ⟨hs, hv⟩)
  have hwhite := cycle_arc_white_card_le_of_finishes n (blue \ loss) 2 hi hNoPair deadline
    (by rw [hfin]; exact Finset.subset_univ _)
  have hsubB : loss ⊆ blue := fun v hv => hminimum.1 (hLoss hv)
  have hunion : region \ (blue \ loss) = (region \ blue) ∪ loss := by
    ext v
    constructor
    · intro hv
      obtain ⟨hr, hb⟩ := Finset.mem_sdiff.mp hv
      by_cases hB : v ∈ blue
      · have hL : v ∈ loss := by
          by_contra hn
          exact hb (Finset.mem_sdiff.mpr ⟨hB, hn⟩)
        exact Finset.mem_union_right _ hL
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hr, hB⟩)
    · intro hv
      rcases Finset.mem_union.mp hv with hb | hl
      · exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hb).1,
          fun h => (Finset.mem_sdiff.mp hb).2 (Finset.mem_sdiff.mp h).1⟩
      · exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hl).2,
          fun h => (Finset.mem_sdiff.mp h).2 hl⟩
  have hdis : Disjoint (region \ blue) loss := Finset.disjoint_left.mpr
    (fun _ h₁ h₂ => (Finset.mem_sdiff.mp h₁).2 (hsubB h₂))
  change (region \ (blue \ loss)).card ≤ 2 * deadline at hwhite
  rwa [hunion, Finset.card_union_of_disjoint hdis, hLossSize] at hwhite

/-- Both vertices of an undamaged pair survive the initial loss. -/
theorem cycle_undamaged_pair_blue (n : ℕ)
    (blue starts loss : Finset (Fin (n + 3))) (hpack : CyclePairPacking n blue starts)
    (a : Fin (n + 3)) (ha : a ∈ starts) (hgood : a ∉ cycleDamaged n starts loss) :
    cyclePair n a ⊆ blue \ loss := by
  intro v hv
  exact Finset.mem_sdiff.mpr ⟨hpack.blue_pair a ha hv,
    fun hL => hgood ((mem_cycleDamaged n starts loss a).mpr ⟨ha, v, hv, hL⟩)⟩

/-- With an intact starting pair at zero, find the first intact pair after
the target. If there is none, use the starting pair across the cut. -/
theorem cycle_intact_arc_after_target (n : ℕ)
    (blue starts loss : Finset (Fin (n + 3))) (hpack : CyclePairPacking n blue starts)
    (h0 : 0 ∈ starts) (hgood0 : 0 ∉ cycleDamaged n starts loss)
    (target : Fin (n + 3))
    (hPrior : cyclePrefix n starts (target.val + 1) ⊆ cycleDamaged n starts loss) :
    ∃ hi ≤ n + 3, target.val < hi ∧
      CycleArcGuards n (blue \ loss) 2 hi ∧
      cyclePrefix n starts hi ⊆ cycleDamaged n starts loss := by
  classical
  let later := starts.filter (fun a => target.val < a.val ∧ a ∉ cycleDamaged n starts loss)
  have hBase := cycle_undamaged_pair_blue n blue starts loss hpack 0 h0 hgood0
  have hGuardLeft : ∀ j, 2 - 2 ≤ j → j < 2 → cycleAt n j ∈ blue \ loss := by
    intro j _ hj
    apply hBase
    have hzero : cycleAt n 0 = 0 := Fin.ext (by simp [cycleAt])
    have hone : cycleAt n 1 = 1 := by rw [cycleAt_succ n 0, hzero, zero_add]
    have hcase : j = 0 ∨ j = 1 := by omega
    rcases hcase with h | h
    · rw [h, hzero]
      simp
    · rw [h, hone]
      simp
  by_cases hn : later.Nonempty
  · let a := later.min' hn
    obtain ⟨ha, haLate, haGood⟩ := Finset.mem_filter.mp (later.min'_mem hn)
    refine ⟨a.val, a.isLt.le, haLate, ⟨hGuardLeft, ?_⟩, ?_⟩
    · intro j hj hj'
      apply cycle_undamaged_pair_blue n blue starts loss hpack a ha haGood
      have hcase : j = a.val ∨ j = a.val + 1 := by omega
      rcases hcase with h | h
      · rw [h, cycleAt_coe]
        simp
      · rw [h, cycleAt_succ, cycleAt_coe]
        simp
    · intro s hs
      obtain ⟨hsMem, hs0, hsLt⟩ := (mem_cyclePrefix n starts a.val s).mp hs
      by_cases ht : s.val ≤ target.val
      · exact hPrior ((mem_cyclePrefix n starts (target.val + 1) s).mpr
          ⟨hsMem, hs0, by omega⟩)
      · by_contra hsGood
        have hsLater : s ∈ later := Finset.mem_filter.mpr ⟨hsMem, by omega, hsGood⟩
        have hmin : a.val ≤ s.val := Finset.min'_le later s hsLater
        omega
  · refine ⟨n + 3, le_rfl, target.isLt, ⟨hGuardLeft, ?_⟩, ?_⟩
    · intro j hj hj'
      apply hBase
      have hcase : j = n + 3 ∨ j = n + 3 + 1 := by omega
      rcases hcase with h | h
      · rw [h, cycleAt_wrap_zero]
        simp
      · rw [h, cycleAt_wrap_one]
        simp
    · intro s hs
      obtain ⟨hsMem, hs0, _⟩ := (mem_cyclePrefix n starts (n + 3) s).mp hs
      by_cases ht : s.val ≤ target.val
      · exact hPrior ((mem_cyclePrefix n starts (target.val + 1) s).mpr
          ⟨hsMem, hs0, by omega⟩)
      · by_contra hsGood
        exact hn ⟨s, Finset.mem_filter.mpr ⟨hsMem, by omega, hsGood⟩⟩

theorem cycle_target_finishes_from_anchored_window (n : ℕ)
    (blue support starts loss : Finset (Fin (n + 3)))
    (hpack : CyclePairPacking n blue starts) (h0 : 0 ∈ starts)
    (hgood0 : 0 ∉ cycleDamaged n starts loss) (hcard : starts.card = support.card)
    (hminimum : IsMinimumKilling (SimpleGraph.cycleGraph (n + 3)).Adj blue support)
    (budget deadline : ℕ) (hsmall : budget < support.card) (hLoss : loss.card ≤ budget)
    (hrobust : RobustBy (SimpleGraph.cycleGraph (n + 3)).Adj blue support budget deadline)
    (target : Fin (n + 3)) (ht2 : 2 ≤ target.val)
    (hPrior : cyclePrefix n starts (target.val + 1) ⊆ cycleDamaged n starts loss) :
    target ∈ colorAfter (SimpleGraph.cycleGraph (n + 3)).Adj (blue \ loss) deadline := by
  classical
  obtain ⟨hi, hiBound, hTarget, hGuard, hDamaged⟩ :=
    cycle_intact_arc_after_target n blue starts loss hpack h0 hgood0 target hPrior
  have hErase : budget ≤ (starts.erase 0).card := by
    rw [Finset.card_erase_of_mem h0, hcard]
    omega
  obtain ⟨long, longBound, longCard, longEnd⟩ := cycle_prefix_exists_of_card_ge n budget starts hErase
  have hWide : hi ≤ long := by
    by_contra hn
    have hl : long < hi := by omega
    obtain ⟨a, haErase, haVal⟩ := longEnd (by omega)
    have hsub : cyclePrefix n starts long ⊆ cycleDamaged n starts loss := by
      intro s hs
      obtain ⟨hsStart, hs0, hsVal⟩ := (mem_cyclePrefix n starts long s).mp hs
      exact hDamaged ((mem_cyclePrefix n starts hi s).mpr ⟨hsStart, hs0, by omega⟩)
    have haDamaged : a ∈ cycleDamaged n starts loss := hDamaged
      ((mem_cyclePrefix n starts hi a).mpr ⟨(Finset.mem_erase.mp haErase).2,
        (Finset.mem_erase.mp haErase).1, by omega⟩)
    have hstrict : cyclePrefix n starts long ⊂ cycleDamaged n starts loss := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨hsub, ?_⟩
      intro heq
      rw [← heq] at haDamaged
      have haLess := ((mem_cyclePrefix n starts long a).mp haDamaged).2.2
      omega
    have hcardLt := Finset.card_lt_card hstrict
    have hdCount := cycle_damaged_card_le n blue starts loss hpack
    omega
  have hUpper := cycle_restricted_prefix_white_bound n blue support starts hpack h0 hcard
    hminimum long budget deadline longEnd longCard hrobust
  have hIncl : cycleArc n 2 hi \ (blue \ loss) ⊆ (cycleArc n 2 long \ blue) ∪ loss := by
    intro s hs
    obtain ⟨hReg, hWhite⟩ := Finset.mem_sdiff.mp hs
    by_cases hBlue : s ∈ blue
    · have hLost : s ∈ loss := by
        by_contra hNotLost
        exact hWhite (Finset.mem_sdiff.mpr ⟨hBlue, hNotLost⟩)
      exact Finset.mem_union_right _ hLost
    · have hsReg := (mem_cycleArc n 2 hi s).mp hReg
      exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
        ⟨(mem_cycleArc n 2 long s).mpr ⟨hsReg.1, by omega⟩, hBlue⟩)
  have hCount := (Finset.card_le_card hIncl).trans (Finset.card_union_le _ _)
  have hNarrow : (cycleArc n 2 hi \ (blue \ loss)).card ≤ 2 * deadline := by omega
  exact cycle_arc_finishes_of_white_card_le n (blue \ loss) 2 hi (by decide) hiBound hGuard
    deadline hNarrow ((mem_cycleArc n 2 hi target).mpr ⟨ht2, hTarget⟩)

private theorem mem_relabelColors_apply {V : Type*} (e : V ≃ V)
    (s : Finset V) (v : V) :
    e v ∈ relabelColors e s ↔ v ∈ s := by
  rw [mem_relabelColors, Equiv.symm_apply_apply]

theorem cycle_mem_damaged_rotate_iff (n : ℕ) (a s : Fin (n + 3))
    (starts loss : Finset (Fin (n + 3))) :
    let e := (cycleRotation n a).symm
    e s ∈ cycleDamaged n (relabelColors e starts) (relabelColors e loss) ↔
      s ∈ cycleDamaged n starts loss := by
  let e := (cycleRotation n a).symm
  change e s ∈ cycleDamaged n (relabelColors e starts) (relabelColors e loss) ↔
    s ∈ cycleDamaged n starts loss
  rw [mem_cycleDamaged, mem_cycleDamaged, mem_relabelColors_apply]
  have hpair : relabelColors e (cyclePair n s) = cyclePair n (e s) :=
    cycle_relabel_pair n a s
  rw [← hpair]
  constructor
  · rintro ⟨hs, v, hvPair, hvLoss⟩
    obtain ⟨w, rfl⟩ := e.surjective v
    exact ⟨hs, w, (mem_relabelColors_apply e _ _).mp hvPair,
      (mem_relabelColors_apply e _ _).mp hvLoss⟩
  · rintro ⟨hs, w, hwPair, hwLoss⟩
    exact ⟨hs, e w, (mem_relabelColors_apply e _ _).mpr hwPair,
      (mem_relabelColors_apply e _ _).mpr hwLoss⟩

/-- Rotate the nearest surviving pair before a white target to zero. -/
theorem cycle_target_finishes_from_restricted (n : ℕ)
    (blue support starts loss : Finset (Fin (n + 3)))
    (hpack : CyclePairPacking n blue starts) (hcard : starts.card = support.card)
    (hminimum : IsMinimumKilling (SimpleGraph.cycleGraph (n + 3)).Adj blue support)
    (budget deadline : ℕ) (hsmall : budget < support.card) (hLoss : loss.card ≤ budget)
    (hrobust : RobustBy (SimpleGraph.cycleGraph (n + 3)).Adj blue support budget deadline)
    (target : Fin (n + 3)) :
    target ∈ colorAfter (SimpleGraph.cycleGraph (n + 3)).Adj (blue \ loss) deadline := by
  classical
  let adj := (SimpleGraph.cycleGraph (n + 3)).Adj
  by_cases hblue : target ∈ blue \ loss
  · exact colorAfter_mono_time adj (blue \ loss) (Nat.zero_le deadline) hblue
  let bad := cycleDamaged n starts loss
  have hcount : bad.card ≤ loss.card := cycle_damaged_card_le n blue starts loss hpack
  have hlt : bad.card < starts.card := by omega
  let good := starts \ bad
  have hgood : good.Nonempty := Finset.sdiff_nonempty_of_card_lt_card hlt
  obtain ⟨pivot, hp, hopt⟩ := Finset.exists_min_image good
    (fun a => (target - a).val) hgood
  obtain ⟨hpStart, hpGood⟩ := Finset.mem_sdiff.mp hp
  let e := (cycleRotation n pivot).symm
  let blue' := relabelColors e blue
  let support' := relabelColors e support
  let starts' := relabelColors e starts
  let loss' := relabelColors e loss
  let bad' := cycleDamaged n starts' loss'
  have heAdj (x y) : adj (e x) (e y) ↔ adj x y := cycle_rotation_symm_adj n pivot x y
  have hpack' : CyclePairPacking n blue' starts' :=
    cycle_pair_packing_rotate n blue starts hpack pivot
  have hp0 : e pivot = 0 := by
    change pivot - pivot = 0
    exact sub_self pivot
  have hStart0 : 0 ∈ starts' := by
    rw [← hp0]
    exact (mem_relabelColors_apply e starts pivot).mpr hpStart
  have hGood0 : 0 ∉ bad' := by
    rw [← hp0]
    exact fun hm => hpGood ((cycle_mem_damaged_rotate_iff n pivot pivot starts loss).mp hm)
  have hxWhite : e target ∉ blue' \ loss' := by
    change e target ∉ relabelColors e blue \ relabelColors e loss
    rwa [← relabelColors_sdiff, mem_relabelColors_apply]
  have ht2 : 2 ≤ (e target).val := by
    by_contra h
    have hzeroOne : (e target).val = 0 ∨ (e target).val = 1 := by omega
    apply hxWhite
    apply cycle_undamaged_pair_blue n blue' starts' loss' hpack' 0 hStart0 hGood0
    rcases hzeroOne with h0 | h1
    · have ht : e target = 0 := Fin.ext h0
      simp [ht]
    · have ht : e target = 1 := Fin.ext h1
      simp [ht]
  have hPrior : cyclePrefix n starts' ((e target).val + 1) ⊆ bad' := by
    intro s hs
    obtain ⟨hsStart, hs0, hsPos⟩ := (mem_cyclePrefix n starts' _ s).mp hs
    by_contra hsGood
    let w := e.symm s
    have hwE : e w = s := e.apply_symm_apply s
    have hwStart : w ∈ starts := (mem_relabelColors_apply e starts w).mp (hwE ▸ hsStart)
    have hwGood : w ∉ bad := by
      intro hw
      have hr := (cycle_mem_damaged_rotate_iff n pivot w starts loss).mpr hw
      change e w ∈ bad' at hr
      exact hsGood (hwE ▸ hr)
    have hcmp := hopt w (Finset.mem_sdiff.mpr ⟨hwStart, hwGood⟩)
    change (e target).val ≤ (target - w).val at hcmp
    have heq : e target - s = target - w := by
      rw [← hwE]
      change (target - pivot) - (w - pivot) = target - w
      exact sub_sub_sub_cancel_right _ _ _
    have hdist : (e target - s).val = (e target).val - s.val :=
      Fin.sub_val_of_le (show s ≤ e target from by change s.val ≤ (e target).val; omega)
    rw [← heq, hdist] at hcmp
    have hsNonzero : s.val ≠ 0 := fun hv => hs0 (Fin.ext hv)
    omega
  have hcard' : starts'.card = support'.card := by
    simpa only [starts', support', relabelColors_card] using hcard
  have hminimum' := (IsMinimumKilling_relabel_iff e adj adj heAdj blue support).mpr hminimum
  have hsmall' : budget < support'.card := by
    simpa only [support', relabelColors_card] using hsmall
  have hLoss' : loss'.card ≤ budget := by simpa only [loss', relabelColors_card] using hLoss
  have hrobust' := (RobustBy_relabel_iff e adj adj heAdj blue support budget deadline).mpr hrobust
  have hcolored := cycle_target_finishes_from_anchored_window n blue' support' starts' loss'
    hpack' hStart0 hGood0 hcard' hminimum' budget deadline hsmall' hLoss' hrobust'
    (e target) ht2 hPrior
  change e target ∈ colorAfter adj (relabelColors e blue \ relabelColors e loss) deadline at hcolored
  rwa [← relabelColors_sdiff, ← colorAfter_relabel e adj adj heAdj,
    mem_relabelColors_apply] at hcolored

/-- Every finite simple cycle satisfies the unrestricted versus restricted
deadline equivalence, for every forcing set and minimum killing set. -/
theorem cycle_everyMinimumSupport (n : ℕ) :
    EveryMinimumSupport (SimpleGraph.cycleGraph (n + 3)).Adj := by
  apply (cycle_everyMinimumSupport_iff_white_zero n).mpr
  intro blue hcut _ support hminimum budget deadline
  constructor
  · intro h loss hsub hcard
    exact h loss (fun v hv => hminimum.1 (hsub hv)) hcard
  · intro hRestricted
    have hk : budget < support.card := by
      by_contra hn
      exact hminimum.2.1 ⟨deadline, hRestricted support (fun _ x => x) (by omega)⟩
    obtain ⟨starts, hpack, hcard⟩ := cycle_exists_start_packing_at_white_zero n blue
      support hcut hminimum
    intro loss _ hLoss
    exact Finset.eq_univ_of_forall (cycle_target_finishes_from_restricted n blue support
      starts loss hpack hcard hminimum budget deadline hk hLoss hRestricted)

theorem cycle_everyMinimumSupportTime (n : ℕ) :
    EveryMinimumSupportTime (SimpleGraph.cycleGraph (n + 3)).Adj :=
  (everyMinimumSupport_iff_worstTime _).mp (cycle_everyMinimumSupport n)

theorem everyMinimumSupport_of_cycleGraph_iso {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (n : ℕ) (iso : G ≃g SimpleGraph.cycleGraph (n + 3)) :
    EveryMinimumSupport G.Adj :=
  (EveryMinimumSupport_relabel_iff iso.toEquiv G.Adj (SimpleGraph.cycleGraph (n + 3)).Adj
    (fun _ _ => iso.map_rel_iff)).mp (cycle_everyMinimumSupport n)

#print axioms cycle_target_finishes_from_anchored_window
#print axioms cycle_everyMinimumSupport
#print axioms cycle_everyMinimumSupportTime
#print axioms everyMinimumSupport_of_cycleGraph_iso

end FaultObservationResearch
