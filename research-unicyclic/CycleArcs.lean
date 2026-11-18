module

public import CycleSeeds

@[expose] public section

set_option autoImplicit false

namespace FaultObservationResearch

open Fin.NatCast

/-- Natural coordinates around a cycle, allowing coordinates past the cut. -/
def cycleAt (n i : ℕ) : Fin (n + 3) := Fin.ofNat (n + 3) i

theorem cycleAt_succ (n i : ℕ) : cycleAt n (i + 1) = cycleAt n i + 1 := by
  simp [cycleAt, Fin.ofNat_eq_cast, Nat.cast_succ]

theorem cycleAt_pred (n i : ℕ) (hi : 0 < i) :
    cycleAt n (i - 1) = cycleAt n i - 1 := by
  have hs := cycleAt_succ n (i - 1)
  rw [show i - 1 + 1 = i by omega] at hs
  rw [hs, add_sub_cancel_right]

theorem cycleAt_val_of_lt (n i : ℕ) (hi : i < n + 3) :
    (cycleAt n i).val = i := by
  change i % (n + 3) = i
  exact Nat.mod_eq_of_lt hi

@[simp] theorem cycleAt_coe (n : ℕ) (v : Fin (n + 3)) : cycleAt n v.val = v :=
  Fin.ext (cycleAt_val_of_lt n v.val v.isLt)

/-- The half-open arc after cutting the cycle at zero. The last edge may wrap
to zero, since the upper endpoint is a natural coordinate. -/
def cycleArc (n lo hi : ℕ) : Finset (Fin (n + 3)) :=
  Finset.univ.filter fun v => lo ≤ v.val ∧ v.val < hi

@[simp] theorem mem_cycleArc (n lo hi : ℕ) (v : Fin (n + 3)) :
    v ∈ cycleArc n lo hi ↔ lo ≤ v.val ∧ v.val < hi := by
  simp [cycleArc]

/-- Two permanently blue vertices at each end of an arc. The end pairs may
share vertices, or be the same pair when all other vertices lie in the arc. -/
def CycleArcGuards (n : ℕ) (blue : Finset (Fin (n + 3))) (lo hi : ℕ) : Prop :=
  (∀ j, lo - 2 ≤ j → j < lo → cycleAt n j ∈ blue) ∧
  (∀ j, hi ≤ j → j < hi + 2 → cycleAt n j ∈ blue)

theorem cycle_arc_finishes_of_white_card_le (n : ℕ)
    (blue : Finset (Fin (n + 3))) (lo hi : ℕ)
    (hlo : 2 ≤ lo) (hhi : hi ≤ n + 3)
    (hguards : CycleArcGuards n blue lo hi)
    (t : ℕ) (hcount : (cycleArc n lo hi \ blue).card ≤ 2 * t) :
    cycleArc n lo hi ⊆ colorAfter (SimpleGraph.cycleGraph (n + 3)).Adj blue t := by
  let G := SimpleGraph.cycleGraph (n + 3)
  let region := cycleArc n lo hi
  have hforcing : IsForcing G.Adj blue := by
    apply (cycle_forcing_iff_adjacent_pair n blue).mpr
    refine ⟨cycleAt n (lo - 2), hguards.1 _ (by omega) (by omega),
      cycleAt n (lo - 1), hguards.1 _ (by omega) (by omega), ?_⟩
    apply (cycle_adj_iff_neighbors n _ _).mpr
    right
    rw [← cycleAt_succ, show lo - 2 + 1 = lo - 1 by omega]
  have band (j : ℕ) (hL : lo - 2 ≤ j) (hR : j < hi + 2) :
      cycleAt n j ∈ region ∨ cycleAt n j ∈ blue := by
    by_cases hl : j < lo
    · exact Or.inr (hguards.1 j hL hl)
    by_cases hh : hi ≤ j
    · exact Or.inr (hguards.2 j hh hR)
    left
    apply (mem_cycleArc n lo hi _).mpr
    rw [cycleAt_val_of_lt n j (by omega)]
    omega
  apply cycle_guarded_region_finishesBy n region blue blue (fun _ h => h) hforcing _ t hcount
  intro target ht source hs
  obtain ⟨hL, hR⟩ := (mem_cycleArc n lo hi target).mp ht
  have hsource (j : ℕ) (hjL : lo - 1 ≤ j) (hjR : j ≤ hi)
      (heq : source = cycleAt n j) :
      (source ∈ region ∨ source ∈ blue) ∧
        ∀ w, G.Adj source w → w ∈ region ∨ w ∈ blue := by
    refine ⟨heq.symm ▸ band j (by omega) (by omega), ?_⟩
    intro w hw
    rcases (cycle_adj_iff_neighbors n source w).mp hw with hw | hw
    · rw [hw, heq, ← cycleAt_pred n j (by omega)]
      exact band (j - 1) (by omega) (by omega)
    · rw [hw, heq, ← cycleAt_succ]
      exact band (j + 1) (by omega) (by omega)
  rcases (cycle_adj_iff_neighbors n target source).mp hs.symm with hh | hh
  · apply hsource (target.val - 1) (by omega) (by omega)
    rw [cycleAt_pred n target.val (by omega), cycleAt_coe]
    exact hh
  · apply hsource (target.val + 1) (by omega) (by omega)
    rw [cycleAt_succ, cycleAt_coe]
    exact hh

/-- Consecutive vertices in the sorted white set cannot skip two adjacent
blue vertices of the arc. -/
private theorem cycle_arc_sorted_white_gap (n : ℕ)
    (blue : Finset (Fin (n + 3))) (lo hi : ℕ)
    (hnoPair : ∀ u ∈ cycleArc n lo hi, ∀ v ∈ cycleArc n lo hi,
      (SimpleGraph.cycleGraph (n + 3)).Adj u v → u ∉ blue ∨ v ∉ blue)
    (i : ℕ) (hiIndex : i + 1 < (cycleArc n lo hi \ blue).card) :
    let whites := cycleArc n lo hi \ blue
    let e := whites.orderEmbOfFin (k := whites.card) rfl
    let a := e ⟨i, lt_trans (Nat.lt_succ_self i) hiIndex⟩
    let b := e ⟨i + 1, hiIndex⟩
    b = a + 1 ∨ b = (a + 1) + 1 := by
  let whites := cycleArc n lo hi \ blue
  let e := whites.orderEmbOfFin (k := whites.card) rfl
  let left : Fin whites.card := ⟨i, lt_trans (Nat.lt_succ_self i) hiIndex⟩
  let right : Fin whites.card := ⟨i + 1, hiIndex⟩
  let a := e left
  let b := e right
  change b = a + 1 ∨ b = (a + 1) + 1
  have ha : a ∈ whites := whites.orderEmbOfFin_mem rfl left
  have hb : b ∈ whites := whites.orderEmbOfFin_mem rfl right
  have hlo := ((mem_cycleArc n lo hi a).mp (Finset.mem_sdiff.mp ha).1).1
  have hhi := ((mem_cycleArc n lo hi b).mp (Finset.mem_sdiff.mp hb).1).2
  have hab : a.val < b.val := e.strictMono (show left < right from Nat.lt_succ_self i)
  have hmid (u : Fin (n + 3)) (hua : a.val < u.val) (hub : u.val < b.val) :
      u ∈ cycleArc n lo hi ∧ u ∈ blue := by
    have hregion : u ∈ cycleArc n lo hi := (mem_cycleArc n lo hi u).mpr (by omega)
    refine ⟨hregion, ?_⟩
    by_contra hwhite
    have hmem : u ∈ Set.range e := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_sdiff.mpr ⟨hregion, hwhite⟩
    obtain ⟨j, rfl⟩ := hmem
    have hleft : left < j := e.lt_iff_lt.mp hua
    have hright : j < right := e.lt_iff_lt.mp hub
    change i < j.val at hleft
    change j.val < i + 1 at hright
    omega
  have hgap : b.val ≤ a.val + 2 := by
    by_contra h
    let u := cycleAt n (a.val + 1)
    let v := cycleAt n (a.val + 2)
    have hu : u.val = a.val + 1 := cycleAt_val_of_lt n _ (by have := b.isLt; omega)
    have hv : v.val = a.val + 2 := cycleAt_val_of_lt n _ (by have := b.isLt; omega)
    obtain ⟨hur, hub⟩ := hmid u (by omega) (by omega)
    obtain ⟨hvr, hvb⟩ := hmid v (by omega) (by omega)
    have hadj : (SimpleGraph.cycleGraph (n + 3)).Adj u v :=
      (cycle_adj_iff_neighbors n _ _).mpr (Or.inr (cycleAt_succ n (a.val + 1)))
    exact (hnoPair u hur v hvr hadj).elim (fun hn => hn hub) (fun hn => hn hvb)
  by_cases h : b.val = a.val + 1
  · left
    calc
      b = cycleAt n (a.val + 1) :=
        Fin.ext (h.trans (cycleAt_val_of_lt n _ (by have := b.isLt; omega)).symm)
      _ = a + 1 := by rw [cycleAt_succ, cycleAt_coe]
  · right
    calc
      b = cycleAt n (a.val + 2) :=
        Fin.ext (by rw [cycleAt_val_of_lt n _ (by have := b.isLt; omega)]; omega)
      _ = (a + 1) + 1 := by
        rw [show a.val + 2 = a.val + 1 + 1 by omega, cycleAt_succ n (a.val + 1),
          cycleAt_succ n a.val, cycleAt_coe]

theorem cycle_arc_white_card_le_of_finishes (n : ℕ)
    (blue : Finset (Fin (n + 3))) (lo hi : ℕ)
    (hnoPair : ∀ u ∈ cycleArc n lo hi, ∀ v ∈ cycleArc n lo hi,
      (SimpleGraph.cycleGraph (n + 3)).Adj u v → u ∉ blue ∨ v ∉ blue)
    (t : ℕ) (hfin : cycleArc n lo hi ⊆
      colorAfter (SimpleGraph.cycleGraph (n + 3)).Adj blue t) :
    (cycleArc n lo hi \ blue).card ≤ 2 * t := by
  classical
  let whites := cycleArc n lo hi \ blue
  let white (i : ℕ) : Fin (n + 3) :=
    if h : i < whites.card then whites.orderEmbOfFin rfl ⟨i, h⟩ else 0
  have hwMem (i : ℕ) (hiIndex : i < whites.card) : white i ∈ whites := by
    simp [white, hiIndex]
  have hgap : ∀ i, i + 1 < whites.card →
      white (i + 1) = white i + 1 ∨ white (i + 1) = (white i + 1) + 1 := by
    intro i hiIndex
    simpa [white, hiIndex, show i < whites.card by omega] using
      cycle_arc_sorted_white_gap n blue lo hi hnoPair i hiIndex
  by_contra h
  have ht : 2 * t < whites.card := by
    change ¬ whites.card ≤ 2 * t at h
    omega
  have hs := cycle_white_chain_survives n blue whites.card white
    (fun i hiIndex => (Finset.mem_sdiff.mp (hwMem i hiIndex)).2) hgap
    t t le_rfl (by omega)
  exact hs (hfin (Finset.mem_sdiff.mp (hwMem t (by omega))).1)

/-- White vertices on an arc with blue end pairs and no internal blue pair
take exactly half the white count, rounded up, to finish. -/
theorem cycle_arc_finishes_iff_white_card_le (n : ℕ)
    (blue : Finset (Fin (n + 3))) (lo hi : ℕ)
    (hlo : 2 ≤ lo) (hhi : hi ≤ n + 3)
    (hguards : CycleArcGuards n blue lo hi)
    (hnoPair : ∀ u ∈ cycleArc n lo hi, ∀ v ∈ cycleArc n lo hi,
      (SimpleGraph.cycleGraph (n + 3)).Adj u v → u ∉ blue ∨ v ∉ blue)
    (t : ℕ) :
    cycleArc n lo hi ⊆ colorAfter (SimpleGraph.cycleGraph (n + 3)).Adj blue t ↔
      (cycleArc n lo hi \ blue).card ≤ 2 * t :=
  ⟨cycle_arc_white_card_le_of_finishes n blue lo hi hnoPair t,
    cycle_arc_finishes_of_white_card_le n blue lo hi hlo hhi hguards t⟩

#print axioms cycle_arc_finishes_iff_white_card_le

end FaultObservationResearch
