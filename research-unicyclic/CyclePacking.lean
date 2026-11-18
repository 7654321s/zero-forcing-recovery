module

public import CycleArcs
public import Mathlib.Order.Interval.Finset.Fin

@[expose] public section

set_option autoImplicit false

namespace FaultObservationResearch

def cyclePair (n : ℕ) (a : Fin (n + 3)) : Finset (Fin (n + 3)) := {a, a + 1}

@[simp] theorem mem_cyclePair (n : ℕ) (a x : Fin (n + 3)) :
    x ∈ cyclePair n a ↔ x = a ∨ x = a + 1 := by
  simp [cyclePair]

theorem cycle_pair_forcing (n : ℕ) (a : Fin (n + 3)) :
    IsForcing (SimpleGraph.cycleGraph (n + 3)).Adj (cyclePair n a) := by
  classical
  exact (cycle_forcing_iff_adjacent_pair n _).mpr
    ⟨a, by simp, a + 1, by simp, (cycle_adj_iff_neighbors n _ _).mpr (Or.inr rfl)⟩

/-- The vertex labels mark the first vertices of pairwise disjoint blue edges. -/
structure CyclePairPacking (n : ℕ) (blue starts : Finset (Fin (n + 3))) : Prop where
  blue_pair : ∀ a ∈ starts, cyclePair n a ⊆ blue
  disjoint : ∀ a ∈ starts, ∀ b ∈ starts, a ≠ b → Disjoint (cyclePair n a) (cyclePair n b)

theorem cycle_exists_start_packing_at_white_zero (n : ℕ)
    (blue support : Finset (Fin (n + 3))) (hcut : 0 ∉ blue)
    (hminimum : IsMinimumKilling (SimpleGraph.cycleGraph (n + 3)).Adj blue support) :
    ∃ starts, CyclePairPacking n blue starts ∧ starts.card = support.card := by
  classical
  obtain ⟨units, cover, pick, hpack, _, hpick⟩ :=
    cycle_exists_pair_packing_selector_at_white_zero n blue support hcut hminimum
  have hpair : ∀ i : Fin units.length, ∃ u v : Fin (n + 3),
      u.val + 1 = v.val ∧ PathIndexedCell (n := n + 2) units i = {u, v} := by
    intro i
    obtain ⟨u, _, v, _, huv, heq⟩ := hpack.pairs _ (List.getElem_mem i.isLt)
    exact ⟨u, v, huv, heq⟩
  choose left right hdiff heq using hpair
  have hcell (i : Fin units.length) :
      PathIndexedCell (n := n + 2) units i = cyclePair n (left i) := by
    have hr : right i = left i + 1 := by
      calc
        right i = cycleAt n ((left i).val + 1) := by
          rw [hdiff i, cycleAt_coe]
        _ = left i + 1 := by rw [cycleAt_succ, cycleAt_coe]
    rw [heq i, hr]
    rfl
  have hdis : DisjointForcingCells (PathIndexedCell (n := n + 2) units) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact pathCellBefore_disjoint (n + 2) _ _
        (List.Pairwise.rel_getElem_of_lt i.isLt j.isLt hpack.ordered h)
    · exact (pathCellBefore_disjoint (n + 2) _ _
        (List.Pairwise.rel_getElem_of_lt j.isLt i.isLt hpack.ordered h)).symm
  have hleft : Function.Injective left := by
    intro i j hij
    by_contra hn
    have ha : left i ∈ PathIndexedCell (n := n + 2) units i := by rw [hcell]; simp
    have hb : left i ∈ PathIndexedCell (n := n + 2) units j := by rw [hcell, hij]; simp
    exact (Finset.disjoint_left.mp (hdis i j hn)) ha hb
  let starts := Finset.univ.image left
  refine ⟨starts, ⟨?_, ?_⟩, ?_⟩
  · intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    rw [← hcell i]
    exact pathPairCoverPacking_cell_subset (n + 2) blue units cover hpack _
      (List.getElem_mem i.isLt)
  · intro a ha b hb hne
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    rw [← hcell i, ← hcell j]
    exact hdis i j (fun h => hne (congrArg left h))
  · rw [hpick.2.2.1]
    exact (Finset.card_image_of_injective _ hleft).trans
      (Finset.card_image_of_injective _ hpick.1).symm

theorem cycle_pair_packing_exact_selector (n : ℕ)
    (blue support starts : Finset (Fin (n + 3)))
    (hpack : CyclePairPacking n blue starts) (hcard : starts.card = support.card)
    (hminimum : IsMinimumKilling (SimpleGraph.cycleGraph (n + 3)).Adj blue support) :
    ∃ pick : starts → Fin (n + 3),
      ExactCellSelection (fun a : starts => cyclePair n a.val) support pick := by
  apply exists_exact_cell_selector
  · intro a b hne
    exact hpack.disjoint a.val a.property b.val b.property (fun h => hne (Subtype.ext h))
  · intro a
    exact minimumKilling_hits_forcing_subset _ blue support _ hminimum
      (hpack.blue_pair a.val a.property) (cycle_pair_forcing n a.val)
  · simpa using hcard.symm

theorem cycle_relabel_pair (n : ℕ) (a s : Fin (n + 3)) :
    relabelColors (cycleRotation n a).symm (cyclePair n s) =
      cyclePair n ((cycleRotation n a).symm s) := by
  classical
  have hshift : (cycleRotation n a).symm (s + 1) = (cycleRotation n a).symm s + 1 := by
    change s + 1 - a = s - a + 1
    rw [add_sub_right_comm, sub_add_eq_add_sub]
  simp [cyclePair, relabelColors, hshift]

theorem cycle_pair_packing_rotate (n : ℕ) (blue starts : Finset (Fin (n + 3)))
    (hpack : CyclePairPacking n blue starts) (a : Fin (n + 3)) :
    CyclePairPacking n (relabelColors (cycleRotation n a).symm blue)
      (relabelColors (cycleRotation n a).symm starts) := by
  let e := (cycleRotation n a).symm
  constructor
  · intro s hs
    obtain ⟨u, rfl⟩ := e.surjective s
    change e u ∈ relabelColors e starts at hs
    have hu : u ∈ starts := by
      rwa [mem_relabelColors, Equiv.symm_apply_apply] at hs
    rw [← cycle_relabel_pair n a u]
    exact (relabelColors_subset_iff e _ _).mpr (hpack.blue_pair u hu)
  · intro s hs t ht hne
    obtain ⟨u, rfl⟩ := e.surjective s
    obtain ⟨v, rfl⟩ := e.surjective t
    change e u ∈ relabelColors e starts at hs
    change e v ∈ relabelColors e starts at ht
    have hu : u ∈ starts := by
      rwa [mem_relabelColors, Equiv.symm_apply_apply] at hs
    have hv : v ∈ starts := by
      rwa [mem_relabelColors, Equiv.symm_apply_apply] at ht
    have hdis := hpack.disjoint u hu v hv (fun h => hne (congrArg e h))
    rw [← cycle_relabel_pair n a u, ← cycle_relabel_pair n a v]
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.disjoint_left.mp hdis) ((mem_relabelColors e _ x).mp hx)
      ((mem_relabelColors e _ x).mp hy)

def cycleDamaged (n : ℕ) (starts loss : Finset (Fin (n + 3))) : Finset (Fin (n + 3)) :=
  starts.filter fun a => (cyclePair n a ∩ loss).Nonempty

@[simp] theorem mem_cycleDamaged (n : ℕ) (starts loss : Finset (Fin (n + 3)))
    (a : Fin (n + 3)) :
    a ∈ cycleDamaged n starts loss ↔ a ∈ starts ∧
      ∃ x ∈ cyclePair n a, x ∈ loss := by
  simp [cycleDamaged, Finset.Nonempty]

theorem cycle_damaged_card_le (n : ℕ) (blue starts loss : Finset (Fin (n + 3)))
    (hpack : CyclePairPacking n blue starts) :
    (cycleDamaged n starts loss).card ≤ loss.card := by
  classical
  let bad := cycleDamaged n starts loss
  have hh : ∀ a : bad, ∃ x ∈ cyclePair n a.val, x ∈ loss :=
    fun a => ((mem_cycleDamaged n starts loss _).mp a.property).2
  have hd : DisjointForcingCells (fun a : bad => cyclePair n a.val) := by
    intro a b hne
    exact hpack.disjoint a.val ((mem_cycleDamaged n starts loss _).mp a.property).1
      b.val ((mem_cycleDamaged n starts loss _).mp b.property).1 (fun heq => hne (Subtype.ext heq))
  have hcard := disjoint_cells_hitting_card_le _ hd loss hh
  rw [Fintype.card_coe] at hcard
  exact hcard

@[simp] theorem cycleAt_wrap_zero (n : ℕ) : cycleAt n (n + 3) = 0 := by
  apply Fin.ext
  change (n + 3) % (n + 3) = 0
  exact Nat.mod_self _

@[simp] theorem cycleAt_wrap_one (n : ℕ) : cycleAt n (n + 3 + 1) = 1 := by
  rw [cycleAt_succ, cycleAt_wrap_zero, zero_add]

theorem cycle_packing_start_bounds (n : ℕ) (blue starts : Finset (Fin (n + 3)))
    (hpack : CyclePairPacking n blue starts) (h0 : 0 ∈ starts)
    (a : Fin (n + 3)) (ha : a ∈ starts) (ha0 : a ≠ 0) :
    2 ≤ a.val ∧ a.val + 1 < n + 3 := by
  have hdis := Finset.disjoint_left.mp (hpack.disjoint a ha 0 h0 ha0)
  constructor
  · by_contra h
    have hval0 : a.val ≠ 0 := fun he => ha0 (Fin.ext he)
    have ha1 : a = 1 := Fin.ext (by simp only [Fin.val_one]; omega)
    exact hdis (show a ∈ cyclePair n a by simp)
      (show a ∈ cyclePair n 0 by simp [ha1])
  · by_contra h
    have hwrap : a.val + 1 = n + 3 := by have := a.isLt; omega
    have hnext : a + 1 = 0 := by
      calc
        a + 1 = cycleAt n (a.val + 1) := by rw [cycleAt_succ, cycleAt_coe]
        _ = cycleAt n (n + 3) := congrArg (cycleAt n) hwrap
        _ = 0 := cycleAt_wrap_zero n
    exact hdis (show 0 ∈ cyclePair n a by simp [hnext]) (show 0 ∈ cyclePair n 0 by simp)

def cyclePrefix (n : ℕ) (starts : Finset (Fin (n + 3))) (hi : ℕ) :
    Finset (Fin (n + 3)) :=
  (starts.erase 0).filter fun a => a.val < hi

@[simp] theorem mem_cyclePrefix (n : ℕ) (starts : Finset (Fin (n + 3))) (hi : ℕ)
    (a : Fin (n + 3)) :
    a ∈ cyclePrefix n starts hi ↔ a ∈ starts ∧ a ≠ 0 ∧ a.val < hi := by
  simp only [cyclePrefix, Finset.mem_filter, Finset.mem_erase]
  tauto

theorem cycle_prefix_exists_of_card_ge (n k : ℕ)
    (starts : Finset (Fin (n + 3))) (hk : k ≤ (starts.erase 0).card) :
    ∃ hi ≤ n + 3, (cyclePrefix n starts hi).card = k ∧
      (hi < n + 3 → ∃ a ∈ starts.erase 0, a.val = hi) := by
  classical
  let rest := starts.erase 0
  by_cases h : k = rest.card
  · refine ⟨n + 3, le_rfl, ?_, fun hn => False.elim (Nat.lt_irrefl _ hn)⟩
    have heq : cyclePrefix n starts (n + 3) = rest := by
      ext a
      simp [cyclePrefix, rest]
    rw [heq, h]
  · have hlt : k < rest.card := by
      change k ≤ rest.card at hk
      omega
    let index : Fin rest.card := ⟨k, hlt⟩
    let emb := rest.orderEmbOfFin (k := rest.card) rfl
    let a := emb index
    have harest : a ∈ rest := rest.orderEmbOfFin_mem rfl index
    refine ⟨a.val, a.isLt.le, ?_, fun _ => ⟨a, harest, rfl⟩⟩
    have heq : cyclePrefix n starts a.val = (Finset.Iio index).image emb := by
      ext b
      change (b ∈ rest.filter fun s => s.val < a.val) ↔ _
      constructor
      · intro hb
        obtain ⟨hbRest, hbLess⟩ := Finset.mem_filter.mp hb
        have hrange : b ∈ Set.range emb := by
          rw [Finset.range_orderEmbOfFin]
          exact hbRest
        obtain ⟨j, rfl⟩ := hrange
        exact Finset.mem_image.mpr ⟨j, Finset.mem_Iio.mpr (emb.lt_iff_lt.mp hbLess), rfl⟩
      · intro hb
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
        exact Finset.mem_filter.mpr ⟨rest.orderEmbOfFin_mem rfl j,
          emb.strictMono (Finset.mem_Iio.mp hj)⟩
    rw [heq, Finset.card_image_of_injective _ emb.injective]
    simp [index]

theorem cycle_pair_meets_arc_implies_prefix (n : ℕ) (blue starts : Finset (Fin (n + 3)))
    (hpack : CyclePairPacking n blue starts) (h0 : 0 ∈ starts) (hi : ℕ)
    (a v : Fin (n + 3)) (ha : a ∈ starts)
    (hvPair : v ∈ cyclePair n a) (hvArc : v ∈ cycleArc n 2 hi) :
    a ∈ cyclePrefix n starts hi := by
  obtain ⟨hv2, hvHi⟩ := (mem_cycleArc n 2 hi v).mp hvArc
  have ha0 : a ≠ 0 := by
    intro heq
    rcases (mem_cyclePair n a v).mp hvPair with hv | hv
    · simp [hv, heq] at hv2
    · simp [hv, heq] at hv2
  have habound := (cycle_packing_start_bounds n blue starts hpack h0 a ha ha0).2
  refine (mem_cyclePrefix n starts hi a).mpr ⟨ha, ha0, ?_⟩
  rcases (mem_cyclePair n a v).mp hvPair with hv | hv
  · rwa [hv] at hvHi
  · have hval : (a + 1).val = a.val + 1 := by
      simpa only [cycleAt_succ, cycleAt_coe] using
        cycleAt_val_of_lt n (a.val + 1) habound
    rw [hv, hval] at hvHi
    omega

theorem cycle_pair_subset_arc_of_prefix (n : ℕ) (blue starts : Finset (Fin (n + 3)))
    (hpack : CyclePairPacking n blue starts) (h0 : 0 ∈ starts) (hi : ℕ)
    (hend : hi < n + 3 → ∃ b ∈ starts.erase 0, b.val = hi)
    (a : Fin (n + 3)) (ha : a ∈ cyclePrefix n starts hi) :
    cyclePair n a ⊆ cycleArc n 2 hi := by
  obtain ⟨haStart, ha0, haHi⟩ := (mem_cyclePrefix n starts hi a).mp ha
  obtain ⟨ha2, haNoWrap⟩ := cycle_packing_start_bounds n blue starts hpack h0 a haStart ha0
  have hval : (a + 1).val = a.val + 1 := by
    simpa only [cycleAt_succ, cycleAt_coe] using
      cycleAt_val_of_lt n (a.val + 1) haNoWrap
  have hnext : a.val + 1 < hi := by
    by_contra h
    have hEq : a.val + 1 = hi := by omega
    obtain ⟨b, hb, hbHi⟩ := hend (by omega)
    have hne : a ≠ b := fun he => by
      have hv := congrArg Fin.val he
      omega
    have hab : a + 1 = b := Fin.ext (by omega)
    have hdis := Finset.disjoint_left.mp
      (hpack.disjoint a haStart b (Finset.mem_erase.mp hb).2 hne)
    exact hdis (show a + 1 ∈ cyclePair n a by simp) (show a + 1 ∈ cyclePair n b by simp [hab])
  intro v hv
  apply (mem_cycleArc n 2 hi v).mpr
  rcases (mem_cyclePair n a v).mp hv with h | h
  · rw [h]
    exact ⟨ha2, haHi⟩
  · rw [h, hval]
    omega

#print axioms cycle_exists_start_packing_at_white_zero
#print axioms cycle_pair_packing_rotate
#print axioms cycle_damaged_card_le
#print axioms cycle_prefix_exists_of_card_ge
#print axioms cycle_pair_subset_arc_of_prefix

end FaultObservationResearch
