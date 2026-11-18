module

/- Ready guards and maximal source-free intervals around a white path vertex. -/
public import «formalization-path-seed-packing»
public import «formalization-path-window-extension»
public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch

theorem path_zero_left_ready (n : ℕ) (blue : Finset (Fin (n + 1)))
    (hz : (0 : Fin (n + 1)) ∈ blue) : PathLeftReady n blue 0 := by
  refine ⟨hz, ?_⟩
  intro x _ hlt
  change x.val < 0 at hlt
  omega

theorem path_last_right_ready (n : ℕ) (blue : Finset (Fin (n + 1)))
    (hl : Fin.last n ∈ blue) : PathRightReady n blue (Fin.last n) := by
  refine ⟨hl, ?_⟩
  intro x _ hlt
  change n < x.val at hlt
  have hx := x.isLt
  omega

theorem path_pair_ready (n : ℕ) (blue : Finset (Fin (n + 1)))
    (u v : Fin (n + 1)) (hu : u ∈ blue) (hv : v ∈ blue) (huv : u.val + 1 = v.val) :
    PathRightReady n blue u ∧ PathLeftReady n blue v := by
  constructor
  · refine ⟨hu, ?_⟩
    intro x ha hlt
    have hAdj := SimpleGraph.pathGraph_adj.mp ha
    have hval : x.val = v.val := by omega
    have heq : x = v := Fin.ext hval
    rwa [heq]
  · refine ⟨hv, ?_⟩
    intro x ha hlt
    have hAdj := SimpleGraph.pathGraph_adj.mp ha
    have hval : x.val = u.val := by omega
    have heq : x = u := Fin.ext hval
    rwa [heq]

theorem pathForcingUnit_ready_around_white (n : ℕ) (blue cell : Finset (Fin (n + 1)))
    (hunit : PathForcingUnit n cell) (hsub : cell ⊆ blue)
    (white : Fin (n + 1)) (hw : white ∉ blue) :
    (∃ p ∈ cell, p.val < white.val ∧ PathLeftReady n blue p ∧ ∀ y ∈ cell, y.val ≤ p.val) ∨
    (∃ p ∈ cell, white.val < p.val ∧ PathRightReady n blue p ∧ ∀ y ∈ cell, p.val ≤ y.val) := by
  classical
  rcases hunit with hz | hl | ⟨u, v, huv, heq⟩
  · subst cell
    have hzB : (0 : Fin (n + 1)) ∈ blue := hsub (Finset.mem_singleton_self _)
    have hne : white.val ≠ 0 := by
      intro heq
      exact hw (by rw [show white = 0 from Fin.ext heq]; exact hzB)
    left
    refine ⟨0, by simp, by change 0 < white.val; omega, path_zero_left_ready n blue hzB, ?_⟩
    intro y hy
    have heq : y = 0 := Finset.mem_singleton.mp hy
    rw [heq]
  · subst cell
    have hlB : Fin.last n ∈ blue := hsub (Finset.mem_singleton_self _)
    have hne : white.val ≠ n := by
      intro heq
      exact hw (by rw [show white = Fin.last n from Fin.ext heq]; exact hlB)
    right
    refine ⟨Fin.last n, by simp, ?_, path_last_right_ready n blue hlB, ?_⟩
    · change white.val < n
      have hx := white.isLt
      omega
    · intro y hy
      have heq : y = Fin.last n := Finset.mem_singleton.mp hy
      rw [heq]
  · subst cell
    have huB : u ∈ blue := hsub (by simp)
    have hvB : v ∈ blue := hsub (by simp)
    have hneU : white.val ≠ u.val := fun h => hw (by rw [Fin.ext h]; exact huB)
    have hneV : white.val ≠ v.val := fun h => hw (by rw [Fin.ext h]; exact hvB)
    have hr := path_pair_ready n blue u v huB hvB huv
    by_cases hbefore : v.val < white.val
    · left
      refine ⟨v, by simp, hbefore, hr.2, ?_⟩
      intro y hy
      rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hy) with hy | hy
      · rw [hy]
        omega
      · rw [hy]
    · right
      refine ⟨u, by simp, by omega, hr.1, ?_⟩
      intro y hy
      rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hy) with hy | hy
      · rw [hy]
      · rw [hy]
        omega

structure PathLeftGuard (n : ℕ) (blue : Finset (Fin (n + 1))) (white : Fin (n + 1))
    (low : ℕ) (left : Fin (n + 1)) : Prop where
  low_le : low ≤ white.val
  left_le : left.val ≤ white.val
  sources_before : ∀ y : Fin (n + 1), y.val < white.val → PathLeftReady n blue y → y.val < low
  kind : (low = 0 ∧ left = 0) ∨ (PathLeftReady n blue left ∧ low = left.val + 1)

structure PathRightGuard (n : ℕ) (blue : Finset (Fin (n + 1))) (white : Fin (n + 1))
    (high : ℕ) (right : Fin (n + 1)) : Prop where
  high_ge : white.val ≤ high
  high_le : high ≤ n
  right_ge : white.val ≤ right.val
  sources_after : ∀ y : Fin (n + 1), white.val < y.val → PathRightReady n blue y → high < y.val
  kind : (high = n ∧ right = Fin.last n) ∨ (PathRightReady n blue right ∧ high + 1 = right.val)

theorem exists_path_left_guard (n : ℕ) (blue : Finset (Fin (n + 1))) (white : Fin (n + 1)) :
    ∃ low left, PathLeftGuard n blue white low left := by
  classical
  let L := Finset.univ.filter (fun y : Fin (n + 1) => y.val < white.val ∧ PathLeftReady n blue y)
  by_cases hne : L.Nonempty
  · let p := L.max' hne
    have hp := (Finset.mem_filter.mp (L.max'_mem hne)).2
    refine ⟨p.val + 1, p, ?_⟩
    constructor
    · omega
    · omega
    · intro y hy hr
      have hyL : y ∈ L := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy, hr⟩
      have hle : y.val ≤ p.val := L.le_max' y hyL
      omega
    · exact Or.inr ⟨hp.2, rfl⟩
  · refine ⟨0, 0, ?_⟩
    constructor
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    · intro y hy hr
      exact False.elim (hne ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy, hr⟩⟩)
    · exact Or.inl ⟨rfl, rfl⟩

theorem exists_path_right_guard (n : ℕ) (blue : Finset (Fin (n + 1))) (white : Fin (n + 1)) :
    ∃ high right, PathRightGuard n blue white high right := by
  classical
  let R := Finset.univ.filter (fun y : Fin (n + 1) => white.val < y.val ∧ PathRightReady n blue y)
  by_cases hne : R.Nonempty
  · let p := R.min' hne
    have hp := (Finset.mem_filter.mp (R.min'_mem hne)).2
    have hpBound := p.isLt
    refine ⟨p.val - 1, p, ?_⟩
    constructor
    · omega
    · omega
    · omega
    · intro y hy hr
      have hyR : y ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy, hr⟩
      have hle : p.val ≤ y.val := R.min'_le y hyR
      omega
    · exact Or.inr ⟨hp.2, by omega⟩
  · refine ⟨n, Fin.last n, ?_⟩
    constructor
    · have hw := white.isLt
      omega
    · exact le_rfl
    · have hw := white.isLt
      change white.val ≤ n
      omega
    · intro y hy hr
      exact False.elim (hne ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy, hr⟩⟩)
    · exact Or.inl ⟨rfl, rfl⟩

theorem path_guard_interval_support_card_le_loss (n : ℕ)
    (blue support loss : Finset (Fin (n + 1)))
    (units : List (Finset (Fin (n + 1)))) (witness : Finset (Fin (n + 1)))
    (hpack : PathSeedPacking n blue units witness)
    (pick : Fin units.length → Fin (n + 1))
    (hsel : ExactCellSelection (PathIndexedCell units) support pick)
    (white : Fin (n + 1)) (hw : white ∉ blue \ loss)
    (low high : ℕ) (left right : Fin (n + 1))
    (hL : PathLeftGuard n (blue \ loss) white low left)
    (hR : PathRightGuard n (blue \ loss) white high right) :
    (PathRangeHits n support low high).card ≤ loss.card := by
  classical
  let chosen := Finset.univ.filter (fun i : Fin units.length => low ≤ (pick i).val ∧ (pick i).val ≤ high)
  let damaged := Finset.univ.filter (fun i : Fin units.length => ∃ x ∈ PathIndexedCell units i, x ∈ loss)
  have hchosen : chosen ⊆ damaged := by
    intro i hi
    have hpos := (Finset.mem_filter.mp hi).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    by_contra hnot
    have hsub : PathIndexedCell units i ⊆ blue \ loss := by
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨hpack.unit_subset _ (List.getElem_mem i.isLt) hx,
        fun hd => hnot ⟨x, hx, hd⟩⟩
    have hr := pathForcingUnit_ready_around_white n (blue \ loss) _
      (hpack.unit_kind _ (List.getElem_mem i.isLt)) hsub white hw
    rcases hr with ⟨p, _, hp, hready, hmax⟩ | ⟨p, _, hp, hready, hmin⟩
    · have hbound := hL.sources_before p hp hready
      have hpick := hmax (pick i) (hsel.2.1 i)
      omega
    · have hbound := hR.sources_after p hp hready
      have hpick := hmin (pick i) (hsel.2.1 i)
      omega
  have heq : PathRangeHits n support low high = chosen.image pick := by
    ext x
    constructor
    · intro hx
      have hi := Finset.mem_filter.mp hx
      have hxImage : x ∈ Finset.univ.image pick := by rw [← hsel.2.2.1]; exact hi.1
      obtain ⟨i, _, heq⟩ := Finset.mem_image.mp hxImage
      apply Finset.mem_image.mpr
      refine ⟨i, ?_, heq⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [heq]; exact hi.2⟩
    · intro hx
      obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hx
      have hxH : x ∈ support := by
        rw [hsel.2.2.1]
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, heq⟩
      exact Finset.mem_filter.mpr ⟨hxH, by rw [← heq]; exact (Finset.mem_filter.mp hi).2⟩
  rw [heq, Finset.card_image_of_injective _ hsel.1]
  have hd0 := damaged_disjoint_cells_card_le_loss (PathIndexedCell units)
    (pathSeedPacking_disjoint n blue units witness hpack) loss
  have hd : damaged.card ≤ loss.card := by
    convert hd0 using 1
    congr 1
    ext i
    simp only [damaged, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (Finset.card_le_card hchosen).trans hd

end FaultObservationResearch
