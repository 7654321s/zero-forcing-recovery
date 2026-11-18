module

public import AttachmentProjection
public import «formalization-path-forcing»

@[expose] public section

set_option autoImplicit false

namespace FaultObservationResearch

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A path seeded only at its first vertex colors one new vertex per round. -/
theorem path_colorAfter_single_first (n t : ℕ) (i : Fin (n + 1)) :
    i ∈ colorAfter (SimpleGraph.pathGraph (n + 1)).Adj {0} t ↔ i.val ≤ t := by
  induction t generalizing i with
  | zero =>
    change i ∈ ({0} : Finset (Fin (n + 1))) ↔ i.val ≤ 0
    simp only [Finset.mem_singleton]
    constructor
    · intro h
      rw [h]
      simp
    · intro h
      exact Fin.ext (by simpa using h)
  | succ t ih =>
    rw [colorAfter, mem_synchronousStep]
    constructor
    · rintro (h | ⟨source, hs, ha, _⟩)
      · have := (ih i).mp h
        omega
      · have := (ih source).mp hs
        rcases SimpleGraph.pathGraph_adj.mp ha with h | h <;> omega
    · intro h
      by_cases hOld : i.val ≤ t
      · exact Or.inl ((ih i).mpr hOld)
      let source : Fin (n + 1) := ⟨t, by have := i.isLt; omega⟩
      have hSource : source.val = t := rfl
      refine Or.inr ⟨source, (ih source).mpr (by omega),
        SimpleGraph.pathGraph_adj.mpr (Or.inl (by omega)), ?_⟩
      intro other ha hWhite
      have hOther : ¬ other.val ≤ t := fun h => hWhite ((ih other).mpr h)
      apply Fin.ext
      rcases SimpleGraph.pathGraph_adj.mp ha with h | h <;> omega

/-- Even zero-based positions, excluding the last vertex. The head is blue
if the path has at least two vertices. -/
def alternatingTail (n : ℕ) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun i => i.val % 2 = 0 ∧ i.val < n)

@[simp] theorem mem_alternatingTail (n : ℕ) (i : Fin (n + 1)) :
    i ∈ alternatingTail n ↔ i.val % 2 = 0 ∧ i.val < n := by
  simp [alternatingTail]

theorem alternatingTail_fixed_when_head_inactive (n : ℕ) :
    synchronousStep (fun x y : Fin (n + 1) =>
      x ≠ 0 ∧ (SimpleGraph.pathGraph (n + 1)).Adj x y) (alternatingTail n) =
      alternatingTail n := by
  apply le_antisymm _ (subset_synchronousStep _ _)
  intro i hi
  rcases (mem_synchronousStep _ _ i).mp hi with hi | ⟨source, hs, ha, hu⟩
  · exact hi
  rcases ha with ⟨hNonzero, ha⟩
  have hPos : 0 < source.val := by
    by_contra h
    exact hNonzero (Fin.ext (show source.val = 0 by omega))
  obtain ⟨hEven, hInner⟩ := (mem_alternatingTail n source).mp hs
  let left : Fin (n + 1) := ⟨source.val - 1, by omega⟩
  let right : Fin (n + 1) := ⟨source.val + 1, by omega⟩
  have hLeft : left.val = source.val - 1 := rfl
  have hRight : right.val = source.val + 1 := rfl
  have h1 := hu left ⟨hNonzero, SimpleGraph.pathGraph_adj.mpr (Or.inr (by omega))⟩
    (fun h => by have := (mem_alternatingTail n left).mp h; omega)
  have h2 := hu right ⟨hNonzero, SimpleGraph.pathGraph_adj.mpr (Or.inl (by omega))⟩
    (fun h => by have := (mem_alternatingTail n right).mp h; omega)
  exfalso
  have he := congrArg Fin.val (h1.trans h2.symm)
  omega

/-- Once the head has a blue predecessor, exactly the initial seeds and
the first two positions per elapsed round are blue in an alternating tail. -/
theorem path_colorAfter_alternating (n : ℕ) (hLength : 0 < n) (t : ℕ)
    (i : Fin (n + 1)) :
    i ∈ colorAfter (SimpleGraph.pathGraph (n + 1)).Adj (alternatingTail n) t ↔
      i ∈ alternatingTail n ∨ i.val < 2 * t := by
  induction t generalizing i with
  | zero => simp
  | succ t ih =>
    rw [colorAfter, mem_synchronousStep]
    constructor
    · rintro (h | ⟨source, hs, ha, hu⟩)
      · exact (ih i).mp h |>.imp id (fun h => by omega)
      · rcases (ih source).mp hs with hSeed | hPrefix
        · by_cases hTarget : i.val < 2 * (t + 1)
          · exact Or.inr hTarget
          obtain ⟨hEven, hInner⟩ := (mem_alternatingTail n source).mp hSeed
          have hPositive : 0 < source.val := by
            rcases SimpleGraph.pathGraph_adj.mp ha with h | h <;> omega
          let left : Fin (n + 1) := ⟨source.val - 1, by omega⟩
          let right : Fin (n + 1) := ⟨source.val + 1, by omega⟩
          have hLeft : left.val = source.val - 1 := rfl
          have hRight : right.val = source.val + 1 := rfl
          have hLeftWhite : left ∉ colorAfter (SimpleGraph.pathGraph (n + 1)).Adj
              (alternatingTail n) t := by
            intro h
            rcases (ih left).mp h with h | h
            · have := (mem_alternatingTail n left).mp h
              omega
            · rcases SimpleGraph.pathGraph_adj.mp ha with hA | hA <;> omega
          have hRightWhite : right ∉ colorAfter (SimpleGraph.pathGraph (n + 1)).Adj
              (alternatingTail n) t := by
            intro h
            rcases (ih right).mp h with h | h
            · have := (mem_alternatingTail n right).mp h
              omega
            · rcases SimpleGraph.pathGraph_adj.mp ha with hA | hA <;> omega
          have hl := hu left (SimpleGraph.pathGraph_adj.mpr (Or.inr (by omega))) hLeftWhite
          have hr := hu right (SimpleGraph.pathGraph_adj.mpr (Or.inl (by omega))) hRightWhite
          have he := congrArg Fin.val (hl.trans hr.symm)
          omega
        · right
          rcases SimpleGraph.pathGraph_adj.mp ha with h | h <;> omega
    · rintro (hSeed | hTarget)
      · exact Or.inl ((ih i).mpr (Or.inl hSeed))
      · by_cases hOld : i ∈ alternatingTail n ∨ i.val < 2 * t
        · exact Or.inl ((ih i).mpr hOld)
        have hNotPrefix : ¬ i.val < 2 * t := fun h => hOld (Or.inr h)
        have hNotSeed : ¬ (i.val % 2 = 0 ∧ i.val < n) :=
          fun h => hOld (Or.inl ((mem_alternatingTail n i).mpr h))
        have hPos : 0 < i.val := by
          by_contra h
          exact hNotSeed (by omega)
        let source : Fin (n + 1) := ⟨i.val - 1, by have := i.isLt; omega⟩
        have hSource : source.val = i.val - 1 := rfl
        have hs : source ∈ alternatingTail n ∨ source.val < 2 * t := by
          by_cases hEven : i.val % 2 = 0
          · exact Or.inr (by omega)
          · exact Or.inl ((mem_alternatingTail n source).mpr
              (by have := i.isLt; omega))
        refine Or.inr ⟨source, (ih source).mpr hs,
          SimpleGraph.pathGraph_adj.mpr (Or.inl (by omega)), ?_⟩
        intro other ha hw
        apply Fin.ext
        by_contra hNe
        have hOther : ¬ other.val < 2 * t := fun h => hw ((ih other).mpr (Or.inr h))
        rcases SimpleGraph.pathGraph_adj.mp ha with h | h <;> omega

theorem path_alternating_finishes_iff (n : ℕ) (hLength : 0 < n) (t : ℕ) :
    FinishesBy (SimpleGraph.pathGraph (n + 1)).Adj (alternatingTail n) t ↔
      (n + 2) / 2 ≤ t := by
  constructor
  · intro h
    have hLast : Fin.last n ∈
        colorAfter (SimpleGraph.pathGraph (n + 1)).Adj (alternatingTail n) t := by
      rw [show colorAfter _ _ _ = Finset.univ from h]
      exact Finset.mem_univ _
    rcases (path_colorAfter_alternating n hLength t (Fin.last n)).mp hLast with h | h
    · have := (mem_alternatingTail n (Fin.last n)).mp h
      simp at this
    · change n < 2 * t at h
      omega
  · intro h
    apply Finset.eq_univ_of_forall
    intro i
    exact (path_colorAfter_alternating n hLength t i).mpr (Or.inr (by
      have := i.isLt
      omega))

/-- Adding a wholly white path at an initially white leaf preserves the core
colors. The suffix also stays white through the leaf's restoration round. -/
theorem white_path_at_leaf_projection (core : V → V → Prop)
    (symmetric : ∀ ⦃x y⦄, core x y → core y x)
    (blue : Finset V) (root neighbor : V) (n : ℕ)
    (unique : ∀ x, core root x → x = neighbor) (white : root ∉ blue) (t : ℕ) :
    let tail := (SimpleGraph.pathGraph (n + 1)).Adj
    let large := blue.disjSum (∅ : Finset (Fin (n + 1)))
    (∀ x, Sum.inl x ∈ colorAfter (attachAtAdj core tail root 0) large t ↔
      x ∈ colorAfter core blue t) ∧
    ((∀ s < t, root ∉ colorAfter core blue s) → ∀ i,
      Sum.inr i ∉ colorAfter (attachAtAdj core tail root 0) large t) := by
  dsimp only
  let tail := (SimpleGraph.pathGraph (n + 1)).Adj
  have hProj := attachAt_core_and_stalled_tail core tail root 0 blue ∅
    (blue.disjSum ∅)
    (fun _ => Finset.inl_mem_disjSum)
    (fun _ => Finset.inr_mem_disjSum)
    (by ext x; simp [mem_synchronousStep]) (by simp)
    (by
      intro s hs
      right
      intro x hx
      rw [unique x hx]
      exact leaf_neighbor_blue_after_restoration core symmetric blue root neighbor unique white s hs)
    t
  exact ⟨hProj.1, fun h i hi => Finset.notMem_empty i ((hProj.2 h i).mp hi)⟩

/-- If the old leaf first turns blue at round r, the vertex at position i in
its white extension first turns blue at round r + 1 + i. -/
theorem white_path_at_leaf_clock (core : V → V → Prop)
    (symmetric : ∀ ⦃x y⦄, core x y → core y x)
    (blue : Finset V) (root neighbor : V) (n r : ℕ)
    (unique : ∀ x, core root x → x = neighbor) (white : root ∉ blue)
    (restore : root ∈ colorAfter core blue r)
    (first : ∀ s < r, root ∉ colorAfter core blue s) (s : ℕ) (i : Fin (n + 1)) :
    let tail := (SimpleGraph.pathGraph (n + 1)).Adj
    let large := blue.disjSum (∅ : Finset (Fin (n + 1)))
    Sum.inr i ∈ colorAfter (attachAtAdj core tail root 0) large (r + 1 + s) ↔
      i.val ≤ s := by
  let tail := (SimpleGraph.pathGraph (n + 1)).Adj
  let joined := attachAtAdj core tail root 0
  let large := blue.disjSum (∅ : Finset (Fin (n + 1)))
  change Sum.inr i ∈ colorAfter joined large (r + 1 + s) ↔ i.val ≤ s
  have hProj := white_path_at_leaf_projection core symmetric blue root neighbor n unique white r
  have hBlue : Sum.inl root ∈ colorAfter joined large r := (hProj.1 root).mpr restore
  have hNeighbors : ∀ x, core root x → Sum.inl x ∈ colorAfter joined large r := by
    intro x hx
    rw [unique x hx]
    exact (hProj.1 neighbor).mpr
      (leaf_neighbor_blue_after_restoration core symmetric blue root neighbor unique white r restore)
  have hTail : ∀ w : Fin (n + 1), Sum.inr w ∈ colorAfter joined large (r + 1) ↔
      w ∈ ({0} : Finset (Fin (n + 1))) := by
    intro w
    change Sum.inr w ∈ synchronousStep joined (colorAfter joined large r) ↔ _
    rw [Finset.mem_singleton]
    exact attachAt_step_starts_white_tail core tail root 0 _ hBlue hNeighbors (hProj.2 first) w
  rw [colorAfter_add]
  exact (attachAt_tail_colorAfter_of_blue_bridge core tail root 0 _ {0} hTail
    (colorAfter_subset_succ joined large r hBlue) (by simp) s i).trans
    (path_colorAfter_single_first n s i)

/-- A side path retains its alternating seeds through the anchor's
restoration round, while projecting exactly onto the core. -/
theorem alternating_side_path_projection (core : V → V → Prop) (blue : Finset V)
    (root : V) (n : ℕ) (hLength : 0 < n) (t : ℕ) :
    let tail := (SimpleGraph.pathGraph (n + 1)).Adj
    let large := blue.disjSum (alternatingTail n)
    (∀ x, Sum.inl x ∈ colorAfter (attachAtAdj core tail root 0) large t ↔
      x ∈ colorAfter core blue t) ∧
    ((∀ s < t, root ∉ colorAfter core blue s) → ∀ i,
      Sum.inr i ∈ colorAfter (attachAtAdj core tail root 0) large t ↔ i ∈ alternatingTail n) := by
  dsimp only
  let tail := (SimpleGraph.pathGraph (n + 1)).Adj
  have hBlue : (0 : Fin (n + 1)) ∈ alternatingTail n := by
    apply (mem_alternatingTail n 0).mpr
    exact ⟨rfl, hLength⟩
  refine attachAt_core_and_stalled_tail core tail root 0 blue (alternatingTail n) _
    (fun _ => Finset.inl_mem_disjSum) (fun _ => Finset.inr_mem_disjSum)
    (alternatingTail_fixed_when_head_inactive n) ?_ (fun _ _ => Or.inl hBlue) t
  intro _
  let next : Fin (n + 1) := ⟨1, by omega⟩
  refine ⟨next, SimpleGraph.pathGraph_adj.mpr (Or.inl rfl), ?_⟩
  intro hNext
  have hEven := ((mem_alternatingTail n next).mp hNext).1
  change 1 % 2 = 0 at hEven
  omega

/-- After the first blue round at the anchor, the alternating side path
completes in exactly ceil(length / 2) additional rounds. -/
theorem alternating_side_path_clock (core : V → V → Prop) (blue : Finset V)
    (root : V) (n : ℕ) (hLength : 0 < n) (r : ℕ)
    (restore : root ∈ colorAfter core blue r)
    (first : ∀ s < r, root ∉ colorAfter core blue s) (s : ℕ) :
    let tail := (SimpleGraph.pathGraph (n + 1)).Adj
    let large := blue.disjSum (alternatingTail n)
    (∀ i, Sum.inr i ∈ colorAfter (attachAtAdj core tail root 0) large (r + s)) ↔
      (n + 2) / 2 ≤ s := by
  let tail := (SimpleGraph.pathGraph (n + 1)).Adj
  let joined := attachAtAdj core tail root 0
  let large := blue.disjSum (alternatingTail n)
  change (∀ i, Sum.inr i ∈ colorAfter joined large (r + s)) ↔ _
  have hProj := alternating_side_path_projection core blue root n hLength r
  have hBlue : Sum.inl root ∈ colorAfter joined large r := (hProj.1 root).mpr restore
  have hHead : (0 : Fin (n + 1)) ∈ alternatingTail n :=
    (mem_alternatingTail n 0).mpr ⟨rfl, hLength⟩
  have hShift := attachAt_tail_colorAfter_of_blue_bridge core tail root 0
    (colorAfter joined large r) (alternatingTail n) (hProj.2 first) hBlue hHead s
  have hTailFull : (∀ i, Sum.inr i ∈ colorAfter joined large (r + s)) ↔
      FinishesBy tail (alternatingTail n) s := by
    simp only [colorAfter_add]
    constructor
    · intro h
      exact Finset.eq_univ_of_forall (fun i => (hShift i).mp (h i))
    · intro h i
      apply (hShift i).mpr
      rw [show colorAfter tail (alternatingTail n) s = Finset.univ from h]
      exact Finset.mem_univ _
  exact hTailFull.trans (path_alternating_finishes_iff n hLength s)

/-- The extended graph is complete exactly when the old graph is complete
and the first restoration of the leaf is at least the tail length ago. -/
theorem white_path_at_leaf_finishesBy_iff (core : V → V → Prop)
    (symmetric : ∀ ⦃x y⦄, core x y → core y x)
    (blue : Finset V) (root neighbor : V) (n r : ℕ)
    (unique : ∀ x, core root x → x = neighbor) (white : root ∉ blue)
    (restore : root ∈ colorAfter core blue r)
    (first : ∀ s < r, root ∉ colorAfter core blue s) (t : ℕ) :
    let tail := (SimpleGraph.pathGraph (n + 1)).Adj
    let large := blue.disjSum (∅ : Finset (Fin (n + 1)))
    FinishesBy (attachAtAdj core tail root 0) large t ↔
      FinishesBy core blue t ∧ r + (n + 1) ≤ t := by
  let tail := (SimpleGraph.pathGraph (n + 1)).Adj
  let large := blue.disjSum (∅ : Finset (Fin (n + 1)))
  dsimp only
  have hProj := white_path_at_leaf_projection core symmetric blue root neighbor n unique white t
  rw [attachAt_finishesBy_iff core tail root 0 blue large t hProj.1]
  apply and_congr_right
  intro _
  by_cases hEarly : t ≤ r
  · have hHeadWhite := hProj.2 (fun s hs => first s (lt_of_lt_of_le hs hEarly)) 0
    exact iff_of_false (fun h => hHeadWhite (h 0)) (by omega)
  · let s := t - (r + 1)
    have hTime : t = r + 1 + s := by dsimp [s]; omega
    rw [hTime]
    constructor
    · intro h
      have hLast := (white_path_at_leaf_clock core symmetric blue root neighbor n r unique
        white restore first s (Fin.last n)).mp (h (Fin.last n))
      change n ≤ s at hLast
      omega
    · intro h i
      exact (white_path_at_leaf_clock core symmetric blue root neighbor n r unique
        white restore first s i).mpr (by have := i.isLt; omega)

theorem alternating_side_path_finishesBy_iff (core : V → V → Prop) (blue : Finset V)
    (root : V) (n : ℕ) (hLength : 0 < n) (r : ℕ)
    (restore : root ∈ colorAfter core blue r)
    (first : ∀ s < r, root ∉ colorAfter core blue s) (t : ℕ) :
    let tail := (SimpleGraph.pathGraph (n + 1)).Adj
    let large := blue.disjSum (alternatingTail n)
    FinishesBy (attachAtAdj core tail root 0) large t ↔
      FinishesBy core blue t ∧ r + (n + 2) / 2 ≤ t := by
  let tail := (SimpleGraph.pathGraph (n + 1)).Adj
  let large := blue.disjSum (alternatingTail n)
  dsimp only
  have hProj := alternating_side_path_projection core blue root n hLength t
  rw [attachAt_finishesBy_iff core tail root 0 blue large t hProj.1]
  apply and_congr_right
  intro _
  by_cases hEarly : t < r
  · have hLast := hProj.2 (fun s hs => first s (lt_trans hs hEarly)) (Fin.last n)
    have hWhite : Fin.last n ∉ alternatingTail n := by
      intro h
      have := (mem_alternatingTail n (Fin.last n)).mp h
      simp at this
    exact iff_of_false (fun h => hWhite (hLast.mp (h (Fin.last n)))) (by omega)
  · let s := t - r
    have hTime : t = r + s := by dsimp [s]; omega
    have hClock := alternating_side_path_clock core blue root n hLength r restore first s
    dsimp only at hClock
    rw [hTime, hClock]
    omega

end FaultObservationResearch

#print axioms FaultObservationResearch.path_colorAfter_single_first
#print axioms FaultObservationResearch.alternatingTail_fixed_when_head_inactive
#print axioms FaultObservationResearch.path_alternating_finishes_iff
#print axioms FaultObservationResearch.white_path_at_leaf_projection
#print axioms FaultObservationResearch.white_path_at_leaf_clock
#print axioms FaultObservationResearch.alternating_side_path_clock
#print axioms FaultObservationResearch.white_path_at_leaf_finishesBy_iff
#print axioms FaultObservationResearch.alternating_side_path_finishesBy_iff
