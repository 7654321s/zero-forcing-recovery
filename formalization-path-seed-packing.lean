module

/-
Ordered endpoint/pair forcing cells on an arbitrary path blue set.
These are static packing and minimum hitting-set facts, not time support
or an originality claim.
-/
public import «formalization-forcing-cells»
public import «formalization-path-pair-packing»
public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace FaultObservationResearch

def PathForcingUnit (n : ℕ) (cell : Finset (Fin (n + 1))) : Prop :=
  cell = {0} ∨ cell = {Fin.last n} ∨
    ∃ u v : Fin (n + 1), u.val + 1 = v.val ∧ cell = {u, v}

structure PathSeedPacking (n : ℕ) (blue : Finset (Fin (n + 1)))
    (units : List (Finset (Fin (n + 1)))) (witness : Finset (Fin (n + 1))) : Prop where
  unit_kind : ∀ cell ∈ units, PathForcingUnit n cell
  unit_subset : ∀ cell ∈ units, cell ⊆ blue
  ordered : units.Pairwise (PathCellBefore n)
  witness_subset : witness ⊆ blue
  witness_kills : ¬ IsForcing (SimpleGraph.pathGraph (n + 1)).Adj (blue \ witness)
  witness_card : witness.card = units.length

theorem pathForcingUnit_forcing (n : ℕ) (cell : Finset (Fin (n + 1)))
    (hunit : PathForcingUnit n cell) :
    IsForcing (SimpleGraph.pathGraph (n + 1)).Adj cell := by
  classical
  apply path_forcing_of_seed
  rcases hunit with hz | hl | ⟨u, v, huv, heq⟩
  · rw [hz]
    exact Or.inl (Finset.mem_singleton_self _)
  · rw [hl]
    exact Or.inr (Or.inl (Finset.mem_singleton_self _))
  · rw [heq]
    exact Or.inr (Or.inr ⟨u, v, by simp, by simp, huv⟩)

theorem exists_path_seed_packing (n : ℕ) (hn : 0 < n)
    (blue : Finset (Fin (n + 1))) :
    ∃ units : List (Finset (Fin (n + 1))), ∃ witness : Finset (Fin (n + 1)),
      PathSeedPacking n blue units witness := by
  classical
  let F := blue ∩ {0, Fin.last n}
  let S := blue \ F
  obtain ⟨pairs, cover, hp⟩ := exists_path_pair_cover_packing n S
  let starts : List (Finset (Fin (n + 1))) := if (0 : Fin (n + 1)) ∈ blue then [{0}] else []
  let ends : List (Finset (Fin (n + 1))) := if Fin.last n ∈ blue then [{Fin.last n}] else []
  have hEndsNe : (0 : Fin (n + 1)) ≠ Fin.last n := by
    intro heq
    have hv := congrArg Fin.val heq
    change 0 = n at hv
    omega
  have hFsub : F ⊆ blue := fun _ hx => (Finset.mem_inter.mp hx).1
  have hSsub : S ⊆ blue := fun _ hx => (Finset.mem_sdiff.mp hx).1
  have hSinterior : ∀ x ∈ S, 0 < x.val ∧ x.val < n := by
    intro x hx
    obtain ⟨hxB, hxF⟩ := Finset.mem_sdiff.mp hx
    have hz : x ≠ 0 := by
      intro heq
      apply hxF
      exact Finset.mem_inter.mpr ⟨hxB, by simp [heq]⟩
    have hl : x ≠ Fin.last n := by
      intro heq
      apply hxF
      exact Finset.mem_inter.mpr ⟨hxB, by simp [heq]⟩
    have hzVal : x.val ≠ 0 := fun heq => hz (Fin.ext heq)
    have hlVal : x.val ≠ n := fun heq => hl (Fin.ext heq)
    have hlt := x.isLt
    omega
  have hStartMem : ∀ cell ∈ starts, cell = {0} ∧ (0 : Fin (n + 1)) ∈ blue := by
    intro cell hc
    by_cases hz : (0 : Fin (n + 1)) ∈ blue
    · have heq : cell = {0} := by simpa [starts, hz] using hc
      exact ⟨heq, hz⟩
    · simp [starts, hz] at hc
  have hEndMem : ∀ cell ∈ ends, cell = {Fin.last n} ∧ Fin.last n ∈ blue := by
    intro cell hc
    by_cases hl : Fin.last n ∈ blue
    · have heq : cell = {Fin.last n} := by simpa [ends, hl] using hc
      exact ⟨heq, hl⟩
    · simp [ends, hl] at hc
  have hStartPair : ∀ a ∈ starts, ∀ b ∈ pairs, PathCellBefore n a b := by
    intro a ha b hb x hx y hy
    have ha0 := (hStartMem a ha).1
    have hx0 : x = 0 := by simpa [ha0] using hx
    have hyS := pathPairCoverPacking_cell_subset n S pairs cover hp b hb hy
    rw [hx0]
    exact (hSinterior y hyS).1
  have hPairEnd : ∀ a ∈ pairs, ∀ b ∈ ends, PathCellBefore n a b := by
    intro a ha b hb x hx y hy
    have hbn := (hEndMem b hb).1
    have hyn : y = Fin.last n := by simpa [hbn] using hy
    have hxS := pathPairCoverPacking_cell_subset n S pairs cover hp a ha hx
    rw [hyn]
    exact (hSinterior x hxS).2
  have hStartEnd : ∀ a ∈ starts, ∀ b ∈ ends, PathCellBefore n a b := by
    intro a ha b hb x hx y hy
    have hx0 : x = 0 := by simpa [(hStartMem a ha).1] using hx
    have hyn : y = Fin.last n := by simpa [(hEndMem b hb).1] using hy
    rw [hx0, hyn]
    exact hn
  have hStartOrdered : starts.Pairwise (PathCellBefore n) := by
    dsimp [starts]
    split <;> simp
  have hEndOrdered : ends.Pairwise (PathCellBefore n) := by
    dsimp [ends]
    split <;> simp
  have hOrdered : ((starts ++ pairs) ++ ends).Pairwise (PathCellBefore n) := by
    apply List.pairwise_append.mpr
    refine ⟨List.pairwise_append.mpr ⟨hStartOrdered, hp.ordered, hStartPair⟩, hEndOrdered, ?_⟩
    intro a ha b hb
    rcases List.mem_append.mp ha with hs | hp'
    · exact hStartEnd a hs b hb
    · exact hPairEnd a hp' b hb
  have hFcard : F.card = starts.length + ends.length := by
    have hFeq : F = (if (0 : Fin (n + 1)) ∈ blue then {0} else ∅) ∪
        (if Fin.last n ∈ blue then {Fin.last n} else ∅) := by
      ext x
      by_cases hz : (0 : Fin (n + 1)) ∈ blue <;>
        by_cases hl : Fin.last n ∈ blue <;>
        simp only [F, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
          hz, hl, ite_true, ite_false, Finset.mem_union, Finset.notMem_empty, or_false, false_or]
      all_goals aesop
    rw [hFeq]
    by_cases hz : (0 : Fin (n + 1)) ∈ blue <;>
      by_cases hl : Fin.last n ∈ blue <;>
      simp [starts, ends, hz, hl, hEndsNe]
  have hDisjoint : Disjoint F cover := by
    apply Finset.disjoint_left.mpr
    intro x hxF hxC
    exact (Finset.mem_sdiff.mp (hp.cover_subset hxC)).2 hxF
  have hWitnessSub : F ∪ cover ⊆ blue := by
    intro x hx
    exact (Finset.mem_union.mp hx).elim (fun h => hFsub h) (fun h => hSsub (hp.cover_subset h))
  have hWitnessKill : ¬ IsForcing (SimpleGraph.pathGraph (n + 1)).Adj (blue \ (F ∪ cover)) := by
    apply (path_nonforcing_sdiff_iff_hits_seeds n blue (F ∪ cover)).mpr
    refine ⟨?_, ?_, ?_⟩
    · intro hz
      exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hz, by simp⟩)
    · intro hl
      exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hl, by simp⟩)
    · intro u v hu hv huv
      by_cases huF : u ∈ F
      · exact Or.inl (Finset.mem_union_left _ huF)
      by_cases hvF : v ∈ F
      · exact Or.inr (Finset.mem_union_left _ hvF)
      have hit := hp.covers u (Finset.mem_sdiff.mpr ⟨hu, huF⟩)
        v (Finset.mem_sdiff.mpr ⟨hv, hvF⟩) huv
      exact hit.elim (fun h => Or.inl (Finset.mem_union_right _ h))
        (fun h => Or.inr (Finset.mem_union_right _ h))
  refine ⟨(starts ++ pairs) ++ ends, F ∪ cover, ?_⟩
  constructor
  · intro cell hc
    rcases List.mem_append.mp hc with hc | hc
    · rcases List.mem_append.mp hc with hs | hp'
      · exact Or.inl (hStartMem cell hs).1
      · obtain ⟨u, _, v, _, huv, heq⟩ := hp.pairs cell hp'
        exact Or.inr (Or.inr ⟨u, v, huv, heq⟩)
    · exact Or.inr (Or.inl (hEndMem cell hc).1)
  · intro cell hc x hx
    rcases List.mem_append.mp hc with hc | hc
    · rcases List.mem_append.mp hc with hs | hp'
      · have hx0 : x = 0 := by simpa [(hStartMem cell hs).1] using hx
        rw [hx0]
        exact (hStartMem cell hs).2
      · exact hSsub (pathPairCoverPacking_cell_subset n S pairs cover hp cell hp' hx)
    · have hxn : x = Fin.last n := by simpa [(hEndMem cell hc).1] using hx
      rw [hxn]
      exact (hEndMem cell hc).2
  · exact hOrdered
  · exact hWitnessSub
  · exact hWitnessKill
  · rw [Finset.card_union_of_disjoint hDisjoint, hFcard, hp.card_eq]
    simp only [List.length_append]
    omega

def PathIndexedCell {n : ℕ} (units : List (Finset (Fin (n + 1))))
    (i : Fin units.length) : Finset (Fin (n + 1)) := units[i.val]

theorem pathSeedPacking_disjoint (n : ℕ) (blue : Finset (Fin (n + 1)))
    (units : List (Finset (Fin (n + 1)))) (witness : Finset (Fin (n + 1)))
    (hpack : PathSeedPacking n blue units witness) :
    DisjointForcingCells (PathIndexedCell units) := by
  intro i j hne
  have hvalNe : i.val ≠ j.val := fun h => hne (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hvalNe with hij | hji
  · exact pathCellBefore_disjoint n _ _
      (List.Pairwise.rel_getElem_of_lt i.isLt j.isLt hpack.ordered hij)
  · exact (pathCellBefore_disjoint n _ _
      (List.Pairwise.rel_getElem_of_lt j.isLt i.isLt hpack.ordered hji)).symm

theorem pathSeedPacking_every_minimum_selector (n : ℕ) (blue support : Finset (Fin (n + 1)))
    (units : List (Finset (Fin (n + 1)))) (witness : Finset (Fin (n + 1)))
    (hpack : PathSeedPacking n blue units witness)
    (hminimum : IsMinimumKilling (SimpleGraph.pathGraph (n + 1)).Adj blue support) :
    ∃ pick : Fin units.length → Fin (n + 1),
      ExactCellSelection (PathIndexedCell units) support pick := by
  classical
  apply minimumKilling_exact_cell_selector _ blue support witness (PathIndexedCell units)
    (pathSeedPacking_disjoint n blue units witness hpack)
  · intro i
    exact hpack.unit_subset _ (List.getElem_mem i.isLt)
  · intro i
    exact pathForcingUnit_forcing n _ (hpack.unit_kind _ (List.getElem_mem i.isLt))
  · exact hminimum
  · exact hpack.witness_subset
  · exact hpack.witness_kills
  · simpa only [Fintype.card_fin] using hpack.witness_card

end FaultObservationResearch
