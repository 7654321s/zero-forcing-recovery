module

/-
Adjacent equal-arm tree family. The target is a minimum three-point killing
support with a strict budget-two time separation. Helper checks alone do not
prove that target, whole-tree exhaustion, or research priority.
-/
public import «formalization-two-center-equal-nonadjacent»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch

abbrev AdjacentEqualVertex (k : ℕ) := EqualCenterVertex (Fin 2) (k + 1)
def adjacentEqualGraph (k : ℕ) :=
  twoCenterGraph (SimpleGraph.pathGraph 2) (0 : Fin 2) 1 (k + 1) 0 (k + 1) 0
abbrev adjacentEqualU (k : ℕ) : AdjacentEqualVertex k := equalCore (Fin 2) (k + 1) 0
abbrev adjacentEqualV (k : ℕ) : AdjacentEqualVertex k := equalCore (Fin 2) (k + 1) 1
abbrev adjacentEqualUL (k : ℕ) := equalULong (Fin 2) (k + 1)
abbrev adjacentEqualUS (k : ℕ) := equalUShort (Fin 2) (k + 1)
abbrev adjacentEqualVL (k : ℕ) := equalVLong (Fin 2) (k + 1)
abbrev adjacentEqualVS (k : ℕ) := equalVShort (Fin 2) (k + 1)

def adjacentEqualInitial (k : ℕ) : Finset (AdjacentEqualVertex k) := by
  classical
  exact Finset.univ.filter (fun z => match z with
    | Sum.inl (Sum.inl x) => x = 1
    | Sum.inl (Sum.inr (Sum.inl i)) => i = 0 ∨ i = Fin.last (k + 1)
    | Sum.inl (Sum.inr (Sum.inr _)) => True
    | Sum.inr (Sum.inl i) => i = 0 ∨ i = Fin.last (k + 1)
    | Sum.inr (Sum.inr _) => True)

def adjacentEqualLeaves (k : ℕ) : Finset (AdjacentEqualVertex k) := by
  classical
  exact {adjacentEqualUL k (Fin.last (k + 1)), adjacentEqualUS k,
    adjacentEqualVL k (Fin.last (k + 1)), adjacentEqualVS k}

def adjacentEqualSupport (k : ℕ) : Finset (AdjacentEqualVertex k) := by
  classical
  exact {adjacentEqualUS k, adjacentEqualUL k (Fin.last (k + 1)), adjacentEqualVS k}

theorem adjacentEqual_core_split (x : Fin 2) : x = 0 ∨ x = 1 := by
  by_cases hx : x.val = 0
  · exact Or.inl (Fin.ext hx)
  · apply Or.inr
    apply Fin.ext
    have := x.isLt
    change x.val = 1
    omega

theorem adjacentEqual_graph_isTree (k : ℕ) : (adjacentEqualGraph k).IsTree :=
  twoCenterGraph_isTree (SimpleGraph.pathGraph 2)
    (SimpleGraph.isTree_pathGraph_add_one 1) 0 1 (k + 1) 0 (k + 1) 0

theorem adjacentEqual_v_to_u_step (k : ℕ) (C : Finset (AdjacentEqualVertex k))
    (hv : adjacentEqualV k ∈ C) (hL : adjacentEqualVL k 0 ∈ C)
    (hS : adjacentEqualVS k ∈ C) :
    adjacentEqualU k ∈ synchronousStep (adjacentEqualGraph k).Adj C := by
  apply (mem_synchronousStep _ _ _).mpr
  refine Or.inr ⟨adjacentEqualV k, hv, ?_, ?_⟩
  · change (SimpleGraph.pathGraph 2).Adj (1 : Fin 2) 0
    exact SimpleGraph.pathGraph_adj.mpr (Or.inr rfl)
  · rintro ((x | (i | j)) | (p | q)) ha hw
    · rcases adjacentEqual_core_split x with rfl | rfl
      · rfl
      · exact False.elim ((SimpleGraph.pathGraph 2).loopless.irrefl 1 ha)
    · have heq := congrArg Fin.val ha.1
      change 1 = 0 at heq
      omega
    · have heq := congrArg Fin.val ha.1
      change 1 = 0 at heq
      omega
    · exact False.elim (hw (ha.2 ▸ hL))
    · have hq : q = 0 := Fin.eq_zero _
      subst q
      exact False.elim (hw hS)

def adjacentEqualUTail (k : ℕ) : Fin (k + 1) ↪ AdjacentEqualVertex k where
  toFun := fun i => adjacentEqualUL k i.succ
  inj' := by
    intro i j h
    have hv := congrArg Fin.val ((adjacentEqualUL k).injective h)
    apply Fin.ext
    change i.val + 1 = j.val + 1 at hv
    omega

theorem adjacentEqual_u_tail_from_last (k : ℕ) (C : Finset (AdjacentEqualVertex k))
    (hh : adjacentEqualUL k 0 ∈ C)
    (he : adjacentEqualUL k (Fin.last (k + 1)) ∈ C) :
    ∀ i : Fin (k + 1), adjacentEqualUL k i.succ ∈ colorAfter (adjacentEqualGraph k).Adj C k := by
  classical
  intro i
  refine colorAfter_embeds_with_blue_exterior (SimpleGraph.pathGraph (k + 1))
    (adjacentEqualGraph k) (adjacentEqualUTail k) ?_ {Fin.last k} C ?_ ?_ k i ?_
  · intro j l h
    change (SimpleGraph.pathGraph (k + 2)).Adj j.succ l.succ
    apply SimpleGraph.pathGraph_adj.mpr
    rcases SimpleGraph.pathGraph_adj.mp h with h | h
    · left
      change (j.val + 1) + 1 = l.val + 1
      omega
    · right
      change (l.val + 1) + 1 = j.val + 1
      omega
  · rintro j ((x | (l | p)) | (q | s)) hz
    · have hzero := congrArg Fin.val hz.2
      change j.val + 1 = 0 at hzero
      omega
    · rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨l, rfl⟩
      · exact Or.inr hh
      · apply Or.inl
        refine ⟨l, rfl, ?_⟩
        apply SimpleGraph.pathGraph_adj.mpr
        rcases SimpleGraph.pathGraph_adj.mp hz with h | h
        · left
          change (j.val + 1) + 1 = l.val + 1 at h
          omega
        · right
          change (l.val + 1) + 1 = j.val + 1 at h
          omega
    · exact hz.elim
    · cases hz.1
    · cases hz.1
  · intro j hj
    have hjLast := Finset.mem_singleton.mp hj
    subst j
    change adjacentEqualUL k (Fin.last k).succ ∈ C
    have heq : (Fin.last k).succ = Fin.last (k + 1) := by apply Fin.ext; rfl
    rw [heq]
    exact he
  · rw [path_last_finishes_n k]
    exact Finset.mem_univ _

theorem adjacentEqual_u_head_to_root_step (k : ℕ) (C : Finset (AdjacentEqualVertex k))
    (hh : adjacentEqualUL k 0 ∈ C)
    (ht : adjacentEqualUL k (0 : Fin (k + 1)).succ ∈ C) :
    adjacentEqualU k ∈ synchronousStep (adjacentEqualGraph k).Adj C := by
  apply (mem_synchronousStep _ _ _).mpr
  refine Or.inr ⟨adjacentEqualUL k 0, hh, ⟨rfl, rfl⟩, ?_⟩
  rintro ((x | (i | j)) | (p | q)) ha hw
  · exact congrArg (equalCore (Fin 2) (k + 1)) ha.1
  · have hi : i = (0 : Fin (k + 1)).succ := by
      apply Fin.ext
      rcases SimpleGraph.pathGraph_adj.mp ha with h | h
      · change 0 + 1 = i.val at h
        change i.val = 0 + 1
        omega
      · change i.val + 1 = 0 at h
        omega
    exact False.elim (hw (hi ▸ ht))
  · exact ha.elim
  · cases ha.1
  · cases ha.1

theorem adjacentEqual_leaves_subset (k : ℕ) :
    adjacentEqualLeaves k ⊆ adjacentEqualInitial k := by
  classical
  intro z hz
  simp only [adjacentEqualLeaves, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · change (Sum.inl (Sum.inr (Sum.inl (Fin.last (k + 1))))) ∈ adjacentEqualInitial k
    simp [adjacentEqualInitial]
  · change (Sum.inl (Sum.inr (Sum.inr (0 : Fin 1)))) ∈ adjacentEqualInitial k
    simp [adjacentEqualInitial]
  · change (Sum.inr (Sum.inl (Fin.last (k + 1)))) ∈ adjacentEqualInitial k
    simp [adjacentEqualInitial]
  · change (Sum.inr (Sum.inr (0 : Fin 1))) ∈ adjacentEqualInitial k
    simp [adjacentEqualInitial]

theorem adjacentEqual_leaves_mem (k : ℕ) (z : AdjacentEqualVertex k)
    (hleaf : TreeLeaf (adjacentEqualGraph k) z) : z ∈ adjacentEqualLeaves k := by
  classical
  rcases z with (x | (i | j)) | (p | q)
  · obtain ⟨neighbor, _, hu⟩ := hleaf
    rcases adjacentEqual_core_split x with rfl | rfl
    · have heq := (hu (adjacentEqualUL k 0) ⟨rfl, rfl⟩).trans
        (hu (adjacentEqualUS k) ⟨rfl, rfl⟩).symm
      cases heq
    · have heq := (hu (adjacentEqualVL k 0) ⟨rfl, rfl⟩).trans
        (hu (adjacentEqualVS k) ⟨rfl, rfl⟩).symm
      cases heq
  · let H := twoPendantGraph (SimpleGraph.pathGraph 2) (0 : Fin 2) (k + 1) 0
    have hH : H.IsTree := twoPendantGraph_isTree (SimpleGraph.pathGraph 2)
      (SimpleGraph.isTree_pathGraph_add_one 1) 0 (k + 1) 0
    obtain ⟨y, hy⟩ := hH.connected.preconnected.exists_adj_of_nontrivial
      (twoPendantA (Fin 2) (k + 1) 0 i)
    have hsmall : TreeLeaf H (twoPendantA (Fin 2) (k + 1) 0 i) := by
      obtain ⟨w, _, hu⟩ := hleaf
      refine ⟨y, hy, ?_⟩
      intro other ho
      apply Sum.inl_injective
      exact (hu (Sum.inl other) ho).trans (hu (Sum.inl y) hy).symm
    have hi := twoPendant_leaf_A_is_last (SimpleGraph.pathGraph 2) 0 (k + 1) 0 i hsmall
    subst i
    change adjacentEqualUL k (Fin.last (k + 1)) ∈ adjacentEqualLeaves k
    exact Finset.mem_insert_self _ _
  · have hj : j = 0 := Fin.eq_zero _
    subst j
    change adjacentEqualUS k ∈ adjacentEqualLeaves k
    simp [adjacentEqualLeaves]
  · have hp := twoPendant_leaf_A_is_last
      (twoPendantGraph (SimpleGraph.pathGraph 2) (0 : Fin 2) (k + 1) 0)
      (twoPendantCore (Fin 2) (k + 1) 0 1) (k + 1) 0 p hleaf
    subst p
    change adjacentEqualVL k (Fin.last (k + 1)) ∈ adjacentEqualLeaves k
    simp [adjacentEqualLeaves]
  · have hq : q = 0 := Fin.eq_zero _
    subst q
    change adjacentEqualVS k ∈ adjacentEqualLeaves k
    simp [adjacentEqualLeaves]


theorem adjacentEqual_keep_nonleaf_seeds (k : ℕ) (loss : Finset (AdjacentEqualVertex k))
    (hsub : loss ⊆ adjacentEqualLeaves k) :
    adjacentEqualV k ∈ adjacentEqualInitial k \ loss ∧
      adjacentEqualUL k 0 ∈ adjacentEqualInitial k \ loss ∧
      adjacentEqualVL k 0 ∈ adjacentEqualInitial k \ loss := by
  classical
  constructor
  · apply Finset.mem_sdiff.mpr
    constructor
    · change (Sum.inl (Sum.inl (1 : Fin 2)) : AdjacentEqualVertex k) ∈ adjacentEqualInitial k
      simp [adjacentEqualInitial]
    · intro h
      have hm := hsub h
      simp only [adjacentEqualLeaves, Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with h | h | h | h <;> cases h
  · constructor
    · apply Finset.mem_sdiff.mpr
      constructor
      · change (Sum.inl (Sum.inr (Sum.inl (0 : Fin (k + 2))))) ∈ adjacentEqualInitial k
        simp [adjacentEqualInitial]
      · intro h
        have hm := hsub h
        simp only [adjacentEqualLeaves, Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with h | h | h | h
        · have hv := congrArg Fin.val ((adjacentEqualUL k).injective h)
          change 0 = k + 1 at hv
          omega
        · cases h
        · cases h
        · cases h
    · apply Finset.mem_sdiff.mpr
      constructor
      · change (Sum.inr (Sum.inl (0 : Fin (k + 2)))) ∈ adjacentEqualInitial k
        simp [adjacentEqualInitial]
      · intro h
        have hm := hsub h
        simp only [adjacentEqualLeaves, Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with h | h | h | h
        · cases h
        · cases h
        · have hv := congrArg Fin.val ((adjacentEqualVL k).injective h)
          change 0 = k + 1 at hv
          omega
        · cases h

theorem adjacentEqual_finish_of_components (k t : ℕ) (C : Finset (AdjacentEqualVertex k))
    (hu : adjacentEqualU k ∈ colorAfter (adjacentEqualGraph k).Adj C t)
    (hv : adjacentEqualV k ∈ colorAfter (adjacentEqualGraph k).Adj C t)
    (hUL : ∀ i, adjacentEqualUL k i ∈ colorAfter (adjacentEqualGraph k).Adj C t)
    (hUS : adjacentEqualUS k ∈ colorAfter (adjacentEqualGraph k).Adj C t)
    (hVL : ∀ i, adjacentEqualVL k i ∈ colorAfter (adjacentEqualGraph k).Adj C t)
    (hVS : adjacentEqualVS k ∈ colorAfter (adjacentEqualGraph k).Adj C t) :
    FinishesBy (adjacentEqualGraph k).Adj C t := by
  apply Finset.eq_univ_of_forall
  rintro ((x | (i | j)) | (p | q))
  · rcases adjacentEqual_core_split x with rfl | rfl
    · exact hu
    · exact hv
  · exact hUL i
  · have hj : j = 0 := Fin.eq_zero _
    subst j
    exact hUS
  · exact hVL p
  · have hq : q = 0 := Fin.eq_zero _
    subst q
    exact hVS

theorem adjacentEqual_leaf_loss_deadline (k : ℕ) (loss : Finset (AdjacentEqualVertex k))
    (hsub : loss ⊆ adjacentEqualLeaves k) (hsize : loss.card ≤ 2) :
    FinishesBy (adjacentEqualGraph k).Adj (adjacentEqualInitial k \ loss) (k + 2) := by
  classical
  let G := adjacentEqualGraph k
  let B := adjacentEqualInitial k
  let C := B \ loss
  have hseed := adjacentEqual_keep_nonleaf_seeds k loss hsub
  have hv0 : adjacentEqualV k ∈ C := hseed.1
  have hUL0 : adjacentEqualUL k 0 ∈ C := hseed.2.1
  have hVL0 : adjacentEqualVL k 0 ∈ C := hseed.2.2
  have hVLfill := twoPendant_armA_by_path_deadline
    (twoPendantGraph (SimpleGraph.pathGraph 2) (0 : Fin 2) (k + 1) 0)
    (twoPendantCore (Fin 2) (k + 1) 0 1) (k + 1) 0 C {0} (k + 1) hv0 (by
      intro i hi
      have heq := Finset.mem_singleton.mp hi
      subst i
      exact hVL0) (path_zero_finishes_n (k + 1))
  have hneq : (1 : Fin 2) ≠ 0 := by decide
  by_cases hshort : adjacentEqualUS k ∈ loss ∧ adjacentEqualVS k ∈ loss
  · have hp : ({adjacentEqualUS k, adjacentEqualVS k} : Finset (AdjacentEqualVertex k)) ⊆ loss := by
      intro z hz
      rcases (Finset.mem_insert.mp hz) with hz | hz
      · subst z
        exact hshort.1
      · have heq := Finset.mem_singleton.mp hz
        subst z
        exact hshort.2
    have hpairCard : ({adjacentEqualUS k, adjacentEqualVS k} : Finset (AdjacentEqualVertex k)).card = 2 := by
      have hne : adjacentEqualUS k ≠ adjacentEqualVS k := by intro h; cases h
      simp [hne]
    have hpair : loss = {adjacentEqualUS k, adjacentEqualVS k} :=
      (Finset.eq_of_subset_of_card_le hp (by omega)).symm
    have hend : adjacentEqualUL k (Fin.last (k + 1)) ∈ C := by
      apply Finset.mem_sdiff.mpr
      constructor
      · change (Sum.inl (Sum.inr (Sum.inl (Fin.last (k + 1))))) ∈ B
        simp [B, adjacentEqualInitial]
      · rw [hpair]
        intro h
        rcases Finset.mem_insert.mp h with h | h
        · cases h
        · have heq := Finset.mem_singleton.mp h
          cases heq
    have htail := adjacentEqual_u_tail_from_last k C hUL0 hend
    have hULall : ∀ i, adjacentEqualUL k i ∈ colorAfter G.Adj C k := by
      intro i
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
      · exact colorAfter_mono_time G.Adj C (Nat.zero_le _) hUL0
      · exact htail i
    have huN : adjacentEqualU k ∈ colorAfter G.Adj C (k + 1) :=
      adjacentEqual_u_head_to_root_step k (colorAfter G.Adj C k)
        (colorAfter_mono_time G.Adj C (Nat.zero_le _) hUL0) (htail 0)
    have hvN : adjacentEqualV k ∈ colorAfter G.Adj C (k + 1) :=
      colorAfter_mono_time G.Adj C (Nat.zero_le _) hv0
    have hcN : ∀ x : Fin 2, equalCore (Fin 2) (k + 1) x ∈ colorAfter G.Adj C (k + 1) := by
      intro x
      rcases adjacentEqual_core_split x with rfl | rfl
      · exact huN
      · exact hvN
    have hU := equal_u_heads_step (SimpleGraph.pathGraph 2) (0 : Fin 2) 1 hneq (k + 1)
      (colorAfter G.Adj C (k + 1)) hcN
      (Or.inl (colorAfter_mono_time G.Adj C (Nat.zero_le _) hUL0))
    have hV := twoPendant_heads_step_of_blue_neighbors
      (twoPendantGraph (SimpleGraph.pathGraph 2) (0 : Fin 2) (k + 1) 0)
      (twoPendantCore (Fin 2) (k + 1) 0 1) (k + 1) 0
      (colorAfter G.Adj C (k + 1)) hvN (by
        rintro (x | (i | j)) hx
        · exact hcN x
        · exact False.elim (hneq hx.1)
        · exact False.elim (hneq hx.1))
      (Or.inl (colorAfter_mono_time G.Adj C (Nat.zero_le _) hVL0))
    exact adjacentEqual_finish_of_components k (k + 2) C
      (colorAfter_mono_time G.Adj C (by omega : k + 1 ≤ k + 2) huN)
      (colorAfter_mono_time G.Adj C (Nat.zero_le _) hv0)
      (fun i => colorAfter_mono_time G.Adj C (by omega : k ≤ k + 2) (hULall i)) hU.2
      (fun i => colorAfter_mono_time G.Adj C (by omega : k + 1 ≤ k + 2) (hVLfill i)) hV.2
  · have hu1 : adjacentEqualU k ∈ colorAfter G.Adj C 1 := by
      by_cases hus : adjacentEqualUS k ∈ loss
      · have hvs : adjacentEqualVS k ∉ loss := fun h => hshort ⟨hus, h⟩
        apply adjacentEqual_v_to_u_step k C hv0 hVL0
        apply Finset.mem_sdiff.mpr
        refine ⟨?_, hvs⟩
        change (Sum.inr (Sum.inr (0 : Fin 1))) ∈ B
        simp [B, adjacentEqualInitial]
      · apply equal_short_u_step (SimpleGraph.pathGraph 2) (0 : Fin 2) 1 (k + 1) C
        apply Finset.mem_sdiff.mpr
        refine ⟨?_, hus⟩
        change (Sum.inl (Sum.inr (Sum.inr (0 : Fin 1)))) ∈ B
        simp [B, adjacentEqualInitial]
    have hv1 : adjacentEqualV k ∈ colorAfter G.Adj C 1 :=
      colorAfter_mono_time G.Adj C (Nat.zero_le _) hv0
    have hc1 : ∀ x : Fin 2, equalCore (Fin 2) (k + 1) x ∈ colorAfter G.Adj C 1 := by
      intro x
      rcases adjacentEqual_core_split x with rfl | rfl
      · exact hu1
      · exact hv1
    have hUfill := equal_long_u_from_first (SimpleGraph.pathGraph 2) (0 : Fin 2) 1 (k + 1)
      (colorAfter G.Adj C 1) hu1
      (colorAfter_mono_time G.Adj C (Nat.zero_le _) hUL0)
    have hULfinish : ∀ i, adjacentEqualUL k i ∈ colorAfter G.Adj C (k + 2) := by
      intro i
      have hm : adjacentEqualUL k i ∈ colorAfter G.Adj C (1 + (k + 1)) := by
        rw [colorAfter_add]
        exact hUfill i
      exact colorAfter_mono_time G.Adj C (by omega : 1 + (k + 1) ≤ k + 2) hm
    have hU := equal_u_heads_step (SimpleGraph.pathGraph 2) (0 : Fin 2) 1 hneq (k + 1)
      (colorAfter G.Adj C 1) hc1
      (Or.inl (colorAfter_mono_time G.Adj C (Nat.zero_le _) hUL0))
    have hV := twoPendant_heads_step_of_blue_neighbors
      (twoPendantGraph (SimpleGraph.pathGraph 2) (0 : Fin 2) (k + 1) 0)
      (twoPendantCore (Fin 2) (k + 1) 0 1) (k + 1) 0 (colorAfter G.Adj C 1) hv1 (by
        rintro (x | (i | j)) hx
        · exact hc1 x
        · exact False.elim (hneq hx.1)
        · exact False.elim (hneq hx.1))
      (Or.inl (colorAfter_mono_time G.Adj C (Nat.zero_le _) hVL0))
    exact adjacentEqual_finish_of_components k (k + 2) C
      (colorAfter_mono_time G.Adj C (by omega : 1 ≤ k + 2) hu1)
      (colorAfter_mono_time G.Adj C (Nat.zero_le _) hv0) hULfinish
      (colorAfter_mono_time G.Adj C (by omega : 2 ≤ k + 2) hU.2)
      (fun i => colorAfter_mono_time G.Adj C (by omega : k + 1 ≤ k + 2) (hVLfill i))
      (colorAfter_mono_time G.Adj C (by omega : 2 ≤ k + 2) hV.2)



/- Static cross-center blocking is prior methodology; see Jacob (2025),
   Lemma 3.9. The deadline comparison is a separate obligation below. -/
def adjacentEqualObstructionBlue (k : ℕ) : Finset (AdjacentEqualVertex k) := by
  classical
  exact Finset.univ.filter (fun z => match z with
    | Sum.inl (Sum.inl x) => x = 1
    | Sum.inl (Sum.inr (Sum.inl i)) => i = 0
    | Sum.inl (Sum.inr (Sum.inr _)) => False
    | Sum.inr (Sum.inl _) => True
    | Sum.inr (Sum.inr _) => False)

theorem adjacentEqual_obstruction_fixed (k : ℕ) :
    synchronousStep (adjacentEqualGraph k).Adj (adjacentEqualObstructionBlue k) =
      adjacentEqualObstructionBlue k := by
  classical
  let C := adjacentEqualObstructionBlue k
  apply le_antisymm
  · intro z hz
    rcases (mem_synchronousStep _ _ _).mp hz with hz | ⟨source, hs, ha, hu⟩
    · exact hz
    rcases source with (x | (i | j)) | (p | q)
    · have hx : x = 1 := by simpa [C, adjacentEqualObstructionBlue] using hs
      subst x
      have hU : adjacentEqualU k ∉ C := by
        change (Sum.inl (Sum.inl (0 : Fin 2)) : AdjacentEqualVertex k) ∉ C
        simp [C, adjacentEqualObstructionBlue]
      have hS : adjacentEqualVS k ∉ C := by
        change (Sum.inr (Sum.inr (0 : Fin 1)) : AdjacentEqualVertex k) ∉ C
        simp [C, adjacentEqualObstructionBlue]
      have hadj : (adjacentEqualGraph k).Adj (adjacentEqualV k) (adjacentEqualU k) := by
        change (SimpleGraph.pathGraph 2).Adj (1 : Fin 2) 0
        exact SimpleGraph.pathGraph_adj.mpr (Or.inr rfl)
      have heq := (hu (adjacentEqualU k) hadj hU).trans
        (hu (adjacentEqualVS k) ⟨rfl, rfl⟩ hS).symm
      cases heq
    · have hi : i = 0 := by simpa [C, adjacentEqualObstructionBlue] using hs
      subst i
      have hU : adjacentEqualU k ∉ C := by
        change (Sum.inl (Sum.inl (0 : Fin 2)) : AdjacentEqualVertex k) ∉ C
        simp [C, adjacentEqualObstructionBlue]
      have hT : adjacentEqualUL k (0 : Fin (k + 1)).succ ∉ C := by
        change (Sum.inl (Sum.inr (Sum.inl (0 : Fin (k + 1)).succ)) : AdjacentEqualVertex k) ∉ C
        simp [C, adjacentEqualObstructionBlue]
      have hadj : (adjacentEqualGraph k).Adj (adjacentEqualUL k 0)
          (adjacentEqualUL k (0 : Fin (k + 1)).succ) := by
        change (SimpleGraph.pathGraph (k + 2)).Adj 0 (0 : Fin (k + 1)).succ
        exact SimpleGraph.pathGraph_adj.mpr (Or.inl rfl)
      have heq := (hu (adjacentEqualU k) ⟨rfl, rfl⟩ hU).trans
        (hu (adjacentEqualUL k (0 : Fin (k + 1)).succ) hadj hT).symm
      cases heq
    · simp [adjacentEqualObstructionBlue] at hs
    · rcases z with (x | (i | j)) | (r | s)
      · have hx : x = 1 := Sum.inl_injective ha.1
        subst x
        simp [adjacentEqualObstructionBlue]
      · cases ha.1
      · cases ha.1
      · simp [adjacentEqualObstructionBlue]
      · exact ha.elim
    · simp [adjacentEqualObstructionBlue] at hs
  · exact subset_synchronousStep _ _

theorem adjacentEqual_support_card (k : ℕ) : (adjacentEqualSupport k).card = 3 := by
  classical
  change ({Sum.inl (Sum.inr (Sum.inr (0 : Fin 1))),
    Sum.inl (Sum.inr (Sum.inl (Fin.last (k + 1)))),
    Sum.inr (Sum.inr (0 : Fin 1))} : Finset (AdjacentEqualVertex k)).card = 3
  simp

theorem adjacentEqual_support_subset_leaves (k : ℕ) :
    adjacentEqualSupport k ⊆ adjacentEqualLeaves k := by
  classical
  intro z hz
  simp only [adjacentEqualSupport, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl <;> simp [adjacentEqualLeaves]

theorem adjacentEqual_support_kills (k : ℕ) :
    ¬ IsForcing (adjacentEqualGraph k).Adj
      (adjacentEqualInitial k \ adjacentEqualSupport k) := by
  classical
  have hsub : adjacentEqualInitial k \ adjacentEqualSupport k ⊆
      adjacentEqualObstructionBlue k := by
    intro z hz
    obtain ⟨hb, hn⟩ := Finset.mem_sdiff.mp hz
    rcases z with (x | (i | j)) | (p | q)
    · simpa [adjacentEqualObstructionBlue, adjacentEqualInitial] using hb
    · have hi : i = 0 ∨ i = Fin.last (k + 1) := by
        simpa [adjacentEqualInitial] using hb
      rcases hi with rfl | rfl
      · simp [adjacentEqualObstructionBlue]
      · exact False.elim (hn (by
          change adjacentEqualUL k (Fin.last (k + 1)) ∈ adjacentEqualSupport k
          simp [adjacentEqualSupport]))
    · have hj : j = 0 := Fin.eq_zero _
      subst j
      exact False.elim (hn (by
        change adjacentEqualUS k ∈ adjacentEqualSupport k
        simp [adjacentEqualSupport]))
    · simp [adjacentEqualObstructionBlue]
    · have hq : q = 0 := Fin.eq_zero _
      subst q
      exact False.elim (hn (by
        change adjacentEqualVS k ∈ adjacentEqualSupport k
        simp [adjacentEqualSupport]))
  intro hforcing
  obtain ⟨t, ht⟩ := IsForcing_mono (adjacentEqualGraph k).Adj hsub hforcing
  have hdone : colorAfter (adjacentEqualGraph k).Adj (adjacentEqualObstructionBlue k) t =
      Finset.univ := ht
  rw [colorAfter_of_fixed _ _ (adjacentEqual_obstruction_fixed k) t] at hdone
  have hm : adjacentEqualU k ∈ adjacentEqualObstructionBlue k := by
    rw [hdone]
    exact Finset.mem_univ _
  change (Sum.inl (Sum.inl (0 : Fin 2)) : AdjacentEqualVertex k) ∈
    adjacentEqualObstructionBlue k at hm
  simp [adjacentEqualObstructionBlue] at hm

theorem adjacentEqual_support_minimum (k : ℕ) :
    IsMinimumKilling (adjacentEqualGraph k).Adj
      (adjacentEqualInitial k) (adjacentEqualSupport k) := by
  classical
  refine ⟨(adjacentEqual_support_subset_leaves k).trans (adjacentEqual_leaves_subset k),
    adjacentEqual_support_kills k, ?_⟩
  intro loss _ hsmall
  have hsize : loss.card ≤ 2 := by rw [adjacentEqual_support_card] at hsmall; omega
  let E := loss ∩ adjacentEqualLeaves k
  have hEloss : E ⊆ loss := Finset.inter_subset_left
  have hEcard : E.card ≤ loss.card := Finset.card_le_card hEloss
  by_cases hsmallE : E.card ≤ 1
  · rcases E.eq_empty_or_nonempty with he | ⟨root, hr⟩
    · apply rooted_leaves_forcing_ordinary (adjacentEqualGraph k)
        (adjacentEqual_graph_isTree k) (adjacentEqualU k)
      intro z hz _
      have hleaf := adjacentEqual_leaves_mem k z hz
      apply Finset.mem_sdiff.mpr
      refine ⟨adjacentEqual_leaves_subset k hleaf, ?_⟩
      intro hloss
      have hm : z ∈ E := Finset.mem_inter.mpr ⟨hloss, hleaf⟩
      rw [he] at hm
      exact Finset.notMem_empty z hm
    · apply rooted_leaves_forcing_ordinary (adjacentEqualGraph k)
        (adjacentEqual_graph_isTree k) root
      intro z hz hne
      have hleaf := adjacentEqual_leaves_mem k z hz
      apply Finset.mem_sdiff.mpr
      refine ⟨adjacentEqual_leaves_subset k hleaf, ?_⟩
      intro hloss
      exact hne ((Finset.card_le_one_iff.mp hsmallE)
        (Finset.mem_inter.mpr ⟨hloss, hleaf⟩ : z ∈ E) hr)
  · have heq : E = loss := Finset.eq_of_subset_of_card_le hEloss (by omega)
    have hsub : loss ⊆ adjacentEqualLeaves k := by
      rw [← heq]
      exact Finset.inter_subset_right
    exact ⟨k + 2, adjacentEqual_leaf_loss_deadline k loss hsub hsize⟩

theorem adjacentEqual_restricted_deadline (k : ℕ) :
    RobustBy (adjacentEqualGraph k).Adj (adjacentEqualInitial k)
      (adjacentEqualSupport k) 2 (k + 2) := by
  intro loss hsub hsize
  exact adjacentEqual_leaf_loss_deadline k loss
    (hsub.trans (adjacentEqual_support_subset_leaves k)) hsize

def adjacentEqualRemoteLoss (k : ℕ) : Finset (AdjacentEqualVertex k) := by
  classical
  exact {adjacentEqualUL k 0, adjacentEqualUL k (Fin.last (k + 1))}

theorem adjacentEqual_remote_loss_subset (k : ℕ) :
    adjacentEqualRemoteLoss k ⊆ adjacentEqualInitial k := by
  classical
  intro z hz
  simp only [adjacentEqualRemoteLoss, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl
  · change (Sum.inl (Sum.inr (Sum.inl (0 : Fin (k + 2))))) ∈ adjacentEqualInitial k
    simp [adjacentEqualInitial]
  · change (Sum.inl (Sum.inr (Sum.inl (Fin.last (k + 1))))) ∈ adjacentEqualInitial k
    simp [adjacentEqualInitial]

theorem adjacentEqual_remote_loss_card (k : ℕ) : (adjacentEqualRemoteLoss k).card = 2 := by
  classical
  have hne : adjacentEqualUL k 0 ≠ adjacentEqualUL k (Fin.last (k + 1)) := by
    intro h
    have hv := congrArg Fin.val ((adjacentEqualUL k).injective h)
    change 0 = k + 1 at hv
    omega
  simp [adjacentEqualRemoteLoss, hne]

theorem adjacentEqual_remote_loss_lower (k t : ℕ)
    (hfinish : FinishesBy (adjacentEqualGraph k).Adj
      (adjacentEqualInitial k \ adjacentEqualRemoteLoss k) t) : k + 3 ≤ t := by
  classical
  let B := adjacentEqualInitial k
  let C := B \ adjacentEqualRemoteLoss k
  let e := twoPendantCommuteEquiv (Fin 2) (k + 1) 0 (k + 1) 0
  have hf := (twoPendant_finishesBy_commute (SimpleGraph.pathGraph 2) (0 : Fin 2) 1
    (k + 1) 0 (k + 1) 0 C t).mpr hfinish
  apply twoPendant_empty_A_white_root_completion_lower
    (twoPendantGraph (SimpleGraph.pathGraph 2) (1 : Fin 2) (k + 1) 0)
    (twoPendantCore (Fin 2) (k + 1) 0 0) (k + 1) 0 (relabelColors e C) ?_ ?_ t hf
  · intro hroot
    have hm := (mem_relabelColors e C
      (twoPendantCore (TwoPendantVertex (Fin 2) (k + 1) 0) (k + 1) 0
        (twoPendantCore (Fin 2) (k + 1) 0 0))).mp hroot
    change (Sum.inl (Sum.inl (0 : Fin 2)) : AdjacentEqualVertex k) ∈ C at hm
    have hb := (Finset.mem_sdiff.mp hm).1
    simp [B, adjacentEqualInitial] at hb
  · intro i hi
    have hm := (mem_relabelColors e C
      (twoPendantA (TwoPendantVertex (Fin 2) (k + 1) 0) (k + 1) 0 i)).mp hi
    change (Sum.inl (Sum.inr (Sum.inl i)) : AdjacentEqualVertex k) ∈ C at hm
    have hp := Finset.mem_sdiff.mp hm
    have hi0 : i = 0 ∨ i = Fin.last (k + 1) := by
      simpa [B, adjacentEqualInitial] using hp.1
    rcases hi0 with rfl | rfl
    · exact hp.2 (by
        change adjacentEqualUL k 0 ∈ adjacentEqualRemoteLoss k
        exact Finset.mem_insert_self _ _)
    · exact hp.2 (by
        change adjacentEqualUL k (Fin.last (k + 1)) ∈ adjacentEqualRemoteLoss k
        simp [adjacentEqualRemoteLoss])

theorem adjacentEqual_not_support (k : ℕ) :
    ¬ EveryMinimumSupport (adjacentEqualGraph k).Adj := by
  classical
  intro hU
  have hB : IsForcing (adjacentEqualGraph k).Adj (adjacentEqualInitial k) := by
    refine ⟨k + 2, ?_⟩
    simpa only [Finset.sdiff_empty] using
      adjacentEqual_leaf_loss_deadline k ∅ (by simp) (by simp)
  have hglobal := (hU (adjacentEqualInitial k) hB (adjacentEqualSupport k)
    (adjacentEqual_support_minimum k) 2 (k + 2)).mpr (adjacentEqual_restricted_deadline k)
  have hf := hglobal (adjacentEqualRemoteLoss k) (adjacentEqual_remote_loss_subset k)
    (by rw [adjacentEqual_remote_loss_card])
  have hlower := adjacentEqual_remote_loss_lower k (k + 2) hf
  omega

theorem adjacentEqual_tree_not_support (k : ℕ) :
    (adjacentEqualGraph k).IsTree ∧ ¬ EveryMinimumSupport (adjacentEqualGraph k).Adj :=
  ⟨adjacentEqual_graph_isTree k, adjacentEqual_not_support k⟩


end FaultObservationResearch
