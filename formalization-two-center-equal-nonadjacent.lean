module

/-
Equal long arms and nonadjacent centers. All colors, vertices and edges refer
to the same full graph. Intermediate helper checks are not a classification.
-/
public import «formalization-tree-attachments»
public import «formalization-pendant-root-delay»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

abbrev EqualCenterVertex (V : Type u) (n : ℕ) := TwoCenterVertex V n 0 n 0
abbrev equalCore (V : Type u) (n : ℕ) (x : V) : EqualCenterVertex V n :=
  Sum.inl (Sum.inl x)
abbrev equalULong (V : Type u) (n : ℕ) := twoCenterInnerA V n 0 n 0
abbrev equalUShort (V : Type u) (n : ℕ) : EqualCenterVertex V n :=
  twoCenterInnerB V n 0 n 0 0
abbrev equalVLong (V : Type u) (n : ℕ) := twoPendantA (TwoPendantVertex V n 0) n 0
abbrev equalVShort (V : Type u) (n : ℕ) : EqualCenterVertex V n :=
  twoPendantB (TwoPendantVertex V n 0) n 0 0

def equalInitial (u : V) (n : ℕ) : Finset (EqualCenterVertex V n) := by
  classical
  exact Finset.univ.filter (fun z => match z with
    | Sum.inl (Sum.inl x) => x ≠ u
    | Sum.inl (Sum.inr (Sum.inl i)) => i = 0
    | Sum.inl (Sum.inr (Sum.inr _)) => True
    | Sum.inr (Sum.inl i) => i = 0
    | Sum.inr (Sum.inr _) => True)

def equalInnerInitial (u : V) (n : ℕ) : Finset (TwoPendantVertex V n 0) := by
  classical
  exact Finset.univ.filter (fun z => match z with
    | Sum.inl x => x ≠ u
    | Sum.inr (Sum.inl i) => i = 0
    | Sum.inr (Sum.inr _) => True)

omit [DecidableEq V] in
theorem equal_initial_eq_nested (u v : V) (hvu : v ≠ u) (n : ℕ) :
    equalInitial u n = twoPendantInitial (twoPendantCore V n 0 v) n 0
      (equalInnerInitial u n) := by
  classical
  ext ((x | (i | j)) | (k | l)) <;>
    simp [equalInitial, equalInnerInitial, twoPendantInitial, twoPendantCore]
  · intro h
    subst x
    exact hvu
  · exact Fin.eq_zero _

theorem equal_short_u_step (R : SimpleGraph V) (u v : V) (n : ℕ)
    (C : Finset (EqualCenterVertex V n)) (hs : equalUShort V n ∈ C) :
    equalCore V n u ∈ synchronousStep (twoCenterGraph R u v n 0 n 0).Adj C := by
  apply (mem_synchronousStep _ _ _).mpr
  refine Or.inr ⟨equalUShort V n, hs, ⟨rfl, rfl⟩, ?_⟩
  rintro ((x | (i | j)) | (k | l)) ha _
  · exact congrArg (equalCore V n) ha.1
  · exact ha.elim
  · have hj : j = 0 := by apply Fin.ext; have := j.isLt; change j.val = 0; omega
    subst j
    exact False.elim ((SimpleGraph.pathGraph 1).loopless.irrefl 0 ha)
  · cases ha.1
  · cases ha.1

theorem equal_short_v_step (R : SimpleGraph V) (u v : V) (n : ℕ)
    (C : Finset (EqualCenterVertex V n)) (hs : equalVShort V n ∈ C) :
    equalCore V n v ∈ synchronousStep (twoCenterGraph R u v n 0 n 0).Adj C := by
  apply (mem_synchronousStep _ _ _).mpr
  refine Or.inr ⟨equalVShort V n, hs, ⟨rfl, rfl⟩, ?_⟩
  rintro ((x | (i | j)) | (k | l)) ha _
  · change (Sum.inl x : TwoPendantVertex V n 0) = Sum.inl v ∧ (0 : Fin 1) = 0 at ha
    exact congrArg Sum.inl ha.1
  · cases ha.1
  · cases ha.1
  · exact ha.elim
  · have hl : l = 0 := by apply Fin.ext; have := l.isLt; change l.val = 0; omega
    subst l
    exact False.elim ((SimpleGraph.pathGraph 1).loopless.irrefl 0 ha)

theorem equal_core_off_center_step (R : SimpleGraph V) (u v x y : V) (n : ℕ)
    (C : Finset (EqualCenterVertex V n)) (hxu : x ≠ u) (hxv : x ≠ v)
    (hxy : R.Adj x y) (hx : equalCore V n x ∈ C)
    (hc : ∀ z, z ≠ y → equalCore V n z ∈ C) :
    equalCore V n y ∈ synchronousStep (twoCenterGraph R u v n 0 n 0).Adj C := by
  apply (mem_synchronousStep _ _ _).mpr
  refine Or.inr ⟨equalCore V n x, hx, hxy, ?_⟩
  rintro ((z | (i | j)) | (k | l)) ha hw
  · by_cases hzy : z = y
    · exact congrArg (equalCore V n) hzy
    · exact False.elim (hw (hc z hzy))
  · exact False.elim (hxu ha.1)
  · exact False.elim (hxu ha.1)
  · have heq : x = v := Sum.inl_injective ha.1
    exact False.elim (hxv heq)
  · have heq : x = v := Sum.inl_injective ha.1
    exact False.elim (hxv heq)

theorem equal_core_with_heads_step (R : SimpleGraph V) (u v x y : V) (n : ℕ)
    (C : Finset (EqualCenterVertex V n))
    (hxy : R.Adj x y) (hx : equalCore V n x ∈ C)
    (hc : ∀ z, z ≠ y → equalCore V n z ∈ C)
    (hUL : equalULong V n 0 ∈ C) (hUS : equalUShort V n ∈ C)
    (hVL : equalVLong V n 0 ∈ C) (hVS : equalVShort V n ∈ C) :
    equalCore V n y ∈ synchronousStep (twoCenterGraph R u v n 0 n 0).Adj C := by
  apply (mem_synchronousStep _ _ _).mpr
  refine Or.inr ⟨equalCore V n x, hx, hxy, ?_⟩
  rintro ((z | (i | j)) | (k | l)) ha hw
  · by_cases hzy : z = y
    · exact congrArg (equalCore V n) hzy
    · exact False.elim (hw (hc z hzy))
  · exact False.elim (hw (ha.2 ▸ hUL))
  · have hj : j = 0 := by apply Fin.ext; have := j.isLt; change j.val = 0; omega
    subst j
    exact False.elim (hw hUS)
  · exact False.elim (hw (ha.2 ▸ hVL))
  · have hl : l = 0 := by apply Fin.ext; have := l.isLt; change l.val = 0; omega
    subst l
    exact False.elim (hw hVS)


theorem equal_u_blue_one (R : SimpleGraph V) (u v : V) (n : ℕ)
    (hnu : ∃ x, R.Adj u x) (hnadj : ¬ R.Adj u v)
    (loss : Finset (EqualCenterVertex V n)) (hsize : loss.card ≤ 1) :
    equalCore V n u ∈ colorAfter (twoCenterGraph R u v n 0 n 0).Adj
      (equalInitial u n \ loss) 1 := by
  classical
  let B := equalInitial u n
  let C := B \ loss
  by_cases hs : equalUShort V n ∈ loss
  · have hnot : ∀ z, z ≠ equalUShort V n → z ∉ loss := by
      intro z hz hm
      exact hz ((Finset.card_le_one_iff.mp hsize) hm hs)
    have hc : ∀ z, z ≠ u → equalCore V n z ∈ C := by
      intro z hzu
      apply Finset.mem_sdiff.mpr
      constructor
      · change (Sum.inl (Sum.inl z) : EqualCenterVertex V n) ∈ B
        simpa [B, equalInitial] using hzu
      · apply hnot
        intro heq
        cases heq
    obtain ⟨x, hux⟩ := hnu
    have hxu : x ≠ u := (R.ne_of_adj hux).symm
    have hxv : x ≠ v := by
      intro heq
      subst x
      exact hnadj hux
    exact equal_core_off_center_step R u v x u n C hxu hxv hux.symm (hc x hxu) hc
  · apply equal_short_u_step R u v n C
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, hs⟩
    change (Sum.inl (Sum.inr (Sum.inr (0 : Fin 1))) : EqualCenterVertex V n) ∈ B
    simp [B, equalInitial]

theorem equal_core_blue_two (R : SimpleGraph V) (u v : V) (n : ℕ)
    (hn : ∀ x, ∃ y, R.Adj x y) (hnadj : ¬ R.Adj u v)
    (loss : Finset (EqualCenterVertex V n)) (hsize : loss.card ≤ 1) :
    ∀ x, equalCore V n x ∈ colorAfter (twoCenterGraph R u v n 0 n 0).Adj
      (equalInitial u n \ loss) 2 := by
  classical
  let G := twoCenterGraph R u v n 0 n 0
  let B := equalInitial u n
  let C := B \ loss
  have hu := equal_u_blue_one R u v n (hn u) hnadj loss hsize
  intro x
  by_cases hxu : x = u
  · subst x
    exact colorAfter_mono_time G.Adj C (by omega : 1 ≤ 2) hu
  · by_cases hxloss : equalCore V n x ∈ loss
    · have hnot : ∀ z, z ≠ equalCore V n x → z ∉ loss := by
        intro z hz hm
        exact hz ((Finset.card_le_one_iff.mp hsize) hm hxloss)
      have hc : ∀ z, z ≠ x → equalCore V n z ∈ colorAfter G.Adj C 1 := by
        intro z hzx
        by_cases hzu : z = u
        · subst z
          exact hu
        · apply colorAfter_mono_time G.Adj C (Nat.zero_le _)
          apply Finset.mem_sdiff.mpr
          constructor
          · change (Sum.inl (Sum.inl z) : EqualCenterVertex V n) ∈ B
            simpa [B, equalInitial] using hzu
          · apply hnot
            intro heq
            exact hzx (Sum.inl_injective (Sum.inl_injective heq))
      have hUL : equalULong V n 0 ∈ colorAfter G.Adj C 1 := by
        apply colorAfter_mono_time G.Adj C (Nat.zero_le _)
        apply Finset.mem_sdiff.mpr
        constructor
        · change (Sum.inl (Sum.inr (Sum.inl (0 : Fin (n + 1))))) ∈ B
          simp [B, equalInitial]
        · apply hnot
          intro heq
          cases heq
      have hUS : equalUShort V n ∈ colorAfter G.Adj C 1 := by
        apply colorAfter_mono_time G.Adj C (Nat.zero_le _)
        apply Finset.mem_sdiff.mpr
        constructor
        · change (Sum.inl (Sum.inr (Sum.inr (0 : Fin 1)))) ∈ B
          simp [B, equalInitial]
        · apply hnot
          intro heq
          cases heq
      have hVL : equalVLong V n 0 ∈ colorAfter G.Adj C 1 := by
        apply colorAfter_mono_time G.Adj C (Nat.zero_le _)
        apply Finset.mem_sdiff.mpr
        constructor
        · change (Sum.inr (Sum.inl (0 : Fin (n + 1)))) ∈ B
          simp [B, equalInitial]
        · apply hnot
          intro heq
          cases heq
      have hVS : equalVShort V n ∈ colorAfter G.Adj C 1 := by
        apply colorAfter_mono_time G.Adj C (Nat.zero_le _)
        apply Finset.mem_sdiff.mpr
        constructor
        · change (Sum.inr (Sum.inr (0 : Fin 1))) ∈ B
          simp [B, equalInitial]
        · apply hnot
          intro heq
          cases heq
      obtain ⟨y, hxy⟩ := hn x
      have hyx : y ≠ x := (R.ne_of_adj hxy).symm
      exact equal_core_with_heads_step R u v y x n (colorAfter G.Adj C 1)
        hxy.symm (hc y hyx) hc hUL hUS hVL hVS
    · apply colorAfter_mono_time G.Adj C (Nat.zero_le _)
      apply Finset.mem_sdiff.mpr
      constructor
      · change (Sum.inl (Sum.inl x) : EqualCenterVertex V n) ∈ B
        simpa [B, equalInitial] using hxu
      · exact hxloss


theorem equal_u_heads_step (R : SimpleGraph V) (u v : V) (hvu : v ≠ u) (n : ℕ)
    (C : Finset (EqualCenterVertex V n))
    (hc : ∀ x, equalCore V n x ∈ C)
    (hh : equalULong V n 0 ∈ C ∨ equalUShort V n ∈ C) :
    equalULong V n 0 ∈ synchronousStep (twoCenterGraph R u v n 0 n 0).Adj C ∧
      equalUShort V n ∈ synchronousStep (twoCenterGraph R u v n 0 n 0).Adj C := by
  constructor
  · rcases hh with hL | hS
    · exact subset_synchronousStep _ _ hL
    · apply (mem_synchronousStep _ _ _).mpr
      refine Or.inr ⟨equalCore V n u, hc u, ⟨rfl, rfl⟩, ?_⟩
      rintro ((x | (i | j)) | (k | l)) ha hw
      · exact False.elim (hw (hc x))
      · exact congrArg (equalULong V n) ha.2
      · have hj : j = 0 := Fin.eq_zero _
        subst j
        exact False.elim (hw hS)
      · exact False.elim (hvu (Sum.inl_injective ha.1).symm)
      · exact False.elim (hvu (Sum.inl_injective ha.1).symm)
  · rcases hh with hL | hS
    · apply (mem_synchronousStep _ _ _).mpr
      refine Or.inr ⟨equalCore V n u, hc u, ⟨rfl, rfl⟩, ?_⟩
      rintro ((x | (i | j)) | (k | l)) ha hw
      · exact False.elim (hw (hc x))
      · exact False.elim (hw (ha.2 ▸ hL))
      · have hj : j = 0 := Fin.eq_zero _
        subst j
        rfl
      · exact False.elim (hvu (Sum.inl_injective ha.1).symm)
      · exact False.elim (hvu (Sum.inl_injective ha.1).symm)
    · exact subset_synchronousStep _ _ hS

theorem equal_long_u_from_first (R : SimpleGraph V) (u v : V) (n : ℕ)
    (C : Finset (EqualCenterVertex V n))
    (hr : equalCore V n u ∈ C) (hh : equalULong V n 0 ∈ C) :
    ∀ i, equalULong V n i ∈ colorAfter (twoCenterGraph R u v n 0 n 0).Adj C n := by
  classical
  intro i
  refine colorAfter_embeds_with_blue_exterior (SimpleGraph.pathGraph (n + 1))
    (twoCenterGraph R u v n 0 n 0) (equalULong V n) (fun h => h)
    {0} C ?_ ?_ n i ?_
  · rintro j ((x | (k | l)) | (m | p)) hz
    · change x = u ∧ j = 0 at hz
      rcases hz with ⟨rfl, _⟩
      exact Or.inr hr
    · exact Or.inl ⟨k, rfl, hz⟩
    · exact hz.elim
    · cases hz.1
    · cases hz.1
  · intro j hj
    have heq := Finset.mem_singleton.mp hj
    subst j
    exact hh
  · rw [path_zero_finishes_n n]
    exact Finset.mem_univ _

theorem equal_finish_of_core_heads (R : SimpleGraph V) (u v : V) (n : ℕ)
    (C : Finset (EqualCenterVertex V n))
    (hc : ∀ x, equalCore V n x ∈ C)
    (hUL : equalULong V n 0 ∈ C) (hUS : equalUShort V n ∈ C)
    (hVL : equalVLong V n 0 ∈ C) (hVS : equalVShort V n ∈ C) :
    FinishesBy (twoCenterGraph R u v n 0 n 0).Adj C n := by
  classical
  let G := twoCenterGraph R u v n 0 n 0
  have hU := equal_long_u_from_first R u v n C (hc u) hUL
  have hV := twoPendant_armA_by_path_deadline (twoPendantGraph R u n 0)
    (twoPendantCore V n 0 v) n 0 C {0} n (hc v) (by
      intro i hi
      have heq := Finset.mem_singleton.mp hi
      subst i
      exact hVL) (path_zero_finishes_n n)
  apply Finset.eq_univ_of_forall
  rintro ((x | (i | j)) | (k | l))
  · exact colorAfter_mono_time G.Adj C (Nat.zero_le _) (hc x)
  · exact hU i
  · have hj : j = 0 := Fin.eq_zero _
    subst j
    exact colorAfter_mono_time G.Adj C (Nat.zero_le _) hUS
  · exact hV k
  · have hl : l = 0 := Fin.eq_zero _
    subst l
    exact colorAfter_mono_time G.Adj C (Nat.zero_le _) hVS

theorem equal_all_single_loss_deadline (R : SimpleGraph V) (u v : V) (hvu : v ≠ u)
    (n : ℕ) (hn : ∀ x, ∃ y, R.Adj x y) (hnadj : ¬ R.Adj u v)
    (loss : Finset (EqualCenterVertex V n)) (hsize : loss.card ≤ 1) :
    FinishesBy (twoCenterGraph R u v n 0 n 0).Adj (equalInitial u n \ loss) (n + 3) := by
  classical
  let G := twoCenterGraph R u v n 0 n 0
  let B := equalInitial u n
  let C := B \ loss
  have hc := equal_core_blue_two R u v n hn hnadj loss hsize
  have hpair : ∀ s t : EqualCenterVertex V n, s ≠ t → s ∈ B → t ∈ B →
      s ∈ colorAfter G.Adj C 2 ∨ t ∈ colorAfter G.Adj C 2 := by
    intro s t hst hs ht
    by_cases hsl : s ∈ loss
    · have htl : t ∉ loss := by
        intro htl
        exact hst ((Finset.card_le_one_iff.mp hsize) hsl htl)
      exact Or.inr (colorAfter_mono_time G.Adj C (Nat.zero_le _)
        (Finset.mem_sdiff.mpr ⟨ht, htl⟩))
    · exact Or.inl (colorAfter_mono_time G.Adj C (Nat.zero_le _)
        (Finset.mem_sdiff.mpr ⟨hs, hsl⟩))
  have hU := equal_u_heads_step R u v hvu n (colorAfter G.Adj C 2) hc
    (hpair (equalULong V n 0) (equalUShort V n) (by intro h; cases h) (by
      change (Sum.inl (Sum.inr (Sum.inl (0 : Fin (n + 1))))) ∈ B
      simp [B, equalInitial]) (by
      change (Sum.inl (Sum.inr (Sum.inr (0 : Fin 1)))) ∈ B
      simp [B, equalInitial]))
  have hV := twoPendant_heads_step_of_blue_neighbors (twoPendantGraph R u n 0)
    (twoPendantCore V n 0 v) n 0 (colorAfter G.Adj C 2) (hc v) (by
      rintro (x | (i | j)) hx
      · exact hc x
      · exact False.elim (hvu hx.1)
      · exact False.elim (hvu hx.1))
    (hpair (equalVLong V n 0) (equalVShort V n) (by intro h; cases h) (by
      change (Sum.inr (Sum.inl (0 : Fin (n + 1)))) ∈ B
      simp [B, equalInitial]) (by
      change (Sum.inr (Sum.inr (0 : Fin 1))) ∈ B
      simp [B, equalInitial]))
  have hc3 : ∀ x, equalCore V n x ∈ colorAfter G.Adj C 3 :=
    fun x => colorAfter_mono_time G.Adj C (by omega : 2 ≤ 3) (hc x)
  change colorAfter G.Adj C (n + 3) = Finset.univ
  rw [Nat.add_comm n 3, colorAfter_add]
  exact equal_finish_of_core_heads R u v n (colorAfter G.Adj C 3)
    hc3 hU.1 hU.2 hV.1 hV.2



theorem equal_restricted_head_deadline (R : SimpleGraph V) (u v : V) (hvu : v ≠ u)
    (n : ℕ) (hnadj : ¬ R.Adj u v) :
    RobustBy (twoCenterGraph R u v n 0 n 0).Adj (equalInitial u n)
      (twoPendantHeads (TwoPendantVertex V n 0) n 0) 1 (n + 1) := by
  classical
  let W := TwoPendantVertex V n 0
  let G := twoCenterGraph R u v n 0 n 0
  let B := equalInitial u n
  intro loss hsub hsize
  let C := B \ loss
  have hnot : ∀ x : W, twoPendantCore W n 0 x ∉ loss := by
    intro x hx
    have hm := hsub hx
    simp only [twoPendantHeads, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with heq | heq <;> cases heq
  have hc : ∀ x, x ≠ u → equalCore V n x ∈ C := by
    intro x hxu
    apply Finset.mem_sdiff.mpr
    constructor
    · change (Sum.inl (Sum.inl x) : EqualCenterVertex V n) ∈ B
      simpa [B, equalInitial] using hxu
    · exact hnot (Sum.inl x)
  have hUL : equalULong V n 0 ∈ C := by
    apply Finset.mem_sdiff.mpr
    constructor
    · change (Sum.inl (Sum.inr (Sum.inl (0 : Fin (n + 1))))) ∈ B
      simp [B, equalInitial]
    · exact hnot (Sum.inr (Sum.inl 0))
  have hUS : equalUShort V n ∈ C := by
    apply Finset.mem_sdiff.mpr
    constructor
    · change (Sum.inl (Sum.inr (Sum.inr (0 : Fin 1)))) ∈ B
      simp [B, equalInitial]
    · exact hnot (Sum.inr (Sum.inr 0))
  have hu1 := equal_short_u_step R u v n C hUS
  have hc1 : ∀ x, equalCore V n x ∈ colorAfter G.Adj C 1 := by
    intro x
    by_cases hxu : x = u
    · subst x
      exact hu1
    · exact colorAfter_mono_time G.Adj C (Nat.zero_le _) (hc x hxu)
  have hpair : equalVLong V n 0 ∈ C ∨ equalVShort V n ∈ C := by
    by_cases hL : equalVLong V n 0 ∈ loss
    · have hS : equalVShort V n ∉ loss := by
        intro hS
        have heq := (Finset.card_le_one_iff.mp hsize) hL hS
        cases heq
      apply Or.inr
      apply Finset.mem_sdiff.mpr
      refine ⟨?_, hS⟩
      change (Sum.inr (Sum.inr (0 : Fin 1))) ∈ B
      simp [B, equalInitial]
    · apply Or.inl
      apply Finset.mem_sdiff.mpr
      refine ⟨?_, hL⟩
      change (Sum.inr (Sum.inl (0 : Fin (n + 1)))) ∈ B
      simp [B, equalInitial]
  have hV := twoPendant_heads_step_of_blue_neighbors (twoPendantGraph R u n 0)
    (twoPendantCore V n 0 v) n 0 C (hc v hvu) (by
      rintro (x | (i | j)) hx
      · apply hc x
        intro hxu
        subst x
        exact hnadj hx.symm
      · exact False.elim (hvu hx.1)
      · exact False.elim (hvu hx.1)) hpair
  have hdone : FinishesBy G.Adj C (1 + n) := by
    change colorAfter G.Adj C (1 + n) = Finset.univ
    rw [colorAfter_add]
    exact equal_finish_of_core_heads R u v n (colorAfter G.Adj C 1) hc1
      (colorAfter_mono_time G.Adj C (Nat.zero_le _) hUL)
      (colorAfter_mono_time G.Adj C (Nat.zero_le _) hUS) hV.1 hV.2
  exact FinishesBy_mono_time G.Adj C hdone (by omega)

theorem equal_head_support_minimum (R : SimpleGraph V) (u v : V) (hvu : v ≠ u)
    (n : ℕ) (hn : ∀ x, ∃ y, R.Adj x y) (hnadj : ¬ R.Adj u v) :
    IsMinimumKilling (twoCenterGraph R u v n 0 n 0).Adj (equalInitial u n)
      (twoPendantHeads (TwoPendantVertex V n 0) n 0) := by
  classical
  have heq := equal_initial_eq_nested u v hvu n
  refine ⟨?_, ?_, ?_⟩
  · rw [heq]
    exact twoPendant_heads_subset (twoPendantCore V n 0 v) n 0 (equalInnerInitial u n)
  · rw [heq]
    exact twoPendant_heads_kill (twoPendantGraph R u n 0)
      (twoPendantCore V n 0 v) n 0 (equalInnerInitial u n)
  · intro loss _ hsmall
    have hsize : loss.card ≤ 1 := by
      rw [twoPendant_heads_card] at hsmall
      omega
    exact ⟨n + 3, equal_all_single_loss_deadline R u v hvu n hn hnadj loss hsize⟩

theorem equal_remote_head_loss_lower (R : SimpleGraph V) (u v : V) (n t : ℕ)
    (hfinish : FinishesBy (twoCenterGraph R u v n 0 n 0).Adj
      (equalInitial u n \ {equalULong V n 0}) t) : n + 2 ≤ t := by
  classical
  let B := equalInitial u n
  let C := B \ {equalULong V n 0}
  let e := twoPendantCommuteEquiv V n 0 n 0
  have hf := (twoPendant_finishesBy_commute R u v n 0 n 0 C t).mpr hfinish
  apply twoPendant_empty_A_white_root_completion_lower (twoPendantGraph R v n 0)
    (twoPendantCore V n 0 u) n 0 (relabelColors e C) ?_ ?_ t hf
  · intro hroot
    have hm := (mem_relabelColors e C
      (twoPendantCore (TwoPendantVertex V n 0) n 0 (twoPendantCore V n 0 u))).mp hroot
    change equalCore V n u ∈ C at hm
    have hne : u ≠ u := by
      simpa [B, equalInitial] using (Finset.mem_sdiff.mp hm).1
    exact hne rfl
  · intro i hi
    have hm := (mem_relabelColors e C
      (twoPendantA (TwoPendantVertex V n 0) n 0 i)).mp hi
    change (Sum.inl (Sum.inr (Sum.inl i)) : EqualCenterVertex V n) ∈ C at hm
    have hp := Finset.mem_sdiff.mp hm
    have hi0 : i = 0 := by simpa [B, equalInitial] using hp.1
    subst i
    exact hp.2 (Finset.mem_singleton_self _)

theorem equal_nonadjacent_not_support (R : SimpleGraph V) (u v : V) (hvu : v ≠ u)
    (n : ℕ) (hn : ∀ x, ∃ y, R.Adj x y) (hnadj : ¬ R.Adj u v) :
    ¬ EveryMinimumSupport (twoCenterGraph R u v n 0 n 0).Adj := by
  classical
  intro hU
  let G := twoCenterGraph R u v n 0 n 0
  let B := equalInitial u n
  let H := twoPendantHeads (TwoPendantVertex V n 0) n 0
  have hmin := equal_head_support_minimum R u v hvu n hn hnadj
  have hB : IsForcing G.Adj B := by
    refine ⟨n + 3, ?_⟩
    simpa only [Finset.sdiff_empty] using
      equal_all_single_loss_deadline R u v hvu n hn hnadj ∅ (by simp)
  have hrestricted : RobustBy G.Adj B H 1 (n + 1) :=
    equal_restricted_head_deadline R u v hvu n hnadj
  have hglobal : RobustBy G.Adj B B 1 (n + 1) := (hU B hB H hmin 1 (n + 1)).mpr hrestricted
  have hsub : {equalULong V n 0} ⊆ B := by
    intro z hz
    have heq := Finset.mem_singleton.mp hz
    subst z
    change (Sum.inl (Sum.inr (Sum.inl (0 : Fin (n + 1))))) ∈ B
    simp [B, equalInitial]
  have hf := hglobal {equalULong V n 0} hsub (by simp)
  have hlower := equal_remote_head_loss_lower R u v n (n + 1) hf
  omega

theorem equal_nonadjacent_tree_not_support (R : SimpleGraph V) (htree : R.IsTree)
    (u v : V) (hvu : v ≠ u) (n : ℕ) (hnadj : ¬ R.Adj u v) :
    (twoCenterGraph R u v n 0 n 0).IsTree ∧
      ¬ EveryMinimumSupport (twoCenterGraph R u v n 0 n 0).Adj := by
  have : Nontrivial V := ⟨⟨v, u, hvu⟩⟩
  exact ⟨twoCenterGraph_isTree R htree u v n 0 n 0,
    equal_nonadjacent_not_support R u v hvu n
      htree.connected.preconnected.exists_adj_of_nontrivial hnadj⟩


end FaultObservationResearch
