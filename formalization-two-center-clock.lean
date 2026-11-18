module

/-
A single initial coloring with a minimum head-pair support and a slower remote
terminal loss. Conditional on the inner attached graph being a tree. This does
not prove structural exhaustion of arbitrary trees or research priority.
-/
public import «formalization-two-pendant-geometry»
public import «formalization-two-pendant-clock»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
universe u

abbrev TwoCenterVertex (V : Type u) (a b c d : ℕ) :=
  TwoPendantVertex (TwoPendantVertex V a b) c d

def twoCenterGraph {V : Type u} (R : SimpleGraph V) (u v : V) (a b c d : ℕ) :=
  twoPendantGraph (twoPendantGraph R u a b) (twoPendantCore V a b v) c d

def twoCenterInitial (V : Type u) [Fintype V] (a b c d : ℕ) :
    Finset (TwoCenterVertex V a b c d) := by
  classical
  exact Finset.univ.filter (fun z => match z with
    | Sum.inl (Sum.inl _) => True
    | Sum.inl (Sum.inr (Sum.inl i)) => i = Fin.last a
    | Sum.inl (Sum.inr (Sum.inr j)) => j = Fin.last b
    | Sum.inr (Sum.inl k) => k = 0
    | Sum.inr (Sum.inr l) => l = 0)

def twoCenterInnerA (V : Type u) (a b c d : ℕ) : Fin (a + 1) ↪ TwoCenterVertex V a b c d where
  toFun := fun i => Sum.inl (Sum.inr (Sum.inl i))
  inj' := by intro i j h; exact Sum.inl_injective (Sum.inr_injective (Sum.inl_injective h))

def twoCenterInnerB (V : Type u) (a b c d : ℕ) : Fin (b + 1) ↪ TwoCenterVertex V a b c d where
  toFun := fun i => Sum.inl (Sum.inr (Sum.inr i))
  inj' := by intro i j h; exact Sum.inr_injective (Sum.inr_injective (Sum.inl_injective h))

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem twoCenter_initial_eq_nested (v : V) (a b c d : ℕ) :
    twoCenterInitial V a b c d =
      twoPendantInitial (twoPendantCore V a b v) c d (twoPendantCoreAndEnds V a b) := by
  classical
  ext ((x | (i | j)) | (k | l)) <;>
    simp [twoCenterInitial, twoPendantInitial, twoPendantCoreAndEnds, twoPendantCore]

theorem twoCenter_inner_A_from_last (R : SimpleGraph V) (u v : V) (a b c d : ℕ)
    (C : Finset (TwoCenterVertex V a b c d))
    (hr : Sum.inl (Sum.inl u) ∈ C)
    (hend : twoCenterInnerA V a b c d (Fin.last a) ∈ C) :
    ∀ i, twoCenterInnerA V a b c d i ∈ colorAfter (twoCenterGraph R u v a b c d).Adj C a := by
  classical
  intro i
  refine colorAfter_embeds_with_blue_exterior (SimpleGraph.pathGraph (a + 1))
    (twoCenterGraph R u v a b c d) (twoCenterInnerA V a b c d) (fun h => h)
    {Fin.last a} C ?_ ?_ a i ?_
  · rintro j ((x | (k | l)) | (m | n)) hz
    · change x = u ∧ j = 0 at hz
      rcases hz with ⟨rfl, _⟩
      exact Or.inr hr
    · exact Or.inl ⟨k, rfl, hz⟩
    · exact hz.elim
    · change (Sum.inr (Sum.inl j) : TwoPendantVertex V a b) = Sum.inl v ∧ m = 0 at hz
      cases hz.1
    · change (Sum.inr (Sum.inl j) : TwoPendantVertex V a b) = Sum.inl v ∧ n = 0 at hz
      cases hz.1
  · intro j hj
    have heq := Finset.mem_singleton.mp hj
    subst j
    exact hend
  · rw [path_last_finishes_n a]
    exact Finset.mem_univ _

theorem twoCenter_inner_B_from_last (R : SimpleGraph V) (u v : V) (a b c d : ℕ)
    (C : Finset (TwoCenterVertex V a b c d))
    (hr : Sum.inl (Sum.inl u) ∈ C)
    (hend : twoCenterInnerB V a b c d (Fin.last b) ∈ C) :
    ∀ i, twoCenterInnerB V a b c d i ∈ colorAfter (twoCenterGraph R u v a b c d).Adj C b := by
  classical
  intro i
  refine colorAfter_embeds_with_blue_exterior (SimpleGraph.pathGraph (b + 1))
    (twoCenterGraph R u v a b c d) (twoCenterInnerB V a b c d) (fun h => h)
    {Fin.last b} C ?_ ?_ b i ?_
  · rintro j ((x | (k | l)) | (m | n)) hz
    · change x = u ∧ j = 0 at hz
      rcases hz with ⟨rfl, _⟩
      exact Or.inr hr
    · exact hz.elim
    · exact Or.inl ⟨l, rfl, hz⟩
    · change (Sum.inr (Sum.inr j) : TwoPendantVertex V a b) = Sum.inl v ∧ m = 0 at hz
      cases hz.1
    · change (Sum.inr (Sum.inr j) : TwoPendantVertex V a b) = Sum.inl v ∧ n = 0 at hz
      cases hz.1
  · intro j hj
    have heq := Finset.mem_singleton.mp hj
    subst j
    exact hend
  · rw [path_last_finishes_n b]
    exact Finset.mem_univ _

theorem twoCenter_head_support_minimum (R : SimpleGraph V) (u v : V) (a b c d : ℕ)
    (hinner : (twoPendantGraph R u a b).IsTree) :
    IsMinimumKilling (twoCenterGraph R u v a b c d).Adj (twoCenterInitial V a b c d)
      (twoPendantHeads (TwoPendantVertex V a b) c d) := by
  rw [twoCenter_initial_eq_nested v a b c d]
  exact twoPendant_nested_heads_minimum R u v a b c d hinner

theorem twoCenter_restricted_head_deadline (R : SimpleGraph V) (u v : V) (hvu : v ≠ u)
    (a b c d : ℕ) :
    RobustBy (twoCenterGraph R u v a b c d).Adj (twoCenterInitial V a b c d)
      (twoPendantHeads (TwoPendantVertex V a b) c d) 1
      (max (max a b) (max (c + 1) (d + 1))) := by
  classical
  let W := TwoPendantVertex V a b
  let G := twoCenterGraph R u v a b c d
  let B := twoCenterInitial V a b c d
  let T := max (max a b) (max (c + 1) (d + 1))
  intro loss hsub hsize
  let C := B \ loss
  have hnotInner : ∀ x : W, twoPendantCore W c d x ∉ loss := by
    intro x hx
    have hm := hsub hx
    simp only [twoPendantHeads, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with heq | heq
    · cases heq
    · cases heq
  have hkeep : ∀ x : W, twoPendantCore W c d x ∈ B → twoPendantCore W c d x ∈ C := by
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨hx, hnotInner x⟩
  have hcore : ∀ x : V, Sum.inl (Sum.inl x) ∈ C := by
    intro x
    apply hkeep (Sum.inl x)
    change (Sum.inl (Sum.inl x) : TwoCenterVertex V a b c d) ∈ B
    simp [B, twoCenterInitial]
  have hendA : twoCenterInnerA V a b c d (Fin.last a) ∈ C := by
    apply hkeep (Sum.inr (Sum.inl (Fin.last a)))
    change (Sum.inl (Sum.inr (Sum.inl (Fin.last a))) : TwoCenterVertex V a b c d) ∈ B
    simp [B, twoCenterInitial]
  have hendB : twoCenterInnerB V a b c d (Fin.last b) ∈ C := by
    apply hkeep (Sum.inr (Sum.inr (Fin.last b)))
    change (Sum.inl (Sum.inr (Sum.inr (Fin.last b))) : TwoCenterVertex V a b c d) ∈ B
    simp [B, twoCenterInitial]
  have hfillA := twoCenter_inner_A_from_last R u v a b c d C (hcore u) hendA
  have hfillB := twoCenter_inner_B_from_last R u v a b c d C (hcore u) hendB
  have hhead : twoPendantA W c d 0 ∈ C ∨ twoPendantB W c d 0 ∈ C := by
    by_cases ha : twoPendantA W c d 0 ∈ loss
    · have hb : twoPendantB W c d 0 ∉ loss := by
        intro hb
        have heq := (Finset.card_le_one_iff.mp hsize) ha hb
        cases heq
      refine Or.inr (Finset.mem_sdiff.mpr ⟨?_, hb⟩)
      change (Sum.inr (Sum.inr (0 : Fin (d + 1))) : TwoCenterVertex V a b c d) ∈ B
      simp [B, twoCenterInitial]
    · refine Or.inl (Finset.mem_sdiff.mpr ⟨?_, ha⟩)
      change (Sum.inr (Sum.inl (0 : Fin (c + 1))) : TwoCenterVertex V a b c d) ∈ B
      simp [B, twoCenterInitial]
  have hheads := twoPendant_heads_step_of_blue_neighbors (twoPendantGraph R u a b)
    (twoPendantCore V a b v) c d C (hcore v) (by
      rintro (x | (i | j)) hz
      · exact hcore x
      · exact False.elim (hvu hz.1)
      · exact False.elim (hvu hz.1)) hhead
  have houtA := twoPendant_armA_by_path_deadline (twoPendantGraph R u a b)
    (twoPendantCore V a b v) c d (colorAfter G.Adj C 1) {0} c
    (colorAfter_mono_time G.Adj C (Nat.zero_le _) (hcore v)) (by
      intro i hi
      have heq := Finset.mem_singleton.mp hi
      subst i
      exact hheads.1) (path_zero_finishes_n c)
  have houtB := twoPendant_armB_by_path_deadline (twoPendantGraph R u a b)
    (twoPendantCore V a b v) c d (colorAfter G.Adj C 1) {0} d
    (colorAfter_mono_time G.Adj C (Nat.zero_le _) (hcore v)) (by
      intro i hi
      have heq := Finset.mem_singleton.mp hi
      subst i
      exact hheads.2) (path_zero_finishes_n d)
  have haT : a ≤ T := le_trans (le_max_left a b) (le_max_left _ _)
  have hbT : b ≤ T := le_trans (le_max_right a b) (le_max_left _ _)
  have hcT : c + 1 ≤ T := le_trans (le_max_left _ _) (le_max_right _ _)
  have hdT : d + 1 ≤ T := le_trans (le_max_right _ _) (le_max_right _ _)
  apply Finset.eq_univ_of_forall
  rintro ((x | (i | j)) | (k | l))
  · exact colorAfter_mono_time G.Adj C (Nat.zero_le _) (hcore x)
  · exact colorAfter_mono_time G.Adj C haT (hfillA i)
  · exact colorAfter_mono_time G.Adj C hbT (hfillB j)
  · have hm : twoPendantA W c d k ∈ colorAfter G.Adj C (1 + c) := by
      rw [colorAfter_add]
      exact houtA k
    exact colorAfter_mono_time G.Adj C (by omega : 1 + c ≤ T) hm
  · have hm : twoPendantB W c d l ∈ colorAfter G.Adj C (1 + d) := by
      rw [colorAfter_add]
      exact houtB l
    exact colorAfter_mono_time G.Adj C (by omega : 1 + d ≤ T) hm

theorem twoCenter_remote_terminal_loss_lower (R : SimpleGraph V) (u v : V) (a b c d : ℕ)
    (t : ℕ) (hfinish : FinishesBy (twoCenterGraph R u v a b c d).Adj
      (twoCenterInitial V a b c d \ {twoCenterInnerA V a b c d (Fin.last a)}) t) :
    a + b + 1 ≤ t := by
  classical
  let B := twoCenterInitial V a b c d
  let C := B \ {twoCenterInnerA V a b c d (Fin.last a)}
  let e := twoPendantCommuteEquiv V a b c d
  have hf := (twoPendant_finishesBy_commute R u v a b c d C t).mpr hfinish
  apply twoPendant_delayed_completion_lower (twoPendantGraph R v c d)
    (twoPendantCore V c d u) a b (relabelColors e C) ?_ ?_ t hf
  · intro i hi
    have hm := (mem_relabelColors e C (twoPendantA (TwoPendantVertex V c d) a b i)).mp hi
    change (Sum.inl (Sum.inr (Sum.inl i)) : TwoCenterVertex V a b c d) ∈ C at hm
    have hp := Finset.mem_sdiff.mp hm
    have hiLast : i = Fin.last a := by simpa [B, twoCenterInitial] using hp.1
    subst i
    exact hp.2 (Finset.mem_singleton_self _)
  · intro j hj
    have hm := (mem_relabelColors e C (twoPendantB (TwoPendantVertex V c d) a b j)).mp hj
    change (Sum.inl (Sum.inr (Sum.inr j)) : TwoCenterVertex V a b c d) ∈ C at hm
    have hp := (Finset.mem_sdiff.mp hm).1
    have hjLast : j = Fin.last b := by simpa [B, twoCenterInitial] using hp
    subst j
    exact le_rfl

theorem twoCenter_strict_not_support (R : SimpleGraph V) (u v : V) (hvu : v ≠ u)
    (a b c d : ℕ) (hinner : (twoPendantGraph R u a b).IsTree)
    (hstrict : max (c + 1) (d + 1) < a + b + 1) :
    ¬ EveryMinimumSupport (twoCenterGraph R u v a b c d).Adj := by
  classical
  intro hU
  let G := twoCenterGraph R u v a b c d
  let B := twoCenterInitial V a b c d
  let H := twoPendantHeads (TwoPendantVertex V a b) c d
  let T := max (max a b) (max (c + 1) (d + 1))
  have hmin := twoCenter_head_support_minimum R u v a b c d hinner
  have hB : IsForcing G.Adj B := by
    have hm := hmin.2.2 ∅ (Finset.empty_subset _) (by
      rw [twoPendant_heads_card]
      simp)
    simpa only [Finset.sdiff_empty] using hm
  have hrestricted : RobustBy G.Adj B H 1 T :=
    twoCenter_restricted_head_deadline R u v hvu a b c d
  have hglobal : RobustBy G.Adj B B 1 T := (hU B hB H hmin 1 T).mpr hrestricted
  have hsub : {twoCenterInnerA V a b c d (Fin.last a)} ⊆ B := by
    intro z hz
    have heq := Finset.mem_singleton.mp hz
    subst z
    change (Sum.inl (Sum.inr (Sum.inl (Fin.last a))) : TwoCenterVertex V a b c d) ∈ B
    simp [B, twoCenterInitial]
  have hf := hglobal {twoCenterInnerA V a b c d (Fin.last a)} hsub (by simp)
  have hlower := twoCenter_remote_terminal_loss_lower R u v a b c d T hf
  have hT : T < a + b + 1 := max_lt (max_lt (by omega) (by omega)) hstrict
  exact (not_lt_of_ge hlower) hT

end FaultObservationResearch
