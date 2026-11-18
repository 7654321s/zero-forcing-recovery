module

public import «formalization-rooted-leaves»
public import «formalization-transport»
public import «formalization-path-seed-packing»
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Data.Finset.Sort
public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option autoImplicit false

namespace FaultObservationResearch

/-- A cycle on at least three vertices has two distinct neighbors at each vertex. -/
theorem cycle_neighbors_distinct (n : ℕ) (v : Fin (n + 3)) : v - 1 ≠ v + 1 := by
  intro heq
  have hc := SimpleGraph.cycleGraph_degree_three_le (n := n) (v := v)
  rw [SimpleGraph.degree, SimpleGraph.cycleGraph_neighborFinset, heq] at hc
  simp at hc

theorem cycle_adj_iff_neighbors (n : ℕ) (v w : Fin (n + 3)) :
    (SimpleGraph.cycleGraph (n + 3)).Adj v w ↔ w = v - 1 ∨ w = v + 1 := by
  change w ∈ (SimpleGraph.cycleGraph (n + 3)).neighborSet v ↔ _
  rw [SimpleGraph.cycleGraph_neighborSet]
  simp

def cycleRotation (n : ℕ) (a : Fin (n + 3)) : Fin (n + 3) ≃ Fin (n + 3) where
  toFun x := a + x
  invFun x := x - a
  left_inv x := by simp
  right_inv x := by simp [add_comm a]

theorem cycle_rotation_symm_adj (n : ℕ) (a x y : Fin (n + 3)) :
    (SimpleGraph.cycleGraph (n + 3)).Adj ((cycleRotation n a).symm x)
      ((cycleRotation n a).symm y) ↔ (SimpleGraph.cycleGraph (n + 3)).Adj x y := by
  change (SimpleGraph.cycleGraph (n + 3)).Adj (x - a) (y - a) ↔
    (SimpleGraph.cycleGraph (n + 3)).Adj x y
  simp [SimpleGraph.cycleGraph_adj, sub_sub_sub_cancel_right]

/-- Static forcing criterion. The adjacent-pair criterion is prior work. -/
theorem cycle_forcing_iff_adjacent_pair (n : ℕ) (blue : Finset (Fin (n + 3))) :
    IsForcing (SimpleGraph.cycleGraph (n + 3)).Adj blue ↔
      ∃ u ∈ blue, ∃ v ∈ blue, (SimpleGraph.cycleGraph (n + 3)).Adj u v := by
  classical
  let G := SimpleGraph.cycleGraph (n + 3)
  change IsForcing G.Adj blue ↔ ∃ u ∈ blue, ∃ v ∈ blue, G.Adj u v
  constructor
  · intro hforcing
    by_contra hpair
    have hfixed : synchronousStep G.Adj blue = blue := by
      apply le_antisymm _ (subset_synchronousStep G.Adj blue)
      intro target htarget
      rcases (mem_synchronousStep _ _ _).mp htarget with hb | ⟨source, hs, _, huniq⟩
      · exact hb
      · have hL : G.Adj source (source - 1) := (cycle_adj_iff_neighbors n _ _).mpr (Or.inl rfl)
        have hR : G.Adj source (source + 1) := (cycle_adj_iff_neighbors n _ _).mpr (Or.inr rfl)
        have hwL : source - 1 ∉ blue := fun hb => hpair ⟨source, hs, source - 1, hb, hL⟩
        have hwR : source + 1 ∉ blue := fun hb => hpair ⟨source, hs, source + 1, hb, hR⟩
        exact False.elim (cycle_neighbors_distinct n source
          ((huniq _ hL hwL).trans (huniq _ hR hwR).symm))
    have hfull := FinishesBy_of_stable G.Adj blue hforcing 0 hfixed
    change blue = Finset.univ at hfull
    have h01 : G.Adj 0 1 := (cycle_adj_iff_neighbors n _ _).mpr (Or.inr (zero_add _).symm)
    exact hpair ⟨0, by simp [hfull], 1, by simp [hfull], h01⟩
  · rintro ⟨u, hu, v, hv, huv⟩
    let C := colorAfter G.Adj blue (n + 3)
    have hfixed : synchronousStep G.Adj C = C := by
      simpa only [Fintype.card_fin, C, colorAfter] using colorAfter_stabilizes_card G.Adj blue
    let good (x : Fin (n + 3)) := x ∈ C ∧ ∃ y ∈ C, G.Adj x y
    have extend {x y : Fin (n + 3)} (hxy : G.Adj x y) (hx : good x) : good y := by
      obtain ⟨hxC, z, hzC, hxz⟩ := hx
      refine ⟨?_, x, hxC, hxy.symm⟩
      by_contra hyC
      have unique : ∀ w, G.Adj x w → w ∉ C → w = y := by
        intro w hxw hwC
        rcases (cycle_adj_iff_neighbors n x y).mp hxy with hy | hy <;>
          rcases (cycle_adj_iff_neighbors n x z).mp hxz with hz | hz <;>
          rcases (cycle_adj_iff_neighbors n x w).mp hxw with hw | hw
        all_goals first
          | exact hw.trans hy.symm
          | exact False.elim (hyC (hy.trans hz.symm ▸ hzC))
          | exact False.elim (hwC (hw.trans hz.symm ▸ hzC))
      have hyStep := (mem_synchronousStep G.Adj C y).mpr (Or.inr ⟨x, hxC, hxy, unique⟩)
      exact hyC (hfixed ▸ hyStep)
    have follow {x y : Fin (n + 3)} (walk : G.Walk x y) : good x → good y := by
      induction walk with
      | nil => exact id
      | cons hxy _ ih => exact fun hx => ih (extend hxy hx)
    have huGood : good u := ⟨colorAfter_mono_time G.Adj blue (Nat.zero_le _) hu,
      v, colorAfter_mono_time G.Adj blue (Nat.zero_le _) hv, huv⟩
    refine ⟨n + 3, Finset.eq_univ_of_forall ?_⟩
    intro x
    obtain ⟨walk⟩ := SimpleGraph.preconnected_cycleGraph (n := n + 3) u x
    exact (follow walk huGood).1

/-- A vertex cover of the edges induced by the initial blue set on a cycle. -/
def HitsCycleEdges (n : ℕ) (blue loss : Finset (Fin (n + 3))) : Prop :=
  ∀ u ∈ blue, ∀ v ∈ blue, (SimpleGraph.cycleGraph (n + 3)).Adj u v →
    u ∈ loss ∨ v ∈ loss

theorem cycle_nonforcing_sdiff_iff_hits_edges (n : ℕ)
    (blue loss : Finset (Fin (n + 3))) :
    ¬ IsForcing (SimpleGraph.cycleGraph (n + 3)).Adj (blue \ loss) ↔
      HitsCycleEdges n blue loss := by
  classical
  rw [cycle_forcing_iff_adjacent_pair]
  unfold HitsCycleEdges
  constructor
  · intro h u hu v hv huv
    by_contra hn
    have hul : u ∉ loss := fun hmem => hn (Or.inl hmem)
    have hvl : v ∉ loss := fun hmem => hn (Or.inr hmem)
    exact h ⟨u, Finset.mem_sdiff.mpr ⟨hu, hul⟩, v, Finset.mem_sdiff.mpr ⟨hv, hvl⟩, huv⟩
  · rintro h ⟨u, hu, v, hv, huv⟩
    obtain ⟨hub, hul⟩ := Finset.mem_sdiff.mp hu
    obtain ⟨hvb, hvl⟩ := Finset.mem_sdiff.mp hv
    exact (h u hub v hvb huv).elim hul hvl

theorem cycle_minimum_killing_iff_minimum_vertex_cover (n : ℕ)
    (blue support : Finset (Fin (n + 3))) :
    IsMinimumKilling (SimpleGraph.cycleGraph (n + 3)).Adj blue support ↔
      support ⊆ blue ∧ HitsCycleEdges n blue support ∧
        ∀ loss : Finset (Fin (n + 3)), loss ⊆ blue → HitsCycleEdges n blue loss →
          support.card ≤ loss.card := by
  rw [IsMinimumKilling_iff_card_minimum]
  simp only [cycle_nonforcing_sdiff_iff_hits_edges]

theorem cycle_step_forward (n : ℕ) (blue : Finset (Fin (n + 3)))
    (v : Fin (n + 3)) (hv : v ∈ blue) (hprev : v - 1 ∈ blue) :
    v + 1 ∈ synchronousStep (SimpleGraph.cycleGraph (n + 3)).Adj blue := by
  apply (mem_synchronousStep _ _ _).mpr
  refine Or.inr ⟨v, hv, (cycle_adj_iff_neighbors n _ _).mpr (Or.inr rfl), ?_⟩
  intro w hw hwWhite
  rcases (cycle_adj_iff_neighbors n _ _).mp hw with h | h
  · exact False.elim (hwWhite (h ▸ hprev))
  · exact h

theorem cycle_step_backward (n : ℕ) (blue : Finset (Fin (n + 3)))
    (v : Fin (n + 3)) (hv : v ∈ blue) (hnext : v + 1 ∈ blue) :
    v - 1 ∈ synchronousStep (SimpleGraph.cycleGraph (n + 3)).Adj blue := by
  apply (mem_synchronousStep _ _ _).mpr
  refine Or.inr ⟨v, hv, (cycle_adj_iff_neighbors n _ _).mpr (Or.inl rfl), ?_⟩
  intro w hw hwWhite
  rcases (cycle_adj_iff_neighbors n _ _).mp hw with h | h
  · exact h
  · exact False.elim (hwWhite (h ▸ hnext))

theorem cycle_step_first_white (n : ℕ) (blue : Finset (Fin (n + 3)))
    (i : Fin (n + 3)) (hi : 2 ≤ i.val)
    (hbefore : ∀ j : Fin (n + 3), j.val < i.val → j ∈ blue) :
    i ∈ synchronousStep (SimpleGraph.cycleGraph (n + 3)).Adj blue := by
  have hi0 : i ≠ 0 := by
    intro h
    simp [h] at hi
  have hsub := Fin.val_sub_one_of_ne_zero hi0
  have hj0 : i - 1 ≠ 0 := by
    intro h
    rw [h] at hsub
    simp at hsub
    omega
  have hsub₂ := Fin.val_sub_one_of_ne_zero hj0
  have hout := cycle_step_forward n blue (i - 1)
    (hbefore _ (by omega)) (hbefore _ (by omega))
  simpa only [sub_add_cancel] using hout

theorem cycle_step_last_white (n : ℕ) (blue : Finset (Fin (n + 3)))
    (i : Fin (n + 3)) (h0 : 0 ∈ blue) (h1 : 1 ∈ blue)
    (hafter : ∀ j : Fin (n + 3), i.val < j.val → j ∈ blue) :
    i ∈ synchronousStep (SimpleGraph.cycleGraph (n + 3)).Adj blue := by
  have shiftBlue (s : Fin (n + 3)) (hs : 1 ≤ s.val) (hs₂ : s.val ≤ 2) :
      i + s ∈ blue := by
    have hbound := i.isLt
    by_cases hin : i.val + s.val < n + 3
    · apply hafter
      rw [Fin.val_add, Nat.mod_eq_of_lt hin]
      omega
    · have hv : (i + s).val = i.val + s.val - (n + 3) := by
        rw [Fin.val_add, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      by_cases hz : (i + s).val = 0
      · have heq : i + s = 0 := Fin.ext hz
        rwa [heq]
      · have heq : i + s = 1 := Fin.ext (by simp only [Fin.val_one]; omega)
        rwa [heq]
  have hs1 : i + 1 ∈ blue := shiftBlue 1 (by simp) (by simp)
  have hs2 : (i + 1) + 1 ∈ blue := by
    rw [add_assoc]
    have hval : ((1 : Fin (n + 3)) + 1).val = 2 := by
      simp [Fin.val_add, Nat.mod_eq_of_lt (show 2 < n + 3 by omega)]
    exact shiftBlue (1 + 1) (by rw [hval]; decide) (by rw [hval])
  simpa only [add_sub_cancel_right] using cycle_step_backward n blue (i + 1) hs1 hs2

theorem cycle_step_white_card_le_of_zero_one (n : ℕ)
    (blue : Finset (Fin (n + 3))) (h0 : 0 ∈ blue) (h1 : 1 ∈ blue) :
    (Finset.univ \ synchronousStep (SimpleGraph.cycleGraph (n + 3)).Adj blue).card ≤
      (Finset.univ \ blue).card - 2 := by
  classical
  let white := Finset.univ \ blue
  let next := synchronousStep (SimpleGraph.cycleGraph (n + 3)).Adj blue
  let nextWhite := Finset.univ \ next
  change nextWhite.card ≤ white.card - 2
  have hsub : nextWhite ⊆ white := by
    intro j hj
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h =>
      (Finset.mem_sdiff.mp hj).2 (subset_synchronousStep _ _ h)⟩
  by_cases hn : white.Nonempty
  · let first := white.min' hn
    let last := white.max' hn
    have hf := white.min'_mem hn
    have hl := white.max'_mem hn
    have hf2 : 2 ≤ first.val := by
      have hw : first ∉ blue := (Finset.mem_sdiff.mp hf).2
      by_contra h
      have hcase : first.val = 0 ∨ first.val = 1 := by omega
      rcases hcase with h | h
      · exact hw ((show first = 0 from Fin.ext h) ▸ h0)
      · exact hw ((show first = 1 from Fin.ext h) ▸ h1)
    have hfNext : first ∈ next := cycle_step_first_white n blue first hf2 (by
      intro j hj
      by_contra hw
      have hmin := Finset.min'_le white j (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hw⟩)
      change first.val ≤ j.val at hmin
      omega)
    have hlNext : last ∈ next := cycle_step_last_white n blue last h0 h1 (by
      intro j hj
      by_contra hw
      have hmax := Finset.le_max' white j (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hw⟩)
      change j.val ≤ last.val at hmax
      omega)
    by_cases heq : first = last
    · have hnone : nextWhite = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro j hj
        have hmin := Finset.min'_le white j (hsub hj)
        have hmax := Finset.le_max' white j (hsub hj)
        have hfirst : j = first := le_antisymm (heq ▸ hmax) hmin
        exact (Finset.mem_sdiff.mp hj).2 (hfirst ▸ hfNext)
      simp [hnone]
    · have hpair : {first, last} ⊆ white := by
        intro j hj
        rcases Finset.mem_insert.mp hj with h | h
        · rwa [h]
        · rwa [Finset.mem_singleton.mp h]
      have hremain : nextWhite ⊆ white \ {first, last} := by
        intro j hj
        refine Finset.mem_sdiff.mpr ⟨hsub hj, ?_⟩
        intro hjpair
        rcases Finset.mem_insert.mp hjpair with h | h
        · exact (Finset.mem_sdiff.mp hj).2 (h ▸ hfNext)
        · exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_singleton.mp h ▸ hlNext)
      calc
        nextWhite.card ≤ (white \ {first, last}).card := Finset.card_le_card hremain
        _ = white.card - 2 := by rw [Finset.card_sdiff_of_subset hpair, Finset.card_pair heq]
  · have hwhite : white = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hcard := Finset.card_le_card hsub
    simpa [hwhite] using hcard

/-- In a forcing coloring, a round on a cycle removes two whites when at least two remain. -/
theorem cycle_step_white_card_le (n : ℕ) (blue : Finset (Fin (n + 3)))
    (hforcing : IsForcing (SimpleGraph.cycleGraph (n + 3)).Adj blue) :
    (Finset.univ \ synchronousStep (SimpleGraph.cycleGraph (n + 3)).Adj blue).card ≤
      (Finset.univ \ blue).card - 2 := by
  classical
  let G := SimpleGraph.cycleGraph (n + 3)
  obtain ⟨u, hu, v, hv, huv⟩ := (cycle_forcing_iff_adjacent_pair n blue).mp hforcing
  obtain ⟨a, ha, haNext⟩ : ∃ a : Fin (n + 3), a ∈ blue ∧ a + 1 ∈ blue := by
    rcases (cycle_adj_iff_neighbors n u v).mp huv with hvu | hvu
    · exact ⟨v, hv, by rwa [hvu, sub_add_cancel]⟩
    · exact ⟨u, hu, hvu ▸ hv⟩
  let e := cycleRotation n a
  have hadj (x y : Fin (n + 3)) : G.Adj (e.symm x) (e.symm y) ↔ G.Adj x y := by
    exact cycle_rotation_symm_adj n a x y
  let shifted := relabelColors e.symm blue
  have h0 : 0 ∈ shifted := by
    simpa [shifted, e, cycleRotation] using ha
  have h1 : 1 ∈ shifted := by
    simpa [shifted, e, cycleRotation] using haNext
  have hstep : relabelColors e.symm (synchronousStep G.Adj blue) =
      synchronousStep G.Adj shifted :=
    synchronousStep_relabel e.symm G.Adj G.Adj hadj blue
  have hwhite : (Finset.univ \ shifted).card = (Finset.univ \ blue).card := by
    rw [← relabelColors_univ e.symm, ← relabelColors_sdiff, relabelColors_card]
    rw [relabelColors_univ]
  have hnext : (Finset.univ \ synchronousStep G.Adj shifted).card =
      (Finset.univ \ synchronousStep G.Adj blue).card := by
    rw [← hstep, ← relabelColors_univ e.symm, ← relabelColors_sdiff, relabelColors_card]
    rw [relabelColors_univ]
  have hbound := cycle_step_white_card_le_of_zero_one n shifted h0 h1
  change (Finset.univ \ synchronousStep G.Adj shifted).card ≤
    (Finset.univ \ shifted).card - 2 at hbound
  rwa [hnext, hwhite] at hbound

theorem cycle_colorAfter_white_card_le (n : ℕ) (blue : Finset (Fin (n + 3)))
    (hforcing : IsForcing (SimpleGraph.cycleGraph (n + 3)).Adj blue) (t : ℕ) :
    (Finset.univ \ colorAfter (SimpleGraph.cycleGraph (n + 3)).Adj blue t).card ≤
      (Finset.univ \ blue).card - 2 * t := by
  let adj := (SimpleGraph.cycleGraph (n + 3)).Adj
  induction t with
  | zero => simp [colorAfter]
  | succ t ih =>
    have hft : IsForcing adj (colorAfter adj blue t) :=
      IsForcing_mono adj (colorAfter_mono_time adj blue (Nat.zero_le t)) hforcing
    have hstep := cycle_step_white_card_le n (colorAfter adj blue t) hft
    change (Finset.univ \ synchronousStep adj (colorAfter adj blue t)).card ≤
      (Finset.univ \ colorAfter adj blue t).card - 2 at hstep
    change (Finset.univ \ synchronousStep adj (colorAfter adj blue t)).card ≤
      (Finset.univ \ blue).card - 2 * (t + 1)
    change (Finset.univ \ colorAfter adj blue t).card ≤
      (Finset.univ \ blue).card - 2 * t at ih
    omega

/-- Every forcing coloring on a cycle finishes within half its white count, rounded up. -/
theorem cycle_finishesBy_of_white_card_le (n : ℕ) (blue : Finset (Fin (n + 3)))
    (hforcing : IsForcing (SimpleGraph.cycleGraph (n + 3)).Adj blue) (t : ℕ)
    (hcount : (Finset.univ \ blue).card ≤ 2 * t) :
    FinishesBy (SimpleGraph.cycleGraph (n + 3)).Adj blue t := by
  classical
  have hle := cycle_colorAfter_white_card_le n blue hforcing t
  have hzero : (Finset.univ \ colorAfter (SimpleGraph.cycleGraph (n + 3)).Adj blue t).card = 0 :=
    by omega
  have hempty := Finset.card_eq_zero.mp hzero
  exact le_antisymm (Finset.subset_univ _) (Finset.sdiff_eq_empty_iff_subset.mp hempty)

/-- The unrestricted upper bound for the all-blue case below the killing threshold. -/
theorem cycle_full_blue_robust_upper (n : ℕ) (support : Finset (Fin (n + 3)))
    (hminimum : IsMinimumKilling (SimpleGraph.cycleGraph (n + 3)).Adj Finset.univ support)
    (budget deadline : ℕ) (hbudget : budget < support.card) (ht : budget ≤ 2 * deadline) :
    RobustBy (SimpleGraph.cycleGraph (n + 3)).Adj Finset.univ Finset.univ budget deadline := by
  classical
  intro loss hsub hsmall
  have hf := hminimum.2.2 loss hsub (lt_of_le_of_lt hsmall hbudget)
  apply cycle_finishesBy_of_white_card_le n _ hf deadline
  have heq : (Finset.univ \ (Finset.univ \ loss)) = loss := by
    ext v
    simp
  rw [heq]
  exact le_trans hsmall ht

/-- The state after one round at a vertex only uses its candidate sources and their neighbors. -/
theorem synchronousStep_agree_at_of_agree_near_sources
    {V : Type*} [Fintype V] [DecidableEq V] (adj : V → V → Prop)
    (blue other : Finset V) (target : V) (ht : target ∈ blue ↔ target ∈ other)
    (hneighborhood : ∀ source, adj source target →
      (source ∈ blue ↔ source ∈ other) ∧
        ∀ w, adj source w → (w ∈ blue ↔ w ∈ other)) :
    target ∈ synchronousStep adj blue ↔ target ∈ synchronousStep adj other := by
  simp only [mem_synchronousStep]
  constructor
  · rintro (hold | ⟨source, hs, ha, hunique⟩)
    · exact Or.inl (ht.mp hold)
    · obtain ⟨hsEq, hwEq⟩ := hneighborhood source ha
      refine Or.inr ⟨source, hsEq.mp hs, ha, ?_⟩
      exact fun w hw hwhite => hunique w hw (fun hb => hwhite ((hwEq w hw).mp hb))
  · rintro (hold | ⟨source, hs, ha, hunique⟩)
    · exact Or.inl (ht.mpr hold)
    · obtain ⟨hsEq, hwEq⟩ := hneighborhood source ha
      refine Or.inr ⟨source, hsEq.mpr hs, ha, ?_⟩
      exact fun w hw hwhite => hunique w hw (fun hb => hwhite ((hwEq w hw).mpr hb))

/-- Initial blue guards make the evolution inside a region independent of other colors. -/
theorem colorAfter_agree_on_with_guards
    {V : Type*} [Fintype V] [DecidableEq V] (adj : V → V → Prop)
    (region guards blue other : Finset V) (hguardBlue : guards ⊆ blue)
    (hguardOther : guards ⊆ other)
    (hinitial : ∀ x ∈ region, x ∈ blue ↔ x ∈ other)
    (hnear : ∀ target ∈ region, ∀ source, adj source target →
      (source ∈ region ∨ source ∈ guards) ∧
        ∀ w, adj source w → w ∈ region ∨ w ∈ guards)
    (t : ℕ) :
    ∀ x ∈ region, x ∈ colorAfter adj blue t ↔ x ∈ colorAfter adj other t := by
  induction t with
  | zero => exact hinitial
  | succ t ih =>
    intro x hx
    have hagree (z : V) (hz : z ∈ region ∨ z ∈ guards) :
        z ∈ colorAfter adj blue t ↔ z ∈ colorAfter adj other t := by
      rcases hz with hr | hg
      · exact ih z hr
      · exact ⟨fun _ => colorAfter_mono_time adj other (Nat.zero_le t) (hguardOther hg),
          fun _ => colorAfter_mono_time adj blue (Nat.zero_le t) (hguardBlue hg)⟩
    change x ∈ synchronousStep adj (colorAfter adj blue t) ↔
      x ∈ synchronousStep adj (colorAfter adj other t)
    apply synchronousStep_agree_at_of_agree_near_sources adj _ _ x (ih x hx)
    intro s hs
    obtain ⟨hsource, hneighbor⟩ := hnear x hx s hs
    exact ⟨hagree s hsource, fun w hw => hagree w (hneighbor w hw)⟩

/-- Count only the white vertices of a guarded region of a cycle. -/
theorem cycle_guarded_region_finishesBy (n : ℕ)
    (region guards blue : Finset (Fin (n + 3))) (hguard : guards ⊆ blue)
    (hforcing : IsForcing (SimpleGraph.cycleGraph (n + 3)).Adj blue)
    (hnear : ∀ target ∈ region, ∀ source,
      (SimpleGraph.cycleGraph (n + 3)).Adj source target →
        (source ∈ region ∨ source ∈ guards) ∧
          ∀ w, (SimpleGraph.cycleGraph (n + 3)).Adj source w →
            w ∈ region ∨ w ∈ guards)
    (t : ℕ) (hcount : (region \ blue).card ≤ 2 * t) :
    region ⊆ colorAfter (SimpleGraph.cycleGraph (n + 3)).Adj blue t := by
  classical
  let adj := (SimpleGraph.cycleGraph (n + 3)).Adj
  let patched := blue ∪ (Finset.univ \ region)
  have hsub : blue ⊆ patched := Finset.subset_union_left
  have hforcePatched := IsForcing_mono adj hsub hforcing
  have hwhite : (Finset.univ \ patched) = region \ blue := by
    ext v
    simp [patched, and_comm]
  have hfin := cycle_finishesBy_of_white_card_le n patched hforcePatched t (by
    rwa [hwhite])
  change colorAfter adj patched t = Finset.univ at hfin
  have hsame := colorAfter_agree_on_with_guards adj region guards blue patched hguard
    (fun x hx => hsub (hguard hx))
    (by intro x hx; simp [patched, hx]) hnear t
  intro v hv
  apply (hsame v hv).mpr
  rw [hfin]
  exact Finset.mem_univ _

/-- A chain of initially white vertices with gaps at most two loses at most one
vertex from each end per round. The chain may cross vertex zero. -/
theorem cycle_white_chain_survives (n : ℕ) (blue : Finset (Fin (n + 3)))
    (m : ℕ) (white : ℕ → Fin (n + 3))
    (hwhite : ∀ i < m, white i ∉ blue)
    (hgap : ∀ i, i + 1 < m →
      white (i + 1) = white i + 1 ∨ white (i + 1) = (white i + 1) + 1)
    (t i : ℕ) (hleft : t ≤ i) (hright : i + t < m) :
    white i ∉ colorAfter (SimpleGraph.cycleGraph (n + 3)).Adj blue t := by
  let G := SimpleGraph.cycleGraph (n + 3)
  induction t generalizing i with
  | zero => exact hwhite i (by omega)
  | succ t ih =>
    have hcenter := ih i (by omega) (by omega)
    have hbefore := ih (i - 1) (by omega) (by omega)
    have hafter := ih (i + 1) (by omega) (by omega)
    have hback := hgap (i - 1) (by omega)
    rw [show i - 1 + 1 = i by omega] at hback
    have hforward := hgap i (by omega)
    intro hcolored
    rcases (mem_synchronousStep G.Adj _ (white i)).mp hcolored with hold |
      ⟨source, hsource, hadj, hunique⟩
    · exact hcenter hold
    · have hsourcePos := (cycle_adj_iff_neighbors n (white i) source).mp hadj.symm
      rcases hsourcePos with hsourcePos | hsourcePos
      · rcases hback with hgapOne | hgapTwo
        · have heq : source = white (i - 1) := by
            rw [hsourcePos, hgapOne, add_sub_cancel_right]
          exact hbefore (heq ▸ hsource)
        · have heq : white (i - 1) = source - 1 := by
            rw [hsourcePos, hgapTwo, add_sub_cancel_right, add_sub_cancel_right]
          have hadjPrev : G.Adj source (white (i - 1)) :=
            (cycle_adj_iff_neighbors n source _).mpr (Or.inl heq)
          have hforced := hunique _ hadjPrev hbefore
          have hi : source + 1 = white i := by rw [hsourcePos, sub_add_cancel]
          exact cycle_neighbors_distinct n source (heq.symm.trans (hforced.trans hi.symm))
      · rcases hforward with hgapOne | hgapTwo
        · exact hafter ((hsourcePos.trans hgapOne.symm) ▸ hsource)
        · have heq : white (i + 1) = source + 1 := by rw [hgapTwo, hsourcePos]
          have hadjNext : G.Adj source (white (i + 1)) :=
            (cycle_adj_iff_neighbors n source _).mpr (Or.inr heq)
          have hforced := hunique _ hadjNext hafter
          have hi : source - 1 = white i := by rw [hsourcePos, add_sub_cancel_right]
          exact cycle_neighbors_distinct n source (hi.trans (hforced.symm.trans heq))

theorem cycle_not_finishesBy_white_chain (n : ℕ) (blue : Finset (Fin (n + 3)))
    (m : ℕ) (white : ℕ → Fin (n + 3))
    (hwhite : ∀ i < m, white i ∉ blue)
    (hgap : ∀ i, i + 1 < m →
      white (i + 1) = white i + 1 ∨ white (i + 1) = (white i + 1) + 1)
    (t : ℕ) (ht : 2 * t < m) :
    ¬ FinishesBy (SimpleGraph.cycleGraph (n + 3)).Adj blue t := by
  intro hfin
  have hsurvivor := cycle_white_chain_survives n blue m white hwhite hgap t t le_rfl (by omega)
  apply hsurvivor
  rw [hfin]
  exact Finset.mem_univ _

private theorem cycle_val_add_one (n : ℕ) (v : Fin (n + 3))
    (h : v.val + 1 < n + 3) : (v + 1).val = v.val + 1 := by
  simp [Fin.val_add, Nat.mod_eq_of_lt h]

/-- Consecutive members of a blue-edge cover are separated by at most two steps. -/
theorem cycle_cover_sorted_consecutive (n : ℕ) (cover : Finset (Fin (n + 3)))
    (hc : HitsCycleEdges n Finset.univ cover) (i : ℕ) (hi : i + 1 < cover.card) :
    let e := cover.orderEmbOfFin (k := cover.card) rfl
    let a := e ⟨i, by omega⟩
    let b := e ⟨i + 1, hi⟩
    b = a + 1 ∨ b = (a + 1) + 1 := by
  let e := cover.orderEmbOfFin (k := cover.card) rfl
  let low : Fin cover.card := ⟨i, by omega⟩
  let high : Fin cover.card := ⟨i + 1, hi⟩
  let a := e low
  let b := e high
  change b = a + 1 ∨ b = (a + 1) + 1
  have hab : a.val < b.val := e.strictMono (show low < high from Nat.lt_succ_self i)
  have hnone (v : Fin (n + 3)) (hl : a < v) (hr : v < b) : v ∉ cover := by
    intro hv
    have hmem : v ∈ Set.range e := by
      rw [Finset.range_orderEmbOfFin]
      exact hv
    obtain ⟨j, rfl⟩ := hmem
    have hlow : low < j := e.lt_iff_lt.mp hl
    have hhigh : j < high := e.lt_iff_lt.mp hr
    change i < j.val at hlow
    change j.val < i + 1 at hhigh
    omega
  have hgap : b.val ≤ a.val + 2 := by
    by_contra h
    have hL : a.val + 1 < n + 3 := by have := b.isLt; omega
    have v1 := cycle_val_add_one n a hL
    have v2 := cycle_val_add_one n (a + 1) (by rw [v1]; have := b.isLt; omega)
    have h1 : a + 1 ∉ cover := hnone _ (by change a.val < (a + 1).val; omega)
      (by change (a + 1).val < b.val; omega)
    have h2 : (a + 1) + 1 ∉ cover := hnone _
      (by change a.val < ((a + 1) + 1).val; omega)
      (by change ((a + 1) + 1).val < b.val; omega)
    have hAdj : (SimpleGraph.cycleGraph (n + 3)).Adj (a + 1) ((a + 1) + 1) :=
      (cycle_adj_iff_neighbors n _ _).mpr (Or.inr rfl)
    exact (hc _ (Finset.mem_univ _) _ (Finset.mem_univ _) hAdj).elim h1 h2
  have h1 := cycle_val_add_one n a (by have := b.isLt; omega)
  by_cases hb : b.val = a.val + 1
  · exact Or.inl (Fin.ext (hb.trans h1.symm))
  · have h2 := cycle_val_add_one n (a + 1) (by rw [h1]; have := b.isLt; omega)
    exact Or.inr (Fin.ext (by omega))

/-- Below the killing threshold, restricted all-blue losses need at least k/2 rounds. -/
theorem cycle_full_blue_restricted_deadline_lower (n : ℕ)
    (support : Finset (Fin (n + 3)))
    (hminimum : IsMinimumKilling (SimpleGraph.cycleGraph (n + 3)).Adj Finset.univ support)
    (budget deadline : ℕ) (hsmall : budget < support.card)
    (hrobust : RobustBy (SimpleGraph.cycleGraph (n + 3)).Adj Finset.univ
      support budget deadline) :
    budget ≤ 2 * deadline := by
  classical
  let white (i : ℕ) : Fin (n + 3) :=
    if h : i < support.card then support.orderEmbOfFin rfl ⟨i, h⟩ else 0
  let loss := (Finset.range budget).image white
  have hsub : loss ⊆ support := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    have hi' : i < budget := Finset.mem_range.mp hi
    simp [white, lt_trans hi' hsmall]
  have hsize : loss.card ≤ budget :=
    (Finset.card_image_le).trans (by rw [Finset.card_range])
  have hfin := hrobust loss hsub hsize
  by_contra ht
  have hc : HitsCycleEdges n Finset.univ support :=
    (cycle_nonforcing_sdiff_iff_hits_edges n Finset.univ support).mp hminimum.2.1
  have hwhite : ∀ i < budget, white i ∉ (Finset.univ \ loss) := by
    intro i hi hw
    exact (Finset.mem_sdiff.mp hw).2 (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hi))
  have hgap : ∀ i, i + 1 < budget →
      white (i + 1) = white i + 1 ∨ white (i + 1) = (white i + 1) + 1 := by
    intro i hi
    have hi' : i + 1 < support.card := lt_trans hi hsmall
    simpa [white, hi', (show i < support.card by omega)] using
      cycle_cover_sorted_consecutive n support hc i hi'
  exact cycle_not_finishesBy_white_chain n (Finset.univ \ loss) budget white
    hwhite hgap deadline (by omega) hfin

/-- The entire restricted and unrestricted deadline profiles agree for all-blue cycles. -/
theorem cycle_full_blue_support (n : ℕ) (support : Finset (Fin (n + 3)))
    (hminimum : IsMinimumKilling (SimpleGraph.cycleGraph (n + 3)).Adj Finset.univ support)
    (budget deadline : ℕ) :
    RobustBy (SimpleGraph.cycleGraph (n + 3)).Adj Finset.univ Finset.univ budget deadline ↔
      RobustBy (SimpleGraph.cycleGraph (n + 3)).Adj Finset.univ support budget deadline := by
  constructor
  · intro h loss hsub hsize
    exact h loss (Finset.subset_univ _) hsize
  · intro h
    have hk : budget < support.card := by
      by_contra hn
      exact hminimum.2.1 ⟨deadline, h support (fun _ hp => hp) (by omega)⟩
    exact cycle_full_blue_robust_upper n support hminimum budget deadline hk
      (cycle_full_blue_restricted_deadline_lower n support hminimum budget deadline hk h)

/-- A cut at an initially white vertex turns every blue edge into a path edge. -/
theorem cycle_blue_adj_val_succ (n : ℕ) (blue : Finset (Fin (n + 3)))
    (hcut : 0 ∉ blue) (u v : Fin (n + 3)) (hu : u ∈ blue) (hv : v ∈ blue)
    (hadj : (SimpleGraph.cycleGraph (n + 3)).Adj u v) :
    u.val + 1 = v.val ∨ v.val + 1 = u.val := by
  have hu0 : u ≠ 0 := fun he => hcut (he ▸ hu)
  have hv0 : v ≠ 0 := fun he => hcut (he ▸ hv)
  rcases (cycle_adj_iff_neighbors n u v).mp hadj with h | h
  · have hval := Fin.val_sub_one_of_ne_zero hu0
    have hne : u.val ≠ 0 := fun he => hu0 (Fin.ext he)
    right
    rw [h, hval]
    omega
  · have hnoWrap : u.val + 1 < n + 3 := by
      by_contra hn
      have hval : u.val + 1 = n + 3 := by have := u.isLt; omega
      apply hv0
      apply Fin.ext
      rw [h]
      simp [Fin.val_add, hval]
    left
    rw [h, cycle_val_add_one n u hnoWrap]

/-- On a cycle cut at a white vertex, every minimum killing set selects exactly
one vertex from each pair in the ordered greedy packing. -/
theorem cycle_exists_pair_packing_selector_at_white_zero (n : ℕ)
    (blue support : Finset (Fin (n + 3))) (hcut : 0 ∉ blue)
    (hminimum : IsMinimumKilling (SimpleGraph.cycleGraph (n + 3)).Adj blue support) :
    ∃ units : List (Finset (Fin (n + 3))), ∃ cover : Finset (Fin (n + 3)),
      ∃ pick : Fin units.length → Fin (n + 3),
        PathPairCoverPacking (n + 2) blue units cover ∧
          HitsCycleEdges n blue cover ∧ ExactCellSelection (PathIndexedCell units) support pick := by
  classical
  obtain ⟨units, cover, hpack⟩ := exists_path_pair_cover_packing (n + 2) blue
  have hcover : HitsCycleEdges n blue cover := by
    intro u hu v hv hadj
    rcases cycle_blue_adj_val_succ n blue hcut u v hu hv hadj with h | h
    · exact hpack.covers u hu v hv h
    · exact (hpack.covers v hv u hu h).symm
  have hdis : DisjointForcingCells (PathIndexedCell (n := n + 2) units) := by
    intro i j hne
    have hvalNe : i.val ≠ j.val := fun h => hne (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hvalNe with hij | hji
    · exact pathCellBefore_disjoint (n + 2) _ _
        (List.Pairwise.rel_getElem_of_lt i.isLt j.isLt hpack.ordered hij)
    · exact (pathCellBefore_disjoint (n + 2) _ _
        (List.Pairwise.rel_getElem_of_lt j.isLt i.isLt hpack.ordered hji)).symm
  obtain ⟨pick, hpick⟩ := minimumKilling_exact_cell_selector _ blue support cover
    (PathIndexedCell (n := n + 2) units) hdis
    (fun i => pathPairCoverPacking_cell_subset (n + 2) blue units cover hpack _
      (List.getElem_mem i.isLt))
    (by
      intro i
      obtain ⟨u, _, v, _, huv, heq⟩ := hpack.pairs _ (List.getElem_mem i.isLt)
      change IsForcing (SimpleGraph.cycleGraph (n + 3)).Adj units[i.val]
      rw [heq, cycle_forcing_iff_adjacent_pair]
      exact ⟨u, by simp, v, by simp,
        SimpleGraph.pathGraph_le_cycleGraph (SimpleGraph.pathGraph_adj.mpr (Or.inl huv))⟩)
    hminimum hpack.cover_subset
    ((cycle_nonforcing_sdiff_iff_hits_edges n blue cover).mpr hcover)
    (by simpa only [Fintype.card_fin] using hpack.card_eq)
  exact ⟨units, cover, pick, hpack, hcover, hpick⟩

/-- The remaining cycle time theorem can be proved with vertex zero initially white. -/
theorem cycle_everyMinimumSupport_iff_white_zero (n : ℕ) :
    EveryMinimumSupport (SimpleGraph.cycleGraph (n + 3)).Adj ↔
      ∀ blue : Finset (Fin (n + 3)), 0 ∉ blue →
        IsForcing (SimpleGraph.cycleGraph (n + 3)).Adj blue →
        ∀ support : Finset (Fin (n + 3)),
          IsMinimumKilling (SimpleGraph.cycleGraph (n + 3)).Adj blue support →
          ∀ budget deadline : ℕ,
            (RobustBy (SimpleGraph.cycleGraph (n + 3)).Adj blue blue budget deadline ↔
              RobustBy (SimpleGraph.cycleGraph (n + 3)).Adj blue support budget deadline) := by
  classical
  constructor
  · intro h blue _ hforcing support hminimum budget deadline
    exact h blue hforcing support hminimum budget deadline
  · intro h blue hforcing support hminimum budget deadline
    by_cases hfull : blue = Finset.univ
    · subst blue
      exact cycle_full_blue_support n support hminimum budget deadline
    · obtain ⟨a, ha⟩ : ∃ a : Fin (n + 3), a ∉ blue := by
        by_contra hn
        apply hfull
        exact Finset.eq_univ_of_forall (fun a => by_contra fun hmem => hn ⟨a, hmem⟩)
      let e := (cycleRotation n a).symm
      let adj := (SimpleGraph.cycleGraph (n + 3)).Adj
      have hadj (x y) : adj (e x) (e y) ↔ adj x y := cycle_rotation_symm_adj n a x y
      have hcut : 0 ∉ relabelColors e blue := by
        simpa [e, cycleRotation] using ha
      have hforcing' := (IsForcing_relabel_iff e adj adj hadj blue).mpr hforcing
      have hminimum' := (IsMinimumKilling_relabel_iff e adj adj hadj blue support).mpr hminimum
      have hnormalized :=
        h (relabelColors e blue) hcut hforcing' (relabelColors e support) hminimum' budget deadline
      exact (RobustBy_relabel_iff e adj adj hadj blue blue budget deadline).symm.trans
        (hnormalized.trans (RobustBy_relabel_iff e adj adj hadj blue support budget deadline))

#print axioms cycle_forcing_iff_adjacent_pair
#print axioms cycle_nonforcing_sdiff_iff_hits_edges
#print axioms cycle_minimum_killing_iff_minimum_vertex_cover
#print axioms cycle_step_white_card_le_of_zero_one
#print axioms cycle_finishesBy_of_white_card_le
#print axioms cycle_full_blue_robust_upper
#print axioms cycle_guarded_region_finishesBy
#print axioms cycle_not_finishesBy_white_chain
#print axioms cycle_full_blue_support
#print axioms cycle_exists_pair_packing_selector_at_white_zero
#print axioms cycle_everyMinimumSupport_iff_white_zero

end FaultObservationResearch
