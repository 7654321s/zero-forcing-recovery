module

/-
General path forcing tools, with no upper bound on path order.
The endpoint/adjacent-pair criterion is prior mathematics. These tools support
the pending path time-support proof and do not prove that time theorem.
-/
public import «formalization-rooted-leaves»
public import «formalization-tree-target»
public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace FaultObservationResearch

universe u

theorem force_target_mem_of_fixed {V : Type u} [Fintype V] [DecidableEq V]
    (adj : V → V → Prop) (blue : Finset V) (hfixed : synchronousStep adj blue = blue)
    (source target : V) (hs : source ∈ blue) (ha : adj source target)
    (hu : ∀ other : V, adj source other → other ∉ blue → other = target) : target ∈ blue := by
  have hm : target ∈ synchronousStep adj blue :=
    (mem_synchronousStep adj blue target).mpr (Or.inr ⟨source, hs, ha, hu⟩)
  rwa [hfixed] at hm

def pathReverseEquiv (n : ℕ) : Fin (n + 1) ≃ Fin (n + 1) where
  toFun := Fin.rev
  invFun := Fin.rev
  left_inv := by
    intro i
    apply Fin.ext
    simp only [Fin.val_rev]
    have := i.isLt
    omega
  right_inv := by
    intro i
    apply Fin.ext
    simp only [Fin.val_rev]
    have := i.isLt
    omega

def pathReverseIso (n : ℕ) : SimpleGraph.pathGraph (n + 1) ≃g SimpleGraph.pathGraph (n + 1) where
  toEquiv := pathReverseEquiv n
  map_rel_iff' := by
    intro i j
    change (SimpleGraph.pathGraph (n + 1)).Adj (Fin.rev i) (Fin.rev j) ↔
      (SimpleGraph.pathGraph (n + 1)).Adj i j
    rw [SimpleGraph.pathGraph_adj, SimpleGraph.pathGraph_adj]
    simp only [Fin.val_rev]
    have := i.isLt
    have := j.isLt
    omega

theorem pathReverseEquiv_symm_zero (n : ℕ) :
    (pathReverseEquiv n).symm (0 : Fin (n + 1)) = Fin.last n := by
  apply Fin.ext
  change (n + 1) - (0 + 1) = n
  omega

theorem path_fixed_of_zero (n : ℕ) (blue : Finset (Fin (n + 1)))
    (hfixed : synchronousStep (SimpleGraph.pathGraph (n + 1)).Adj blue = blue)
    (hzero : (0 : Fin (n + 1)) ∈ blue) : blue = Finset.univ := by
  classical
  have all : ∀ m : ℕ, ∀ hm : m < n + 1, (⟨m, hm⟩ : Fin (n + 1)) ∈ blue := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm
      by_cases hm0 : m = 0
      · subst m
        exact hzero
      · let source : Fin (n + 1) := ⟨m - 1, by omega⟩
        have hs : source ∈ blue := ih (m - 1) (by omega) source.isLt
        apply force_target_mem_of_fixed (SimpleGraph.pathGraph (n + 1)).Adj blue hfixed
          source ⟨m, hm⟩ hs
        · apply SimpleGraph.pathGraph_adj.mpr
          left
          change m - 1 + 1 = m
          omega
        · intro other ha hw
          rcases SimpleGraph.pathGraph_adj.mp ha with hright | hleft
          · apply Fin.ext
            change m - 1 + 1 = other.val at hright
            change other.val = m
            omega
          · have hlt : other.val < m := by
              change other.val + 1 = m - 1 at hleft
              omega
            exact False.elim (hw (ih other.val hlt other.isLt))
  apply Finset.eq_univ_of_forall
  intro i
  exact all i.val i.isLt

theorem path_fixed_of_last (n : ℕ) (blue : Finset (Fin (n + 1)))
    (hfixed : synchronousStep (SimpleGraph.pathGraph (n + 1)).Adj blue = blue)
    (hlast : Fin.last n ∈ blue) : blue = Finset.univ := by
  classical
  let e := pathReverseEquiv n
  let adj := (SimpleGraph.pathGraph (n + 1)).Adj
  have hadj : ∀ x y : Fin (n + 1), adj (e x) (e y) ↔ adj x y :=
    fun _ _ => (pathReverseIso n).map_rel_iff
  have hmapfixed : synchronousStep adj (relabelColors e blue) = relabelColors e blue := by
    rw [← synchronousStep_relabel e adj adj hadj blue, hfixed]
  have hmapzero : (0 : Fin (n + 1)) ∈ relabelColors e blue := by
    apply (mem_relabelColors e blue 0).mpr
    change (pathReverseEquiv n).symm 0 ∈ blue
    rw [pathReverseEquiv_symm_zero]
    exact hlast
  have hfull := path_fixed_of_zero n (relabelColors e blue) hmapfixed hmapzero
  apply Finset.eq_univ_of_forall
  intro i
  have hm : e i ∈ relabelColors e blue := by rw [hfull]; exact Finset.mem_univ _
  have hback := (mem_relabelColors e blue (e i)).mp hm
  simpa only [Equiv.symm_apply_apply] using hback

theorem path_fixed_of_pair (n : ℕ) (blue : Finset (Fin (n + 1)))
    (hfixed : synchronousStep (SimpleGraph.pathGraph (n + 1)).Adj blue = blue)
    (i j : Fin (n + 1)) (hi : i ∈ blue) (hj : j ∈ blue) (hij : i.val + 1 = j.val) :
    blue = Finset.univ := by
  classical
  have right : ∀ m : ℕ, j.val ≤ m → ∀ hm : m < n + 1,
      (⟨m, hm⟩ : Fin (n + 1)) ∈ blue := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hjm hm
      by_cases heq : m = j.val
      · have heqFin : (⟨m, hm⟩ : Fin (n + 1)) = j := Fin.ext heq
        rwa [heqFin]
      · let source : Fin (n + 1) := ⟨m - 1, by omega⟩
        have hs : source ∈ blue := ih (m - 1) (by omega) (by omega) source.isLt
        apply force_target_mem_of_fixed (SimpleGraph.pathGraph (n + 1)).Adj blue hfixed
          source ⟨m, hm⟩ hs
        · apply SimpleGraph.pathGraph_adj.mpr
          left
          change m - 1 + 1 = m
          omega
        · intro other ha hw
          rcases SimpleGraph.pathGraph_adj.mp ha with hright | hleft
          · apply Fin.ext
            change m - 1 + 1 = other.val at hright
            change other.val = m
            omega
          · have hlt : other.val < m := by
              change other.val + 1 = m - 1 at hleft
              omega
            by_cases hbefore : other.val < j.val
            · have heqFin : other = i := by
                apply Fin.ext
                change other.val + 1 = m - 1 at hleft
                omega
              exact False.elim (hw (by rwa [heqFin]))
            · exact False.elim (hw (ih other.val hlt (by omega) other.isLt))
  apply path_fixed_of_last n blue hfixed
  exact right n (by have := j.isLt; omega) (Nat.lt_succ_self n)

def HasPathSeed (n : ℕ) (blue : Finset (Fin (n + 1))) : Prop :=
  (0 : Fin (n + 1)) ∈ blue ∨ Fin.last n ∈ blue ∨
    ∃ i j : Fin (n + 1), i ∈ blue ∧ j ∈ blue ∧ i.val + 1 = j.val

theorem hasPathSeed_mono (n : ℕ) {A B : Finset (Fin (n + 1))}
    (hAB : A ⊆ B) (hA : HasPathSeed n A) : HasPathSeed n B := by
  rcases hA with hz | hl | ⟨i, j, hi, hj, hij⟩
  · exact Or.inl (hAB hz)
  · exact Or.inr (Or.inl (hAB hl))
  · exact Or.inr (Or.inr ⟨i, j, hAB hi, hAB hj, hij⟩)

theorem path_forcing_of_seed (n : ℕ) (blue : Finset (Fin (n + 1)))
    (hseed : HasPathSeed n blue) : IsForcing (SimpleGraph.pathGraph (n + 1)).Adj blue := by
  classical
  let adj := (SimpleGraph.pathGraph (n + 1)).Adj
  let C := colorAfter adj blue (n + 1)
  have hfixed : synchronousStep adj C = C := by
    simpa only [Fintype.card_fin, C, colorAfter] using colorAfter_stabilizes_card adj blue
  have hC : HasPathSeed n C := hasPathSeed_mono n
    (colorAfter_mono_time adj blue (Nat.zero_le (n + 1))) hseed
  have hfull : C = Finset.univ := by
    rcases hC with hz | hl | ⟨i, j, hi, hj, hij⟩
    · exact path_fixed_of_zero n C hfixed hz
    · exact path_fixed_of_last n C hfixed hl
    · exact path_fixed_of_pair n C hfixed i j hi hj hij
  exact ⟨n + 1, hfull⟩

theorem path_no_seed_step_eq (n : ℕ) (blue : Finset (Fin (n + 1)))
    (hseed : ¬ HasPathSeed n blue) :
    synchronousStep (SimpleGraph.pathGraph (n + 1)).Adj blue = blue := by
  classical
  have hz : (0 : Fin (n + 1)) ∉ blue := fun h => hseed (Or.inl h)
  have hl : Fin.last n ∉ blue := fun h => hseed (Or.inr (Or.inl h))
  have hp : ∀ i j : Fin (n + 1), i ∈ blue → j ∈ blue → i.val + 1 ≠ j.val := by
    intro i j hi hj hij
    exact hseed (Or.inr (Or.inr ⟨i, j, hi, hj, hij⟩))
  apply le_antisymm
  · intro target ht
    rcases (mem_synchronousStep _ _ _).mp ht with hold | ⟨source, hs, _, hu⟩
    · exact hold
    · have hs0 : source.val ≠ 0 := by
        intro h
        have heq : source = 0 := Fin.ext h
        exact hz (by rwa [← heq])
      have hsn : source.val ≠ n := by
        intro h
        have heq : source = Fin.last n := Fin.ext h
        exact hl (by rwa [← heq])
      let left : Fin (n + 1) := ⟨source.val - 1, by have := source.isLt; omega⟩
      let right : Fin (n + 1) := ⟨source.val + 1, by have := source.isLt; omega⟩
      have hleft : left.val + 1 = source.val := by dsimp [left]; omega
      have hlwhite : left ∉ blue := fun h => hp left source h hs hleft
      have hrwhite : right ∉ blue := fun h => hp source right hs h rfl
      have heqL := hu left (SimpleGraph.pathGraph_adj.mpr (Or.inr hleft)) hlwhite
      have heqR := hu right (SimpleGraph.pathGraph_adj.mpr (Or.inl rfl)) hrwhite
      have hv := congrArg Fin.val (heqL.trans heqR.symm)
      change source.val - 1 = source.val + 1 at hv
      omega
  · exact subset_synchronousStep _ _

theorem path_no_seed_not_forcing (n : ℕ) (blue : Finset (Fin (n + 1)))
    (hseed : ¬ HasPathSeed n blue) : ¬ IsForcing (SimpleGraph.pathGraph (n + 1)).Adj blue := by
  intro hf
  have hfull := FinishesBy_of_stable (SimpleGraph.pathGraph (n + 1)).Adj blue hf 0
    (path_no_seed_step_eq n blue hseed)
  change blue = Finset.univ at hfull
  apply hseed
  exact Or.inl (by rw [hfull]; exact Finset.mem_univ _)

theorem path_forcing_iff_seed (n : ℕ) (blue : Finset (Fin (n + 1))) :
    IsForcing (SimpleGraph.pathGraph (n + 1)).Adj blue ↔ HasPathSeed n blue := by
  classical
  constructor
  · intro hf
    by_contra hseed
    exact path_no_seed_not_forcing n blue hseed hf
  · exact path_forcing_of_seed n blue

def HitsPathSeeds (n : ℕ) (blue loss : Finset (Fin (n + 1))) : Prop :=
  ((0 : Fin (n + 1)) ∈ blue → (0 : Fin (n + 1)) ∈ loss) ∧
  (Fin.last n ∈ blue → Fin.last n ∈ loss) ∧
  ∀ i j : Fin (n + 1), i ∈ blue → j ∈ blue → i.val + 1 = j.val → i ∈ loss ∨ j ∈ loss

theorem path_nonforcing_sdiff_iff_hits_seeds (n : ℕ) (blue loss : Finset (Fin (n + 1))) :
    ¬ IsForcing (SimpleGraph.pathGraph (n + 1)).Adj (blue \ loss) ↔
      HitsPathSeeds n blue loss := by
  classical
  rw [path_forcing_iff_seed]
  unfold HitsPathSeeds
  constructor
  · intro hno
    refine ⟨?_, ?_, ?_⟩
    · intro hz
      by_contra hnot
      exact hno (Or.inl (Finset.mem_sdiff.mpr ⟨hz, hnot⟩))
    · intro hl
      by_contra hnot
      exact hno (Or.inr (Or.inl (Finset.mem_sdiff.mpr ⟨hl, hnot⟩)))
    · intro i j hi hj hij
      by_contra hnot
      have hiL : i ∉ loss := fun h => hnot (Or.inl h)
      have hjL : j ∉ loss := fun h => hnot (Or.inr h)
      exact hno (Or.inr (Or.inr ⟨i, j,
        Finset.mem_sdiff.mpr ⟨hi, hiL⟩, Finset.mem_sdiff.mpr ⟨hj, hjL⟩, hij⟩))
  · rintro ⟨hz, hl, hp⟩ hseed
    rcases hseed with hzero | hlast | ⟨i, j, hi, hj, hij⟩
    · exact (Finset.mem_sdiff.mp hzero).2 (hz (Finset.mem_sdiff.mp hzero).1)
    · exact (Finset.mem_sdiff.mp hlast).2 (hl (Finset.mem_sdiff.mp hlast).1)
    · have hhit := hp i j (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1 hij
      exact hhit.elim (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).2

theorem path_minimum_killing_iff_minimum_seed_hit (n : ℕ)
    (blue support : Finset (Fin (n + 1))) :
    IsMinimumKilling (SimpleGraph.pathGraph (n + 1)).Adj blue support ↔
      support ⊆ blue ∧ HitsPathSeeds n blue support ∧
        ∀ loss : Finset (Fin (n + 1)), loss ⊆ blue → HitsPathSeeds n blue loss →
          support.card ≤ loss.card := by
  rw [IsMinimumKilling_iff_card_minimum]
  simp only [path_nonforcing_sdiff_iff_hits_seeds]

theorem robustBy_iff_of_minimum_card_le_one {V : Type u} [Fintype V] [DecidableEq V]
    (adj : V → V → Prop) (blue support : Finset V)
    (hminimum : IsMinimumKilling adj blue support) (hcard : support.card ≤ 1)
    (budget deadline : ℕ) :
    RobustBy adj blue blue budget deadline ↔ RobustBy adj blue support budget deadline := by
  constructor
  · intro h loss hs hc
    exact h loss (fun _ hx => hminimum.1 (hs hx)) hc
  · intro h
    by_cases hzero : budget = 0
    · subst budget
      exact (robustBy_zero_iff adj blue blue deadline).mpr
        ((robustBy_zero_iff adj blue support deadline).mp h)
    · have hlarge : support.card ≤ budget := by omega
      exact False.elim (hminimum.2.1 ⟨deadline, h support (fun _ hx => hx) hlarge⟩)

theorem everyMinimumSupport_of_card_le_two {V : Type u} [Fintype V] [DecidableEq V]
    (adj : V → V → Prop) (hcard : Fintype.card V ≤ 2) : EveryMinimumSupport adj := by
  classical
  intro blue _ support hminimum budget deadline
  by_cases hsmall : support.card ≤ 1
  · exact robustBy_iff_of_minimum_card_le_one adj blue support hminimum hsmall budget deadline
  · have hB : blue.card ≤ 2 := by
      have hN : blue.card ≤ Fintype.card V := by
        simpa only [Finset.card_univ] using Finset.card_le_card (Finset.subset_univ blue)
      exact Nat.le_trans hN hcard
    have hH : support.card ≤ blue.card := Finset.card_le_card hminimum.1
    have heq : support = blue := Finset.eq_of_subset_of_card_le hminimum.1 (by omega)
    subst support
    rfl

theorem path_small_support (n : ℕ) (hn : n ≤ 2) :
    EveryMinimumSupport (SimpleGraph.pathGraph n).Adj :=
  everyMinimumSupport_of_card_le_two _ (by simpa only [Fintype.card_fin] using hn)

theorem IsForcing_finishes_unblue {V : Type u} [Fintype V] [DecidableEq V]
    (adj : V → V → Prop) (blue : Finset V) (hforcing : IsForcing adj blue) :
    FinishesBy adj blue (Fintype.card V - blue.card) := by
  classical
  let w := Fintype.card V - blue.card
  by_contra hnot
  have hstrict : ∀ t : ℕ, t ≤ w →
      (colorAfter adj blue t).card < (colorAfter adj blue (t + 1)).card := by
    intro t htw
    apply card_colorAfter_strict_of_unfinished adj blue hforcing t
    intro hdone
    exact hnot (FinishesBy_mono_time adj blue hdone htw)
  have lower : ∀ t : ℕ, t ≤ w + 1 → blue.card + t ≤ (colorAfter adj blue t).card := by
    intro t
    induction t with
    | zero => intro _; simp only [colorAfter, Nat.add_zero]; exact Nat.le_refl _
    | succ t ih =>
      intro ht
      have htw : t ≤ w := Nat.le_of_succ_le_succ ht
      have hp := ih (Nat.le_trans htw (Nat.le_succ w))
      have hg := hstrict t htw
      omega
  have hB : blue.card ≤ Fintype.card V := by
    simpa only [Finset.card_univ] using Finset.card_le_card (Finset.subset_univ blue)
  have hsum : blue.card + w = Fintype.card V := by dsimp [w]; omega
  have hlow := lower (w + 1) (Nat.le_refl _)
  have hupp : (colorAfter adj blue (w + 1)).card ≤ Fintype.card V := by
    simpa only [Finset.card_univ] using
      Finset.card_le_card (Finset.subset_univ (colorAfter adj blue (w + 1)))
  omega

theorem full_blue_loss_finishes_card {V : Type u} [Fintype V] [DecidableEq V]
    (adj : V → V → Prop) (loss : Finset V)
    (hforcing : IsForcing adj (Finset.univ \ loss)) :
    FinishesBy adj (Finset.univ \ loss) loss.card := by
  classical
  have hsplit : (Finset.univ \ loss).card + loss.card = Fintype.card V := by
    simpa only [Finset.card_univ] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ loss)
  have heq : Fintype.card V - (Finset.univ \ loss).card = loss.card := by omega
  simpa only [heq] using IsForcing_finishes_unblue adj (Finset.univ \ loss) hforcing

theorem full_blue_robust_by_budget {V : Type u} [Fintype V] [DecidableEq V]
    (adj : V → V → Prop) (support : Finset V)
    (hminimum : IsMinimumKilling adj Finset.univ support) (budget : ℕ)
    (hbudget : budget < support.card) : RobustBy adj Finset.univ Finset.univ budget budget := by
  intro loss hs hc
  have hf := hminimum.2.2 loss hs (Nat.lt_of_le_of_lt hc hbudget)
  exact FinishesBy_mono_time adj (Finset.univ \ loss)
    (full_blue_loss_finishes_card adj loss hf) hc

end FaultObservationResearch
