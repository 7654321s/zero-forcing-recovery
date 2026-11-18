module

/-
Computable finite verification of the original support property.
The equivalence below preserves all budgets and deadlines. A certificate for
one graph is only a proof for that graph, not a general tree classification.
-/
public import «formalization-foundations»
public import Mathlib.Data.Fintype.Powerset
public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 8192

namespace FaultObservationResearch

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

def computedSynchronousStep (adj : V → V → Prop) [DecidableRel adj]
    (blue : Finset V) : Finset V :=
  blue ∪ Finset.univ.filter (fun target =>
    ∃ source ∈ blue, adj source target ∧
      ∀ other, adj source other → other ∉ blue → other = target)

def computedColorAfter (adj : V → V → Prop) [DecidableRel adj]
    (blue : Finset V) : ℕ → Finset V
  | 0 => blue
  | t + 1 => computedSynchronousStep adj (computedColorAfter adj blue t)

def computedFinishesBy (adj : V → V → Prop) [DecidableRel adj]
    (blue : Finset V) (deadline : ℕ) : Prop :=
  computedColorAfter adj blue deadline = Finset.univ

instance decidableComputedFinishesBy (adj : V → V → Prop) [DecidableRel adj]
    (blue : Finset V) (deadline : ℕ) : Decidable (computedFinishesBy adj blue deadline) :=
  inferInstanceAs (Decidable (computedColorAfter adj blue deadline = Finset.univ))

def computedMinimumKilling (adj : V → V → Prop) [DecidableRel adj]
    (blue support : Finset V) : Prop :=
  support ⊆ blue ∧ ¬ computedFinishesBy adj (blue \ support) (Fintype.card V) ∧
    ∀ loss : Finset V, loss ⊆ blue → loss.card < support.card →
      computedFinishesBy adj (blue \ loss) (Fintype.card V)

instance decidableComputedMinimumKilling (adj : V → V → Prop) [DecidableRel adj]
    (blue support : Finset V) : Decidable (computedMinimumKilling adj blue support) := by
  unfold computedMinimumKilling
  infer_instance

def computedRobustBy (adj : V → V → Prop) [DecidableRel adj]
    (blue allowed : Finset V) (budget deadline : ℕ) : Prop :=
  ∀ loss : Finset V, loss ⊆ allowed → loss.card ≤ budget →
    computedFinishesBy adj (blue \ loss) deadline

instance decidableComputedRobustBy (adj : V → V → Prop) [DecidableRel adj]
    (blue allowed : Finset V) (budget deadline : ℕ) :
    Decidable (computedRobustBy adj blue allowed budget deadline) := by
  unfold computedRobustBy
  infer_instance

def computedEveryMinimumSupport (adj : V → V → Prop) [DecidableRel adj] : Prop :=
  ∀ blue support : Finset V,
    computedFinishesBy adj blue (Fintype.card V) →
    computedMinimumKilling adj blue support →
      ∀ budget : Fin support.card, ∀ deadline : Fin (Fintype.card V + 1),
        (computedRobustBy adj blue blue budget.val deadline.val ↔
          computedRobustBy adj blue support budget.val deadline.val)

instance decidableComputedEveryMinimumSupport (adj : V → V → Prop) [DecidableRel adj] :
    Decidable (computedEveryMinimumSupport adj) := by
  unfold computedEveryMinimumSupport
  infer_instance

theorem computedSynchronousStep_eq (adj : V → V → Prop) [DecidableRel adj]
    (blue : Finset V) : computedSynchronousStep adj blue = synchronousStep adj blue := by
  classical
  ext x
  simp [computedSynchronousStep, synchronousStep]

theorem computedColorAfter_eq (adj : V → V → Prop) [DecidableRel adj]
    (blue : Finset V) (t : ℕ) : computedColorAfter adj blue t = colorAfter adj blue t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change computedSynchronousStep adj (computedColorAfter adj blue t) =
      synchronousStep adj (colorAfter adj blue t)
    rw [ih, computedSynchronousStep_eq]

theorem computedFinishesBy_iff (adj : V → V → Prop) [DecidableRel adj]
    (blue : Finset V) (t : ℕ) : computedFinishesBy adj blue t ↔ FinishesBy adj blue t := by
  unfold computedFinishesBy FinishesBy
  rw [computedColorAfter_eq]

theorem computedMinimumKilling_iff (adj : V → V → Prop) [DecidableRel adj]
    (blue support : Finset V) :
    computedMinimumKilling adj blue support ↔ IsMinimumKilling adj blue support := by
  simp only [computedMinimumKilling, IsMinimumKilling, IsForcing_iff_card_deadline,
    computedFinishesBy_iff]

theorem computedRobustBy_iff (adj : V → V → Prop) [DecidableRel adj]
    (blue allowed : Finset V) (budget deadline : ℕ) :
    computedRobustBy adj blue allowed budget deadline ↔ RobustBy adj blue allowed budget deadline := by
  simp only [computedRobustBy, RobustBy, computedFinishesBy_iff]

theorem FinishesBy_min_card_iff (adj : V → V → Prop) (blue : Finset V) (t : ℕ) :
    FinishesBy adj blue (min t (Fintype.card V)) ↔ FinishesBy adj blue t := by
  constructor
  · intro h
    exact FinishesBy_mono_time adj blue h (min_le_left _ _)
  · intro h
    by_cases ht : t ≤ Fintype.card V
    · simpa only [Nat.min_eq_left ht] using h
    · have hn := IsForcing_finishes_card adj blue ⟨t, h⟩
      simpa only [Nat.min_eq_right (Nat.le_of_not_ge ht)] using hn

theorem RobustBy_min_card_deadline_iff (adj : V → V → Prop)
    (blue allowed : Finset V) (budget deadline : ℕ) :
    RobustBy adj blue allowed budget (min deadline (Fintype.card V)) ↔
      RobustBy adj blue allowed budget deadline := by
  constructor
  · intro h loss hs hc
    exact (FinishesBy_min_card_iff adj (blue \ loss) deadline).mp (h loss hs hc)
  · intro h loss hs hc
    exact (FinishesBy_min_card_iff adj (blue \ loss) deadline).mpr (h loss hs hc)

theorem computedEveryMinimumSupport_iff (adj : V → V → Prop) [DecidableRel adj] :
    computedEveryMinimumSupport adj ↔ EveryMinimumSupport adj := by
  classical
  constructor
  · intro h blue hforcing support hminimum budget deadline
    by_cases hlarge : support.card ≤ budget
    · constructor
      · intro hg
        exact False.elim (hminimum.2.1 ⟨deadline, hg support hminimum.1 hlarge⟩)
      · intro hr
        exact False.elim (hminimum.2.1 ⟨deadline, hr support (fun _ hx => hx) hlarge⟩)
    · let k : Fin support.card := ⟨budget, Nat.lt_of_not_ge hlarge⟩
      let d : Fin (Fintype.card V + 1) :=
        ⟨min deadline (Fintype.card V), Nat.lt_succ_of_le (min_le_right _ _)⟩
      have hc := h blue support
        ((computedFinishesBy_iff adj blue _).mpr (IsForcing_finishes_card adj blue hforcing))
        ((computedMinimumKilling_iff adj blue support).mpr hminimum) k d
      have hm : RobustBy adj blue blue budget (min deadline (Fintype.card V)) ↔
          RobustBy adj blue support budget (min deadline (Fintype.card V)) :=
        (computedRobustBy_iff adj blue blue k.val d.val).symm.trans
          (hc.trans (computedRobustBy_iff adj blue support k.val d.val))
      exact (RobustBy_min_card_deadline_iff adj blue blue budget deadline).symm.trans
        (hm.trans (RobustBy_min_card_deadline_iff adj blue support budget deadline))
  · intro h blue support hforcing hminimum k d
    have hB : IsForcing adj blue :=
      ⟨Fintype.card V, (computedFinishesBy_iff adj blue _).mp hforcing⟩
    have hH := (computedMinimumKilling_iff adj blue support).mp hminimum
    exact (computedRobustBy_iff adj blue blue k.val d.val).trans
      ((h blue hB support hH k.val d.val).trans
        (computedRobustBy_iff adj blue support k.val d.val).symm)

def fourPathAdj (x y : Fin 4) : Prop := x.val + 1 = y.val ∨ y.val + 1 = x.val

instance decidableFourPathAdj : DecidableRel fourPathAdj := by
  intro x y
  unfold fourPathAdj
  infer_instance

set_option maxHeartbeats 4000000 in
theorem fourPath_computed_support : computedEveryMinimumSupport fourPathAdj := by
  decide +kernel

theorem fourPath_every_minimum_support : EveryMinimumSupport fourPathAdj :=
  (computedEveryMinimumSupport_iff fourPathAdj).mp fourPath_computed_support

end FaultObservationResearch
