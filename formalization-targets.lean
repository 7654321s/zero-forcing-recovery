module

/-
MODEL DEFINITIONS AND UNPROVED CLASSIFICATION TARGETS.
These are definitions of the intended general statements; the final target
propositions below have no proofs yet. Foundational process and semantic lemmas
are developed in formalization-foundations.lean. Exact compilation status and
source hashes are recorded in the isolated Lean build runs and current status.
Defining any of the target propositions below does not prove that proposition.
-/
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.Sigma

@[expose] public section

noncomputable section

namespace FaultObservationResearch

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- All eligible forces use the same round-start coloring. -/
def synchronousStep (adj : V → V → Prop) (blue : Finset V) : Finset V := by
  classical
  exact blue ∪ Finset.univ.filter (fun target =>
    ∃ source ∈ blue, adj source target ∧
      ∀ other, adj source other → other ∉ blue → other = target)

def colorAfter (adj : V → V → Prop) (blue : Finset V) : ℕ → Finset V
  | 0 => blue
  | t + 1 => synchronousStep adj (colorAfter adj blue t)

def FinishesBy (adj : V → V → Prop) (blue : Finset V) (t : ℕ) : Prop :=
  colorAfter adj blue t = Finset.univ

def IsForcing (adj : V → V → Prop) (blue : Finset V) : Prop :=
  ∃ t : ℕ, FinishesBy adj blue t

/-- A loss changes only the initial color; adjacency is unchanged. -/
def IsMinimumKilling (adj : V → V → Prop) (blue support : Finset V) : Prop :=
  support ⊆ blue ∧ ¬ IsForcing adj (blue \ support) ∧
    ∀ loss : Finset V, loss ⊆ blue → loss.card < support.card →
      IsForcing adj (blue \ loss)

def RobustBy (adj : V → V → Prop) (blue allowed : Finset V)
    (budget deadline : ℕ) : Prop :=
  ∀ loss : Finset V, loss ⊆ allowed → loss.card ≤ budget →
    FinishesBy adj (blue \ loss) deadline

/-- Deadline form of equality of every worst-time value, including noncompletion.
The corresponding equivalence theorem is in formalization-foundations.lean. -/
def EveryMinimumSupport (adj : V → V → Prop) : Prop :=
  ∀ blue : Finset V, IsForcing adj blue →
    ∀ support : Finset V, IsMinimumKilling adj blue support →
      ∀ budget deadline : ℕ,
        (RobustBy adj blue blue budget deadline ↔
          RobustBy adj blue support budget deadline)

abbrev CoronaVertex (I : Type u) (amount : I → ℕ) :=
  I ⊕ (Σ i : I, Fin (amount i))

/-- Original core edges; each new leaf has precisely its designated core neighbor.
Symmetry and irreflexivity lemmas are in formalization-foundations.lean. -/
def coronaAdj {I : Type u} (core : SimpleGraph I) (amount : I → ℕ) :
    CoronaVertex I amount → CoronaVertex I amount → Prop
  | Sum.inl v, Sum.inl w => core.Adj v w
  | Sum.inl v, Sum.inr leaf => v = leaf.1
  | Sum.inr leaf, Sum.inl v => leaf.1 = v
  | Sum.inr _, Sum.inr _ => False

def CoreComplete {I : Type u} (core : SimpleGraph I) : Prop :=
  ∀ v w : I, v ≠ w → core.Adj v w

/-- General candidate target: this is a proposition definition, NOT a theorem. -/
def LeafyCoreTarget (I : Type u) [Fintype I] [DecidableEq I] [Nonempty I]
    (core : SimpleGraph I) (amount : I → ℕ) : Prop :=
  (∀ v : I, 2 ≤ amount v) →
    (EveryMinimumSupport (coronaAdj core amount) ↔ CoreComplete core)

/-- Last turn's exact double-star target, including the one-leaf boundary.
This is also an unproved proposition definition. -/
def DoubleStarTarget : Prop :=
  ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    (EveryMinimumSupport
      (coronaAdj (⊤ : SimpleGraph (Fin 2)) (fun i => if i = 0 then a else b)) ↔
      ((a = 1 ∧ b = 1) ∨ (2 ≤ a ∧ 2 ≤ b)))

end FaultObservationResearch
