module

/-
Foundations for the initial-color-loss synchronous zero-forcing model.
This file proves model/semantic lemmas, not the candidate tree classification.
The accompanying build record determines which exact source was checked.
-/
public import «formalization-targets»
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace FaultObservationResearch

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

theorem mem_synchronousStep (adj : V → V → Prop) (blue : Finset V) (target : V) :
    target ∈ synchronousStep adj blue ↔ target ∈ blue ∨
      ∃ source ∈ blue, adj source target ∧
        ∀ other, adj source other → other ∉ blue → other = target := by
  classical
  simp [synchronousStep]

theorem subset_synchronousStep (adj : V → V → Prop) (blue : Finset V) :
    blue ⊆ synchronousStep adj blue := by
  intro target h
  exact (mem_synchronousStep adj blue target).mpr (Or.inl h)

theorem synchronousStep_mono (adj : V → V → Prop) {A B : Finset V}
    (hAB : A ⊆ B) : synchronousStep adj A ⊆ synchronousStep adj B := by
  classical
  intro target ht
  apply (mem_synchronousStep adj B target).mpr
  rcases (mem_synchronousStep adj A target).mp ht with h | ⟨source, hs, ha, hu⟩
  · exact Or.inl (hAB h)
  · by_cases hb : target ∈ B
    · exact Or.inl hb
    · refine Or.inr ⟨source, hAB hs, ha, ?_⟩
      intro other hao hwhite
      exact hu other hao (fun hother => hwhite (hAB hother))

@[simp] theorem synchronousStep_full (adj : V → V → Prop) :
    synchronousStep adj Finset.univ = Finset.univ := by
  apply le_antisymm (Finset.subset_univ _)
  exact subset_synchronousStep adj Finset.univ

@[simp] theorem colorAfter_zero (adj : V → V → Prop) (blue : Finset V) :
    colorAfter adj blue 0 = blue := rfl

theorem colorAfter_subset_succ (adj : V → V → Prop) (blue : Finset V) (t : ℕ) :
    colorAfter adj blue t ⊆ colorAfter adj blue (t + 1) :=
  subset_synchronousStep adj (colorAfter adj blue t)

theorem colorAfter_mono_time (adj : V → V → Prop) (blue : Finset V) :
    Monotone (colorAfter adj blue) := by
  exact monotone_nat_of_le_succ (colorAfter_subset_succ adj blue)

theorem colorAfter_mono_blue (adj : V → V → Prop) {A B : Finset V}
    (hAB : A ⊆ B) (t : ℕ) : colorAfter adj A t ⊆ colorAfter adj B t := by
  induction t with
  | zero => exact hAB
  | succ t ih => exact synchronousStep_mono adj ih

@[simp] theorem colorAfter_full (adj : V → V → Prop) (t : ℕ) :
    colorAfter adj Finset.univ t = Finset.univ := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [colorAfter, ih, synchronousStep_full]

theorem FinishesBy_mono_time (adj : V → V → Prop) (blue : Finset V)
    {s t : ℕ} (hs : FinishesBy adj blue s) (hst : s ≤ t) :
    FinishesBy adj blue t := by
  unfold FinishesBy at hs ⊢
  apply le_antisymm (Finset.subset_univ _)
  simpa only [hs] using colorAfter_mono_time adj blue hst

theorem FinishesBy_mono_blue (adj : V → V → Prop) {A B : Finset V}
    (hAB : A ⊆ B) {t : ℕ} (hA : FinishesBy adj A t) : FinishesBy adj B t := by
  unfold FinishesBy at hA ⊢
  apply le_antisymm (Finset.subset_univ _)
  simpa only [hA] using colorAfter_mono_blue adj hAB t

theorem IsForcing_mono (adj : V → V → Prop) {A B : Finset V}
    (hAB : A ⊆ B) (hA : IsForcing adj A) : IsForcing adj B := by
  obtain ⟨t, ht⟩ := hA
  exact ⟨t, FinishesBy_mono_blue adj hAB ht⟩

theorem colorAfter_add (adj : V → V → Prop) (blue : Finset V) (s t : ℕ) :
    colorAfter adj blue (s + t) = colorAfter adj (colorAfter adj blue s) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change synchronousStep adj (colorAfter adj blue (s + t)) =
      synchronousStep adj (colorAfter adj (colorAfter adj blue s) t)
    exact congrArg (synchronousStep adj) ih

theorem colorAfter_of_fixed (adj : V → V → Prop) (blue : Finset V)
    (hfixed : synchronousStep adj blue = blue) (t : ℕ) :
    colorAfter adj blue t = blue := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [colorAfter, ih, hfixed]

theorem FinishesBy_of_stable (adj : V → V → Prop) (blue : Finset V)
    (hforcing : IsForcing adj blue) (s : ℕ)
    (hstable : colorAfter adj blue (s + 1) = colorAfter adj blue s) :
    FinishesBy adj blue s := by
  obtain ⟨t, ht⟩ := hforcing
  by_cases hts : t ≤ s
  · exact FinishesBy_mono_time adj blue ht hts
  · have hst : s ≤ t := Nat.le_of_lt (Nat.lt_of_not_ge hts)
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hst
    have hfixed : synchronousStep adj (colorAfter adj blue s) = colorAfter adj blue s :=
      hstable
    unfold FinishesBy at ht ⊢
    rw [colorAfter_add, colorAfter_of_fixed adj (colorAfter adj blue s) hfixed] at ht
    exact ht

theorem card_colorAfter_strict_of_unfinished (adj : V → V → Prop) (blue : Finset V)
    (hforcing : IsForcing adj blue) (t : ℕ) (hnot : ¬ FinishesBy adj blue t) :
    (colorAfter adj blue t).card < (colorAfter adj blue (t + 1)).card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨colorAfter_subset_succ adj blue t, ?_⟩
  intro heq
  exact hnot (FinishesBy_of_stable adj blue hforcing t heq.symm)

/-- An autonomous increasing process cannot postpone its first completion beyond |V|. -/
theorem IsForcing_finishes_card (adj : V → V → Prop) (blue : Finset V)
    (hforcing : IsForcing adj blue) : FinishesBy adj blue (Fintype.card V) := by
  classical
  by_contra hnot
  let n := Fintype.card V
  have hgrow : ∀ t : ℕ, t ≤ n →
      (colorAfter adj blue t).card < (colorAfter adj blue (t + 1)).card := by
    intro t htn
    apply card_colorAfter_strict_of_unfinished adj blue hforcing t
    intro ht
    exact hnot (FinishesBy_mono_time adj blue ht htn)
  have hlower : ∀ t : ℕ, t ≤ n + 1 → t ≤ (colorAfter adj blue t).card := by
    intro t
    induction t with
    | zero => intro _; exact Nat.zero_le _
    | succ t ih =>
      intro htn
      have ht : t ≤ n := Nat.le_of_succ_le_succ htn
      have hc : t ≤ (colorAfter adj blue t).card :=
        ih (Nat.le_trans ht (Nat.le_succ n))
      exact Nat.succ_le_of_lt (lt_of_le_of_lt hc (hgrow t ht))
  have hupper : (colorAfter adj blue (n + 1)).card ≤ n := by
    simpa only [Finset.card_univ] using
      (Finset.card_le_card (Finset.subset_univ (colorAfter adj blue (n + 1))))
  exact Nat.not_succ_le_self n (le_trans (hlower (n + 1) le_rfl) hupper)

theorem IsForcing_iff_card_deadline (adj : V → V → Prop) (blue : Finset V) :
    IsForcing adj blue ↔ FinishesBy adj blue (Fintype.card V) :=
  ⟨IsForcing_finishes_card adj blue, fun h => ⟨Fintype.card V, h⟩⟩

theorem IsMinimumKilling_iff_card_minimum (adj : V → V → Prop)
    (blue support : Finset V) :
    IsMinimumKilling adj blue support ↔
      support ⊆ blue ∧ ¬ IsForcing adj (blue \ support) ∧
        ∀ loss : Finset V, loss ⊆ blue → ¬ IsForcing adj (blue \ loss) →
          support.card ≤ loss.card := by
  classical
  constructor
  · rintro ⟨hs, hfail, hmin⟩
    refine ⟨hs, hfail, ?_⟩
    intro loss hloss hfailed
    exact le_of_not_gt (fun hlt => hfailed (hmin loss hloss hlt))
  · rintro ⟨hs, hfail, hmin⟩
    refine ⟨hs, hfail, ?_⟩
    intro loss hloss hlt
    by_contra hfailed
    exact not_lt_of_ge (hmin loss hloss hfailed) hlt

/-- First successful round, or infinity if the process never finishes. -/
def completionTime (adj : V → V → Prop) (blue : Finset V) : ℕ∞ := by
  classical
  exact if h : IsForcing adj blue then (Nat.find h : ℕ∞) else ⊤

theorem completionTime_le_iff (adj : V → V → Prop) (blue : Finset V) (t : ℕ) :
    completionTime adj blue ≤ (t : ℕ∞) ↔ FinishesBy adj blue t := by
  classical
  by_cases h : IsForcing adj blue
  · simp only [completionTime, dite_eq_left h, ENat.natCast_le_natCast]
    constructor
    · intro ht
      exact FinishesBy_mono_time adj blue (Nat.find_spec h) ht
    · intro ht
      exact Nat.find_min' h ht
  · have hn : ¬ FinishesBy adj blue t := fun ht => h ⟨t, ht⟩
    simp [completionTime, h, hn]

theorem completionTime_eq_top_iff (adj : V → V → Prop) (blue : Finset V) :
    completionTime adj blue = ⊤ ↔ ¬ IsForcing adj blue := by
  classical
  by_cases h : IsForcing adj blue <;> simp [completionTime, h]

/-- Every loss is a subset of initial blue points; no graph vertex is deleted. -/
def allowedLosses (allowed : Finset V) (budget : ℕ) : Finset (Finset V) :=
  allowed.powerset.filter (fun loss => loss.card ≤ budget)

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mem_allowedLosses (allowed loss : Finset V) (budget : ℕ) :
    loss ∈ allowedLosses allowed budget ↔ loss ⊆ allowed ∧ loss.card ≤ budget := by
  simp [allowedLosses]

omit [Fintype V] [DecidableEq V] in
theorem empty_mem_allowedLosses (allowed : Finset V) (budget : ℕ) :
    ∅ ∈ allowedLosses allowed budget := by
  simp

/-- The maximum is taken in the extended naturals, so a failing loss contributes infinity. -/
def worstTime (adj : V → V → Prop) (blue allowed : Finset V) (budget : ℕ) : ℕ∞ :=
  (allowedLosses allowed budget).sup (fun loss => completionTime adj (blue \ loss))

theorem worstTime_le_iff (adj : V → V → Prop) (blue allowed : Finset V)
    (budget deadline : ℕ) :
    worstTime adj blue allowed budget ≤ (deadline : ℕ∞) ↔
      RobustBy adj blue allowed budget deadline := by
  classical
  simp only [worstTime, Finset.sup_le_iff, mem_allowedLosses,
    completionTime_le_iff, RobustBy, and_imp]

/-- Finite deadline comparisons separate all extended-natural values, including infinity. -/
theorem enat_eq_iff_finite_deadlines (F G : ℕ∞) :
    F = G ↔ ∀ t : ℕ, (F ≤ (t : ℕ∞) ↔ G ≤ (t : ℕ∞)) := by
  constructor
  · intro h
    subst G
    intro t
    rfl
  · intro h
    apply le_antisymm
    · by_cases hg : G = ⊤
      · simp [hg]
      · obtain ⟨t, rfl⟩ := ENat.ne_top_iff_exists.mp hg
        exact (h t).mpr le_rfl
    · by_cases hf : F = ⊤
      · simp [hf]
      · obtain ⟨t, rfl⟩ := ENat.ne_top_iff_exists.mp hf
        exact (h t).mp le_rfl

/-- The paper's worst-time formulation, using the exact original B/H/budget quantifiers. -/
def EveryMinimumSupportTime (adj : V → V → Prop) : Prop :=
  ∀ blue : Finset V, IsForcing adj blue →
    ∀ support : Finset V, IsMinimumKilling adj blue support →
      ∀ budget : ℕ, worstTime adj blue blue budget = worstTime adj blue support budget

theorem everyMinimumSupport_iff_worstTime (adj : V → V → Prop) :
    EveryMinimumSupport adj ↔ EveryMinimumSupportTime adj := by
  constructor
  · intro h blue hb support hs budget
    apply (enat_eq_iff_finite_deadlines _ _).mpr
    intro deadline
    rw [worstTime_le_iff, worstTime_le_iff]
    exact h blue hb support hs budget deadline
  · intro h blue hb support hs budget deadline
    rw [← worstTime_le_iff, ← worstTime_le_iff, h blue hb support hs budget]

theorem coronaAdj_symmetric {I : Type u} (core : SimpleGraph I) (amount : I → ℕ) :
    ∀ v w, coronaAdj core amount v w → coronaAdj core amount w v := by
  intro v w h
  cases v with
  | inl i =>
    cases w with
    | inl j => exact core.symm.symm i j h
    | inr leaf => exact h.symm
  | inr leaf =>
    cases w with
    | inl j => exact h.symm
    | inr other => exact False.elim h

theorem coronaAdj_irreflexive {I : Type u} (core : SimpleGraph I) (amount : I → ℕ) :
    ∀ v, ¬ coronaAdj core amount v v := by
  intro v h
  cases v with
  | inl i => exact core.loopless.irrefl i h
  | inr leaf => exact h

#print axioms synchronousStep_mono
#print axioms FinishesBy_mono_time
#print axioms completionTime_le_iff
#print axioms worstTime_le_iff
#print axioms enat_eq_iff_finite_deadlines
#print axioms everyMinimumSupport_iff_worstTime
#print axioms coronaAdj_symmetric
#print axioms coronaAdj_irreflexive

end FaultObservationResearch
