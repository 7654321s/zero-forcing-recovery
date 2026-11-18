module

public import MaskForcing
public import CertificateDeadline

@[expose] public section

set_option autoImplicit false

namespace FaultObservationResearch.MaskForcing

variable {n : ℕ}

/-- A budget-one certificate from a finite table. Vertex numbers are bounded
by the chosen graph order. -/
structure Witness (n : ℕ) where
  blue : ℕ
  first : Fin n
  second : Fin n
  slow : Fin n
  early : ℕ
  late : ℕ

def Witness.killing (w : Witness n) : ℕ := 2 ^ w.first.val ||| 2 ^ w.second.val

def Witness.support (w : Witness n) : Finset (Fin n) := {w.first, w.second}

theorem Witness.colors_killing (w : Witness n) : colors n w.killing = w.support := by
  ext v
  simp only [Witness.killing, Witness.support, mem_colors, Finset.mem_insert,
    Finset.mem_singleton, Nat.testBit_or, Nat.testBit_two_pow, decide_eq_true_eq,
    Bool.or_eq_true]
  exact ⟨Or.imp (fun h => Fin.ext h.symm) (fun h => Fin.ext h.symm),
    Or.imp (fun h => congrArg Fin.val h.symm) (fun h => congrArg Fin.val h.symm)⟩

def Witness.restricted (w : Witness n) : List ℕ :=
  [w.blue, remove w.blue (2 ^ w.first.val), remove w.blue (2 ^ w.second.val)]

def Witness.delayed (w : Witness n) : ℕ := remove w.blue (2 ^ w.slow.val)

def Witness.double (w : Witness n) : ℕ := remove w.blue w.killing

def Witness.compared (w : Witness n) : List ℕ :=
  w.restricted ++ [w.delayed, w.double]

/-- Check termination of every possible singleton loss, nontermination of
the pair, and both exact compared times. -/
def Witness.checkUsing (w : Witness n) (done : ℕ → ℕ → Bool) : Bool :=
  decide (w.first ≠ w.second) &&
  w.blue.testBit w.first.val && w.blue.testBit w.second.val && w.blue.testBit w.slow.val &&
  !(done w.double n) &&
  (List.finRange n).all (fun v =>
    !(w.blue.testBit v.val) || done (remove w.blue (2 ^ v.val)) n) &&
  w.restricted.all (fun start => done start w.early) &&
  (w.early == 0 || !(w.restricted.all (fun start => done start (w.early - 1)))) &&
  decide (w.early < w.late) &&
  done w.delayed w.late &&
  !(done w.delayed (w.late - 1))

def Witness.check (w : Witness n) (nbr : Neighbors n) : Bool := w.checkUsing (finishes nbr)

theorem Witness.checked_using_sound (w : Witness n) (relation : Fin n → Fin n → Prop)
    (done : ℕ → ℕ → Bool)
    (correct : ∀ start t, done start t = true ↔ FinishesBy relation (colors n start) t)
    (checked : w.checkUsing done = true) :
    BudgetOnePairWitness relation (colors n w.blue) w.support w.slow w.early := by
  simp only [Witness.checkUsing, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at checked
  obtain ⟨hDiff, hFirst, hSecond, hSlow, hDouble, hAll, hEarly, _, hTimes, _, hLate⟩ := checked
  have singleton (v : Fin n) : colors n (remove w.blue (2 ^ v.val)) =
      colors n w.blue \ {v} := by rw [colors_remove, colors_single]
  refine ⟨by simp [Witness.support, hDiff], ?_, ?_, ?_, ?_, (mem_colors _ _).mpr hSlow, ?_⟩
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | h
    · exact (mem_colors _ _).mpr hFirst
    · obtain rfl := Finset.mem_singleton.mp h
      exact (mem_colors _ _).mpr hSecond
  · intro h
    have hFinished := IsForcing_finishes_card _ _ h
    rw [Fintype.card_fin, ← w.colors_killing, ← colors_remove] at hFinished
    have hOver := (correct w.double n).mpr hFinished
    simp [hOver] at hDouble
  · intro v hv
    have hAllV := (List.all_eq_true.mp hAll) v (List.mem_finRange v)
    have hb := (mem_colors _ _).mp hv
    have hCompute : done (remove w.blue (2 ^ v.val)) n = true := by
      simpa [hb] using hAllV
    refine ⟨n, ?_⟩
    rw [← singleton]
    exact (correct _ _).mp hCompute
  · apply (robustBy_one_iff _ _ _ _).mpr
    have hRestricted (start : ℕ) (h : start ∈ w.restricted) :=
      (correct start w.early).mp ((List.all_eq_true.mp hEarly) start h)
    refine ⟨hRestricted w.blue (by simp [Witness.restricted]), ?_⟩
    intro v hv
    rw [← singleton]
    apply hRestricted
    rcases Finset.mem_insert.mp hv with rfl | h
    · simp [Witness.restricted]
    · obtain rfl := Finset.mem_singleton.mp h
      simp [Witness.restricted]
  · intro h
    rw [← singleton] at h
    have hMiss := FinishesBy_mono_time _ _ h (show w.early ≤ w.late - 1 by omega)
    have hTooEarly := (correct w.delayed (w.late - 1)).mpr hMiss
    simp [hTooEarly] at hLate

theorem Witness.checked_sound (w : Witness n) (nbr : Neighbors n)
    (distinct : ∀ v, (nbr v).Nodup) (checked : w.check nbr = true) :
    BudgetOnePairWitness (adj nbr) (colors n w.blue) w.support w.slow w.early :=
  w.checked_using_sound (adj nbr) (finishes nbr) (finishes_agrees nbr distinct) checked

end FaultObservationResearch.MaskForcing

#print axioms FaultObservationResearch.MaskForcing.Witness.checked_sound
