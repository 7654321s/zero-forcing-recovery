module

public import FiniteExtensions
public import FastMaskStep

@[expose] public section

set_option autoImplicit false

namespace FaultObservationResearch.MaskForcing

variable {n : ℕ}

/-- A sequence of proposed round results that ends at a fixed point. -/
def traceCorrect (nbr : Neighbors n) : ℕ → List ℕ → Bool
  | mask, [] => fastStep nbr mask == mask
  | mask, next :: rest => (fastStep nbr mask == next) && traceCorrect nbr next rest

def traceRound : ℕ → List ℕ → ℕ → ℕ
  | mask, _, 0 => mask
  | mask, [], _ + 1 => mask
  | _, next :: rest, t + 1 => traceRound next rest t

theorem traceRound_agrees (nbr : Neighbors n) (distinct : ∀ v, (nbr v).Nodup)
    (mask : ℕ) (states : List ℕ) (checked : traceCorrect nbr mask states) (t : ℕ) :
    colors n (traceRound mask states t) = colorAfter (adj nbr) (colors n mask) t := by
  induction t generalizing mask states with
  | zero => rfl
  | succ t ih =>
    cases states with
    | nil =>
      have h : step nbr mask = mask := (fastStep_eq nbr mask).symm.trans (eq_of_beq checked)
      have hFixed : synchronousStep (adj nbr) (colors n mask) = colors n mask := by
        rw [← step_agrees nbr distinct mask, h]
      exact (colorAfter_of_fixed (adj nbr) (colors n mask) hFixed (t + 1)).symm
    | cons next rest =>
      simp only [traceCorrect, Bool.and_eq_true, beq_iff_eq, fastStep_eq] at checked
      have hAdd : colorAfter (adj nbr) (colors n mask) (t + 1) =
          colorAfter (adj nbr) (colors n next) t := by
        rw [show t + 1 = 1 + t by omega, colorAfter_add]
        change colorAfter (adj nbr) (synchronousStep (adj nbr) (colors n mask)) t = _
        rw [← step_agrees nbr distinct, checked.1]
      rw [hAdd]
      exact ih next rest checked.2

def neighborsFor (nbr : Neighbors n) : Option (Fin n) → Neighbors n
  | none => nbr
  | some v => suppress nbr v

theorem neighborsFor_distinct (nbr : Neighbors n) (distinct : ∀ v, (nbr v).Nodup)
    (block : Option (Fin n)) : ∀ v, (neighborsFor nbr block v).Nodup := by
  cases block with
  | none => exact distinct
  | some v => exact suppress_distinct nbr distinct v

structure Replay (n : ℕ) where
  blocked : Option (Fin n)
  start : ℕ
  states : List ℕ

def Replay.check (nbr : Neighbors n) (trace : Replay n) : Bool :=
  traceCorrect (neighborsFor nbr trace.blocked) trace.start trace.states

def replayRun (nbr : Neighbors n) (traces : List (Replay n))
    (block : Option (Fin n)) (start t : ℕ) : ℕ :=
  match traces.find? (fun trace => (trace.blocked == block) && (trace.start == start)) with
  | none => run (neighborsFor nbr block) start t
  | some trace => traceRound start trace.states t

theorem replayRun_agrees (nbr : Neighbors n) (distinct : ∀ v, (nbr v).Nodup)
    (traces : List (Replay n)) (checked : traces.all (Replay.check nbr))
    (block : Option (Fin n)) (start t : ℕ) :
    colors n (replayRun nbr traces block start t) =
      colorAfter (adj (neighborsFor nbr block)) (colors n start) t := by
  unfold replayRun
  cases h : traces.find? (fun trace => (trace.blocked == block) && (trace.start == start)) with
  | none => exact run_agrees _ (neighborsFor_distinct nbr distinct block) start t
  | some trace =>
    have hMatch := List.find?_some h
    simp only [Bool.and_eq_true, beq_iff_eq] at hMatch
    have hCheck := List.all_eq_true.mp checked trace (List.mem_of_find?_eq_some h)
    unfold Replay.check at hCheck
    rw [hMatch.1, hMatch.2] at hCheck
    exact traceRound_agrees _ (neighborsFor_distinct nbr distinct block) start trace.states hCheck t

def replayDone (nbr : Neighbors n) (traces : List (Replay n))
    (block : Option (Fin n)) (start t : ℕ) : Bool :=
  fullMask n (replayRun nbr traces block start t)

theorem replayDone_agrees (nbr : Neighbors n) (distinct : ∀ v, (nbr v).Nodup)
    (traces : List (Replay n)) (checked : traces.all (Replay.check nbr))
    (block : Option (Fin n)) (start t : ℕ) :
    replayDone nbr traces block start t = true ↔
      FinishesBy (adj (neighborsFor nbr block)) (colors n start) t := by
  unfold replayDone FinishesBy
  rw [fullMask_agrees, replayRun_agrees nbr distinct traces checked block start t]

theorem replayDone_eq (nbr : Neighbors n) (distinct : ∀ v, (nbr v).Nodup)
    (traces : List (Replay n)) (checked : traces.all (Replay.check nbr))
    (block : Option (Fin n)) (start t : ℕ) :
    replayDone nbr traces block start t = finishes (neighborsFor nbr block) start t :=
  Bool.eq_iff_iff.mpr ((replayDone_agrees nbr distinct traces checked block start t).trans
    (finishes_agrees (neighborsFor nbr block) (neighborsFor_distinct nbr distinct block) start t).symm)

def replayRead (nbr : Neighbors n) (traces : List (Replay n)) : TimedColors n :=
  fun start v round => fastBit (replayRun nbr traces none start round) v.val

theorem replayRead_eq (nbr : Neighbors n) (distinct : ∀ v, (nbr v).Nodup)
    (traces : List (Replay n)) (checked : traces.all (Replay.check nbr)) :
    replayRead nbr traces = byRound nbr := by
  funext start v round
  apply Bool.eq_iff_iff.mpr
  simp only [replayRead, fastBit_eq]
  change (replayRun nbr traces none start round).testBit v.val = true ↔
    (run nbr start round).testBit v.val = true
  rw [← mem_colors, ← mem_colors, replayRun_agrees nbr distinct traces checked, run_agrees nbr distinct]
  rfl

theorem check_replayed_numbered_witness (edges : List (ℕ × ℕ))
    (rows : Array (List (Fin n))) (w : Witness n) (traces : List (Replay n))
    (sameGraph : tableMatches rows edges)
    (checked : traces.all (Replay.check (tableNeighbors rows)))
    (valid : w.checkUsing (replayDone (tableNeighbors rows) traces none)) :
    BudgetOnePairWitness (adj (tableNeighbors (edgeTable n edges)))
      (colors n w.blue) w.support w.slow w.early := by
  rw [← tableMatches_adj rows edges sameGraph]
  exact w.checked_using_sound _ _
    (replayDone_agrees _ (tableMatches_distinct rows edges sameGraph) traces checked none) valid

end FaultObservationResearch.MaskForcing

#print axioms FaultObservationResearch.MaskForcing.traceRound_agrees
#print axioms FaultObservationResearch.MaskForcing.replayDone_agrees
#print axioms FaultObservationResearch.MaskForcing.replayRead_eq
#print axioms FaultObservationResearch.MaskForcing.check_replayed_numbered_witness
