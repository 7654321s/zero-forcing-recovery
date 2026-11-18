module

public import NumberedGraph

@[expose] public section

set_option autoImplicit false

namespace FaultObservationResearch.MaskForcing

variable {n : ℕ}

def byRound (nbr : Neighbors n) (start : ℕ) (v : Fin n) (t : ℕ) : Bool :=
  (run nbr start t).testBit v.val

theorem byRound_agrees (nbr : Neighbors n) (distinct : ∀ v, (nbr v).Nodup)
    (start : ℕ) (v : Fin n) (t : ℕ) :
    byRound nbr start v t = true ↔ v ∈ colorAfter (adj nbr) (colors n start) t := by
  rw [← run_agrees nbr distinct start t, mem_colors]
  rfl

def suppress (nbr : Neighbors n) (v : Fin n) : Neighbors n :=
  fun source => if source = v then [] else nbr source

theorem suppress_adj (nbr : Neighbors n) (blocked a b : Fin n) :
    adj (suppress nbr blocked) a b ↔ adj nbr a b ∧ a ≠ blocked := by
  by_cases h : a = blocked <;> simp [adj, suppress, h]

theorem suppress_distinct (nbr : Neighbors n) (distinct : ∀ v, (nbr v).Nodup)
    (blocked a : Fin n) : (suppress nbr blocked a).Nodup := by
  by_cases h : a = blocked <;> simp [suppress, h, distinct]

abbrev TimedColors (n : ℕ) := ℕ → Fin n → ℕ → Bool

def byOneUsing (w : Witness n) (read : TimedColors n) (v : Fin n) : Bool :=
  w.compared.all (fun start => read start v 1)

def byOneInCompared (w : Witness n) (nbr : Neighbors n) (v : Fin n) : Bool :=
  byOneUsing w (byRound nbr) v

/-- The new tail may be all blue. Its first vertex can help restore the
old terminal in round one. The final disjunction checks a lost new leaf. -/
def blueTailSafeUsing (w : Witness n) (nbr : Neighbors n) (read : TimedColors n)
    (suppressed : Fin n → Bool) (v : Fin n) : Bool :=
  byOneUsing w read v &&
  (!(w.blue.testBit v.val) || (nbr v).any (fun v => w.blue.testBit v.val) ||
    suppressed v)

def blueTailSafe (w : Witness n) (nbr : Neighbors n) (v : Fin n) : Bool :=
  blueTailSafeUsing w nbr (byRound nbr) (fun v => finishes (suppress nbr v) w.blue n) v

def arrivalAtUsing (read : TimedColors n) (start : ℕ) (v : Fin n) (t : ℕ) : Bool :=
  read start v t && (t == 0 || !(read start v (t - 1)))

def arrivalAt (nbr : Neighbors n) : TimedColors n :=
  arrivalAtUsing (byRound nbr)

theorem arrivalAt_sound (nbr : Neighbors n) (distinct : ∀ v, (nbr v).Nodup)
    (start : ℕ) (v : Fin n) (t : ℕ) (checked : arrivalAt nbr start v t) :
    v ∈ colorAfter (adj nbr) (colors n start) t ∧
      ∀ r < t, v ∉ colorAfter (adj nbr) (colors n start) r := by
  simp only [arrivalAt, arrivalAtUsing, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at checked
  refine ⟨(byRound_agrees nbr distinct start v t).mp checked.1, ?_⟩
  intro r hrt hBlue
  rcases checked.2 with hZero | hLate
  · omega
  · have hb := colorAfter_mono_time (adj nbr) (colors n start)
      (show r ≤ t - 1 by omega) hBlue
    have heq := (byRound_agrees nbr distinct start v (t - 1)).mpr hb
    simp [heq] at hLate

structure Clock (n : ℕ) where
  vertex : Fin n
  early : ℕ
  late : ℕ

def Clock.checkUsing (c : Clock n) (w : Witness n) (read : TimedColors n) : Bool :=
  w.restricted.all (fun start => read start c.vertex c.early) &&
  (c.early == 0 ||
    !(w.restricted.all (fun start => read start c.vertex (c.early - 1)))) &&
  arrivalAtUsing read w.delayed c.vertex c.late

def Clock.check (c : Clock n) (w : Witness n) (nbr : Neighbors n) : Bool :=
  c.checkUsing w (byRound nbr)

theorem Clock.checked_sound (c : Clock n) (w : Witness n) (nbr : Neighbors n)
    (distinct : ∀ v, (nbr v).Nodup) (checked : c.check w nbr) :
    (∀ start ∈ w.restricted, c.vertex ∈ colorAfter (adj nbr) (colors n start) c.early) ∧
    c.vertex ∈ colorAfter (adj nbr) (colors n w.delayed) c.late ∧
    (∀ s < c.late, c.vertex ∉ colorAfter (adj nbr) (colors n w.delayed) s) := by
  simp only [Clock.check, Clock.checkUsing, Bool.and_eq_true, and_assoc] at checked
  exact ⟨fun start h => (byRound_agrees nbr distinct start c.vertex c.early).mp
    ((List.all_eq_true.mp checked.1) start h),
    arrivalAt_sound nbr distinct w.delayed c.vertex c.late checked.2.2⟩

inductive TailAudit (n : ℕ) where
  | blue (vertex : Fin n)
  | white (clock : Clock n)

def TailAudit.vertex : TailAudit n → Fin n
  | .blue v => v
  | .white c => c.vertex

def TailAudit.clock? : TailAudit n → Option (Clock n)
  | .blue _ => none
  | .white c => some c

def TailAudit.checkUsing (w : Witness n) (nbr : Neighbors n) (read : TimedColors n)
    (suppressed : Fin n → Bool) : TailAudit n → Bool
  | .blue v => blueTailSafeUsing w nbr read suppressed v
  | .white c => !(w.blue.testBit c.vertex.val) && c.checkUsing w read

def TailAudit.check (w : Witness n) (nbr : Neighbors n) : TailAudit n → Bool :=
  TailAudit.checkUsing w nbr (byRound nbr) (fun v => finishes (suppress nbr v) w.blue n)

end FaultObservationResearch.MaskForcing

#print axioms FaultObservationResearch.MaskForcing.suppress_adj
#print axioms FaultObservationResearch.MaskForcing.Clock.checked_sound
