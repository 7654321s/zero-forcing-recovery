module

public import ReplayForcing

@[expose] public section

set_option autoImplicit false

namespace FaultObservationResearch.MaskForcing

structure ForkLayout where
  leftGap : ℕ
  rightGap : ℕ
  depth : ℕ
  leftLength : ℕ
  rightLength : ℕ
  deriving DecidableEq, Repr

def ForkLayout.valid (p : ForkLayout) : Prop :=
  p.leftGap ≤ 2 ∧ p.leftGap ≤ p.rightGap ∧ p.rightGap ≤ 12 ∧
  2 ≤ p.leftGap + p.rightGap ∧ p.depth ≤ 4 ∧
  (p.leftLength = 1 ∨ p.leftLength = 2) ∧ (p.rightLength = 1 ∨ p.rightLength = 2) ∧
  (p.leftGap = p.rightGap → p.leftLength ≤ p.rightLength)

instance : DecidablePred ForkLayout.valid := by
  intro p
  unfold ForkLayout.valid
  infer_instance

def ForkLayout.ring (p : ForkLayout) := 3 + p.leftGap + p.rightGap
def ForkLayout.fork (p : ForkLayout) := if p.depth = 0 then 0 else p.ring + p.depth - 1
def ForkLayout.longLength (p : ForkLayout) := if p.leftLength = 1 ∧ p.rightLength = 1 then 3 else 4
def ForkLayout.longStart (p : ForkLayout) := p.ring + p.depth + 1
def ForkLayout.leftStart (p : ForkLayout) := p.longStart + p.longLength
def ForkLayout.rightStart (p : ForkLayout) := p.leftStart + p.leftLength
def ForkLayout.order (p : ForkLayout) := p.rightStart + p.rightLength

def ForkLayout.stemEdges (p : ForkLayout) : List (ℕ × ℕ) := pendantEdges 0 p.ring p.depth

def ForkLayout.edges (p : ForkLayout) : List (ℕ × ℕ) :=
  cycleEdges p.ring ++ p.stemEdges ++
    [(p.fork, p.longStart - 1)] ++ pendantEdges p.fork p.longStart p.longLength ++
    pendantEdges (p.leftGap + 1) p.leftStart p.leftLength ++
    pendantEdges (p.leftGap + 2) p.rightStart p.rightLength

def ForkLayout.endVertex (p : ForkLayout) (arm : ℕ) : ℕ :=
  if arm = 0 then p.leftStart - 1 else if arm = 1 then p.rightStart - 1 else p.order - 1

def ForkLayout.variableArms (p : ForkLayout) : List ℕ :=
  [0] ++ [1].filter (fun _ => p.leftLength > 1) ++ [2].filter (fun _ => p.rightLength > 1)

def ForkLayout.properAncestors (p : ForkLayout) : List ℕ :=
  if p.depth = 0 then [] else 0 :: (List.range (p.depth - 1)).map (p.ring + ·)

/-- Generate the finite family from the cycle gaps, stem depth and pattern of
the two exterior paths. The bounds correspond to the adjacent-site reduction. -/
def forkLayouts : List ForkLayout :=
  ((List.range 3).flatMap fun a =>
    (List.range 13).flatMap fun b =>
    (List.range 5).flatMap fun d =>
    [1, 2].flatMap fun l =>
    [1, 2].map fun r => (⟨a, b, d, l, r⟩ : ForkLayout)).filter
      (fun p => decide p.valid)

theorem forkLayout_mem_iff (p : ForkLayout) : p ∈ forkLayouts ↔ p.valid := by
  constructor
  · intro h
    exact of_decide_eq_true (List.mem_filter.mp h).2
  · intro h
    rcases p with ⟨a, b, d, l, r⟩
    have hFields := h
    rcases hFields with ⟨ha, _, hb, _, hd, hl, hr, _⟩
    change a ≤ 2 at ha
    change b ≤ 12 at hb
    change d ≤ 4 at hd
    apply List.mem_filter.mpr
    refine ⟨?_, decide_eq_true (show (ForkLayout.mk a b d l r).valid from h)⟩
    apply List.mem_flatMap.mpr
    refine ⟨a, List.mem_range.mpr (by omega), ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨b, List.mem_range.mpr (by omega), ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨d, List.mem_range.mpr (by omega), ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨l, by simpa using hl, ?_⟩
    exact List.mem_map.mpr ⟨r, by simpa using hr, rfl⟩

structure ForkCertificate where
  layout : ForkLayout
  table : Array (List (Fin layout.order))
  witness : Witness layout.order
  arms : List (ℕ × TailAudit layout.order)
  waiting : List (Clock layout.order)
  splitEdge : Option (Fin layout.order × Fin layout.order)

def ForkCertificate.longWhiteClock (c : ForkCertificate) : Option (Clock c.layout.order) :=
  (c.arms.find? (fun a => a.1 == 0)).bind (fun a => a.2.clock?)

def ForkCertificate.terminalChecksUsing (c : ForkCertificate) (read : TimedColors c.layout.order)
    (suppressed : Fin c.layout.order → Bool) : Bool :=
  let nbr : Neighbors c.layout.order := tableNeighbors c.table
  decide (c.arms.map Prod.fst = c.layout.variableArms) &&
  c.arms.all (fun (arm, tail) =>
    (tail.vertex.val == c.layout.endVertex arm) &&
    tail.checkUsing c.witness nbr read suppressed &&
    match tail.clock? with
    | none => true
    | some clock => decide (clock.early < clock.late) ||
        (c.longWhiteClock.any (fun long => decide (clock.early < long.late))))

def ForkCertificate.ancestorChecksUsing (c : ForkCertificate) (read : TimedColors c.layout.order)
    (suppressed : Fin c.layout.order → Bool) : Bool :=
  let wait := c.layout.properAncestors.filter fun v =>
    if h : v < c.layout.order then !(byOneUsing c.witness read ⟨v, h⟩) else true
  decide (c.waiting.map (fun clock => clock.vertex.val) = wait) &&
  c.waiting.all (fun clock =>
    clock.checkUsing c.witness read &&
    suppressed clock.vertex &&
    (decide (clock.early < clock.late) ||
      c.longWhiteClock.any (fun long => decide (clock.early + 1 < long.late))))

def ForkCertificate.edgeChecks (c : ForkCertificate) : Bool :=
  let nbr : Neighbors c.layout.order := tableNeighbors c.table
  match c.splitEdge with
  | none => c.layout.depth != 4
  | some (a, b) =>
    (c.layout.depth == 4) && (a != b) && edgeTest c.layout.stemEdges a.val b.val &&
    c.witness.compared.all (fun m => m.testBit a.val && m.testBit b.val) &&
    ((nbr a).all (fun v => c.witness.blue.testBit v.val) ||
      (nbr b).all (fun v => c.witness.blue.testBit v.val))

def ForkCertificate.checkUsing (c : ForkCertificate) (done : ℕ → ℕ → Bool)
    (read : TimedColors c.layout.order) (suppressed : Fin c.layout.order → Bool) : Bool :=
  decide c.layout.valid &&
  tableMatches c.table c.layout.edges &&
  c.witness.checkUsing done &&
  c.terminalChecksUsing read suppressed && c.ancestorChecksUsing read suppressed && c.edgeChecks

def ForkCertificate.terminalChecks (c : ForkCertificate) : Bool :=
  let nbr := tableNeighbors c.table
  c.terminalChecksUsing (byRound nbr) (fun v => finishes (suppress nbr v) c.witness.blue c.layout.order)

def ForkCertificate.ancestorChecks (c : ForkCertificate) : Bool :=
  let nbr := tableNeighbors c.table
  c.ancestorChecksUsing (byRound nbr) (fun v => finishes (suppress nbr v) c.witness.blue c.layout.order)

def ForkCertificate.check (c : ForkCertificate) : Bool :=
  let nbr := tableNeighbors c.table
  c.checkUsing (finishes nbr) (byRound nbr) (fun v => finishes (suppress nbr v) c.witness.blue c.layout.order)

theorem ForkCertificate.checked_witness (c : ForkCertificate) (ok : c.check) :
    BudgetOnePairWitness
      (adj (tableNeighbors (edgeTable c.layout.order c.layout.edges)))
      (colors c.layout.order c.witness.blue) c.witness.support c.witness.slow c.witness.early := by
  simp only [ForkCertificate.check, ForkCertificate.checkUsing, Bool.and_eq_true, and_assoc] at ok
  exact check_numbered_witness c.layout.edges c.table c.witness ok.2.1 ok.2.2.1

theorem ForkCertificate.checked_extensions (c : ForkCertificate) (ok : c.check) :
    c.terminalChecks = true ∧ c.ancestorChecks = true ∧ c.edgeChecks = true := by
  simp only [ForkCertificate.check, ForkCertificate.checkUsing, Bool.and_eq_true, and_assoc] at ok
  exact ok.2.2.2

structure ForkReplay where
  certificate : ForkCertificate
  traces : List (Replay certificate.layout.order)

def ForkReplay.layout (r : ForkReplay) : ForkLayout := r.certificate.layout

def ForkReplay.check (r : ForkReplay) : Bool :=
  let c := r.certificate
  let nbr := tableNeighbors c.table
  r.traces.all (Replay.check nbr) &&
  c.checkUsing (replayDone nbr r.traces none) (replayRead nbr r.traces)
    (fun v => replayDone nbr r.traces (some v) c.witness.blue c.layout.order)

theorem ForkReplay.checked_certificate (r : ForkReplay) (ok : r.check) :
    r.certificate.check = true := by
  let c := r.certificate
  let nbr := tableNeighbors c.table
  simp only [ForkReplay.check, ForkCertificate.checkUsing, Bool.and_eq_true, and_assoc] at ok
  have distinct : ∀ v, (nbr v).Nodup :=
    tableMatches_distinct c.table c.layout.edges ok.2.2.1
  have hReplay : r.traces.all (Replay.check nbr) := ok.1
  have hDone : replayDone nbr r.traces none = finishes nbr := by
    funext start t
    exact replayDone_eq nbr distinct r.traces hReplay none start t
  have hRead := replayRead_eq nbr distinct r.traces hReplay
  have hSuppress : (fun v => replayDone nbr r.traces (some v) c.witness.blue c.layout.order) =
      fun v => finishes (suppress nbr v) c.witness.blue c.layout.order := by
    funext v
    exact replayDone_eq nbr distinct r.traces hReplay (some v) c.witness.blue c.layout.order
  have hUsing : c.checkUsing (replayDone nbr r.traces none) (replayRead nbr r.traces)
      (fun v => replayDone nbr r.traces (some v) c.witness.blue c.layout.order) = true := by
    simpa only [ForkCertificate.checkUsing, Bool.and_eq_true, and_assoc] using ok.2
  rw [hDone, hRead, hSuppress] at hUsing
  exact hUsing

end FaultObservationResearch.MaskForcing

#print axioms FaultObservationResearch.MaskForcing.forkLayout_mem_iff
#print axioms FaultObservationResearch.MaskForcing.ForkCertificate.checked_witness
#print axioms FaultObservationResearch.MaskForcing.ForkCertificate.checked_extensions
#print axioms FaultObservationResearch.MaskForcing.ForkReplay.checked_certificate
