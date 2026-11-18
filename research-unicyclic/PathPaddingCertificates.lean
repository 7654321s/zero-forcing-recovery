module

public import ReplayForcing

@[expose] public section

set_option autoImplicit false

namespace FaultObservationResearch.MaskForcing

structure PathLayout where
  gaps : List ℕ
  lengths : List ℕ
  deriving DecidableEq, Repr

def PathLayout.ring (p : PathLayout) := p.gaps.length + p.gaps.sum
def PathLayout.order (p : PathLayout) := p.ring + p.lengths.sum

def pathStarts : List ℕ → ℕ → List ℕ
  | [], _ => []
  | length :: rest, start => start :: pathStarts rest (start + length)

def PathLayout.starts (p : PathLayout) := pathStarts p.lengths p.ring

def attachNumberedPaths : List ℕ → List ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | gap :: gaps, length :: lengths, site, start =>
    pendantEdges site start length ++
      attachNumberedPaths gaps lengths (site + gap + 1) (start + length)
  | _, _, _, _ => []

def PathLayout.edges (p : PathLayout) : List (ℕ × ℕ) :=
  cycleEdges p.ring ++ attachNumberedPaths p.gaps p.lengths 0 p.ring

def PathLayout.variables (p : PathLayout) : List ℕ :=
  (List.range p.lengths.length).filter (fun i => p.lengths[i]?.getD 0 > 1)

def PathLayout.endVertex (p : PathLayout) (arm : ℕ) : ℕ :=
  p.starts[arm]?.getD 0 + p.lengths[arm]?.getD 0 - 1

def PathLayout.rotated (p : PathLayout) (start : ℕ) (reverse : Bool) : PathLayout :=
  let n := p.gaps.length
  let positions := (List.range n).map fun i =>
    if reverse then (start + n - i) % n else (start + i) % n
  ⟨positions.map (fun i => p.gaps[if reverse then (i + n - 1) % n else i]?.getD 0),
    positions.map (fun i => p.lengths[i]?.getD 0)⟩

def digitRank (base : ℕ) (values : List ℕ) : ℕ :=
  values.foldl (fun rank digit => base * rank + digit) 0

def PathLayout.rank (p : PathLayout) : ℕ :=
  3 ^ p.gaps.length * digitRank 4 p.gaps + digitRank 3 (p.lengths.map (· - 1))

def PathLayout.canonical (p : PathLayout) : Bool :=
  (List.range p.gaps.length).all fun j =>
    decide (p.rank ≤ (p.rotated j false).rank) &&
    decide (p.rank ≤ (p.rotated j true).rank)

def words (digits : List ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => digits.flatMap (fun digit => (words digits n).map (digit :: ·))

theorem mem_words_iff (digits : List ℕ) (n : ℕ) (word : List ℕ) :
    word ∈ words digits n ↔ word.length = n ∧ ∀ d ∈ word, d ∈ digits := by
  induction n generalizing word with
  | zero =>
    cases word <;> simp [words]
  | succ n ih =>
    cases word with
    | nil => simp [words, List.mem_flatMap]
    | cons d tail =>
      simp only [words, List.mem_flatMap, List.mem_map, List.cons.injEq,
        List.length_cons, Nat.add_right_cancel_iff, List.mem_cons]
      constructor
      · rintro ⟨digit, hdigit, rest, hRest, rfl, rfl⟩
        obtain ⟨hLength, hDigits⟩ := (ih _).mp hRest
        exact ⟨hLength, fun x hx => hx.elim (fun hx => hx ▸ hdigit) (hDigits x)⟩
      · rintro ⟨hLength, hDigits⟩
        refine ⟨d, hDigits d (Or.inl rfl), tail, ?_, rfl, rfl⟩
        exact (ih _).mpr ⟨hLength, fun x hx => hDigits x (Or.inr hx)⟩

def shortGapWords (sites : ℕ) : List (List ℕ) :=
  (words [0, 1, 2, 3] sites).filter fun gaps =>
    let p : PathLayout := ⟨gaps, List.replicate sites 1⟩
    decide (5 ≤ p.ring) && p.canonical

def paddingGapWords : List (List ℕ) := [3, 4, 5].flatMap shortGapWords

def palettesAt (gaps : List ℕ) : List PathLayout :=
  ((words [1, 2] gaps.length).map (fun lengths => (⟨gaps, lengths⟩ : PathLayout))).filter fun p =>
    p.lengths.contains 2 && p.canonical

def shortPathLayouts : List PathLayout := paddingGapWords.flatMap palettesAt

theorem PathLayout.mem_shortPalettes (p : PathLayout) :
    p ∈ shortPathLayouts ↔ p.gaps ∈ paddingGapWords ∧
      p.lengths ∈ words [1, 2] p.gaps.length ∧ 2 ∈ p.lengths ∧ p.canonical := by
  rcases p with ⟨gaps, lengths⟩
  simp [shortPathLayouts, palettesAt, List.mem_flatMap, List.mem_filter, List.mem_map,
    Bool.and_eq_true, and_assoc]

def paddingException : PathLayout := ⟨[0, 1, 1], [1, 1, 2]⟩
def paddingExceptionLong : PathLayout := ⟨[0, 1, 1], [1, 1, 3]⟩

abbrev MarkedLayout := PathLayout × ℕ

def requiredAt (gaps : List ℕ) : List MarkedLayout :=
  ((palettesAt gaps).flatMap fun p => p.variables.map ((p, ·))).map fun mark =>
    if mark = (paddingException, 2) then (paddingExceptionLong, 2) else mark

def requiredPaddingMarks : List MarkedLayout := paddingGapWords.flatMap requiredAt

theorem required_padding_mark (p : PathLayout) (i : ℕ) (palette : p ∈ shortPathLayouts)
    (growing : i ∈ p.variables) :
    (if (p, i) = (paddingException, 2) then (paddingExceptionLong, 2) else (p, i)) ∈
      requiredPaddingMarks := by
  obtain ⟨gaps, hgaps, hp⟩ := List.mem_flatMap.mp palette
  apply List.mem_flatMap.mpr
  refine ⟨gaps, hgaps, List.mem_map.mpr ?_⟩
  refine ⟨(p, i), ?_, rfl⟩
  exact List.mem_flatMap.mpr ⟨p, hp, List.mem_map.mpr ⟨i, growing, rfl⟩⟩

structure PaddingCertificate where
  layout : PathLayout
  edges : List (ℕ × ℕ)
  edgesExact : edges = layout.edges
  table : Array (List (Fin layout.order))
  witness : Witness layout.order
  arms : List (ℕ × TailAudit layout.order)
  maxima : List ℕ

def PaddingCertificate.whiteClock (p : PaddingCertificate) (arm : ℕ) :
    Option (Clock p.layout.order) :=
  (p.arms.find? (fun a => a.1 == arm)).bind (fun a => a.2.clock?)

def PaddingCertificate.marked (p : PaddingCertificate) : List MarkedLayout :=
  p.maxima.map ((p.layout, ·))

def PaddingCertificate.extensionChecksUsing (p : PaddingCertificate) (read : TimedColors p.layout.order)
    (suppressed : Fin p.layout.order → Bool) : Bool :=
  let nbr : Neighbors p.layout.order := tableNeighbors p.table
  decide (p.arms.map Prod.fst = p.layout.variables) &&
  p.arms.all (fun (arm, tail) =>
    (tail.vertex.val == p.layout.endVertex arm) && tail.checkUsing p.witness nbr read suppressed) &&
  !p.maxima.isEmpty &&
  p.maxima.all (fun marked =>
    p.layout.variables.contains marked &&
    p.arms.all (fun (_, tail) =>
      match tail.clock? with
      | none => true
      | some c => decide (c.early < c.late) ||
          (p.whiteClock marked).any (fun maxClock => decide (c.early < maxClock.late))))

def PaddingCertificate.checkUsing (p : PaddingCertificate) (done : ℕ → ℕ → Bool)
    (read : TimedColors p.layout.order) (suppressed : Fin p.layout.order → Bool) : Bool :=
  tableMatches p.table p.edges &&
  p.witness.checkUsing done &&
  p.extensionChecksUsing read suppressed

def PaddingCertificate.extensionChecks (p : PaddingCertificate) : Bool :=
  let nbr := tableNeighbors p.table
  p.extensionChecksUsing (byRound nbr) (fun v => finishes (suppress nbr v) p.witness.blue p.layout.order)

def PaddingCertificate.check (p : PaddingCertificate) : Bool :=
  let nbr := tableNeighbors p.table
  p.checkUsing (finishes nbr) (byRound nbr) (fun v => finishes (suppress nbr v) p.witness.blue p.layout.order)

theorem PaddingCertificate.checked_witness (p : PaddingCertificate) (ok : p.check) :
    BudgetOnePairWitness
      (adj (tableNeighbors (edgeTable p.layout.order p.layout.edges)))
      (colors p.layout.order p.witness.blue) p.witness.support p.witness.slow p.witness.early := by
  simp only [PaddingCertificate.check, PaddingCertificate.checkUsing, Bool.and_eq_true, and_assoc] at ok
  rw [← p.edgesExact]
  exact check_numbered_witness p.edges p.table p.witness ok.1 ok.2.1

theorem PaddingCertificate.checked_extensions (p : PaddingCertificate) (ok : p.check) :
    p.extensionChecks = true := by
  simp only [PaddingCertificate.check, PaddingCertificate.checkUsing, Bool.and_eq_true, and_assoc] at ok
  exact ok.2.2

structure PaddingReplay where
  certificate : PaddingCertificate
  traces : List (Replay certificate.layout.order)

def PaddingReplay.marked (r : PaddingReplay) : List MarkedLayout := r.certificate.marked

def PaddingReplay.check (r : PaddingReplay) : Bool :=
  let p := r.certificate
  let nbr := tableNeighbors p.table
  r.traces.all (Replay.check nbr) &&
  p.checkUsing (replayDone nbr r.traces none) (replayRead nbr r.traces)
    (fun v => replayDone nbr r.traces (some v) p.witness.blue p.layout.order)

theorem PaddingReplay.checked_certificate (r : PaddingReplay) (ok : r.check) :
    r.certificate.check = true := by
  let p := r.certificate
  let nbr := tableNeighbors p.table
  simp only [PaddingReplay.check, PaddingCertificate.checkUsing, Bool.and_eq_true, and_assoc] at ok
  have distinct : ∀ v, (nbr v).Nodup :=
    tableMatches_distinct p.table p.edges ok.2.1
  have hReplay : r.traces.all (Replay.check nbr) := ok.1
  have hDone : replayDone nbr r.traces none = finishes nbr := by
    funext start t
    exact replayDone_eq nbr distinct r.traces hReplay none start t
  have hRead := replayRead_eq nbr distinct r.traces hReplay
  have hSuppress : (fun v => replayDone nbr r.traces (some v) p.witness.blue p.layout.order) =
      fun v => finishes (suppress nbr v) p.witness.blue p.layout.order := by
    funext v
    exact replayDone_eq nbr distinct r.traces hReplay (some v) p.witness.blue p.layout.order
  have hUsing : p.checkUsing (replayDone nbr r.traces none) (replayRead nbr r.traces)
      (fun v => replayDone nbr r.traces (some v) p.witness.blue p.layout.order) = true := by
    simpa only [PaddingCertificate.checkUsing, Bool.and_eq_true, and_assoc] using ok.2
  rw [hDone, hRead, hSuppress] at hUsing
  exact hUsing

def sameMarks (actual expected : List MarkedLayout) : Bool :=
  expected.all (fun mark => actual.contains mark) &&
  actual.all (fun mark => expected.contains mark)

structure PaddingGroup where
  gaps : List ℕ
  data : List PaddingReplay
  layoutCount : ℕ
  markCount : ℕ
  checked : data.all PaddingReplay.check = true
  covers : sameMarks (data.flatMap PaddingReplay.marked) (requiredAt gaps) = true
  layoutCount_ok : (palettesAt gaps).length = layoutCount
  markCount_ok : (requiredAt gaps).length = markCount

theorem PaddingGroup.covered_witness (g : PaddingGroup) (key : MarkedLayout)
    (member : key ∈ requiredAt g.gaps) :
    ∃ c : PaddingCertificate, key ∈ c.marked ∧ c.check = true := by
  have hSame := g.covers
  simp only [sameMarks, Bool.and_eq_true] at hSame
  have h : key ∈ g.data.flatMap PaddingReplay.marked := by
    simpa using List.all_eq_true.mp hSame.1 key member
  obtain ⟨r, hr, mark⟩ := List.mem_flatMap.mp h
  exact ⟨r.certificate, mark, r.checked_certificate (List.all_eq_true.mp g.checked r hr)⟩

end FaultObservationResearch.MaskForcing

#print axioms FaultObservationResearch.MaskForcing.PaddingCertificate.checked_witness
#print axioms FaultObservationResearch.MaskForcing.PaddingCertificate.checked_extensions
#print axioms FaultObservationResearch.MaskForcing.PaddingReplay.checked_certificate
#print axioms FaultObservationResearch.MaskForcing.PathLayout.mem_shortPalettes
#print axioms FaultObservationResearch.MaskForcing.required_padding_mark
#print axioms FaultObservationResearch.MaskForcing.PaddingGroup.covered_witness
